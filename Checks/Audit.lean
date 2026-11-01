import SevenBridges
open Lean Elab Command

/-- `#audit_axioms thm`: print the axioms `thm` depends on. -/
elab "#audit_axioms " id:ident : command => do
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms thm
  logInfo m!"{thm}: {axs.toList}"

/-- Definitions a theorem's statement mentions, followed through their bodies. -/
partial def specSurface (env : Environment) (thm : Name) : NameSet :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | c :: rest =>
      if seen.contains c then go rest seen else
      let next := match env.find? c with
        | some (.defnInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
        | some ci => ci.type.getUsedConstants.toList
        | none => []
      go (next ++ rest) (seen.insert c)
  match env.find? thm with
  | some ci => go ci.type.getUsedConstants.toList {}
  | none => {}

/-- `#spec_surface thm`: this project's definitions that the statement of `thm` depends on. -/
elab "#spec_surface " id:ident : command => do
  let env ← getEnv
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let own := (specSurface env thm).toList.filter fun c =>
    (`SevenBridges).isPrefixOf c && !c.isInternal && !Meta.isMatcherCore env c
  logInfo m!"{own.length} definitions: {own}"

#audit_axioms SevenBridges.solve_is_best
#audit_axioms SevenBridges.solveWithFuel_steps_le
#audit_axioms SevenBridges.solvePlain_is_best
#audit_axioms SevenBridges.solveWork_le
#audit_axioms SevenBridges.empty_valid
#audit_axioms SevenBridges.rating_le_100
#audit_axioms SevenBridges.rating_eq_100_iff
#audit_axioms SevenBridges.length_candidates
#audit_axioms SevenBridges.Generator.generate_work_le
#spec_surface SevenBridges.solve_is_best
