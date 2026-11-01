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
#audit_axioms SevenBridges.Generator.generate_no_fixed
#audit_axioms SevenBridges.routeRush_maxLoad_le
#audit_axioms SevenBridges.routeRush_all_off
#audit_axioms SevenBridges.routeRush_boarded_add_leftBehind
#audit_axioms SevenBridges.legs_return_home
#audit_axioms SevenBridges.simulate_cats
#audit_axioms SevenBridges.population_nodup
#audit_axioms SevenBridges.cats_conserved
#audit_axioms SevenBridges.night_at_home
#audit_axioms SevenBridges.Generator.next_injective
#audit_axioms SevenBridges.Generator.prevState_next
#audit_axioms SevenBridges.Generator.streams_differ
#audit_axioms SevenBridges.Generator.lcg_returns_iff
#audit_axioms SevenBridges.Generator.lcg_full_period
#audit_axioms SevenBridges.Generator.rng_full_period
#audit_axioms SevenBridges.Generator.every_output_reached
#audit_axioms SevenBridges.Generator.below_fair
#audit_axioms SevenBridges.Generator.pick_mem
#audit_axioms SevenBridges.Generator.choose_spec
#audit_axioms SevenBridges.Generator.choose_length
#audit_axioms SevenBridges.Generator.choose_mem
#audit_axioms SevenBridges.Generator.choose_nodup
#audit_axioms SevenBridges.Generator.catTraits_same
#audit_axioms SevenBridges.Generator.population_traits
#spec_surface SevenBridges.solve_is_best
