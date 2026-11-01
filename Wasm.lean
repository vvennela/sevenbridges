import SevenBridges.Backend

/-!
# The browser backend. Exports one function to JavaScript: give it a request line,
get the reply line. It runs the same `handleLine` as the native program
(`Main.lean`), and keeps the game state between calls.
-/

instance : Nonempty Game := ⟨initialGame⟩

/-- The current game, kept between requests. -/
initialize gameRef : IO.Ref Game ← IO.mkRef initialGame

/-- Answer one request line (called from C as `sb_handle`). -/
@[export sb_handle]
def wasmHandle (line : String) : IO String := do
  let (reply, g) := handleLine (← gameRef.get) line
  gameRef.set g
  return reply
