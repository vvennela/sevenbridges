import SevenBridges.Backend

/-!
# The native game backend: one JSON request per line on stdin, one JSON reply per
line on stdout (DESIGN.md §9). The commands are in `SevenBridges/Backend.lean`.
-/

partial def loop (g : Game) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let (reply, g) := handleLine g line
  stdout.putStrLn reply
  stdout.flush
  loop g stdin stdout

def main : IO Unit := do
  loop initialGame (← IO.getStdin) (← IO.getStdout)
