import Rails.Extract

/-!
The extractor's file reading: a dataset directory's session files, each session's parts in order,
through the pure core (`Rails.Extract`).
-/

namespace Rails.Extract

/-- Every session file under `root`, as each session's parts in part order. A file whose name isn't
a session file's is skipped, and counted in the second component. -/
partial def listSessions (root : System.FilePath) : IO (List (List System.FilePath) × Nat) := do
  let mut found : Array (String × Nat × System.FilePath) := #[]
  let mut skipped := 0
  let mut todo := #[root]
  while h : todo.size > 0 do
    let dir := todo.back
    todo := todo.pop
    for entry in ← dir.readDir do
      if ← entry.path.isDir then
        if walked entry.fileName then todo := todo.push entry.path
      else match partOf entry.fileName with
        | some (base, n) => found := found.push ((dir / base).toString, n, entry.path)
        | none => skipped := skipped + 1
  let sorted := found.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  let groups := sorted.toList.splitBy (fun a b => a.1 == b.1)
  return (groups.map (·.map (·.2.2)), skipped)

/-- One session's trace and summary, its parts read in the order given. -/
def readSession (parts : List System.FilePath) : IO (Array Step × Summary) := do
  let mut lines : Array Line := #[]
  for part in parts do
    for line in ← IO.FS.lines part do
      lines := lines.push (parseLine line)
  return assemble lines.toList

end Rails.Extract
