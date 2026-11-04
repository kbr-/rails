import Rails.Extract

/-!
The extractor's guarantees: no line is dropped silently (each is counted under exactly one kind),
every event becomes a step, and the parsers of times, file names and positions read their forms.
-/

namespace Rails.Extract

/-- Every line is counted under exactly one kind. -/
theorem tally_partition (ls : List Line) :
    (tally ls).lines = (tally ls).events + (tally ls).labels + (tally ls).metas +
      (tally ls).unknownKind + (tally ls).unknownRecord + (tally ls).unparsable := by
  induction ls with
  | nil => rfl
  | cons l ls ih => cases l <;> simp only [tally] <;> omega

theorem tally_lines (ls : List Line) : (tally ls).lines = ls.length := by
  induction ls with
  | nil => rfl
  | cons l ls ih => cases l <;> simp [tally, ih]

theorem turns_length (ls : List Line) : (turns ls).length = (tally ls).events := by
  induction ls with
  | nil => rfl
  | cons l ls ih => cases l <;> simp [turns, tally, ih]

theorem messages_length (prev : Option Bool) (n : Nat) (as : List Bool) :
    (messages prev n as).length = as.length := by
  induction as generalizing prev n with
  | nil => rfl
  | cons a as ih => simp [messages, ih]

/-- Splitting into runs keeps every event, in order. -/
theorem runs_flatten (rs : List Rec) : (runs rs).flatten = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [runs]
    split
    · rename_i s g gs h
      rw [h] at ih
      split <;> simp_all
    · rename_i gs h
      simp_all

/-- Every event of a session becomes a step of its trace. -/
theorem assemble_steps (ls : List Line) : (assemble ls).1.size = (tally ls).events := by
  have hlen : ((runs (turns ls)).map fun g => g.mergeSort (fun x y => x.2.1 ≤ y.2.1)).flatten.length
      = (turns ls).length := by
    rw [List.length_flatten, List.map_map]
    have : (List.length ∘ fun g : List Rec => g.mergeSort (fun x y => x.2.1 ≤ y.2.1)) =
        List.length := by
      funext g; simp [List.length_mergeSort]
    rw [this, ← List.length_flatten, runs_flatten]
  simp only [assemble, List.size_toArray, List.length_map, List.length_zip, messages_length]
  rw [hlen, turns_length]
  omega

/-- The summary counts every line given. -/
theorem assemble_lines (ls : List Line) : (assemble ls).2.lines = ls.length := by
  simp [assemble, tally_lines]

/-- The agent's consecutive events share a message; any other event starts one. -/
example : messages none 0 [false, true, true, false, true] = [0, 1, 1, 2, 3] := by decide

/-- A missing position, a repeated one and a step back are each counted. -/
example : runFaults none [0, 1, 1, 3, 2] = (1, 1, 1) := by decide
/-- A run whose first position isn't 0 counts the missing start. -/
example : runFaults none [2, 3] = (2, 0, 0) := by decide
/-- A turn continuing in a later run starts one past its last position, with no fault. -/
example : sessionFaults [] [[("t", 0, true, .reply "", none), ("t", 1, true, .reply "", none)],
    [("u", 0, true, .reply "", none)], [("t", 2, true, .reply "", none)]] = (0, 0, 0) := by decide
/-- Consecutive events of one turn form one run; another turn starts a new one. -/
example : (runs [("t", 0, true, .reply "", none), ("t", 1, true, .reply "", none),
    ("u", 0, true, .reply "", none)]).map List.length = [2, 1] := by decide

/-! Times: the epoch, a leap day and a dataset time, against Python's `datetime`. -/
example : parseTime "1970-01-01T00:00:00.000Z" = some 0 := by decide
example : parseTime "2000-02-29T23:59:59.999Z" = some 951868799999 := by decide
example : parseTime "2026-10-25T20:16:56.336Z" = some 1792959416336 := by decide
example : parseTime "2026-10-25T20:16:56Z" = none := by decide
example : parseTime "2026-13-25T20:16:56.336Z" = none := by decide
example : parseTime "2026-1x-25T20:16:56.336Z" = none := by decide

/-- `latest` returns a time it was given, at least as late as every other. -/
theorem latest_mem_ge (ts : List String) (t : String) (h : latest ts = some t) :
    t ∈ ts ∧ ∀ u ∈ ts, ¬ t < u := by
  induction ts generalizing t with
  | nil => simp [latest] at h
  | cons x xs ih =>
    simp only [latest] at h
    split at h
    · rename_i hn
      cases h
      have : xs = [] := by
        cases xs with
        | nil => rfl
        | cons y ys => simp [latest] at hn; split at hn <;> simp at hn
      subst this
      simp
    · rename_i u hu
      obtain ⟨mem, ge⟩ := ih u hu
      cases h
      by_cases hxu : x < u
      · simp only [hxu, ite_true]
        refine ⟨List.mem_cons_of_mem _ mem, ?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact String.lt_asymm hxu
        · exact ge v hv
      · simp only [hxu, ite_false]
        refine ⟨List.mem_cons_self, ?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact String.lt_irrefl _
        · exact fun hxv => ge v hv (Std.lt_of_le_of_lt hxu hxv)

example : latest [] = none := rfl

/-! File names. -/
example : partOf "abc.jsonl" = some ("abc", 1) := by decide
example : partOf "abc.2.jsonl" = some ("abc", 2) := by decide
example : partOf "abc.12.jsonl" = some ("abc", 12) := by decide
example : partOf "agent-a6.jsonl" = some ("agent-a6", 1) := by decide
example : partOf "abc.jsonl.zst" = none := by decide
example : partOf "abc.txt" = none := by decide

end Rails.Extract
