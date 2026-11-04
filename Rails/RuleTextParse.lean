/-!
Reading `tasks/agents-on-rails/RULES.md`'s numbered rules: each item's number, its RFC keywords in
the order they occur (MUST NOT and SHOULD NOT read before MUST and SHOULD), its text with the
bracketed sources at its end cut, and the sources' codes (`TP`, `AG`, `ED`, ...). Pure, so its
behaviour on sample items is proved in `Rails.RuleTextProofs`; `rails-texts` writes the table.
-/

namespace Rails.RuleTextParse

inductive Keyword where
  | must | mustNot | should | shouldNot | may
  deriving Repr, DecidableEq, Inhabited

def Keyword.leanName : Keyword → String
  | .must => ".must" | .mustNot => ".mustNot" | .should => ".should"
  | .shouldNot => ".shouldNot" | .may => ".may"

structure Item where
  number : Nat
  keywords : List Keyword
  text : String
  sources : List String
  deriving Repr, Inhabited

/-- The digits ending at the first `". "` of a line that starts an item, and the rest. -/
def itemStart (line : String) : Option (Nat × String) :=
  let cs := line.toList
  let digits := cs.takeWhile Char.isDigit
  let rest := cs.drop digits.length
  if digits.isEmpty then none
  else match rest with
    | '.' :: ' ' :: body => some (String.ofList digits |>.toNat!, String.ofList body)
    | _ => none

/-- The words of a text: its maximal runs of letters, in order. -/
def words (cs : List Char) : List (List Char) :=
  go cs [] []
where
  /-- `w` is the current word reversed, `acc` the words so far reversed. -/
  go : List Char → List Char → List (List Char) → List (List Char)
    | [], w, acc => (if w.isEmpty then acc else w.reverse :: acc).reverse
    | c :: rest, w, acc =>
      if c.isAlpha then go rest (c :: w) acc
      else go rest [] (if w.isEmpty then acc else w.reverse :: acc)

/-- The keywords among a text's words, in order, `MUST` followed by `NOT` read as one. Whole words
only, so `MUST` inside `MUSTER` is none. -/
def keywordsOf : List (List Char) → List Keyword
  | ['M', 'U', 'S', 'T'] :: ['N', 'O', 'T'] :: rest => .mustNot :: keywordsOf rest
  | ['S', 'H', 'O', 'U', 'L', 'D'] :: ['N', 'O', 'T'] :: rest => .shouldNot :: keywordsOf rest
  | ['M', 'U', 'S', 'T'] :: rest => .must :: keywordsOf rest
  | ['S', 'H', 'O', 'U', 'L', 'D'] :: rest => .should :: keywordsOf rest
  | ['M', 'A', 'Y'] :: rest => .may :: keywordsOf rest
  | _ :: rest => keywordsOf rest
  | [] => []

def keywords (cs : List Char) : List Keyword := keywordsOf (words cs)

def trimEnd (cs : List Char) : List Char := ((cs.reverse).dropWhile Char.isWhitespace).reverse
def trim (cs : List Char) : List Char := trimEnd (cs.dropWhile Char.isWhitespace)

/-- A text split at its last `[`, when it ends `]`: the text before, trimmed, and the inside. -/
def splitSources (cs : List Char) : List Char × Option (List Char) :=
  let t := trimEnd cs
  match t.reverse with
  | ']' :: r =>
    let inside := (r.takeWhile (· != '[')).reverse
    match r.dropWhile (· != '[') with
    | '[' :: before => (trimEnd before.reverse, some inside)
    | _ => (t, none)
  | _ => (t, none)

/-- A source list's codes: each `;`-separated part's text before `#`, trimmed. -/
def codes (inside : List Char) : List String :=
  (inside.splitOn ';').map fun p => String.ofList (trim (p.takeWhile (· != '#')))

/-- The items of a file's lines: an item starts at a numbered line and runs over the indented lines
after it, each joined with one space. -/
def items (lines : List String) : List Item :=
  let rec loop : List String → Option (Nat × List String) → List Item
    | [], none => []
    | [], some (n, parts) => [finish n parts]
    | l :: rest, cur =>
      match itemStart l with
      | some (n, body) =>
        let done := match cur with
          | some (m, parts) => [finish m parts]
          | none => []
        done ++ loop rest (some (n, [body]))
      | none =>
        match cur with
        | some (m, parts) =>
          if l.startsWith " " && !(trim l.toList).isEmpty then
            loop rest (some (m, parts ++ [String.ofList (trim l.toList)]))
          else finish m parts :: loop rest none
        | none => loop rest none
  loop lines none
where
  finish (n : Nat) (parts : List String) : Item :=
    let whole := " ".intercalate parts
    let (text, inside) := splitSources whole.toList
    { number := n, keywords := keywords text, text := String.ofList text,
      sources := (inside.map codes).getD [] }

end Rails.RuleTextParse
