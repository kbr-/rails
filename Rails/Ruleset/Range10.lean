import Rails.Rules
import Rails.Examples
import Rails.Witness

/-!
Rules 1261 to 1403 of `tasks/agents-on-rails/RULES.md`, rule 1293 (in the sample) left out: the
formula rules in `rules`, the MAY rules as theorems, their numbers in `permissions`.
-/

namespace Rails.Ruleset.Range10
open Rails Formula Ruleset Rules Examples

/-! Event tests. -/

/-- A word among a command's words. -/
def hasW (s : String) (ws : List (List Char)) : Bool := ws.contains s.toList

/-- Some command of the call runs a program whose name ends one of `progs`, with `p` of its words. -/
def runsAny (progs : List String) (p : List (List Char) → Bool) (e : Event) : Bool :=
  (programs e).any fun (w, ws) => progs.any (fun s => endsWith s.toList w) && p ws

/-- Some word of some command of the call holds `s`. -/
def mentions (s : String) (e : Event) : Bool :=
  (programs e).any fun (_, ws) => ws.any (occursIn s.toList)

/-- An edit's path ends one of `ss`. -/
def writesEnding (ss : List String) (e : Event) : Bool :=
  match writePath e with
  | some p => ss.any fun s => endsWith s.toList p.toList
  | none => false

/-- An edit's path holds `s`. -/
def writesContaining (s : String) (e : Event) : Bool :=
  match writePath e with
  | some p => occursIn s.toList p.toList
  | none => false

/-- A read's path ends one of `ss`. -/
def readsEnding (ss : List String) (e : Event) : Bool :=
  match readPath e with
  | some p => ss.any fun s => endsWith s.toList p.toList
  | none => false

/-- The text an edit writes: an Edit's `new_string`, a Write's `content`. -/
def writtenText (e : Event) : List Char :=
  ((e.field "new_string").getD "" ++ (e.field "content").getD "").toList

/-- The instruction files whose rules are stated as direct instructions. -/
def ruleFiles : List String :=
  ["AGENTS.md", "CLAUDE.md", "SKILL.md", "TASK_PROTOCOL.md", "COMPUTATION_RULES.md", "RULES.md"]

/-- An edit of a Python file whose base name holds a hyphen. -/
def hyphenatedPython (e : Event) : Bool :=
  match writePath e with
  | some p => endsWith ".py".toList p.toList && (p.toList.reverse.takeWhile (· != '/')).contains '-'
  | none => false

/-- The diacritics of Polish. -/
def polishDiacritics : List Char := "ąćęłńóśźżĄĆĘŁŃÓŚŹŻ".toList

/-! Event predicates. -/

def shellCall : Pred := ⟨"shellCall", fun e => (command e).isSome, [bash "ls", exec "ls"]⟩
def anyCall : Pred := ⟨"anyCall", isCall, [bash "ls", read "a.md"]⟩
def anyResult : Pred := ⟨"anyResult", isResult, [.result "c" "out"]⟩
def agentStep : Pred := ⟨"agentStep", fun e => isCall e || isReply e, [bash "ls", .reply "done"]⟩
def agentText : Pred :=
  ⟨"agentText", fun e => isReply e || isThinking e, [.reply "why?", .thinking "why?"]⟩
def writesDescription : Pred := ⟨"writesDescription", writesEnding ["_MR.md", "_COMMIT.md"],
  [edit "tasks/x/FIX_MR.md", edit "tasks/x/FIX_COMMIT.md"]⟩
def writesLedger : Pred :=
  ⟨"writesLedger", writesEnding ["_EVIDENCE.md"], [edit "tasks/x/FIX_MR_EVIDENCE.md"]⟩
def writesMessage : Pred :=
  ⟨"writesMessage", writesEnding ["_MESSAGE.md"], [edit "tasks/x/private/ASK_MESSAGE.md"]⟩
def writesPrivate : Pred := ⟨"writesPrivate", writesContaining "/private/",
  [edit "tasks/x/private/ASK_MESSAGE_EVIDENCE.md"]⟩
def writesDocument : Pred := ⟨"writesDocument", writesEnding [".md"], [edit "tasks/x/NOTES.md"]⟩
def writesReviewFile : Pred := ⟨"writesReviewFile",
  fun e => writesContaining "REVIEW" e && writesEnding [".md"] e, [edit "tasks/x/MR_REVIEW.md"]⟩
def writesPlan : Pred := ⟨"writesPlan", writesEnding ["PLAN.md"], [edit "tasks/x/PLAN.md"]⟩
def editsNotebook : Pred := ⟨"editsNotebook", writesEnding ["notebook.html"], [edit "notebook.html"]⟩
def editsPaper : Pred := ⟨"editsPaper", writesEnding [".tex"], [edit "paper/main.tex"]⟩
def editsLean : Pred := ⟨"editsLean", writesEnding [".lean"], [edit "Rails/Logic.lean"]⟩
def editsPython : Pred := ⟨"editsPython", writesEnding [".py"], [edit "tools/check.py"]⟩
def editsRuleFile : Pred := ⟨"editsRuleFile", writesEnding ruleFiles, [edit "AGENTS.md"]⟩
def readsRuleFile : Pred := ⟨"readsRuleFile", readsEnding ruleFiles, [read "AGENTS.md"]⟩
def writesResultFile : Pred :=
  ⟨"writesResultFile", writesContaining "research/results/", [edit "research/results/x/out.json"]⟩
def writesHyphenatedPython : Pred :=
  ⟨"writesHyphenatedPython", hyphenatedPython, [edit "tools/my-tool.py"]⟩
def writesEmDashInDescription : Pred := ⟨"writesEmDashInDescription",
  fun e => writesEnding ["_MR.md", "_COMMIT.md"] e && (writtenText e).contains '—',
  [.call "w" "Write" [("file_path", "tasks/x/FIX_MR.md"), ("content", "a — b")]]⟩
def writesDiacriticsInMessage : Pred := ⟨"writesDiacriticsInMessage",
  fun e => writesEnding ["_MESSAGE.md"] e && (writtenText e).any polishDiacritics.contains,
  [.call "w" "Write" [("file_path", "tasks/x/private/ASK_MESSAGE.md"), ("content", "dziękuję")]]⟩
def commits : Pred := ⟨"commits", runs "git" (hasW "commit"), [bash "git commit -m fix"]⟩
def commitNoVerify : Pred := ⟨"commitNoVerify",
  runs "git" (fun ws => hasW "commit" ws && (hasW "--no-verify" ws || hasW "-n" ws)),
  [bash "git commit --no-verify -m fix", bash "git commit -n -m fix"]⟩
def runsCheckpoint : Pred := ⟨"runsCheckpoint", runs "task_checkpoint.py" (fun _ => true),
  [bash "python3 tools/task_checkpoint.py x --suite python3.12=3:40"]⟩
def runsRewrap : Pred := ⟨"runsRewrap", runsAny ["rewrap_md.py", "rewrap_comment.py"] (fun _ => true),
  [bash "python3 tools/rewrap_md.py a.md", bash "python3 tools/rewrap_comment.py a.py 10"]⟩
def runsCommentRewrap : Pred := ⟨"runsCommentRewrap", runs "rewrap_comment.py" (fun _ => true),
  [bash "python3 tools/rewrap_comment.py a.py 10"]⟩
def shellInPlaceEdit : Pred := ⟨"shellInPlaceEdit",
  fun e => runs "sed" (hasW "-i") e || runs "perl" (fun ws => hasW "-pi" ws || hasW "-i" ws) e,
  [bash "sed -i s/a/b/ f.md", bash "perl -pi -e s/a/b/ f.md"]⟩
def runsNotebookExcerpt : Pred := ⟨"runsNotebookExcerpt", runs "notebook-excerpt.py" (fun _ => true),
  [bash "python3 tools/notebook-excerpt.py entry-x --out brief.txt"]⟩
def symlinkIntoScratch : Pred := ⟨"symlinkIntoScratch",
  runs "ln" (fun ws => (hasW "-s" ws || hasW "-sf" ws || hasW "-sfn" ws) &&
    ws.any (occursIn "scratch".toList)),
  [bash "ln -s /data scratchpad/data"]⟩
def codexExec : Pred := ⟨"codexExec", isTool "exec", [exec "ls"]⟩
def runsCompute : Pred :=
  ⟨"runsCompute", runs "compute.sh" (fun _ => true), [bash "./compute.sh python3 calc.py"]⟩
def runsComputePhase : Pred := ⟨"runsComputePhase", runs "compute.sh" (hasW "phase"),
  [bash "./compute.sh phase t1 reading"]⟩
def browses : Pred := ⟨"browses", fun e => isTool "WebFetch" e || isTool "WebSearch" e,
  [.call "f" "WebFetch" [("url", "https://example.org")], .call "s" "WebSearch" [("query", "x")]]⟩
def bareTestRun : Pred := ⟨"bareTestRun",
  fun e => runsAny ["tests/run.py", "pytest"] (fun _ => true) e ||
    runs "-m" (fun ws => hasW "pytest" ws || hasW "unittest" ws) e,
  [bash "python3 tools/tests/run.py test_x", bash "pytest -q", bash "python3 -m unittest t"]⟩
def runsVenvPythonBare : Pred := ⟨"runsVenvPythonBare", runs ".venv/bin/python" (fun _ => true),
  [bash ".venv/bin/python calc.py"]⟩
def runsAria2c : Pred := ⟨"runsAria2c", runs "aria2c" (fun _ => true), [bash "aria2c https://x/f"]⟩
def aria2cDiskCache : Pred := ⟨"aria2cDiskCache",
  runs "aria2c" (fun ws => ws.any (hasPrefix "--disk-cache".toList)),
  [bash "aria2c --disk-cache=64M https://x/f"]⟩
def aria2cContinue : Pred := ⟨"aria2cContinue",
  runs "aria2c" (fun ws => hasW "-c" ws || hasW "--continue" ws), [bash "aria2c -c https://x/f"]⟩
def runsSetup : Pred :=
  ⟨"runsSetup", runs "setup.py" (fun _ => true), [bash "python3 resource-controls/setup.py"]⟩
def compilesC : Pred := ⟨"compilesC", runsAny ["gcc", "g++", "clang", "clang++", "cc", "c++"] (fun _ => true),
  [bash "gcc -O2 k.c -o k -lflint -lgmp"]⟩
def rendersPaper : Pred := ⟨"rendersPaper",
  runsAny ["latexmk", "pdflatex", "lualatex", "xelatex", "tectonic"] (fun _ => true),
  [bash "latexmk -pdf main.tex"]⟩
def runsShake : Pred := ⟨"runsShake", runs "lake" (hasW "shake"), [bash "lake shake"]⟩
def gitSwitch : Pred := ⟨"gitSwitch", runs "git" (fun ws => hasW "checkout" ws || hasW "switch" ws),
  [bash "git checkout mr-12", bash "git switch mr-12"]⟩
def worktreeAdd : Pred := ⟨"worktreeAdd", runs "git" (fun ws => hasW "worktree" ws && hasW "add" ws),
  [bash "git worktree add ../mr-12 origin/mr-12"]⟩
def worktreeRemove : Pred :=
  ⟨"worktreeRemove", runs "git" (fun ws => hasW "worktree" ws && hasW "remove" ws),
  [bash "git worktree remove ../mr-12"]⟩
def sonnetReviewer : Pred := ⟨"sonnetReviewer",
  fun e => isReviewerRun e && e.field "model" == some "sonnet",
  [.call "a" "Agent" [("subagent_type", "medium-reviewer"), ("model", "sonnet")]]⟩
def hunkLedgerProse : Pred := ⟨"hunkLedgerProse", runs "hunk_ledger.py" (hasW "prose"),
  [bash "python3 tools/hunk_ledger.py prose LEDGER.md"]⟩
def resultSaysComplete : Pred := ⟨"resultSaysComplete",
  fun e => match e with
    | .result _ out failed => !failed && occursIn "Complete".toList out.toList
    | _ => false,
  [.result "c" "Complete"]⟩
def runsScopedTests : Pred := ⟨"runsScopedTests",
  fun e => mentions "formalization/tests" e || mentions "resource-controls/test_" e,
  [bash "./compute.sh python3 resource-controls/test_watchdog.py"]⟩
def loogleCall : Pred := ⟨"loogleCall", isTool "mcp__lean-lsp__lean_loogle",
  [.call "l" "mcp__lean-lsp__lean_loogle" [("query", "List.map")]]⟩
def runCodeCall : Pred := ⟨"runCodeCall", isTool "mcp__lean-lsp__lean_run_code",
  [.call "r" "mcp__lean-lsp__lean_run_code" [("code", "#eval 1")]]⟩
def runsLeanToolingInfo : Pred := ⟨"runsLeanToolingInfo", runs "lean_tooling.py" (hasW "info"),
  [bash "python3 tools/lean_tooling.py info"]⟩

def preds : List Pred :=
  [shellCall, anyCall, anyResult, agentStep, agentText, writesDescription, writesLedger,
   writesMessage, writesPrivate, writesDocument, writesReviewFile, writesPlan, editsNotebook,
   editsPaper, editsLean, editsPython, editsRuleFile, readsRuleFile, writesResultFile,
   writesHyphenatedPython, writesEmDashInDescription, writesDiacriticsInMessage, commits,
   commitNoVerify, runsCheckpoint, runsRewrap, runsCommentRewrap, shellInPlaceEdit, runsNotebookExcerpt,
   symlinkIntoScratch, codexExec, runsCompute, runsComputePhase, browses, bareTestRun,
   runsVenvPythonBare, runsAria2c, aria2cDiskCache, aria2cContinue, runsSetup, compilesC,
   rendersPaper, runsShake, gitSwitch, worktreeAdd, worktreeRemove, sonnetReviewer,
   hunkLedgerProse, resultSaysComplete, runsScopedTests, loogleCall, runCodeCall,
   runsLeanToolingInfo]

theorem preds_wellFormed : preds.all Pred.wellFormed = true := by decide

/-! Atoms. -/

def draftsColleagueMessage : Atom := ⟨"draftsColleagueMessage",
  "Does this edit draft a message the user will send a colleague?", .edit⟩
def ledgerOfMessage : Atom := ⟨"ledgerOfMessage",
  "Is this edit the evidence ledger of a message the user will send a colleague?", .edit⟩
def leavesAbbreviationUnexpanded : Atom := ⟨"leavesAbbreviationUnexpanded",
  "Does this edit leave an abbreviation unexpanded at its first mention in the document, other than a standard one such as API, JSON, URL, ID, SQL, CI or HTTP?", .edit⟩
def vagueReference : Atom := ⟨"vagueReference",
  "Does this edit write a reference the reader can't look up or act on (\"another proof of concept\", \"some services\")?", .edit⟩
def namesPeople : Atom := ⟨"namesPeople",
  "Does this edit name a person in a document colleagues read over time?", .edit⟩
def recordsReviewRound : Atom := ⟨"recordsReviewRound",
  "Does this edit record a round of a review loop?", .edit⟩
def roundWithoutNamedHeading : Atom := ⟨"roundWithoutNamedHeading",
  "Does this edit record a review round under a heading that doesn't name the round (\"Round 3\", \"Fifteenth pass\", a fresh-context reviewer)?", .edit⟩
def statesUnneededNumber : Atom := ⟨"statesUnneededNumber",
  "Does this fix state a number its reader's decision doesn't need?", .edit⟩
def ownSuiteTimeUnlabelled : Atom := ⟨"ownSuiteTimeUnlabelled",
  "Does this checkpoint record the suite time of the target's own check under a label not ending in -own?", .call⟩
def runsOldPython : Atom := ⟨"runsOldPython",
  "Does this command run a Python interpreter older than 3.12?", .call⟩
def rewrapsByHand : Atom := ⟨"rewrapsByHand",
  "Does this edit rewrap prose or a comment by hand-placed line breaks rather than with the rewrap tool?", .edit⟩
def writesCommentParagraph : Atom := ⟨"writesCommentParagraph",
  "Does this edit write or change a paragraph of a code or configuration comment?", .edit⟩
def replacesProsePassage : Atom := ⟨"replacesProsePassage",
  "Does this edit replace a passage of prose (rather than make an exact edit) without tools/replace_text.py?", .edit⟩
def appendsEntryByHand : Atom := ⟨"appendsEntryByHand",
  "Does this edit append a research-record entry or a Proposed next step by hand?", .edit⟩
def briefQuotesNotebook : Atom := ⟨"briefQuotesNotebook",
  "Does this reviewer's brief include excerpts of the notebook?", .call⟩
def mathOutsideMathJax : Atom := ⟨"mathOutsideMathJax",
  "Does this edit write mathematical notation outside MathJax, or code formatting for something that is no program identifier or source reference?", .edit⟩
def articleMissingHeader : Atom := ⟨"articleMissingHeader",
  "Does this edit add an article lacking a stable anchor, a descriptive title, a date or a status in the active goal's vocabulary?", .edit⟩
def entryMetaTooLong : Atom := ⟨"entryMetaTooLong",
  "Does this edit write an entry-meta over 300 characters before the producer credit, or a status line holding more than the status, one scope clause and a cycle label?", .edit⟩
def numbersCycles : Atom := ⟨"numbersCycles",
  "Does this edit number a cycle (\"cycle 12\")?", .edit⟩
def entryLacksIdentifier : Atom := ⟨"entryLacksIdentifier",
  "Does this edit add an entry without an anchor, or a parallel formalization entry without its route ID, or a task entry without its task ID?", .edit⟩
def namesWithCode : Atom := ⟨"namesWithCode",
  "Does this edit name a result or another named thing with a letter code, a prime or a digit or letter suffix, or a lemma, theorem, corollary or conjecture in more than four or non-descriptive words?", .edit⟩
def unknownStatus : Atom := ⟨"unknownStatus",
  "Does this edit give an entry a status outside its goal's status values?", .edit⟩
def dutyWithoutAttribute : Atom := ⟨"dutyWithoutAttribute",
  "Does this edit state a standing per-entry duty without declaring it with data-entry-paragraphs on a living section?", .edit⟩
def commitMessageMalformed : Atom := ⟨"commitMessageMalformed",
  "Does this commit's message have a line over 100 characters, unwrapped prose, or paragraphs not separated by blank lines?", .call⟩
def writesMachinePath : Atom := ⟨"writesMachinePath",
  "Does this edit write an absolute path or a machine- or user-specific path the repository's code or records depend on?", .edit⟩
def runsOutsideRepoRoot : Atom := ⟨"runsOutsideRepoRoot",
  "Does this command run this repository's tools from outside its root?", .call⟩
def tempOutsideCodexScratch : Atom := ⟨"tempOutsideCodexScratch",
  "Does this Codex command put temporary work outside the directory tools/codex_state.py scratch gives?", .call⟩
def breaksPagesLiveMode : Atom := ⟨"breaksPagesLiveMode",
  "Does this edit drop the site's live mode or make a published revision URL absolute?", .edit⟩
def publishesBeyondSiteArtifact : Atom := ⟨"publishesBeyondSiteArtifact",
  "Does this publication upload more than the minimal artifact tools/build_pages.py --out _site builds?", .publish⟩
def overstatesTestedScope : Atom := ⟨"overstatesTestedScope",
  "Does this commit's message state a framework change as tested beyond what was run?", .call⟩
def testUsesLargeFixture : Atom := ⟨"testUsesLargeFixture",
  "Does this edit write a framework test that runs on the real repository or a large fixture rather than a small one?", .edit⟩
def repeatsRuledMistake : Atom := ⟨"repeatsRuledMistake",
  "Does this action make a mistake that a rule persisted to correct that same mistake forbids?", .any⟩
def payloadNotZstd : Atom := ⟨"payloadNotZstd",
  "Does this edit write a new result or provenance payload uncompressed where it should be zstd level 3?", .edit⟩
def rewritesArchive : Atom := ⟨"rewritesArchive",
  "Does this edit rewrite an existing evidence archive in ordinary archival?", .edit⟩
def archivesLargeOutputWhole : Atom := ⟨"archivesLargeOutputWhole",
  "Does this command store a captured output over 32 MiB other than in ordered zstd parts listed in the manifest's archived_parts, or drop a byte or split a UTF-8 character?", .call⟩
def wantsOutputWithoutTailBytes : Atom := ⟨"wantsOutputWithoutTailBytes",
  "Does this compute.sh call run a non-computation command whose output is wanted beside the launcher's lines, without --tail-bytes?", .call⟩
def unknownPhase : Atom := ⟨"unknownPhase",
  "Does this phase marker name a category the timing rules don't define, or one that doesn't fit the work it marks?", .call⟩
def workloadInWrongDirectory : Atom := ⟨"workloadInWrongDirectory",
  "Does this compute.sh call run another repository's workload from a directory other than the one it needs, or call compute.sh by other than its path?", .call⟩
def downloadsHubOtherwise : Atom := ⟨"downloadsHubOtherwise",
  "Does this command download from the Hugging Face Hub other than with hf download and the skill's file naming?", .call⟩
def reportsUnmeasuredRateLimit : Atom := ⟨"reportsUnmeasuredRateLimit",
  "Does this reply report the Hub's rate-limit caveat without having measured it?", .reply⟩
def bloatedReply : Atom := ⟨"bloatedReply",
  "Is this status report or question padded with narrative, hedging or needless caveats, unlike the user's terse imperative style?", .reply⟩
def localizesFailure : Atom := ⟨"localizesFailure",
  "Does this reply name where a failure lies?", .reply⟩
def usesConceptBeforeDefining : Atom := ⟨"usesConceptBeforeDefining",
  "Does this reply explain something complex using a concept before defining it?", .reply⟩
def copiesSiblingForRuledPart : Atom := ⟨"copiesSiblingForRuledPart",
  "Does this edit copy a sibling artifact for a part a rule already states?", .edit⟩
def ruleWithAnecdote : Atom := ⟨"ruleWithAnecdote",
  "Does this edit state a rule other than as a direct instruction, with an anecdote, citation or padding?", .edit⟩
def needlessNesting : Atom := ⟨"needlessNesting",
  "Does this edit nest or number structure where neither serves a purpose?", .edit⟩
def commandNotPasteReady : Atom := ⟨"commandNotPasteReady",
  "Does this text give a command the reader is to run other than in a fenced block, one per line?", .any⟩
def monolithicModule : Atom := ⟨"monolithicModule",
  "Does this edit put into one module code that would sensibly be split, or split a type from its methods or tightly coupled decisions?", .edit⟩
def importsUnused : Atom := ⟨"importsUnused",
  "Does this edit import something the module doesn't use?", .edit⟩
def scopesChange : Atom := ⟨"scopesChange", "Does this reply scope a change?", .reply⟩
def statesNonGoals : Atom := ⟨"statesNonGoals",
  "Does this reply state the change's non-goals?", .reply⟩
def asksOutsideParty : Atom := ⟨"asksOutsideParty",
  "Does this request ask something of someone outside the agent and the user (a colleague, another team)?", .call⟩
def runsCheckOrLinter : Atom := ⟨"runsCheckOrLinter",
  "Does this call run a check (a test, a build, a linter, a review)?", .call⟩
def proposesRiskyProcedure : Atom := ⟨"proposesRiskyProcedure",
  "Does this reply propose a risky manual operator procedure (a revert, a migration)?", .reply⟩
def readsUsersOpinionOnChange : Atom := ⟨"readsUsersOpinionOnChange",
  "Does this read open the user's opinion of a change the user asked to have reviewed independently?", .read⟩
def paraphrasesShortOutput : Atom := ⟨"paraphrasesShortOutput",
  "Does this reply paraphrase a tool output short enough to paste raw?", .reply⟩
def placesUiElement : Atom := ⟨"placesUiElement",
  "Does this edit place an element in a user interface?", .edit⟩
def claimsScheduledJobTested : Atom := ⟨"claimsScheduledJobTested",
  "Does this reply say a scheduled job was tested?", .reply⟩
def readsIrrelevantLeanReference : Atom := ⟨"readsIrrelevantLeanReference",
  "Does this read open a Lean reference unrelated to the current obstacle?", .read⟩
def searchesLeanHelpersByHand : Atom := ⟨"searchesLeanHelpersByHand",
  "Does this command search for the pinned Lean helper commands or references by hand?", .call⟩
def interpretsLoogleCoverage : Atom := ⟨"interpretsLoogleCoverage",
  "Does this reply conclude from a lean_loogle result what the library holds or lacks?", .reply⟩
def importsMisaligned : Atom := ⟨"importsMisaligned",
  "Does this lean_run_code call import other than what the target project imports?", .call⟩
def ranksByFileCounts : Atom := ⟨"ranksByFileCounts",
  "Does this reply rank design problems by file counts or method lengths rather than by how often the interface or change is exercised?", .reply⟩
def addsCostlySyntax : Atom := ⟨"addsCostlySyntax",
  "Does this edit introduce new domain syntax whose expressiveness doesn't justify its parsing, tooling and learning cost?", .edit⟩
def mismatchedComposition : Atom := ⟨"mismatchedComposition",
  "Does this edit use an extensible operation where parts and relationships are fixed and known, or fixed composition where new cases must join independently?", .edit⟩
def breaksTypeSurface : Atom := ⟨"breaksTypeSurface",
  "Does this edit change a public interface's type-argument order, constraints, inference or diagnostics without treating it as a compatibility change?", .edit⟩
def ignoresUniverseLevels : Atom := ⟨"ignoresUniverseLevels",
  "Does this Lean edit design a type without respecting universe levels?", .edit⟩
def coverLetterMisnamed : Atom := ⟨"coverLetterMisnamed",
  "Does this edit write an MR cover letter in a file not named <TOPIC>_MR.md after an existing plan document's TOPIC?", .edit⟩
def coverLetterBadTitle : Atom := ⟨"coverLetterBadTitle",
  "Does this edit title the cover letter other than with an H1 naming the feature or fix (such as \"MR:\" or \"Cover letter for\")?", .edit⟩
def commitListMalformed : Atom := ⟨"commitListMalformed",
  "Does this edit write the commit list other than flat, one bullet per commit: subject in backticks, \" -- \", short summary?", .edit⟩
def singleItemSublist : Atom := ⟨"singleItemSublist",
  "Does this edit nest a single-item sub-list under a commit entry?", .edit⟩
def versionNoteMalformed : Atom := ⟨"versionNoteMalformed",
  "Does this edit write a version note not starting with exactly v<N>: followed by one flat bullet list, or with a greeting or sign-off?", .edit⟩
def versionNoteWrongTense : Atom := ⟨"versionNoteWrongTense",
  "Does this edit write a version-note bullet not in present tense, or a verbatim request without \"As requested:\"?", .edit⟩
def versionNoteUnformatted : Atom := ⟨"versionNoteUnformatted",
  "Does this edit write a version note naming a file, setting or value outside backticks, an MR or ticket unlinked, or a commit hash?", .edit⟩
def diacriticsOutsideLabels : Atom := ⟨"diacriticsOutsideLabels",
  "Does this edit put Polish diacritics in a Polish word outside a quoted UI label or value?", .edit⟩
def questionMarkOnNonQuestion : Atom := ⟨"questionMarkOnNonQuestion",
  "Does this edit put a question mark on a sentence that is no real question?", .edit⟩
def usesChatMarkdown : Atom := ⟨"usesChatMarkdown",
  "Does this chat message use Markdown (bold, headings, numbered lists), or a - list for what is no real list?", .edit⟩
def partsNotSeparated : Atom := ⟨"partsNotSeparated",
  "Does this chat message run context, the ask, each question or a side note together without blank lines between?", .edit⟩
def overusesDoubleDash : Atom := ⟨"overusesDoubleDash",
  "Does this chat message use -- more than it needs?", .edit⟩
def identifiersNotVerbatim : Atom := ⟨"identifiersNotVerbatim",
  "Does this chat message give a command, URL or identifier other than verbatim and paste-ready, or a name from code or infrastructure outside backticks?", .edit⟩
def instructionsNotWalkthrough : Atom := ⟨"instructionsNotWalkthrough",
  "Does this message instruct a colleague other than in the second person as a walk-through saying what they should see at each step?", .edit⟩
def translatesTeamTerms : Atom := ⟨"translatesTeamTerms",
  "Does this message translate a technical term the team says in English, or avoid its colloquial shortening?", .edit⟩
def notationUndefinedAtUse : Atom := ⟨"notationUndefinedAtUse",
  "Does this edit use global notation substantially before defining it, or define local notation far from its use?", .edit⟩
def coinsNeedlessName : Atom := ⟨"coinsNeedlessName",
  "Does this edit coin a name where established terminology exists, or for a concept that doesn't recur?", .edit⟩
def internalLabelsInMath : Atom := ⟨"internalLabelsInMath",
  "Does this edit put an internal notebook label, claim code or implementation name into the mathematical vocabulary?", .edit⟩
def vagueCrossReference : Atom := ⟨"vagueCrossReference",
  "Does this edit refer to a result as \"the above lemma\" or the like where its destination could become unclear, rather than by number?", .edit⟩
def subtitlesMinorResult : Atom := ⟨"subtitlesMinorResult",
  "Does this edit give a descriptive subtitle to a result that doesn't anchor the argument?", .edit⟩
def displayNotInSentence : Atom := ⟨"displayNotInSentence",
  "Does this edit write a displayed formula not integrated and punctuated as part of a sentence?", .edit⟩
def historyInPaper : Atom := ⟨"historyInPaper",
  "Does this edit put development history or workflow administration into the paper?", .edit⟩
def symbolTableMisplaced : Atom := ⟨"symbolTableMisplaced",
  "Does this edit add a symbol table or inequality map to an argument that isn't parameter-heavy, or leave a parameter-heavy argument without one?", .edit⟩
def definitionSplit : Atom := ⟨"definitionSplit",
  "Does this edit separate a definition's object from its essential conditions, by the text or by a floating figure?", .edit⟩
def identifierBrokenAcrossPages : Atom := ⟨"identifierBrokenAcrossPages",
  "Does this edit let an exact identifier break across a page, or an attribution separate from its author list?", .edit⟩
def runningHeadNamesLaterSection : Atom := ⟨"runningHeadNamesLaterSection",
  "Does this edit let a running head name a later section on a transition page?", .edit⟩
def strandedLayout : Atom := ⟨"strandedLayout",
  "Does this edit split a short theorem statement from its hypotheses across pages, or leave a nearly empty stranded page?", .edit⟩
def graphFigureOffStyle : Atom := ⟨"graphFigureOffStyle",
  "Does this edit draw a graph figure without small round vertices, curved connections, or positions and colors stable across stages?", .edit⟩
def figureLacksKey : Atom := ⟨"figureLacksKey",
  "Does this edit add a figure without enough key to be understood alone?", .edit⟩
def addsFigure : Atom := ⟨"addsFigure", "Does this edit add or change a figure?", .edit⟩
def chatConventionsInPaper : Atom := ⟨"chatConventionsInPaper",
  "Does this edit let workplace-chat conventions govern the paper's headings, typography or rhetorical questions?", .edit⟩
def asksToAddProse : Atom := ⟨"asksToAddProse",
  "Does this review comment, on wrong prose, ask for more prose rather than the fix that removes or narrows it?", .edit⟩
def commentLacksProblemFirst : Atom := ⟨"commentLacksProblemFirst",
  "Does this review comment fail to state the problem first and the ask, as a question for one concrete tested change, in its own paragraph?", .edit⟩
def hidesOwnCause : Atom := ⟨"hidesOwnCause",
  "Does this review comment leave unsaid that our own runbook, design or code led to the defect?", .edit⟩
def commentNotStandalone : Atom := ⟨"commentNotStandalone",
  "Does this review comment depend on context it doesn't name or link?", .edit⟩
def commentUnanchored : Atom := ⟨"commentUnanchored",
  "Does this review comment lack the anchor of the line it is about?", .edit⟩
def commentNotForCompany : Atom := ⟨"commentNotForCompany",
  "Is this review comment written other than in English for any reader in the company, with an internal abbreviation unexpanded or a private reference?", .edit⟩
def commentWithoutFix : Atom := ⟨"commentWithoutFix",
  "Does this review comment withhold the command or the fix the author could use?", .edit⟩
def attachesCommand : Atom := ⟨"attachesCommand",
  "Does this review comment attach a command for its reader to run?", .edit⟩
def reviewNotInOneFile : Atom := ⟨"reviewNotInOneFile",
  "Does this edit keep a review other than in one local file ordered as each comment with its anchor, then \"Checked, no comment\", then \"Ours\"?", .edit⟩
def postsReviewComments : Atom := ⟨"postsReviewComments",
  "Does this call post review comments on a merge request?", .publish⟩
def postsAsOneReview : Atom := ⟨"postsAsOneReview",
  "Does this call post the review as one review with one diff note per comment?", .publish⟩
def commitTouchesTasks : Atom := ⟨"commitTouchesTasks",
  "Does this commit include files under tasks/?", .call⟩
def linksCompleteTask : Atom := ⟨"linksCompleteTask",
  "Does this edit link, from a living section, a complete task with no open request?", .edit⟩
def keepsCompleteTaskInStand : Atom := ⟨"keepsCompleteTaskInStand",
  "Does this edit keep a complete task in Where we stand?", .edit⟩
def exceedsLivingBudget : Atom := ⟨"exceedsLivingBudget",
  "Does this edit take a living section over its hard budget?", .edit⟩
def scopedTestsUnneeded : Atom := ⟨"scopedTestsUnneeded",
  "Does this call run formalization/tests/ or the resource-controls tests when neither formalization tooling nor those controls changed?", .call⟩
def wholeSuiteWithoutLauncher : Atom := ⟨"wholeSuiteWithoutLauncher",
  "Does this call run the whole framework suite other than as ./compute.sh --threads 1 python3 tools/tests/run.py?", .call⟩
def reportsToolOverBudget : Atom := ⟨"reportsToolOverBudget",
  "Does this result warn that compute.sh start, the finisher or resume.py took longer than its budget?", .result⟩
def servesNotebookOtherwise : Atom := ⟨"servesNotebookOtherwise",
  "Does this command serve the live notebook other than with python3 server.py?", .call⟩
def resolvesMdConflictByHand : Atom := ⟨"resolvesMdConflictByHand",
  "Does this edit resolve a merge conflict in wrapped Markdown by hand rather than with tools/merge_md_words.py?", .edit⟩
def omitsStatedLinkFlags : Atom := ⟨"omitsStatedLinkFlags",
  "Does this command link a kernel against fflas-ffpack, FLINT or LinBox without the flags the computation rules state?", .call⟩
def diskCacheOverLimit : Atom := ⟨"diskCacheOverLimit",
  "Does this aria2c call pass a --disk-cache above aria2c's limit?", .call⟩
def resumesDownload : Atom := ⟨"resumesDownload",
  "Does this aria2c call resume an interrupted download?", .call⟩
def untimedIndirectCall : Atom := ⟨"untimedIndirectCall",
  "Does this command run a framework CLI command outside the automatic hooks or behind dynamic shell indirection without tools/tool_runtime.py?", .call⟩
def inspectsJobOtherwise : Atom := ⟨"inspectsJobOtherwise",
  "Does this command inspect a running job or its samples other than with tools/job_metrics.py inspect or summarize?", .call⟩
def setupOutsideProject : Atom := ⟨"setupOutsideProject",
  "Does this call run resource-controls/setup.py from outside the project directory?", .call⟩
def longRunWithoutBridge : Atom := ⟨"longRunWithoutBridge",
  "Does this Codex call start a run that may take over a minute without the native background bridge?", .call⟩
def shmOverBudget : Atom := ⟨"shmOverBudget",
  "Does this command set a Pod's /dev/shm use above 352 GB on a 755 GB Pod?", .call⟩
def reliesOnPageCacheDrop : Atom := ⟨"reliesOnPageCacheDrop",
  "Does this rely on a container dropping the host's page cache?", .any⟩
def cookieFileMisplaced : Atom := ⟨"cookieFileMisplaced",
  "Does this command write a cookie file other than at ~/.cache/cookies-HOST.json, or readable by others than its owner?", .call⟩
def addsOrChangesRule : Atom := ⟨"addsOrChangesRule", "Does this edit add or change a rule?", .edit⟩
def scriptNamedGenerically : Atom := ⟨"scriptNamedGenerically",
  "Does this edit give a script serving one library, tool or service a generic name, or generic code a specific one?", .edit⟩
def usesLovely : Atom := ⟨"usesLovely",
  "Does this message use a word like \"lovely\" where \"great observation\" or \"nice observation\" belongs?", .edit⟩
def refersToPaperNonNeutrally : Atom := ⟨"refersToPaperNonNeutrally",
  "Does this message refer to the paper's content other than neutrally (\"the arguments presented in the paper I sent you\")?", .edit⟩
def proseNotConnected : Atom := ⟨"proseNotConnected",
  "Does this edit write other than connected prose in a plain, patient register with varied sentence length and inclusive \"we\"?", .edit⟩
def reassuresOrPraisesReader : Atom := ⟨"reassuresOrPraisesReader",
  "Does this edit reassure the reader about ease, simulate intimacy or praise the reader?", .edit⟩
def announcesTeachingChoice : Atom := ⟨"announcesTeachingChoice",
  "Does this edit announce a teaching choice or add an assurance such as \"that is intentional\"?", .edit⟩
def losesAuthorsHumor : Atom := ⟨"losesAuthorsHumor",
  "Does this edit drop the author's humor or rhythm?", .edit⟩
def forcesJoke : Atom := ⟨"forcesJoke", "Does this edit force or announce a joke?", .edit⟩
def fillsHumorQuota : Atom := ⟨"fillsHumorQuota",
  "Does this edit add humor to fill a quota?", .edit⟩
def addsDecorativeHook : Atom := ⟨"addsDecorativeHook",
  "Does this edit add a tagline, teaching diagram or rhetorical question merely to make a page seem inviting?", .edit⟩
def captionRecitesPicture : Atom := ⟨"captionRecitesPicture",
  "Does this edit write a caption reciting what is visible or announcing how the picture helps, rather than adding mathematical context?", .edit⟩
def reusesGlobalSymbolAsIndex : Atom := ⟨"reusesGlobalSymbolAsIndex",
  "Does this edit use a nearby global symbol as a local summation index?", .edit⟩
def neglectsTypography : Atom := ⟨"neglectsTypography",
  "Does this edit leave the paper's typography, spacing or color unconsidered or unrestrained?", .edit⟩
def switchesUsersCheckout : Atom := ⟨"switchesUsersCheckout",
  "Does this command switch the user's own checkout to another branch?", .call⟩
def checksOutMergeRequest : Atom := ⟨"checksOutMergeRequest",
  "Does this command check out a merge request's head for review?", .call⟩
def runsHunkLedgerPhase : Atom := ⟨"runsHunkLedgerPhase",
  "Does this reviewer run the hunk-ledger phase of a merge request review?", .call⟩
def briefHoldsTaskRecords : Atom := ⟨"briefHoldsTaskRecords",
  "Does this reviewer's brief give it the task's records?", .call⟩
def briefTakesCommitsOutOfOrder : Atom := ⟨"briefTakesCommitsOutOfOrder",
  "Does this reviewer's brief take the commits other than in order?", .call⟩
def ledgerRowOutOfOrder : Atom := ⟨"ledgerRowOutOfOrder",
  "Does this edit write a hunk-ledger row without Does, Context and Findings before the failure-mode list?", .edit⟩
def delegatesLedgerRows : Atom := ⟨"delegatesLedgerRows",
  "Does this reviewer run ask another agent to write the hunk ledger's rows?", .call⟩
def startsNextLedgerUnit : Atom := ⟨"startsNextLedgerUnit",
  "Does this edit start the next unit of a hunk ledger?", .edit⟩
def marksUnitRevisit : Atom := ⟨"marksUnitRevisit",
  "Does this edit mark a hunk-ledger unit Revisit?", .edit⟩
def addsHunkFindings : Atom := ⟨"addsHunkFindings",
  "Does this edit add the hunk ledger's findings to the review draft?", .edit⟩
def rereviewFindingUnmarked : Atom := ⟨"rereviewFindingUnmarked",
  "Does this edit record a re-review finding not marked Miss or New, or a miss without its cause and fix?", .edit⟩

/-! Links. -/

def ledgerOfDescription : Link := ⟨"ledgerOfDescription",
  "Is this edit the evidence ledger beside the anchored description?"⟩
def correctsThisMistake : Link := ⟨"correctsThisMistake",
  "Does this message from the user explicitly correct a mistake of the kind the anchored action makes?"⟩
def comparesWithReference : Link := ⟨"comparesWithReference",
  "Does this command compare the failure the anchored reply localizes against a known-good reference environment?"⟩
def pendingAskSameParty : Link := ⟨"pendingAskSameParty",
  "Is this earlier request a still-pending ask to the same outside party that the anchored request could have joined?"⟩
def checkedActionHasNoDiff : Link := ⟨"checkedActionHasNoDiff",
  "Is this call an action with no file-content diff (a commit reword, an edit of a comment nothing reads, a branch rename) that the anchored check is run for?"⟩
def runbookForProcedure : Link := ⟨"runbookForProcedure",
  "Is this edit a runbook of the risks, steps and test of the procedure the anchored reply proposes?"⟩
def formsOwnJudgement : Link := ⟨"formsOwnJudgement",
  "Does this reply state the agent's own judgement of the change whose user opinion the anchored read opens?"⟩
def settlesUiAudience : Link := ⟨"settlesUiAudience",
  "Does this message settle who sees the element the anchored edit places?"⟩
def triggersJobDirectly : Link := ⟨"triggersJobDirectly",
  "Does this command trigger directly the scheduled job the anchored reply says was tested?"⟩
def checksLoogleRoot : Link := ⟨"checksLoogleRoot",
  "Does this call check the configured root module of the lean_loogle search the anchored reply interprets?"⟩
def testOfProcedure : Link := ⟨"testOfProcedure",
  "Is this edit a test of the procedure the anchored reply proposes?"⟩
def readsWholeEditedFile : Link := ⟨"readsWholeEditedFile",
  "Does this read open, end to end, the rule file the anchored edit changes?"⟩
def testsCommandOnStandIn : Link := ⟨"testsCommandOnStandIn",
  "Does this command test, on the nearest stand-in, the command the anchored comment attaches?"⟩
def confirmsCommentsLanded : Link := ⟨"confirmsCommentsLanded",
  "Does this command confirm that each comment the anchored call posted landed on its line?"⟩
def recordsPostingTime : Link := ⟨"recordsPostingTime",
  "Does this edit record in the review draft when the anchored review was posted?"⟩
def updatesPlanForPosting : Link := ⟨"updatesPlanForPosting",
  "Does this edit update the task's plan and requests for the review the anchored call posted?"⟩
def fixesSlowCause : Link := ⟨"fixesSlowCause",
  "Does this edit fix the cause of the slowness the anchored result warns of?"⟩
def inspectsFigureAtReadingSize : Link := ⟨"inspectsFigureAtReadingSize",
  "Does this read inspect, at actual reading size, the figure the anchored edit adds?"⟩
def sameHunkLedgerPhase : Link := ⟨"sameHunkLedgerPhase",
  "Is this reviewer run part of the same hunk-ledger phase as the anchored one?"⟩
def raisesQuickQuestion : Link := ⟨"raisesQuickQuestion",
  "Does this text raise a question, about the unit before the anchored one, that a check of a few minutes answers?"⟩
def settlesQuickQuestion : Link := ⟨"settlesQuickQuestion",
  "Does this call settle a quick question raised about the unit before the anchored one?"⟩
def findsKnowledgeForLaterUnits : Link := ⟨"findsKnowledgeForLaterUnits",
  "Does this text find something, about the unit before the anchored one, that later units need?"⟩
def recordsKnowledge : Link := ⟨"recordsKnowledge",
  "Does this edit write under Knowledge what the unit before the anchored one found that later units need?"⟩
def rereadsRevisitUnit : Link := ⟨"rereadsRevisitUnit",
  "Does this read reread the unit the anchored edit marks Revisit?"⟩
def answersListedClaims : Link := ⟨"answersListedClaims",
  "Does this edit check each scope claim and accepted limit the anchored hunk_ledger.py prose call lists?"⟩
def resultOfHunkLedgerCheck : Link := ⟨"resultOfHunkLedgerCheck",
  "Is this result the output of hunk_ledger.py check on the ledger whose findings the anchored edit adds?"⟩

/-! Formula shapes. -/

/-- A judgement of one event: no event `p` of which the model answers `a` yes. -/
def judged (p : Pred) (a : Atom) : Formula := never (ev p ∧ₗ atom a)

/-- A SHOULD rule's judgement of one event: an event `p` of which `a` holds needs a reason. -/
def unlessJustified (p : Pred) (a : Atom) : Formula := ev p ∧ₗ atom a ⟹ atom justified

/-! The rules. -/

/-- Rule 1261: no description without its ledger beside it, written first. -/
def descriptionNeedsLedger : Rule where
  number := 1261
  keyword := .mustNot
  domain := .tasks
  formula := ev writesDescription ⟹ once (ev writesLedger ∧ₗ link ledgerOfDescription)

/-- Rule 1262: a message is drafted in `<NAME>_MESSAGE.md`, its ledger in `private/`. -/
def messageFileNaming : Rule where
  number := 1262
  keyword := .must
  domain := .tasks
  formula := never (ev writesDocument ∧ₗ atom draftsColleagueMessage ∧ₗ ¬ₗ ev writesMessage) ∧ₗ
    never (ev writesLedger ∧ₗ atom ledgerOfMessage ∧ₗ ¬ₗ ev writesPrivate)

/-- Rule 1263: abbreviations expanded, no vague references or people's names in documents. -/
def documentReferences : Rule where
  number := 1263
  keyword := .must
  domain := .discipline
  formula := never (ev writesDocument ∧ₗ
    (atom leavesAbbreviationUnexpanded ∨ₗ atom vagueReference ∨ₗ atom namesPeople))

/-- Rule 1264: review rounds only in a `*REVIEW*.md`, each under a heading naming it. -/
def reviewRoundsInReviewFile : Rule where
  number := 1264
  keyword := .must
  domain := .tasks
  formula := never (ev writesDocument ∧ₗ atom recordsReviewRound ∧ₗ ¬ₗ ev writesReviewFile) ∧ₗ
    judged writesReviewFile roundWithoutNamedHeading

/-- Rule 1265: a fix states a number only where its reader's decision needs it. -/
def noNeedlessNumberInFix : Rule where
  number := 1265
  keyword := .mustNot
  domain := .tasks
  formula := never (ev editing ∧ₗ atom isFix ∧ₗ atom statesUnneededNumber)

/-- Rule 1266: the target's own suite time under a label ending `-own`. -/
def ownSuiteLabel : Rule where
  number := 1266
  keyword := .must
  domain := .tasks
  formula := judged runsCheckpoint ownSuiteTimeUnlabelled

/-- Rule 1267: Python 3.12 or later. -/
def recentPython : Rule where
  number := 1267
  keyword := .must
  domain := .softwareEngineering
  formula := judged shellCall runsOldPython

/-- Rule 1268: every Markdown file written is rewrapped by the tool, a code comment's paragraph by
`tools/rewrap_comment.py`, never by hand. -/
def rewrapWithTool : Rule where
  number := 1268
  keyword := .must
  domain := .softwareEngineering
  formula := (ev writesDocument ⟹ eventually (ev runsRewrap)) ∧ₗ
    (ev editing ∧ₗ atom writesCommentParagraph ⟹ eventually (ev runsCommentRewrap)) ∧ₗ
    judged editing rewrapsByHand

/-- Rule 1269: prose passages through `tools/replace_text.py`, exact edits with the editing tool. -/
def proseReplacedByTool : Rule where
  number := 1269
  keyword := .must
  domain := .softwareEngineering
  formula := judged editing replacesProsePassage ∧ₗ never (ev shellInPlaceEdit)

/-- Rule 1270: entries appended with `notebook-append.py`, reviewer excerpts built with
`notebook-excerpt.py`. -/
def notebookTools : Rule where
  number := 1270
  keyword := .must
  domain := .mathematics
  formula := judged editsNotebook appendsEntryByHand ∧ₗ
    (ev reviewerRun ∧ₗ atom briefQuotesNotebook ⟹ once (ev runsNotebookExcerpt))

/-- Rule 1271: MathJax for mathematics, code formatting for identifiers only. -/
def mathJaxForMath : Rule where
  number := 1271
  keyword := .must
  domain := .mathematics
  formula := judged editsNotebook mathOutsideMathJax

/-- Rule 1272: each article with anchor, title, date and status. -/
def articleHeader : Rule where
  number := 1272
  keyword := .must
  domain := .mathematics
  formula := judged editsNotebook articleMissingHeader

/-- Rule 1273: entry-meta within 300 characters, a short status line. -/
def shortEntryMeta : Rule where
  number := 1273
  keyword := .must
  domain := .mathematics
  formula := judged editsNotebook entryMetaTooLong

/-- Rule 1274: no cycle numbers; anchors, route IDs and task IDs instead. -/
def noCycleNumbers : Rule where
  number := 1274
  keyword := .mustNot
  domain := .mathematics
  formula := judged editsNotebook numbersCycles ∧ₗ judged editsNotebook entryLacksIdentifier

/-- Rule 1275: descriptive names, never codes. -/
def descriptiveNames : Rule where
  number := 1275
  keyword := .must
  domain := .discipline
  formula := judged editing namesWithCode

/-- Rule 1276: only the goal's status values. -/
def knownStatusValues : Rule where
  number := 1276
  keyword := .must
  domain := .tasks
  formula := judged editsNotebook unknownStatus

/-- Rule 1277: a standing per-entry duty declared with `data-entry-paragraphs`. -/
def dutyDeclared : Rule where
  number := 1277
  keyword := .must
  domain := .mathematics
  formula := judged editsNotebook dutyWithoutAttribute

/-- Rule 1278: commit-message lines within 100 characters, wrapped, paragraphs separated. -/
def commitMessageShape : Rule where
  number := 1278
  keyword := .must
  domain := .softwareEngineering
  formula := judged commits commitMessageMalformed

/-- Rule 1279: from the repository root, with no machine, user or absolute path. -/
def portablePaths : Rule where
  number := 1279
  keyword := .must
  domain := .softwareEngineering
  formula := judged editing writesMachinePath ∧ₗ judged shellCall runsOutsideRepoRoot

/-- Rule 1280: no symlink inside managed scratch. -/
def noScratchSymlink : Rule where
  number := 1280
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev symlinkIntoScratch)

/-- Rule 1281: Codex's temporary work in its owned scratch directory. -/
def codexScratch : Rule where
  number := 1281
  keyword := .must
  domain := .softwareEngineering
  formula := judged codexExec tempOutsideCodexScratch

/-- Rule 1282: live mode and relative revision URLs kept; only the minimal site artifact published. -/
def pagesArtifact : Rule where
  number := 1282
  keyword := .must
  domain := .softwareEngineering
  formula := judged editing breaksPagesLiveMode ∧ₗ judged publish publishesBeyondSiteArtifact

/-- Rule 1283: a framework change's tested scope stated accurately, its tests on small fixtures. -/
def accurateTestedScope : Rule where
  number := 1283
  keyword := .must
  domain := .softwareEngineering
  formula := judged commits overstatesTestedScope ∧ₗ judged editing testUsesLargeFixture

/-- Rule 1284: no mistake repeated after the user corrected it, or a rule persisted against it. -/
def noRepeatedMistake : Rule where
  number := 1284
  keyword := .mustNot
  domain := .discipline
  formula := never (ev agentStep ∧ₗ
    (once (ev user ∧ₗ link correctsThisMistake) ∨ₗ atom repeatsRuledMistake))

/-- Rule 1285: new payloads in zstd, no existing archive rewritten. -/
def zstdPayloads : Rule where
  number := 1285
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesResultFile payloadNotZstd ∧ₗ judged editing rewritesArchive

/-- Rule 1286: outputs over 32 MiB in ordered zstd parts. -/
def largeOutputParts : Rule where
  number := 1286
  keyword := .must
  domain := .softwareEngineering
  formula := judged shellCall archivesLargeOutputWhole

/-- Rule 1287: `--tail-bytes N` to see a non-computation run's output. -/
def tailBytes : Rule where
  number := 1287
  keyword := .must
  domain := .softwareEngineering
  formula := judged runsCompute wantsOutputWithoutTailBytes

/-- Rule 1288: the defined phase categories, the work phase restored after browsing: the first call
after a browse that is neither a browse nor a phase marker has a phase marker between it and the
browse. -/
def phaseCategories : Rule where
  number := 1288
  keyword := .must
  domain := .discipline
  formula := judged runsComputePhase unknownPhase ∧ₗ
    (ev anyCall ∧ₗ ¬ₗ ev browses ∧ₗ ¬ₗ ev runsComputePhase ⟹
      ¬ₗ since (ev browses) (ev runsComputePhase))

/-- Rule 1289: a project venv's interpreter through the launcher. -/
def venvThroughLauncher : Rule where
  number := 1289
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev runsVenvPythonBare)

/-- Rule 1290: another repository's workload from its directory, `compute.sh` by its path. -/
def otherRepositoryWorkload : Rule where
  number := 1290
  keyword := .must
  domain := .softwareEngineering
  formula := judged runsCompute workloadInWrongDirectory

/-- Rule 1291: Hub downloads with `hf download`, the rate-limit caveat only as measured. -/
def hubDownloads : Rule where
  number := 1291
  keyword := .should
  domain := .softwareEngineering
  formula := ev shellCall ∧ₗ atom downloadsHubOtherwise ∨ₗ ev reply ∧ₗ atom reportsUnmeasuredRateLimit ⟹
    atom justified

/-- Rule 1292: terse, imperative status reports and questions. -/
def terseReplies : Rule where
  number := 1292
  keyword := .should
  domain := .discipline
  formula := unlessJustified reply bloatedReply

/-- Rule 1294: a failure localized against a known-good reference environment. -/
def compareWithReference : Rule where
  number := 1294
  keyword := .should
  domain := .discipline
  formula := ev reply ∧ₗ atom localizesFailure ⟹ once (ev shellCall ∧ₗ link comparesWithReference) ∨ₗ
    atom justified

/-- Rule 1295: complex explanations bottom-up. -/
def bottomUpExplanation : Rule where
  number := 1295
  keyword := .should
  domain := .discipline
  formula := unlessJustified reply usesConceptBeforeDefining

/-- Rule 1296: a sibling copied only for what no rule states. -/
def siblingOnlyWhereUnruled : Rule where
  number := 1296
  keyword := .should
  domain := .discipline
  formula := unlessJustified editing copiesSiblingForRuledPart

/-- Rule 1298: rules as direct instructions. -/
def directRules : Rule where
  number := 1298
  keyword := .must
  domain := .discipline
  formula := judged editsRuleFile ruleWithAnecdote

/-- Rule 1299: flat structure unless nesting or numbering serves a purpose. -/
def flatStructure : Rule where
  number := 1299
  keyword := .should
  domain := .discipline
  formula := unlessJustified writesDocument needlessNesting

/-- Rule 1300: commands paste-ready, in fenced blocks, one per line. -/
def pasteReadyCommands : Rule where
  number := 1300
  keyword := .must
  domain := .discipline
  formula := never ((ev reply ∨ₗ ev writesDocument) ∧ₗ atom commandNotPasteReady)

/-- Rule 1301: modules from the first line where splitting makes sense. -/
def modulesFromStart : Rule where
  number := 1301
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified editing monolithicModule

/-- Rule 1302: only used imports; the unused-import analyser after a Lean edit. -/
def onlyUsedImports : Rule where
  number := 1302
  keyword := .must
  domain := .softwareEngineering
  formula := judged editing importsUnused ∧ₗ
    (ev editsLean ⟹ eventually (ev runsShake) ∨ₗ atom justified)

/-- Rule 1303: Python file names with underscores. -/
def underscoredPythonNames : Rule where
  number := 1303
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev writesHyphenatedPython)

/-- Rule 1305: non-goals stated when scoping a change. -/
def statedNonGoals : Rule where
  number := 1305
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom scopesChange ⟹ atom statesNonGoals ∨ₗ atom justified

/-- Rule 1306: pending external asks batched into one request. -/
def batchedExternalAsks : Rule where
  number := 1306
  keyword := .should
  domain := .tasks
  formula := ev requestAdd ∧ₗ atom asksOutsideParty ⟹
    ¬ₗ once (ev requestAdd ∧ₗ link pendingAskSameParty) ∨ₗ atom justified

/-- Rule 1307: no check run for an action with no file-content diff. -/
def noCheckWithoutDiff : Rule where
  number := 1307
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev anyCall ∧ₗ atom runsCheckOrLinter ∧ₗ once (ev anyCall ∧ₗ link checkedActionHasNoDiff))

/-- Rule 1308: a risky manual procedure gets a runbook and a test. -/
def runbookForRiskyProcedure : Rule where
  number := 1308
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom proposesRiskyProcedure ⟹
    eventually (ev editing ∧ₗ link runbookForProcedure) ∧ₗ eventually (ev editing ∧ₗ link testOfProcedure) ∨ₗ
    atom justified

/-- Rule 1309: one's own judgement of a change before reading the user's. -/
def ownJudgementFirst : Rule where
  number := 1309
  keyword := .should
  domain := .discipline
  formula := ev reading ∧ₗ atom readsUsersOpinionOnChange ⟹
    once (ev reply ∧ₗ link formsOwnJudgement) ∨ₗ atom justified

/-- Rule 1310: short raw tool output pasted. -/
def pasteRawOutput : Rule where
  number := 1310
  keyword := .should
  domain := .discipline
  formula := unlessJustified reply paraphrasesShortOutput

/-- Rule 1311: who sees a UI element settled before it is placed. -/
def uiAudienceFirst : Rule where
  number := 1311
  keyword := .must
  domain := .softwareEngineering
  formula := ev editing ∧ₗ atom placesUiElement ⟹ once ((ev reply ∨ₗ ev user) ∧ₗ link settlesUiAudience)

/-- Rule 1312: a scheduled job tested by triggering it directly. -/
def triggerScheduledJob : Rule where
  number := 1312
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom claimsScheduledJobTested ⟹
    once (ev shellCall ∧ₗ link triggersJobDirectly) ∨ₗ atom justified

/-- Rule 1313: only the Lean references relevant to the obstacle. -/
def relevantLeanReferences : Rule where
  number := 1313
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified reading readsIrrelevantLeanReference

/-- Rule 1314: `tools/lean_tooling.py info` locates the pinned helpers. -/
def leanToolingInfo : Rule where
  number := 1314
  keyword := .should
  domain := .softwareEngineering
  formula := ev shellCall ∧ₗ atom searchesLeanHelpersByHand ⟹ once (ev runsLeanToolingInfo) ∨ₗ
    atom justified

/-- Rule 1315: lean_loogle's root module checked before its coverage is read. -/
def loogleRootChecked : Rule where
  number := 1315
  keyword := .should
  domain := .softwareEngineering
  formula := ev reply ∧ₗ atom interpretsLoogleCoverage ⟹
    once (ev loogleCall) ∧ₗ once (ev anyCall ∧ₗ link checksLoogleRoot) ∨ₗ atom justified

/-- Rule 1316: lean_run_code's imports aligned with the project. -/
def runCodeImports : Rule where
  number := 1316
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified runCodeCall importsMisaligned

/-- Rule 1317: frequently exercised interfaces first. -/
def frequentInterfacesFirst : Rule where
  number := 1317
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified reply ranksByFileCounts

/-- Rule 1318: new domain syntax only when worth its cost. -/
def syntaxWorthItsCost : Rule where
  number := 1318
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified editing addsCostlySyntax

/-- Rule 1319: fixed composition for known parts, an extensible operation for joining cases. -/
def fittingComposition : Rule where
  number := 1319
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified editing mismatchedComposition

/-- Rule 1320: inference, diagnostics and type arguments as interface. -/
def typeSurfaceAsInterface : Rule where
  number := 1320
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified editing breaksTypeSurface

/-- Rule 1321: universe levels respected in Lean types. -/
def universeLevels : Rule where
  number := 1321
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified editsLean ignoresUniverseLevels

/-- Rule 1322: the cover letter named `<TOPIC>_MR.md` after its plan document. -/
def coverLetterName : Rule where
  number := 1322
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesDocument coverLetterMisnamed

/-- Rule 1323: the cover letter's H1 names the feature or fix. -/
def coverLetterTitle : Rule where
  number := 1323
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesDescription coverLetterBadTitle

/-- Rule 1324: a flat commit list. -/
def flatCommitList : Rule where
  number := 1324
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesDescription commitListMalformed

/-- Rule 1325: no single-item sub-list under a commit entry. -/
def noSingleItemSublist : Rule where
  number := 1325
  keyword := .mustNot
  domain := .softwareEngineering
  formula := judged writesDescription singleItemSublist

/-- Rule 1326: no em dash in a cover letter. -/
def noEmDash : Rule where
  number := 1326
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never (ev writesEmDashInDescription)

/-- Rule 1327: a version note starts `v<N>:` with one flat list. -/
def versionNoteShape : Rule where
  number := 1327
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesDescription versionNoteMalformed

/-- Rule 1328: version-note bullets in present tense, "As requested:" for verbatim requests. -/
def versionNoteTense : Rule where
  number := 1328
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesDescription versionNoteWrongTense

/-- Rule 1329: version-note names in backticks, MRs and tickets linked, no hashes. -/
def versionNoteFormatting : Rule where
  number := 1329
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesDescription versionNoteUnformatted

/-- Rule 1330: no Polish diacritics in chat messages, save quoted labels. -/
def noPolishDiacritics : Rule where
  number := 1330
  keyword := .mustNot
  domain := .discipline
  formula := judged writesDiacriticsInMessage diacriticsOutsideLabels

/-- Rule 1331: a question mark only on a real question. -/
def realQuestionMarks : Rule where
  number := 1331
  keyword := .must
  domain := .discipline
  formula := judged writesMessage questionMarkOnNonQuestion

/-- Rule 1332: no Markdown in chat messages. -/
def noChatMarkdown : Rule where
  number := 1332
  keyword := .mustNot
  domain := .discipline
  formula := judged writesMessage usesChatMarkdown

/-- Rule 1333: blank lines between a chat message's parts. -/
def separatedChatParts : Rule where
  number := 1333
  keyword := .must
  domain := .discipline
  formula := judged writesMessage partsNotSeparated

/-- Rule 1334: `--` kept to a minimum in chat messages. -/
def fewDoubleDashes : Rule where
  number := 1334
  keyword := .should
  domain := .discipline
  formula := unlessJustified writesMessage overusesDoubleDash

/-- Rule 1335: commands, URLs and identifiers verbatim. -/
def verbatimIdentifiers : Rule where
  number := 1335
  keyword := .must
  domain := .discipline
  formula := judged writesMessage identifiersNotVerbatim

/-- Rule 1336: instructions to colleagues as a second-person walk-through. -/
def walkthroughInstructions : Rule where
  number := 1336
  keyword := .must
  domain := .discipline
  formula := judged writesMessage instructionsNotWalkthrough

/-- Rule 1337: the team's English terms and shortenings kept. -/
def teamTerms : Rule where
  number := 1337
  keyword := .should
  domain := .discipline
  formula := unlessJustified writesMessage translatesTeamTerms

/-- Rule 1338: notation defined before use, local notation near it. -/
def notationDefined : Rule where
  number := 1338
  keyword := .must
  domain := .mathematics
  formula := judged editsPaper notationUndefinedAtUse

/-- Rule 1339: established terminology, new names only where they help. -/
def establishedTerminology : Rule where
  number := 1339
  keyword := .must
  domain := .mathematics
  formula := judged editsPaper coinsNeedlessName

/-- Rule 1340: no internal labels in the mathematical vocabulary. -/
def noInternalLabels : Rule where
  number := 1340
  keyword := .must
  domain := .mathematics
  formula := judged editsPaper internalLabelsInMath

/-- Rule 1341: numbered references where the destination could become unclear. -/
def numberedReferences : Rule where
  number := 1341
  keyword := .must
  domain := .mathematics
  formula := judged editsPaper vagueCrossReference

/-- Rule 1342: subtitles only for anchoring results. -/
def fewSubtitles : Rule where
  number := 1342
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper subtitlesMinorResult

/-- Rule 1343: displayed formulas as parts of sentences. -/
def displaysInSentences : Rule where
  number := 1343
  keyword := .must
  domain := .mathematics
  formula := judged editsPaper displayNotInSentence

/-- Rule 1344: no development history in the paper. -/
def noHistoryInPaper : Rule where
  number := 1344
  keyword := .must
  domain := .mathematics
  formula := judged editsPaper historyInPaper

/-- Rule 1345: a symbol table only, and always, for parameter-heavy arguments. -/
def symbolTableWhereHeavy : Rule where
  number := 1345
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper symbolTableMisplaced

/-- Rule 1346: a definition kept with its conditions; no floating figure between them. -/
def definitionWithConditions : Rule where
  number := 1346
  keyword := .must
  domain := .mathematics
  formula := judged editsPaper definitionSplit

/-- Rule 1347: identifiers intact across pages, attributions with their authors. -/
def intactIdentifiers : Rule where
  number := 1347
  keyword := .must
  domain := .mathematics
  formula := judged editsPaper identifierBrokenAcrossPages

/-- Rule 1348: no running head naming a later section; the rendered result checked. -/
def runningHeads : Rule where
  number := 1348
  keyword := .mustNot
  domain := .mathematics
  formula := judged editsPaper runningHeadNamesLaterSection ∧ₗ
    (ev editsPaper ⟹ eventually (ev rendersPaper))

/-- Rule 1349: short statements on one page, no stranded pages. -/
def pageLayout : Rule where
  number := 1349
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper strandedLayout

/-- Rule 1350: graph figures in the stated style. -/
def graphFigureStyle : Rule where
  number := 1350
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper graphFigureOffStyle

/-- Rule 1351: figures inspected at reading size, with enough key. -/
def figuresInspected : Rule where
  number := 1351
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper figureLacksKey ∧ₗ
    (ev editsPaper ∧ₗ atom addsFigure ⟹
      eventually (ev reading ∧ₗ link inspectsFigureAtReadingSize) ∨ₗ atom justified)

/-- Rule 1352: no workplace-chat conventions in a paper. -/
def noChatConventionsInPaper : Rule where
  number := 1352
  keyword := .mustNot
  domain := .mathematics
  formula := judged editsPaper chatConventionsInPaper

/-- Rule 1353: on wrong prose, ask for the fix that removes or narrows it. -/
def removeWrongProse : Rule where
  number := 1353
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified writesReviewFile asksToAddProse

/-- Rule 1354: the problem first, then the ask, in its own paragraph. -/
def problemThenAsk : Rule where
  number := 1354
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesReviewFile commentLacksProblemFirst

/-- Rule 1355: say so when our own runbook, design or code led to the defect. -/
def ownCauseStated : Rule where
  number := 1355
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesReviewFile hidesOwnCause

/-- Rule 1356: each comment stands alone. -/
def standaloneComments : Rule where
  number := 1356
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesReviewFile commentNotStandalone

/-- Rule 1357: each comment anchored to its line. -/
def anchoredComments : Rule where
  number := 1357
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesReviewFile commentUnanchored

/-- Rule 1358: comments in English for any reader in the company. -/
def companyReadableComments : Rule where
  number := 1358
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesReviewFile commentNotForCompany

/-- Rule 1359: the command or the fix given. -/
def commentGivesFix : Rule where
  number := 1359
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified writesReviewFile commentWithoutFix

/-- Rule 1360: an attached command tested on the nearest stand-in first. -/
def attachedCommandTested : Rule where
  number := 1360
  keyword := .must
  domain := .softwareEngineering
  formula := ev writesReviewFile ∧ₗ atom attachesCommand ⟹
    once (ev shellCall ∧ₗ link testsCommandOnStandIn)

/-- Rule 1361: the review in one local file, in its order. -/
def reviewInOneFile : Rule where
  number := 1361
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesDocument reviewNotInOneFile

/-- Rule 1362: posted as one review, each comment then confirmed on its line. -/
def postedAsOneReview : Rule where
  number := 1362
  keyword := .must
  domain := .softwareEngineering
  formula := ev publish ∧ₗ atom postsReviewComments ⟹
    atom postsAsOneReview ∧ₗ eventually (ev shellCall ∧ₗ link confirmsCommentsLanded)

/-- Rule 1363: the posting recorded in the draft, the plan and requests updated. -/
def postingRecorded : Rule where
  number := 1363
  keyword := .must
  domain := .softwareEngineering
  formula := ev publish ∧ₗ atom postsReviewComments ⟹
    eventually (ev writesReviewFile ∧ₗ link recordsPostingTime) ∧ₗ
    eventually (ev writesPlan ∧ₗ link updatesPlanForPosting)

/-- Rule 1364: the pre-commit task check never bypassed on commits under `tasks/`. -/
def noTaskCheckBypass : Rule where
  number := 1364
  keyword := .mustNot
  domain := .tasks
  formula := judged commitNoVerify commitTouchesTasks

/-- Rule 1365: living sections link no closed task, hold none in Where we stand, keep budget. -/
def livingSectionsCurrent : Rule where
  number := 1365
  keyword := .mustNot
  domain := .tasks
  formula := never (ev editsNotebook ∧ₗ
    (atom linksCompleteTask ∨ₗ atom keepsCompleteTaskInStand ∨ₗ atom exceedsLivingBudget))

/-- Rule 1366: formalization and resource-control tests only when their code changed. -/
def scopedTestRuns : Rule where
  number := 1366
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified runsScopedTests scopedTestsUnneeded

/-- Rule 1367: tests through `compute.sh`, the whole suite with `--threads 1`. -/
def testsThroughLauncher : Rule where
  number := 1367
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev bareTestRun) ∧ₗ judged runsCompute wholeSuiteWithoutLauncher

/-- Rule 1368: a slow-tool warning's cause fixed. -/
def slowToolFixed : Rule where
  number := 1368
  keyword := .should
  domain := .softwareEngineering
  formula := ev anyResult ∧ₗ atom reportsToolOverBudget ⟹
    eventually (ev editing ∧ₗ link fixesSlowCause) ∨ₗ atom justified

/-- Rule 1369: the live notebook served with `python3 server.py`. -/
def notebookServer : Rule where
  number := 1369
  keyword := .must
  domain := .mathematics
  formula := judged shellCall servesNotebookOtherwise

/-- Rule 1370: wrapped-Markdown conflicts through `tools/merge_md_words.py`. -/
def markdownMergeTool : Rule where
  number := 1370
  keyword := .must
  domain := .softwareEngineering
  formula := judged editing resolvesMdConflictByHand

/-- Rule 1371: C kernels linked with the stated flags. -/
def kernelLinkFlags : Rule where
  number := 1371
  keyword := .must
  domain := .mathematics
  formula := judged compilesC omitsStatedLinkFlags

/-- Rule 1372: no `--disk-cache` above aria2c's limit. -/
def aria2cCacheLimit : Rule where
  number := 1372
  keyword := .mustNot
  domain := .softwareEngineering
  formula := judged aria2cDiskCache diskCacheOverLimit

/-- Rule 1373: `aria2c -c` to resume. -/
def aria2cResume : Rule where
  number := 1373
  keyword := .should
  domain := .softwareEngineering
  formula := ev runsAria2c ∧ₗ atom resumesDownload ⟹ ev aria2cContinue ∨ₗ atom justified

/-- Rule 1374: framework commands outside the hooks timed with `tools/tool_runtime.py`. -/
def toolRuntimeTiming : Rule where
  number := 1374
  keyword := .must
  domain := .softwareEngineering
  formula := judged shellCall untimedIndirectCall

/-- Rule 1375: running jobs inspected with `tools/job_metrics.py`. -/
def jobMetricsInspection : Rule where
  number := 1375
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified shellCall inspectsJobOtherwise

/-- Rule 1376: setup rerun when the controls are inactive. -/
def setupAfterReboot : Rule where
  number := 1376
  keyword := .must
  domain := .softwareEngineering
  formula := ev anyResult ∧ₗ atom reportsControlsInactive ⟹ eventually (ev runsSetup)

/-- Rule 1377: setup run from the project directory. -/
def setupFromProject : Rule where
  number := 1377
  keyword := .must
  domain := .softwareEngineering
  formula := judged runsSetup setupOutsideProject

/-- Rule 1378: Codex's long runs through its background bridge. -/
def codexBackgroundBridge : Rule where
  number := 1378
  keyword := .must
  domain := .softwareEngineering
  formula := judged codexExec longRunWithoutBridge

/-- Rule 1379: a Pod's `/dev/shm` within 352 GB. -/
def shmBudget : Rule where
  number := 1379
  keyword := .must
  domain := .softwareEngineering
  formula := judged shellCall shmOverBudget

/-- Rule 1380: no reliance on a container dropping the host page cache. -/
def noPageCacheReliance : Rule where
  number := 1380
  keyword := .mustNot
  domain := .softwareEngineering
  formula := never ((ev reply ∨ₗ ev shellCall) ∧ₗ atom reliesOnPageCacheDrop)

/-- Rule 1381: the cookie file at its path, owner-readable only. -/
def cookieFile : Rule where
  number := 1381
  keyword := .must
  domain := .softwareEngineering
  formula := judged shellCall cookieFileMisplaced

/-- Rule 1382: a rule file reread end to end before a rule is changed. -/
def rereadRuleFile : Rule where
  number := 1382
  keyword := .should
  domain := .discipline
  formula := ev editsRuleFile ∧ₗ atom addsOrChangesRule ⟹ once (ev readsRuleFile ∧ₗ link readsWholeEditedFile) ∨ₗ
    atom justified

/-- Rule 1383: a script serving one library named after it. -/
def scriptNames : Rule where
  number := 1383
  keyword := .should
  domain := .softwareEngineering
  formula := unlessJustified editsPython scriptNamedGenerically

/-- Rule 1386: no "lovely". -/
def noLovely : Rule where
  number := 1386
  keyword := .mustNot
  domain := .discipline
  formula := judged writesMessage usesLovely

/-- Rule 1387: the paper's content referred to neutrally. -/
def neutralPaperReference : Rule where
  number := 1387
  keyword := .should
  domain := .discipline
  formula := unlessJustified writesMessage refersToPaperNonNeutrally

/-- Rule 1388: connected prose in a plain, patient register. -/
def connectedProse : Rule where
  number := 1388
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper proseNotConnected

/-- Rule 1389: no reassurance, simulated intimacy or praise. -/
def noReassurance : Rule where
  number := 1389
  keyword := .mustNot
  domain := .mathematics
  formula := judged editsPaper reassuresOrPraisesReader

/-- Rule 1390: no announced teaching choices. -/
def noTeachingAnnouncements : Rule where
  number := 1390
  keyword := .mustNot
  domain := .mathematics
  formula := judged editsPaper announcesTeachingChoice

/-- Rule 1391: the author's humor kept, never forced, announced or quota-filled. -/
def authorsHumor : Rule where
  number := 1391
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper losesAuthorsHumor ∧ₗ
    never (ev editsPaper ∧ₗ (atom forcesJoke ∨ₗ atom fillsHumorQuota))

/-- Rule 1392: no decorative tagline, diagram or rhetorical question. -/
def noDecorativeHooks : Rule where
  number := 1392
  keyword := .shouldNot
  domain := .mathematics
  formula := unlessJustified editsPaper addsDecorativeHook

/-- Rule 1393: captions add mathematical context. -/
def contextualCaptions : Rule where
  number := 1393
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper captionRecitesPicture

/-- Rule 1394: no nearby global symbol as a summation index. -/
def freshSummationIndex : Rule where
  number := 1394
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper reusesGlobalSymbolAsIndex

/-- Rule 1395: considered typography. -/
def consideredTypography : Rule where
  number := 1395
  keyword := .should
  domain := .mathematics
  formula := unlessJustified editsPaper neglectsTypography

/-- Rule 1396: a merge request checked out in its own worktree, removed after; the user's checkout
never switched. -/
def reviewWorktree : Rule where
  number := 1396
  keyword := .must
  domain := .softwareEngineering
  formula := judged gitSwitch switchesUsersCheckout ∧ₗ
    (ev worktreeAdd ∧ₗ atom checksOutMergeRequest ⟹ eventually (ev worktreeRemove))

/-- Rule 1397: the hunk-ledger phase as one Sonnet medium-reviewer, commits in order, no records. -/
def hunkLedgerReviewer : Rule where
  number := 1397
  keyword := .must
  domain := .softwareEngineering
  formula := ev reviewerRun ∧ₗ atom runsHunkLedgerPhase ⟹
    ev sonnetReviewer ∧ₗ ¬ₗ atom briefHoldsTaskRecords ∧ₗ ¬ₗ atom briefTakesCommitsOutOfOrder ∧ₗ
    ¬ₗ once (ev reviewerRun ∧ₗ link sameHunkLedgerPhase)

/-- Rule 1398: each ledger row written by the agent, Does, Context and Findings first. -/
def ownLedgerRows : Rule where
  number := 1398
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesDocument ledgerRowOutOfOrder ∧ₗ judged reviewerRun delegatesLedgerRows

/-- Rule 1399: a quick question settled before the next unit. -/
def quickQuestionsSettled : Rule where
  number := 1399
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev writesDocument ∧ₗ atom startsNextLedgerUnit ∧ₗ
    since (ev agentText ∧ₗ link raisesQuickQuestion) (ev anyCall ∧ₗ link settlesQuickQuestion))

/-- Rule 1400: knowledge for later units written before the next unit; Revisit units reread. -/
def knowledgeBeforeNextUnit : Rule where
  number := 1400
  keyword := .must
  domain := .softwareEngineering
  formula := never (ev writesDocument ∧ₗ atom startsNextLedgerUnit ∧ₗ
      since (ev agentText ∧ₗ link findsKnowledgeForLaterUnits) (ev writesDocument ∧ₗ link recordsKnowledge)) ∧ₗ
    (ev writesDocument ∧ₗ atom marksUnitRevisit ⟹ eventually (ev reading ∧ₗ link rereadsRevisitUnit))

/-- Rule 1401: each scope claim and accepted limit `hunk_ledger.py prose` lists is checked. -/
def proseListChecked : Rule where
  number := 1401
  keyword := .must
  domain := .softwareEngineering
  formula := ev hunkLedgerProse ⟹ eventually (ev writesDocument ∧ₗ link answersListedClaims)

/-- Rule 1402: hunk-ledger findings join the draft only after its check prints "Complete". -/
def findingsAfterComplete : Rule where
  number := 1402
  keyword := .mustNot
  domain := .softwareEngineering
  formula := ev writesDocument ∧ₗ atom addsHunkFindings ⟹
    once (ev resultSaysComplete ∧ₗ link resultOfHunkLedgerCheck)

/-- Rule 1403: each re-review finding marked Miss or New, each miss with cause and fix. -/
def rereviewFindingsMarked : Rule where
  number := 1403
  keyword := .must
  domain := .softwareEngineering
  formula := judged writesReviewFile rereviewFindingUnmarked

def rules : List Rule :=
  [descriptionNeedsLedger, messageFileNaming, documentReferences, reviewRoundsInReviewFile,
   noNeedlessNumberInFix, ownSuiteLabel, recentPython, rewrapWithTool, proseReplacedByTool,
   notebookTools, mathJaxForMath, articleHeader, shortEntryMeta, noCycleNumbers, descriptiveNames,
   knownStatusValues, dutyDeclared, commitMessageShape, portablePaths, noScratchSymlink,
   codexScratch, pagesArtifact, accurateTestedScope, noRepeatedMistake, zstdPayloads,
   largeOutputParts, tailBytes, phaseCategories, venvThroughLauncher, otherRepositoryWorkload,
   hubDownloads, terseReplies, compareWithReference, bottomUpExplanation, siblingOnlyWhereUnruled,
   directRules, flatStructure, pasteReadyCommands, modulesFromStart, onlyUsedImports,
   underscoredPythonNames, statedNonGoals, batchedExternalAsks, noCheckWithoutDiff,
   runbookForRiskyProcedure, ownJudgementFirst, pasteRawOutput, uiAudienceFirst,
   triggerScheduledJob, relevantLeanReferences, leanToolingInfo, loogleRootChecked,
   runCodeImports, frequentInterfacesFirst, syntaxWorthItsCost, fittingComposition,
   typeSurfaceAsInterface, universeLevels, coverLetterName, coverLetterTitle, flatCommitList,
   noSingleItemSublist, noEmDash, versionNoteShape, versionNoteTense, versionNoteFormatting,
   noPolishDiacritics, realQuestionMarks, noChatMarkdown, separatedChatParts, fewDoubleDashes,
   verbatimIdentifiers, walkthroughInstructions, teamTerms, notationDefined,
   establishedTerminology, noInternalLabels, numberedReferences, fewSubtitles, displaysInSentences,
   noHistoryInPaper, symbolTableWhereHeavy, definitionWithConditions, intactIdentifiers,
   runningHeads, pageLayout, graphFigureStyle, figuresInspected, noChatConventionsInPaper,
   removeWrongProse, problemThenAsk, ownCauseStated, standaloneComments, anchoredComments,
   companyReadableComments, commentGivesFix, attachedCommandTested, reviewInOneFile,
   postedAsOneReview, postingRecorded, noTaskCheckBypass, livingSectionsCurrent, scopedTestRuns,
   testsThroughLauncher, slowToolFixed, notebookServer, markdownMergeTool, kernelLinkFlags,
   aria2cCacheLimit, aria2cResume, toolRuntimeTiming, jobMetricsInspection, setupAfterReboot,
   setupFromProject, codexBackgroundBridge, shmBudget, noPageCacheReliance, cookieFile,
   rereadRuleFile, scriptNames, noLovely, neutralPaperReference, connectedProse, noReassurance,
   noTeachingAnnouncements, authorsHumor, noDecorativeHooks, contextualCaptions,
   freshSummationIndex, consideredTypography, reviewWorktree, hunkLedgerReviewer, ownLedgerRows,
   quickQuestionsSettled, knowledgeBeforeNextUnit, proseListChecked, findingsAfterComplete,
   rereviewFindingsMarked]

/-! The MAY rules. -/

/-- The verdict of each rule on a trace whose every question a model answers no. -/
def keepsAll (rs : List Rule) (steps : Array Step) : Bool :=
  rs.all fun r => r.verdict (Ctx.build steps true fun _ => some false) == .kept

/-- Rule 1297 (MAY): a regression test's comment naming its bug, and a commit message motivating
the approach against a rejected one, break no rule of the range. -/
theorem r1297_narration_allowed : keepsAll rules (seq
    [.call "e" "Edit" [("file_path", "tests/test_queue.py"),
      ("new_string", "# Regression: the queue dropped the last job when two workers finished at once.")],
     bash "git commit -m 'Use a lock-free queue: a mutex was rejected for its contention'"]) = true := by
  decide

/-- Rule 1304 (MAY): logging inside a function breaks no rule of the range. -/
theorem r1304_logging_allowed : keepsAll rules (seq
    [.call "e" "Edit" [("file_path", "tools/solver.py"), ("new_string", "    log.debug(\"step %d\", i)")]]) =
    true := by
  decide

/-- Rule 1384 (MAY): a mutation spec using ISOLATE for an independent service fixture breaks no rule
of the range. -/
theorem r1384_isolate_allowed : keepsAll rules (seq
    [.call "e" "Edit" [("file_path", "research/results/x/mutants/db_spec.py"),
      ("new_string", "ISOLATE = 'tests/db_fixture.py'")]]) = true := by
  decide

/-- Rule 1385 (MAY): a line-based REPL trial and an exact-column LSP trial break no rule of the
range. -/
theorem r1385_repl_and_lsp_allowed : keepsAll rules (seq
    [.call "r" "mcp__lean-lsp__lean_run_code" [("code", "example : 1 + 1 = 2 := rfl")],
     .call "g" "mcp__lean-lsp__lean_goal" [("file_path", "Rails/Logic.lean"), ("line", "40"),
      ("column", "5")]]) = true := by
  decide

def permissions : List Nat := [1297, 1304, 1384, 1385]

end Rails.Ruleset.Range10
