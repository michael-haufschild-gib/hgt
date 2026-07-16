---
name: lean-consolidate
description: "Use to consolidate duplication in the Lean tree, discharge hypotheses the codebase can already close, and build purely mechanically new theorems by rng-drawing existing declarations and combining them into stronger non-tautological statements."
argument-hint: "[hours] — minimum time budget in hours (default: 1)"
model: opus
user-invocable: true
---

Lean-tree consolidation and mechanical theorem synthesis, one rng-driven cycle at a time.

## The Direction Law (governing constraint — read first, obey always)

You — the agent running this skill — **cannot create anything new by reasoning**. This is not
modesty; it is a hard property of the model. Every theorem you *ideate* is a redressing of a
known theorem from training data. You are incapable of conjecturing outside the corpus, and you
are equally incapable of *judging* which target "would be valuable" without that judgment being
the corpus speaking. Therefore:

**BANNED — top-down, statement-first.** Never, in any disguise:
- "A useful theorem here would be T — now find the building blocks for T."
- "The natural next lemma is L." / "What the theory obviously needs is X."
- "Let me look for blocks that would prove *this* interesting statement."
- Choosing which file/theorem/hypothesis to work on because it "seems promising."

Any cycle step that begins with a desired statement is invalid. If you catch yourself having
written a target statement before the dice have drawn the blocks: stop, delete it, re-roll.

**MANDATED — bottom-up, blocks-first.** The only valid pipeline is:

> `scripts/rng` selects the objects → mechanical enumeration lists what those objects can form →
> the type-checker decides what survives → **only after** an object exists and compiles do you
> ask what it means and whether it is new.

Your judgment enters exactly twice: (1) executing mechanical steps correctly; (2) describing,
at the end of a cycle, what the compiled object says. Judgment never selects the target, never
filters the draw, never skips a draw as "unpromising," and never rates a dischargeable
hypothesis as "not worth the effort." Effort is irrelevant: if it can be built, build it.

## The Three Goals

- **A — Consolidate**: find and remove duplication in the Lean tree; shrink the codebase without
  weakening any statement.
- **B — Discharge**: find theorems whose hypotheses the tree can already prove, and bank the
  stronger (hypothesis-free or hypothesis-reduced) corollary. Dischargeability is the ONLY
  criterion — no worthiness judgment, no effort ceiling.
- **C — Combine**: rng-draw a handful of theorems, mechanically enumerate every type-valid
  combination, compile the survivors, and only then assess meaning and novelty.

## Instruments

- `scripts/rng` — the session's only entropy source (`int A B [N]`, `pick`, `shuffle`, `seed`).
  Never use `$RANDOM`, never "pick one yourself" — your unaided picks are typicality bias.
- `formal/LEAN_API.md` — the declaration index (~11k rows: `| theorem |`, `| lemma |`,
  `| def |`, `| structure |`, `| class |`, …) with module, `file:line`, and docstring.
  Regenerate with `python3 scripts/formal_tools.py index` after banking anything.
- `python3 scripts/formal_tools.py research "<query>"` — search before proving; duplicates are
  the disease.
- `python3 scripts/formal_tools.py lint` — authoritative gate: no `sorry`, `admit`, `axiom`,
  `opaque`, `unsafe`.
- Name probes and `#print axioms` go through `/tmp` scratch files (`lake env lean /tmp/x.lean`
  with `have := @Name` lines) — never trust a recalled name, never edit the tree to probe.
- Batch edits, compile rarely: verify once per cycle, not after every edit.
- Never `git commit` — the user commits.

**Minimum time budget: $ARGUMENTS hours (default: 1 if no argument given).**

## Startup

1. Run `date +%s`. Compute `deadline_unix = started_unix + ($ARGUMENTS * 3600)` (default 1
   hour). Write `logs/lean_consolidate_$(date +%Y%m%d_%H%M%S).md` with `started_unix`,
   `deadline_unix`, human-readable times. This is the **audit log**.
2. Run `scripts/rng seed`, state the seed in chat.
3. Read `formal/README.md`. Run `python3 scripts/formal_tools.py index` so `LEAN_API.md` is
   current, then `status` for the area map.
4. State in chat: what the formal tree proves, its theorem areas, and the Direction Law in one
   sentence ("the dice pick, the type-checker decides, meaning comes last").
5. Begin the work loop with chat message "Starting next cycle" — never enumerate cycles.

## The Work Loop

### Step 1: Roll the lane

```bash
scripts/rng pick consolidate discharge combine
```

Run the lane the dice return, even if the previous cycle in that lane was dry — dryness is not
a reason to override the roll.

### Step 2: Run the lane

#### Lane A — Consolidate (rng file → duplication hunt → merge)

1. Draw a random Lean file:
   ```bash
   files=$(find formal/GaloisForLFunctions -name '*.lean' | sort)
   n=$(echo "$files" | wc -l | tr -d ' ')
   echo "$files" | sed -n "$(scripts/rng int 1 "$n")p"
   ```
2. Read the file fully — statements AND proofs, not just signatures. State in chat what the
   module proves and how its declarations relate.
3. Hunt the rest of the tree mechanically for overlap: for each declaration, run
   `formal_tools.py research` on its head symbols and its conclusion's shape; grep
   `LEAN_API.md` docstrings for the same mathematical content under different names. Lean
   duplication wears these forms:
   - the same lemma proven in two modules under different names;
   - a special case re-proven from scratch where a general lemma already exists (the special
     case should become a one-line corollary, or be deleted and call sites re-pointed);
   - two `def`s/`structure`s describing the same object or the same hypothesis interface;
   - copy-pasted proof blocks that should be one helper lemma;
   - parallel "tower" files that differ only in a parameter a single parametrized module could
     carry.
4. Merge rule: the consolidated declaration must **subsume** every original — never weaken a
   statement to make the merge easier. Originals become one-line corollaries or are deleted
   with all uses re-pointed. No re-export shims.
5. Do not consolidate duplication that exists for proof-performance (e.g. a specialized lemma
   kept because the general one makes `simp`/elaboration blow up) — verify the claim before
   accepting it as a reason.

#### Lane B — Discharge (rng hypothesis → provider search → bank the stronger theorem)

Entry is random, not chosen. Roll a sub-lane with `scripts/rng pick interface theorem`:

- **interface**: draw a random `def`/`structure`/`class` row from the index —
  ```bash
  n=$(grep -cE '^\| (def|structure|class) \|' formal/LEAN_API.md)
  grep -E '^\| (def|structure|class) \|' formal/LEAN_API.md | sed -n "$(scripts/rng int 1 "$n")p"
  ```
  If it is a hypothesis interface (a Prop-valued predicate that theorems assume), grep the tree
  for every theorem assuming it, then search (`research`, grep) for declarations that PROVE it
  — outright, or in instances the assuming theorems accept.
- **theorem**: draw a random `theorem`/`lemma` row —
  ```bash
  n=$(grep -cE '^\| (theorem|lemma) \|' formal/LEAN_API.md)
  grep -E '^\| (theorem|lemma) \|' formal/LEAN_API.md | sed -n "$(scripts/rng int 1 "$n")p"
  ```
  Read the declaration at its `file:line`. List its explicit hypotheses. For EACH hypothesis,
  search the index for a provider whose conclusion unifies with it.

Then: if every hypothesis closes, build and bank the unconditional corollary. If only some
close, bank the hypothesis-reduced version — fewer assumptions is strictly stronger and counts.
**Dischargeability is the only criterion.** If the chain closes, you build it — no matter how
long the proof, how many bridging lemmas the unification needs, or how uninteresting it looks
to you. "Not worth it" is your prior talking; it is exactly the judgment you are not allowed to
make. Human-months are agent-minutes.

Before writing anything, `research` for an existing corollary — if it already exists, you found
Lane-A duplication instead; treat it as such.

#### Lane C — Combine (rng draw → mechanical enumeration → compile → meaning LAST)

1. Draw the blocks. Draw size first, then rows:
   ```bash
   k=$(scripts/rng int 4 8)
   n=$(grep -cE '^\| (theorem|lemma) \|' formal/LEAN_API.md)
   for i in $(scripts/rng int 1 "$n" "$k"); do
     grep -E '^\| (theorem|lemma) \|' formal/LEAN_API.md | sed -n "${i}p"
   done
   ```
   No re-rolling because a draw "looks useless." A draw is only re-rolled if a row is
   unreadable or the declaration no longer exists.
2. Read every drawn declaration at its `file:line` — the real Lean statement, binders and all,
   not the docstring.
3. Enumerate combinations from this fixed catalog — apply each move to every ordered pair (and
   triple, where a pair produced something) in the draw. The catalog IS the ideation; you add
   nothing to it:
   1. **Pipe**: conclusion of X unifies with a hypothesis of Y → `Y ∘ X`, hypothesis eliminated.
   2. **Specialize**: instantiate a universally quantified binder of Y with the concrete object
      X talks about, then simplify.
   3. **Transport**: X is an `iff`/equality → rewrite Y's statement across it.
   4. **Witness feed**: X proves an existential → feed the witness into Y's hypothesis.
   5. **Contrapose-then-pipe**: contrapose Y, then try moves 1–4 again.
   6. **Refute**: X and Y share hypothesis H and yield contradictory conclusions → `¬H`.
4. For each candidate, write a scratch skeleton in `/tmp` and let `lake env lean` decide:
   probe the names (`have := @name`), then attempt
   `theorem candidate … := by exact Y (X …)` (or the move's shape). The type-checker is the
   only filter. Expect most candidates to die; that is the method working, not failing.
5. **Non-tautology gate** (mechanical, no taste involved). A compiled candidate is bankable
   only if it
   (a) eliminates at least one hypothesis an input theorem carried, or
   (b) strictly widens a binder domain / moves a quantifier, or
   (c) is the first declaration connecting two different theorem areas (different `###`
       sections of `LEAN_API.md` — verify by grep).
   BANNED regardless of compiling: `⟨X, Y⟩` conjunction gluing; `Iff.mp`/`Iff.mpr` round trips;
   alpha-renamed restatements; fixed-numeral witnesses (`norm_num` instances are theatre);
   anything whose whole proof is `exact <one existing declaration>` — if `exact?` closes the
   candidate with a single existing declaration, you have found Lane-A duplication, not a
   combination; treat it as such.
6. **Only now — meaning.** For each banked survivor, write in the audit log: what the combined
   statement says mathematically, which areas it touches, and the answer to "is this new
   knowledge or a mechanical corollary?" — labelled `[MECHANICAL COROLLARY]` or
   `[POSSIBLY NEW — needs review]`. You do not promote; you flag. Possibly-new survivors are
   surfaced in the completion report for human review. Asking the meaning question BEFORE this
   point is a Direction Law violation.

### Step 3: Verify (per cycle, batched)

1. Compile every touched module (`lake env lean` on the files, or `lake build` of the touched
   targets). Fix what breaks.
2. `#print axioms` on every new declaration via a `/tmp` scratch file — axiom-clean only.
3. `python3 scripts/formal_tools.py lint` — must pass.
4. Docstrings on banked declarations: self-contained mathematics and mechanism only — no
   process notes, no dates, no references to this skill or its cycles.
5. Wire new files into the umbrella imports, then `python3 scripts/formal_tools.py index` —
   banked declarations must enter `LEAN_API.md` so later cycles can draw them. The loop feeds
   itself.

Placement: same-area results go in the module of the consumed theorem; cross-area results go in
the shared/bridge infrastructure area.

### Step 4: Log and loop

Append to the audit log: lane rolled, dice values, objects drawn, candidates tried, survivors
banked (with `file:line`), duplication removed (net lines), hypotheses discharged, meaning
notes. Do not enumerate or count cycles in the log or in chat.

**Never stop before `deadline_unix`.** Run `date +%s`. If current time < `deadline_unix`, go
back to Step 1 with chat message "Starting next cycle." Otherwise proceed to Completion.

## Completion

1. **Time gate (mandatory).** Run `date +%s`. If before `deadline_unix`, STOP — return to the
   work loop.
2. `python3 scripts/formal_tools.py lint` passes; all touched modules compile; index
   regenerated.
3. Report: duplication removed (declarations merged, net lines), hypotheses discharged
   (corollaries banked, each named), combinations built (candidates tried → compiled →
   banked), and the list of `[POSSIBLY NEW — needs review]` survivors with one-sentence meaning
   each. Do not commit.

## Compaction Protocol

After context compaction:
1. Glob `logs/lean_consolidate_*.md`, read the most recent — re-internalize deadline, seed, and
   what is already banked.
2. Re-read the Direction Law section of this skill.
3. Resume the work loop at Step 1.
