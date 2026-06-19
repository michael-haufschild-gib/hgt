# Verification Guide for Agents

**Purpose**: How to verify a claim before it enters the ledger, and how to keep the Lean tree
green and axiom-clean.
**Read this when**: adding/changing a Lean theorem, running the audit, or grading a draft claim.
**Stack**: Lean 4 + mathlib `v4.30.0`; `mpmath` (dps≥30) for numeric pre-certification.

## The evidence ladder

A claim's status is exactly one of these. Never round up.

| Tier | Meaning | Where it may live |
|---|---|---|
| **ledger-proven** | `lake build` green **and** `check_axioms.sh` PASS | A Lean theorem in `formal/` |
| **draft-claimed** | Argued in a draft, not (yet) in Lean | A draft brick, air-marked `[PROVED HERE]`/`[THEOREM]` |
| **numeric** | Supported by `mpmath`/PSLQ at stated precision | A draft, with the dps and the quantity shown |
| **conjecture / open core** | Stated, not proved | A draft, air-marked `[CONJECTURE]`/`[OPEN CORE]` |

The Lean tree may contain **only** ledger-proven Tier A (and provable Tier B fragments). Tier C
(RH, LI, DSS, archimedean positivity) stays in the drafts — never a theorem, never an `axiom`.

## Lean verification

Run from the repo root unless noted.

| Command | What it proves |
|---|---|
| `cd formal && lake exe cache get` | Pulls the prebuilt mathlib cache (do before the first build). |
| `cd formal && lake build` | The whole library compiles under the pinned toolchain. |
| `bash scripts/check_axioms.sh` | Every audited theorem depends only on the approved axiom subset of `[propext, Classical.choice, Quot.sound]` and no `sorry`/`sorryAx` appears. |

`scripts/check_axioms.sh` is the **ledger gate**. It builds a `/tmp` scratch file that
`#print axioms` each audited theorem, then fails unless:
- all audited theorems report an allowed axiom subset of `[propext, Classical.choice, Quot.sound]`
  (it counts them — the count must equal the number of `#print axioms` lines, currently **69**);
- no `sorryAx` appears in any axiom set;
- no real `sorry` token appears in the source (comments/docstrings are excluded by the grep filter).

### Verifying a mathlib name (mandatory, every time)

Never trust a recalled mathlib lemma/def name — the library renames across versions. Probe it
against **this** toolchain first:

```lean
-- /tmp/probe.lean
import Mathlib
example := @Complex.norm_cpow_eq_rpow_re_of_pos   -- replace with the name(s) you need
```

```sh
cd formal && lake env lean /tmp/probe.lean   # silence = the name resolves; error = it does not
```

Use the same scratch-file pattern for `#print axioms Some.Name`. **Never edit the tree to run a
probe**, and never delete `formal/.lake/` (the cache).

### Adding a theorem to the audit

When you add a citable theorem:
1. Add a `#print axioms GaloisForLFunctions.<name>` line to the heredoc in `scripts/check_axioms.sh`.
2. Bump the expected count in the `if [ "$COUNT" -ne 69 ]` guard to the new total.
3. Run `bash scripts/check_axioms.sh` and confirm it prints `PASS:`.
4. Update the `README.md` ledger table.

If a theorem legitimately needs an axiom beyond the standard three, that is a design event —
stop and raise it; do not loosen the audit silently.

## Numeric pre-certification

Before writing Lean for anything with numeric content, certify it with `mpmath` at `dps≥30`
(heavy runs go to runpods; archive results into the workspace if kept). The draft should record
the quantity, the precision, and the observed value (e.g. a projection distance `d_N`, a `Q_W`
sign, a PSLQ null-result to a stated height). Numeric support is its own tier — it is evidence
for a draft claim, **not** a substitute for a Lean proof and **not** grounds to call a brick
ledger-proven.

## Anti-circularity & fake-family filters

A draft claim that "sees RH" must survive these before it is taken seriously (the drafts apply
them explicitly; honor them when adding new bricks):

- **Anti-circularity.** A construction must be *source-pure*: built from primes / `μ` / `ζ`-data,
  **not** from the zeros it purports to constrain. If a step reads the `γ_n`, it cannot then
  conclude RH about them.
- **Fake-family filter.** A genuine mechanism must reject the known non-examples
  (Davenport–Heilbronn, Epstein). The field's First Theorem (`EulerProduct.lean`) is exactly
  this: no Euler product ⟹ no Bohr-lift factorization, detectable at a finite `n` — *pre-spectral*.
  A new criterion that passes a fake is wrong.
- **No-margin filter.** Positivity in this problem holds with **no uniform floor** (`λ_min→0`);
  a claim that produces a fixed positive margin has smuggled in extra strength and is suspect.

## Common mistakes

- **Don't** report `lake build` as passing without running it. **Do** paste the command + outcome.
- **Don't** mark a brick ledger-proven on numeric evidence alone. **Do** keep numeric a separate tier.
- **Don't** add a theorem to the tree without adding it to the audit and bumping the count.
- **Don't** assume a mathlib name exists. **Do** probe it with `lake env lean` first.

## On-Demand References

| Domain | Serena memory |
|---|---|
| Audit-script mechanics, name-verification idioms, common mathlib hooks used here | `lean_proof_conventions` |
| The fake-family / seam vocabulary these filters rest on | `field_vocabulary` |
