# Style Guide (Immutable)

Violations are review rejections. Detailed examples: Serena memories `lean_proof_conventions`
and `draft_writing_conventions`.

## The two-channel rule (above all)

Keep the **LEDGER** (Lean) and the **SEARCH** (drafts) separate and each honest in its own way.
- Never write a conjecture as a Lean `theorem` or `axiom`. Never add a `sorry`.
- Never downgrade a draft idea for being speculative; never upgrade it to "proven" without the
  audit. Air-mark instead.

## Lean style

| Rule | Required form |
|---|---|
| Import | `import Mathlib` (or a sibling `GaloisForLFunctions.<Module>`); nothing narrower. |
| File header | A `/-! … -/` module docstring naming the draft + section it formalizes, and stating what is **not** formalized. |
| Namespace | All content inside `namespace GaloisForLFunctions` … `end GaloisForLFunctions`. |
| Section | `noncomputable section` … `end`; `open scoped BigOperators` when sums/products appear. |
| Docstring | Every `def`/`theorem`/`lemma` carries a `/-- … -/` doc comment in the field's vocabulary. |
| Naming | `snake_case` theorem names that read as the statement: `cpow_inversion_scale`, `logPrime_no_rat_relation`, `isMultiplicative_iff_bohr_factorization`. |
| Prime index | Primes are `Nat.Primes`; exponent vectors are `Nat.Primes →₀ ℤ`/`ℕ`. |
| Names verified | Every mathlib name probed with `lake env lean` before use (see `@docs/testing.md`). |
| Forbidden | `sorry`, `axiom` (for conjectures), `native_decide`, editing the tree to `#print axioms`. |

## Draft style

| Rule | Required form |
|---|---|
| Status banner | First lines state: founding/companion, date, and an explicit honesty banner (e.g. "NASCENT field … conjectural throughout … No proof of RH is claimed."). |
| Air-marking | Grade claims: `[THEOREM]` (proved/imported, named ref), `[PROVED HERE]`, `[CONJECTURE]`, `[OPEN CORE]`, or an explicit "verified / open" split. |
| Brick format | Advance via `## n. Brick #k (status): <claim>`; computation/argument; end with a `**House status**` line listing which bricks check and the current open core. |
| Tiering | Use Tier A/B/C honestly. Tier C is "the wall", never "almost closed". |
| Cross-refs | Reference companion drafts by filename; keep the field's vocabulary consistent across drafts. |
| Append-only | Add new bricks at EOF with a here-doc; do not silently rewrite a recorded brick. |

## Repo hygiene

- Standalone subtree: no parent-workspace paths, private coordination logs, or agent identities.
- Keep `README.md`'s draft↔theorem ledger table in sync when a theorem lands.
- `.gitignore` already excludes `formal/.lake/` and LaTeX/build debris; never commit them.

## On-Demand References

| Domain | Serena memory |
|---|---|
| Lean idioms with worked examples from this tree | `lean_proof_conventions` |
| Draft banners, brick/house templates, the five drafts | `draft_writing_conventions` |
