# Weil cone / PBAP research work packages

Status: ready for assignment; no research agents launched. Snapshot: 2026-10-07.

Seven independently startable packages separate existence, direct dual positivity, four detection mechanisms, and higher-denominator classification. These are alternative mathematical attacks, not seven routine steps whose completion is assured.

Basis: [Lean audit](/Users/michael/Documents/code/hgt/docs/reports/weil-cone-pbap-lean-audit-2026-10-07.md) and [evidence manifest](/Users/michael/Documents/code/hgt/docs/reports/weil-cone-pbap-lean-audit-2026-10-07-evidence.json). The audit checked 54 declarations from 36 production modules, including explicit hypotheses and axioms. Search absence means “no closing theorem located,” not a formal proof that none exists.

## Assignment map

| Package | Single objective | Role and dependency |
|---|---|---|
| [WP01 — Full PBAP existence](/Users/michael/Documents/code/hgt/docs/reports/weil-work/01-pbap-existence.md) | Prove the full pole-plus-archimedean functional nonnegative on the exact integer-null test cone. | Supplies a full-positive sequence. General detection still needed. |
| [WP02 — Exposing-ray positivity](/Users/michael/Documents/code/hgt/docs/reports/weil-work/02-exposing-ray.md) | Prove the existing exposing-ray inequality at every cutoff and level. | Direct RH route; does not wait for WP01. |
| [WP03 — Singular arithmetic detection](/Users/michael/Documents/code/hgt/docs/reports/weil-work/03-singular-arithmetic-detection.md) | Supply the bounded zeta-quotient hypothesis beyond the already rigid regular classes. | Detection theorem can be researched with a hypothetical full-positive input. |
| [WP04 — Half-integer spectral counts](/Users/michael/Documents/code/hgt/docs/reports/weil-work/04-spectral-quantization.md) | Produce the exact half-integer interval-counting property for the canonical boundary measure. | Alternative detection mechanism; stronger than merely excluding off-line zeros. |
| [WP05 — Settled spectral phase](/Users/michael/Documents/code/hgt/docs/reports/weil-work/05-settled-phase.md) | Produce the exact atomic representation and settled phase required by an existing rigidity theorem. | Alternative to quantization; assumptions must be produced, not added silently. |
| [WP06 — Vanishing spectral deficit density](/Users/michael/Documents/code/hgt/docs/reports/weil-work/06-spectral-deficit.md) | Show the actual zeta-zero deficit has zero lower density on the linear scale. | Alternative detection mechanism; does not require quantization as an input. |
| [WP07 — Higher-denominator rigidity](/Users/michael/Documents/code/hgt/docs/reports/weil-work/07-higher-denominator-rigidity.md) | Classify the first unresolved rational-mass case, denominator three. | Conditional classification; a rational-mass producer remains a separate requirement. |

With three agent slots, start WP01, WP02 and WP06 to cover existence, a direct route, and detection. With more slots, add the other packages independently. This is a coverage recommendation, not a prediction of which hard problem will yield first. Do not launch extra agents merely because a package mentions a handoff.

## Logical interfaces

Write `W(λ)` for `RHTower.WeilPositiveFull λ`, `μλ` for `RHTower.WeilSpectral.boundaryMeasure hW`, and `Λ` for von Mangoldt. Coefficient conclusions concern `n ≥ 2`.

- **Already proved:** full PBAP ⇔ `∃ λ, W(λ)`; RH ⇔ `W(Λ)`.
- **Not supplied by that equivalence:** `∃ λ, W(λ) → RH`.
- WP01 plus a detector from WP03–WP06 that applies to **the same λ** would give RH. A detector with an extra hypothesis does not compose until that hypothesis is proved for the producer.
- WP02 reaches RH directly through an existing equivalence.
- WP07 plus an independent denominator-three full-positive producer would give RH if the proposed rigidity target is proved. WP07 alone supplies no producer.
- WP04–WP06 may prove `λ = Λ`, which is stronger than the minimal detection goal `W(λ) → RH`. A failure of one stronger approach does not refute general detection.

Full and polar positivity are different predicates. `WeilPositive` has pole-vanishing test constraints; `WeilPositiveFull` retains pole terms. Full implies polar, but the audit did not locate a converse for arbitrary weights. The exposing-ray theorem in WP02 has its own exact polar dual definition; use that definition literally.

No coefficientwise nonnegativity is implicit in `λ : ℕ → ℝ`. “Prime-blind” means the combined symmetric log-values vanish at **every integer `n ≥ 2`**, not merely primes. Nonnegative mixture coefficients do not make the underlying functions pointwise nonnegative.

## Common agent contract

Mode: mathematical research, paper proof first, then Lean formalization of the exact dependency-closed result. Read the assigned package and this contract before working. Do not load writing skills unless the user explicitly asks for one.

1. Refresh the relevant corpus search using the package's commands. Inspect `candidate_lemmas`, `source_arguments`, partial coverage and freshness; use `rg` for exhaustive checks. Read exact theorem statements before invoking them. Consult the relevant entries of [frontier map](/Users/michael/Documents/code/hgt/docs/reports/rh-current-frontier-map.md) and [STATUS](/Users/michael/Documents/code/hgt/docs/reports/STATUS.md), searching before opening large files. The audit is a starting snapshot, not permission to ignore subsequent results.
2. Create the package's own pipeline card before difficult work, using [card template](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/_card-template.md). State one falsifiable target and list every extra assumption. Separate existing Lean results, paper results, experiments and conjectures.
3. Complete the first milestone specified in the package. A renamed known receiver, a restatement of RH, or an unproduced premise is not new progress. Search a proposed lemma before proving it.
4. Produce a dependency-closed proof before formalizing. Verify names against this toolchain in a `/tmp` scratch file. Run relevant Lean compilation and `#print axioms` without editing existing source merely to inspect it. No `sorry`, `admit`, new axioms, `opaque` or `unsafe` declarations.
5. If an approach fails, prove the exact obstruction when possible and extract its strongest nontrivial positive survivor: a sharp threshold, rigidity statement, decomposition, replacement hypothesis or invariant. Formalize the survivor after its paper proof closes. After a serious second pass with no survivor, record `NO POSITIVE SALVAGE FOUND`. Failure to find a proof is not a no-go theorem.
6. Report exact scope. “Conditional advance” leaves the main target open. Do not declare RH, PBAP or classification closed from finite computation, a finite-dimensional relaxation, a smoothed asymptotic, or a newly assumed condition.

No new computation service, external spend, commit or push is included in these assignments. Use finite timeouts for long Python scratch work via the repository's guarded runner. Preserve existing working-tree changes.

## Disjoint write scopes and outputs

All existing Lean modules, this README, package instructions, global ledgers and shared umbrella modules are read-only for package agents. Each package below reserves its own result directory, pipeline-card basename and new Lean filename prefix. Reserved paths are proposed output scopes, not claims that files already exist. One agent owns a package at a time.

Each result directory must contain:

- `RESULT.md`: verdict (`CLOSED`, `CONDITIONAL ADVANCE`, `SCOPED NO-GO`, or `OPEN`); exact new statement; hypotheses paid versus unpaid; difference from prior corpus; proof and Lean evidence; downstream consequence.
- `PROOF.md`: complete argument, or explicitly separated proved lemmas and the remaining gap. Include obstruction and positive-survivor audit when applicable.
- `EVIDENCE.md`: search queries/coverage, exact reused declarations, new theorem locations, commands and exit codes, axiom output, and any numerical method/error bounds. Never label a numerical observation a theorem.

Keep ongoing state in the owned pipeline card. If a useful result needs a shared-file change, submit the exact proposed patch in the result directory; the coordinator applies it after review. Do not silently widen write scope or move into another package's target. Exchange mathematical statements and proof artifacts through the coordinator.

The coordinator checks that each new result is genuinely new, spot-checks its source and hypotheses, compiles the combined imports, applies umbrella/ledger changes once, and runs `scripts/formal_tools.py lint`. The previous audit's lint had six unrelated umbrella-reachability errors; report the current result and distinguish new errors from baseline. Do not fix unrelated modules or claim a clean gate without running it.

## What is deliberately not a separate package

Compactness, full spectral representation, critical-half-plane Herglotz continuation, and the basic duality/receiver theorems already exist. Rebuilding them is not a frontier task. Finite-aperture certification and numerical producer pinning can support WP01 or WP02, but are not an independent RH solution: every truncation needs a proved extension or tail argument. Do not create a separate “general detection” assignment that duplicates all four concrete detector packages.
