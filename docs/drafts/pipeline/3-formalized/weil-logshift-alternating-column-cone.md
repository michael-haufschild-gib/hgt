# Alternating late columns and a cone without finite-error cancellation

Status: formalized and kernel-audited. Corpus-only research, 2026-10-09. Global lint findings are recorded below.

## Target

Find a common K ≥ 625 such that, for every k ≥ K and n ≥ k+2,

`(-1)^(n+k) * C(k,n) > 0`,

where C is the native recovery coefficient column. Consequently, for any finite list of indices kᵢ ≥ K and real amplitudes aᵢ with `aᵢ * (-1)^kᵢ ≥ 0`, not all zero, the combined response `Σᵢ aᵢ Response(y,n,kᵢ)` has no finite factorial majorant at any real shift. Every factorial/exponential normalization of that combined response is nonsummable. Repeated indices are allowed.

This excludes an explicit nonzero cone from the direction submodule of the factorial-regular amplitude space. For full affine moments, use the arithmetic history as center, whose moments vanish. An arbitrary center may cancel a perturbation; no unconditional all-center irregularity claim is made.

## Local novelty and dependency audit

Direct research query `column ratio cancellation recurrence`, lexical OR, WeilLogShift filter: fts5, 30 hits in 11 modules, 18 eligible under per-module cap. Exhaustive `rg` over all WeilLogShift Lean leaves found no existing alternating-sign/parity law for coefficient columns.

Read `WeilLogShiftRecoveryColumns.lean` definitions and exact row/seed/factorization proofs, and the complete older-tail bound and growth proof in `WeilLogShiftLateColumnRunaway.lean`. The relevant existing statements are:

- `weilLogShiftRecoveryCoefficientColumn_seed_pos`: the seed is positive.
- `weilLogShiftRecoveryCoefficientColumn_row_zero`: every later row is homogeneous.
- `exists_weilLogShiftRecoveryCoefficientColumn_growth`: a common late threshold gives all required accumulated coefficient bounds.
- Private `coefficientColumn_older_tail_bound`: under those coefficient bounds and the native weight-tail threshold, the sum of older contributions has absolute value at most half the adjacent contribution's magnitude.
- The existing growth proof derives positive adjacent weight from `eventually_weilLogShiftRecoveryWeight_subdiagonal_amplifies` and positive diagonal weight. Its exact row split is already present there.
- `weilLogShiftRecoveryMomentResponse_eq_coefficientColumn`: every response column is C(k,n) times the same factor `pairedLogKernel(y,n)/sqrt(n)`.
- `WeilLogShiftFactorialRegularization` excludes all finite factorial majorants for each late response column.
- `WeilLogShiftFactorialMajorant` supplies eventual absolute-domination closure, nonzero scalar cancellation, and the implication from normalized summability to a majorant.

No external sources, numerical experiments, new analytic assumptions, or column-independence assumption.

## Dependency-closed paper proof

1. Increase the common threshold to dominate the already-proved column-growth, weight-tail, adjacent-amplification, and factorial-obstruction thresholds. For n ≥ k+2, growth from the positive seed implies C(k,n) ≠ 0.
2. Write the exact next-row equation as `d C(k,n+1) + w C(k,n) + R = 0`. Native diagonal positivity gives d>0; native adjacent amplification gives w>0. The existing older-tail theorem and the already-proved growth bounds give `|R| ≤ w |C(k,n)| / 2`.
3. If C(k,n)>0, then `w C(k,n)+R ≥ w C(k,n)/2 > 0`, hence C(k,n+1)<0. If C(k,n)<0, then `w C(k,n)+R ≤ w C(k,n)/2 < 0`, hence C(k,n+1)>0. Thus consecutive nonzero coefficients have opposite signs. Induction from the positive seed proves `(-1)^(n+k) C(k,n)>0`; the seed exponent is 2k+2, which is even.
4. For a finite list, choose n beyond every seed. The numbers `(-1)^n aᵢ C(kᵢ,n)` are all nonnegative because they are the products of `aᵢ(-1)^kᵢ` and the positive signed coefficients. At least one is strictly positive. Therefore absolute value of the coefficient sum equals the sum of absolute values and dominates `|aⱼ C(kⱼ,n)|` for each selected nonzero amplitude aⱼ.
5. The response factorization multiplies every coefficient term by the same real factor at fixed y,n. Thus `|Σᵢ aᵢ Response(y,n,kᵢ)| ≥ |aⱼ| |Response(y,n,kⱼ)|` on that common tail. No separate positivity assumption on the common kernel factor is needed.
6. A factorial majorant for the combined response would, by eventual absolute domination and nonzero scalar cancellation, imply a factorial majorant for the selected late response column, contradicting the existing theorem. The argument works for every real shift and all majorant parameters. Normalized summability is excluded by the already-proved implication to a factorial majorant.
7. For the arithmetic center, linearity of the moment continuous linear maps and the exact arithmetic-anchor identity identify the combined response with the full moment of the finite perturbation. Thus the same cone is excluded from regular affine amplitudes around that anchor. For any other center, only relative direction exclusion follows automatically.

## Implementation plan and boundaries

1. Add an unconditional uniform half-tail theorem in `WeilLogShiftLateColumnRunaway.lean`, reusing its existing private helper and proved growth/weight thresholds. Include adjacent positivity and coefficient nonvanishing. Keep the private helper and its original caller unchanged. Recompile that leaf and audit the new public theorem.
2. Formalize adjacent sign reversal and the parity sign law in a new leaf after checking local mathlib sign/power APIs in scratch Lean.
3. Formalize the finite aligned-cone response bound, all-shift no-majorant theorem, nonsummability, and arithmetic-anchor specialization. Then compile/audit only owned leaves, wire umbrella, refresh index, and lint.

Do not infer that mixed-sign amplitudes cancel, that they never cancel, or that the regular subspace has any specified codimension. Do not extend the sign theorem to early columns without proof. Do not replace the native `/sqrt(n)` response normalization by an unnormalized coefficient sequence.

## Implementation log — 2026-10-09

Revalidated current source and reran the local alternating/parity/cone research query. Scope: one unconditional theorem added to the existing late-column leaf, plus new sign and cone leaves. The revised implementation exposes the exact unconditional native estimate rather than promoting the conditional private helper; no proof duplication or existing proof edits are needed. Direct leaf verification begins next.


The unconditional half-tail theorem and both new sign theorems compile/export cleanly. The sign leaf proves strict negative adjacent products and the exact positive phase `(-1)^(n+k) C(k,n)` after every sufficiently late seed. No resource limits changed. The sign leaf is wired into the umbrella. The finite-cone algebra and arithmetic-anchor API checks are running; final combined axiom audit/index/lint remain. Current local novelty query `alternating column parity cone` returned fts5 58 hits in 13 modules, 23 eligible; no existing column parity or cone obstruction theorem was found.


All three owned leaves now compile/export cleanly: the amended native late-column leaf, `WeilLogShiftAlternatingColumns`, and `WeilLogShiftAlignedImpulseCone`. This includes eight new public theorems: uniform half-tail control, adjacent sign reversal, exact parity, exact finite-response triangle equality, response no-majorant, simultaneous normalization obstruction, arithmetic finite-response identity, and the full arithmetic-history obstruction. The final audit checks all 12 public theorems across the three files, including four pre-existing theorems in the amended leaf. Both new imports are wired uniquely into the umbrella; audit/index/lint remain.

The exact cone exclusion exposes a further positive invariant: strictly positive parity-adjusted weights whose linear combination is constant across every regular affine amplitude fibre, with weights independent of the center. Its formalized proof and local source audit are in `docs/drafts/pipeline/3-formalized/weil-logshift-positive-finite-error-balance.md`. Both follow-up leaves and all four public theorems are compiled and kernel-audited.


## Final verification — 2026-10-09

Direct final leaf commands compiled/exported `WeilLogShiftLateColumnRunaway`, `WeilLogShiftAlternatingColumns`, and `WeilLogShiftAlignedImpulseCone` cleanly, without warnings or resource-limit changes. The existing private older-tail helper and all existing proofs remain unchanged; one unconditional public theorem was added to the existing leaf. There are eight new public theorems in total. Scratch `#print axioms` checked all 12 public theorems across the three touched files, including four pre-existing theorems, and every result listed exactly `propext`, `Classical.choice`, and `Quot.sound`.

Index refresh exited 0. All 12 public declarations are indexed exactly once, all three umbrella imports are unique, and each exported object is newer than its source. Formal lint exited 1 with six unique unrelated unreachable HTGeometry modules: `AwayLinearGenerators`, `PaperIdealPowerReesFiltration`, `PaperNativeReesQuotient`, `PaperNativeReesSpecialization`, `PaperWeightOrderIdeals`, and `QKrawtchoukCompanionTriangular`. No finding concerns the owned leaves; unrelated modules were not modified. This is the current lint snapshot, superseding historical snapshots for status reporting.

The verified positive survivor consists of exact late-column alternating signs, exact triangle equality for finite parity-aligned responses at every shift, and exclusion of every finite factorial majorant and factorial/exponential summability normalization for nonzero aligned finite errors, including full moments at the arithmetic anchor. The positive weighted-balance follow-up is now formalized in the linked card above.
