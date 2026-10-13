# Real-amplitude JAS tests detect every attained off-line zero

- **ID:** jas-real-amplitude-detection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** JAS ledger row 164 (`1-in-progress/jas-goal-loop-2026-10-09.md`), open question of row 161
- **Statement:** If some zero of ξ off the critical line has the largest distance `δ = |Re ρ₀ − ½|` among all zeros, then for every level `δ < σ < 1 + δ` and every `X` there are `N > X` and `t ∈ (0, 1]` with `Re Σ_ρ K(ρ)/(ρ(1−ρ)) < 0`, where `K(s) = ∏_{X<p≤N} (1 + t p^{−σ} cosh((s − ½) log p))`.

## Goal
Row 161 left open whether JAS positivity with few phases is still a receiver. The corpus receivers use
complex test vectors, i.e. phases `e^{iθ}` attached to `p^{−ρ}` and `p^{−(1−ρ)}`. The question is whether
real test vectors suffice. A real test vector `x` gives the Bernoulli factor
`(1 + x²)(1 + t p^{−σ} cosh((ρ − ½) log p))` with `t = 2x/(1 + x²)`, so real tests are positivity of the
zero measure against products of cosine factors.

## Mechanism
Real tests cannot rotate the zero's contribution. The diagonal subgroup `{±1}` has two characters, so
any Bochner-type frequency extraction aliases all odd levels and loses a factor `√|P|`. This is the
phase-count law of row 161.

The phase comes instead from the edge of the prime range. For `s = σ − δ − iγ`, the prime number theorem
gives
`Σ_{X<p≤N} p^{−s} = N^{1−s}/((1 − s) log N) + o(N^{1−Re s}/log N)`.
The argument `γ log N − arg(1 − s)` turns with `N`. This main term is the interaction of the zero with
the pole of ζ at `s = 1`.

Among the zeros at the maximal distance `δ`, choose `ρ* = ½ + δ + iγ` with `|γ|` minimal; `γ ≠ 0`
because ξ has no real zeros.
- Choose `N` with `N^{iγ}` in a prescribed direction, and the amplitude `t = 2|Z|/E` with
  `E = N^{1−α}/log N`, `α = σ − δ`. Then the kernel of `ρ*` is `exp(Z + e)` with `‖e‖ ≤ 1/4` and
  `Z = R + i(π − arg w)`, `w = 1/(ρ*(1−ρ*))`. So `Re(w K(ρ*)) ≤ −|w| e^R/2`.
- The four zeros `ρ*, ρ̄*, 1−ρ*, 1−ρ̄*` give equal real parts.
- Zeros at distance `δ` and larger height have main terms smaller by the fixed ratio
  `√((1−α)²+γ²)/√((1−α)²+γ₁²) < 1`, where `γ₁` is the next height at distance `δ`.
- Zeros closer to the line have sums `o(Σ_p p^{−α})`, so their kernels tend to `1`.
- Every zero has kernel at most `exp(t Σ_p p^{−α})`, which stays bounded; the zeros outside a large
  finite set have small total weight.

Only the prime number theorem (`tendsto_sum_primesLE_cpow_sub_main`) is used, not the Vinogradov–Korobov
region.

## Lean
- `RHTower/JointAncestryRealAmplitudeDetection.lean`:
  - `not_jasRealPositiveAbove_of_maximal_offLine` (main theorem);
  - `frequently_cexp_log_near` (the edge phases `e^{iγ log N}` are dense for `γ ≠ 0`);
  - `tendsto_jasWindowSum_sub_main` (window sums follow their main terms);
  - `exists_normalized_maximal_zero` (minimal height and gap at the maximal distance);
  - `re_jasRealTerm_eq_of_abs` (the four-zero symmetry);
  - `re_mul_cexp_antiAligned_le`, `jasReal_tsum_neg_core`;
  - `frequently_jasReal_neg_of_maximal_offLine` (the negative tests, frequently in `N`, amplitude `κ/E_{σ−δ}(N)`);
  - `not_jasRealBudgetPositiveAbove_of_maximal_offLine` (budget sharpness: the negative tests have prime budget `≲ N^{½−δ}`, so positivity within `N^λ` fails for `λ > ½ − δ`, `½ < σ < min(3/2, 1+δ)`).
- `RHTower/JointAncestryRealAmplitudeCapstone.lean`:
  - `jasBernoulliFactor_ofReal`;
  - `JasProductPositiveAbove.realPositive`;
  - `exists_maximal_offLine_of_zerosApproachLine`;
  - `abs_re_sub_half_le_of_zerosApproachLine_of_jasRealPositiveAbove`;
  - `riemannHypothesis_iff_zerosApproachLine_and_jasRealPositiveAbove`;
  - `riemannHypothesis_iff_finiteOffLine_and_jasRealPositiveAbove`.

- `RHTower/JointAncestryRealAmplitudeVertex.lean` (vertex reduction, row 169):
  - `re_tsum_jasRealTerm_eq_sum_powerset` (Bernstein expansion over subsets at full amplitude);
  - `re_tsum_jasRealVecTerm_eq_sum_signs` (per-prime amplitudes = convex combination of sign patterns);
  - `jasRealPositiveAbove_iff_subset`, `jasRealVecPositiveAbove_iff_sign`;
  - `jasRealVecPositiveAbove_of_riemannHypothesis` (all levels `σ ≥ 0`, all `X`);
  - capstones `riemannHypothesis_iff_zerosApproachLine_and_jasRealSubsetPositiveAbove`,
    `..._jasRealSignPositiveAbove`, `riemannHypothesis_iff_finiteOffLine_and_jasRealSubsetPositiveAbove`;
  - bridge `jasRealKernel_one_eq_jasCosineKernel`, `JasCosinePositiveAbove.subsetPositive`.

## No-go closure / open core
- **Open:** the chain case. If the distances `|Re ρ − ½|` have no maximum, the dominant zero changes
  with the scale. A real test must then beat near-ties between chain members without phase rotation.
  The candidate target is a vertex of the lower convex hull of `{(δ_ρ, log|γ_ρ|)}`. Uniformity of the
  edge asymptotics above the Vinogradov–Korobov height and near-ties at the vertex are not controlled.
- **Producer reading:** for real tests, every detection runs through the pole–zero edge term at the
  zero's own frequency (consistent with MUST-132 and MUST-861). A producer for the real family must
  control `Σ_{p≤N} p^{−(σ−ρ+½)}` at every zero: prime counting at the zero's frequency.

## Log
- 2026-10-12 — conjectured, proved on paper, formalized; both modules built (`lake build`, capstone
  with `--old`), wired in `RHTower.lean`, `#print axioms` = standard three; STATUS MUST-1335.
- 2026-10-12 — budget sharpness added (ledger row 168): real budget law two-sided in the attained case; STATUS MUST-1340.
- 2026-10-12 — vertex reduction (ledger row 169): amplitude eliminated; untranslated prime cosine kernels suffice under ZAL; STATUS MUST-1344.
