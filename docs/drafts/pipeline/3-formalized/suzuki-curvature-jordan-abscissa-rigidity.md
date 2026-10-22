# Suzuki curvature Jordan abscissa rigidity

Status: `[FORMALIZED]` 2026-08-30; corpus/literature/falsity audits, dependency-closed paper proof, and unconditional Lean proof passed.

## Exact RH proof chain

Exact signed Suzuki prime--archimedean curvature cells
→ floor-selected affine checkpoint current
→ bounded CCM-FU Suzuki checkpoint mixture
→ `riemannHypothesis_of_ccmFUSuzukiCheckpointAffineMixtureBound`
→ RH.

This card attacks the only survivor of the formalized Jordan-gauge escape: singular damping of the
shared CCM-FU/SP-E source. It asks for the exact critical order at which such damping first becomes
a finite-variation receiver.

## `[CORPUS]` frontier

- `suzukiCheckpointSignedCurvatureCell_neg_iff_odd_primePower_endpoint` and
  `suzukiCheckpointSignedCurvatureCell_pos_iff_not_odd_primePower_endpoint` give the exact sign
  support.
- `suzukiCheckpointSignedCurvaturePositiveMass_ge_sixthHarmonic` and
  `suzukiCheckpointSignedCurvatureNegativeMass_ge_primeHarmonic` prove undamped two-sided infinite
  variation, but do not classify singular gauges.
- `summable_ccmFUSignedCurvatureMatchedCurrent` proves that quadratic actual-head damping
  compactifies the source.
- `unitRiesz_center_eq_weightedSignedCurvature_add_arch` proves that the source-faithful UR/HG
  channel instead retains the event-label first moment before damping.
- Corpus search found no exact polynomial-gauge chamber or common Jordan abscissa theorem.

## `[CONJECTURE]` S-CURVATURE-JORDAN-ABSCISSA-RIGIDITY

For `α ∈ ℝ`, put

`w_α(N) = (N+1)^(-α)`.

Then each Jordan sector of the exact signed curvature has the same sharp summability chamber:

`Summable (N ↦ w_α(N)c_N^+) ↔ 1/2 < α`,

`Summable (N ↦ w_α(N)c_N^-) ↔ 1/2 < α`.

Equivalently, both positive and negative Jordan Dirichlet series have abscissa `1/2`, despite one
sector living mainly on the integer continuum cells and the other on odd prime powers.

Public meaning: exact Suzuki curvature is a signed source of critical half-order, not an ordinary
measure. Every half-density-compatible polynomial damping remains infinite-variation; every
finite-variation polynomial receiver is necessarily supercritical and has an inverse growing
strictly faster than square root.

## Hostile falsity and rediscovery audit

- A support-density mismatch could have produced different abscissae: positive cells occur on an
  explicit integer lattice, while negative cells occur only at odd prime powers. The von Mangoldt
  logarithm exactly compensates prime sparsity, so the same half-order is plausible but not formal.
- The statement is stronger than the existing undamped no-go and weaker than an RH-bearing
  cancellation theorem: it classifies absolute Jordan size without claiming signed cancellation.
- Suzuki's screw-function papers and 2026 finite-aperture operator paper do not define these
  discrete Jordan sectors or classify their weighted variation. Suzuki's Chebyshev-variant paper
  studies weighted signed summatory functions and sign criteria, not two-sided Jordan abscissae.
- Standard Dirichlet-series and prime-harmonic theorems supply parent mechanisms, but no located
  source states the exact curvature classification.

Primary records:

- https://arxiv.org/abs/2206.03682
- https://arxiv.org/abs/2209.04658
- https://arxiv.org/abs/2411.07436
- https://arxiv.org/abs/2606.09096

Verdict: `SURVIVES PRELIMINARY ATTACK`.

## `[OPEN CORE]`

Prove the matching upper and lower half-order estimates without replacing exact curvature by a
surrogate:

- positive upper control must retain the smooth Suzuki cell and subtract the nonnegative atomic
  mass;
- negative upper control must retain the von Mangoldt atom and subtract the positive smooth cell;
- lower divergence must use actual curvature on the `6(m+1)` lattice and on cofinally many prime
  endpoints, including the exact `N ↦ N+1` index shift.

## Dependency-closed paper proof

Put `k=N+1` and

`I_k = ∫_[log(k-1),log k] screwRegularKernel(t)dt`,

so `c_N=I_k-Λ(k)/sqrt(k)`. Write `β=α+1/2`.

### Convergence when `α>1/2`

Discard the first two cells; finite changes do not affect summability. For `N≥2`, the smooth cell
is positive and

`I_k ≤ 2(sqrt(k)-sqrt(k-1)) = 2/(sqrt(k)+sqrt(k-1)) ≤ 2/sqrt(k)`.

Because the atomic term is nonnegative,

`0 ≤ c_N^+ ≤ I_k ≤ 2 k^(-1/2)`.

Hence

`0 ≤ k^(-α)c_N^+ ≤ 2k^(-β)`.

Since `β>1`, comparison with the shifted real `p`-series proves summability of the positive sector.

Also `I_k≥0`, so

`0 ≤ c_N^- = max(Λ(k)/sqrt(k)-I_k,0) ≤ Λ(k)/sqrt(k)`.

Therefore

`0 ≤ k^(-α)c_N^- ≤ Λ(k)k^(-β)`.

The von Mangoldt Dirichlet series is absolutely summable for every real exponent `β>1`; this proves
negative-sector summability.

### Positive divergence when `α≤1/2`

For `k=6(m+1)`, two distinct primes divide `k`, hence `Λ(k)=0`. The exact Suzuki cell lower bound
gives

`c_(k-1)^+ = I_k ≥ (4/5)k^(-1/2)`.

Consequently

`k^(-α)c_(k-1)^+ ≥ (4/5)k^(-β)`.

The map `m↦6m+5` is injective. Since `β≤1`, the shifted `p`-series on this lattice diverges, so the
full positive Jordan series cannot be summable.

### Negative divergence when `α≤1/2`

For every prime `p≥11`, the exact cell estimate gives `I_p sqrt(p)≤27/25`. Monotonicity of the
logarithm and `log 3>0.9` give `log p>9/5`. Thus

`c_(p-1)^- = log(p)/sqrt(p)-I_p ≥ (18/25)p^(-1/2)`.

It follows that

`p^(-α)c_(p-1)^- ≥ (18/25)p^(-β)`.

The map `p↦p-1` is injective. Euler's prime-series theorem, together with monotonicity of real
powers, says `Σ_p p^(-β)` diverges for every `β≤1`; deleting the finitely many primes below `11`
does not change this. Hence the negative Jordan series is not summable.

The convergence and divergence directions match exactly at `α=1/2`, proving both equivalences.

## Hostile proof audit

- The proof does not infer density of prime powers or use PNT. The positive lower subsequence is
  explicit; negative divergence is Euler's prime-harmonic theorem.
- Every comparison term is nonnegative, so no conditional rearrangement is used.
- The atom and smooth cell are never separated inside the exact signed source except through the
  definition of its positive or negative part and one-sided inequalities valid pointwise.
- The critical endpoint `α=1/2` is included in divergence on both sides.
- Cells `N=0,1` and primes below `11` are finite modifications only.

Verdict: `DEPENDENCY-CLOSED PAPER PROOF`.

## Proposed positive survivor

If proved, the common abscissa is the sharp boundary left by the previous no-go. Supercritical
damping is a valid compactified receiver, but it cannot be mistaken for the source-faithful
half-density channel. Any surviving CCM-FU/SP-E construction must therefore transport conditional
signed cancellation before crossing the half-order boundary, or justify an unbounded inverse on a
strictly larger distribution space.

## Lean closure

Module:

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCurvatureJordanAbscissaRigidity.lean`

Unconditional public results:

- `suzukiCheckpointSignedCurvaturePositiveMass_le_halfOrder`: exact positive-sector half-order
  upper majorant from the Suzuki smooth cell.
- `suzukiCheckpointSignedCurvatureNegativeMass_le_atom`: exact negative-sector von-Mangoldt
  half-density majorant.
- `suzukiCheckpointSignedCurvaturePositiveMass_ge_latticeHalfOrder`: half-order lower mass on the
  multiple-of-six lattice.
- `suzukiCheckpointSignedCurvatureNegativeMass_ge_primeHalfOrder`: half-order lower mass at every
  prime endpoint `p ≥ 11`.
- `summable_suzukiCheckpointSignedCurvaturePositiveMass_powerDamping_iff` and
  `summable_suzukiCheckpointSignedCurvatureNegativeMass_powerDamping_iff`: each sector is summable
  exactly when `1 / 2 < α`.
- `summable_suzukiCheckpointSignedCurvatureJordan_powerDamping_iff`: common exact Jordan abscissa.
- `no_halfOrderPolynomialDamping_summable_suzukiCheckpointCurvatureJordan`: closed theorem killing
  every half-order or subcritical polynomial compactification of the two-sided source.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCurvatureJordanAbscissaRigidity.lean` passed.
- `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiCurvatureJordanAbscissaRigidity` passed.
- Major theorem axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint found no issue in this module and confirmed umbrella reachability; repository-wide lint
  remains red on unrelated concurrently unwired modules.
