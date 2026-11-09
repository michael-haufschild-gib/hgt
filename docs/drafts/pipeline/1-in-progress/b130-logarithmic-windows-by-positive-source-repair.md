# Logarithmic windows through positive source repair

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B130 scale locality: replace log-square prime windows by `C log(T+2)`.

## Proposed mechanism

Delete the full multiplicity of one off-line quartet from the Xi transform.
The inverse transform `g` is real and even, has every exponential moment,
and should be strictly positive outside a compact interval by the existing
zero-division tail asymptotic. Its bilateral Laplace transform is positive
on the real axis: the removed quartet polynomial is strictly positive there.

Seek a finite positive translation average making `g` nonnegative everywhere,
while preserving the selected off-line exponent. Compact translation changes
the theta moment growth only by `O(|s|)`. A resulting positive annihilator
would have logarithmic moment `O(|s| log(2+|s|))`; Chernoff parameter `q=T`
would then give exponentially small leakage at radius `C log(T+2)`.

## Positivity-repair conjecture

If continuous real `g` has every exponential moment, is strictly positive
outside a compact interval, and `∫exp(sx)g(x)dx>0` for every real `s`, then
there exist `δ>0` and `N` such that

`Σ_(j=0)^N binomial(N,j) g(x+jδ) ≥ 0` for every real `x`.

Candidate proof: choose a compact step function `l≤g` with strictly positive
bilateral Laplace transform. Positive outer intervals dominate the compact
negative part for large `|s|`; truncation and uniform approximation handle
the remaining compact range of `s`. Its transform is a positive factor times
a Laurent polynomial `P(exp(δs))`, with positive extreme coefficients.
A Pólya multiplier `(1+X)^N` makes every coefficient nonnegative. Translating
`l` by the corresponding binomial weights therefore gives a nonnegative step
function, and the same weights preserve the inequality `l≤g`.

For the step approximation, fix positive intervals strictly beyond the compact
negative part on both sides. Their masses dominate all negative contributions
when `|s|≥S`, uniformly over sufficiently fine meshes. On `[-S,S]`, the Laplace
transform has a positive minimum. Truncate the weighted integrable tail, then
use cell minima and uniform continuity on the remaining compact interval to
make the Laplace error smaller than half that minimum. Extend the step function
by zero only where `g>0`. This gives a global lower approximation with every
real Laplace sign preserved. The mesh may be arbitrarily small.

The multiplier `(1+exp(δw))^N` is nonzero whenever `Re w≠0`. Thus repair cannot
erase the chosen positive-depth mode. Exponential tilting supplies the shifted
depth tests needed for prime-gap iteration.

## Inputs and gaps

- `ThetaZeroDivisionRealization.ThetaDivisionList` admits repeated roots up to
  their full Xi multiplicity; `sourceTransform_thetaListDivision_mul` proves
  the entire quotient identity. `ThetaDivisorCardinalSource` proves survival
  after complete multiplicity removal. No simple-zero premise is needed.
- `ThetaTailScalingAsymptotics.tendsto_thetaListDivision` gives leading tail
  coefficient `∏β²/(2π)^(2|L|)`. For full conjugate pairs this is positive.
  `ThetaZeroDivisionRateTomography.listComb_thetaListDivision_eq_ofReal`
  handles conjugate-invariant admissible lists. Quartet specialization pending.
- `ThetaZeroDivisionLipschitz.exists_lipschitz_thetaListDivision` provides a
  global Lipschitz constant. On each mesh cell, the left value minus `Lδ`
  is a lower bound and differs from the source by at most `2Lδ`; this can
  replace cell minima in the compact approximation proof.
- `local-divisor-coefficient-repair`: sharp quadratic binomial repair already
  formalized. `ArithmeticLocalDivisorGeometry/PositiveMultipliers.lean` now proves
  `exists_negativeRootMultiplier_repair`: every polynomial positive on `[0,∞)`
  has a coefficientwise nonnegative multiple using only correcting factors
  `X+r`, `r>0`. It also proves those correcting factors nonzero in the closed
  right half-plane. Both axiom audits contain only the standard three axioms.
- Missing: compact lower step approximation preserving every real Laplace sign,
  complete positivity-repair theorem, zeta specialization, logarithmic leakage,
  and prime-window conclusion. No theorem in this card is claimed formalized.

This changes the observation scale only. It supplies no arithmetic lower bound.
No external novelty claim; no web search used.

## Weaker repair sufficient for detection

Equal binomial weights are unnecessary. It suffices to use coefficients of
`Q(X)=∏(X+r_j)^(n_j)`, `r_j>0`. For any polynomial positive on `[0,∞)`,
factorization into real linear factors and conjugate quadratic factors,
followed by the quadratic repair theorem, supplies such a `Q`
with coefficientwise nonnegative `PQ`. The repair factor has only negative
real roots. Choose the step mesh with `δ |Im w₀|<π`; then `exp(δw₀)` is
not negative real, so `Q(exp(δw₀))≠0`. This suffices for the chosen mode
and avoids requiring a new equal-factor Pólya theorem.

## Uniform approximation parameters

For a Lipschitz source, take `A≥1` with `g>0` for `|x|>A`, Lipschitz
constant `L>0`, and `B=1+sup_(|x|≤A+2)|g(x)|`. Let `m>0` be a lower
bound on `A+2≤|x|≤A+5`. Choose `S≥1` with
`(m/2)exp(S)>2(A+2)B`; put `η=min_(|s|≤S)∫exp(sx)g(x)dx>0`.
Choose `R>A+6` so that
`exp(-R)∫exp((S+1)|x|)|g(x)|dx<η/4`, and let `u>0` bound `g`
below on `A+1≤|x|≤R`.

Use grid mesh `h=2R/M`, smaller than the prescribed mesh bound and
`min(1,1/L,u/(2L),m/(2L),η/(16RL exp(SR)))`. On each cell take its
left value minus `Lh`, and use zero outside `(-R,R]`. This is a global
lower approximation, its negative part is supported in `[-A-2,A+2]`
and bounded by `B`, and it is at least `m/2` on both outer unit bands.
Those bands prove Laplace positivity for `|s|≥S`. For `|s|≤S`, compact
error is at most `4RLh exp(SR)≤η/4`, and discarded weighted tail is
less than `η/4`. The first coefficient is positive because `g(-R)≥u`.
Thus the associated polynomial is positive on `[0,∞)` and admits the
negative-root correcting multiplier. These analytic estimates still await Lean.
