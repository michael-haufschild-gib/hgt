# Gaussian counts and arithmetic section height

- **ID:** RIAC-gaussian-section-height
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Integral sections](riac-integral-section-height.md)
- **Lean:** [GaussianSectionHeight.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/GaussianSectionHeight.lean)

## Actual count and quadratic comparison

For `A_N=ℤ^N/L_N`, let sections be all actual integral representatives
of a quotient class. For `t>0`, define

`Θ_N(c,t)=Σ_(v representing c) exp(−t Σ_i v_i²)`,
`H_N(c,t)=log Θ_N(0,t)−log Θ_N(c,t)`.

The definition uses neither the charge formula nor a quadratic form chosen
after its sign. Ambient Gaussian summability proves convergence; every
class has a representative, so its count is strictly positive.

Let `Z_N(t)` be the same Gaussian sum over all integral vectors,
`q=Q(N)` the squarefree count, and `k` the charge obtained from divisor
inversion. Then

`|H_N(c,t)−t k²/q|≤C_N(t)`, `C_N(t)=log Z_N(t)+tq`.

Consequently the actual quotient addition has parallelogram defect at
most `6C_N(t)`. Its logarithmic Tate sequence satisfies

`|4^(−j)H_N(2^j c,t)−t k²/q|≤C_N(t)4^(−j)`.

`divisorSectionLogHeight_error`, `divisorSectionLogHeight_parallelogram_bound`
and `divisorGaussianTateSequence_error` prove these bounds.
The Tate height is defined by this limit before it is identified with
`t k²/q`; it obeys the exact parallelogram and natural scaling laws.

## Arithmetic mechanism

Translation by the actual integral normal vector `aμ` is a bijection of
section sets, changes charge by `qa`, and changes energy by `2ak+qa²`.
Thus

`Θ(c+[aμ],t)=exp(−t(2ak+qa²))Θ(c,t)`.

The corrected height `H(c,t)−tk²/q` is therefore periodic in charge
modulo `q`. For the actual residue class `0≤r<q`, minimum section size
is exactly `r`. Hence `exp(−tr)≤Θ(c_r,t)≤Z_N(t)`, while
`1≤Θ(0,t)≤Z_N(t)`. These inequalities prove the displayed error without
assuming a shifted-theta maximum or any arithmetic cancellation.

Finite dilation by `q` is already an integral normal translation:

`H_N(qc,t)=tqk²`.

`divisorSectionLogHeight_squarefree_smul` proves this exact finite
log-count identity, not only an asymptotic law.
The raw count of minimizing sections has zero Tate limit; summing all
sections is what supplies this nonzero logarithmic coefficient.

## Signed local indices and remaining estimate

On the original class `b=−Σ_(j≥2)e_j`,

`Ĥ_N([b],t)=t D_N²=t(Σ_p index_p(N))²/Q(N)`.

`divisorGluingClass_gaussianTateHeight` proves this comparison. Thus this
actual arithmetic log-count retains the original signed target.
The conductor error is explicit and not uniform in `N`. No independent
subpower bound on `D_N`, full Hecke-correspondence height, or product formula
for this Gaussian height is established.

The [positive finite-height comparison](riac-gaussian-section-positivity.md)
proves the stronger bound `0≤H(c,t)−tk²/q≤tq/4`, through actual lattice
Poisson summation and paired sections. It also recovers the integral
minimum as the full real-parameter limit of `H(c,t)/t` when `t→∞`.
RH-scale signed cancellation remains open.
