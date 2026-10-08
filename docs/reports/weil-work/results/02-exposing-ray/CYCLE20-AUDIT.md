# Cycle20: square-density correction and pole-completion question

Status: NO FRONTIER ADVANCE. No new Lean edits or builds. Universal WP02 and
the vanishing-mass-defect producer remain OPEN. This is a research audit,
not a newly formalized obstruction or a claimed RH proof.

## The square-root threshold was not the corpus frontier

Source checked: WeilPrimitiveSetMeanSquare.lean, especially
`WeilMeanSquare.exists_sum_sq_div_le_of_primitive` and
`WeilMeanSquare.exists_sum_sq_Ioc_le`. Both take the literal POLAR
`WeilPositive`, not `WeilPositiveFull`. The theorem on primitive sets gives

    sum_(n in S) lambda(n)^2/n <= (log N+C)^2.

Every dyadic interval is primitive. For X large, the integer interval
exp(X-1)<=n<=exp(X+1) is covered by a fixed number of dyadic intervals whose
endpoints are comparable to exp(X). Therefore its weighted square mass is
at most C1*(X+C2)^2. This uses the primitive bound on each block, not a false
primitive-set assertion about the entire logarithmic window.

Let H(X) count nonzero weights in this window. Cauchy--Schwarz gives

    localAtomMass(lambda,X) <= sqrt(C1)*(X+C2)*sqrt(H(X)).

If the support has count O(N^theta), theta<1, then

    exp(-X/2)*localAtomMass(lambda,X)
      = O((X+C2)*exp(-(1-theta)*X/2)) -> 0.

This contradicts the existing
`WeilPositivitySparseWeightsObstruction.not_weilPositive_of_localAtomMass`.
Thus the earlier use of only the pointwise sqrt(n)*log(n) box missed an
ordinary stronger consequence of the existing mean-square theorem. In
particular, square-supported polar-positive weights are excluded on paper.
No full-cone strengthening or RH premise is used in this deduction.

This does not by itself instantiate the exact finite mixture in C-minus.
That requires the prime-blind duality proof with only square coordinates
retained, including its closedness/coordinate repair and compactness steps.
Those steps were not formalized here. The density correction is enough to
withdraw the diagnostic's claimed critical-boundary motivation; it is not a
new scientific result warranting a duplicate sparse-corollary leaf.

## Fourier annuli do not supply an energy gain

Consider a smooth even additive Fourier profile beta supported in
(-2,-1) union (1,2), and its even Fourier transform g. On the positive half-line
write M_h(s)=integral_0^infinity h(x)*x^(s-1) dx and

    U_h(u)=exp(u/4)/sqrt(2)*h(exp(u/2)).

Direct substitution gives paperFT(U_h)(tau)=sqrt(2)*M_h(1/2+2*i*tau).
The classical even local Fourier functional equation reflects s to1-s with
a multiplier of modulus one on Re(s)=1/2. Hence

    |paperFT(U_g)(tau)|^2=|paperFT(U_beta)(-tau)|^2.

Every even Mellin spectral weight, including the actual gamma energy when
integrable, has the same value on these two sources. Integer dilations of
the annulus have disjoint supports, giving square-lag orthogonality, but
U_beta already has support [0,2*log2]. Centering puts it at aperture log2.
Its autocorrelation vanishes at every square lag, including the smooth
boundary lag log4. The transform has not reduced this source's gamma energy.

Pole bookkeeping: U_h has half-pole values proportional to M_h(-1/2) and
M_h(3/2). The even Fourier gamma factor is finite and nonzero at both
points, so under legitimate Mellin continuation/integrability these two
zero moments are exchanged. For g, impose integral beta=0 to obtain g(x)
=O(x^2) near zero; smooth compact annulus data give rapid decay at infinity.
The two beta Mellin moment constraints then give actual convergent pole
integrals. None of this establishes a negative energy or compact support of
U_g. Truncating U_g would require a fresh exact trace repair argument.

Parent: Burnol, [Spectral Analysis of the local Conductor Operator]
(https://arxiv.org/pdf/math/9811040), local Fourier functional equation and
critical-line unitarity. This is an ordinary unitary transfer, not a new
construction of negative gamma energy. No numerical sign claim was made.

## Actual producer and source audit

The producer searches returned the already proved matched-family identity,
primitive surrogate boundary, source decompositions, and conditional ground
criteria. They did not provide the signed lower estimate. Positive gamma
energy of a different source norm cannot be substituted for `archEnergy`.
The source's exact all-integer matching and t=0 remain load-bearing.

The current abstract of Desogus arXiv:2609.20367v3 was opened. It explicitly
uses a finite computation and supplies no permitted proof for this task.
STATUS's exact-prime-deletion objection was also read. No independent audit
of v3, and no claim that its revised argument is refuted here, is made.

## Next precise diagnostic

POLAR-FULL-COMPLETION-CONJECTURE.md records the exact unproved implication
from polar to full positivity for the SAME integer weight. The corpus only
supplied the reverse implication. A generated search recipe reversed that
theorem and also listed full positivity itself as an obligation; rejected.
The proposed distribution argument isolates an exponential remainder, not
its disappearance. It supplies neither a cone point nor endpoint attainment.
Retain a utility gate before any implementation: no generic Bochner wrapper
or conditional receiver counts as progress on WP02.

## Assessment

No new scientific knowledge or signed lower bound established. The square
detour repeated known mechanisms; checking the stronger parent earlier would
have avoided it. No work was deferred for effort, size or missing Lean API.
The hardest obligation remains the full-family signed gamma estimate.
Next cycle must test the exact pole-completion claim against the integer
source, or return directly to the producer if it only shifts the same open
condition. Paper closure and novelty/utility audits precede Lean.
