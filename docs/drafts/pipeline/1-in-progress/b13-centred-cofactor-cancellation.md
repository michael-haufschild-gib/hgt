# Signed cancellation in the centred cofactor current

- **ID:** b13-centred-cofactor-cancellation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B13 / B134.

## Target

Bound the actual centred higher-moment Vaughan sum below a selected
exceptional-mode rate, retaining both signed continuum corrections.
The growing-order reduction gives an exponentially small error with
`X=exp(at)`, `r≈κt/log t`, `U≈X/t^(J+1)`, `V≈t`, `W≈t^(J+3)`.
The remaining object has coefficient

`(Λ−Λ_≤U)*trunc_(≤W)(δ−1*μ_≤V)`.

Its prime variable remains long. A bound for the number of cofactors,
for unsigned coefficient norms, or for the reduction error is insufficient.
No cancellation estimate closing B13 is proved.

## Signed structure to retain

Write `P_V(n)=Σ_(d|n,d≤V)μ(d)`. Then the short coefficient is
`δ(n)−P_V(n)`. The periodic divisibility part has finite Ramanujan
conductor expansion, but the unit mass carries the original prime sum.
For `n≤W`, the same coefficient is `P_W(n)−P_V(n)`.
Convolving this replacement with the long prime factor moves the
uncontrolled term to the finite prime head and the boundary `n>UW`;
it does not by itself give an upper bound.

At the level of continued Dirichlet multipliers, finite Möbius polynomial
`M_V(s)` gives `1−ζ(s)M_V(s)`, which equals one at every zero of ζ.
Thus choosing the truncated inverse more carefully cannot annihilate a
zero's contribution through this factor alone. A successful estimate
must use cancellation involving the actual prime coefficients.

## Current tests

- Identify whether same-source signed covariance or divisor-edge energy
  controls the centred current before absolute values are introduced.
- Audit transfer from Ramanujan residual bounds with the unit term and
  finite-head boundary explicit.
- Use finite-layer information only through proved arithmetic consequences;
  an explicit-formula identity cannot supply the missing upper bound.

## Audited transfers

`RHTower.abs_ccmPrimeDeficitCriticalEnergy_add_coprimeCrossWork_le`
bounds energy **plus** its signed coprime cross work; it supplies no lower
bound for the cross work separately.

`RHTower.pmRamanujanPrimeFeature_cutoff_invariant_square_nonpos`
gives a sign for prime-invariant inputs. The periodic divisor factor is
invariant under primes larger than its cutoff, but the physical Gaussian
weight is not. The exact cutoff formula retains both the source change
and the terminal band. Their contribution cannot be discarded.

The [Gaussian cross-sign test](../5-failed/b13-gaussian-prime-cross-sign.md)
now proves the failure of this general sign transfer for the literal
Gaussian moment. The even cofactor mask is invariant under odd primes,
yet its scaled cross form tends to `w_η(2)>0`, uniformly in every positive
moment order. The surviving atom is at `n=2p`; the complementary mass
vanishes. This fixes positive damping and a fixed mask, so it does not
decide the sign or size of the actual growing-cutoff centred current.

For a prime `p>W`, `P_W(pb)−P_V(pb)=P_W(b)−P_V(b)` when `V≤W`.
On the large-prime part this converts the periodic cofactor convolution
to the same periodic factor times the actual large-prime-divisor weight
`Σ_(p|n,p>U)log p`. This is not the constant harmonic mean. Prime-power
terms and the finite-head boundary must also remain explicit.


`ArithmeticDefectRigidity.TheSignedCofactorGramHasNoExtraCoordinates`
identifies the fixed receiver/residual/forcing Gram blocks as
`[[K,−K,0],[−K,K,0],[0,0,0]]` on escape. The forcing covariances
vanish after normalization. This is a result for the damped Möbius
receiver, not a bound for the Gaussian current above. Its uniform forcing-covariance bounds control the paid remainder,
but leave the receiver block `K` unbounded in the required arithmetic
sense. No transfer from this signed table to a bound for the Gaussian
prime current has been proved.
