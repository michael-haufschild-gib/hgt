# Gamma payment for a frequency-dependent pair remainder

- **Stage:** 1-in-progress.
- **Inputs:** `BesselGammaSpectralFloor`, `thetaFullApertureTail_remainder_le`.
- **Target:** Pay the complete infinite remainder uniformly in polynomial degree, retaining a finite head whose size grows with frequency.

The existing rectangular remainder is bounded by `aD exp(−π(M+1))`, with `D` uniform over `0<a<1/2`. The new first-atom floor suggests
`A₁₁(a,b)≥aC/cosh(πb/2)`, where
`C=4π^(−1/2)exp(−2(π exp(1)+1))>0`.
Restricting the center integral to `[1/2,1]` should prove this explicit aperture reserve.

Choose a fixed `K` paying `D exp(−πK)≤C/2`, then set `M(b)=ceil(|b|/2+K)`. The proposed payment is

`|S(a,b)−Σ_(n,m≤M(b))S_nm(a,b)|≤aC/(2cosh(πb/2))≤A₁₁(a,b)/2`.

Multiplication by `P(b)²` and integration would give
`∫P²|S−Head|≤(aC/2)∫P²/cosh(πb/2)` for every polynomial, with no degree restriction. The moving cutoff is measurable because it is a ceiling of a continuous function; every fixed pair head is continuous. The Gamma reserve supplies integrability.

This pays only the infinite remainder. Positivity of the growing finite head, including its aggregate unequal-pair loss, remains the substantive unresolved inequality. No independent phase substitution is made. Production formalization is under audit in `CompletedArithmeticForms/GammaAdaptivePairPayment.lean`; the upstream Gamma floor has compiled with only standard axioms.
