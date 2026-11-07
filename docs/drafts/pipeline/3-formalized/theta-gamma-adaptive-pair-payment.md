# Gamma payment for a frequency-dependent pair remainder

- **Stage:** 3-formalized.
- **Inputs:** `BesselGammaSpectralFloor`, `thetaFullApertureTail_remainder_le`.
- **Statement:** One first-atom Gamma reserve pays the complete infinite remainder in every polynomial degree, retaining a finite head whose size grows with frequency.

The rectangular remainder is bounded by `aD exp(−π(M+1))`, with `D` uniform over `0≤a<1/2`. The first-atom floor is
`A₁₁(a,b)≥aC/cosh(πb/2)`, where
`C=4π^(−1/2)exp(−2(π exp(1)+1))>0`.
Restricting the center integral to `[1/2,1]` supplies this explicit aperture reserve.

Set `K=max(0,log(2(D+1)/C)/π)` and `M(b)=ceil(|b|/2+K)`. Then

`|S(a,b)−Σ_(n,m≤M(b))S_nm(a,b)|≤aC/(2cosh(πb/2))≤A₁₁(a,b)/2`.

Multiplication by `P(b)²` and integration gives
`∫P²|S−Head|≤(aC/2)∫P²/cosh(πb/2)` for every polynomial, with no degree restriction. The moving cutoff is measurable because it is a ceiling of a continuous function; every fixed pair head is continuous. The Gamma reserve supplies integrability.

This pays only the infinite remainder. Positivity of the growing finite head, including its aggregate unequal-pair loss, remains the substantive unresolved inequality. No independent phase substitution is made.

Lean: `CompletedArithmeticForms/GammaAdaptivePairPayment.lean`.
Capstones: `firstAtom_aperture_gamma_lower`, `gammaAdaptivePair_remainder_le`,
`firstAtom_pays_gammaAdaptivePair_remainder`, `polynomial_gammaAdaptivePair_remainder_payment`.
Final ordinary audit passed; all four use only `propext`, `Classical.choice`, `Quot.sound`. Wired into the umbrella.
