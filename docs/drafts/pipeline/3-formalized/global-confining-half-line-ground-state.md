# Global simplicity of the confining half-line ground state

- **Stage:** 3-formalized
- **Target:** B16, B17; signed ground states and variation of the ratio.
- **Statement:** For every positive ratio, the actual full half-line energy has an attained unit-mass floor with a unique minimizing state line. Every nonzero minimizing profile has zero-free Laplace transform in the open right half-plane.

## Corpus connection

`criticalHalfLineFullEnergy_realCausalReflection` and its paired complex analogue preserve the arithmetic terms and lose a strictly positive weighted resolvent energy. `integral_mul_translate_realCausalReflection` preserves ordinary square mass at translation zero. Subtracting the variational floor times square mass therefore preserves the reflection defect. A Laplace zero of an attaining profile forces its resolvent, and then the profile, to vanish.

Two distinct minimizing lines would yield a nonzero minimizing combination with one prescribed positive real Laplace zero. Excluding it proves global simplicity without a one-sign assumption.

## Paper proof

Fix `R>0`. Write `λ=inf{E_R(H): H in the actual domain, ∫H²=1}`. Positive confinement gives coercivity, and a reflected normalized tilted spline makes the range nonempty. The actual-domain compactness proof on the ground-energy branch card attains `λ`.

Homogeneity gives `E_R(G)≥λm(G)` for positive mass. At zero mass, coercivity gives `E_R(G)≥0=λm(G)`. Therefore `Q_R=E_R-λm` is nonnegative throughout the domain.

Suppose an attaining profile `G` has a positive real Laplace zero at `s`. Its real causal reflection at `a=s/π` remains in the actual domain. `integral_mul_translate_realCausalReflection` at translation zero preserves `m(G)`. The exact energy defect gives

`Q_R(reflect(G))=-a(R)(16a/π)∫resolvent(G)²exp(-8u)`.

The coefficient is positive. Nonnegativity of `Q_R` forces the weighted integral to vanish. The exponential weight is everywhere positive; resolvent integrability then gives zero resolvent almost everywhere. Injectivity of causal exponential convolution gives `G=0` almost everywhere.

At a nonreal zero `z` with positive real part, use the real representative of the conjugate reflection pair with rates `a=Re(z)/π>0`, `b=Im(z)/(2π)≠0`. `integral_mul_translate_realPairedCausalReflection` at translation zero again preserves square mass. The paired defect is a positive coefficient times the sum of two nonnegative weighted resolvent energies. Its vanishing kills the first resolvent, and injectivity kills `G`. Thus every nonzero attaining profile has no Laplace zero in the open right half-plane.

If `H,K` attain the floor, applying `Q_R≥0` to `H+K` and `H-K` forces their mixed shifted form to vanish. Every linear combination therefore attains the homogeneous floor. Their Laplace values at `s=1` are nonzero. Subtracting `K` times the ratio of those values produces an attaining profile with Laplace value zero, hence the zero profile. Thus `H` is proportional to `K` almost everywhere. Unit mass makes the scalar `±1`.

This is an unconditional classification for every `R>0`, independent of RH or a finite global threshold. No sign condition on the profiles enters. Polar nonvanishing and boundary regularity remain separate.

## Lean status

`CausalReflection/ConfiningHalfLineGroundStateRigidity.lean` passed its final plain source audit. The unconditional theorem `exists_unique_laplaceZeroFree_halfLineEnergyMinimizer` depends exactly on `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into the umbrella.

The homogeneous zero-exclusion lemmas cover all attaining profiles. `halfLineEnergyMinimizer_eq_laplace_ratio_ae` identifies their scalar relation, and `halfLineEnergyMinimizer_unique_up_to_sign` classifies normalized minimizers.
