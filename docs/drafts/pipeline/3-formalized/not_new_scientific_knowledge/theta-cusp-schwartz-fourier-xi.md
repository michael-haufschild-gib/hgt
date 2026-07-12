# Theta-cusp Schwartz Fourier realization of Xi

- **ID:** theta-cusp-schwartz-fourier-xi
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** An explicit rescaling of the positive theta-cusp Schwartz source has Fourier transform exactly equal to the centered completed Xi function on the real spectral axis.

## Theorem

Let

\[
k_\Xi(x)=2\pi\,\Phi(2\pi x),
\qquad \Phi(x)=\thetaCuspFullSource(x).
\]

The source `k_Ξ` is constructed as the Schwartz map `xiThetaSchwartzSource`. With mathlib's Fourier
normalization,

\[
\widehat{k_\Xi}(t)=\Xi_C(t)
\qquad(t\in\mathbb R).
\]

The proof uses the unconditional positive cosine representation of `XiC`, global evenness and
Schwartz integrability of `Phi`, and the exact `2*pi` Fourier scaling. It uses no zero data and no RH
hypothesis.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCuspSchwartzFourierXi`
- Scaled raw transform: `fourier_thetaCuspSchwartz_scaled`
- Explicit normalized source: `xiThetaSchwartzSource`
- Exact Fourier identity: `fourier_xiThetaSchwartzSource`
- Exact Xi energy formula:
  `spectralMeasureForm_xiThetaSchwartzSource_self_eq_integral_xiRealNormSq`
- Null-source atomicity:
  `spectralMeasure_eq_sum_smul_dirac_xiRealZeroSet_of_null_xiThetaSchwartzSource`

## Consequence

For every positive temperate spectral measure `mu`, nullity of the explicit source `k_Ξ` forces
`mu` to be the sum of its atoms on the real Xi zero set. This discharges the previously open Fourier
realization hypothesis in the Hedenmalm divisor-supported metric chain. It does not establish source
nullity or metric conservativity and therefore does not prove RH.
