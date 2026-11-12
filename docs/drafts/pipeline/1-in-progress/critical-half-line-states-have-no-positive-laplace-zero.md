# Critical half-line states have no positive Laplace zero

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B104; a spectral substitute for positivity of the state.
- **Statement:** At the finite global window threshold, every actual critical state F satisfies `L_F(s)=∫ F(u) exp(su) du ≠ 0` for every real `s>0`.
- **Status:** Support, real representatives, weighted domain closure, exact energy defect and correlation preservation verified in Lean. Pole-product and final nonvanishing modules written; compilation incomplete. Not counted.

## Proposed argument

Assume `L_F(s)=0`. Put
`G(u)=∫_{v<u} exp(-s(u-v)) F(v) dv` and `H=-F+2sG`.

1. For `u≥0`, the convolution tail is `exp(-su)L_F(s)`, hence zero.
   Thus G and H retain negative-half-line support.
2. H is the literal `causalBlaschkeStep (s/π) (cx F)`. Its Fourier
   multiplier has modulus one, preserving full Gamma energy. Polarized
   Plancherel and the translation character preserve every actual translated
   correlation, hence every prime term and the complete prime sum.
3. For the two pole moments, prove `L_F(q)=(s-q)L_G(q)` and
   `L_H(q)=(s+q)L_G(q)`. When `q<s`, exponential weighting leaves an
   integrable causal kernel. When `q>s`, the vanishing total Laplace
   integral gives the anti-causal representation of G; its weighted kernel
   is integrable. At `q=s`, the first identity is the assumed zero.
   Therefore `L_F(1/2)L_F(-1/2)=L_H(1/2)L_H(-1/2)`, including `s=1/2`.
4. Weighting by `exp(-4u)` shifts the resolvent rate from s to s+4.
   The exact L² multiplier identity gives
   `I₈(F)-I₈(H)=16s I₈(G)`.
5. Full-domain nonnegativity and the critical state's zero energy imply
   `0≤Q(H)=Q(F)-16s α(W₀)I₈(G)`. Since `s,α(W₀)>0`, G has zero norm.
   The nonvanishing resolvent multiplier then forces F to have zero norm,
   contradicting its defining unit norm.

No classical derivative of the actual state is used. The remaining domain
work must establish every admissibility field for H. No unproved regularity
or factorization condition may enter the final ground-state theorem.

## Lean inputs and status

Proved corpus inputs:

- `RHTower.fourier_causalBlaschkeStep`: literal convolution multiplier.
- `RHTower.causalLaplaceWeighted_convolution`: unrestricted exponential weighting.
- `HTGeometry.convolutionKernel_op_eq_fourierMulCLM`: actual L² convolution.
- `RHTower.integral_conj_fourier_mul_fourier`: actual L¹∩L² polarization.
- `HTGeometry.fourier_translate`: exact translation character.

Verified:

- `HTGeometry/CausalExponentialZeroReflection`: **verified** lower/upper Laplace formulas, support preservation, kernel-rate shift.
- `HTGeometry/CausalExponentialReflectionEnergy`: **verified** actual L² convolution, exact shifted-resolvent energy defect, Fourier-modulus preservation.
- `HTGeometry/WeightedCausalExponentialReflection`: **verified** actual weighted L² closure and exact weighted norm defect.
- `HTGeometry/RealCausalExponentialReflection`: literal real representatives, measurability, support, L¹ and weighted L² closure.
- `HTGeometry/FourierModulusDeterminesActualCorrelation`: preservation of every literal translated correlation.
- `HTGeometry/CausalExponentialLaplaceReflection`: causal/anti-causal moment laws, resonance-inclusive pole-product identity and actual resolvent injectivity.
- AHT/`TheCausalReflectionPreservesPrimeAndGammaEnergy`: prime/Gamma invariance and every reflected-domain field.

Written, unchecked:

- AHT/`TheCausalReflectionPreservesThePoleProduct`: opposite pole-moment invariance, including resonance.
- AHT/`TheCriticalHalfLineStateHasNoPositiveLaplaceZero`: exact full-form defect and actual-state nonvanishing.

The actual-state zero-energy and weak-equation framework is on the
[causal-coordinate card](../3-formalized/critical-half-line-states-have-causal-logarithmic-coordinates.md).

This does not identify the arithmetic polar source with a Laplace moment,
nor prove its pairing with F is nonzero.
