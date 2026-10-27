# Every nonzero absolutely continuous dilation part has a visible successor

- **ID:** every-absolutely-continuous-dilation-part-has-a-visible-successor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), uncredited supporting mathematics
- **Source:** APD topic 6; sufficiency direction of `successor-visible-spectrum-is-absolutely-continuous`
- **Statement:** Every finite positive measure on ℝ whose Lebesgue absolutely continuous part is nonzero is the prescribed positive-dilation measure of a positive-definite function on Aff(ℚ) with nonconstant successor on ℚ∖{0}.

## Exact result

Let ν be a finite positive measure and νa = Leb.withDensity(dν/dLeb).
If νa ≠ 0, there exists φ : Aff(ℚ) → ℂ such that:

1. every finite Gram form of φ is real and nonnegative;
2. for every positive rational unit u,
   `φ(dilation u) = ∫ exp(i γ log u) dν(γ)`;
3. no complex constant equals `φ(translation b)` for every nonzero rational b.

The entire prescribed measure is retained, including its singular part. No
continuity, smoothness, compact support, or boundedness of its density is
required beyond finite mass. This is the positive realization direction;
singular-continuous blindness and the proposed `2νa(ℝ)` oscillation bound are
not conclusions of this card.

## Proof

Write ν=νa+νs by Lebesgue decomposition. Both measures are finite. Push νa
forward by γ↦γ/(2π), obtaining an absolutely continuous measure μ. If
w=dμ/dLeb, the function G=√w belongs to L² and satisfies |G|²=w almost
everywhere. Let H be its inverse unitary Fourier transform. Translation–
modulation exchange and Plancherel give, for every real t,

`∫ H(x+t) conj(H(x)) dx = ∫ exp(iγt) dνa(γ)`,

and `∫|H|²=νa(ℝ)>0`. The frequency rescaling accounts exactly for the
Fourier convention `exp(−2πixξ)`.

For positive rational slope a and rational translation b, define

`φa(b,a)=∫ exp(i b exp x) H(x+log a) conj(H(x)) dx`.

Translations of H and multiplication by a unimodular phase preserve L²;
Hölder makes every Gram product integrable. The affine composition identity
expresses each finite Gram form as the integral of a squared norm. Thus φa is
positive definite on the positive-slope subgroup. Extend it by zero to the
whole rational affine group using subgroup induction.

Its successor is `S(b)=∫exp(i b exp x)|H(x)|² dx`. Suppose S is constant
on the nonzero rationals. Dominated convergence along b=1/(n+1) identifies
that constant with S(0). Hence for each nonzero rational b the nonnegative
integrand `(1−cos(b exp x))|H(x)|²` has integral zero. Countability gives one
full-measure set on which every such identity holds. At a point with nonzero
energy, b=1 forces exp x=2πk for a nonzero integer k; then b=1/(4k) forces
cos(π/2)=1, a contradiction. Thus H would vanish almost everywhere, contradicting
its positive squared norm. The successor is nonconstant.

Finally set `φs(g)=∫|slope g|^(iγ) dνs(γ)`. Each integrand is a unitary
character; integrating its squared-norm Gram identity proves positivity.
Its successor equals the constant νs(ℝ). Therefore φ=φa+φs is positive
definite, has exactly ν as positive-dilation measure, and remains nonblind.

## Lean declarations

- `HTGeometry.AbsolutelyContinuousMeasuresAreAutocorrelations`:
  `exists_L2_rnDeriv_wave`, `exists_L2_autocorrelation_density`,
  `exists_L2_autocorrelation_eq_charFun`.
- `ArithmeticPositiveDuality.EverySquareIntegrableWaveHasAVisibleSuccessor`:
  `memLp_realAffVec`, `isPosDefOnGroup_realAffPosDef_of_memLp`,
  `realAffPosDef_nonblind_of_memLp`, `successor_sees_L2_autocorrelation`.
- `ArithmeticPositiveDuality.EveryDensityHasAVisibleAffineExtension`:
  `blindArchState`, `isPosDefOnGroup_blindArchState`,
  `exists_nonblind_affine_extension_of_absolutelyContinuous`,
  `exists_nonblind_affine_extension_of_positive_ac_mass`,
  `exists_nonblind_affine_extension_of_ac_part_ne_zero`.

## Verification and significance

All three individual source checks pass with `lake --old env lean`; the main
transitive axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`. Both umbrellas import their finished modules; no umbrella was
compiled. Only missing new oleans required by the final leaf were built.

This is classical Fourier realization applied to the corpus's affine state,
extending the existing compactly supported continuous-profile examples to
every finite density. It supplies no source-prescribed mixed arithmetic data
and no self-dual spectral identity. Wall 3.16 remains open. No significant
RH-contribution credit is assigned; accepted count remains **0 / 250**.
