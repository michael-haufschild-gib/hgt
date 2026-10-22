# CCM exterior cosine dual mass wall

- **ID:** ccm-exterior-cosine-dual-mass-wall
- **Stage:** 3-formalized
- **Type:** universal quantitative obstruction
- **Route:** CCM exterior finite-measure gauge quotient
- **Status:** [LEAN-PROVED] [NOVELTY-PLAUSIBLE]
- **RH used:** no
- **Computation used:** no

## Audited frontier

[CORPUS] `CCMActualHeadExteriorCosineMeasureGauge.lean` realizes arbitrary positive-minus-positive
finite exterior measures as exact aperture-null quadratic gauges.

[CORPUS] `CCMActualHeadExteriorCosineSuperoscillation.lean` proves one canonical atomic family can
approximate lower-frequency cosines, but its total variation grows exponentially.  That left open
whether noncanonical or non-atomic exterior measures evade the cost.

[CORPUS] `SoninReferenceTailSup.lean` supplies a uniform Fourier-tail majorant tending to zero, and
`SoninScaledMeanBound.lean` supplies exact compact-bump mass scaling.  Corpus search found no theorem
coupling these facts to arbitrary CCM exterior measures.

## Theorem

Fix `H₀>0` and `0≤ε<1`.  For every sequence of finite positive measures `μ_N,ν_N` supported on
`[H₀,∞)`, suppose their cosine-transform difference approximates the constant mode `1` with error
at most `ε` wherever the width-`N+1` Sonin bump is nonzero.  Then

~~~text
μ_N(ℝ) + ν_N(ℝ) → +∞.
~~~

In fact, for every fixed `p : ℕ`,

~~~text
(μ_N(ℝ)+ν_N(ℝ)) / (((N+1)H₀)^p) → +∞.
~~~

The finite-width certificate is the sharper inequality

~~~text
(1-ε) J₀ ≤ 2 S((N+1)H₀) (μ_N(ℝ)+ν_N(ℝ)),
~~~

where `J₀>0` is exact reference-bump mass and `S(R)→0` is the uniform exterior Fourier-tail
majorant.

## Proof architecture

1. Establish product integrability and Fubini for a Sonin bump paired with an arbitrary CCM cosine
   measure gauge.
2. Exterior support bounds every inner cosine pairing by `4δ S(δH₀)`.
3. Positive-minus-positive triangle inequality charges the sum of the two measure masses.
4. Compact-window approximation to `1` supplies the fixed positive lower pairing
   `2δ(1-ε)J₀`.
5. Cancel `2δ`; since `S((N+1)H₀)→0`, combined mass tends to infinity.
6. Reuse `tendsto_pow_mul_soninRefTailSup_atTop`; because every polynomially weighted tail still
   vanishes, combined mass divided by every fixed power of scaled window width tends to infinity.

No atomicity, canonical coefficient representation, moment finiteness, or RH premise occurs.

## Scientific conclusion

Canonical superoscillation blow-up is not an artifact of binomial coefficients.  Every exterior
finite-measure representation that maintains any fixed subunit error on expanding compact windows
must lose bounded or polynomially growing total variation.  Thus local density and globally
polynomially controlled Fourier–Stieltjes mass are incompatible at expanding scale.

This does not prove RH and does not yet exclude mass-divergent gauges.  Next exact question is a
fixed-point comparison: corrected-symbol Gamma recovery is logarithmic in frequency while the
dual mass floor inherits rapid Fourier decay.  If every positivity construction must control a
window large enough to recover its own mass loss, those rates may be incompatible.

## Lean certificate

Module:

~~~text
GaloisForLFunctions.RHTower.CCM.CCMActualHeadExteriorCosineDualMassWall
~~~

Main theorem:

~~~text
tendsto_exteriorCosineMeasureGauge_mass_atTop_of_constant_approximation
~~~

Verification:

- direct `lake env lean` source check passed;
- targeted `lake build GaloisForLFunctions.RHTower.CCM.CCMActualHeadExteriorCosineDualMassWall` passed;
- all ten public theorem axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden-declaration scan is empty;
- module is wired into `GaloisForLFunctions.RHTower`; no umbrella/full build was run.
