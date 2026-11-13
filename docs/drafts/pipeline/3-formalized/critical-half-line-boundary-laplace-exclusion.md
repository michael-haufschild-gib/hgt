# Critical half-line boundary Laplace exclusion

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** B104, `review-1211/obstacles-summary.md` §2.2.
- **Statement:** Every actual critical half-line state has nonzero Laplace transform on the imaginary axis.

## Proof

**[PROVED HERE; Lean verified]** Suppose the actual state F has a Laplace zero at `iβ`, where `β=2πb`. Set `K=C_{0,b}F` and `H=Re K`.

Cancellation of the Laplace coefficient removes K's positive-half-line tail. Weighting by `exp(-4u)` changes its kernel to an exponentially decaying convolution, so the existing weighted L² theorem applies. Negative support then gives ordinary L² and, by weighted Cauchy–Schwarz, L¹. The same statements hold at the conjugate zero `-iβ`.

The causal and reflected anti-causal representations give
`(iβ-q)L_K(q)=πL_F(q)` on the two open sides of the imaginary axis, at every admitted moment. On the axis, approach from positive real part. Negative support gives the common L¹ majorants `|F|` and `|K|`; dominated continuity proves the same multiplied identity, including resonance. In Fourier normalization this is `2i(b+ξ) Fourier(K)(ξ)=Fourier(F)(ξ)`.

Taking norms and using `|ξ|≤|b+ξ|+|b|` gives
`(1+|ξ|)|Fourier(K)(ξ)| ≤ (1+|b|)||K||₁+||F||₁/2`.
The Gamma bracket's square-root bound makes the squared transform times the bracket integrable. Conjugation exchanges the two resolvents; H is their average. Thus H has all six actual energy-domain properties, including full Gamma integrability.

Averaging the multiplier identities gives
`2i(ξ²-b²) Fourier(H)(ξ)=ξ Fourier(F)(ξ)`.
Away from ±b this makes their pointwise real inner product zero. At either resonance the transform of F itself is zero. Hence the Gamma mixed density vanishes everywhere. F+H and F−H have equal Fourier modulus, therefore equal translated correlations and equal full prime sums. Quadratic polarization, justified by absolute summability on the actual weighted domain, cancels the symmetrized prime mixed form.

For real q in the half-pole strip, taking real and imaginary parts of the moment law eliminates `Im L_K(q)` and gives
`(q²+β²)L_H(q)=-πq L_F(q)`.
The coefficients at q=±1/2 are opposite; their common denominator is strictly positive. Consequently the polarized pole term also vanishes.

Test the state's actual weak equation against H. Only the exponential mixed mass remains. The verified weighted-resolvent identity makes it
`criticalAliasCoefficient(W₀) (4/π)||exp(-4u)K||₂²`.
Both scalar factors are positive. K vanishes almost everywhere; its multiplied Fourier identity and L¹ Fourier uniqueness force F to vanish almost everywhere, contradicting unit norm.

Combining this boundary exclusion with the existing open-right-half-plane theorem proves zero-freeness on the closed right half-plane. The existing unconditional critical-state existence dichotomy gives RH or such a state. No polar-charge or new analytic premise enters this conclusion.

## Formalization chain

Owner: `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/`.

1. `UndampedCausalLaplaceMoments`: verified.
2. `UndampedCausalFourierDecay`: verified.
3. `TheUndampedRealResolventHasTheActualDomain`: verified.
4. `SkewFourierPairsHaveZeroArithmeticMixedForm`: verified.
5. `TheUndampedRealResolventIsSkewInFrequency`: verified.
6. `TheUndampedRealResolventCancelsThePoleForm`: verified.
7. `TheCriticalHalfLineStateHasNoBoundaryLaplaceZero`: verified; final unconditional theorem `riemannHypothesis_or_exists_closedRightHalfPlaneLaplaceZeroFree_criticalHalfLineGroundState`.

Final check: `lake --old env lean GaloisForLFunctions/ArithmeticHodgeTheoryOfDegenerations/CausalReflection/TheCriticalHalfLineStateHasNoBoundaryLaplaceZero.lean` passed. Transitive `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. All seven modules are wired into the umbrella. The whole chain is one mathematical contribution.

Existing inputs: `UndampedCausalResolventBasicDomain`, `CausalResolventMixedEnergy`, `GammaIntegrabilityFromLinearFourierDecay`, and `TheCriticalHalfLineStateSatisfiesTheWeakEquation`. No new analytic premise is permitted in the final statement.
