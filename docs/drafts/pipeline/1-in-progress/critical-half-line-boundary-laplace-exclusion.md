# Critical half-line boundary Laplace exclusion

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B104, `review-1211/obstacles-summary.md` §2.2.
- **Statement:** Every actual critical half-line state has nonzero Laplace transform on the imaginary axis.

## Mechanism

At a boundary zero, the undamped modulated causal resolvent retains negative-half-line support and belongs to L¹∩L² with the actual exponential square weight. Test the critical-state weak equation against its real part. Its Fourier multiplier is purely imaginary; symmetrized prime and Gamma mixed terms should vanish. Opposite half-pole moments should cancel. The remaining weighted mixed term is a positive multiple of the resolvent's weighted square norm.

## Open proof obligations

- Neutral-rate Laplace identity, including the Fourier boundary: `UndampedCausalLaplaceMoments` passed Lean.
- Fourier decay and actual complex-resolvent Gamma-domain admission: `UndampedCausalFourierDecay` passed Lean.
- Symmetric prime, Gamma and half-pole mixed cancellations.
- Zero resolvent implies zero state; unconditional RH dichotomy.

## Exact identities

Put `K=C_{0,b}F`, `H=Re K`, and `β=2πb`. The proposed moment law is
`(iβ-q)L_K(q)=πL_F(q)`, including purely imaginary q. Hence
`2i(b+ξ) Fourier(K)(ξ)=Fourier(F)(ξ)` and
`(1+|ξ|)|Fourier(K)(ξ)| ≤ (1+|b|)||K||₁+||F||₁/2`.
For real q, `(q²+β²)L_H(q)=-πq L_F(q)`.
At q=±1/2 the two coefficients are opposite, cancelling the polarized pole term.
The real-part Fourier multiplier is purely imaginary away from ±b; its
symmetrized translated correlations and Gamma mixed density vanish.
The surviving weighted mixed term is `(4/π)||exp(-4u)K||₂²`.

## Formalization chain

Owner: `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/`.

1. `UndampedCausalLaplaceMoments`: verified.
2. `UndampedCausalFourierDecay`: verified.
3. `TheUndampedRealResolventHasTheActualDomain`: verification running.
4. `SkewFourierPairsHaveZeroArithmeticMixedForm`: drafted.
5. `TheUndampedRealResolventIsSkewInFrequency`: drafted.
6. `TheUndampedRealResolventCancelsThePoleForm`: drafted.
7. `TheCriticalHalfLineStateHasNoBoundaryLaplaceZero`: drafted; final unconditional theorem `riemannHypothesis_or_exists_closedRightHalfPlaneLaplaceZeroFree_criticalHalfLineGroundState`.

No contribution counted before the entire chain and transitive axiom audit pass.

Existing inputs: `UndampedCausalResolventBasicDomain`, `CausalResolventMixedEnergy`, `GammaIntegrabilityFromLinearFourierDecay`, and `TheCriticalHalfLineStateSatisfiesTheWeakEquation`. No new analytic premise is permitted in the final statement.
