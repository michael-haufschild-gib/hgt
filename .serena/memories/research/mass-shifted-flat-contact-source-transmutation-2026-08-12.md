# Mass-shifted flat-contact source transmutation (2026-08-12)

## Hostile correction
Worldline identity `u' Γ = 2 n y x² h_n` and normalized form control relative mass `Γ/h_n` only in positive chamber. They do not imply absolute terminal mass extinction forces speed escape, because Route U's flat face has `h_n=0`. Prior interpretation in the worldline card/report was corrected.

## New theorem
At positive flat canonical shifted-Xi face:
[
V=∂_yP_n=X^2P_n'-nXP_n+[X^{n-1}]P_n,P_n.
]
Proof uses head-positive canonical adjoint source law, flat kernel annihilation, and positivity on difference (D=V-R).

For differentiable simple root branch:
[
x'=-x^2,qquad (x^{-1}-y)'=0.
]

At tangential face this hard-root freeze combines with existing singular producer:
[
mathcal F_n'=(2n+1)mathcal A_n^sharp,
]
where adaptive completed mixed `P^sharp` source is formed before reflection aggregation.

## Lean
New module:
`formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionFlatContactSourceTransmutation.lean`

Six capstones:
- `momentInner_xiShiftedCanonicalAdmissionCovariantVelocity_eq_generatorAdjoint_of_headPosDef`
- `finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_normRemainder_of_flatFace`
- `finitePolynomialVelocity_xiShiftedCanonicalAdmission_eval_root_of_flatFace`
- `xiShiftedCanonicalAdmission_flatRootCurve_deriv_eq_neg_sq`
- `hasDerivAt_xiShiftedCanonicalAdmission_reciprocalHardRoot_zero_of_flatFace`
- `xiShiftedCanonicalAdmission_flatTangent_hardRootFreeze_and_completedSource`

Direct Lean and targeted lake build pass. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.

## Exact open core
Contact-order transmutation replaces speed-tightness proposal. Remaining split:
1. positive terminal mass: source-derived positive-axis Padé atom extinction/local boundedness;
2. zero terminal mass: exploit parity-doubled radical plus first nonzero higher contact source.
Contact orientation does not anchor absolute hard-root level. RH remains open.

## Docs
- formalized card: `docs/drafts/pipeline/3-formalized/mass-shifted-contact-order-source-transmutation.md`
- report addendum equations 9.3.659–9.3.663
- corrected prior worldline and transverse-capacity cards.
