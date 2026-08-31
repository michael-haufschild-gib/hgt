# ULF-TAFM-20 observer-clock interaction anomaly

Paper: docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/observer-clock-multiplier-descent-interaction-anomaly-and-literal-escape-law.md

Formalized:
- formal/GaloisForLFunctions/HTGeometry/ObserverClockInteractionAnomaly.lean
- formal/GaloisForLFunctions/RHTower/SuzukiClockInteractionAnomaly.lean
- Stage-3 certificate in corresponding topologically-admitted-formation-mechanics folder.

Core law: row+column marginals M are a vector subspace but not an ideal under scale-only pointwise clock multiplication. Anchored interaction I tests M exactly. For separated rate/organ observable,
I(rate ⊠ organ)(a,b)=(rate(a)-rate(1))*(organ(b)-organ(1)).
A scale multiplier preserves every marginal iff rate is constant (assuming a non-anchor organ point). Anomaly action on all marginals reconstructs rate modulo constants. Constant clock action, including FE sign/phase subgroup, is explicitly information-neutral.

Literal landing: completed harmonic-to-square-root Suzuki rate paired with fixed Fin 2 sign reporter has anomaly
-2*(lambda_R(k)-lambda_R(1)); existing lambda_R(k)>=k+1 for k>=3 yields escape above every real ceiling. This is unconditional and not RH.

Verification: scratch and direct Lean pass; targeted builds generic 8779/8779 and literal 12878/12878; 10 audited capstones depend only on propext, Classical.choice, Quot.sound. New modules contain no forbidden declarations. Wired into HTGeometry.UniversalLawField; literal also into RHTower; umbrellas not built. Global lint currently fails only on five unrelated concurrent unreachable modules.

Research consequence: clock noncompactness survives marginal quotient as a canonical reconstructive mixed interaction class. Remaining RH producer is source-specific signed control of the literal pre-quotient anomaly before positivity/marginalization loses orientation. Absolute Selberg weighting and generic phase/Fock averaging were attacked and rejected as old-gap redressings.