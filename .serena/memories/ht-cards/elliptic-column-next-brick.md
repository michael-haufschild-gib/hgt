# Elliptic column — DONE list and what is next (2026-08-14)

## The compact-signature deck fixed field is CLOSED
`HTGeometry/PlaneScaleSimilarity.lean` — `planeScaleEquiv`, `planeScale_constPlane`,
**`planeScale_deriv`** (`(f(m·))′ = m·f′(m·)`, the similarity law).
`HTGeometry/EllipticRotationTail.lean` — `rotationEquiv`, `rotationAlgEquiv`, `rotationEquiv_jet`,
`rotationEquiv_deriv`, `rotation_fixes_jetPow`, `differentialAdjoin_jetPow_le_velocityField`,
`mem_differentialAdjoin_jetPow_of_rotation_invariant`,
**`setOf_deck_rotation_invariant_eq_differentialAdjoin_jetPow`** — the deck fixed field of a
compact parabolic signature on the generic reparametrisation is exactly `C⟨(u′)ⁿ⟩`.
Also `instance charZeroMeromorphicPlane`.
All axiom-clean, wired.

Full stack now in place (dependency order):
EllipticMeromorphicOrderTools → EllipticEvenPolynomialWeierstrass → EllipticEvenRationalWeierstrass
→ EllipticFunctionFieldWeierstrass;  MeromorphicPlaneField → MeromorphicPlaneDifferential →
MeromorphicPlaneTranslation → MeromorphicPlaneAlgebra → EllipticPlaneSubfield →
EllipticIsogenyDeck → EllipticIsogenyTailPlane;  CoefficientDerivation →
GenericReparametrization → ReparametrizationAutomorphism → {ReparametrizationDescent,
TwistedReparametrizationAutomorphism} → EllipticReparamProtocolTail → EllipticVelocityTail →
EllipticReparamCurrent → PlaneScaleSimilarity → EllipticRotationTail.

## NEXT
1. CARD 6 promotion assessment: its gate item was "complete-tail identification in the protocol
   presentation for the compact signatures".  That is now formal.  Re-read the card's gate list and
   decide whether every clause is discharged; if so, git-mv to `3-formalized/new_scientific_knowledge/ht/`,
   set Stage, add a formalized-companion file, fix relative links (follow the pattern of the already
   promoted `triptic-ht-kummer` card, see `mem:ht-cards/stage3-sweep-2026-08-13`).
2. CARD 4: items (1)(2)(5)(6)(7) formal for the elliptic column at DIMENSION ONE.  The gate says
   "full algebraic-group statement", so decide: build a several-variable `MeromorphicPlane` (ℂ^g)
   for general abelian varieties, or promote with the dimension-one scope stated explicitly.
3. CARD 5: fixed-field/groupoid descent + Lie–Cartan rank ≤ 3 (deep, untouched).
4. CARDS 1, 2, 3: untouched; recon in `mem:ht-cards/stage3-sweep-2026-08-13`.
   - card 1 needs Pong 5.9's conclusion, Andersson's divisor theorem, Saksman–Webb abscissa;
   - card 2 needs the triptic exact-image theorem + multiple-gamma signature computations;
   - card 3 needs Barnes asymptotics (4)-(6) and the Sibuya–Ramis exact Newton-slope theorem.
