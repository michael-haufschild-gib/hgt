# Elliptic column of ht cards 4/5/6 — state and plan (2026-08-13, checkpoint 4)

## DONE — all axiom-clean, all wired into `GaloisForLFunctions.HTGeometry`
1. Elliptic function field theorem — `mem:ht-cards/elliptic-function-field-theorem-proved-2026-08-13`
2. Meromorphic plane field carrier — `mem:ht-cards/meromorphic-plane-field-carrier-2026-08-13`
3. Generic reparametrisation — `mem:ht-cards/generic-reparametrization-built-2026-08-13`
4. `EllipticIsogenyDeck.lean`, 5. `EllipticIsogenyTailPlane.lean`,
6. `TwistedReparametrizationAutomorphism.lean`, 7. `ReparametrizationDescent.lean`,
8. `EllipticReparamProtocolTail.lean`
9. `EllipticVelocityTail.lean` — the payoff module:
   `velocityField = differentialAdjoin ℂ {jet 0}`,
   **`deckInvariantField_eq_velocityField`** = card 4 item (6),
   **`differentialIndependent_jet_zero`** + **`eq_constPlane_of_algebraMap_mem_velocityField`**
     = card 4 item (7) (dtrdeg 1 = dim, and `T ∩ C(G) = C`),
   plus `velocityField_eq_adjoin_range_jet`, `aeval_jet_eq_algebraMap`,
   `algebraicIndependent_jet`, `algebraMap_mem_velocityField_of_const_coeff`.
   In the degree-expanding branch the reversible quotient is trivial, so item (2) = item (6).

## CARD 4 remaining for a HONEST stage-3 promotion
The elliptic column is done at DIMENSION ONE over ℂ. "Full algebraic-group statement" would need
abelian varieties of dimension `g`: the same construction over `ℂ^g/Λ`, which needs a
several-variable analogue of `MeromorphicPlane` (codiscrete filter in `ℂ^g`, several-variable
meromorphic functions — mathlib is thin here). Decide whether to (a) build that, or (b) promote with
an explicit statement of the dimension-one scope. Prefer (a) per the no-shortcuts directive.

## CARD 6 (compact signatures) — NEXT BRICK, plan
Deck group = translations + rotation of exact order `n ∈ {2,3,4,6}`.
- translations act by `ReparamField.fieldEquiv` (fix the jets) → tail `ℂ⟨jet 0⟩` (already proved);
- the rotation `ζ` acts by `ReparamField.twistFieldEquiv` with `c = ζ`, i.e. `jet i ↦ ζ · jet i`;
- inside `ℂ⟨jet 0⟩` (a FREE rank-one differential field over ℂ by
  `differentialIndependent_jet_zero`) the corpus theorem
  `RootOfUnityScalingFixedField.setOf_rootOfUnity_invariant_eq_differentialAdjoin_pow`
  gives the invariant field `ℂ⟨(jet 0)^n⟩` — the card's compact-signature current.
- Downstairs identification: corpus `EuclideanOrbifoldCurrents.weierstrass_square_current_div`
  etc. give `(jet 0)^2 = (P′)²/(4P³ - g₂P - g₃)` with `P = algebraMap ℘`.
WARNING (from `mem:ht-cards/stage3-sweep-progress-2`): passing implicit palettes as `adjoinLift`
families to the rotation theorem causes a whnf defeq explosion; define the generator explicitly.

## CARD 5
fixed-field/groupoid descent + Lie–Cartan rank ≤ 3 classification (separate, much deeper).
