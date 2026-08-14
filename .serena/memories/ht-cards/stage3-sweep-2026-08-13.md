# HT stage-2 → stage-3 sweep (`2-fully-proven/new_scientific_knowledge/ht`)

State as of 2026-08-14.

## PROMOTED
- `nonautonomous-rational-first-order-tail-orbifold-law` (card 6) → `3-formalized`, with certificate.
- `nonautonomous-isogeny-tail-time-splitting` (card 4) → `3-formalized`, with certificate.
  Closed by the complex-torus column in every dimension — see
  `mem:ht-cards/card4-complex-torus-stack-plan`.

## STILL IN 2-fully-proven (4 cards)

### `nonautonomous-rational-complete-tail-orbifold-classification` (card 5)
Gate: "formalize fixed-field/groupoid descent and the global orbifold signature reduction".
BOTH named items are now formal (2026-08-14):
- `RationalPrefixDifferentialAdjoin.lean` — the §1 descent for an ARBITRARY rational map:
  `derivationClosed_adjoin_of_ratMapEval`, `differentialAdjoin_le_adjoin_ratMapEval`,
  `finrank_differentialAdjoin_ratMapEval_le` (`[L : K] ≤ deg P`),
  `finiteDimensional_differentialAdjoin_ratMapEval`.  Generalises `RadicalDifferentialAdjoin`
  (the `y ↦ y^N` case) via the chain rule `g′ = (u′/W)·Q(g)²`, `W = P′Q − PQ′`.
- `RationalPrefixDeckDescent.lean` — `differentialAdjoin_ratMapEval_eq_fixedField`,
  `finrank_differentialAdjoin_ratMapEval_eq_card`.
- `NonautonomousCompleteTailOrbifoldLaw.lean` — `twelve_dvd_of_forall_holonomyOrder_dvd`
  (12 is the LEAST universal charge), `completeTail_orbifold_reduction`,
  `completeTail_frozen_charge`.
**Residue, and the only one**: the Lie–Cartan/Casale classification of proper transitive rational
differential groupoids on a curve into `G1/G2/G3`.  The card CITES it as a published parent; its two
consumers are already formal.  Formalizing it means building transitive Lie pseudogroups and
`D`-envelopes on a curve — absent from mathlib in any form.  DO NOT promote until that exists.

### `hypertranscendental-pair-localization-noncompression` (card 2) — CLOSEST TO DONE
Algebraic core formal (`PairFacePrivateSector`), order-one atomic parent corpus-owned
(`EllipticGammaAtomicOverDAExtension`), `Ψ ∈ Q` proved (`EllipticGammaConeSource`,
`ellipticGammaSource_mixed_difference`).
Missing: the canonical carrier `F_e = ∏_{k∉e} Δ_{τ_k} Ψ_{d-1}`, its signatures (4) `S_e(F_e) ≠ 0`
and (5) `S_f(F_e) = 0` for `f ≠ e`, and the resulting boundary-noncompression no-go.  The
direct-sum private field additionally needs the exact-image parent, which belongs to the all-depth
card, not this one.

### `irrational-power-canonical-products-…-gevrey-slope-rigidity` (card 3)
Open gate: "unconditional analytic Lean formalization".  Needs the Barnes expansion (4)–(6) and the
Sibuya–Ramis exact Newton-slope theorem.

### `helson-universal-ht-arbitrary-divisor-orthogonality` (card 1)
Abstract layer formal; Pong's HYPOTHESIS discharged (`PrimeSupportNotFinitelyGenerated`).
Missing: the CONCLUSIONS of Pong 5.9, Andersson Thm 5, Saksman–Webb/Seip.
