# The additive deck-charge calculus (Phase A)

- **ID:** deck-charge-calculus
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — the Phase-A "reusable formal calculus of root-torsor charges"
- **Source:** Phase A of `../../rh-monodromy-weight-mismatch/00-apporach-reorientation.md`
  ("Build the deck-charge calculus"). Builds the **additive** `ℤ/2^k` face on top of the existing
  multiplicative geometric deck apparatus (`DeckCocycle`, `DeckMultiZero`, `DeckMonomial`,
  `AnnulusRootGluing`, `SignatureParity`).
- **Statement:** The obstruction to lifting a nonvanishing holomorphic `f` through `z ↦ z^n` around
  the two-chart annulus cover — read off multiplicatively from the enclosed integer zero-index as
  `deckRed n idx ∈ μ_n` — is given its additive avatar `wCharge n idx = (idx : ℤ/n)`, and the two
  faces are proven to be **one object** under a group isomorphism `ℤ/n ≃* ⟨deckUnitHom n⟩ ≤ ℂˣ`
  (`deckIso`). The three Phase-A deliverables — additivity, power law, vanishing ⟺ root existence —
  are formalized in the additive register, together with the dyadic-tower coherence, the
  boundary-crossing formula, and the additive conservation law.

## Goal

The multiplicative deck class `deckRed n ∈ μ_n` and its geometric root-torsor calculus already exist
(`deckClass`, `deckClass_mul`, `deckClass_prod`, `deckClass_monomial`, root-existence
`deckClass_eq_one_iff_exists_root`, deformation invariance `deckClass_deformation_invariant`). What
Phase A names but the tree did **not** carry as a clean reusable object is the **additive charge**
`w_k(γ;f) ∈ ℤ/2^k` with its additive laws, and — crucially — the identification of that additive
charge with the multiplicative deck class as an element of a **cyclic group** (so it obeys an
additive conservation law, the spine of the program's dynamic front). This card builds exactly that
missing face and welds it to the existing multiplicative side. mathlib has no argument principle /
winding number (`grep` confirms), so the loop obstruction is realized — as the tree already does —
via the two-chart cover, not via a contour integral; that realization is complete here in additive
form.

## The Lean certificate (axiom-clean)

`GaloisForLFunctions/RHTower/DeckChargeCalculus.lean` (32 declarations, all
`[propext, Classical.choice, Quot.sound]` or subsets, lint green, in the `RHTower` umbrella):

- **The object** — `wCharge n idx = (idx : ZMod n)`, the additive deck charge of the enclosed index.
- **Deliverable 1 (additivity)** — `wCharge_add`: `w(fg) = w(f) + w(g)` (orders of a product add),
  with multiplicative face `deckChar_mul`.
- **Deliverable 2 (power law)** — `wCharge_intMul`/`wCharge_nsmul`: `w(f^r) = r • w(f)`, with
  multiplicative face `deckChar_nsmul` (`deckChar (r • x) = deckChar x ^ r`).
- **Deliverable 3 (vanishing ⟺ root)** — `wCharge_eq_zero_iff` (`w = 0 ↔ n ∣ idx`),
  `wCharge_eq_zero_iff_deckRed_eq_one` (`↔ deck class trivial`), and the geometric closure
  `exists_root_iff_wCharge_zero`: on any valid two-chart cover (with the deck class identified with
  the charge, supplied concretely by `box_deckClass_eq_deckChar_wCharge`/`box_charge_eq_deckRed`),
  `wCharge n idx = 0 ↔ f` admits a global analytic `n`-th root across the cover.
- **The calculus spine (new unification)** — `deckChar` (the `n`-th-root-of-unity character on
  `ℤ/n`), `deckChar_wCharge` (the two avatars agree), `deckChar_injective`, `deckChar_pow_eq_one`
  (image in `μ_n`); packaged as the injective hom `deckUnitHom : Multiplicative (ℤ/n) →* ℂˣ` and the
  group isomorphism `deckIso : Multiplicative (ℤ/n) ≃* ⟨deckUnitHom n⟩`. This is the exact sense in
  which the multiplicative deck class **is** the additive charge: `ℤ/n ≅ μ_n ≤ ℂˣ`.
- **Dyadic-tower coherence** — `wCharge_tower` (the reduction `ℤ/2^k ↠ ℤ/2^j` carries the rung-`k`
  charge to the rung-`j` charge) and `wCharge_eq_zero_of_le` (triviality descends the ladder). The
  additive `2^k`-ladder structure, mirroring `rhLadder_of_le`.
- **Dynamic-front deliverables** — `wCharge_boundary_crossing` (`w(after) − w(before) = w(net
  crossing)`; zero-free ⟹ invariant), `wCharge_sum`/`deckChar_sum`, and
  `interior_charge_conservation` (outer-boundary charge `0` ⟹ interior box charges sum to `0` in
  `ℤ/n`) — the additive conservation law the program's dynamic front (Phase E) rests on.
- **Deformation transfer** — `wCharge_eq_of_deckRed_eq`: equal deck class ⟹ equal charge, so the
  existing multiplicative homotopy invariance (`deckClass_deformation_invariant`) transfers to the
  additive charge.

## Approach

Everything rides on `SignatureParity.deckRed` (`k ↦ exp(2πik/n)`, a homomorphism `(ℤ,+) → (ℂ,×)`
with kernel `nℤ`, factoring through `ℤ/n`) and `box_charge_eq_deckRed` (the box deck class is
`deckRed n (Σmᵢ)`). The additive charge is the tautological residue `(idx : ℤ/n)`; its laws are the
ring-hom laws of `Int.cast`. The character `deckChar n x = deckRed n (ZMod.val x)` transports
`deckRed` along the canonical section `ZMod.val`, and `deckRed_eq_iff_zmod` makes it well-defined,
injective, and multiplicative — hence a group monomorphism `ℤ/n ↪ ℂˣ` onto `μ_n`. No carrier, no
operator, no flow is constructed: every statement is a property of the *given* index data, and the
charge is a cocycle/obstruction invariant (rule 7 — constraint, not flow).

## Verdict — dual gate

**DELIVERED (formalized):** the additive deck-charge calculus is proven, machine-checked, axiom-clean,
and integrated. Phase A's three named deliverables (additivity, power law, vanishing ⟺ root
existence) hold in the additive `ℤ/2^k` register; the additive and multiplicative faces are unified
by an explicit group isomorphism `ℤ/n ≅ μ_n`; the dyadic-tower coherence, boundary-crossing formula,
and additive conservation law are all in place.

**Graded as branch infrastructure (a mathlib-gap fill / consolidation):** the cyclic-group iso
`ℤ/n ≅ μ_n` and the elementary charge laws are reduce-to-known group theory; formalizing them and
welding the additive face to the pre-existing multiplicative geometric apparatus is legitimate
Phase-A infrastructure ("a reusable formal calculus, not an RH proof attempt", per the source), not
new mathematics. Significance is proximity to the program: the additive charge is what makes the
conservation law (`interior_charge_conservation`) and the ladder-descent (`wCharge_eq_zero_of_le`)
first-class, so the deck class stops being "a complex number that happens to be a root of unity" and
becomes "an element of the cyclic group `ℤ/2^k`."

**What it opens (springboards, per the program):** (1) **Phase E — charge motion**: the conservation
law + boundary-crossing formula are the additive seeds; the pair-annihilation rule and the interior
conservation theorem for admissible FE-symmetric deformations build directly on
`interior_charge_conservation`. (2) **Phase C/quadrant-local charge**: the additive face makes
"symmetric-aggregate charge vanishes mod 4" a statement about `wCharge (2^k)` reductions
(`wCharge_tower`), sharpening the search for a quadrant-local detector. (3) **the contour/winding
realization** awaits a mathlib argument principle — a separate complex-analysis prerequisite, not a
gap in this calculus. (4) feeding `wCharge_eq_zero_of_le` back to `RHLadderTheory`/`DeckWindow` to
express the whole `RH_{2^k}` ladder additively.

## Log
- 2026-07-07 — created in 3-formalized: the additive deck-charge calculus built end-to-end
  (`DeckChargeCalculus.lean`, 32 decls, axiom-clean, lint green, umbrella-imported). `wCharge` object
  + additivity/power/vanishing deliverables; `deckIso : ℤ/n ≅ μ_n` unifying the additive and
  multiplicative faces; dyadic-tower coherence `wCharge_tower`/`wCharge_eq_zero_of_le`;
  boundary-crossing `wCharge_boundary_crossing`; additive conservation `interior_charge_conservation`;
  deformation transfer `wCharge_eq_of_deckRed_eq`. Loop/contour realization confirmed mathlib-blocked
  (no argument principle) and correctly routed via the two-chart cover.
