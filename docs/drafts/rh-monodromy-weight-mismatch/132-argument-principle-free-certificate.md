# 132 — Phase B closed: the RH ladder is certified contour-integration-free, and the deck charge is a named observable

Phase B of `00-apporach-reorientation.md` asks for the RH ladder formalized *without
argument-principle dependence*. The equivalences were already Lean theorems (docs 91, 92);
what was only asserted — in prose and docstrings — is the defining adverb: *without the
argument principle*. This closes Phase B by (i) turning that adverb into a machine-checked
build gate, and (ii) packaging the ladder rung as a single named `μ_{2^k}`-valued
observable with its full torsor structure.

## 1. The certificate (`RHTower/ArgumentPrincipleFree.lean`)

The argument principle counts enclosed zeros by a loop integral `(2πi)⁻¹ ∮ f'/f` — a
*flow*. The ladder here is proved from a *constraint*: the `2^k`-th-root branches are fixed
algebraically on two slit charts and their monodromy `exp(2πi·m/n)` is read off the jump
`log I − log(−I) = 2πi` of the principal logarithm (`deckClass_monomial`); divisibility is
forced pointwise by `analyticOrderAt_pow` (`root_orders_dvd`); roots are peeled and glued
(`exists_root_iff_orders_dvd`). No loop is transported and no integral evaluated.

The file makes this checkable. For a named declaration it walks the whole transitive
constant-dependency closure of its proof term (value and type) and verifies:

- **no contour-integration constant** appears — nothing whose name carries `circleIntegral`,
  `circleMap`, or `intervalIntegral`. In mathlib every contour integral is one of these, so
  their joint absence certifies that no argument-principle mechanism enters.
- **no axiom** beyond mathlib's three (`propext`, `Classical.choice`, `Quot.sound`) — in
  particular no `sorryAx`.

Both share one traversal; a violation raises an elaboration error, so the property is
enforced whenever the file is built. Scope is contour integration specifically, not
integration in general: ξ is built from `completedRiemannZeta₀`, a Mellin integral over
`(0,∞)`, so the closure *does* contain `MeasureTheory.integral` — the real integral that
*defines* the object, not the loop integral that would *count* its zeros. The argument
principle is exactly the loop integral, and that is what is absent.

Certified (each ≈ 4800–4900 constants scanned, all clean): the engine
(`root_orders_dvd`, `pow_root_unique`, `exists_root_iff_orders_dvd`,
`coherentTower_iff_nonvanishing`, `nonvanishing_of_exists_roots_all_two_powers`,
`deckClass_eq_one_iff_exists_root`); the half-plane ladder (`rhLadder_iff_root`,
`rh_iff_forall_ladder`, `rh_iff_tower`, `rh_iff_exists_roots_all_two_powers`); the u-plane
slit form (`rhLadder_iff_root_slitPlane`, `rh_iff_forall_root_slitPlane`,
`rh_iff_xiDescent_coherentTower_slitPlane`); the deck-cocycle realization (`xi_deckClass`,
`xi_deckClass_eq_one_iff_ladder_dvd`, `deckClass_monomial`, `xi_deckClass_eq_sign_product`,
`rhLadder_iff_forall_deck_trivial`, `rh_iff_forall_deck_trivial`); the charge observable
(§2); and `rh_iff_xi_ne_zero_right` tying it to mathlib's `RiemannHypothesis`.

**Self-validating.** Two positive controls (`doubledTrace_pairing`,
`trace_parity_spectral_dichotomy`) are the spectral side of the root-trace holonomy, which
integrates by design; the file asserts they *do* carry `intervalIntegral`/`circleMap`. Were
the traversal blind to integration, those lines would raise. Their success witnesses that
the traversal detects contour integration where present, so the clean verdict on the ladder
is not vacuous.

## 2. The deck charge as a named observable (`RHTower/XiDeckCharge.lean`)

The rung `RHLadder k` is a per-zero divisibility condition. It is now one function of a
point,

    xiDeckCharge k ρ = exp(2πi · ord_ρ(ξ) / 2^k)  ∈  μ_{2^k},

the monodromy of the `2^k`-th-root torsor around ρ. Written from the vanishing order, so
root-choice independent; yet equal to the deck class of any actual pair of chart roots
(`xiDeckCharge_eq_chart_deckClass`, realized by `exists_chart_roots_deckClass_eq_xiDeckCharge`),
so it is genuine monodromy, not bookkeeping. Then:

- `rhLadder_iff_xiDeckCharge_one` : `RHLadder k ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → xiDeckCharge k ρ = 1`
  — the rung is the vanishing of the charge, stated directly over `rightHalf` with no box
  exhaustion.
- `rh_iff_xiDeckCharge` : RH ↔ the charge vanishes at every level and every right-half zero.

Torsor structure:
- `xiDeckCharge_pow` : it is a `2^k`-th root of unity.
- `xiDeckCharge_succ_sq` : `w_{k+1}² = w_k` — the dyadic tower.
- `xiDeckCharge_conj`, `xiDeckCharge_one_sub`, `xiDeckCharge_quadruple` : constant on the
  `V₄` orbit `{ρ, 1−ρ, ρ̄, 1−ρ̄}`.
- `xiDeckCharge_one_eq_neg_one_pow` : `xiDeckCharge 1 ρ = (−1)^{ord}` — the base rung is the
  classical parity sign (the μ₂ face of the tower).
- `xiDeckCharge_eq_one_iff_le_ladderHeight` : at a zero, `w_k = 1 ↔ k ≤ ladderHeight ρ` —
  the charge stratifies the divisor by 2-adic height.

## 3. State

`GaloisForLFunctions.MainTheorems` builds green (9264 jobs) with both files wired into the
`RHTower` umbrella; formal lint passes; all certified statements are axiom-clean. Phase B's
deliverable — the ladder as a deck-torsor object, proved without the argument principle — is
now a self-checking artifact rather than a claim.

## 4. What this opens

The charge is a `μ_{2^k}`-valued function on ℂ, constant on `V₄` orbits, whose vanishing
locus off the line is the open content. Two forward objects sit on it directly, neither a
contour flow:

1. The charge is defined for *any* completed FE-symmetric entire carrier, not only ξ. The
   `V₄`-invariance and the parity face used only `xi_orderAt_conj`/`xi_orderAt_one_sub`
   (Schwarz + FE). Abstracting `xiDeckCharge` to a carrier class with those two symmetries
   isolates exactly which carriers force `w_1 = 0` off the seam — the Goldilocks question
   (Phase H) posed on the charge rather than on the zeros.
2. The `k = 1` face `(−1)^{ord}` pairs the charge with the boundary functional of the
   root-trace holonomy (`trace_parity_spectral_dichotomy`, doc 122): parity of the charge is
   positivity of an L² pairing. Certifying the *order* side integration-free while the
   *spectral* side integrates by design (the two controls) is the precise seam between the
   constraint reading and the flow reading of the same invariant — the place to push next.

## 5. Weld with the additive charge (`RHTower/DeckChargeBridge.lean`)

A parallel formalization (`DeckChargeLadder`/`DeckChargeCalculus`) carries the rung's deck
charge in the **additive** avatar `ladderCharge k ρ = ord_ρ(ξ) mod 2^k ∈ ℤ/2^k`, on the
abstract `wCharge`/`deckRed` calculus. That is the same object as `xiDeckCharge` here in the
**multiplicative, geometric** avatar. The bridge makes it one:

- `xiDeckCharge_eq_deckRed` : `xiDeckCharge k ρ = deckRed (2^k) (ord)` — the geometric charge
  is the abstract multiplicative deck value at ξ's order.
- `xiDeckCharge_eq_deckChar_ladderCharge` : `xiDeckCharge k ρ = deckChar (2^k) (ladderCharge k ρ)`
  — it is the deck character of the additive charge.
- `xiDeckCharge_eq_one_iff_ladderCharge_zero` : the geometric triviality (a global chart root
  glues) is the additive vanishing (divisibility) — the two agents' rung conditions are one.

So the algebraic charge calculus (conservation, reflection-depth invisibility, the
quadrant-local motivation) and the geometric monodromy realization (chart-root deck class,
the argument-principle-free ladder, the certificate) are two faces of a single `μ_{2^k}`-valued
observable on the ξ-divisor. The weld is itself certified contour-integration-free and
axiom-clean.

## 6. The charge, abstracted to any carrier (`RHTower/CarrierDeckCharge.lean`)

`xiDeckCharge` is the `f = ξ` case of one object on *any* analytic carrier:

    carrierCharge f k ρ = deckRed (2^k) (ord_ρ(f)) = exp(2πi·ord_ρ(f)/2^k).

Nothing about ξ enters the definition or the structural laws (`carrierCharge_pow`,
`carrierCharge_succ_sq`, `carrierCharge_zero`, `carrierCharge_eq_one_iff_dvd`). What ξ
contributes is isolated as *hypotheses*:

- `exists_root_iff_carrierCharge_trivial` : on a convex open Ω with a marked nonvanishing
  point and a locally finite zero set, `f` has an analytic `2^k`-th root iff its charge is
  trivial at every zero — the Kummer obstruction as one observable, for an arbitrary carrier.
- `carrierCharge_conj` / `carrierCharge_one_sub` / `carrierCharge_quadruple` : the charge is
  `V₄`-invariant *exactly* for carriers with Schwarz reflection and the functional equation —
  the two symmetries, made into hypotheses rather than facts about ξ.
- `carrierCharge_one_eq_neg_one_pow` : the μ₂ face `(−1)^{ord}` for any carrier.

`xiDeckCharge_eq_carrierCharge` (in `DeckChargeBridge`) confirms ξ's charge is this object at
`f = ξ`; the ξ-specific content is only the geometric chart-root realization and the tie to
mathlib's `RiemannHypothesis`. This is the deck-torsor object in the generality later seam
operations act on, and it poses the Goldilocks question — which FE-symmetric carriers force
`carrierCharge f 1 = 1` off the seam — on the charge, not on the zeros. (Reads a *given*
carrier's order; constructs no carrier.)

## 7. The seam, machine-graded (`RHTower/HolonomyChargeBridge.lean` + §1 grading)

The base charge is read a second way: `trace_holonomy_eq_carrierCharge_one` shows that for any
carrier with an isolated zero, every continuous square-root trace around a circle returns
multiplied by `carrierCharge f 1 ρ`. The endpoint holonomy of the circle trace *is* the deck
charge. The certificate then separates three rungs by their dependency footprint, each gate
machine-checked:

- `carrierCharge_one_eq_neg_one_pow` — no circle path, no loop integral (pure constraint).
- `trace_holonomy_eq_carrierCharge_one` — uses the circle as a *path* (`circleMap`) but
  evaluates no loop integral (`#assert_no_loop_integral`).
- `doubledTrace_pairing` — the spectral reading adds the loop integral (`intervalIntegral`).

So charge → circle-path holonomy → spectral functional is a graded ascent from constraint to
flow, with the charge pinned at the constraint end. The order-linked reading of the invariant
never integrates; only the spectral reading does. This is the constraint/flow boundary of the
lane made into a build-checked fact rather than a slogan.
