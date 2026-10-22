# Xi-Descent Far-Field Empty-Census Deck-Charge Universality Law

- **ID:** xi-descent-far-field-empty-census-deck-charge-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of far-field loop drain and arbitrary-circle local/global deck-charge census
- **Statement:** Every far-right Xi point has a descended zero-free ball on which every smaller circle has an empty enclosed-zero census, zero additive charge, unit deck character, empty local-charge product, and unit Xi/Xi-descent carrier charges at every dyadic rung.

## Goal

Close the gap between local far-field charge triviality and global circle factorization.  The
common descended center and same dyadic rung supply the connector; emptiness of the exact census is
stronger than merely restating zero loop charge.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, exact `lake env lean` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Use Euler-product nonvanishing at `Re ρ > 1`, the square-descent identity, and local analyticity to
extract a zero-free ball around `(ρ-1/2)^2`.  Intersect that radius with the existing far-field
loop-drain radius.  Apply the arbitrary-circle census theorem to every smaller circle and prove its
finite census is empty from ball nonvanishing.

## Proof

`[PROVED HERE]` For `Re ρ > 1`, Euler-product nonvanishing gives `xi ρ ≠ 0`.  The square-descent
identity identifies this with nonvanishing of `xiDescent` at `c=(ρ-1/2)^2`; `c` lies in the slit
plane, so local analyticity and continuity give a zero-free ball about `c`.  Intersect its radius
with the all-rung far-field drain radius.

For every smaller circle, ball nonvanishing supplies boundary avoidance and interior
nonvanishing.  The arbitrary-circle theorem then returns a finite census `t` whose members are
exactly the interior Xi-descent zeros; therefore `t=∅`.  Its local/global identities identify the
loop charge with the empty weighted sum and the deck character with the empty carrier-charge
product.  The far-field drain theorem supplies the simultaneous values `0,1,1,1`.

## Novelty audit

- **Status:** `[LEAN PROVED — LITERATURE AUDITED]`
- Classical argument-principle literature identifies contour winding with enclosed
  zero multiplicity, and zero-free half-plane literature supplies the standard far-right zeta
  anchor; see Freitas,
  [*A Li-Type Criterion for Zero-Free Half-Planes of Riemann's Zeta Function*](https://doi.org/10.1112/S0024610706022599),
  and Stankov,
  [*Zero-free half-planes of the ζ-function via spaces of analytic functions*](https://arxiv.org/abs/2206.00434).
- Lodone studies the argument of Riemann's Xi function off the critical line
  ([arXiv:0904.1051](https://arxiv.org/abs/0904.1051)).
- Li–Mahboubi formalize winding-number root counting in Isabelle/HOL
  ([arXiv:1804.03922](https://arxiv.org/abs/1804.03922)), but not this Xi descent or dyadic
  charge factorization.
- Targeted searches found no exact square-descended far-field theorem simultaneously identifying
  an empty zero census, empty additive/multiplicative local factorizations, and all dyadic
  loop/deck/carrier charge avatars.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiDescentFarFieldEmptyCensusDeckChargeUniversalityLaw`
- Main theorem:
  `RHTower.xiDescent_farField_emptyCensusDeckChargeUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/XiDescentFarFieldEmptyCensusDeckChargeUniversalityLaw.lean`
  (exit 0, no output)
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Axiom audit and module build deferred to required final audit; no intermediate `lake build`.

## Log

- 2026-07-23 — created in 1-in-progress after terminal-module descent-cluster scan.
- 2026-07-23 — exact Lean proof completed and post-proof literature audit found no exact prior law.
