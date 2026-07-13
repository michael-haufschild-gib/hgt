# Derivation is not a Frobenius twist

- **ID:** derivation-not-frobenius-twist
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/multi-q-abp-criterion.md` section 3 and
  `../2-fully-proven/parametrized-differential-abp-escape.md` sections A-B.
- **Statement:** A Leibniz operator that is also multiplicative is necessarily the zero map; hence a nonzero
  derivation-type operator cannot itself be the multiplicative Frobenius twist required by a Frobenius-ABP
  values-to-functions lift.

## Goal

This banks the exact finite algebraic floor behind the ABP-route type distinction: `partial_s` may be the
right derivation for parametrized-differential Galois theory, but a nonzero derivation cannot itself play the
role of a multiplicative Frobenius twist. It does not formalize ABP, Hardouin-Singer theory, Picard-Vessiot
rings, differential-algebraic Galois groups, Holder, or the open value-specialization arrow at `s=1`.

## Paper Proof

Let `D` be a Leibniz operator on a ring, so `D(xy)=D(x)y+xD(y)`. Applying this to `1*1` gives
`D(1)=D(1)+D(1)`, hence `D(1)=0` by additive cancellation.

If in addition `D` were multiplicative, `D(xy)=D(x)D(y)`, then for any `x`,
`D(x)=D(x*1)=D(x)D(1)=D(x)*0=0`. Thus `D` is the zero map. Equivalently, any Leibniz operator with some
`D(x) != 0` cannot satisfy multiplicativity.

## Gates

- [x] 0 -> 1  in-progress: exact algebraic type-obstruction lemma extracted from the ABP cards.
- [x] 1 -> 2  fully-proven: paper proof above by applying Leibniz and multiplicativity at `1`.
- [x] 2 -> 3  formalized: Lean theorems `map_one_eq_zero_of_leibniz`,
  `map_eq_zero_of_map_one_zero_of_map_mul`, `map_eq_zero_of_leibniz_of_map_mul`, and
  `not_map_mul_of_leibniz_of_exists_ne_zero` in `formal/GaloisForLFunctions/HTGeometry/DifferentialABP.lean`; names
  checked by scratch file; `#print axioms` uses only the allowed standard subset
  `[propext, Classical.choice, Quot.sound]`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the algebraic type-obstruction lemma in the ABP/F1 note.

## Door Passport

Door-2 strips this to elementary ring algebra, so it is BRIDGE. Its value is as the Lean-certified algebraic
floor for the claim that the derivation `partial_s` is the wrong type for a Frobenius-ABP twist, even though
it remains the right type for parametrized-differential Galois theory.

## Log

- 2026-06-19 - Leaner added the Lean theorem and this synced paper-proof ticket while inspecting the new ABP
  cards in `2-fully-proven`. The parent cards remain in `2-fully-proven` because their HS/ABP/Holder imports,
  function-level group statements, and value-specialization analysis are not fully Lean-formalized.
