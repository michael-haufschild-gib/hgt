# Group-like and cyclotomic extensions of the field-one core

- **ID:** field-one-group-cyclotomic-extensions
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION / CONSTRUCTION (Lean)
- **Labels:** `[LITERATURE] [BRIDGE] [PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Depends on:** `field-one-multiplicative-core`,
  `field-one-signed-band-axis`
- **Statement:** Every commutative group with zero is canonically obtained by
  adjoining an absorbing zero to its unit group. Conversely, adjoining zero to
  any abelian group produces a field-like pointed commutative monoid. Its
  contracted scalar extension is the corresponding group algebra. Taking the
  cyclic group `C_n` gives the cyclotomic extension usually denoted
  `F_(1^n)`.

## Complete paper proof

Let `G` be an abelian group. The set

`G₀={0}⊔G`

becomes a commutative group with zero by extending multiplication on `G` and
declaring zero absorbing. Every nonzero element lies in `G` and is invertible.
The unit group of `G₀` is canonically `G`.

Conversely, let `K` be a commutative group with zero. Every nonzero element of
`K` is a unit. Define

`φ:{0}⊔Kˣ→K`

by `φ(0)=0` and `φ(u)=u.val`. It preserves multiplication and is injective:
zero cannot equal a unit value, and equality of unit values implies equality
of units. It is surjective: zero is hit by zero, and nonzero `x` is hit by the
unit with value `x` and inverse `x⁻¹`. Thus `K≃WithZero(Kˣ)`.

For a commutative semiring `R`, contracted scalar extension kills the adjoined
zero basis vector. The remaining monoid is `G`, hence

`R[G₀]^c=R[G]`.

Taking `G=C_n` yields

`F_(1^n)={0}⊔C_n`,
`R[F_(1^n)]^c=R[C_n]`.

For `n=1`, the group is trivial and this is `F₁^mult`. For `n=2`, the
multiplicative carrier is `{0,1,−1}`, the carrier underlying `F₁±`; the band
null relation is additional data and reduces ring base extension from
`R[C₂]` to `R`. ∎

## Hostile audit

1. **`F_(1^n)` has `1^n` elements — `FALSE`.** The notation is mnemonic; the
   carrier has `n+1` elements when `C_n` is finite.
2. **Group-like extension adds addition — `FALSE`.** It adds roots of unity
   multiplicatively.
3. **Every extension is cyclic — `FALSE`.** Arbitrary abelian unit groups give
   group-like extensions; cyclic groups are the cyclotomic subfamily.
4. **`F_(1^2)` and the initial band are identical structures — `FALSE`.**
   Their pointed-monoid carriers agree, but the band includes balanced null
   sums.

**Verdict:** `REDISCOVERED` / `BRIDGE`.

## Gates

- [x] 0 → 1: extension notion typed in the pointed-monoid doctrine.
- [x] 1 → 2: two-way classification and scalar extension proved.
- [x] 2 → 3: exact Lean theorem package and axiom audit complete.
- [ ] 3 → 4: publication-ready extraction.

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.FieldOneCyclotomicExtensions`
- **Theorems:** `groupExtensionUnitsEquiv`,
  `commGroupWithZeroClassification`, `groupExtension_isUnit_of_ne_zero`,
  `card_cyclotomicFieldOne`
- **Audit:** direct `lake env lean` and final targeted `lake build` passed;
  `#print axioms` reports only standard Lean principles.

## Log

- 2026-07-26 — group-with-zero classification isolated from band null
  relations; paper proof closed.
- 2026-07-26 — formalized unconditionally; targeted build, axiom audit, and
  project lint passed; cyclotomic family integrated into doctrine atlas.
