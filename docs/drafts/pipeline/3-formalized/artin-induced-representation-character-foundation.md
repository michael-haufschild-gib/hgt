# Artin induced-representation character foundation

- **ID:** `artin-induced-representation-character-foundation`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[LEAN-PROVED] [BRIDGE]`

## Exact claim

Let `G` be a finite group, `H <= G`, and let `rho` be a finite-dimensional complex
representation of `H` on a carrier in an arbitrary universe. Form the standard induced
representation

```text
Ind_H^G(rho) = (C[G] tensor_C V)_H
```

with its actual `G`-action. Then:

1. `Ind_H^G(rho)` is finite-dimensional over `C`.
2. Its character belongs to the concrete generator set `CharFD(G)` after canonical coordinate
   smallification.
3. Hence its character defines a concrete genuine character and, canonically, a concrete virtual
   character of `G`.

No formula is postulated for induced characters. No proposition asserting that an arbitrary
function is induced or a character is introduced.

## Paper proof

Because `G` is finite, `C[G]` is finite-dimensional. Tensoring it with finite-dimensional `V`
remains finite-dimensional, and passing to coinvariants is a quotient, hence remains
finite-dimensional. The standard action on the coinvariants is therefore an actual
finite-dimensional representation of `G`.

Choose the canonical basis of its carrier indexed by `Fin(dim)`. Conjugating the action by the
coordinate equivalence gives an `FDRep` model on `Fin(dim) -> C`. Trace is invariant under this
equivalence, so its `FDRep` character is exactly the character of the original induced
representation. Thus that function lies in `CharFD(G)`, hence in its additive-monoid closure and
additive-group closure.

## Significance boundary

This closes the universe obstruction between mathlib's induced representation and `FDRep`. It is
required infrastructure, not a proof of the induced-character sum formula, Frobenius reciprocity,
Brauer induction, Heilbronn positivity, or Artin holomorphy.

## Lean target

Wrap `Representation.ind H.subtype rho`, prove its character is an `fdCharacterSet` generator via
`representation_character_mem_fdCharacterSet`, and construct the genuine and virtual character
elements. No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or target-equivalent proposition
interface.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/Artin/ArtinCharacterInduction.lean`.
- Actual induced action: `inducedRepresentation`.
- Generator theorem: `inducedRepresentation_character_mem_fdCharacterSet`.
- Closure objects: `inducedGenuineCharacter`, `inducedVirtualCharacter`.
- Source check: `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinCharacterInduction.lean`.
- Targeted olean audit: `lake build GaloisForLFunctions.RHTower.Artin.ArtinCharacterInduction`.
- `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella deliberately not built.
