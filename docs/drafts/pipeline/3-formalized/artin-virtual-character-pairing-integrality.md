# Artin virtual-character pairing integrality

- **ID:** `artin-virtual-character-pairing-integrality`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[LEAN-PROVED] [BRIDGE]`

## Exact claim

Let `G` be a finite group. For complex functions on `G`, define the normalized character pairing

```text
pair_G(chi, psi) = |G|^-1 * sum_{g in G} psi(g) chi(g^-1).
```

Using the concrete genuine- and virtual-character closures from
`artin-virtual-character-restriction-foundation`:

1. If `V,W` are actual finite-dimensional complex representations, then
   `pair_G(char(V),char(W)) = dim_C Hom_G(V,W)`.
2. If `chi,psi` are genuine characters, their pairing is the complex cast of a natural number.
3. If `chi,psi` are virtual characters, their pairing is the complex cast of an integer.

No irreducibility, character-basis completeness, or Artin-holomorphy premise occurs.

The first statement is formalized for arbitrary carrier universes, not only bundled `FDRep`
objects.

## Paper proof

For actual representations, the averaging projector on `Hom_C(V,W)` has image
`Hom_G(V,W)`. Its trace is both the dimension of that invariant subspace and

```text
|G|^-1 * sum_g char(W)(g) char(V)(g^-1).
```

This proves (1). The group order is nonzero in `C`, so normalization is legitimate.

The pairing is additive in each argument. Induct first over the additive-monoid closure defining
one genuine character and then over the other. At generator pairs, (1) gives a natural number;
zero and addition preserve natural-number casts. This proves (2).

Repeat the double induction over the additive-group closures defining virtual characters. At
generator pairs, cast the natural dimension to an integer. Zero, addition, and negation preserve
integer casts. This proves (3).

## Significance boundary

This is required representation-theoretic infrastructure. It makes virtual-character
multiplicities intrinsically integral from actual representations. It does not yet prove
irreducible decomposition, induction formulas, Brauer induction, Heilbronn positivity, or any
analytic statement about Artin L-functions.

## Lean target

Formalize normalized pairing and all three claims over the concrete closure carriers. Use
`FDRep.scalar_product_char_eq_finrank_equivariant` for generator pairs and closure induction for
the extensions. No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, or target-equivalent
proposition interface.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/Artin/ArtinVirtualCharacterPairing.lean`.
- Exact normalization: `characterPairing`.
- Actual-representation generator theorem: `fdCharacterPairing_eq_finrank`.
- Universe-polymorphic actual-representation theorem:
  `representationCharacterPairing_eq_finrank`.
- Closure theorems: `genuineCharacterPairing_eq_natCast` and
  `virtualCharacterPairing_eq_intCast`.
- Source check:
  `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinVirtualCharacterPairing.lean`.
- Targeted olean audit:
  `lake build GaloisForLFunctions.RHTower.Artin.ArtinVirtualCharacterPairing`.
- `#print axioms` audit of every theorem reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella deliberately not built.
