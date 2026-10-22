# Universe-polymorphic Frobenius reciprocity for Artin characters

- **ID:** `artin-frobenius-reciprocity-universe-polymorphic`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Status:** `[LEAN-PROVED] [BRIDGE]`

## Exact claim

Let `phi : H -> G` be a homomorphism of finite groups. Let `rho` be a finite-dimensional complex
representation of `H` and `sigma` one of `G`; their carriers may live in unrelated universes.
Then there is a complex-linear equivalence

```text
Hom_G(Ind_phi rho, sigma) ~= Hom_H(rho, Res_phi sigma).
```

Consequently, for the normalized character pairing,

```text
pair_G(char(Ind_phi rho), char(sigma))
  = pair_H(char(rho), char(Res_phi sigma)).
```

The statement uses actual representations, actual intertwining maps, and the actual induced
coinvariant module. It does not postulate an induced-character formula or a Frobenius-reciprocity
proposition interface.

## Paper proof

For `F : Ind_phi rho -> sigma`, send `F` to

```text
v |-> F([1 tensor v]).
```

The coinvariant relation and `G`-equivariance of `F` make this map `H`-equivariant. Conversely, for
an `H`-intertwiner `f : rho -> Res_phi sigma`, define on elementary tensors

```text
g tensor v |-> sigma(g^-1)(f(v)).
```

The `H`-intertwining identity makes this descend to coinvariants, and the result is
`G`-equivariant. Direct evaluation on generators proves the two maps inverse. All constructions
are complex-linear.

For finite groups, normalized pairing of actual characters equals the complex cast of the
dimension of the corresponding intertwining space. Apply this identity on both sides and use
dimension invariance under the displayed linear equivalence.

## Higher principle exposed

Function-level induced-character sums are coordinates for a more universal fact: induction is
left adjoint to restriction. The Artin/Heilbronn route should transport order data through this
adjunction, using explicit character sums only where local Frobenius determinants require them.
This removes a false dependency on a prematurely chosen coset formula and preserves arbitrary
universes.

## Significance boundary

This is a genuine missing theorem in the available Lean surface and a necessary bridge to
Heilbronn multiplicity identities. It does not prove Brauer induction, positivity of a Heilbronn
character, or any analytic Artin L-function statement.

## Lean target

Formalize a universe-polymorphic linear equivalence between raw `Representation.IntertwiningMap`
spaces by descending the explicit tensor formula to coinvariants. Add the general
representation-pairing theorem and derive exact pairing reciprocity. No `sorry`, `admit`, new
axiom, `opaque`, `unsafe`, or target-equivalent proposition interface.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/Artin/ArtinFrobeniusReciprocity.lean`.
- Explicit adjunction: `indResIntertwiningEquiv`.
- Pairing theorem: `characterPairing_induced_restricted`.
- Source check:
  `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinFrobeniusReciprocity.lean`.
- Targeted olean audit:
  `lake build GaloisForLFunctions.RHTower.Artin.ArtinFrobeniusReciprocity`.
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella deliberately not built.
