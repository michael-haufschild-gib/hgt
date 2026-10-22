# Virtual-character Frobenius reciprocity for Artin monomial multiplicities

- **ID:** `artin-virtual-character-frobenius-reciprocity`
- **Stage:** 3-formalized
- **Type:** THEOREM (finite-character infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** the multiplicity of an induced linear character in a virtual character equals the
  multiplicity of that linear character in the restricted virtual character.

## Exact formal result

`formal/GaloisForLFunctions/RHTower/Artin/ArtinVirtualFrobeniusReciprocity.lean` proves the finite
pairing symmetry `characterPairing_comm`, then proves

```text
virtualCharacter_monomial_pairing_restriction:
  <theta, Ind_H^G chi>_G = <Res_H theta, chi>_H,

monomialMultiplicity_eq_restriction_linearMultiplicity:
  monomialMultiplicity G theta H chi
    = virtualMultiplicity H (theta.restrict H.subtype) (linearVirtualCharacter H chi).
```

All carriers are concrete virtual characters, induced representations, restricted representations,
and integral multiplicities.  No `FrobeniusReciprocal` proposition or analytic-order interface is
introduced.

## Paper proof

For an actual finite-dimensional representation the equality is ordinary Frobenius reciprocity.
The character pairing is symmetric, and both sides are additive and negation-compatible in the
first argument.  Closure induction over the actual `FDRep` character generators extends the
equality to every concrete virtual character.  Existing multiplicity casts identify the two
integral coefficients.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinVirtualFrobeniusReciprocity.lean` passed.
- `lake build GaloisForLFunctions.RHTower.Artin.ArtinVirtualFrobeniusReciprocity` passed; this is the
  targeted module build, not an umbrella or full build.
- `/tmp/ArtinVirtualFrobeniusReciprocityAxioms.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for all three exported theorems.
- The leaf is imported by `formal/GaloisForLFunctions/RHTower.lean`; the umbrella was deliberately
  not built.

## Anti-theatre boundary

This is not the Heilbronn restriction theorem for actual Artin orders: no global Artin L-function,
continuation, order character, or local effectivity is yet formalized.  It supplies the exact
finite-character equality that those future analytic derivations must use.

## Log

- 2026-08-15 — source-checked a closure-induction proof in `/tmp/VirtualFRScratch.lean`; opened
  after Maschke and local-factor infrastructure audits exposed the missing virtual-character bridge.
- 2026-08-15 — formalized, target-built, axiom-audited, and wired without an umbrella build.
