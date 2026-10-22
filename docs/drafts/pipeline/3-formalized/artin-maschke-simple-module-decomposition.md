# Finite-group Maschke simple-module decomposition for Artin representations

- **ID:** `artin-maschke-simple-module-decomposition`
- **Stage:** 3-formalized
- **Type:** THEOREM (classical representation-theory infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** every finite-dimensional complex representation of a finite group is a finite
  direct sum of actual simple group-algebra submodules.

## Exact formal result

`formal/GaloisForLFunctions/RHTower/Artin/ArtinMaschkeDecomposition.lean` proves

```text
finiteGroup_exists_simpleModule_decomposition:
  ∃ n (S : Fin n → Submodule ℂ[G] rho.asModule),
    rho.asModule ≃ₗ[ℂ[G]] Π₀ i, S i ∧ ∀ i, IsSimpleModule ℂ[G] (S i).
```

The theorem returns actual `Submodule ℂ[G] rho.asModule` summands and an actual
`ℂ[G]`-linear equivalence.  It has no proposition interface that assumes a decomposition.

The same module defines `groupAlgebraModuleRepresentation`, the explicit restricted-scalar
representation carried by any actual `ℂ[G]`-module, proves its exact simple/irreducible equivalence
(`groupAlgebraModuleRepresentation_isIrreducible_iff`), and upgrades the Maschke output to
`finiteGroup_exists_irreducibleModule_decomposition`.  The explicit scalar structure is real data,
not an assumed instance; this avoids Mathlib's intentional absence of a global restricted-scalar
instance.

## Paper proof

Maschke’s theorem makes the group algebra `ℂ[G]` semisimple for finite `G`.  A finite-dimensional
module over a semisimple ring is a finite direct sum of simple modules.  Restricting the scalar
finite-dimensionality of `rho` to `ℂ[G]` gives the needed module-finiteness hypothesis.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinMaschkeDecomposition.lean` passed.
- `lake build GaloisForLFunctions.RHTower.Artin.ArtinMaschkeDecomposition` passed; this is the targeted
  module build, not an umbrella or full build.
- `/tmp/ArtinMaschkeDecompositionAxioms.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for all three exported theorems.
- The leaf is imported by `formal/GaloisForLFunctions/RHTower.lean`; the umbrella was deliberately
  not built.

## Anti-theatre boundary

Semisimplicity alone does not prove the integral monomial lattice, rational Artin induction,
Brauer induction, Hecke continuation, or Heilbronn effectivity.  Do not rename it as an
irreducible-character decomposition until actual representation/character transport is formalized.

## Log

- 2026-08-15 — Mathlib API and a concrete proof route source-checked in
  `/tmp/BrauerMathlibAudit.lean`; opened as the first missing general non-abelian character carrier.
- 2026-08-15 — formalized, target-built, axiom-audited, and wired without an umbrella build.
