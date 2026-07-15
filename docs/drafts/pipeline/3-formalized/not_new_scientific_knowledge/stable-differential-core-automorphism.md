# Stable differential core automorphism

- **ID:** `stable-differential-core-automorphism`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** An injective field endomorphism restricts to an automorphism of the intersection
  of all its forward image fields; if it commutes with a derivation, that stable core is
  derivation-closed.

## Theorem

For a field extension `K -> F` and a `K`-algebra endomorphism `Phi : F -> F`, define

```text
Core(Phi) = intersection over n >= 0 of Phi^n(F).
```

Then:

1. `x in Core(Phi)` exactly when `x` has a preimage under every finite iterate;
2. `Phi(Core(Phi)) = Core(Phi)`;
3. the restricted map is a `K`-algebra automorphism;
4. if `Phi(x') = Phi(x)'`, every iterate commutes with the derivation and `Core(Phi)` is
   derivation-closed.

The inverse on the core is not an extra choice of dynamics.  A depth-one preimage of a core
element automatically has preimages at every depth by injectivity.

## Lean certificate

`formal/GaloisForLFunctions/HTGeometry/StableDifferentialCore.lean` proves:

```text
mem_stableRangeCore_iff
stableRangeCore_map_mem
stableRangeCore_exists_preimage
stableRangeCoreAlgHom_bijective
stableRangeCoreAlgEquiv
algHom_pow_deriv
derivationClosed_stableRangeCore
```

The targeted leaf build and formal lint pass.  The axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

## Scientific classification

The stable-image argument is elementary field theory and is recorded as infrastructure, not new
scientific knowledge.  Its role is to isolate the exact unconditional Lean core used by the
paper-level scalar projective-core theorem; the latter additionally needs differential Luroth and
differential-order rigidity.

## RH impact audit

None without a source-pure endomorphism of the completed zeta differential field.

## Gates

- [x] 0 -> 1 in-progress: exact stable-core statement isolated
- [x] 1 -> 2 fully-proven: complete algebraic proof
- [x] 2 -> 3 formalized: targeted Lean build, lint, and axiom audit pass
- [ ] 3 -> 4 publication-ready: not a standalone publication target
