# Commuting core symmetries produce exact fixed currents

- **ID:** `persistent-core-symmetry-fixed-current-kernels`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), SUPPORT
- **Statement:** Every algebraic symmetry commuting with a constraint restricts to an algebraic
  symmetry of its stable core, and multiplicative, additive, and finite cyclic eigenmotions yield
  explicit fixed differential observables.

## Formal theorem

Let `phi:F->F` be an algebra endomorphism and `rho:F~=F` an algebra equivalence satisfying

```text
phi(rho(x))=rho(phi(x)).
```

Then `rho` maps `stableRangeCore(phi)` exactly to itself and restricts to an algebra equivalence of
that core.  Moreover:

- a clock character of `q` is preserved by `phi`;
- if `phi(q)=a q` for a nonzero differential constant `a`, then `Dq/q` is fixed;
- under a semilinear clock symmetry, `Dq/q` has unit clock character;
- if `phi(q)=q+b` for a differential constant `b`, then `Dq` is fixed;
- if `phi(q)=a q` and `a^N=1`, then `q^N` is fixed.

These are the exact formal kernels of the complete scalar persistent gauge-reduction theorem.
The identities themselves are classical; the candidate-new scientific claim is the paper-level
classification that forces every nonconstant scalar stable core into one of these branches.

## Lean certificate

File: `formal/GaloisForLFunctions/HTGeometry/StableCoreFunctoriality.lean`

Declarations:

- `map_stableRangeCore_eq_of_commuting_algEquiv`
- `stableRangeCore_symmetry_mem_iff`
- `stableRangeCoreSymmetryAlgHom`
- `stableRangeCoreSymmetryAlgHom_bijective`
- `stableRangeCoreSymmetryAlgEquiv`
- `algHom_preserves_character_of_commuting`
- `logDeriv_fixed_of_eigenvector`
- `logDeriv_unit_character_of_semilinear`
- `deriv_fixed_of_translation`
- `pow_fixed_of_eigenvector`

The existing module cache was present.  The touched file passed the required direct check:

```text
lake env lean GaloisForLFunctions/HTGeometry/StableCoreFunctoriality.lean
```

No full build or concurrent local Lean invocation was run.

## Gates

- [x] 0 -> 1 in-progress: exact commuting-square and eigenmotion statements isolated
- [x] 1 -> 2 fully-proven: algebraic proofs complete
- [x] 2 -> 3 formalized: direct touched-file check passes without placeholders
- [ ] 3 -> 4 publication-ready: support surface only; publish with the scalar classification

## Log

- 2026-07-15 -- commuting symmetry restriction and all scalar fixed-current branch kernels
  formalized and directly verified from cache.
