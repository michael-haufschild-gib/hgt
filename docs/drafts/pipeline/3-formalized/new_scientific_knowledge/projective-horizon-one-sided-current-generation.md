# One-sided projective-horizon current generation

- **ID:** `projective-horizon-one-sided-current-generation`
- **Stage:** 3-formalized
- **Type:** MINIMAL CURRENT GENERATORS / ASYMMETRIC HORIZON CORE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [STRENGTHENED CORE]`
- **Parent:** `projective-horizon-one-sided-depth-transition`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonOneSidedCurrentAlgebra.lean`

## Theorems

### Scalar

In `sl_2(K[t])`, the three modes

```text
E_0,F_0,F_1
```

generate every `E_k,F_k,H_k`. In any Lie-module representation, a vector annihilated by those
three modes is annihilated by every polynomial current mode.

### Projective plane

In the current algebra of `sl_2 semidirect (K^2)^*`, the four constant root/shear modes

```text
E_0,F_0,U_0,V_0
```

together with the single linear root `F_1` generate every `E_k,F_k,U_k,V_k,H_k`. Annihilation by
those five modes likewise propagates to every mode in every representation.

## Mechanism

In both cases `H_1=[E_0,F_1]`. Its adjoint action creates the missing linear root and, in the plane
case, both missing linear shears. The previously formalized symmetric depth-two generator set is
therefore contained in the one-sided Lie span, so all-mode generation follows. Point stabilizers in
arbitrary representations are Lie subalgebras, giving annihilation propagation.

## Lean declarations

```text
oneSidedCurrentGenerators
oneSidedCurrentLie
depthTwoCurrentLie_le_oneSidedCurrentLie
oneSidedCurrentLie_contains_all_modes
oneSidedCurrent_annihilation_propagates
p2OneSidedCurrentGenerators
p2OneSidedCurrentLie
p2DepthTwoCurrentLie_le_p2OneSidedCurrentLie
p2OneSidedCurrentLie_contains_all_modes
p2OneSidedCurrent_annihilation_propagates
```

## Verification

- scratch elaboration against the pinned toolchain: passed
- isolated leaf elaboration: passed
- targeted module build: passed
- axiom audit of both containment, all-mode, and annihilation theorems: only `propext`,
  `Classical.choice`, and `Quot.sound`
- no full build was run

## Scientific role

The parent unequal-depth field theorem needs only one horizon to supply a degree-one gauge mode.
This file certifies that minimal trigger in both the scalar and first higher-rank cases. The
infinite free-jet rational fixed-field conclusion remains paper-level, with no Lean assumption
added.

## RH impact audit

`[NO DIRECT RH IMPACT]` The formal result validates the asymmetric symmetry mechanism. Its zeta
specialization is a field-theoretic no-go for common direct/reciprocal tail observables, not a
statement about the zero divisor.
