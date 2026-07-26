# Sonin projection-walk prolate phase-energy universality law

- **ID:** `sonin-projection-walk-prolate-phase-energy-universality-law`
- **Law:** LAW513
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/SoninProjectionWalkProlatePhaseEnergyUniversalityLaw.lean`

## Theorem

For every positive central Sonin aperture `a`, let `W_a` be the product-of-reflections quantum
walk and let `T_a` be the central prolate compression.  Then

```text
||W_a - W_a†||²_HS = 32 Re tr(T_a - T_a²).
```

Consequently its complete finite-aperture phase/occupation budget is

```text
||W_a - W_a†||²_HS + 32 ||T_a||²_HS = 128 a².
```

Thus anti-Hermitian unitary-walk phase energy is exactly thirty-two times free-fermion
number variance, and its complement is exactly retained prolate occupation.

## Theorem-generated derivation

Whole-corpus leaf comparison exposed:

- `centralSoninProjectionQuantumWalk_sub_adjoint_eq_four_mul_cutoffCommutator`;
- `hsNormSq_centralCutoffCommutator_eq_two_mul_re_opTrace_prolateImpurity`;
- `hsNormSq_centralProlateBlock_add_re_opTrace_impurity_eq_four_mul_sq`.

The first is operator-valued but corpus never takes its Hilbert--Schmidt energy and eliminates the
cutoff commutator.  Scalar homogeneity contributes `4² = 16`; the number-variance identity
contributes the remaining factor `2`, yielding `32`.  Substitution into the occupation budget
yields the phase/occupation conservation law.

## Dependency-closed paper proof

Write `C_a` for the physical/Fourier projection commutator.  The walk polarization theorem gives
`W_a - W_a† = 4 C_a`, so Hilbert--Schmidt homogeneity gives
`||W_a - W_a†||²_HS = 16 ||C_a||²_HS`.  Existing Sonin number variance gives
`||C_a||²_HS = 2 Re tr(T_a - T_a²)`.  Transitivity proves the first identity.

Existing finite-aperture occupation conservation is

```text
||T_a||²_HS + Re tr(T_a - T_a²) = 4a².
```

Multiplying by `32` and replacing the variance term by the walk phase energy proves the second
identity.  No numerical computation is used.

## Strict corpus delta

Corpus states the operator walk/commutator relation and the commutator/number-variance relation
separately.  It does not state either the exact walk-phase/free-fermion scalar identity or the
resulting aperture phase/occupation conservation law.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [ ] Lean formalization; direct `lake env lean`
- [ ] Post-proof literature audit
- [ ] Axiom and umbrella audit
