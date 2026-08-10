# ULF-GAS-1 — Lean certification companion

- **Card:** `abelian-zeta-gas-two-observable-divisor-dictionary-and-condensation-wall-law.md`
- **Stage:** 3-formalized
- **Area:** `GaloisForLFunctions.HTGeometry` (umbrella `HTGeometry.UniversalLawField`)

## What is certified

All eight theorems of the card, unconditionally: no premises, no added axioms, no `sorry`.
`#print axioms` on every capstone reports only `propext`, `Classical.choice`, `Quot.sound`.

| Theorem | Capstone(s) |
|---|---|
| 2.1 | `tsum_classMass_eq_one`, `classMass_eq_ennNormalizer_mul_twoObservableWeight` |
| 3.1 (GAS.5) | `gas_socle_law`, `measure_exactPartsEvent_eq_localSocleMass` |
| Cor. 3.2 (GAS.6)(GAS.7) | `gasResponse_toReal_mul_zetaPartition`, `zetaPartition_depthShift` |
| 4.1 | `gas_kms_existsUnique`, `gasGibbs_adjoint_mul_self_nonneg`, `vectorState_unique` |
| 5.1 | `temperature_finite_depthTail_eq_one`, `temperature_infinite_exactDepth_eq_one`, `gasMeasure_map_depthTail` |
| 6.1 (GAS.9)(GAS.10) | `meromorphicOrderAt_grandResponse`, `no_analytic_extension` |
| 7.1 (GAS.11) | `gasDilate_comp`, `gasDilate_twist`, `gasGibbs_comp_gasDilate` |
| 8.1 (GAS.12)–(GAS.14) | `klDiv_symmetrised_eq_zeta`, `orderExpectation_temperature_depthLadder`, `klDiv_symmetrised_temperature_shift` |

## Reusable infrastructure built here

- **Partition generating functions** (`PartitionGeneratingFunction`): occupation-number model,
  Euler's shift bijection, and the recursion `T_{n+1} = T_n + q^{n+1}T_{n+1}`, all as `ℝ≥0∞` sums,
  so no summability side condition appears.  Mathlib's Euler proof lives in `Archive`, which is not
  importable.
- **`tprod_split_nat`**: splitting a multipliable family at a finite index in a commutative
  *monoid*.  Mathlib's `Multipliable.prod_mul_tprod_nat_add` needs a group, and `ℂ` is not one
  under multiplication.
- **The monomial monoid of a Toeplitz gas** (`GasWord`): the restricted direct sum of bicyclic
  monoids, with contraction, charge, disjoint-mode commutation and one-mode peeling — the exact
  algebraic model of the dense `*`-subalgebra of an infinite tensor product of Toeplitz algebras.
- **A GNS construction for a `*`-algebra that is not yet a C\*-algebra** (`GasGNS`).  Mathlib's
  `GelfandNaimarkSegal` assumes a C\*-algebra; here `PreInnerProductSpace.Core` plus
  `UniformSpace.Completion` do the work, with the null space quotiented out automatically.
- **An elementary positivity certificate** (`GasPositivity`): the Gram kernel
  `φ(x^*y) = [charge x = charge y]∏_i q_i^{max}` is a Hadamard product of a charge kernel with
  per-mode kernels, and `q^{max(b,d)} = q^b q^d q^{-min(b,d)}` telescopes with nonnegative
  increments — so mathlib's Schur product theorem finishes it with no operator theory.
- **Zeta zeros of unbounded ordinate from the corpus's own `xiDivisorSupport_infinite`**
  (`NaturalBoundary`), and the observation that the *depths* — not a Riemann–von Mangoldt count —
  supply the density needed for the natural boundary.

## Verification

Targeted foreground `lake env lean` green on every module; final foreground
`lake build GaloisForLFunctions.HTGeometry.UniversalLawField` green at 11,590 jobs.

## Scope note

Theorem 4.1 is certified in C\*-form on the concrete C\*-algebra `gasCStar θ`: the closed
`*`-subalgebra of the bounded operators on the GNS Hilbert space of the Gibbs state, in which the
monomials are dense (`gasCStar_carrier`).  The KMS exchange identity is imposed on that dense
image, because the modular flow at imaginary time scales monomials by `q^{charge}` and is unbounded,
so it does not act on the completion.  No C\*-tensor product and no inductive limit of C\*-algebras
was needed.
