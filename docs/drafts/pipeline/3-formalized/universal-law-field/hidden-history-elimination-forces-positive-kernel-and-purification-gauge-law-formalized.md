# Hidden-history elimination, positive kernel, purification gauge — Lean certification

- **ID:** ULF-HKPG-1
- **Paper card:**
  `hidden-history-elimination-forces-positive-kernel-and-purification-gauge-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveVisibleKernelPurificationGauge`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## New infrastructure

`rank_le_one_iff_vecMulVec` — **a matrix has rank at most one exactly when it is an outer
product.**  Mathlib has no rank-one characterization; this is proved by identifying the range of
`mulVecLin` as a principal submodule and reading off the columns.

`ker_eq_of_norm_eq` and `gaugeEquiv` — **two surjective linear maps of equal length differ by a
length-preserving linear equivalence**, built from the two first-isomorphism equivalences composed
across the identification of kernels.  This is the abstract content of the purification gauge.

## Certified declarations, by clause

| Clause | Lean |
|---|---|
| (1) the visible kernel | `visibleKernel`, `visibleKernel_apply`, `visibleKernel_eq_transpose` |
| 1: positive semidefinite | `visibleKernel_posSemidef` |
| 1: unit trace | `trace_visibleKernel` |
| 2: `rank K = rank Ψ` | `rank_visibleKernel` |
| 4: expectations | `trace_visibleKernel_mul` |
| 3: rank one ⟺ separable | `rank_le_one_iff_vecMulVec`, `rank_visibleKernel_le_one_iff_separable` |
| (5) the Bell kernel | `bellAmp`, `visibleKernel_bellAmp` |
| the closure obstruction | `rank_visibleKernel_bellAmp`, `bellAmp_not_separable` |
| §3 diagonal ≠ kernel | `rankOneKernel`, `coherentBeta`, `diag_coherentBeta`, `coherentBeta_kernel_ne` |
| (7) Gram factorization | `exists_gram_factorization` |
| (8) the gauge | `gram_dotProduct_eq`, `ker_eq_of_norm_eq`, `gaugeEquiv`, `gaugeEquiv_apply`, `gaugeEquiv_norm` |

The kernel is defined by the card's formula (1) exactly; `visibleKernel_eq_transpose` records that
it is the transpose of the column Gram matrix, which is the "harmless transpose convention" the card
itself flags, and every structural result (positivity, rank, trace) is transported through that
identity rather than assumed.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveVisibleKernelPurificationGauge.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both pass with no warnings; the umbrella build completed 11,437 jobs.  `#print axioms` on the
fifteen declarations audited reports only `propext`, `Classical.choice`, and `Quot.sound`.  No
project axiom, placeholder, hypothesis interface, or computation proof is used.

## Exact field consequence

The rank-one amplitude ontology is forced open.  Discarding a hidden factor from a maximally
entangled amplitude leaves `(1/d)·I`, of rank `d`, which is not `|β⟩⟨β|` for any visible amplitude —
so any history theory closed under elimination must enlarge amplitudes to positive kernels.  The
kernel then carries strictly more than the probability law it induces (`diag_coherentBeta` versus
`coherentBeta_kernel_ne`), and strictly less than a marked hidden history: minimal realizations form
one gauge orbit (`gaugeEquiv`).  Positivity plus all visible expectations therefore fixes the
smallest hidden dimension and nothing beyond it.
