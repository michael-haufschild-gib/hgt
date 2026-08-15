# Formalization certificate — `ccm-characteristic-evans-boundary-infinite-rank-law`

- **Card:** `ccm-characteristic-evans-boundary-infinite-rank-law.md`
- **Stage:** 3-formalized / not-new
- **Lean module:** `formal/GaloisForLFunctions/RHTower/CCMEvansBoundaryInfiniteRank.lean`
- **Umbrella:** `formal/GaloisForLFunctions/RHTower.lean`
- **Axioms:** `[propext, Classical.choice, Quot.sound]` on all 10 declarations
- **Hypotheses:** none beyond the quantified data of each statement; no `sorry`, `axiom`, `opaque`

## Declarations

- `GaloisForLFunctions.RHTower.exterior_displacement_split`
- `GaloisForLFunctions.RHTower.hankelColumn`
- `GaloisForLFunctions.RHTower.hankelColumn_eq_realTranslate`
- `GaloisForLFunctions.RHTower.mem_expPolySpace_of_hankelColumns`
- `GaloisForLFunctions.RHTower.exists_finite_frequencies`
- `GaloisForLFunctions.RHTower.exists_entire_extension_of_hankelColumns`
- `GaloisForLFunctions.RHTower.not_hankelColumns_finiteDimensional`
- `GaloisForLFunctions.RHTower.digammaArgument_eq_neg_natCast_iff`
- `GaloisForLFunctions.RHTower.digammaArgumentNeg_eq_neg_natCast_iff`
- `GaloisForLFunctions.RHTower.gammaPoleLattice`
- `GaloisForLFunctions.RHTower.gammaPoleLattice_infinite`
- `GaloisForLFunctions.RHTower.not_subset_rootSet_of_gammaPoleLattice`

## Coverage

| Card item | Lean |
|-|-|
| `(4)` pole lattice `± i(2n+1/2)` | `digammaArgument_eq_neg_natCast_iff`, `digammaArgumentNeg_eq_neg_natCast_iff` |
| lattice infinite, symbol not rational | `gammaPoleLattice_infinite`, `not_subset_rootSet_of_gammaPoleLattice` |
| `(5)` → `(6)` Hankel change of variables | `exterior_displacement_split`, `hankelColumn_eq_realTranslate` |
| `(7)` finite rank ⟹ exponential polynomial | `mem_expPolySpace_of_hankelColumns`, `exists_finite_frequencies` |
| finite rank ⟹ no singularity | `exists_entire_extension_of_hankelColumns` |
| **infinite rank of the exterior trace** | `not_hankelColumns_finiteDimensional` |

## Deliberately outside the Lean statement

- the distribution kernel `k_a` of `c_a(D)` and the integral form `(5)`;
- the meromorphic continuation `(3)` of the Gamma symbol (only the lattice `(4)` is formalized);
- the identification of the kernel's Laplace transform with a half-plane branch of `c_a`.

The card's remaining open gates (construct the infinite-dimensional Fredholm Evans operator, prove
its kernel vanishes at every aperture, RH) are route gates, not statements of this card.
