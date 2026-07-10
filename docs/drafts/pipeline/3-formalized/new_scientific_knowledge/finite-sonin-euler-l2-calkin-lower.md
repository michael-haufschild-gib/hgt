# Finite Sonin Euler families contain their coefficient l2 norm modulo compacts

- **ID:** finite-sonin-euler-l2-calkin-lower
- **Stage:** 3-formalized
- **Type:** THEOREM / OBSTRUCTION (Lean)
- **Date:** 2026-07-10
- **Status banner:** `[NOVELTY UNVERIFIED]` The quantitative finite-family theorem and its literal
  Hardy--Titchmarsh source transport are formalized. Scientific priority remains subject to an
  independent Wiener--Hopf, Toeplitz, crossed-product, and Sonin/prolate audit.
- **Paper source:**
  `../../2-fully-proven/new_scientific_knowledge/sonin-finite-calkin-l2-lower-bound.md`
- **Lean endpoint:**
  `formal/GaloisForLFunctions/RHTower/SoninEulerFiniteL2Lower.lean`

## Formalized theorem

Let `a>0`, let `r : Fin n -> R` be injective with `r_i>1`, and let

`L_i=(1-Q_a)(U_(r_i)+U_(r_i)^(-1))Q_a`

on the actual even Sonin carrier. For every coefficient family `c : Fin n -> C` and every compact
operator `K`, Lean proves

`sqrt(sum_i ||c_i||^2) <= ||sum_i c_i L_i-K||`.           (1)

The theorem includes the empty family and carries no shell, separation, convergence, or
orthogonality hypothesis.

For the positive Euler corners `C_i=-r_i^(-1/2)L_i`, Lean proves

`sqrt(sum_i ||c_i||^2/r_i) <= ||sum_i c_i C_i-K||`.      (2)

Both inequalities are transported through the concrete archimedean dual Hardy--Titchmarsh unitary.
For an injective finite prime family `p_i`, the literal source theorem is

`sqrt(sum_i 1/p_i) <= ||sum_i C_(p_i)-K||`.              (3)

If arbitrary prime coefficients `c_p` have all finite source sections uniformly bounded modulo
compacts by `B`, Lean further proves

`Summable (p |-> ||c_p||^2/p)`.                          (4)

## Constraint mechanism

Lean constructs a single common exterior shell `a<|x|<b` satisfying simultaneously

`b<r_i a`

and, whenever `r_i<r_j`,

`b r_i<a r_j`.

The corrected shell sequence

`f_m=Q_a v_m`

is contractive and weakly null. Each corner sends it asymptotically to the normalized inward shell

`U_(r_i)v_m`.

The finite selector makes these inward shells pairwise orthonormal. Therefore

`sum_i c_iL_if_m -> sum_i c_iU_(r_i)v_m`

and the target norm is exactly `sqrt(sum_i||c_i||^2)`. Every compact operator sends `f_m` to zero,
so the lower bound survives arbitrary compact perturbation.

This proof uses dilation only to expose what crosses the fixed constraint boundary. It does not
construct a carrier by propagating one.

## Lean surface

The module proves:

- `exists_finiteScale_separatingShellUpper`
- `inwardDilatedEvenShellEven_orthonormal_scales`
- `centralSoninDilationCorner_commonExteriorShell_tendsto`
- `finiteEvenDilationCorners_commonExteriorShell_tendsto`
- `finiteCoefficientL2Norm_le_norm_finiteEvenDilationCorners_sub_compact_all`
- `finiteEulerCoefficientL2Norm_le_norm_finiteEvenPositiveEulerCorners_sub_compact`
- `norm_unitaryPush`
- `finiteEulerCoefficientL2Norm_le_norm_finiteArchimedeanPrimeEulerCorners_sub_compact`
- `finitePrimeReciprocalL2Norm_le_norm_archimedeanEulerCorners_sub_compact`
- `summable_primeEulerCoefficientEnergy_of_uniform_sub_compact_bound`
- `exists_finitePrime_archimedeanEulerCorner_sub_compact_norm_gt`
- `exists_finitePrime_archimedeanEulerCorner_norm_gt`

The shell selector is constructed from the finite family itself. The proof does not expose a Prop
interface for the separation geometry or for the simultaneous Sonin limit.

## Consequence and formal boundary

The standard divergence of the reciprocal-prime sum combines with (3) to show that canonical
finite all-prime Euler sums are unbounded in the Calkin quotient, with a lower bound of order
`sqrt(log log X)` along primes `p<=X`.

Lean formalizes (3) for every injective finite prime family and combines it with
`Nat.Primes.not_summable_one_div`. The endpoint
`exists_finitePrime_archimedeanEulerCorner_sub_compact_norm_gt` proves that for every `M>=0` there
is a finite prime family whose canonical source corner sum remains at norm greater than `M` after
subtracting any compact operator. The ordinary operator-norm endpoint follows at `K=0`. A specific
ordered exhaustion by all primes and the sharper `sqrt(log log X)` rate remain paper-level.

For general coefficients, the endpoint
`summable_primeEulerCoefficientEnergy_of_uniform_sub_compact_bound` converts a uniform finite-section
bound modulo compact operators into the necessary weighted condition `sum_p ||c_p||^2/p<infinity`.
Thus phase cancellation alone cannot evade the obstruction: it must be accompanied by weighted
amplitude decay or by a construction not represented as uniformly bounded canonical finite
sections.

## Dual gate

- **NOVEL:** The earlier project theorem isolated one coefficient and proved only Calkin linear
  independence. This theorem recovers the entire Euclidean coefficient energy simultaneously and
  yields a prime-harmonic growth obstruction. Targeted searches found general Toeplitz essential-norm
  estimates and semigroup crossed-product regular representations, but no actual-Sonin statement or
  this Euler boundary consequence. Scientific novelty remains provisional.
- **SIGNIFICANT:** The canonical unsmoothed all-prime additive Euler seam cannot even remain bounded
  modulo compacts. A viable global construction must renormalize, smooth, or introduce a cancellation
  unavailable to every finite positive Euler section.

## Gates

- [x] 0 -> 1: quantitative finite-family statement and one-shell mechanism isolated
- [x] 1 -> 2: paper proof and all-prime consequence completed
- [x] 2 -> 3: hypothesis-free even, Euler, source, finite-prime, and weighted coefficient forms formalized
- [ ] 3 -> 4: complete the parent-theory audit and formalize a specific ordered prime exhaustion
