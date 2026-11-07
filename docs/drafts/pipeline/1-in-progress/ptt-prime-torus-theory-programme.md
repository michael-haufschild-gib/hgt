# Prime torus theory

- **ID:** ptt
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0611/obstacles-summary.md §2.8b
- **Statement:** The pair `(t, ω_t)` at finite time: alignment, near-diagonal energy, Bohr sets as approximate groups, kernel-valued certificates, the hull.

## Goal
Answer the six questions of §2.8b and build its five tools, in `formal/GaloisForLFunctions/PrimeTorusTheory/`. A macroscopic non-alignment theorem on the critical line is quasi-RH strength, so the honest targets are sharp brackets, exact identities, no-gos with their positive survivors, and small unconditional savings.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: every statement below
- [x] 2 → 3  formalized: every statement below compiles
- The programme stays open for the topics of README §9.

## Status

| # | Statement | Lean |
|---|---|---|
| P1 | Group closure, transport, corners, Halász–Montgomery | `TheOrbitOfAPhaseSystem` |
| P2 | Bohr sets, clusters, large-value pairs, descent | `LargeValueHeightsFormAnApproximateGroup` |
| P3 | Finite-time Bohr isometry; Kronecker scale; boxes and the mixing bracket; boxes at Chernoff cost `exp(10 y √(log y log log y/δ))` | `TheFiniteTimeBohrIsometry`, `TheBoxesOfTheTorus`, `TheBoxesAtSquareRootCost` |
| P4 | Pigeonhole non-alignment; saving `T^{−2/(A−1)−δ}`; any set of primes; top of the column | `UniqueFactorizationPaysForNonAlignment`, `TheSavingAgainstSize`, `TheSavingOnAnySetOfPrimes` |
| P5 | Moment = energy; start of the orbit; diagonal range; energy at every order; oscillating energy | `TheEnergyOfTheOrbit`, `TheDiagonalRange`, `TheEnergyPastTheDiagonal` |
| P6 | Rounded orbit: diagonal data cannot exclude a return | `TheRoundedOrbit` |
| P7 | Agler wall, finite and all primes; first and second test; sharpness; coordinates that see the height | `PrimeByPrimePaymentCannotUseTheGammaFactor`, `TheWallForAllPrimes`, `CoordinatesThatSeeTheHeight` |
| P8 | Fejér sign at the start; twin; start is extremal | `TheCornersOfTheOrbit` |
| P9 | Hull: finite type, characters, Liouville ⇔ RH, typical zero-free, limits ⇔ RH; a zero forces an entry; prime characters lacunary (Zygmund); natural boundary of typical fibres; logarithm of a fibre; typical order-two points extend zero-free with the line as natural boundary; Zygmund for every lacunary family | `TheHullOverTheTorus`, `TheHullOverTorsionPoints`, `AnIsolatedZeroForcesAnEntry`, `PrimeCharactersAreLacunary`, `TheLogarithmOfAFibre`, `TheNaturalBoundaryOfTheHull`, `TheHullOverOrderTwoPoints`, `TheNaturalBoundaryOverOrderTwoPoints` |
| P10 | Pole price; large values counted through the pole | `TheReturnsThePoleMustPay` |
| P11 | Graph lift; frozen = size; outer factor; allocation; the lift of the Ξ-current, fibre minimum at the pole, torus positivity = size | `CertificatesOnTheOrbit`, `TheLiftOfTheXiCurrent` |
| P12 | Critical coupling: theta counts integers | `TheCriticalCouplingOfTheBase` |
| P13 | Rank law; continuous systems have no torus; Pick certificate at rank one | `TheRankLaw`, `TheCertificateAtRankOne` |
| P14 | Character discrepancy; box count | `TheDiscrepancyOfTheOrbit` |
| P15 | Tarry–Escott and squared words; saving at every length; polylogarithmic saving past the horizon; away from small primes; sup of integer powers; `ζ` below its supremum | `TarryEscottWords`, `TarryEscottWordsForbidAlignment`, `NonAlignmentAtEveryLargeHeight`, `TheOrbitAvoidsTorsionPoints`, `TheLogarithmicHankelForm`, `SquaredWordsForbidAlignment`, `TheMisalignmentBand`, `TheMassOfMisalignedPrimes`, `TheSavingAtEveryLength`, `TheSavingAwayFromSmallPrimes`, `TheSupBoundOfIntegerPowers`, `ZetaStaysBelowItsSupremum` |
| P17 | Escape from low-rank progressions; every rotation; many misaligned primes; modulus below size | `TheOrbitEscapesProgressions` |
| P18 | Where the words stop: full progressions need the primorial in the step; squared-word patterns | `WhereTheWordsStop` |
| P19 | Transfer by translation: one large value generates `m` in a window of the Kronecker scale | `TheTransferToRareHeights` |
| P16 | The six questions, one statement each | `TheQuestionsOfTheField` |

## Open
Required saving `≍ εL/ℓ` at `y = (1+ε)L²/16` on the top of the column, against the proved `L⁻⁸ℓ⁻⁴` on all primes and a power of `T` at the top. Polylogarithmic precision above the primes up to `log y`; smooth numbers in short intervals; exact mixing exponent (gap `(log y)^{3/2}√(log log y)`, from the union bound); certificate coordinates tied to `p^{−s}`; zero-carrying set of the hull. README §9.

## No-go closure
- **Exact killing theorem/mechanism:** the kernel-valued Agler form of §2.8b dies on two points: `agler_wall`, `agler_wall_all_primes`, `no_decomposition_euler`, `euler_test`.
- **Strongest positive survivor:** `two_point_inequality` for arbitrary coordinates, and `norm_sub_sq_le_of_general` for a general archimedean term; the positive side `aglerDecompositionMulTwo`, `selfDecomposition`, at rank one `exists_certificate_iff`, and with coordinates that see the height `euler_test_has_height_certificate`.
- **New insight:** a passing certificate must use coordinates that see absolute height.
- **Status:** Lean, as named.

## Log
- 2026-11-07 — created
