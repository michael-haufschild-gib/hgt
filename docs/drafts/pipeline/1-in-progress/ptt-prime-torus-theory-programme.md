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
| P3 | Finite-time Bohr isometry; Kronecker scale | `TheFiniteTimeBohrIsometry` |
| P4 | Pigeonhole non-alignment; saving `T^{−2/(A−1)−δ}`; any set of primes; top of the column | `UniqueFactorizationPaysForNonAlignment`, `TheSavingAgainstSize`, `TheSavingOnAnySetOfPrimes` |
| P5 | Moment = energy; start of the orbit; diagonal range; last-moment bound | `TheEnergyOfTheOrbit`, `TheDiagonalRange` |
| P6 | Rounded orbit: diagonal data cannot exclude a return | `TheRoundedOrbit` |
| P7 | Agler wall, finite and all primes; first and second test; sharpness | `PrimeByPrimePaymentCannotUseTheGammaFactor`, `TheWallForAllPrimes` |
| P8 | Fejér sign at the start; twin; start is extremal | `TheCornersOfTheOrbit` |
| P9 | Hull: finite type, Liouville ⇔ RH, typical zero-free, limits ⇔ RH | `TheHullOverTheTorus` |
| P10 | Pole price; large values counted through the pole | `TheReturnsThePoleMustPay` |
| P11 | Graph lift; frozen = size; outer factor; allocation | `CertificatesOnTheOrbit` |
| P12 | Critical coupling: theta counts integers | `TheCriticalCouplingOfTheBase` |
| P13 | Rank law; continuous systems have no torus; Pick certificate at rank one | `TheRankLaw`, `TheCertificateAtRankOne` |
| P14 | Character discrepancy; box count | `TheDiscrepancyOfTheOrbit` |
| P15 | Tarry–Escott and squared words; saving at every length; polylogarithmic saving past the horizon; sup of integer powers | `TarryEscottWords`, `TarryEscottWordsForbidAlignment`, `NonAlignmentAtEveryLargeHeight`, `TheOrbitAvoidsTorsionPoints`, `TheLogarithmicHankelForm`, `SquaredWordsForbidAlignment`, `TheMisalignmentBand`, `TheMassOfMisalignedPrimes`, `TheSavingAtEveryLength`, `TheSupBoundOfIntegerPowers` |
| P16 | The six questions, one statement each | `TheQuestionsOfTheField` |

## Open
Required saving `≍ εL/ℓ` at `y = (1+ε)L²/16` on the top of the column, against the proved `L⁻⁸ℓ⁻⁴` on all primes and a power of `T` at the top. Transfer of the polylogarithmic saving to the top; oscillating energy past the diagonal; boxes at the mixing time; non-returning coordinates; hull beyond finite type.

## No-go closure
- **Exact killing theorem/mechanism:** the kernel-valued Agler form of §2.8b dies on two points: `agler_wall`, `agler_wall_all_primes`, `no_decomposition_euler`, `euler_test`.
- **Strongest positive survivor:** `two_point_inequality` for arbitrary coordinates, and `norm_sub_sq_le_of_general` for a general archimedean term; the positive side `aglerDecompositionMulTwo`, `selfDecomposition`, and at rank one `exists_certificate_iff`.
- **New insight:** a passing certificate must use coordinates that see absolute height.
- **Status:** Lean, as named.

## Log
- 2026-11-07 — created
