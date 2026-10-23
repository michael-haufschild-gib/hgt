# Arithmetic Orientation Theory (AOT): programme card

- **ID:** aot-2026-10-23
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** docs/reports/review-2310/fable.md §3–§4 (the walls as questions; the field)
- **Statement:** Develop the theory of orientation invariants of arithmetic sources that survive
  passage to unbounded aperture, horizon, damping and height: frustration and holonomy of signed
  incidence forms, the companion (parity) orientation of divisor rows and the readings faithful to
  it, section counts of node divisors (Nyquist–Riemann–Roch), the stability class of paid
  receivers, and the width dictionary as one theorem. Lean in
  `formal/GaloisForLFunctions/ArithmeticOrientationTheory/`, umbrella
  `GaloisForLFunctions.ArithmeticOrientationTheory` (registered in `MainTheorems.lean`).

## Goal
Give each face of the three walls (sign in estimates, parity class in transport, effectivity in
realization) an exact integer- or sign-valued invariant with a theorem, and decide each research
topic of the review by a theorem or by a recorded open problem with its sharp boundary.

## Gates
- [ ] 0 → 1 folder, umbrella, registration, first modules compiled with `lake --old env lean`
- [ ] README written (`formal/GaloisForLFunctions/ArithmeticOrientationTheory/README.md`)
- [ ] research topics T1–T10 of the review each addressed by a Lean theorem or an open problem

## Plan (modules)
1. `FrustrationIndexControlsTheGroundEnergy`: switching classes, frustration index, signed
   Dirichlet form; ground energy zero iff balanced; `λ_min ≤ 4ν/n`; switching covariance.
2. `TheSumDifferenceFormOfTheOddPrimeSide`: discrete multiplicative model; odd autocorrelation
   = 2·ratio − product; product correlation at a prime power is tower-local.
3. `TheNyquistRankBound`: rank of a Gram with unit diagonal and frame bound `K` is `≥ RN/K`;
   sections (Dirichlet polynomials vanishing at separated heights) have codimension `≥ RN/K`.
4. `TheEvenFlipIsReadByTheDyadicTower`: first pronic moment difference across the even flip
   equals `−2 log 2 · Σ_a W_c(2^a)`; squarefree rows read at the prime 2.
5. `TheCriticalWienerMonoid`: critical Wiener kernels form a convolution monoid with
   submultiplicative norm; paid receivers are unions of its orbits.
6. `OrientedReadings`: involutions, orientation-faithful readings, the parity collapse law.
7. `TheDampingChainTransportsOrientationExactly`: residue-mode combinations keep their sign
   pattern under the damping flow.
8. `TheWidthDictionary`: TFAE assembling the corpus equivalences (index, effectivity, damping,
   positivity) into one statement.
9. README.

## Outcomes
(filled as modules compile)

## Log
- 2026-10-23 — created in 1-in-progress from review-2310/fable.md
