# PBAP node criticality, unique repair and the archimedean unit-node energy

- **ID:** pbap-node-criticality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** producer loop rows 233–248 (`1-in-progress/producer-loop-opus-2026-10-12.md`); STATUS MUST-1437–1440,
  CANNOT-535–537
- **Statement:** prime-blind positivity on a node set S holds ⟺ RH ∧ S ⊇ prime powers; repairing deleted nodes keeps
  positivity ⟺ RH ∧ weights = Λ; under RH, Λ(m) is the least archimedean energy putting unit mass at the single node
  log m, and RH ⟺ that energy is bounded below.

## Goal
These results sharpen the HF producer core after the Weil cone was shown to contain at most one point
(`WeilConeUniquenessUnconditional`, via the twisted minimum principle). In the HF route RH is exactly PBAP. The
theorems below fix which constraints any PBAP proof must use, and identify the extremal problem it has to solve.

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized: standard axioms, `lake --old` clean, wired into `RHTower`.
  - `RHTower/PrimeBlindNodeCriticality`:
    - `primeBlindPositiveOn_iff`
    - `exists_negative_arch_of_primePower_node_deleted`
    - `riemannHypothesis_iff_primeBlindPositiveOn_primePowers`
    - `repairedBlindPositive_iff`
    - `riemannHypothesis_iff_repairedBlindPositive_vonMangoldt`
    - `riemannHypothesis_iff_singlePrimeWeilPositive`
  - `RHTower/ArchimedeanUnitNodeEnergy`:
    - `isGLB_unitNodeEnergies`
    - `not_bddBelow_unitNodeEnergies`
    - `riemannHypothesis_iff_bddBelow_unitNodeEnergies`
- [ ] 3 → 4 publication-ready

## Approach
- An S-restricted Hahn–Banach (`exists_weilPositiveFull_of_primeBlindPositiveOn`): the log vectors restricted to S
  and the pair tests reach every coordinate with both signs.
- Then the unconditional cone uniqueness `eq_vonMangoldt_of_weilPositiveFull`.
- The unit-node energy combines the W_Λ lower bound, sharpness from unique repair, and unboundedness from ¬PBAP plus
  a normalised pair test.

## No-go closure (barriers established for PBAP attacks)
- **Exact killing theorem:** deleting any single prime-power node makes archimedean positivity false, unconditionally.
- **Strongest positive survivor:** unique repair (`repairedBlindPositive_iff`), plus the variational formula
  inf E_m = Λ(m) under RH.
- **New insight:** the walls for PBAP attacks are:
  - (11) the proof must use blindness at every prime power and at nothing else (no density, sampling or uncertainty
    arguments);
  - (12) the dual positive measure is forced to be the critical-zero counting measure, so the producer is a spectral
    realisation;
  - (13) maximum-principle, transfer-operator and Hecke positivity preserve pointwise cones, while PBAP lives on the
    Bochner cone. The two meet only on nonnegative cores, which carry no RH content.
- **Mechanisms tried and killed** (rows 235–248): Farey–Möbius encoding, Schur products, Krein extension, modular
  transfer, infinite divisibility, tangent cone at the witness, Hecke variance of resonant states, Maass–Selberg,
  second s-derivative of E (Laguerre), Pontryagin index, Mayer/Perron–Frobenius, Selberg trace formula,
  pseudo-Laplacian/Lax–Phillips, local Euler factors, Schoenberg total positivity, tiling-preserving averaging,
  dyadic lattice decomposition, single-test Boas–Kac form; (rows 272–276) blind Riemann–Roch transfer (blind
  effectivity is window-confined), null-face plus window decomposition (interpolation density), doubly-positive cone
  (non-RH: far mass enters with the positive kernel 4cosh(x/2) − 2ω), blind moment calculus (first moments of every
  Dirichlet series are pole data; |ζ|² needs Fourier-side blindness), doubly-blind Jensen squeeze (falsifier only).
- **Status:** open core = inf E_2 > −∞ (equivalently PBAP, equivalently RH).
- **Non-RH side target recorded:** `WindowPositive` (nonnegative-core sector). The pointwise relaxation gives
  5.216 < |A(0)| = 5.3721, so about 3% must come from the Bochner structure.

## Log
- 2026-10-14 — created at stage 3 (Lean modules audited)
- 2026-10-14 — rows 272–276 added to the killed list; RH content is carried only by blind PD tests that change sign
  beyond log 2 (row 274)
