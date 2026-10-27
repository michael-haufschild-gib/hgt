# Arithmetic Intersection Theory programme

- **ID:** ait
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/fable.md §4 ("the field the walls ask for")
- **Statement:** Intersection theory of the characteristic circle (torsion of 𝔾_m over ℤ: power maps,
  rotations, Galois) and its transfer to Weil's pairing: projection formula, regulator anomaly,
  adjunction (different), Hecke cocycle, prime towers and local Hodge index, Fourier duality with the
  archimedean digamma, Weil's prime form in tower form.

## Goal
Lean folder `formal/GaloisForLFunctions/ArithmeticIntersectionTheory/`, umbrella
`ArithmeticIntersectionTheory.lean` (to wire into `MainTheorems.lean`), foundational README.
Answer the six questions of README §6 by theorems or sharp no-gos with survivors.

Territory: AET owns `orbitIntersection`, `torsionEnergy`, `weilPrimeKernel`, the renormalized limit;
AES owns electrostatics, the static self-intersection formula (ES5, planned there), counterterm rate
(ES6), arithmetic point (ES7); RBG owns survival law, rank dichotomy, `latticeGerm`. AIT adds
correspondences, anomaly, cocycle, towers, Fourier duality, transfer.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proofs per pillar
- [x] 2 → 3  each pillar in Lean, audited with `lake --old env lean`

## Pillars and modules

| Pillar | Module | Status |
|---|---|---|
| I–II projection formula, regulator anomaly | `TheProjectionFormulaAndTheRegulatorAnomaly` | Lean |
| III log-orders; IV' discriminant = self-intersection (prime powers) | `TheArchimedeanIntersectionIsALogOrder` | Lean |
| IV different c(n) | `TheDifferentOfATorsionOrbit` | Lean |
| V Hecke cocycle | `TheHeckeCocycleOfRenormalization` | Lean |
| VI tower form, KMS, ladder bounds | `TheTowerFormOfAPrime` | Lean |
| VII transverse decomposition, tensor form, local bounds | `ThePrimeKernelIsASumOfTransverseTowers` | Lean |
| VIII local forms do not sum | `TheLocalFormsDoNotSum` | Lean |
| IX gauge blindness (sign twins, Liouville) | `TheFiniteIntersectionIsGaugeBlind` | Lean |
| X Gauss digamma = Fourier of torsion energy | `GaussDigammaIsTheFourierTransformOfTheTorsionEnergy` | Lean |
| X' rotation spectrum on μ_N | `TheEllipticCorrespondencesOfTheCircle` | Lean |
| XI transfer to log-atom tests; RH ⇒ arch+polar ≥ towers | `WeilsPrimeFunctionalIsTheFiniteIntersection` | Lean |
| XII spacing regulator | `TheSpacingRegulatorRemovesTheAnomaly` | Lean |
| XIII Rosati moments | `ZeroMomentsAreRosatiPairings` | Lean |
| XIV adjunction beats the tower (index ≤ 2 per ladder) | `TheSelfIntersectionDominatesTheTower` | Lean |
| XV polar part on log-atom tests | `ThePolarPartPairsThePoleDirection` | Lean |
| XVI square-root price of separate towers | `TheSquareRootPriceOfSeparateTowers` | Lean |
| XVII RH in tower coordinates; E_φ ≥ log(1/δ) bound | `TheHodgeIndexInTowerCoordinates` | Lean |
| XVIII base (disjoint ladder supports vs 𝔽_q overlap), successor transversality | `TheBaseAndTheSuccessor` | Lean |

Open (README §9): covariant regulator with nontrivial null cone; asymptotics of E_φ, K_φ;
arithmetic RR on torsion orbits; discriminant for all n; indices on boxes; weight filtration.

## Paper proofs (key facts)
- Projection: z^t − u = ∏_{w^t=u}(z − w); 1 − r^t z^t = ∏_{ω∈μ_t}(1 − rωz).
- Anomaly: (1 − r^t)/(1 − r) = 1 + r + … + r^{t−1} → t.
- kLogKernel = μ ⋆ (id·log) = φ·log + φ ⋆ Λ (log is a derivation); (φ⋆Λ)(n) = φ(n) Σ_{p∣n} log p/(p−1).
  Hence c(n) = I(n,n)/φ(n) = log n − Σ_{p∣n} log p/(p−1).
- β(n,t) = c(tn) − c(n) = log t − Σ_{p∣t,p∤n} log p/(p−1); cocycle; 0 ≤ c(t) ≤ β ≤ log t.
- Hecke variation: P(tm,tn) = P(m,n), |T_t x| = |x| ⇒ lim[Q_r(T_t x) − Q_r(x)] = −Σ x_n² β(n,t).
- Tower: p^{−|i−j|/2} = Σ_{k ≤ min(i,j)} φ(p^k) p^{−i/2} p^{−j/2} (φ(1) = 1, Σ_{k≤m} φ(p^k) = p^m).
- KMS: K = (1−q²)⁻¹ LᵀL-type; x = (I − qS)u ⇒ (1−q)/(1+q)|x|² ≤ xᵀKx ≤ (1+q)/(1−q)|x|².
- Fourier: Σ_{a mod N} −log|1 − rζ^a| cos(2πak/N) = (N/2) Σ_j (r^j/j)([j≡k] + [j≡−k]) = ½[r^k G_{r^N}(k/N) + r^{N−k} G_{r^N}(1−k/N)].

## Log
- 2026-10-27 — created; README first draft.
