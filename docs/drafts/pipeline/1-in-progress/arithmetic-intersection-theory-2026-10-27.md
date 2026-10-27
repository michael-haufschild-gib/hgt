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
- [ ] 1 → 2  paper proofs per pillar
- [ ] 2 → 3  each pillar in Lean, audited with `lake --old env lean`

## Pillars and modules

| Pillar | Module | Status |
|---|---|---|
| I correspondences, projection formula | `TheCorrespondencesOfTheCharacteristicCircle` | planned |
| II regulator anomaly | `TheRegulatorAnomaly` | planned |
| III Λ(n) = log #(𝓞/(ζ_n − 1)) | `IntersectionNumbersAreLogOrders` | planned |
| IV different c(n) | `TheDifferentOfATorsionOrbit` | planned |
| V Hecke cocycle | `TheHeckeCocycleOfRenormalization` | planned |
| VI towers, KMS, P = Σ log p (K_p − 1) | `TheTowerDecompositionOfThePrimeKernel` | planned |
| VII Fourier duality, Gauss digamma | `GaussDigammaIsTheFourierTransformOfTheTorsionEnergy` | planned |
| VIII transfer, RH in tower form | `TheHodgeIndexInTowerForm` | planned |

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
