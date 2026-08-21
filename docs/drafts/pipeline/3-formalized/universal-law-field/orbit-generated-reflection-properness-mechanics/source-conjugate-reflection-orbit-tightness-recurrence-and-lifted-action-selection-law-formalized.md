# ULF-OGRPM-1 — Lean formalization record

**Card:** `source-conjugate-reflection-orbit-tightness-recurrence-and-lifted-action-selection-law.md`
**Module:** `formal/GaloisForLFunctions/HTGeometry/OrbitGeneratedReflectionProperness.lean`
**Namespace:** `GaloisForLFunctions.HTGeometry`
**Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Card result → Lean declaration

| Card | Lean |
|---|---|
| `P_k`, `J_k`, `D_k`, (ORT.1) | `orbitProjection`, `orbitReversal`, `orbitDefect` |
| **Theorem 2.1(1)** | `orbitProjection_idem`, `orbitProjection_selfAdjoint` |
| **Theorem 2.1(2)** | `orbitReversal_involutive` (self-adjointness of `J_k` is `orbitProjection_selfAdjoint`) |
| **Theorem 2.1(3)** | `orbitReversal_succ` |
| **Theorem 2.1(4)** | `orbitDefect_eq` |
| **Theorem 2.1(5)**, (ORT.3) | `norm_orbitDefect_sq`, `norm_orbitDefect_sq_eq_four_mul`, `sum_norm_orbitDefect_sq` |
| **Theorem 2.1(6)**, (ORT.4) | `forall_orbitDefect_eq_zero_iff` |
| **Theorem 3.1**, (ORT.7) | `hasSum_orbitDefect_of_parseval` |
| (ORT.9) | `cyclicReversal`, `cyclicDefect_apply` |
| **(ORT.10)** | `sum_sum_norm_cyclicDefect` (via `sum_norm_cyclicDefect`) |
| **Corollary 4.1** | `eq_zero_of_forall_cyclicReversal_eq_neg` |
| (ORT.11) periodicity | `cyclicReversal_periodic` |
| `𝒜_q`, (ORT.12) | `cyclicAction` |
| **Theorem 5.1**, (ORT.13) | `cyclicAction_eq` (via `sum_range_mul_ofNat`) |
| **(ORT.14)** | `bddAbove_cyclicAction_iff` |
| **§6**, (ORT.16) | `orbitDefect_intertwine`, `norm_orbitDefect_intertwine` (via `map_zpow_of_intertwine`) |
| **§7** completeness | `eq_zero_of_summable_of_forall_sub_succ` |
| **§7** no lower frame bound | `exists_unit_small_difference_energy` |

## Method notes

* The reversal atlas is carried by plain `𝕜`-linear maps with the projection hypotheses stated as
  `P ∘ P = P` and `⟪P y, z⟫ = ⟪y, P z⟫`; no operator-algebra machinery is needed.
* `(ORT.4)` is proved through the elementary equivalence `P z = 0 ↔ ∀ y, ⟪P y, z⟫ = 0` for a
  self-adjoint idempotent, transported along `U^k`.
* `(ORT.7)` is stated as the exact `HasSum` transfer: a Parseval orbit gives joint defect energy
  `4‖x‖²` over an arbitrary index type.
* `(ORT.13)` uses the block identity `∑_{m < qN} f(m mod N) = q ∑_{k} f k`.
* **§7 needs no Fourier analysis.**  Taking the normalized indicator of a window of length `n`
  gives a unit family whose successive-difference energy is exactly `2/n`, and a square-summable
  family with vanishing differences is constant, hence zero.  Completeness and properness are thus
  separated by an explicit elementary family.

## Verification

* `lake env lean` on the module: 0 errors, 0 warnings.
* Axiom audit: 31 public declarations, only `propext`, `Classical.choice`, `Quot.sound`.
