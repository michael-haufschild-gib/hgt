import GaloisForLFunctions.HTGeometry.CompactGroupMetricReturnLaw

/-!
# The covering-volume sandwich on a compact metric group

For a compact group with a left-invariant extended metric and Haar probability measure the
covering number at radius `eps` is squeezed between the reciprocal volumes of two balls:

```text
1 <= N_eps * mu(closedBall 1 eps),      N_eps * mu(ball 1 (eps/2)) <= 1.
```

The left bound is subadditivity over a minimal cover; the right bound is disjointness of the
half-radius balls around a maximal separated set, together with the mathlib inequality between
covering and packing numbers.  Both use only that left translation is an isometry preserving the
measure, so every ball has the volume of the ball at the identity.
-/

open Metric MeasureTheory Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

variable {G : Type*} [PseudoEMetricSpace G] [CommGroup G] [IsIsometricSMul G G]

theorem closedEBall_eq_image (c : G) (r : ℝ≥0∞) :
    closedEBall c r = (fun x => c * x) '' closedEBall 1 r := by
  ext y
  simp only [Metric.mem_closedEBall, Set.mem_image]
  constructor
  · intro hy
    refine ⟨c⁻¹ * y, ?_, by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
    rw [show edist (c⁻¹ * y) 1 = edist (c * (c⁻¹ * y)) (c * 1) from (edist_mul_left c _ _).symm]
    simpa [← mul_assoc] using hy
  · rintro ⟨x, hx, rfl⟩
    calc edist (c * x) c = edist (c * x) (c * 1) := by rw [mul_one]
      _ = edist x 1 := edist_mul_left c x 1
      _ ≤ r := hx

theorem eball_eq_image (c : G) (r : ℝ≥0∞) :
    eball c r = (fun x => c * x) '' eball 1 r := by
  ext y
  simp only [Metric.mem_eball, Set.mem_image]
  constructor
  · intro hy
    refine ⟨c⁻¹ * y, ?_, by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
    rw [show edist (c⁻¹ * y) 1 = edist (c * (c⁻¹ * y)) (c * 1) from (edist_mul_left c _ _).symm]
    simpa [← mul_assoc] using hy
  · rintro ⟨x, hx, rfl⟩
    calc edist (c * x) c = edist (c * x) (c * 1) := by rw [mul_one]
      _ = edist x 1 := edist_mul_left c x 1
      _ < r := hx

section Haar

variable [MeasurableSpace G] [MeasurableMul G]

theorem measure_closedEBall_eq (μ : Measure G) [μ.IsMulLeftInvariant] (c : G) (r : ℝ≥0∞) :
    μ (closedEBall c r) = μ (closedEBall (1 : G) r) := by
  rw [closedEBall_eq_image, Set.image_mul_left, measure_preimage_mul]

theorem measure_eball_eq (μ : Measure G) [μ.IsMulLeftInvariant] (c : G) (r : ℝ≥0∞) :
    μ (eball c r) = μ (eball (1 : G) r) := by
  rw [eball_eq_image, Set.image_mul_left, measure_preimage_mul]

end Haar

/-! ## The covering–volume sandwich -/

section Sandwich

variable [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  (μ : Measure G) [hHaarμ : μ.IsHaarMeasure] [hProbμ : IsProbabilityMeasure μ]

omit [IsIsometricSMul G G] [BorelSpace G] [IsTopologicalGroup G] hProbμ in
theorem measure_eball_pos {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (eball (1 : G) r) := by
  refine Metric.isOpen_eball.measure_pos μ ⟨1, ?_⟩
  rw [Metric.mem_eball, edist_self]
  exact pos_iff_ne_zero.mpr hr

/-- Balls of half the separation radius around a separated set are disjoint, so their common
Haar measure bounds the cardinality. -/
theorem card_mul_measure_eball_le_one {ε : ℝ≥0} {S : Set G}
    (hS : Metric.IsSeparated (ε : ℝ≥0∞) S) (T : Finset G) (hT : ↑T ⊆ S) :
    (T.card : ℝ≥0∞) * μ (eball (1 : G) ((ε : ℝ≥0∞) / 2)) ≤ 1 := by
  classical
  have hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      Disjoint (eball x ((ε : ℝ≥0∞) / 2)) (eball y ((ε : ℝ≥0∞) / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr ?_
    intro z hzx hzy
    rw [Metric.mem_eball] at hzx hzy
    have hsep : (ε : ℝ≥0∞) < edist x y := hS (hT hx) (hT hy) hxy
    have hlt : edist x y < (ε : ℝ≥0∞) := by
      calc edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
        _ = edist z x + edist z y := by rw [edist_comm x z]
        _ < (ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2 := ENNReal.add_lt_add hzx hzy
        _ = (ε : ℝ≥0∞) := ENNReal.add_halves _
    exact absurd hlt (not_lt.mpr hsep.le)
  have hmeas : ∀ x : G, MeasurableSet (eball x ((ε : ℝ≥0∞) / 2)) := fun x =>
    Metric.isOpen_eball.measurableSet
  calc (T.card : ℝ≥0∞) * μ (eball (1 : G) ((ε : ℝ≥0∞) / 2))
      = ∑ t ∈ T, μ (eball t ((ε : ℝ≥0∞) / 2)) := by
        rw [Finset.sum_congr rfl (fun t _ => measure_eball_eq μ t ((ε : ℝ≥0∞) / 2)),
          Finset.sum_const, nsmul_eq_mul]
    _ = μ (⋃ t ∈ T, eball t ((ε : ℝ≥0∞) / 2)) :=
        (measure_biUnion_finset hdisj (fun t _ => hmeas t)).symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem encard_mul_measure_eball_le_one {ε : ℝ≥0} (hε : ε ≠ 0) {S : Set G}
    (hS : Metric.IsSeparated (ε : ℝ≥0∞) S) :
    (S.encard : ℝ≥0∞) * μ (eball (1 : G) ((ε : ℝ≥0∞) / 2)) ≤ 1 := by
  classical
  have hmpos : 0 < μ (eball (1 : G) ((ε : ℝ≥0∞) / 2)) := by
    refine measure_eball_pos μ ?_
    simp only [ne_eq, ENNReal.div_eq_zero_iff]
    push Not
    exact ⟨by exact_mod_cast hε, by norm_num⟩
  have hfin : S.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hmpos.ne' ENNReal.one_ne_top
    obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq N
    have := card_mul_measure_eball_le_one μ hS T hTsub
    rw [hTcard] at this
    exact absurd this (not_le.mpr hN)
  have hcard := card_mul_measure_eball_le_one μ hS hfin.toFinset (by simp)
  rw [hfin.encard_eq_coe_toFinset_card]
  simpa using hcard

theorem packingNumber_le_of_measure {ε : ℝ≥0} (hε : ε ≠ 0) {N : ℕ}
    (hN : 1 < (N : ℝ≥0∞) * μ (eball (1 : G) ((ε : ℝ≥0∞) / 2))) :
    Metric.packingNumber ε (Set.univ : Set G) ≤ (N : ℕ∞) := by
  refine iSup_le fun C => iSup_le fun _ => iSup_le fun hC => ?_
  by_contra hcon
  rw [not_le] at hcon
  have hle : (N : ℝ≥0∞) ≤ (C.encard : ℝ≥0∞) := by
    exact_mod_cast (ENat.toENNReal_le).mpr hcon.le
  have hbound := encard_mul_measure_eball_le_one μ hε hC
  have : (N : ℝ≥0∞) * μ (eball (1 : G) ((ε : ℝ≥0∞) / 2)) ≤ 1 :=
    le_trans (by gcongr) hbound
  exact absurd this (not_le.mpr hN)

include μ hHaarμ hProbμ in
theorem packingNumber_ne_top {ε : ℝ≥0} (hε : ε ≠ 0) :
    Metric.packingNumber ε (Set.univ : Set G) ≠ ⊤ := by
  have hmpos : 0 < μ (eball (1 : G) ((ε : ℝ≥0∞) / 2)) := by
    refine measure_eball_pos μ ?_
    simp only [ne_eq, ENNReal.div_eq_zero_iff]
    push Not
    exact ⟨by exact_mod_cast hε, by norm_num⟩
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hmpos.ne' ENNReal.one_ne_top
  exact ne_top_of_le_ne_top (by simp) (packingNumber_le_of_measure μ hε hN)

/-- **Right half of the covering–volume sandwich.**  The covering number at radius `ε` times the
Haar volume of the ball of radius `ε/2` is at most one. -/
theorem coveringNumber_mul_measure_eball_le_one {ε : ℝ≥0} (hε : ε ≠ 0) :
    (Metric.coveringNumber ε (Set.univ : Set G) : ℝ≥0∞) *
      μ (eball (1 : G) ((ε : ℝ≥0∞) / 2)) ≤ 1 := by
  have hPtop := packingNumber_ne_top μ hε
  have hsep := Metric.isSeparated_maximalSeparatedSet (ε := ε) (A := (Set.univ : Set G))
  have hcard := Metric.encard_maximalSeparatedSet (ε := ε) (A := (Set.univ : Set G)) hPtop
  have hbound := encard_mul_measure_eball_le_one μ hε hsep
  rw [hcard] at hbound
  refine le_trans ?_ hbound
  gcongr
  exact_mod_cast ENat.toENNReal_le.mpr (Metric.coveringNumber_le_packingNumber ε Set.univ)

/-- **Left half of the covering–volume sandwich.**  The covering number at radius `ε` times the
Haar volume of the closed ball of radius `ε` is at least one. -/
theorem one_le_coveringNumber_mul_measure_closedEBall {ε : ℝ≥0} (hε : ε ≠ 0) :
    1 ≤ (Metric.coveringNumber ε (Set.univ : Set G) : ℝ≥0∞) *
      μ (closedEBall (1 : G) (ε : ℝ≥0∞)) := by
  classical
  have hPtop := packingNumber_ne_top μ hε
  have hCtop : Metric.coveringNumber ε (Set.univ : Set G) ≠ ⊤ :=
    ne_top_of_le_ne_top hPtop (Metric.coveringNumber_le_packingNumber ε Set.univ)
  set C : Set G := Metric.minimalCover ε (Set.univ : Set G) with hC
  have hCfin : C.Finite := Metric.finite_minimalCover
  have hCcover : Metric.IsCover ε Set.univ C := Metric.isCover_minimalCover hCtop
  have hCcard : C.encard = Metric.coveringNumber ε (Set.univ : Set G) :=
    Metric.encard_minimalCover hCtop
  have hsub : (Set.univ : Set G) ⊆ ⋃ c ∈ hCfin.toFinset, closedEBall c (ε : ℝ≥0∞) := by
    intro x _
    obtain ⟨c, hcC, hdist⟩ := hCcover (Set.mem_univ x)
    refine Set.mem_biUnion (by simpa using hcC) ?_
    rw [Metric.mem_closedEBall]
    exact hdist
  calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
    _ ≤ μ (⋃ c ∈ hCfin.toFinset, closedEBall c (ε : ℝ≥0∞)) := measure_mono hsub
    _ ≤ ∑ c ∈ hCfin.toFinset, μ (closedEBall c (ε : ℝ≥0∞)) := measure_biUnion_finset_le _ _
    _ = (hCfin.toFinset.card : ℝ≥0∞) * μ (closedEBall (1 : G) (ε : ℝ≥0∞)) := by
        rw [Finset.sum_congr rfl (fun c _ => measure_closedEBall_eq μ c (ε : ℝ≥0∞)),
          Finset.sum_const, nsmul_eq_mul]
    _ = (Metric.coveringNumber ε (Set.univ : Set G) : ℝ≥0∞) *
          μ (closedEBall (1 : G) (ε : ℝ≥0∞)) := by
        rw [← hCcard, hCfin.encard_eq_coe_toFinset_card]
        norm_cast

end Sandwich

end GaloisForLFunctions.HTGeometry
