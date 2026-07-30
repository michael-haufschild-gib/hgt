import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Compact-group metric return law

Finite metric covers give deterministic return deadlines for every rotation
of a compact metric group.  The statement is dimension-free: the relevant
quantity is the exact covering number of the orbit carrier.
-/

open Set
open MeasureTheory
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

variable {G : Type*} [CommGroup G]

section MetricReturn

variable [PseudoEMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]

/-- A finite radius-`r` cover of a commutative metric group forces a
positive power to return within radius `2 * r` by the cardinality of the
cover. -/
theorem exists_pow_return_le_two_mul_of_finset_isCover
    (α : G) (r : ℝ≥0) (C : Finset G)
    (hcover : Metric.IsCover r Set.univ (C : Set G)) :
    ∃ n : ℕ, 0 < n ∧ n ≤ C.card ∧ edist (α ^ n) 1 ≤ 2 * r := by
  let center : Fin (C.card + 1) → C := fun k =>
    ⟨(hcover (by simp : α ^ k.1 ∈ (Set.univ : Set G))).choose,
      (hcover (by simp : α ^ k.1 ∈ (Set.univ : Set G))).choose_spec.1⟩
  have hcenter (k : Fin (C.card + 1)) :
      edist (α ^ k.1) (center k : G) ≤ r :=
    (hcover (by simp : α ^ k.1 ∈ (Set.univ : Set G))).choose_spec.2
  obtain ⟨i, j, hij, hcenter_eq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt center (by simp)
  have collision {i j : Fin (C.card + 1)} (hij_lt : i.1 < j.1)
      (hcenter_eq : center i = center j) :
      ∃ n : ℕ, 0 < n ∧ n ≤ C.card ∧ edist (α ^ n) 1 ≤ 2 * r := by
    refine ⟨j.1 - i.1, Nat.sub_pos_of_lt hij_lt, ?_, ?_⟩
    · exact (Nat.sub_le _ _).trans (Nat.lt_succ_iff.mp j.2)
    · have hpair : edist (α ^ i.1) (α ^ j.1) ≤ r + r := by
        calc
          edist (α ^ i.1) (α ^ j.1)
              ≤ edist (α ^ i.1) (center i : G) +
                  edist (center i : G) (α ^ j.1) := edist_triangle ..
          _ ≤ r + r := add_le_add (hcenter i) (by
            simpa [hcenter_eq, edist_comm] using hcenter j)
      have htranslate :
          edist (α ^ (j.1 - i.1)) 1 = edist (α ^ j.1) (α ^ i.1) := by
        rw [pow_sub α (Nat.le_of_lt hij_lt)]
        calc
          edist (α ^ j.1 * (α ^ i.1)⁻¹) 1 =
              edist ((α ^ j.1 * (α ^ i.1)⁻¹) * α ^ i.1)
                (1 * α ^ i.1) :=
            (edist_mul_right
              (α ^ j.1 * (α ^ i.1)⁻¹) 1 (α ^ i.1)).symm
          _ = edist (α ^ j.1) (α ^ i.1) := by simp
      rw [htranslate, edist_comm]
      simpa [two_mul] using hpair
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · exact collision hij_lt hcenter_eq
  · exact collision hji_lt hcenter_eq.symm

/-- On a compact commutative metric group, every rotation returns within
twice the cover radius by the exact covering number. -/
theorem exists_pow_return_le_two_mul_coveringNumber
    [CompactSpace G] (α : G) (r : ℝ≥0) (hr : r ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      (n : ℕ∞) ≤ Metric.coveringNumber r (Set.univ : Set G) ∧
      edist (α ^ n) 1 ≤ 2 * r := by
  obtain ⟨C, hCsub, hCfin, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hr
      (isCompact_univ : IsCompact (Set.univ : Set G))
  have hcover_ne_top :
      Metric.coveringNumber r (Set.univ : Set G) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hCfin)
      (hCcover.coveringNumber_le_encard hCsub)
  let S := Metric.minimalCover r (Set.univ : Set G)
  have hSfin : S.Finite := Metric.finite_minimalCover
  let F : Finset G := hSfin.toFinset
  have hFcover : Metric.IsCover r Set.univ (F : Set G) := by
    simpa [F, S] using Metric.isCover_minimalCover hcover_ne_top
  obtain ⟨n, hn_pos, hn_card, hn_dist⟩ :=
    exists_pow_return_le_two_mul_of_finset_isCover α r F hFcover
  refine ⟨n, hn_pos, ?_, hn_dist⟩
  calc
    (n : ℕ∞) ≤ F.card := by exact_mod_cast hn_card
    _ = (S : Set G).encard := by
      simpa [F] using hSfin.encard_eq_coe_toFinset_card.symm
    _ = Metric.coveringNumber r (Set.univ : Set G) := by
      simpa [S] using Metric.encard_minimalCover hcover_ne_top

end MetricReturn

/-- If the first `L` power maps preserve probability and `Good` is conull,
a target of measure smaller than `1 / L` is avoided by the first `L`
powers of some point in `Good`. -/
theorem exists_mem_avoids_first_powers_of_measure_budget
    [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (B Good : Set G) (hB : MeasurableSet B)
    (hGood : μ Goodᶜ = 0)
    (hpow : ∀ k : ℕ, MeasurePreserving (fun x : G => x ^ (k + 1)) μ μ)
    (L : ℕ) (hbudget : (L : ℝ≥0∞) * μ B < 1) :
    ∃ α ∈ Good, ∀ n : ℕ, 0 < n → n ≤ L → α ^ n ∉ B := by
  let bad : Set G :=
    ⋃ k ∈ Finset.range L, (fun x : G => x ^ (k + 1)) ⁻¹' B
  have hbad_meas : MeasurableSet bad := by
    dsimp [bad]
    exact Finset.measurableSet_biUnion _ fun k _ =>
      hB.preimage (hpow k).measurable
  have hbad_lt : μ bad < 1 := by
    calc
      μ bad ≤ ∑ k ∈ Finset.range L,
          μ ((fun x : G => x ^ (k + 1)) ⁻¹' B) :=
        measure_biUnion_finset_le _ _
      _ = ∑ _k ∈ Finset.range L, μ B := by
        apply Finset.sum_congr rfl
        intro k _
        exact (hpow k).measure_preimage hB.nullMeasurableSet
      _ = (L : ℝ≥0∞) * μ B := by simp
      _ < 1 := hbudget
  have hbad_compl_pos : 0 < μ badᶜ := by
    rw [measure_compl hbad_meas (measure_ne_top μ bad)]
    simpa using (tsub_pos_iff_lt.mpr hbad_lt)
  have hinter_pos : 0 < μ (badᶜ ∩ Good) := by
    rw [measure_inter_conull hGood]
    exact hbad_compl_pos
  obtain ⟨α, hαbad, hαGood⟩ :=
    nonempty_of_measure_ne_zero hinter_pos.ne'
  refine ⟨α, hαGood, ?_⟩
  intro n hn_pos hnL hnB
  have hk : n - 1 ∈ Finset.range L := by
    simp only [Finset.mem_range]
    omega
  have hpow_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
  have : α ∈ bad := by
    simp only [bad, Set.mem_iUnion]
    exact ⟨n - 1, ⟨hk, by simpa [hpow_eq] using hnB⟩⟩
  exact hαbad this

/-- Haar specialization of
`exists_mem_avoids_first_powers_of_measure_budget` for compact rootable
commutative groups. -/
theorem exists_mem_avoids_first_powers_of_haar_budget
    [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G]
    [BorelSpace G] [CompactSpace G] [RootableBy G ℤ]
    (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (B Good : Set G) (hB : MeasurableSet B)
    (hGood : μ Goodᶜ = 0)
    (L : ℕ) (hbudget : (L : ℝ≥0∞) * μ B < 1) :
    ∃ α ∈ Good, ∀ n : ℕ, 0 < n → n ≤ L → α ^ n ∉ B := by
  apply exists_mem_avoids_first_powers_of_measure_budget
    μ B Good hB hGood _ L hbudget
  intro k
  have h :=
    MeasureTheory.Measure.measurePreserving_zpow μ
      (n := ((k + 1 : ℕ) : ℤ)) (by omega)
  convert h using 1
  funext x
  exact (zpow_natCast x (k + 1)).symm

end GaloisForLFunctions.HTGeometry
