import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Compact additive-group metric return law

Finite metric covers give deterministic return deadlines for translations of a compact additive
metric group. Applying the bounded return law to an arbitrary large multiple produces cofinally
large near-identity returns. This additive infrastructure is the recurrence input for formation
properness selection.
-/

open Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [AddCommGroup K]

section AdditiveMetricReturn

variable [PseudoEMetricSpace K] [IsIsometricVAdd Kᵃᵒᵖ K]

/-- A finite radius-`r` cover of a commutative additive metric group forces a positive natural
multiple to return within radius `2 * r` by the cardinality of the cover. -/
theorem exists_nsmul_return_le_two_mul_of_finset_isCover
    (α : K) (r : ℝ≥0) (C : Finset K)
    (hcover : Metric.IsCover r Set.univ (C : Set K)) :
    ∃ n : ℕ, 0 < n ∧ n ≤ C.card ∧ edist (n • α) 0 ≤ 2 * r := by
  let center : Fin (C.card + 1) → C := fun k =>
    ⟨(hcover (by simp : k.1 • α ∈ (Set.univ : Set K))).choose,
      (hcover (by simp : k.1 • α ∈ (Set.univ : Set K))).choose_spec.1⟩
  have hcenter (k : Fin (C.card + 1)) :
      edist (k.1 • α) (center k : K) ≤ r :=
    (hcover (by simp : k.1 • α ∈ (Set.univ : Set K))).choose_spec.2
  obtain ⟨i, j, hij, hcenter_eq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt center (by simp)
  have collision {i j : Fin (C.card + 1)} (hij_lt : i.1 < j.1)
      (hcenter_eq : center i = center j) :
      ∃ n : ℕ, 0 < n ∧ n ≤ C.card ∧ edist (n • α) 0 ≤ 2 * r := by
    refine ⟨j.1 - i.1, Nat.sub_pos_of_lt hij_lt, ?_, ?_⟩
    · exact (Nat.sub_le _ _).trans (Nat.lt_succ_iff.mp j.2)
    · have hpair : edist (i.1 • α) (j.1 • α) ≤ r + r := by
        calc
          edist (i.1 • α) (j.1 • α)
              ≤ edist (i.1 • α) (center i : K) +
                  edist (center i : K) (j.1 • α) := edist_triangle ..
          _ ≤ r + r := add_le_add (hcenter i) (by
            simpa [hcenter_eq, edist_comm] using hcenter j)
      have htranslate :
          edist ((j.1 - i.1) • α) 0 = edist (j.1 • α) (i.1 • α) := by
        rw [sub_nsmul α (Nat.le_of_lt hij_lt)]
        calc
          edist (j.1 • α + -(i.1 • α)) 0 =
              edist ((j.1 • α + -(i.1 • α)) + i.1 • α)
                (0 + i.1 • α) :=
            (edist_add_right (j.1 • α + -(i.1 • α)) 0 (i.1 • α)).symm
          _ = edist (j.1 • α) (i.1 • α) := by simp
      rw [htranslate, edist_comm]
      simpa [two_mul] using hpair
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · exact collision hij_lt hcenter_eq
  · exact collision hji_lt hcenter_eq.symm

/-- On a compact commutative additive metric group, every translation returns within twice the
cover radius by the exact covering number. -/
theorem exists_nsmul_return_le_two_mul_coveringNumber
    [CompactSpace K] (α : K) (r : ℝ≥0) (hr : r ≠ 0) :
    ∃ n : ℕ, 0 < n ∧
      (n : ℕ∞) ≤ Metric.coveringNumber r (Set.univ : Set K) ∧
      edist (n • α) 0 ≤ 2 * r := by
  obtain ⟨C, hCsub, hCfin, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hr
      (isCompact_univ : IsCompact (Set.univ : Set K))
  have hcover_ne_top :
      Metric.coveringNumber r (Set.univ : Set K) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hCfin)
      (hCcover.coveringNumber_le_encard hCsub)
  let S := Metric.minimalCover r (Set.univ : Set K)
  have hSfin : S.Finite := Metric.finite_minimalCover
  let F : Finset K := hSfin.toFinset
  have hFcover : Metric.IsCover r Set.univ (F : Set K) := by
    simpa [F, S] using Metric.isCover_minimalCover hcover_ne_top
  obtain ⟨n, hn_pos, hn_card, hn_dist⟩ :=
    exists_nsmul_return_le_two_mul_of_finset_isCover α r F hFcover
  refine ⟨n, hn_pos, ?_, hn_dist⟩
  calc
    (n : ℕ∞) ≤ F.card := by exact_mod_cast hn_card
    _ = (S : Set K).encard := by
      simpa [F] using hSfin.encard_eq_coe_toFinset_card.symm
    _ = Metric.coveringNumber r (Set.univ : Set K) := by
      simpa [S] using Metric.encard_minimalCover hcover_ne_top

/-- Compact recurrence is cofinal in word length: for every threshold there is a strictly larger
multiple returning to the same fixed phase ball. -/
theorem exists_large_nsmul_return_le_two_mul
    [CompactSpace K] (α : K) (r : ℝ≥0) (hr : r ≠ 0) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ edist (n • α) 0 ≤ 2 * r := by
  obtain ⟨q, hq_pos, _hq_cover, hq_dist⟩ :=
    exists_nsmul_return_le_two_mul_coveringNumber ((N + 1) • α) r hr
  refine ⟨(N + 1) * q, ?_, ?_⟩
  · have hle : N + 1 ≤ (N + 1) * q := Nat.le_mul_of_pos_right (N + 1) hq_pos
    omega
  · simpa [mul_nsmul] using hq_dist

end AdditiveMetricReturn

end GaloisForLFunctions.HTGeometry
