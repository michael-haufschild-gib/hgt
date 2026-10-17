import GaloisForLFunctions.BiScaleUncertainty.OverlapSafeCollarMeasureTransport
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section


/-- Adjacent logarithmic-grid gaps are strictly smaller than two collar radii. -/
theorem log_adjacent_gap_lt_log_two (n : ℕ) :
    Real.log ((n + 3 : ℕ) : ℝ) - Real.log ((n + 2 : ℕ) : ℝ) < Real.log 2 := by
  have hp : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hlt : (((n + 3 : ℕ) : ℝ)) < 2 * ((n + 2 : ℕ) : ℝ) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    linarith
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < ((n + 3 : ℕ) : ℝ)) hlt
  rw [Real.log_mul (by norm_num) hp.ne'] at h
  linarith

/-- Half-log-two collars around every integer from 2 to N form one interval. -/
theorem logarithmic_collar_union (n : ℕ) :
    (⋃ k ∈ Finset.range (n + 1),
      Ioo (Real.log ((k + 2 : ℕ) : ℝ) - Real.log 2 / 2)
          (Real.log ((k + 2 : ℕ) : ℝ) + Real.log 2 / 2)) =
      Ioo (Real.log 2 / 2) (Real.log ((n + 2 : ℕ) : ℝ) + Real.log 2 / 2) := by
  induction n with
  | zero =>
      simp only [Nat.zero_add, Finset.range_one, Finset.mem_singleton,
        iUnion_iUnion_eq_left, Nat.cast_ofNat]
      congr 1
      ring
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by rfl, Finset.range_add_one]
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
      rw [ih, union_comm]
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hmono : Real.log ((n + 2 : ℕ) : ℝ) < Real.log ((n + 3 : ℕ) : ℝ) :=
        Real.log_lt_log (by positivity) (by exact_mod_cast (show n + 2 < n + 3 by omega))
      have hbase : Real.log 2 ≤ Real.log ((n + 2 : ℕ) : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n + 2 by omega))
      have hgap := log_adjacent_gap_lt_log_two n
      rw [Ioo_union_Ioo' (by linarith) (by linarith)]
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]

/-- Truncating the overlapping logarithmic collars at log N covers precisely
all of the finite interval beyond the origin half-collar. -/
theorem truncated_logarithmic_collar_union (n : ℕ) :
    (⋃ k ∈ Finset.range (n + 1),
      truncatedPhysicalCollar (Real.log ((k + 2 : ℕ) : ℝ)) (Real.log 2 / 2)
        (Real.log ((n + 2 : ℕ) : ℝ))) =
      Ioo (Real.log 2 / 2) (Real.log ((n + 2 : ℕ) : ℝ)) := by
  simp only [truncatedPhysicalCollar]
  rw [← iUnion₂_inter, logarithmic_collar_union]
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  ext x
  simp only [mem_inter_iff, mem_Ioo]
  constructor
  · rintro ⟨⟨ha, _⟩, ⟨_, hb⟩⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨⟨ha, by linarith⟩, ⟨by linarith, hb⟩⟩

/-- Exact decomposition of finite-interval archimedean energy into one origin
interval and multiplicity-normalized signed logarithmic collars. -/
theorem arch_logarithmic_origin_collar_decomposition (n : ℕ) (h : C(ℝ, ℝ)) :
    (∫⁻ x in Ioo 0 (Real.log ((n + 2 : ℕ) : ℝ)), continuousArchIncrementDensity h x) =
      (∫⁻ y in Ioo 0 (Real.log 2 / 2), continuousArchIncrementDensity h y) +
      ∑ k ∈ Finset.range (n + 1),
        ((∫⁻ y in Ioo 0 (Real.log 2 / 2),
          allocatedCollarDensity (Finset.range (n + 1))
            (fun j => Real.log ((j + 2 : ℕ) : ℝ)) (Real.log 2 / 2)
            (Real.log ((n + 2 : ℕ) : ℝ)) (continuousArchIncrementDensity h) k
              (Real.log ((k + 2 : ℕ) : ℝ) - y)) +
         (∫⁻ y in Ioo 0 (Real.log 2 / 2),
          allocatedCollarDensity (Finset.range (n + 1))
            (fun j => Real.log ((j + 2 : ℕ) : ℝ)) (Real.log 2 / 2)
            (Real.log ((n + 2 : ℕ) : ℝ)) (continuousArchIncrementDensity h) k
              (Real.log ((k + 2 : ℕ) : ℝ) + y))) := by
  rw [archimedean_collar_measure_transport, truncated_logarithmic_collar_union]
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Real.log 2 ≤ Real.log ((n + 2 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n + 2 by omega))
  have hd : Disjoint (Ioo 0 (Real.log 2 / 2))
      (Ioo (Real.log 2 / 2) (Real.log ((n + 2 : ℕ) : ℝ))) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2.le) hy.1
  rw [← lintegral_union measurableSet_Ioo hd]
  apply setLIntegral_congr
  filter_upwards [volume.ae_ne (Real.log 2 / 2)] with x hx
  apply propext
  change (0 < x ∧ x < Real.log ((n + 2 : ℕ) : ℝ)) ↔
    ((0 < x ∧ x < Real.log 2 / 2) ∨
      (Real.log 2 / 2 < x ∧ x < Real.log ((n + 2 : ℕ) : ℝ)))
  constructor
  · rintro ⟨ha, hb'⟩
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exact Or.inl ⟨ha, hlt⟩
    · exact Or.inr ⟨hgt, hb'⟩
  · rintro (⟨ha, hb'⟩ | ⟨ha, hb'⟩) <;> constructor <;> linarith

end
end GaloisForLFunctions.BiScaleUncertainty
