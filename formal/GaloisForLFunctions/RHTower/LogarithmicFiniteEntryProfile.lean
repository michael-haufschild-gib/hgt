import GaloisForLFunctions.RHTower.LogarithmicMobiusShortReconstruction
import GaloisForLFunctions.RHTower.LogarithmicEntryIntegration

/-!
# Finite causal logarithmic profiles

Each coefficient enters at its own logarithmic delay. A fixed finite
prefix is equivalent to the moving minimum cutoff, including negative
times. The Möbius specialization is the actual short inverse.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

def logarithmicFiniteEntryProfile (w : ℕ → ℝ) (U : ℕ) (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 U,
    (Ici (Real.log n)).indicator (fun t => w n * f (t - Real.log n)) T

theorem logarithmicFiniteEntryProfile_eq_min_prefix
    (w : ℕ → ℝ) (U : ℕ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicFiniteEntryProfile w U f T =
      ∑ n ∈ Finset.Icc 1 (min U ⌊Real.exp T⌋₊), w n * f (T - Real.log n) := by
  classical
  have hset : (Finset.Icc 1 U).filter (fun n : ℕ => Real.log n ≤ T) =
      Finset.Icc 1 (min U ⌊Real.exp T⌋₊) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨hn, hnU⟩, hlog⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      exact ⟨hn, hnU, (Nat.le_floor_iff (Real.exp_pos T).le).mpr
        ((Real.log_le_iff_le_exp hnpos).mp hlog)⟩
    · rintro ⟨hn, hnU, hnT⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      exact ⟨⟨hn, hnU⟩, (Real.log_le_iff_le_exp hnpos).mpr
        ((Nat.le_floor_iff (Real.exp_pos T).le).mp hnT)⟩
  rw [logarithmicFiniteEntryProfile, ← hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : Real.log n ≤ T <;> simp [hn]

theorem logarithmicShortMobiusInverse_eq_min_prefix (U : ℕ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicShortMobiusInverse U f T =
      ∑ n ∈ Finset.Icc 1 (min U ⌊Real.exp T⌋₊),
        (ArithmeticFunction.moebius n : ℝ) * f (T - Real.log n) := by
  classical
  have hset : (Finset.Icc 1 ⌊Real.exp T⌋₊).filter (fun n => n ≤ U) =
      Finset.Icc 1 (min U ⌊Real.exp T⌋₊) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    omega
  unfold logarithmicShortMobiusInverse logarithmicWeightedDilation
  simp only [Sieve.truncatedMoebius_apply, ite_mul, zero_mul]
  rw [← Finset.sum_filter, hset]

theorem logarithmicShortMobiusInverse_eq_finiteEntryProfile
    (U : ℕ) (f : ℝ → ℝ) (T : ℝ) :
    logarithmicShortMobiusInverse U f T =
      logarithmicFiniteEntryProfile (fun n => (ArithmeticFunction.moebius n : ℝ)) U f T := by
  rw [logarithmicShortMobiusInverse_eq_min_prefix, logarithmicFiniteEntryProfile_eq_min_prefix]

theorem logarithmicShortMobiusInverse_eq_full_of_cutoff_le (U : ℕ) (f : ℝ → ℝ)
    {T : ℝ} (hU : ⌊Real.exp T⌋₊ ≤ U) :
    logarithmicShortMobiusInverse U f T = logarithmicMobiusInverse f T := by
  rw [logarithmicShortMobiusInverse_eq_min_prefix, min_eq_right hU]
  rfl

theorem logarithmicFiniteEntryProfile_eq_zero_of_neg
    (w : ℕ → ℝ) (U : ℕ) (f : ℝ → ℝ) {T : ℝ} (hT : T < 0) :
    logarithmicFiniteEntryProfile w U f T = 0 := by
  have hfloor : ⌊Real.exp T⌋₊ = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hT)
  rw [logarithmicFiniteEntryProfile_eq_min_prefix, hfloor, min_zero]
  simp

end RHTower
