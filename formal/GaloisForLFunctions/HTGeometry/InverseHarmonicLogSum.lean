import GaloisForLFunctions.HTGeometry.HarmonicLogWindow

/-!
# Logarithmic increments weighted by inverse harmonic numbers

Replacing the harmonic increment by the corresponding logarithmic increment
costs a summable reciprocal-square error. The weighted sum therefore differs
from the logarithm of the harmonic number by a bounded nonnegative amount.
-/

noncomputable section
open Finset

namespace GaloisForLFunctions.HTGeometry

/-- Every positive harmonic number contains its first unit summand. -/
theorem one_le_real_harmonic {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ (harmonic n : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  have h := Finset.single_le_sum (f := fun k : ℕ => (k : ℝ)⁻¹)
    (fun _ _ => by positivity) (mem_Icc.mpr ⟨le_rfl, hn⟩)
  simpa only [Nat.cast_one, inv_one] using h

private theorem log_increment_div_sub_bounds {x H : ℝ} (hx : 1 ≤ x) (hH : 1 ≤ H) :
    0 ≤ Real.log ((x + 1) / x) / H - Real.log ((H + 1 / (x + 1)) / H) ∧
    Real.log ((x + 1) / x) / H - Real.log ((H + 1 / (x + 1)) / H) ≤
      2 / (x * (x + 1)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hx1 : 0 < x + 1 := by linarith only [hx]
  have hy : 0 < H + 1 / (x + 1) := by positivity
  have hD : 0 < (x + 1) * H + 1 := by positivity
  have ha₀ : 1 / (x + 1) ≤ Real.log ((x + 1) / x) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx0)
    have he : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by
      field_simp
      ring
    rwa [he] at h
  have ha₁ : Real.log ((x + 1) / x) ≤ 1 / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx1 hx0)
    have he : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    rwa [he] at h
  have hb₀ : 1 / ((x + 1) * H + 1) ≤ Real.log ((H + 1 / (x + 1)) / H) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hH0)
    have he : 1 - ((H + 1 / (x + 1)) / H)⁻¹ = 1 / ((x + 1) * H + 1) := by
      field_simp; ring
    rwa [he] at h
  have hb₁ : Real.log ((H + 1 / (x + 1)) / H) ≤ 1 / ((x + 1) * H) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy hH0)
    have he : (H + 1 / (x + 1)) / H - 1 = 1 / ((x + 1) * H) := by
      field_simp; ring
    rwa [he] at h
  refine ⟨sub_nonneg.mpr ?_, ?_⟩
  · calc
      _ ≤ 1 / ((x + 1) * H) := hb₁
      _ = (1 / (x + 1)) / H := by field_simp
      _ ≤ Real.log ((x + 1) / x) / H := div_le_div_of_nonneg_right ha₀ hH0.le
  · calc
      _ ≤ (1 / x) / H - 1 / ((x + 1) * H + 1) :=
        sub_le_sub (div_le_div_of_nonneg_right ha₁ hH0.le) hb₀
      _ = (H + 1) / (x * H * ((x + 1) * H + 1)) := by
        field_simp; ring
      _ ≤ (2 * H) / (x * H * ((x + 1) * H + 1)) :=
        div_le_div_of_nonneg_right (by linarith only [hH]) (by positivity)
      _ = 2 / (x * ((x + 1) * H + 1)) := by field_simp
      _ ≤ 2 / (x * (x + 1)) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        apply mul_le_mul_of_nonneg_left _ hx0.le
        have h := mul_nonneg hx1.le (sub_nonneg.mpr hH)
        nlinarith only [h]

/-- The logarithmic mesh sum with cofactor harmonic resistance. -/
def inverseHarmonicLogIncrementSum (N : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 N, (Real.log ((k : ℝ) + 1) - Real.log k) / (harmonic k : ℝ)

/-- Finite summation by parts exposes the successive inverse harmonic drops. -/
theorem inverseHarmonicLogIncrementSum_eq_layers {N : ℕ} (hN : 1 ≤ N) :
    inverseHarmonicLogIncrementSum N = Real.log N / (harmonic N : ℝ) +
      ∑ k ∈ Ico 1 N, (1 / (harmonic k : ℝ) - 1 / (harmonic (k + 1) : ℝ)) *
        Real.log ((k : ℝ) + 1) := by
  induction N, hN using Nat.le_induction with
  | base => simp [inverseHarmonicLogIncrementSum]
  | succ N hN ih =>
    have hs : inverseHarmonicLogIncrementSum (N + 1) = inverseHarmonicLogIncrementSum N +
        (Real.log ((N : ℝ) + 1) - Real.log N) / (harmonic N : ℝ) := by
      unfold inverseHarmonicLogIncrementSum
      rw [sum_Ico_succ_top hN]
    rw [hs, ih, sum_Ico_succ_top hN]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private theorem harmonic_log_increment_bounds {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ (Real.log ((k : ℝ) + 1) - Real.log k) / (harmonic k : ℝ) -
      (Real.log (harmonic (k + 1) : ℝ) - Real.log (harmonic k : ℝ)) ∧
    (Real.log ((k : ℝ) + 1) - Real.log k) / (harmonic k : ℝ) -
      (Real.log (harmonic (k + 1) : ℝ) - Real.log (harmonic k : ℝ)) ≤
        2 / ((k : ℝ) * (k + 1)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hH := one_le_real_harmonic hk
  have hH0 : 0 < (harmonic k : ℝ) := zero_lt_one.trans_le hH
  have hH1 : 0 < (harmonic (k + 1) : ℝ) :=
    zero_lt_one.trans_le (one_le_real_harmonic (by omega))
  have hs : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k : ℝ) + 1) := by
    rw [harmonic_succ]
    push_cast
    simp only [one_div]
  have h := log_increment_div_sub_bounds (x := (k : ℝ)) (by exact_mod_cast hk) hH
  rw [Real.log_div hk1.ne' hk0.ne', ← hs, Real.log_div hH1.ne' hH0.ne'] at h
  exact h

/-- Inverse harmonic weights give the logarithm of the harmonic number, with error at most two. -/
theorem inverseHarmonicLogIncrementSum_sub_log_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ inverseHarmonicLogIncrementSum N - Real.log (harmonic N : ℝ) ∧
    inverseHarmonicLogIncrementSum N - Real.log (harmonic N : ℝ) ≤ 2 := by
  have ht : (∑ k ∈ Ico 1 N,
      (Real.log (harmonic (k + 1) : ℝ) - Real.log (harmonic k : ℝ))) =
        Real.log (harmonic N : ℝ) := by
    rw [sum_Ico_eq_sub _ hN,
      sum_range_sub (fun k : ℕ => Real.log (harmonic k : ℝ)) N,
      sum_range_sub (fun k : ℕ => Real.log (harmonic k : ℝ)) 1]
    have h1 : Real.log (harmonic 1 : ℝ) = 0 := by norm_num [harmonic]
    rw [h1]
    ring
  have he : inverseHarmonicLogIncrementSum N - Real.log (harmonic N : ℝ) =
      ∑ k ∈ Ico 1 N, ((Real.log ((k : ℝ) + 1) - Real.log k) / (harmonic k : ℝ) -
        (Real.log (harmonic (k + 1) : ℝ) - Real.log (harmonic k : ℝ))) := by
    rw [sum_sub_distrib, ht]
    rfl
  rw [he]
  refine ⟨sum_nonneg fun k hk => (harmonic_log_increment_bounds (mem_Ico.mp hk).1).1, ?_⟩
  calc
    _ ≤ ∑ k ∈ Ico 1 N, 2 / ((k : ℝ) * (k + 1)) :=
      sum_le_sum fun k hk => (harmonic_log_increment_bounds (mem_Ico.mp hk).1).2
    _ = 2 - 2 / (N : ℝ) := by
      have hp : (∑ k ∈ Ico 1 N, 2 / ((k : ℝ) * (k + 1))) =
          ∑ k ∈ Ico 1 N, ((-2 / ((k + 1 : ℕ) : ℝ)) - (-2 / (k : ℝ))) := by
        apply sum_congr rfl
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Ico.mp hk).1
        push_cast
        field_simp; ring
      rw [hp, sum_Ico_eq_sub _ hN,
        sum_range_sub (fun k : ℕ => -2 / (k : ℝ)) N,
        sum_range_sub (fun k : ℕ => -2 / (k : ℝ)) 1]
      norm_num; ring
    _ ≤ 2 := sub_le_self _ (by positivity)

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.inverseHarmonicLogIncrementSum_sub_log_bounds
