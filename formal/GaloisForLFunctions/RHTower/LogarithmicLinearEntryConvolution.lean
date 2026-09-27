import GaloisForLFunctions.RHTower.LogarithmicExponentialEntryConvolution

/-!
# Reflection factorization of the causal linear ramp

Two unit entries convolve to `max t 0`. This complements the exponential
ramp factorization and keeps arbitrary signed coefficients in both factors.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

def logarithmicLinearRamp (t : ℝ) : ℝ := max t 0

theorem logarithmicLinearRamp_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    logarithmicLinearRamp t = 0 := max_eq_right ht

theorem logarithmicLinearRamp_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    logarithmicLinearRamp t = t := max_eq_left ht

private theorem unit_pair_eq_window (p q T s : ℝ) :
    logarithmicUnitEntry p s * logarithmicUnitEntry q (T - s) =
      (Icc p (T - q)).indicator (fun _ : ℝ => 1) s := by
  have hcut : q ≤ T - s ↔ s ≤ T - q := by constructor <;> intro h <;> linarith
  by_cases hs : p ≤ s <;> by_cases ht : s ≤ T - q <;>
    simp [logarithmicUnitEntry, Set.indicator, hcut, hs, ht]

theorem intervalIntegrable_logarithmicUnitEntry_pair (p q T a b : ℝ) :
    IntervalIntegrable (fun s => logarithmicUnitEntry p s *
      logarithmicUnitEntry q (T - s)) volume a b := by
  simp_rw [unit_pair_eq_window]
  have hi : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b := intervalIntegrable_const
  exact ⟨hi.1.indicator measurableSet_Icc, hi.2.indicator measurableSet_Icc⟩

theorem integral_logarithmicUnitEntry_pair {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, logarithmicUnitEntry p s *
      logarithmicUnitEntry q (T - s)) = logarithmicLinearRamp (T - p - q) := by
  simp_rw [unit_pair_eq_window]
  by_cases hpq : p + q ≤ T
  · have hwin : (∫ s in (0 : ℝ)..T, (Icc p (T - q)).indicator (fun _ : ℝ => (1 : ℝ)) s) =
        ∫ s in p..(T - q), (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le (by linarith only [hp, hq, hpq]),
        ← integral_Icc_eq_integral_Ioc,
        integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr (Icc_subset_Icc hp (by linarith only [hq])),
        integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith only [hpq])]
    rw [hwin, intervalIntegral.integral_const,
      logarithmicLinearRamp_of_nonneg (by linarith only [hpq])]
    simp only [smul_eq_mul, mul_one]
    ring
  · have he : Icc p (T - q) = ∅ := Icc_eq_empty_of_lt (by linarith)
    rw [he, Set.indicator_empty, intervalIntegral.integral_zero,
      logarithmicLinearRamp_of_nonpos (by linarith)]

private theorem one_profile_eq_sum (w : ℕ → ℝ) (U : ℕ) (t : ℝ) :
    logarithmicFiniteEntryProfile w U (fun _ => 1) t =
      ∑ n ∈ Finset.Icc 1 U, w n * logarithmicUnitEntry (Real.log n) t := by
  unfold logarithmicFiniteEntryProfile
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : Real.log n ≤ t <;> simp [logarithmicUnitEntry, hn]

private theorem profile_pair_expansion (w v : ℕ → ℝ) (U : ℕ) (T s : ℝ) :
    logarithmicFiniteEntryProfile w U (fun _ => 1) s *
      logarithmicFiniteEntryProfile v U (fun _ => 1) (T - s) =
      ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U, w a * v b *
        (logarithmicUnitEntry (Real.log a) s * logarithmicUnitEntry (Real.log b) (T - s)) := by
  rw [one_profile_eq_sum, one_profile_eq_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem intervalIntegrable_logarithmicFiniteUnitEntry_pair
    (w v : ℕ → ℝ) (U : ℕ) (T a b : ℝ) :
    IntervalIntegrable (fun s => logarithmicFiniteEntryProfile w U (fun _ => 1) s *
      logarithmicFiniteEntryProfile v U (fun _ => 1) (T - s)) volume a b := by
  have hi (m n : ℕ) :=
    (intervalIntegrable_logarithmicUnitEntry_pair (Real.log m) (Real.log n) T a b).const_mul (w m * v n)
  have hs := IntervalIntegrable.sum (s := Finset.Icc 1 U)
    (fun m _ => IntervalIntegrable.sum (s := Finset.Icc 1 U) (fun n _ => hi m n))
  apply hs.congr
  intro s _
  simpa only [Finset.sum_apply] using (profile_pair_expansion w v U T s).symm

theorem integral_logarithmicFiniteUnitEntry_pair (w v : ℕ → ℝ) (U : ℕ) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, logarithmicFiniteEntryProfile w U (fun _ => 1) s *
      logarithmicFiniteEntryProfile v U (fun _ => 1) (T - s)) =
      ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U,
        w a * v b * logarithmicLinearRamp (T - Real.log (a * b : ℕ)) := by
  let term := fun (a b : ℕ) (s : ℝ) => w a * v b *
    (logarithmicUnitEntry (Real.log a) s * logarithmicUnitEntry (Real.log b) (T - s))
  have hi (a b : ℕ) : IntervalIntegrable (term a b) volume 0 T :=
    (intervalIntegrable_logarithmicUnitEntry_pair (Real.log a) (Real.log b) T 0 T).const_mul _
  have hirow (a : ℕ) : IntervalIntegrable
      (fun s => ∑ b ∈ Finset.Icc 1 U, term a b s) volume 0 T := by
    apply (IntervalIntegrable.sum (s := Finset.Icc 1 U) (fun b _ => hi a b)).congr
    intro s _
    simp only [Finset.sum_apply]
  simp_rw [profile_pair_expansion]
  rw [intervalIntegral.integral_finsetSum (fun a _ => hirow a)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [intervalIntegral.integral_finsetSum (fun b _ => hi a b)]
  apply Finset.sum_congr rfl
  intro b hb
  have hap : (0 : ℝ) < a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have hbp : (0 : ℝ) < b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
  rw [intervalIntegral.integral_const_mul,
    integral_logarithmicUnitEntry_pair (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg b) T,
    Nat.cast_mul, Real.log_mul hap.ne' hbp.ne', sub_add_eq_sub_sub]

end RHTower
