import GaloisForLFunctions.RHTower.LogarithmicFiniteEntryProfile

/-!
# Reflection factorization of the causal exponential ramp

The ramp `(exp t - 1)_+` factors into one exponential entry and one
constant entry. Finite signed arithmetic pairings therefore become a
single reflection integral, without discarding coefficient cancellation.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

def logarithmicExponentialRamp (t : ℝ) : ℝ := max (Real.exp t - 1) 0

def logarithmicExponentialEntry (p t : ℝ) : ℝ :=
  (Ici p).indicator (fun s => Real.exp (s - p)) t

def logarithmicUnitEntry (p t : ℝ) : ℝ :=
  (Ici p).indicator (fun _ : ℝ => 1) t

theorem logarithmicExponentialRamp_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    logarithmicExponentialRamp t = 0 :=
  max_eq_right (sub_nonpos.mpr (Real.exp_le_one_iff.mpr ht))

theorem logarithmicExponentialRamp_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    logarithmicExponentialRamp t = Real.exp t - 1 :=
  max_eq_left (sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht))

private theorem entry_pair_eq_window (p q T s : ℝ) :
    logarithmicExponentialEntry p s * logarithmicUnitEntry q (T - s) =
      (Icc p (T - q)).indicator (fun u => Real.exp (u - p)) s := by
  have hcut : q ≤ T - s ↔ s ≤ T - q := by constructor <;> intro h <;> linarith
  by_cases hs : p ≤ s <;> by_cases ht : s ≤ T - q <;>
    simp [logarithmicExponentialEntry, logarithmicUnitEntry, Set.indicator, hcut, hs, ht]

theorem intervalIntegrable_logarithmicExponentialEntry_pair (p q T a b : ℝ) :
    IntervalIntegrable (fun s => logarithmicExponentialEntry p s *
      logarithmicUnitEntry q (T - s)) volume a b := by
  simp_rw [entry_pair_eq_window]
  have hi : IntervalIntegrable (fun s : ℝ => Real.exp (s - p)) volume a b :=
    (Real.continuous_exp.comp (continuous_id.sub continuous_const)).intervalIntegrable a b
  exact ⟨hi.1.indicator measurableSet_Icc, hi.2.indicator measurableSet_Icc⟩

private theorem integral_closed_window (f : ℝ → ℝ) {a b T : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ s in (0 : ℝ)..T, (Icc a b).indicator f s) = ∫ s in a..b, f s := by
  rw [intervalIntegral.integral_of_le ((ha.trans hab).trans hb),
    ← integral_Icc_eq_integral_Ioc,
    integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_eq_left.mpr (Icc_subset_Icc ha hb), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab]

theorem integral_logarithmicExponentialEntry_pair {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, logarithmicExponentialEntry p s *
      logarithmicUnitEntry q (T - s)) = logarithmicExponentialRamp (T - p - q) := by
  simp_rw [entry_pair_eq_window]
  by_cases hpq : p + q ≤ T
  · rw [integral_closed_window _ hp (by linarith only [hpq]) (by linarith only [hq]),
      intervalIntegral.integral_comp_sub_right Real.exp,
      sub_self, integral_exp, Real.exp_zero,
      logarithmicExponentialRamp_of_nonneg (by linarith only [hpq])]
    congr 2
    ring
  · have he : Icc p (T - q) = ∅ := Icc_eq_empty_of_lt (by linarith)
    rw [he, Set.indicator_empty, intervalIntegral.integral_zero,
      logarithmicExponentialRamp_of_nonpos (by linarith)]

private theorem profile_pair_expansion (w v : ℕ → ℝ) (U : ℕ) (T s : ℝ) :
    logarithmicFiniteEntryProfile w U Real.exp s *
      logarithmicFiniteEntryProfile v U (fun _ => 1) (T - s) =
      ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U, w a * v b *
        (logarithmicExponentialEntry (Real.log a) s *
          logarithmicUnitEntry (Real.log b) (T - s)) := by
  have he : logarithmicFiniteEntryProfile w U Real.exp s =
      ∑ a ∈ Finset.Icc 1 U, w a * logarithmicExponentialEntry (Real.log a) s := by
    unfold logarithmicFiniteEntryProfile
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : Real.log a ≤ s <;> simp [logarithmicExponentialEntry, ha]
  have hu : logarithmicFiniteEntryProfile v U (fun _ => 1) (T - s) =
      ∑ b ∈ Finset.Icc 1 U, v b * logarithmicUnitEntry (Real.log b) (T - s) := by
    unfold logarithmicFiniteEntryProfile
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : Real.log b ≤ T - s <;> simp [logarithmicUnitEntry, hb]
  rw [he, hu, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem intervalIntegrable_logarithmicFiniteExponentialEntry_pair
    (w v : ℕ → ℝ) (U : ℕ) (T a b : ℝ) :
    IntervalIntegrable (fun s => logarithmicFiniteEntryProfile w U Real.exp s *
      logarithmicFiniteEntryProfile v U (fun _ => 1) (T - s)) volume a b := by
  have hi (m n : ℕ) :=
    (intervalIntegrable_logarithmicExponentialEntry_pair (Real.log m) (Real.log n) T a b).const_mul
      (w m * v n)
  have hs := IntervalIntegrable.sum (s := Finset.Icc 1 U)
    (fun m _ => IntervalIntegrable.sum (s := Finset.Icc 1 U) (fun n _ => hi m n))
  apply hs.congr
  intro s _
  simpa only [Finset.sum_apply] using (profile_pair_expansion w v U T s).symm

theorem integral_logarithmicFiniteExponentialEntry_pair
    (w v : ℕ → ℝ) (U : ℕ) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, logarithmicFiniteEntryProfile w U Real.exp s *
      logarithmicFiniteEntryProfile v U (fun _ => 1) (T - s)) =
      ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U,
        w a * v b * logarithmicExponentialRamp (T - Real.log (a * b : ℕ)) := by
  let term := fun (a b : ℕ) (s : ℝ) => w a * v b *
    (logarithmicExponentialEntry (Real.log a) s * logarithmicUnitEntry (Real.log b) (T - s))
  have hi (a b : ℕ) : IntervalIntegrable (term a b) volume 0 T :=
    (intervalIntegrable_logarithmicExponentialEntry_pair (Real.log a) (Real.log b) T 0 T).const_mul _
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
    integral_logarithmicExponentialEntry_pair (Real.log_natCast_nonneg a)
      (Real.log_natCast_nonneg b) T,
    Nat.cast_mul, Real.log_mul hap.ne' hbp.ne', sub_add_eq_sub_sub]

end RHTower
