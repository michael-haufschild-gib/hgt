import GaloisForLFunctions.RHTower.Sieve.PrimeLeakageProfileVanishing

/-!
# Regularity of the exponential weight profile

The projective clock is driven by a weight `f`, and the leading prime-density term of its leakage
is the profile

`g t = (e^{f t} − 1)²`.

The prime-profile transfer needs exactly two things from `g`: a global Lipschitz constant, and a
linear bound `|g t| ≤ C t` at the origin.  Both follow from `f` being bounded, globally Lipschitz,
and vanishing at `0` — the class one gets by truncating a `C¹` weight on `[0,1]`.

The one analytic input is that `exp` is `e^F`-Lipschitz on `[−F, F]`, which comes from
`1 + x ≤ e^x` alone.
-/

namespace RHTower.Sieve

open Filter Finset
open scoped Topology

noncomputable section

/-- **`exp` is `e^F`-Lipschitz on a symmetric band.** -/
theorem abs_exp_sub_exp_le {a b F : ℝ} (ha : |a| ≤ F) (hb : |b| ≤ F) :
    |Real.exp a - Real.exp b| ≤ Real.exp F * |a - b| := by
  have key : ∀ u v : ℝ, u ≤ v → v ≤ F → Real.exp v - Real.exp u ≤ Real.exp F * (v - u) := by
    intro u v huv hvF
    have hgap : (0 : ℝ) ≤ v - u := by linarith
    have hone : 1 - (v - u) ≤ Real.exp (u - v) := by
      have := Real.add_one_le_exp (u - v)
      linarith
    have hexpv : (0 : ℝ) < Real.exp v := Real.exp_pos v
    have hsplit : Real.exp u = Real.exp v * Real.exp (u - v) := by
      rw [← Real.exp_add]
      ring_nf
    have hstep : Real.exp v - Real.exp u ≤ Real.exp v * (v - u) := by
      rw [hsplit]
      nlinarith [hexpv, hone]
    have hvle : Real.exp v ≤ Real.exp F := Real.exp_le_exp.mpr hvF
    nlinarith [hstep, hvle, hgap]
  have haF : a ≤ F := le_trans (le_abs_self a) ha
  have hbF : b ≤ F := le_trans (le_abs_self b) hb
  rcases le_total a b with hab | hab
  · rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_exp.mpr hab] :
      (0 : ℝ) ≤ Real.exp b - Real.exp a), abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]
    exact key a b hab hbF
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.mpr hab] :
      (0 : ℝ) ≤ Real.exp a - Real.exp b), abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    exact key b a hab haF

/-- The exponential weight profile. -/
def expProfile (f : ℝ → ℝ) (t : ℝ) : ℝ := (Real.exp (f t) - 1) ^ 2

theorem expProfile_nonneg (f : ℝ → ℝ) (t : ℝ) : 0 ≤ expProfile f t := sq_nonneg _

theorem continuous_expProfile {f : ℝ → ℝ} (hf : Continuous f) : Continuous (expProfile f) := by
  unfold expProfile
  fun_prop

theorem abs_exp_profile_root_le {f : ℝ → ℝ} {F : ℝ} (hfb : ∀ t, |f t| ≤ F) (t : ℝ) :
    |Real.exp (f t) - 1| ≤ Real.exp F - 1 := by
  have hFnn : 0 ≤ F := le_trans (abs_nonneg (f 0)) (hfb 0)
  have hsq := sq_exp_sub_one_le (hfb t)
  have hnn : (0 : ℝ) ≤ Real.exp F - 1 := by
    have := Real.one_le_exp hFnn
    linarith
  nlinarith [sq_abs (Real.exp (f t) - 1), abs_nonneg (Real.exp (f t) - 1), hsq, hnn]

/-- **The profile is globally Lipschitz.** -/
theorem expProfile_lipschitz {f : ℝ → ℝ} {F Lf : ℝ} (hfb : ∀ t, |f t| ≤ F)
    (hflip : ∀ s t, |f s - f t| ≤ Lf * |s - t|) (s t : ℝ) :
    |expProfile f s - expProfile f t|
      ≤ (2 * (Real.exp F - 1) * Real.exp F * Lf) * |s - t| := by
  have hFnn : 0 ≤ F := le_trans (abs_nonneg (f 0)) (hfb 0)
  have hEnn : (0 : ℝ) ≤ Real.exp F - 1 := by
    have := Real.one_le_exp hFnn
    linarith
  have hus := abs_exp_profile_root_le hfb s
  have hut := abs_exp_profile_root_le hfb t
  have hdiff : |Real.exp (f s) - Real.exp (f t)| ≤ Real.exp F * (Lf * |s - t|) := by
    refine le_trans (abs_exp_sub_exp_le (hfb s) (hfb t)) ?_
    have := hflip s t
    have hexpF : (0 : ℝ) < Real.exp F := Real.exp_pos F
    exact mul_le_mul_of_nonneg_left this hexpF.le
  have hfac : expProfile f s - expProfile f t
      = ((Real.exp (f s) - 1) + (Real.exp (f t) - 1)) *
        (Real.exp (f s) - Real.exp (f t)) := by
    unfold expProfile
    ring
  rw [hfac, abs_mul]
  have hsum : |(Real.exp (f s) - 1) + (Real.exp (f t) - 1)| ≤ 2 * (Real.exp F - 1) := by
    refine le_trans (abs_add_le _ _) ?_
    linarith
  calc |(Real.exp (f s) - 1) + (Real.exp (f t) - 1)| * |Real.exp (f s) - Real.exp (f t)|
      ≤ (2 * (Real.exp F - 1)) * (Real.exp F * (Lf * |s - t|)) := by
        exact mul_le_mul hsum hdiff (abs_nonneg _) (by linarith)
    _ = (2 * (Real.exp F - 1) * Real.exp F * Lf) * |s - t| := by ring

/-- **The profile vanishes linearly at the origin.** -/
theorem expProfile_le_linear {f : ℝ → ℝ} {F Lf : ℝ} (hfb : ∀ t, |f t| ≤ F)
    (hf0 : f 0 = 0) (hflip : ∀ s t, |f s - f t| ≤ Lf * |s - t|) {t : ℝ} (ht : 0 ≤ t) :
    |expProfile f t| ≤ max ((Real.exp F * Lf) ^ 2) ((Real.exp F - 1) ^ 2) * t := by
  have hFnn : 0 ≤ F := le_trans (abs_nonneg (f 0)) (hfb 0)
  have hEnn : (0 : ℝ) ≤ Real.exp F - 1 := by
    have := Real.one_le_exp hFnn
    linarith
  have hLnn : (0 : ℝ) ≤ Lf := by
    have h := hflip 1 0
    have habs : (0 : ℝ) ≤ |f 1 - f 0| := abs_nonneg _
    simp only [abs_one, sub_zero, mul_one] at h
    nlinarith [habs, h, abs_nonneg ((1 : ℝ) - 0)]
  have habs : |expProfile f t| = expProfile f t := abs_of_nonneg (expProfile_nonneg f t)
  rw [habs]
  rcases le_total t 1 with ht1 | ht1
  · -- near the origin the profile is quadratic
    have hroot : |Real.exp (f t) - 1| ≤ Real.exp F * (Lf * t) := by
      have hz : |f t - f 0| ≤ Lf * |t - 0| := hflip t 0
      rw [hf0, sub_zero, sub_zero, abs_of_nonneg ht] at hz
      have hstep := abs_exp_sub_exp_le (hfb t) (hfb 0)
      rw [hf0, Real.exp_zero, sub_zero] at hstep
      refine le_trans hstep ?_
      have hexpF : (0 : ℝ) < Real.exp F := Real.exp_pos F
      exact mul_le_mul_of_nonneg_left hz hexpF.le
    have hsq : expProfile f t ≤ (Real.exp F * (Lf * t)) ^ 2 := by
      unfold expProfile
      nlinarith [sq_abs (Real.exp (f t) - 1), abs_nonneg (Real.exp (f t) - 1), hroot,
        mul_nonneg (Real.exp_pos F).le (mul_nonneg hLnn ht)]
    have hquad : (Real.exp F * (Lf * t)) ^ 2 = (Real.exp F * Lf) ^ 2 * t ^ 2 := by ring
    have hle : (Real.exp F * Lf) ^ 2 * t ^ 2 ≤ (Real.exp F * Lf) ^ 2 * t := by
      have hsq0 : (0 : ℝ) ≤ (Real.exp F * Lf) ^ 2 := sq_nonneg _
      have ht2 : t ^ 2 ≤ t := by nlinarith [ht, ht1]
      nlinarith [hsq0, ht2]
    calc expProfile f t ≤ (Real.exp F * (Lf * t)) ^ 2 := hsq
      _ = (Real.exp F * Lf) ^ 2 * t ^ 2 := hquad
      _ ≤ (Real.exp F * Lf) ^ 2 * t := hle
      _ ≤ max ((Real.exp F * Lf) ^ 2) ((Real.exp F - 1) ^ 2) * t := by
          have := le_max_left ((Real.exp F * Lf) ^ 2) ((Real.exp F - 1) ^ 2)
          nlinarith [this, ht]
  · -- away from the origin the profile is simply bounded
    have hbound : expProfile f t ≤ (Real.exp F - 1) ^ 2 := by
      unfold expProfile
      exact sq_exp_sub_one_le (hfb t)
    calc expProfile f t ≤ (Real.exp F - 1) ^ 2 := hbound
      _ ≤ max ((Real.exp F * Lf) ^ 2) ((Real.exp F - 1) ^ 2) * t := by
          have hmax := le_max_right ((Real.exp F * Lf) ^ 2) ((Real.exp F - 1) ^ 2)
          have hmax0 : (0 : ℝ) ≤ max ((Real.exp F * Lf) ^ 2) ((Real.exp F - 1) ^ 2) :=
            le_trans (sq_nonneg _) (le_max_left _ _)
          nlinarith [hmax, hmax0, ht1]

end

end RHTower.Sieve
