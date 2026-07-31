import Mathlib
import GaloisForLFunctions.RHTower.MFreeLadder

/-!
# The bounded-exponent positive dilation operator and its Mellin multiplier

The positive dilation operator supported on the `m`-free integers,

`(Z_m g)(x) = ∑_{n : m-free} g(n x)`,

acts on Mellin transforms by the `m`-free Dirichlet series.  On the absolute-convergence
half-plane the term-by-term Mellin transform is legitimate, because the ray integral of the
`n`-th term is `n^{-σ}` times that of the original, and

`ℳ(Z_m g)(s) = (ζ(s)/ζ(ms)) · ℳg(s)`   for `Re s > 1`.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Classical

namespace RHTower

/-- Positive dilation sum restricted to the `m`-free integers. -/
noncomputable def mFreeDilationSum (m : ℕ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, if MFree m n then g (n * x) else 0

theorem mFree_ne_zero {m n : ℕ} (h : MFree m n) : n ≠ 0 := by
  rintro rfl
  exact not_mFree_zero m h

/-- The ray norm integral of a dilated term rescales by `n^{-σ}`. -/
theorem integral_norm_cpow_smul_comp_mul {g : ℝ → ℂ} {s : ℂ} {n : ℕ} (hn : n ≠ 0) :
    (∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) • g ((n : ℝ) * x)‖)
      = (n : ℝ) ^ (-s.re) * ∫ x in Ioi (0 : ℝ), x ^ (s.re - 1) * ‖g x‖ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hstep : ∀ x ∈ Ioi (0 : ℝ), ‖(x : ℂ) ^ (s - 1) • g ((n : ℝ) * x)‖
      = (n : ℝ) ^ (1 - s.re) * (((n : ℝ) * x) ^ (s.re - 1) * ‖g ((n : ℝ) * x)‖) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, sub_re, one_re,
      Real.mul_rpow hn0.le hx0.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hn0]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hstep, integral_const_mul]
  have hcv := integral_comp_mul_left_Ioi (fun u : ℝ => u ^ (s.re - 1) * ‖g u‖) 0 hn0
  rw [mul_zero] at hcv
  rw [hcv, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one ((n : ℝ)), ← Real.rpow_add hn0,
    show (1 - s.re + -1 : ℝ) = -s.re from by ring]

/-- **Mellin multiplier of the bounded-exponent dilation operator.** -/
theorem mellin_mFreeDilationSum {m : ℕ} (hm : m ≠ 0) {g : ℝ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (hgm : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    (hg : IntegrableOn (fun x : ℝ => x ^ (s.re - 1) * ‖g x‖) (Ioi 0)) :
    mellin (mFreeDilationSum m g) s
      = riemannZeta s / riemannZeta ((m : ℂ) * s) * mellin g s := by
  have hconv : MellinConvergent g s :=
    (mellin_convergent_iff_norm (subset_refl _) measurableSet_Ioi hgm).mpr hg
  set F : ℕ → ℝ → ℂ := fun n x => (x : ℂ) ^ (s - 1) • (if MFree m n then g ((n : ℝ) * x) else 0)
    with hF
  have hFint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := by
    intro n
    by_cases h : MFree m n
    · have hn0 : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (mFree_ne_zero h)
      have hcomp : MellinConvergent (fun t : ℝ => g ((n : ℝ) * t)) s :=
        (MellinConvergent.comp_mul_left hn0).mpr hconv
      have : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) • g ((n : ℝ) * x)) (Ioi 0) := hcomp
      exact this.congr_fun (fun x _ => by simp [hF, h]) measurableSet_Ioi
    · have : F n = fun _ : ℝ => (0 : ℂ) := by
        funext x
        simp [hF, h]
      rw [this]
      exact integrable_zero _ _ _
  have hnorm : ∀ n : ℕ, (∫ x in Ioi (0 : ℝ), ‖F n x‖)
      = if MFree m n then (n : ℝ) ^ (-s.re) *
          (∫ x in Ioi (0 : ℝ), x ^ (s.re - 1) * ‖g x‖) else 0 := by
    intro n
    by_cases h : MFree m n
    · rw [if_pos h]
      rw [← integral_norm_cpow_smul_comp_mul (g := g) (s := s) (mFree_ne_zero h)]
      exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by simp [hF, h])
    · rw [if_neg h]
      have : ∀ x ∈ Ioi (0 : ℝ), ‖F n x‖ = 0 := by
        intro x _
        simp [hF, h]
      rw [setIntegral_congr_fun measurableSet_Ioi this]
      simp
  have hsummable : Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖F n x‖ := by
    have hbase : Summable fun n : ℕ => (n : ℝ) ^ (-s.re) := by
      rw [Real.summable_nat_rpow]
      linarith
    have hI : (0 : ℝ) ≤ ∫ x in Ioi (0 : ℝ), x ^ (s.re - 1) * ‖g x‖ :=
      setIntegral_nonneg measurableSet_Ioi (fun x hx => by
        have hx0 : (0 : ℝ) < x := hx
        exact mul_nonneg (Real.rpow_nonneg hx0.le _) (norm_nonneg _))
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (hbase.mul_right (∫ x in Ioi (0 : ℝ), x ^ (s.re - 1) * ‖g x‖))
    · exact integral_nonneg (fun x => norm_nonneg _)
    · rw [hnorm n]
      split_ifs with h
      · exact le_refl _
      · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hI
  have hsum := hasSum_integral_of_summable_integral_norm hFint hsummable
  have hpoint : ∀ x : ℝ, (∑' n : ℕ, F n x) = (x : ℂ) ^ (s - 1) • mFreeDilationSum m g x := by
    intro x
    simp only [hF, smul_eq_mul, mFreeDilationSum]
    exact tsum_mul_left
  have hterm : ∀ n : ℕ, (∫ x in Ioi (0 : ℝ), F n x)
      = if MFree m n then ((n : ℂ) ^ (-s)) * mellin g s else 0 := by
    intro n
    by_cases h : MFree m n
    · rw [if_pos h]
      have hn0 : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (mFree_ne_zero h)
      have hcongr : (∫ x in Ioi (0 : ℝ), F n x)
          = mellin (fun t : ℝ => g ((n : ℝ) * t)) s := by
        rw [mellin]
        exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by simp [hF, h])
      rw [hcongr, mellin_comp_mul_left g s hn0, smul_eq_mul, Complex.ofReal_natCast]
    · rw [if_neg h]
      have : ∀ x ∈ Ioi (0 : ℝ), F n x = 0 := by
        intro x _
        simp [hF, h]
      rw [setIntegral_congr_fun measurableSet_Ioi this]
      simp
  have hmel : (∫ x in Ioi (0 : ℝ), (∑' n : ℕ, F n x)) = mellin (mFreeDilationSum m g) s := by
    rw [mellin]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpoint x)
  rw [← hmel, ← hsum.tsum_eq]
  simp only [hterm]
  have hfactor : ∀ n : ℕ, (if MFree m n then ((n : ℂ) ^ (-s)) * mellin g s else 0)
      = (if MFree m n then 1 / (n : ℂ) ^ s else 0) * mellin g s := by
    intro n
    by_cases h : MFree m n
    · rw [if_pos h, if_pos h, Complex.cpow_neg, one_div]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [tsum_congr hfactor, tsum_mul_right, tsum_mFree_cpow hm hs]

end RHTower
