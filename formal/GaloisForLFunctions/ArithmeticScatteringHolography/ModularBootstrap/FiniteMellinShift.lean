import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular

/-!
# Quantitative finite Mellin contours

Cauchy’s rectangle identity separates the exponential gain on the left edge
from the decay on the two horizontal edges.
-/

open Complex Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- A finite Mellin rectangle trades its leftward width for exponential decay,
with explicit vertical length and two horizontal-edge errors. -/
theorem norm_finite_mellin_shift_le {F : ℂ → ℂ} {d T L a C : ℝ} {N : ℕ}
    (hd : 0 ≤ d) (hT : 0 ≤ T) (hL : 0 ≤ L) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hF : ∀ u : ℂ, -d ≤ u.re → u.re ≤ 0 → |u.im| ≤ T → AnalyticAt ℂ F u)
    (hb : ∀ u : ℂ, -d ≤ u.re → u.re ≤ 0 → |u.im| ≤ T →
      ‖F u‖ ≤ C * (1 + |u.im|) ^ N * Real.exp (-(a * |u.im|))) :
    ‖∫ t : ℝ in (-T)..T, Complex.exp ((L : ℂ) * ((t : ℂ) * I)) * F ((t : ℂ) * I)‖ ≤
      2 * T * C * (1 + T) ^ N * Real.exp (-(d * L)) +
        2 * d * C * (1 + T) ^ N * Real.exp (-(a * T)) := by
  let G : ℂ → ℂ := fun u => Complex.exp ((L : ℂ) * u) * F u
  have hdiff : DifferentiableOn ℂ G (uIcc (-d) 0 ×ℂ uIcc (-T) T) := by
    intro u hu
    rw [uIcc_of_le (by linarith only [hd]), uIcc_of_le (by linarith only [hT])] at hu
    exact ((by fun_prop : AnalyticAt ℂ (fun u : ℂ => Complex.exp ((L : ℂ) * u)) u).mul
      (hF u hu.1.1 hu.1.2 (abs_le.mpr hu.2))).differentiableAt.differentiableWithinAt
  have hshift := RHTower.Sieve.integral_vertical_sub_eq_horizontal_rect T hdiff
  have hnorm (u : ℂ) : ‖G u‖ = Real.exp (L * u.re) * ‖F u‖ := by
    simp [G, Complex.norm_exp, Complex.mul_re]
  have hleft := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T) (f := fun t : ℝ => G ((-d : ℂ) + t * I))
    (C := C * (1 + T) ^ N * Real.exp (-(d * L))) (fun t ht => by
      rw [uIoc_of_le (by linarith only [hT])] at ht
      have habs : |t| ≤ T := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hbound := hb ((-d : ℂ) + t * I) (by simp) (by simpa using hd)
        (by simpa using habs)
      simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.I_re, mul_zero, add_zero, zero_add] at hbound
      rw [hnorm]
      have he : Real.exp (-(a * |t|)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha (abs_nonneg t)))
      have hpoly : (1 + |t|) ^ N ≤ (1 + T) ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith only [habs]) N
      have hre : ((-d : ℂ) + (t : ℂ) * I).re = -d := by simp
      rw [hre]
      calc
        _ ≤ Real.exp (L * -d) * (C * (1 + |t|) ^ N * Real.exp (-(a * |t|))) :=
          mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
        _ ≤ Real.exp (L * -d) * (C * (1 + T) ^ N * 1) := by gcongr
        _ = _ := by rw [show L * -d = -(d * L) by ring]; ring)
  have hedge (v : ℝ) (hv : |v| = T) :
      ‖∫ r : ℝ in (-d)..0, G ((r : ℂ) + v * I)‖ ≤
        (C * (1 + T) ^ N * Real.exp (-(a * T))) * d := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -d) (b := 0) (f := fun r : ℝ => G ((r : ℂ) + v * I))
      (C := C * (1 + T) ^ N * Real.exp (-(a * T))) (fun r hr => by
        rw [uIoc_of_le (by linarith only [hd])] at hr
        have hb' := hb ((r : ℂ) + v * I) (by simpa using hr.1.le)
          (by simpa using hr.2) (by simpa using hv.le)
        have hre : ((r : ℂ) + (v : ℂ) * I).re = r := by simp
        have him : |((r : ℂ) + (v : ℂ) * I).im| = T := by simpa using hv
        rw [him] at hb'
        rw [hnorm, hre]
        have he : Real.exp (L * r) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hL hr.2)
        calc
          _ ≤ 1 * (C * (1 + T) ^ N * Real.exp (-(a * T))) :=
            mul_le_mul he hb' (norm_nonneg _) (by positivity)
          _ = _ := one_mul _)
    simpa only [sub_neg_eq_add, zero_add, abs_of_nonneg hd] using hi
  have htop := hedge T (abs_of_nonneg hT)
  have hbottom := hedge (-T) (by rw [abs_neg, abs_of_nonneg hT])
  have hleft' : ‖∫ t : ℝ in (-T)..T, G ((-d : ℂ) + t * I)‖ ≤
      (C * (1 + T) ^ N * Real.exp (-(d * L))) * (2 * T) := by
    simpa only [sub_neg_eq_add, ← two_mul, abs_of_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hT)] using hleft
  simp only [Complex.ofReal_zero, Complex.ofReal_neg] at hshift hbottom
  have hdiffnorm : ‖(∫ t : ℝ in (-T)..T, G ((0 : ℂ) + t * I)) -
      ∫ t : ℝ in (-T)..T, G ((-d : ℂ) + t * I)‖ ≤
        2 * (C * (1 + T) ^ N * Real.exp (-(a * T))) * d := by
    rw [← smul_sub] at hshift
    have hn := congrArg norm hshift
    simp only [norm_smul, Complex.norm_I, one_mul] at hn
    rw [hn]
    exact (norm_sub_le _ _).trans (by linarith only [htop, hbottom])
  have htriangle := norm_add_le
    ((∫ t : ℝ in (-T)..T, G ((0 : ℂ) + t * I)) -
      ∫ t : ℝ in (-T)..T, G ((-d : ℂ) + t * I))
    (∫ t : ℝ in (-T)..T, G ((-d : ℂ) + t * I))
  rw [sub_add_cancel] at htriangle
  have htotal := htriangle.trans (add_le_add hdiffnorm hleft')
  simp only [zero_add, G] at htotal
  exact htotal.trans_eq (by ring)

#print axioms norm_finite_mellin_shift_le
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
