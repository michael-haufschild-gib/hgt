import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian moments with a complex exponent

`∫_0^∞ θ^λ e^{-bθ²} dθ = ½ b^{-(λ+1)/2} Γ((λ+1)/2)` for every complex `λ` with `Re λ > -1` and
every `b > 0`.  The substitution `t = θ²` reduces it to the Gamma integral.
-/

open Complex MeasureTheory Set

namespace RHTower

/-- For a positive real base, a complex power of the square is the doubled power. -/
theorem cpow_sq_ofReal {x : ℝ} (hx : 0 < x) (c : ℂ) :
    (((x ^ 2 : ℝ)) : ℂ) ^ c = ((x : ℝ) : ℂ) ^ (2 * c) := by
  have hne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [show (x ^ 2 : ℝ) = x * x by ring, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hx.le hx.le, ← Complex.cpow_add _ _ hne]
  ring_nf

/-- **The half-line Gaussian moment with a complex exponent.** -/
theorem integral_cpow_mul_exp_neg_mul_sq_Ioi {lam : ℂ} (hlam : -1 < lam.re) {b : ℝ}
    (hb : 0 < b) :
    (∫ θ in Ioi (0 : ℝ), ((θ : ℝ) : ℂ) ^ lam * Complex.exp (-((b : ℂ) * (θ : ℂ) ^ 2)))
      = 1 / 2 * (1 / (b : ℂ)) ^ ((lam + 1) / 2) * Complex.Gamma ((lam + 1) / 2) := by
  set a : ℂ := (lam + 1) / 2 with hadef
  have hare : 0 < a.re := by
    rw [hadef]
    simp only [Complex.div_re, Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    norm_num
    linarith
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun y : ℝ => ((y : ℝ) : ℂ) ^ (a - 1) * Complex.exp (-((b : ℂ) * (y : ℂ))))
    (p := 2) (by norm_num)
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hare hb] at hsub
  have hleft : (∫ x in Ioi (0 : ℝ),
      ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
        (((x ^ (2 : ℝ) : ℝ) : ℂ) ^ (a - 1) * Complex.exp (-((b : ℂ) * ((x ^ (2 : ℝ) : ℝ) : ℂ)))))
      = 2 * ∫ θ in Ioi (0 : ℝ), ((θ : ℝ) : ℂ) ^ lam
          * Complex.exp (-((b : ℂ) * (θ : ℂ) ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hxsq : (x : ℝ) ^ (2 : ℝ) = x ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast x 2]
      norm_num
    have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    rw [hxsq, cpow_sq_ofReal hx0]
    have hpow : ((x : ℝ) : ℂ) ^ (2 * (a - 1)) = ((x : ℝ) : ℂ) ^ (lam - 1) := by
      congr 1
      rw [hadef]
      ring
    rw [hpow]
    have hcast : (((x ^ (2 : ℕ) : ℝ)) : ℂ) = ((x : ℝ) : ℂ) ^ (2 : ℕ) := by push_cast; ring
    rw [hcast]
    have hsmul : ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
        (((x : ℝ) : ℂ) ^ (lam - 1) * Complex.exp (-((b : ℂ) * ((x : ℝ) : ℂ) ^ (2 : ℕ))))
        = ((2 : ℂ) * ((x : ℝ) : ℂ))
          * (((x : ℝ) : ℂ) ^ (lam - 1) * Complex.exp (-((b : ℂ) * ((x : ℝ) : ℂ) ^ (2 : ℕ)))) := by
      rw [Complex.real_smul]
      congr 1
      push_cast
      norm_num
    rw [hsmul]
    have hxlam : ((x : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (lam - 1) = ((x : ℝ) : ℂ) ^ lam := by
      nth_rewrite 1 [← Complex.cpow_one ((x : ℝ) : ℂ)]
      rw [← Complex.cpow_add _ _ hxne]
      ring_nf
    calc ((2 : ℂ) * ((x : ℝ) : ℂ))
        * (((x : ℝ) : ℂ) ^ (lam - 1) * Complex.exp (-((b : ℂ) * ((x : ℝ) : ℂ) ^ (2 : ℕ))))
        = 2 * (((x : ℝ) : ℂ) * ((x : ℝ) : ℂ) ^ (lam - 1))
            * Complex.exp (-((b : ℂ) * ((x : ℝ) : ℂ) ^ (2 : ℕ))) := by ring
      _ = 2 * (((x : ℝ) : ℂ) ^ lam * Complex.exp (-((b : ℂ) * ((x : ℝ) : ℂ) ^ (2 : ℕ)))) := by
          rw [hxlam]; ring
  rw [hleft] at hsub
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  field_simp at hsub ⊢
  linear_combination hsub

/-- **The real half-line Gaussian moment.** -/
theorem integral_rpow_mul_exp_neg_mul_sq_Ioi {sig : ℝ} (hsig : -1 < sig) {b : ℝ} (hb : 0 < b) :
    (∫ θ in Ioi (0 : ℝ), θ ^ sig * Real.exp (-b * θ ^ 2))
      = 1 / 2 * (1 / b) ^ ((sig + 1) / 2) * Real.Gamma ((sig + 1) / 2) := by
  have hcx := integral_cpow_mul_exp_neg_mul_sq_Ioi (lam := (sig : ℂ)) (by simpa using hsig) hb
  have hint : (∫ θ in Ioi (0 : ℝ), ((θ : ℝ) : ℂ) ^ ((sig : ℝ) : ℂ)
        * Complex.exp (-((b : ℂ) * (θ : ℂ) ^ 2)))
      = ((∫ θ in Ioi (0 : ℝ), θ ^ sig * Real.exp (-b * θ ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [Complex.ofReal_mul, ← Complex.ofReal_cpow hx0.le, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  rw [hint] at hcx
  have hgam : Complex.Gamma (((sig : ℂ) + 1) / 2) = ((Real.Gamma ((sig + 1) / 2) : ℝ) : ℂ) := by
    rw [show ((sig : ℂ) + 1) / 2 = ((((sig + 1) / 2 : ℝ)) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal]
  have hpow : (1 / (b : ℂ)) ^ (((sig : ℂ) + 1) / 2)
      = (((1 / b) ^ ((sig + 1) / 2) : ℝ) : ℂ) := by
    rw [show (1 / (b : ℂ)) = (((1 / b : ℝ)) : ℂ) by push_cast; ring,
      show ((sig : ℂ) + 1) / 2 = ((((sig + 1) / 2 : ℝ)) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by positivity)]
  rw [hgam, hpow] at hcx
  have : ((∫ θ in Ioi (0 : ℝ), θ ^ sig * Real.exp (-b * θ ^ 2) : ℝ) : ℂ)
      = ((1 / 2 * (1 / b) ^ ((sig + 1) / 2) * Real.Gamma ((sig + 1) / 2) : ℝ) : ℂ) := by
    rw [hcx]
    push_cast
    ring
  exact_mod_cast this

/-- **The Gaussian tail past a threshold is exponentially small.** -/
theorem norm_integral_cpow_mul_exp_neg_mul_sq_Ioi_le {lam : ℂ} (hlam : -1 < lam.re) {b c : ℝ}
    (hb : 0 < b) (hc : 0 ≤ c) :
    ‖∫ θ in Ioi c, ((θ : ℝ) : ℂ) ^ lam * Complex.exp (-((b : ℂ) * (θ : ℂ) ^ 2))‖
      ≤ Real.exp (-(b * c ^ 2 / 2))
        * (1 / 2 * (2 / b) ^ ((lam.re + 1) / 2) * Real.Gamma ((lam.re + 1) / 2)) := by
  have hb2 : 0 < b / 2 := by positivity
  have hnorm : ∀ θ : ℝ, θ ∈ Ioi c →
      ‖((θ : ℝ) : ℂ) ^ lam * Complex.exp (-((b : ℂ) * (θ : ℂ) ^ 2))‖
        = θ ^ lam.re * Real.exp (-b * θ ^ 2) := by
    intro θ hθ
    have hθ0 : (0 : ℝ) < θ := lt_of_le_of_lt hc hθ
    have hsq : ((θ : ℝ) : ℂ) ^ 2 = (((θ ^ 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hθ0, Complex.norm_exp, hsq,
      ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re, neg_mul]
  have hstep1 : ‖∫ θ in Ioi c, ((θ : ℝ) : ℂ) ^ lam * Complex.exp (-((b : ℂ) * (θ : ℂ) ^ 2))‖
      ≤ ∫ θ in Ioi c, θ ^ lam.re * Real.exp (-b * θ ^ 2) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    exact le_of_eq (setIntegral_congr_fun measurableSet_Ioi hnorm)
  refine hstep1.trans ?_
  -- pointwise domination
  have hdom : ∀ θ : ℝ, θ ∈ Ioi c →
      θ ^ lam.re * Real.exp (-b * θ ^ 2)
        ≤ Real.exp (-(b * c ^ 2 / 2)) * (θ ^ lam.re * Real.exp (-(b / 2) * θ ^ 2)) := by
    intro θ hθ
    have hθ0 : (0 : ℝ) < θ := lt_of_le_of_lt hc hθ
    have hcθ' : c < θ := hθ
    have hcθ : c ^ 2 ≤ θ ^ 2 := by nlinarith
    have hexp : Real.exp (-b * θ ^ 2)
        ≤ Real.exp (-(b * c ^ 2 / 2)) * Real.exp (-(b / 2) * θ ^ 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hpos : (0 : ℝ) ≤ θ ^ lam.re := Real.rpow_nonneg hθ0.le _
    calc θ ^ lam.re * Real.exp (-b * θ ^ 2)
        ≤ θ ^ lam.re * (Real.exp (-(b * c ^ 2 / 2)) * Real.exp (-(b / 2) * θ ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp hpos
      _ = Real.exp (-(b * c ^ 2 / 2)) * (θ ^ lam.re * Real.exp (-(b / 2) * θ ^ 2)) := by ring
  have hint1 : IntegrableOn (fun θ : ℝ => θ ^ lam.re * Real.exp (-b * θ ^ 2)) (Ioi c) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq hb hlam).mono_set ?_
    exact Set.Ioi_subset_Ioi hc
  have hint2 : IntegrableOn
      (fun θ : ℝ => Real.exp (-(b * c ^ 2 / 2)) * (θ ^ lam.re * Real.exp (-(b / 2) * θ ^ 2)))
      (Ioi c) := by
    refine (((integrableOn_rpow_mul_exp_neg_mul_sq hb2 hlam).mono_set
      (Set.Ioi_subset_Ioi hc)).const_mul _)
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Ioi hdom
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  have hsub : (∫ θ in Ioi c, θ ^ lam.re * Real.exp (-(b / 2) * θ ^ 2))
      ≤ ∫ θ in Ioi (0 : ℝ), θ ^ lam.re * Real.exp (-(b / 2) * θ ^ 2) := by
    refine setIntegral_mono_set ((integrableOn_rpow_mul_exp_neg_mul_sq hb2 hlam)) ?_ ?_
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with θ hθ
      have hθ0 : (0 : ℝ) < θ := hθ
      exact mul_nonneg (Real.rpow_nonneg hθ0.le _) (Real.exp_nonneg _)
    · exact Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hc)
  refine hsub.trans ?_
  rw [integral_rpow_mul_exp_neg_mul_sq_Ioi hlam hb2]
  have : (1 : ℝ) / (b / 2) = 2 / b := by rw [one_div_div]
  rw [this]

/-- The complex Gaussian moment integrand is continuous on the open half line. -/
theorem continuousOn_cpow_mul_exp_neg_mul_sq (lam : ℂ) (b : ℝ) :
    ContinuousOn (fun θ : ℝ => ((θ : ℝ) : ℂ) ^ lam * Complex.exp (-((b : ℂ) * (θ : ℂ) ^ 2)))
      (Ioi 0) := by
  refine ContinuousOn.mul ?_ (by fun_prop)
  intro θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ
  have hslit : ((θ : ℝ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (by simpa using hθ0)
  exact ((continuousAt_cpow_const hslit).comp
    (Complex.continuous_ofReal.continuousAt)).continuousWithinAt

/-- The complex Gaussian moment integrand is integrable on the half line. -/
theorem integrableOn_cpow_mul_exp_neg_mul_sq_Ioi {lam : ℂ} (hlam : -1 < lam.re) {b : ℝ}
    (hb : 0 < b) :
    IntegrableOn (fun θ : ℝ => ((θ : ℝ) : ℂ) ^ lam * Complex.exp (-((b : ℂ) * (θ : ℂ) ^ 2)))
      (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => ((θ : ℝ) : ℂ) ^ lam * Complex.exp (-((b : ℂ) * (θ : ℂ) ^ 2)))
      (volume.restrict (Ioi 0)) :=
    (continuousOn_cpow_mul_exp_neg_mul_sq lam b).aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul_sq hb hlam) hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ
  have hsq : ((θ : ℝ) : ℂ) ^ 2 = (((θ ^ 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hθ0, Complex.norm_exp, hsq,
    ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re, neg_mul]

end RHTower
