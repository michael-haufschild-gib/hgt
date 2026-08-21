import Mathlib
import GaloisForLFunctions.HTGeometry.GaussianMellinMoments
import GaloisForLFunctions.HTGeometry.GammaLogIntegralEulerMascheroni

/-!
# Connes' archimedean Gaussian logarithmic moments

Formalization of Appendix II (32) and (41) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

To identify his principal value `∫'` with Weil's `Pfw` at the two archimedean places, Connes
evaluates the tempered distribution `φ(u) = -log|u|` on the self-dual Gaussian:

  real place    `⟨φ , e^{-π u²}⟩ = ½ log π + γ/2 + log 2`      (32)
  complex place `⟨φ , e^{-2π|z|²}⟩ = log 2π + γ`               (41)

with `|z|_ℂ = |z|²` and the self-dual measure `|dz ∧ dz̄| = 2 dx dy`.  He obtains them by
differentiating `∫ |u|^{-s} e^{-πu²} du = π^{(s-1)/2} Γ((1-s)/2)` and
`∫ e^{-2π|z|²}|z|^{-2ε} |dz ∧ dz̄| = (2π)^ε Γ(1-ε)` at the origin, using
`Γ'(½)/Γ(½) = -γ - 2 log 2` and `Γ'(1) = -γ`.

The proofs here follow exactly that route, but replace the differentiation under the integral sign
by mathlib's `Complex.hasDerivAt_GammaIntegral` at `s = 1/2` (real place) and by the corpus's
`HTGeometry.integral_log_mul_exp_neg_Ioi` (complex place), and then transport the result by the
substitutions `t = π u²` and `t = 2π r²`.

* `connes_gammaIntegral_deriv_half`, `connes_gamma_half_log_integral_real` - `Γ'(½) = √π(-γ-2log2)`
  in integral form.
* `connes_integral_log_mul_gaussian_Ioi`, `connes_integral_neg_log_abs_mul_gaussian` - (32).
* `connes_integral_id_log_mul_gaussian_twoPi`,
  `connes_integral_neg_logComplexModule_mul_gaussian` - (41).
* `connes_integrableOn_log_mul_gaussian`, `connes_integrableOn_pow_log_mul_gaussian`,
  `connes_integral_id_mul_gaussian_Ioi`, `connes_integral_gaussian_Ioi` - the supporting
  integrability and elementary moments.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Set Real Filter Topology

/-- `Γ'(1/2)` in integral form. -/
theorem connes_gammaIntegral_deriv_half :
    (∫ t : ℝ in Ioi 0, ((t : ℂ)) ^ ((1/2 : ℂ) - 1) * ((Real.log t : ℂ) * (Real.exp (-t) : ℂ)))
      = ((-2 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) * ((Real.sqrt π : ℝ) : ℂ) := by
  have hre : (0 : ℝ) < ((1/2 : ℂ)).re := by norm_num
  have hint := Complex.hasDerivAt_GammaIntegral hre
  have heq : Complex.GammaIntegral =ᶠ[nhds ((1/2 : ℂ))] Complex.Gamma := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hre] with s hs
    exact (Complex.Gamma_eq_integral hs).symm
  have hgam : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Ioi 0, ((t : ℂ)) ^ ((1/2 : ℂ) - 1) *
        ((Real.log t : ℂ) * (Real.exp (-t) : ℂ))) (1/2 : ℂ) :=
    hint.congr_of_eventuallyEq heq.symm
  have hGne : Complex.Gamma (1/2 : ℂ) ≠ 0 := by
    rw [Complex.Gamma_one_half_eq]
    exact Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num) |>.2
      (by simp [Real.pi_ne_zero])
  have hlog : Complex.digamma (1/2 : ℂ) = deriv Complex.Gamma (1/2) / Complex.Gamma (1/2) := by
    rw [Complex.digamma_def, logDeriv_apply]
  have hderiv : deriv Complex.Gamma (1/2 : ℂ) = Complex.digamma (1/2) * Complex.Gamma (1/2) := by
    rw [hlog]
    field_simp
  rw [← hgam.deriv, hderiv, Complex.digamma_one_half, Complex.Gamma_one_half_eq]
  have hpi : ((π : ℂ)) ^ ((1:ℂ)/2) = ((Real.sqrt π : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (le_of_lt Real.pi_pos)]
    norm_num
  rw [hpi]
  have hlog2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_ofNat, Complex.ofReal_log (by norm_num)]
  rw [hlog2]
  push_cast
  ring

/-- The Gaussian is integrable against the logarithm on the positive ray. -/
theorem connes_integrableOn_log_mul_gaussian :
    IntegrableOn (fun x : ℝ => Real.log x * Real.exp (-π * x ^ 2)) (Ioi (0 : ℝ)) := by
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hunion]
  refine IntegrableOn.union ?_ ?_
  · -- near the origin the Gaussian is bounded and `log` is integrable
    have hlog : IntegrableOn (fun x : ℝ => Real.log x) (Ioc (0:ℝ) 1) := by
      have h := (intervalIntegral.intervalIntegrable_log' (a := (0:ℝ)) (b := 1))
      exact h.1
    refine Integrable.mono' hlog.norm ?_ ?_
    · exact ((Real.continuousOn_log.mono (by intro x hx; exact ne_of_gt hx.1)).mul
        (Real.continuous_exp.comp (by fun_prop)).continuousOn).aestronglyMeasurable
        measurableSet_Ioc
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hle : Real.exp (-π * x ^ 2) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [sq_nonneg x, Real.pi_pos]
      nlinarith [abs_nonneg (Real.log x), Real.exp_pos (-π * x ^ 2)]
  · -- at infinity `|log x| ≤ x` and a polynomial times a Gaussian is integrable
    have hpoly : IntegrableOn (fun x : ℝ => x * Real.exp (-π * x ^ 2)) (Ioi (1:ℝ)) := by
      have h : IntegrableOn (fun x : ℝ => x * Real.exp (-π * x ^ 2)) (Ioi (0:ℝ)) := by
        have := integrable_rpow_mul_exp_neg_mul_sq (b := π) Real.pi_pos (s := 1)
          (by norm_num)
        have heq : (fun x : ℝ => x ^ (1:ℝ) * Real.exp (-π * x ^ 2))
            =ᵐ[volume.restrict (Ioi (0:ℝ))] fun x : ℝ => x * Real.exp (-π * x ^ 2) := by
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
          rw [Real.rpow_one]
        exact ((this.integrableOn).congr heq)
      exact h.mono_set (Ioi_subset_Ioi (by norm_num))
    refine Integrable.mono' hpoly ?_ ?_
    · exact ((Real.continuousOn_log.mono (by intro x hx; exact ne_of_gt (lt_trans one_pos hx))).mul
        (Real.continuous_exp.comp (by fun_prop)).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with x hx
      have hx1 : (1:ℝ) < x := hx
      have hxpos : (0:ℝ) < x := lt_trans one_pos hx1
      have hlogle : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hxpos).trans (by linarith)
      have hlognn : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx1)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlognn, abs_of_pos (Real.exp_pos _)]
      have := Real.exp_pos (-π * x ^ 2)
      nlinarith

/-- Real form of `Γ'(1/2)`. -/
theorem connes_gamma_half_log_integral_real :
    (∫ t : ℝ in Ioi 0, t ^ (-(1:ℝ)/2) * (Real.log t * Real.exp (-t)))
      = Real.sqrt π * (-2 * Real.log 2 - Real.eulerMascheroniConstant) := by
  have hc := connes_gammaIntegral_deriv_half
  have hcast : (∫ t : ℝ in Ioi 0, ((t : ℂ)) ^ ((1/2 : ℂ) - 1) *
        ((Real.log t : ℂ) * (Real.exp (-t) : ℂ)))
      = (((∫ t : ℝ in Ioi 0, t ^ (-(1:ℝ)/2) * (Real.log t * Real.exp (-t)) : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    have hpow : ((t : ℂ)) ^ ((1/2 : ℂ) - 1) = ((t ^ (-(1:ℝ)/2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht0.le]
      norm_num
    rw [hpow]
    push_cast
    ring
  rw [hcast] at hc
  have hreal : (∫ t : ℝ in Ioi 0, t ^ (-(1:ℝ)/2) * (Real.log t * Real.exp (-t)))
      = (-2 * Real.log 2 - Real.eulerMascheroniConstant) * Real.sqrt π := by
    exact_mod_cast hc
  rw [hreal]; ring

/-- The half-line Gaussian mass. -/
theorem connes_integral_gaussian_Ioi :
    (∫ x : ℝ in Ioi 0, Real.exp (-π * x ^ 2)) = 1 / 2 := by
  have h := GaloisForLFunctions.HTGeometry.integral_Ioi_rpow_mul_gaussian (a := 1) one_pos
  have hcongr : (∫ t : ℝ in Ioi 0, t ^ ((1:ℝ) - 1) * Real.exp (-π * t ^ 2))
      = ∫ x : ℝ in Ioi 0, Real.exp (-π * x ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [sub_self, Real.rpow_zero, one_mul]
  rw [hcongr] at h
  rw [h, Real.Gamma_one_half_eq, Real.sqrt_eq_rpow]
  have hneg : (-1 : ℝ) / 2 = -(1/2) := by norm_num
  rw [hneg, Real.rpow_neg (le_of_lt Real.pi_pos)]
  have hne : (π : ℝ) ^ ((1:ℝ)/2) ≠ 0 := by positivity
  field_simp

/-- The Gaussian is integrable on the positive ray. -/
theorem connes_integrableOn_gaussian :
    IntegrableOn (fun x : ℝ => Real.exp (-π * x ^ 2)) (Ioi (0:ℝ)) :=
  (integrable_exp_neg_mul_sq Real.pi_pos).integrableOn

/-- **Appendix II (32), half-line form.**  The logarithmic moment of the normalized Gaussian. -/
theorem connes_integral_log_mul_gaussian_Ioi :
    (∫ x : ℝ in Ioi 0, Real.log x * Real.exp (-π * x ^ 2))
      = (-2 * Real.log 2 - Real.eulerMascheroniConstant - Real.log π) / 4 := by
  set F : ℝ → ℝ := fun t => t ^ (-(1:ℝ)/2) * (Real.log t * Real.exp (-t)) with hF
  set L : ℝ := ∫ x : ℝ in Ioi 0, Real.log x * Real.exp (-π * x ^ 2) with hL
  have hsqrt : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  -- the affine substitution
  have hscale : (∫ x : ℝ in Ioi 0, F (π * x)) = π⁻¹ • ∫ x : ℝ in Ioi 0, F x := by
    have h := integral_comp_mul_left_Ioi F 0 Real.pi_pos
    simpa using h
  -- the quadratic substitution
  have hquad : (∫ x : ℝ in Ioi 0, ((|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • F (π * x ^ (2:ℝ))))
      = ∫ y : ℝ in Ioi 0, F (π * y) :=
    integral_comp_rpow_Ioi (fun s : ℝ => F (π * s)) (p := 2) two_ne_zero
  -- the pointwise identity on the positive ray
  have hpt : ∀ x ∈ Ioi (0:ℝ), ((|(2:ℝ)| * x ^ ((2:ℝ) - 1)) • F (π * x ^ (2:ℝ)))
      = (Real.sqrt π)⁻¹ * (2 * Real.log π * Real.exp (-π * x ^ 2))
        + (Real.sqrt π)⁻¹ * (4 * (Real.log x * Real.exp (-π * x ^ 2))) := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    have hx2 : x ^ (2:ℝ) = x ^ (2:ℕ) := by
      rw [← Real.rpow_natCast x 2]; norm_num
    have hprodpow : (π * x ^ (2:ℝ)) ^ (-(1:ℝ)/2)
        = (Real.sqrt π)⁻¹ * x⁻¹ := by
      rw [Real.mul_rpow (le_of_lt Real.pi_pos) (Real.rpow_nonneg hx0.le _)]
      have h1 : (π : ℝ) ^ (-(1:ℝ)/2) = (Real.sqrt π)⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (le_of_lt Real.pi_pos)]
        norm_num
      have h2 : ((x : ℝ) ^ (2:ℝ)) ^ (-(1:ℝ)/2) = x⁻¹ := by
        rw [← Real.rpow_mul hx0.le]
        norm_num
        rw [Real.rpow_neg_one]
      rw [h1, h2]
    have hlogprod : Real.log (π * x ^ (2:ℝ)) = Real.log π + 2 * Real.log x := by
      rw [Real.log_mul (ne_of_gt Real.pi_pos) (by positivity), Real.log_rpow hx0]
    have hexp : Real.exp (-(π * x ^ (2:ℝ))) = Real.exp (-π * x ^ 2) := by
      rw [hx2]; ring_nf
    simp only [hF, smul_eq_mul, hprodpow, hlogprod, hexp]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hxr : x ^ ((2:ℝ) - 1) = x := by
      norm_num
    rw [hxr]
    field_simp
    ring
  -- assemble
  have hsplit : (∫ x : ℝ in Ioi 0,
        ((Real.sqrt π)⁻¹ * (2 * Real.log π * Real.exp (-π * x ^ 2))
          + (Real.sqrt π)⁻¹ * (4 * (Real.log x * Real.exp (-π * x ^ 2)))))
      = (Real.sqrt π)⁻¹ * (2 * Real.log π) * (1/2) + (Real.sqrt π)⁻¹ * 4 * L := by
    have hg : IntegrableOn (fun x : ℝ =>
        (Real.sqrt π)⁻¹ * (2 * Real.log π * Real.exp (-π * x ^ 2))) (Ioi (0:ℝ)) :=
      (connes_integrableOn_gaussian.const_mul _).const_mul _
    have hl : IntegrableOn (fun x : ℝ =>
        (Real.sqrt π)⁻¹ * (4 * (Real.log x * Real.exp (-π * x ^ 2)))) (Ioi (0:ℝ)) :=
      (connes_integrableOn_log_mul_gaussian.const_mul _).const_mul _
    rw [integral_add hg hl, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, connes_integral_gaussian_Ioi, ← hL]
    ring
  have hkey : (∫ x : ℝ in Ioi 0, F x)
      = π * ((Real.sqrt π)⁻¹ * (2 * Real.log π) * (1/2) + (Real.sqrt π)⁻¹ * 4 * L) := by
    have h1 : (∫ y : ℝ in Ioi 0, F (π * y))
        = (Real.sqrt π)⁻¹ * (2 * Real.log π) * (1/2) + (Real.sqrt π)⁻¹ * 4 * L := by
      rw [← hquad, setIntegral_congr_fun measurableSet_Ioi hpt, hsplit]
    have h2 : π⁻¹ * (∫ x : ℝ in Ioi 0, F x)
        = (Real.sqrt π)⁻¹ * (2 * Real.log π) * (1/2) + (Real.sqrt π)⁻¹ * 4 * L := by
      rw [← h1, hscale, smul_eq_mul]
    have hπ : (π:ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    calc (∫ x : ℝ in Ioi 0, F x) = π * (π⁻¹ * ∫ x : ℝ in Ioi 0, F x) := by field_simp
      _ = π * ((Real.sqrt π)⁻¹ * (2 * Real.log π) * (1/2) + (Real.sqrt π)⁻¹ * 4 * L) := by
          rw [h2]
  rw [connes_gamma_half_log_integral_real] at hkey
  have hne : Real.sqrt π ≠ 0 := ne_of_gt hsqrt
  field_simp at hkey
  have hsq2 : Real.sqrt π ^ 2 = π := Real.sq_sqrt (le_of_lt Real.pi_pos)
  rw [hsq2] at hkey
  have hπ : (π:ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have h3 : (-(2 * Real.log 2) - Real.eulerMascheroniConstant) = Real.log π + 4 * L :=
    mul_left_cancel₀ hπ hkey
  rw [hL] at h3 ⊢
  linarith [h3]

/-- **Appendix II (32).**  `⟨-log |u| , e^{-π u²}⟩ = ½ log π + γ/2 + log 2`. -/
theorem connes_integral_neg_log_abs_mul_gaussian :
    (∫ u : ℝ, (-Real.log |u|) * Real.exp (-π * u ^ 2))
      = (1/2) * Real.log π + Real.eulerMascheroniConstant / 2 + Real.log 2 := by
  have habs : (∫ u : ℝ, (-Real.log |u|) * Real.exp (-π * u ^ 2))
      = 2 * ∫ x : ℝ in Ioi 0, (-Real.log x) * Real.exp (-π * x ^ 2) := by
    have h := integral_comp_abs (f := fun y : ℝ => (-Real.log y) * Real.exp (-π * y ^ 2))
    have hcongr : (fun u : ℝ => (-Real.log |u|) * Real.exp (-π * |u| ^ 2))
        = fun u : ℝ => (-Real.log |u|) * Real.exp (-π * u ^ 2) := by
      funext u; rw [sq_abs]
    rw [hcongr] at h
    exact h
  rw [habs]
  have hneg : (∫ x : ℝ in Ioi 0, (-Real.log x) * Real.exp (-π * x ^ 2))
      = -(∫ x : ℝ in Ioi 0, Real.log x * Real.exp (-π * x ^ 2)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
  rw [hneg, connes_integral_log_mul_gaussian_Ioi]
  ring

/-! ### The complex place -/

/-- Integrability of `x^n log x e^{-b x²}` on the positive ray. -/
theorem connes_integrableOn_pow_log_mul_gaussian {b : ℝ} (hb : 0 < b) (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * (Real.log x * Real.exp (-b * x ^ 2))) (Ioi (0:ℝ)) := by
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hunion]
  have hmeasOc : AEStronglyMeasurable
      (fun x : ℝ => x ^ n * (Real.log x * Real.exp (-b * x ^ 2)))
      (volume.restrict (Ioc (0:ℝ) 1)) :=
    (((continuous_pow n).continuousOn).mul
      ((Real.continuousOn_log.mono (by intro x hx; exact ne_of_gt hx.1)).mul
        (Real.continuous_exp.comp (by fun_prop)).continuousOn)).aestronglyMeasurable
        measurableSet_Ioc
  have hmeasIoi : AEStronglyMeasurable
      (fun x : ℝ => x ^ n * (Real.log x * Real.exp (-b * x ^ 2)))
      (volume.restrict (Ioi (1:ℝ))) :=
    (((continuous_pow n).continuousOn).mul
      ((Real.continuousOn_log.mono
          (by intro x hx; exact ne_of_gt (lt_trans one_pos hx))).mul
        (Real.continuous_exp.comp (by fun_prop)).continuousOn)).aestronglyMeasurable
        measurableSet_Ioi
  refine IntegrableOn.union ?_ ?_
  · have hlog : IntegrableOn (fun x : ℝ => Real.log x) (Ioc (0:ℝ) 1) :=
      (intervalIntegral.intervalIntegrable_log' (a := (0:ℝ)) (b := 1)).1
    refine Integrable.mono' hlog.norm hmeasOc ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    have hx0 : (0:ℝ) < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hpow : x ^ n ≤ 1 := pow_le_one₀ hx0.le hx1
    have hexp : Real.exp (-b * x ^ 2) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [sq_nonneg x]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (pow_nonneg hx0.le n)]
    calc x ^ n * (|Real.log x| * Real.exp (-b * x ^ 2))
        ≤ 1 * (|Real.log x| * 1) := by
          refine mul_le_mul hpow ?_ (by positivity) (by norm_num)
          exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ = |Real.log x| := by ring
  · have hpoly : IntegrableOn (fun x : ℝ => x ^ (n + 1) * Real.exp (-b * x ^ 2)) (Ioi (1:ℝ)) := by
      have h0 := (integrable_rpow_mul_exp_neg_mul_sq hb
        (s := ((n : ℝ) + 1))
        (by have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)).integrableOn
          (s := Ioi (1:ℝ))
      refine h0.congr ?_
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with x hx
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx
      rw [show ((n:ℝ) + 1) = (((n+1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_natCast]
    refine Integrable.mono' hpoly hmeasIoi ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with x hx
    have hx1 : (1:ℝ) < x := hx
    have hxpos : (0:ℝ) < x := lt_trans one_pos hx1
    have hlogle : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hxpos).trans (by linarith)
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx1)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hlognn,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (pow_nonneg hxpos.le n)]
    calc x ^ n * (Real.log x * Real.exp (-b * x ^ 2))
        ≤ x ^ n * (x * Real.exp (-b * x ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hxpos.le n)
          exact mul_le_mul_of_nonneg_right hlogle (Real.exp_pos _).le
      _ = x ^ (n + 1) * Real.exp (-b * x ^ 2) := by ring

/-- The first Gaussian half-moment `∫_0^∞ x e^{-b x²} dx = 1/(2b)`. -/
theorem connes_integral_id_mul_gaussian_Ioi {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x * Real.exp (-b * x ^ 2)) = 1 / (2 * b) := by
  set f : ℝ → ℝ := fun t => -Real.exp (-b * t ^ 2) / (2 * b) with hf
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt f (x * Real.exp (-b * x ^ 2)) x := by
    intro x _
    have hinner : HasDerivAt (fun t : ℝ => -b * t ^ 2) (-b * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-b))
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-b * t ^ 2))
        (Real.exp (-b * x ^ 2) * (-b * (2 * x))) x := hinner.exp
    have h2 : HasDerivAt f
        (-(Real.exp (-b * x ^ 2) * (-b * (2 * x))) / (2 * b)) x := (hexp.neg).div_const _
    have hval : -(Real.exp (-b * x ^ 2) * (-b * (2 * x))) / (2 * b)
        = x * Real.exp (-b * x ^ 2) := by
      field_simp
    rwa [hval] at h2
  have hcont : ContinuousWithinAt f (Ici (0:ℝ)) 0 := by
    refine Continuous.continuousWithinAt ?_
    exact (Real.continuous_exp.comp (by fun_prop)).neg.div_const _
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-b * x ^ 2)) (Ioi (0:ℝ)) := by
    have h0 := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (1:ℝ))
      (by norm_num)).integrableOn (s := Ioi (0:ℝ))
    refine h0.congr ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x _
    rw [Real.rpow_one]
  have htend : Filter.Tendsto f Filter.atTop (𝓝 0) := by
    have hsq : Filter.Tendsto (fun t : ℝ => b * t ^ 2) Filter.atTop Filter.atTop := by
      apply Filter.Tendsto.const_mul_atTop hb
      exact tendsto_pow_atTop (by norm_num)
    have hexp : Filter.Tendsto (fun t : ℝ => Real.exp (-(b * t ^ 2))) Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq
    have : Filter.Tendsto (fun t : ℝ => -Real.exp (-(b * t ^ 2)) / (2 * b))
        Filter.atTop (𝓝 (-0 / (2 * b))) := (hexp.neg).div_const _
    simpa [hf, neg_mul] using this
  have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  rw [this, hf]
  norm_num
  field_simp

/-- The radial logarithmic moment of the complex-place Gaussian. -/
theorem connes_integral_id_log_mul_gaussian_twoPi :
    (∫ r : ℝ in Ioi 0, r * (Real.log r * Real.exp (-(2*π) * r ^ 2)))
      = (-Real.eulerMascheroniConstant - Real.log (2*π)) / (8*π) := by
  set H : ℝ → ℝ := fun t => Real.log t * Real.exp (-t) with hH
  set M : ℝ := ∫ r : ℝ in Ioi 0, r * (Real.log r * Real.exp (-(2*π) * r ^ 2)) with hM
  have h2pi : (0:ℝ) < 2 * π := by positivity
  have hscale : (∫ x : ℝ in Ioi 0, H ((2*π) * x)) = (2*π)⁻¹ • ∫ x : ℝ in Ioi 0, H x := by
    have h := integral_comp_mul_left_Ioi H 0 h2pi
    simpa using h
  have hquad : (∫ r : ℝ in Ioi 0, ((|(2:ℝ)| * r ^ ((2:ℝ) - 1)) • H ((2*π) * r ^ (2:ℝ))))
      = ∫ y : ℝ in Ioi 0, H ((2*π) * y) :=
    integral_comp_rpow_Ioi (fun s : ℝ => H ((2*π) * s)) (p := 2) two_ne_zero
  have hpt : ∀ r ∈ Ioi (0:ℝ), ((|(2:ℝ)| * r ^ ((2:ℝ) - 1)) • H ((2*π) * r ^ (2:ℝ)))
      = 2 * Real.log (2*π) * (r * Real.exp (-(2*π) * r ^ 2))
        + 4 * (r * (Real.log r * Real.exp (-(2*π) * r ^ 2))) := by
    intro r hr
    have hr0 : (0:ℝ) < r := hr
    have hr2 : r ^ (2:ℝ) = r ^ (2:ℕ) := by
      rw [← Real.rpow_natCast r 2]; norm_num
    have hlogprod : Real.log ((2*π) * r ^ (2:ℝ)) = Real.log (2*π) + 2 * Real.log r := by
      rw [Real.log_mul (ne_of_gt h2pi) (by positivity), Real.log_rpow hr0]
    have hexp : Real.exp (-((2*π) * r ^ (2:ℝ))) = Real.exp (-(2*π) * r ^ 2) := by
      rw [hr2]; ring_nf
    simp only [hH, smul_eq_mul, hlogprod, hexp]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hxr : r ^ ((2:ℝ) - 1) = r := by norm_num
    rw [hxr]
    ring
  have hsplit : (∫ r : ℝ in Ioi 0,
        (2 * Real.log (2*π) * (r * Real.exp (-(2*π) * r ^ 2))
          + 4 * (r * (Real.log r * Real.exp (-(2*π) * r ^ 2)))))
      = 2 * Real.log (2*π) * (1 / (2 * (2*π))) + 4 * M := by
    have h1 : IntegrableOn (fun r : ℝ =>
        2 * Real.log (2*π) * (r * Real.exp (-(2*π) * r ^ 2))) (Ioi (0:ℝ)) := by
      have h0 := (integrable_rpow_mul_exp_neg_mul_sq h2pi (s := (1:ℝ))
        (by norm_num)).integrableOn (s := Ioi (0:ℝ))
      have h0' : IntegrableOn (fun r : ℝ => r * Real.exp (-(2*π) * r ^ 2)) (Ioi (0:ℝ)) := by
        refine h0.congr ?_
        filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x _
        rw [Real.rpow_one]
      exact h0'.const_mul _
    have h2 : IntegrableOn (fun r : ℝ =>
        4 * (r * (Real.log r * Real.exp (-(2*π) * r ^ 2)))) (Ioi (0:ℝ)) := by
      have h0 := connes_integrableOn_pow_log_mul_gaussian h2pi 1
      have h0' : IntegrableOn (fun r : ℝ =>
          r * (Real.log r * Real.exp (-(2*π) * r ^ 2))) (Ioi (0:ℝ)) := by
        refine h0.congr ?_
        filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x _
        rw [pow_one]
      exact h0'.const_mul _
    rw [integral_add h1 h2, integral_const_mul, integral_const_mul,
      connes_integral_id_mul_gaussian_Ioi h2pi, ← hM]
  have hkey : (∫ x : ℝ in Ioi 0, H x)
      = (2*π) * (2 * Real.log (2*π) * (1 / (2 * (2*π))) + 4 * M) := by
    have h1 : (∫ y : ℝ in Ioi 0, H ((2*π) * y))
        = 2 * Real.log (2*π) * (1 / (2 * (2*π))) + 4 * M := by
      rw [← hquad, setIntegral_congr_fun measurableSet_Ioi hpt, hsplit]
    have h2 : (2*π)⁻¹ * (∫ x : ℝ in Ioi 0, H x)
        = 2 * Real.log (2*π) * (1 / (2 * (2*π))) + 4 * M := by
      rw [← h1, hscale, smul_eq_mul]
    calc (∫ x : ℝ in Ioi 0, H x) = (2*π) * ((2*π)⁻¹ * ∫ x : ℝ in Ioi 0, H x) := by
          field_simp
      _ = (2*π) * (2 * Real.log (2*π) * (1 / (2 * (2*π))) + 4 * M) := by rw [h2]
  rw [hH] at hkey
  rw [HTGeometry.integral_log_mul_exp_neg_Ioi] at hkey
  have hpine : (π:ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  rw [hM] at hkey ⊢
  field_simp at hkey ⊢
  linarith [hkey]

/-- **Appendix II (41).**  `⟨-log |z|_ℂ , e^{-2π|z|²}⟩ = log 2π + γ`, where `|z|_ℂ = |z|²` is the
module of the local field `ℂ` and the self-dual Haar measure attached to the basic character
`α(z) = exp 2πi(z + z̄)` is `|dz ∧ dz̄| = 2 dx dy`. -/
theorem connes_integral_neg_logComplexModule_mul_gaussian :
    2 * ∫ z : ℂ, (-2 * Real.log ‖z‖) * Real.exp (-(2*π) * ‖z‖ ^ 2)
      = Real.log (2*π) + Real.eulerMascheroniConstant := by
  set f : ℝ → ℝ := fun y => (-2 * Real.log y) * Real.exp (-(2*π) * y ^ 2) with hf
  have hradial := MeasureTheory.integral_fun_norm_addHaar (volume : Measure ℂ) f
  have hball : (volume : Measure ℂ).real (Metric.ball (0:ℂ) 1) = π := by
    rw [Measure.real, Complex.volume_ball]; simp
  have hfin : Module.finrank ℝ ℂ = 2 := by simp
  rw [hball, hfin] at hradial
  have hinner : (∫ y : ℝ in Ioi 0, y ^ (2 - 1) • f y)
      = -2 * ∫ r : ℝ in Ioi 0, r * (Real.log r * Real.exp (-(2*π) * r ^ 2)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hf, smul_eq_mul]
    ring
  rw [hinner, connes_integral_id_log_mul_gaussian_twoPi] at hradial
  simp only [nsmul_eq_mul, smul_eq_mul] at hradial
  rw [hradial]
  have hpine : (π:ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

end
end GaloisForLFunctions.RHTower
