/-
# Böttcher tower — `bottcherCoord` has no analytic square root on the escape annulus

The base-period non-squareness: there is no single-valued analytic `h` on `escapeOpen c` with
`h² = bottcherCoord c`. Along the base circle `C(0,R)` (a closed loop in the escape annulus) the period
of `d log(h²) = d log φ_c` would be both `2πi` (`circleIntegral_logDeriv_bottcher`) and
`2·∮ d log h = 2·(2πi·ℤ)` (closed-loop FTC: `∮ d log h ∈ 2πiℤ`), i.e. `1 = 2k` — impossible. This is the
sign-monodromy obstruction (`√bottcherCoord → −√bottcherCoord` around the loop), the non-squareness
input of the Kummer route. `L` is the single-valued log of `h∘circleMap` (its existence is the
hypothesis the germ provides).
-/
import GaloisForLFunctions.Bottcher.CoverConstruction
import GaloisForLFunctions.Bottcher.LiftPeriod

open Complex Metric

namespace Bottcher

theorem no_analytic_sqrt_bottcher {c : ℂ} {R : ℝ} (hR : max 2 ‖c‖ < R)
    {h : ℂ → ℂ} {L : ℝ → ℂ}
    (hh : AnalyticOnNhd ℂ h (escapeOpen c))
    (hsq : Set.EqOn (fun z => (h z) ^ 2) (bottcherCoord c) (escapeOpen c))
    (hL : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        HasDerivAt L (deriv (fun t => h (circleMap 0 R t)) θ / h (circleMap 0 R θ)) θ) :
    False := by
  have hRpos : 0 < R := lt_of_le_of_lt (le_trans (by norm_num) (le_max_left 2 ‖c‖)) hR
  set γ : ℝ → ℂ := circleMap 0 R with hγdef
  have hmem : ∀ θ : ℝ, γ θ ∈ escapeOpen c := by
    intro θ
    have : ‖γ θ‖ = R := mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere 0 hRpos.le θ)
    rw [escapeOpen, Set.mem_setOf_eq, this]; exact hR
  have hne : ∀ θ : ℝ, h (γ θ) ≠ 0 := by
    intro θ hz0
    have he := hsq (hmem θ)
    rw [hz0] at he
    exact bottcherCoord_ne_zero c (γ θ) (by simpa using he.symm)
  set φ : ℝ → ℂ := fun θ => h (γ θ) with hφ
  have hγd : ∀ θ, HasDerivAt γ (deriv γ θ) θ :=
    fun θ => (hasDerivAt_circleMap 0 R θ).differentiableAt.hasDerivAt
  have hhd : ∀ θ, HasDerivAt h (deriv h (γ θ)) (γ θ) :=
    fun θ => (hh (γ θ) (hmem θ)).differentiableAt.hasDerivAt
  have hφd : ∀ θ, HasDerivAt φ (deriv h (γ θ) * deriv γ θ) θ :=
    fun θ => (hhd θ).comp θ (hγd θ)
  have hderivφ : ∀ θ, deriv (fun t => h (γ t)) θ = deriv h (γ θ) * deriv γ θ :=
    fun θ => (hφd θ).deriv
  have hφclosed : φ (2 * Real.pi) = φ 0 := by
    simp only [hφ]
    have : γ (2 * Real.pi) = γ 0 := by
      have hp := periodic_circleMap 0 R 0
      simpa [hγdef] using hp
    rw [this]
  -- continuity of the loop log-derivative integrand
  have hcont_dh : Continuous (fun θ => deriv h (γ θ)) :=
    (hh.deriv.continuousOn).comp_continuous (by simpa [hγdef] using continuous_circleMap 0 R) hmem
  have hcont_h : Continuous (fun θ => h (γ θ)) :=
    (hh.continuousOn).comp_continuous (by simpa [hγdef] using continuous_circleMap 0 R) hmem
  have hcont_dγ : Continuous (fun θ => deriv γ θ) := by
    have : (fun θ => deriv γ θ) = fun θ => γ θ * Complex.I :=
      funext fun θ => (hasDerivAt_circleMap 0 R θ).deriv
    rw [this]; exact ((by simpa [hγdef] using continuous_circleMap 0 R : Continuous γ)).mul
      continuous_const
  have hcontinuity : Continuous (fun θ => logDeriv h (γ θ) * deriv γ θ) := by
    have heq : (fun θ => logDeriv h (γ θ) * deriv γ θ)
        = fun θ => deriv h (γ θ) / h (γ θ) * deriv γ θ := by
      funext θ; rw [logDeriv_apply]
    rw [heq]
    exact (hcont_dh.div hcont_h hne).mul hcont_dγ
  -- the base period
  have hbase : (∮ z in C(0, R), logDeriv (bottcherCoord c) z) = 2 * (Real.pi : ℂ) * Complex.I :=
    circleIntegral_logDeriv_bottcher hR
  -- pointwise: on the circle `logDeriv φ_c = logDeriv (h²)`
  have hlogcong : ∀ θ : ℝ, logDeriv (bottcherCoord c) (γ θ) = logDeriv (fun w => (h w) ^ 2) (γ θ) := by
    intro θ
    have heq : bottcherCoord c =ᶠ[nhds (γ θ)] (fun w => (h w) ^ 2) :=
      Filter.eventuallyEq_of_mem ((isOpen_escapeOpen c).mem_nhds (hmem θ)) (fun w hw => (hsq hw).symm)
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  -- rewrite the contour integral as the squared-loop integral
  have hcong : (∮ z in C(0, R), logDeriv (bottcherCoord c) z)
      = ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (fun w => (h w) ^ 2) (γ θ) * deriv γ θ := by
    show (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv γ θ • logDeriv (bottcherCoord c) (γ θ))
        = ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (fun w => (h w) ^ 2) (γ θ) * deriv γ θ
    apply intervalIntegral.integral_congr
    intro θ _
    rw [hlogcong θ, smul_eq_mul, mul_comm]
  -- period halving for the square
  have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), DifferentiableAt ℂ h (γ θ) :=
    fun θ _ => (hh (γ θ) (hmem θ)).differentiableAt
  have hsq2 : (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (fun w => (h w) ^ 2) (γ θ) * deriv γ θ)
      = 2 * ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv h (γ θ) * deriv γ θ :=
    pathInt_logDeriv_sq (h := h) (γ := γ) (γ' := deriv γ) hd
  -- FTC: the loop log-derivative integral is `L(2π) − L(0)`
  have hL'' : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt L (logDeriv h (γ θ) * deriv γ θ) θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by positivity)] at hθ
    have hd2 := hL θ hθ
    rw [hderivφ θ] at hd2
    rwa [logDeriv_apply, div_mul_eq_mul_div]
  have hint : IntervalIntegrable (fun θ => logDeriv h (γ θ) * deriv γ θ) volume 0 (2 * Real.pi) :=
    hcontinuity.intervalIntegrable 0 (2 * Real.pi)
  have hI3 : (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv h (γ θ) * deriv γ θ) = L (2 * Real.pi) - L 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hL'' hint
  -- combine: `2πi = 2·(L(2π) − L(0))`
  have key : 2 * (Real.pi : ℂ) * Complex.I = 2 * (L (2 * Real.pi) - L 0) := by
    rw [← hbase, hcong, hsq2, hI3]
  -- closed-loop FTC: `exp(L(2π) − L(0)) = φ(2π)/φ(0) = 1`
  have hexp1 : Complex.exp (L (2 * Real.pi) - L 0) = 1 := by
    rw [exp_logDeriv_antiderivative (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
      (fun t _ => hne t) (fun t _ => (hφd t).differentiableAt.hasDerivAt)
      (fun t ht => hL t ht), hφclosed, div_self (hne 0)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp1
  rw [hk] at key
  have hne0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hc : (2 * (Real.pi : ℂ) * Complex.I) * 1 = (2 * (Real.pi : ℂ) * Complex.I) * (2 * (k : ℂ)) := by
    rw [mul_one, key]; ring
  have h2k : (1 : ℂ) = 2 * (k : ℂ) := mul_left_cancel₀ hne0 hc
  have : (1 : ℤ) = 2 * k := by exact_mod_cast h2k
  omega

end Bottcher
