/-
# Böttcher tower — `bottcherCoord` has no analytic square root on the escape annulus

The base-period non-squareness: there is no single-valued analytic `h` on `escapeOpen c` with
`h² = bottcherCoord c`. Along the base circle `C(0,R)` (a closed loop in the escape annulus) the period
of `d log(h²) = d log φ_c` would be both `2πi` (`circleIntegral_logDeriv_bottcher`) and
`2·∮ d log h = 2·(2πi·ℤ)` (closed-loop FTC: `∮ d log h ∈ 2πiℤ`), i.e. `1 = 2k` — impossible. This is the
sign-monodromy obstruction (`√bottcherCoord → −√bottcherCoord` around the loop), the non-squareness
input of the Kummer route. `L` is the single-valued log of `h∘circleMap` along the loop (its existence
is the hypothesis the germ supplies).
-/
import GaloisForLFunctions.Bottcher.CoverConstruction
import GaloisForLFunctions.Bottcher.LiftPeriod

open Complex Metric MeasureTheory

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
  have hγcont : Continuous γ := by simpa [hγdef] using continuous_circleMap 0 R
  have hmem : ∀ θ : ℝ, γ θ ∈ escapeOpen c := by
    intro θ
    have : ‖γ θ‖ = R := mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere 0 hRpos.le θ)
    rw [escapeOpen, Set.mem_setOf_eq, this]; exact hR
  have hne : ∀ θ : ℝ, h (γ θ) ≠ 0 := by
    intro θ hz0
    have he : (h (γ θ)) ^ 2 = bottcherCoord c (γ θ) := hsq (hmem θ)
    rw [hz0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
    exact bottcherCoord_ne_zero c (γ θ) he.symm
  have hγclosed : γ (2 * Real.pi) = γ 0 := by
    simpa [hγdef] using (periodic_circleMap 0 R) 0
  have hγd : ∀ θ, HasDerivAt γ (deriv γ θ) θ :=
    fun θ => (hasDerivAt_circleMap 0 R θ).differentiableAt.hasDerivAt
  have hhd : ∀ θ, HasDerivAt h (deriv h (γ θ)) (γ θ) :=
    fun θ => (hh (γ θ) (hmem θ)).differentiableAt.hasDerivAt
  have hφd : ∀ θ, HasDerivAt (fun t => h (γ t)) (deriv h (γ θ) * deriv γ θ) θ :=
    fun θ => (hhd θ).comp θ (hγd θ)
  have hderivφ : ∀ θ, deriv (fun t => h (γ t)) θ = deriv h (γ θ) * deriv γ θ :=
    fun θ => (hφd θ).deriv
  -- continuity of the loop log-derivative integrand
  have hcont_dh : Continuous (fun θ => deriv h (γ θ)) :=
    (hh.deriv.continuousOn).comp_continuous hγcont hmem
  have hcont_h : Continuous (fun θ => h (γ θ)) := (hh.continuousOn).comp_continuous hγcont hmem
  have hcont_dγ : Continuous (fun θ => deriv γ θ) := by
    have : (fun θ => deriv γ θ) = fun θ => γ θ * Complex.I :=
      funext fun θ => (hasDerivAt_circleMap 0 R θ).deriv
    rw [this]; exact hγcont.mul continuous_const
  have hcontinuity : Continuous (fun θ => logDeriv h (γ θ) * deriv γ θ) := by
    have heq : (fun θ => logDeriv h (γ θ) * deriv γ θ)
        = fun θ => deriv h (γ θ) / h (γ θ) * deriv γ θ := by
      funext θ; rw [logDeriv_apply]
    rw [heq]
    exact (hcont_dh.div hcont_h hne).mul hcont_dγ
  -- the base period `∮ d log φ_c = 2πi`
  have hbase : (∮ z in C(0, R), logDeriv (bottcherCoord c) z) = 2 * (Real.pi : ℂ) * Complex.I :=
    circleIntegral_logDeriv_bottcher hR
  have hlogcong : ∀ θ : ℝ, logDeriv (bottcherCoord c) (γ θ) = logDeriv (fun w => (h w) ^ 2) (γ θ) := by
    intro θ
    have heq : bottcherCoord c =ᶠ[nhds (γ θ)] (fun w => (h w) ^ 2) :=
      Filter.eventuallyEq_of_mem ((isOpen_escapeOpen c).mem_nhds (hmem θ)) (fun w hw => (hsq hw).symm)
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.eq_of_nhds]
  have hcong : (∮ z in C(0, R), logDeriv (bottcherCoord c) z)
      = ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (fun w => (h w) ^ 2) (γ θ) * deriv γ θ := by
    show (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv γ θ • logDeriv (bottcherCoord c) (γ θ))
        = ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (fun w => (h w) ^ 2) (γ θ) * deriv γ θ
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [hlogcong θ, smul_eq_mul, mul_comm]
  have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), DifferentiableAt ℂ h (γ θ) :=
    fun θ _ => (hh (γ θ) (hmem θ)).differentiableAt
  have hsq2 : (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv (fun w => (h w) ^ 2) (γ θ) * deriv γ θ)
      = 2 * ∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv h (γ θ) * deriv γ θ :=
    pathInt_logDeriv_sq (h := h) (γ := γ) (γ' := deriv γ) hd
  have hL'' : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt L (logDeriv h (γ θ) * deriv γ θ) θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by positivity)] at hθ
    have hd2 := hL θ hθ
    rw [hderivφ θ] at hd2
    have hval : logDeriv h (γ θ) * deriv γ θ = deriv h (γ θ) * deriv γ θ / h (γ θ) := by
      rw [logDeriv_apply]; ring
    rw [hval]; exact hd2
  have hint : IntervalIntegrable (fun θ => logDeriv h (γ θ) * deriv γ θ) volume 0 (2 * Real.pi) :=
    hcontinuity.intervalIntegrable 0 (2 * Real.pi)
  have hI3 : (∫ θ in (0 : ℝ)..(2 * Real.pi), logDeriv h (γ θ) * deriv γ θ) = L (2 * Real.pi) - L 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hL'' hint
  have key : 2 * (Real.pi : ℂ) * Complex.I = 2 * (L (2 * Real.pi) - L 0) := by
    rw [← hbase, hcong, hsq2, hI3]
  -- closed-loop FTC: `exp(L(2π) − L(0)) = h(γ 2π)/h(γ 0) = 1`
  have hexp1 : Complex.exp (L (2 * Real.pi) - L 0) = 1 := by
    have hratio := exp_logDeriv_antiderivative (φ := fun t => h (γ t)) (I := L)
      (a := 0) (b := 2 * Real.pi) Real.two_pi_pos.le
      (fun t _ => hne t) (fun t _ => (hφd t).differentiableAt.hasDerivAt) (fun t ht => hL t ht)
    rw [hratio]
    show h (γ (2 * Real.pi)) / h (γ 0) = 1
    rw [hγclosed, div_self (hne 0)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp1
  rw [hk] at key
  have hne0 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hcancel : (1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
      = (2 * (k : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination key
  have h2k : (1 : ℂ) = 2 * (k : ℂ) := mul_right_cancel₀ hne0 hcancel
  have : (1 : ℤ) = 2 * k := by exact_mod_cast h2k
  omega

/-- **`bottcherCoord` has no analytic square root on the escape annulus — unconditionally.** The
single-valued log `L` of `h∘circleMap` is constructed as the indefinite integral (1D FTC), discharging
the hypothesis of `no_analytic_sqrt_bottcher`. So: there is NO analytic `h` on `escapeOpen c` with
`h² = bottcherCoord c`. This is the non-squareness fact (`a = bottcherCoord` not a square) the Kummer
route consumes, with no remaining hypothesis. -/
theorem no_analytic_sqrt_bottcher' {c : ℂ} {R : ℝ} (hR : max 2 ‖c‖ < R)
    {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (escapeOpen c))
    (hsq : Set.EqOn (fun z => (h z) ^ 2) (bottcherCoord c) (escapeOpen c)) :
    False := by
  have hRpos : 0 < R := lt_of_le_of_lt (le_trans (by norm_num) (le_max_left 2 ‖c‖)) hR
  have hγcont : Continuous (circleMap 0 R) := continuous_circleMap 0 R
  have hmem : ∀ θ : ℝ, circleMap 0 R θ ∈ escapeOpen c := by
    intro θ
    have : ‖circleMap 0 R θ‖ = R := mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere 0 hRpos.le θ)
    rw [escapeOpen, Set.mem_setOf_eq, this]; exact hR
  have hne : ∀ θ : ℝ, h (circleMap 0 R θ) ≠ 0 := by
    intro θ hz0
    have he : (h (circleMap 0 R θ)) ^ 2 = bottcherCoord c (circleMap 0 R θ) := hsq (hmem θ)
    rw [hz0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
    exact bottcherCoord_ne_zero c _ he.symm
  have hderivφ : ∀ θ, deriv (fun t => h (circleMap 0 R t)) θ
      = deriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ := fun θ =>
    ((hh (circleMap 0 R θ) (hmem θ)).differentiableAt.hasDerivAt.comp θ
      (hasDerivAt_circleMap 0 R θ).differentiableAt.hasDerivAt).deriv
  have hcont_dh : Continuous (fun θ => deriv h (circleMap 0 R θ)) :=
    (hh.deriv.continuousOn).comp_continuous hγcont hmem
  have hcont_h : Continuous (fun θ => h (circleMap 0 R θ)) :=
    (hh.continuousOn).comp_continuous hγcont hmem
  have hcont_dγ : Continuous (fun θ => deriv (circleMap 0 R) θ) := by
    have : (fun θ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I :=
      funext fun θ => (hasDerivAt_circleMap 0 R θ).deriv
    rw [this]; exact hγcont.mul continuous_const
  have hgcont : Continuous
      (fun θ => deriv (fun t => h (circleMap 0 R t)) θ / h (circleMap 0 R θ)) := by
    have heq : (fun θ => deriv (fun t => h (circleMap 0 R t)) θ / h (circleMap 0 R θ))
        = fun θ => deriv h (circleMap 0 R θ) * deriv (circleMap 0 R) θ / h (circleMap 0 R θ) :=
      funext fun θ => by rw [hderivφ θ]
    rw [heq]; exact (hcont_dh.mul hcont_dγ).div hcont_h hne
  refine no_analytic_sqrt_bottcher hR hh hsq
    (L := fun u => ∫ t in (0 : ℝ)..u,
      deriv (fun s => h (circleMap 0 R s)) t / h (circleMap 0 R t)) (fun θ _ => ?_)
  exact intervalIntegral.integral_hasDerivAt_right (hgcont.intervalIntegrable 0 θ)
    hgcont.stronglyMeasurable.stronglyMeasurableAtFilter hgcont.continuousAt

end Bottcher
