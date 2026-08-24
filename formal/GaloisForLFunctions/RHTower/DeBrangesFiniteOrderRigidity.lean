import GaloisForLFunctions.RHTower.DeBrangesHTGaugeSaturation
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.HTGeometry.FiniteOrderEntireQuotient
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicCancellation
import GaloisForLFunctions.HTGeometry.FiniteOrderZeroFreeDifferentialAlgebraic
import GaloisForLFunctions.HTGeometry.EntireQuotientNormalForm

namespace GaloisForLFunctions.RHTower

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section

theorem suzukiHermiteBiehler_ne_zero_upper {E : ℂ → ℂ}
    (hE : SuzukiHermiteBiehler E) {z : ℂ} (hz : 0 < z.im) : E z ≠ 0 := by
  intro hzero
  have hlt := hE z hz
  rw [hzero, norm_zero] at hlt
  exact (not_lt_of_ge (norm_nonneg _)) hlt

theorem analyticOrderAt_suzukiEntireSharp_conj {E : ℂ → ℂ}
    (hE : Differentiable ℂ E) (z : ℂ) :
    analyticOrderAt (suzukiEntireSharp E) (star z) = analyticOrderAt E z := by
  change analyticOrderAt (fun w => star (E (star w))) (star z) = analyticOrderAt E z
  exact _root_.RHTower.analyticOrderAt_conj_conj hE z

theorem analyticOrderAt_suzukiEntireSharp_eq_of_innerQuotient_eq_upper
    {E₁ E₂ : ℂ → ℂ}
    (hE₁ : AnalyticOnNhd ℂ E₁ Set.univ) (hE₂ : AnalyticOnNhd ℂ E₂ Set.univ)
    (hHB₁ : SuzukiHermiteBiehler E₁) (hHB₂ : SuzukiHermiteBiehler E₂)
    (hTheta : ∀ z, suzukiEntireSharp E₁ z / E₁ z =
      suzukiEntireSharp E₂ z / E₂ z)
    {w : ℂ} (hw : 0 < w.im) :
    analyticOrderAt (suzukiEntireSharp E₁) w =
      analyticOrderAt (suzukiEntireSharp E₂) w := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hmem : {z : ℂ | 0 < z.im} ∈ 𝓝 w := hopen.mem_nhds hw
  have hcross :
      (suzukiEntireSharp E₁ * E₂) =ᶠ[𝓝 w]
        (suzukiEntireSharp E₂ * E₁) := by
    filter_upwards [hmem] with z hz
    change suzukiEntireSharp E₁ z * E₂ z = suzukiEntireSharp E₂ z * E₁ z
    exact (div_eq_div_iff (suzukiHermiteBiehler_ne_zero_upper hHB₁ hz)
      (suzukiHermiteBiehler_ne_zero_upper hHB₂ hz)).mp (hTheta z)
  have hord := analyticOrderAt_congr hcross
  have hE₁sharp := analyticOnNhd_suzukiEntireSharp hE₁
  have hE₂sharp := analyticOnNhd_suzukiEntireSharp hE₂
  rw [analyticOrderAt_mul (hE₁sharp w (Set.mem_univ w)) (hE₂ w (Set.mem_univ w)),
    analyticOrderAt_mul (hE₂sharp w (Set.mem_univ w)) (hE₁ w (Set.mem_univ w)),
    (hE₂ w (Set.mem_univ w)).analyticOrderAt_eq_zero.mpr
      (suzukiHermiteBiehler_ne_zero_upper hHB₂ hw),
    (hE₁ w (Set.mem_univ w)).analyticOrderAt_eq_zero.mpr
      (suzukiHermiteBiehler_ne_zero_upper hHB₁ hw), add_zero] at hord
  simpa using hord

/-- Equal de Branges inner quotients determine the complete divisor when both HB functions have
no real zeros. -/
theorem analyticOrderAt_eq_of_deBrangesInnerQuotient_eq
    {E₁ E₂ : ℂ → ℂ}
    (hE₁ : AnalyticOnNhd ℂ E₁ Set.univ) (hE₂ : AnalyticOnNhd ℂ E₂ Set.univ)
    (hHB₁ : SuzukiHermiteBiehler E₁) (hHB₂ : SuzukiHermiteBiehler E₂)
    (hreal₁ : ∀ x : ℝ, E₁ (x : ℂ) ≠ 0) (hreal₂ : ∀ x : ℝ, E₂ (x : ℂ) ≠ 0)
    (hTheta : ∀ z, suzukiEntireSharp E₁ z / E₁ z =
      suzukiEntireSharp E₂ z / E₂ z) :
    ∀ z, analyticOrderAt E₁ z = analyticOrderAt E₂ z := by
  have hE₁diff : Differentiable ℂ E₁ := by
    rwa [Complex.analyticOnNhd_univ_iff_differentiable] at hE₁
  have hE₂diff : Differentiable ℂ E₂ := by
    rwa [Complex.analyticOnNhd_univ_iff_differentiable] at hE₂
  intro z
  rcases lt_trichotomy z.im 0 with hzlower | hzreal | hzupper
  · have hstarupper : 0 < (star z).im := by simp; linarith
    have hsharp := analyticOrderAt_suzukiEntireSharp_eq_of_innerQuotient_eq_upper
      hE₁ hE₂ hHB₁ hHB₂ hTheta hstarupper
    rw [analyticOrderAt_suzukiEntireSharp_conj hE₁diff,
      analyticOrderAt_suzukiEntireSharp_conj hE₂diff] at hsharp
    exact hsharp
  · have hzof : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hzreal
    rw [(hE₁ z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr (by
        rw [hzof]; exact hreal₁ z.re),
      (hE₂ z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr (by
        rw [hzof]; exact hreal₂ z.re)]
  · rw [(hE₁ z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr
        (suzukiHermiteBiehler_ne_zero_upper hHB₁ hzupper),
      (hE₂ z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr
        (suzukiHermiteBiehler_ne_zero_upper hHB₂ hzupper)]

/-- Complete finite-order rigidity package for two exact de Branges representatives. -/
structure FiniteOrderDeBrangesRigidityData (E₁ E₂ : ℂ → ℂ) where
  gauge : ℂ → ℂ
  exponent : Polynomial ℂ
  gauge_analytic : AnalyticOnNhd ℂ gauge Set.univ
  gauge_zeroFree : ZeroFreeGauge gauge
  factor : ∀ z, E₁ z = gauge z * E₂ z
  gauge_eq_expPolynomial : ∀ z, gauge z = Complex.exp (exponent.eval z)
  gauge_schwarzReal : SchwarzRealGauge gauge
  differentialType_iff : DifferentiallyAlgebraic E₁ ↔ DifferentiallyAlgebraic E₂
  hypertranscendental_iff : Hypertranscendental E₁ ↔ Hypertranscendental E₂

/-- **Sharp finite-order de Branges rigidity.**  Finite-order Hermite--Biehler entire functions
without real zeros and with the same exact inner quotient differ by a Schwarz-real exponential of
a polynomial.  Therefore differential-algebraic and hypertranscendental type agree exactly. -/
theorem exists_finiteOrderDeBrangesRigidityData
    {E₁ E₂ : ℂ → ℂ}
    (hE₁ : AnalyticOnNhd ℂ E₁ Set.univ) (hE₂ : AnalyticOnNhd ℂ E₂ Set.univ)
    (hHB₁ : SuzukiHermiteBiehler E₁) (hHB₂ : SuzukiHermiteBiehler E₂)
    (hreal₁ : ∀ x : ℝ, E₁ (x : ℂ) ≠ 0) (hreal₂ : ∀ x : ℝ, E₂ (x : ℂ) ≠ 0)
    (hTheta : ∀ z, suzukiEntireSharp E₁ z / E₁ z =
      suzukiEntireSharp E₂ z / E₂ z)
    (hfinite₁ : FiniteOrderEnvelope E₁) (hfinite₂ : FiniteOrderEnvelope E₂) :
    Nonempty (FiniteOrderDeBrangesRigidityData E₁ E₂) := by
  have hE₁diff : Differentiable ℂ E₁ := by
    rwa [Complex.analyticOnNhd_univ_iff_differentiable] at hE₁
  have hE₂diff : Differentiable ℂ E₂ := by
    rwa [Complex.analyticOnNhd_univ_iff_differentiable] at hE₂
  have hE₁ne : ∃ z, E₁ z ≠ 0 := exists_ne_zero_of_suzukiHermiteBiehler hHB₁
  have hE₂ne : ∃ z, E₂ z ≠ 0 := exists_ne_zero_of_suzukiHermiteBiehler hHB₂
  have horder : ∀ z, analyticOrderAt E₁ z = analyticOrderAt E₂ z :=
    analyticOrderAt_eq_of_deBrangesInnerQuotient_eq
      hE₁ hE₂ hHB₁ hHB₂ hreal₁ hreal₂ hTheta
  obtain ⟨z₁, hz₁⟩ := hE₁ne
  have hford : ∀ z, analyticOrderAt E₁ z ≠ ⊤ :=
    analyticOrderAt_ne_top_of_entire hE₁diff hz₁
  have hE₂I : E₂ Complex.I ≠ 0 :=
    suzukiHermiteBiehler_ne_zero_upper hHB₂ (by simp)
  obtain ⟨H, hHdiff, hHzero, hfac⟩ :=
    EntireQuotient.exists_entire_nonvanishing_quotient
      hE₁ hE₂ hford horder hE₂I
  have hH : AnalyticOnNhd ℂ H Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact hHdiff
  have hHfinite : FiniteOrderEnvelope H :=
    FiniteOrderEnvelope.of_entire_quotient hE₂ hE₁ hH hE₂ne ⟨z₁, hz₁⟩
      hHzero hfac hfinite₂ hfinite₁
  obtain ⟨p, hp⟩ := exists_polynomial_exp_of_ne_zero hHdiff hHzero hHfinite
  have hE₁sharp := analyticOnNhd_suzukiEntireSharp hE₁
  have hE₂sharp := analyticOnNhd_suzukiEntireSharp hE₂
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hmem : {z : ℂ | 0 < z.im} ∈ 𝓝 Complex.I := hopen.mem_nhds (by simp)
  have hcrossLocal :
      (suzukiEntireSharp E₁ * E₂) =ᶠ[𝓝 Complex.I]
        (suzukiEntireSharp E₂ * E₁) := by
    filter_upwards [hmem] with z hz
    change suzukiEntireSharp E₁ z * E₂ z = suzukiEntireSharp E₂ z * E₁ z
    exact (div_eq_div_iff (suzukiHermiteBiehler_ne_zero_upper hHB₁ hz)
      (suzukiHermiteBiehler_ne_zero_upper hHB₂ hz)).mp (hTheta z)
  have hcrossFun : suzukiEntireSharp E₁ * E₂ = suzukiEntireSharp E₂ * E₁ :=
    (hE₁sharp.mul hE₂).eq_of_eventuallyEq (hE₂sharp.mul hE₁) hcrossLocal
  have hsharpFac : ∀ z,
      suzukiEntireSharp E₁ z = suzukiEntireSharp H z * suzukiEntireSharp E₂ z := by
    intro z
    change star (E₁ (star z)) = star (H (star z)) * star (E₂ (star z))
    rw [hfac (star z), star_mul]
    exact mul_comm _ _
  have hprod : ∀ z,
      (suzukiEntireSharp H z - H z) * (suzukiEntireSharp E₂ z * E₂ z) = 0 := by
    intro z
    have hc := congrFun hcrossFun z
    simp only [Pi.mul_apply] at hc
    rw [hsharpFac z, hfac z] at hc
    calc
      (suzukiEntireSharp H z - H z) * (suzukiEntireSharp E₂ z * E₂ z) =
          (suzukiEntireSharp H z * suzukiEntireSharp E₂ z) * E₂ z -
            suzukiEntireSharp E₂ z * (H z * E₂ z) := by ring
      _ = 0 := sub_eq_zero.mpr hc
  have hHsharp := analyticOnNhd_suzukiEntireSharp hH
  have hdelta : AnalyticOnNhd ℂ (suzukiEntireSharp H - H) Set.univ := hHsharp.sub hH
  obtain ⟨z₀, hz₀⟩ := exists_ne_zero_mul_sharp hE₂ hE₂ne
  have hz₀' : suzukiEntireSharp E₂ z₀ * E₂ z₀ ≠ 0 := by
    rw [mul_comm]
    exact hz₀
  have hfactorEv : ∀ᶠ z in 𝓝 z₀, suzukiEntireSharp E₂ z * E₂ z ≠ 0 :=
    ((hE₂sharp.mul hE₂) z₀ (Set.mem_univ z₀)).continuousAt.eventually_ne hz₀'
  have hdeltaEv : (suzukiEntireSharp H - H) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hfactorEv] with z hz
    change suzukiEntireSharp H z - H z = 0
    exact (mul_eq_zero.mp (hprod z)).resolve_right hz
  have hHreal : SchwarzRealGauge H := by
    intro z
    exact sub_eq_zero.mp (hdelta.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z₀) hdeltaEv (Set.mem_univ z))
  have hHDA : DifferentiallyAlgebraic H := by
    have hfun : H = fun z => Complex.exp (p.eval z) := funext hp
    rw [hfun]
    exact differentiallyAlgebraic_exp_polynomial p
  have hDAiff : DifferentiallyAlgebraic E₁ ↔ DifferentiallyAlgebraic E₂ := by
    constructor
    · intro hE₁DA
      exact differentiallyAlgebraic_right_of_mul_eq hH hE₂ hE₁ ⟨0, hHzero 0⟩
        (fun z => (hfac z).symm) hHDA hE₁DA
    · intro hE₂DA
      have hmul := differentiallyAlgebraic_mul hH hE₂ hHDA hE₂DA
      have hfun : E₁ = fun z => H z * E₂ z := funext hfac
      rwa [hfun]
  refine ⟨⟨H, p, hH, hHzero, hfac, hp, hHreal, hDAiff, ?_⟩⟩
  change (¬ DifferentiallyAlgebraic E₁) ↔ (¬ DifferentiallyAlgebraic E₂)
  exact not_congr hDAiff

end

end GaloisForLFunctions.RHTower
