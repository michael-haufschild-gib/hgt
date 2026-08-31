import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildResponseJetInterpolationNoGo
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity
import GaloisForLFunctions.RHTower.BVPrimeWindowDivisorTomography

/-!
# FZZ Schwarzschild physical response: finite-type selection no-go

The pole-filled all-order Schwarzschild response is the shifted completed zeta carrier
`z ↦ regularizedRiemannZeta (z + 2)`.  This file proves that every Xi divisor point in the
critical strip transfers, with its full analytic multiplicity, to a zero of that response.
Consequently its divisor mass in radius `T + 2` dominates the unconditional Xi zero count
`xiZeroCount T`.

Riemann--von Mangoldt gives superlinear `T log T` growth, whereas a nonzero entire function
of finite exponential type has only linear divisor mass.  The physical response therefore
has no finite exponential type.  Together with the already-proved nonuniqueness of entire
all-order response interpolation, this closes the regular finite-type response-selection
branch of the FZZ-P route.

The conclusion is deliberately sharp: it does not exclude order-one maximal growth
`exp (O(r log r))`, singular response categories, or a deformation of the physical source.
-/

open Complex Set Metric

noncomputable section

namespace RHTower

/-- The canonical pole-filled Schwarzschild response obeys a global finite-exponential-type
bound.  The normalization `1 ≤ C` is harmless and matches the zero-density theorem. -/
def BlackHolePoleFilledResponseFiniteExponentialType : Prop :=
  ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧
    ∀ z : ℂ, ‖blackHolePoleFilledJetInterpolation z‖ ≤
      C * Real.exp (A * ‖z‖)

theorem analyticOrderAt_blackHolePoleFilledJetInterpolation_shift_eq_xi {ρ : ℂ} (hρ : ρ.re ∈ Ioo (0 : ℝ) 1) :
    analyticOrderAt blackHolePoleFilledJetInterpolation (ρ - 2) =
      analyticOrderAt xi ρ := by
  let shift : ℂ → ℂ := fun z => z + 2
  have hshiftAn : AnalyticAt ℂ shift (ρ - 2) := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift (ρ - 2) ≠ 0 := by
    dsimp only [shift]
    rw [deriv_add_const, deriv_id'']
    norm_num
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := regularizedRiemannZeta) hshiftAn hshiftDeriv
  have hshift : shift (ρ - 2) = ρ := by dsimp only [shift]; ring
  rw [hshift] at hcomp
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hρ
    exact (lt_irrefl 1 hρ.2).elim
  calc
    analyticOrderAt blackHolePoleFilledJetInterpolation (ρ - 2) =
        analyticOrderAt regularizedRiemannZeta ρ := by
      change analyticOrderAt (fun z : ℂ => regularizedRiemannZeta (z + 2)) (ρ - 2) =
        analyticOrderAt regularizedRiemannZeta ρ
      exact hcomp
    _ = analyticOrderAt riemannZeta ρ :=
      analyticOrderAt_regularizedRiemannZeta_eq_riemannZeta hρ1
    _ = analyticOrderAt xi ρ :=
      (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hρ).symm

theorem xiZeroCount_le_blackHolePoleFilledJetInterpolation_shiftedDivisor {T : ℝ} (hT : 0 ≤ T) :
    xiZeroCount T ≤
      ∑ᶠ u, MeromorphicOn.divisor blackHolePoleFilledJetInterpolation
        (closedBall (0 : ℂ) (T + 2)) u := by
  classical
  let S : Finset XiDivisorSupport := xiSupportsPos T
  let φ : XiDivisorSupport → ℂ := fun ρ => (ρ : ℂ) - 2
  let d := MeromorphicOn.divisor blackHolePoleFilledJetInterpolation
    (closedBall (0 : ℂ) (T + 2))
  let Z : Finset ℂ := S.image φ
  have hfan : AnalyticOnNhd ℂ blackHolePoleFilledJetInterpolation
      (closedBall (0 : ℂ) (T + 2)) :=
    (differentiable_blackHolePoleFilledJetInterpolation.differentiableOn.analyticOnNhd
      isOpen_univ).mono (Set.subset_univ _)
  have hterm : ∀ ρ ∈ S, d (φ ρ) = (xiSupportMultiplicity ρ : ℤ) := by
    intro ρ hρS
    have hρpos : ρ ∈ xiSupportsPos T := by simpa only [S] using hρS
    have hρmem := mem_xiSupportsPos.mp hρpos
    have hstrip := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support ρ)
    have hreabs : |(φ ρ).re| ≤ 2 := by
      dsimp only [φ]
      change |(ρ : ℂ).re - 2| ≤ 2
      rw [abs_le]
      constructor <;> linarith [hstrip.1, hstrip.2]
    have himabs : |(φ ρ).im| ≤ T := by
      dsimp only [φ]
      simpa using hρmem.1
    have hball : φ ρ ∈ closedBall (0 : ℂ) (T + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc
        ‖φ ρ‖ ≤ |(φ ρ).re| + |(φ ρ).im| :=
          Complex.norm_le_abs_re_add_abs_im (φ ρ)
        _ ≤ 2 + T := add_le_add hreabs himabs
        _ = T + 2 := by ring
    have hord := analyticOrderAt_blackHolePoleFilledJetInterpolation_shift_eq_xi hstrip
    have hfinite : analyticOrderAt blackHolePoleFilledJetInterpolation (φ ρ) ≠ ⊤ := by
      rw [hord]
      exact xi_orderAt_ne_top (ρ : ℂ)
    have hd : d (φ ρ) =
        ((analyticOrderAt blackHolePoleFilledJetInterpolation (φ ρ)).toNat : ℤ) := by
      dsimp only [d]
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfan hball,
        ← ENat.coe_toNat hfinite]
      simp
    rw [hd, hord, ← xiSupportMultiplicity_eq_analyticOrderAt_toNat]
  have hinj : Set.InjOn φ (S : Set XiDivisorSupport) := by
    intro a ha b hb hab
    apply Subtype.ext
    dsimp only [φ] at hab
    apply_fun (fun z : ℂ => z + 2) at hab
    simpa using hab
  have hdnonneg : ∀ u : ℂ, 0 ≤ d u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan
  have hdfin : (Function.support d).Finite :=
    d.finiteSupport (isCompact_closedBall (0 : ℂ) (T + 2))
  let D : Finset ℂ := hdfin.toFinset
  have hZsub : Z ⊆ D := by
    intro u hu
    simp only [Z, Finset.mem_image] at hu
    obtain ⟨ρ, hρS, rfl⟩ := hu
    have hpos : (0 : ℤ) < (xiSupportMultiplicity ρ : ℤ) := by
      exact_mod_cast xiSupportMultiplicity_pos ρ
    have hne : d (φ ρ) ≠ 0 := by
      rw [hterm ρ hρS]
      exact ne_of_gt hpos
    simpa [D] using Function.mem_support.mpr hne
  have hsumZ : ∑ u ∈ Z, d u =
      ∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℤ) := by
    dsimp only [Z]
    rw [Finset.sum_image (fun a ha b hb h =>
      hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h)]
    exact Finset.sum_congr rfl fun ρ hρ => hterm ρ hρ
  rw [xiZeroCount_eq_pos_sum hT]
  change (∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℤ)) ≤ ∑ᶠ u, d u
  rw [← hsumZ]
  calc
    ∑ u ∈ Z, d u ≤ ∑ u ∈ D, d u := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hZsub
        (fun u _ _ => hdnonneg u)
    _ = ∑ᶠ u, d u := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro u hu
      simpa [D] using hu

/-- The physical all-order Schwarzschild response has no finite exponential type.  This is
unconditional: multiplicities are retained and neither RH nor zero simplicity is used. -/
theorem blackHolePoleFilledJetInterpolation_not_finiteExponentialType :
    ¬ BlackHolePoleFilledResponseFiniteExponentialType := by
  unfold BlackHolePoleFilledResponseFiniteExponentialType
  rintro ⟨A, C, hA, hC, hgrow⟩
  obtain ⟨K, hK0, hK⟩ := exponentialType_zeroCount_linear
    differentiable_blackHolePoleFilledJetInterpolation
    blackHolePoleFilledJetInterpolation_zero_ne hA hC hgrow
  let ε : ℝ := 1 / (4 * Real.pi)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨T₀, hT₀, hRVM⟩ := exists_xiZeroCount_close ε hε
  let T : ℝ := max T₀ (Real.exp (8 * Real.pi * K) + 1)
  have hTT₀ : T₀ ≤ T := le_max_left _ _
  have hT4 : 4 ≤ T := hT₀.trans hTT₀
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT4
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT4
  have hT3 : 3 ≤ T := le_trans (by norm_num) hT4
  have hexpT : Real.exp (8 * Real.pi * K) < T := by
    exact (lt_add_one _).trans_le (le_max_right _ _)
  have hlogT : 8 * Real.pi * K < Real.log T := by
    rw [← Real.exp_lt_exp, Real.exp_log hTpos]
    simpa using hexpT
  have hmain := hRVM T hTT₀
  have hTlog0 : 0 ≤ T * Real.log T := by
    exact mul_nonneg hT0 (Real.log_nonneg (by linarith))
  have hNlower : (1 / (4 * Real.pi)) * (T * Real.log T) ≤
      (xiZeroCount T : ℝ) := by
    have hlower := (abs_le.mp hmain).1
    dsimp only [ε] at hlower
    have hπ : 0 < Real.pi := Real.pi_pos
    calc
      (1 / (4 * Real.pi)) * (T * Real.log T) =
          (1 / (2 * Real.pi)) * (T * Real.log T) -
            (1 / (4 * Real.pi)) * (T * Real.log T) := by
        field_simp
        ring
      _ ≤ (xiZeroCount T : ℝ) := by linarith
  have hcountZ := xiZeroCount_le_blackHolePoleFilledJetInterpolation_shiftedDivisor hT0
  have hcountR : (xiZeroCount T : ℝ) ≤
      (↑(∑ᶠ u, MeromorphicOn.divisor blackHolePoleFilledJetInterpolation
        (closedBall (0 : ℂ) (T + 2)) u) : ℝ) := by
    exact_mod_cast hcountZ
  have hupper := hK (T + 2) (by linarith)
  have htoTwo : K * (1 + (T + 2)) ≤ 2 * K * T := by
    nlinarith
  have hstrict : 2 * K * T < (1 / (4 * Real.pi)) * (T * Real.log T) := by
    have hscale : 0 < T / (4 * Real.pi) := by positivity
    have hmul := mul_lt_mul_of_pos_left hlogT hscale
    calc
      2 * K * T = (T / (4 * Real.pi)) * (8 * Real.pi * K) := by
        field_simp
        ring
      _ < (T / (4 * Real.pi)) * Real.log T := hmul
      _ = (1 / (4 * Real.pi)) * (T * Real.log T) := by ring
  have := hNlower.trans (hcountR.trans (hupper.trans htoTwo))
  exact (not_lt_of_ge this) hstrict

/-- Closed certificate for the regular finite-type FZZ response-selection no-go.

The first conjunct says entireness plus every physical response jet is non-identifying for
every scale convention.  The second says the intended physical continuation is not even in
the finite-exponential-type category that was proposed to restore uniqueness. -/
def FZZRegularFiniteTypePhysicalResponseRouteKilled : Prop :=
  (∀ scaleLog : ℂ,
      ¬ ∃! F : ℂ → ℂ, IsEntireBlackHoleJetInterpolant scaleLog F) ∧
    ¬ BlackHolePoleFilledResponseFiniteExponentialType

/-- The regular finite-exponential-type physical-response branch of FZZ-P is impossible. -/
theorem fzz_regularFiniteTypePhysicalResponse_route_noGo :
    FZZRegularFiniteTypePhysicalResponseRouteKilled := by
  exact ⟨not_unique_entire_blackHoleJetInterpolation,
    blackHolePoleFilledJetInterpolation_not_finiteExponentialType⟩

end RHTower
