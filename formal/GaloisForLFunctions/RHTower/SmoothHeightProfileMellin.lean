import GaloisForLFunctions.RHTower.HeightProfileMellin
import GaloisForLFunctions.RHTower.FourierCompactSupportDensity
import Mathlib.Analysis.MellinInversion

/-!
# Smooth height profiles: Mellin decay and density on the critical line

* For a smooth height profile `ψ`, `θψ = yψ'` is again a smooth height profile with
  `(θψ)^(s) = s ψ̂(s)` (`hMellin_theta`, one integration by parts), so
  `‖ψ̂(σ+it)‖(1+|t|)^k` is bounded uniformly on vertical strips for every `k`
  (`exists_bound_hMellin_pow`).
* Every test function `g` gives the smooth profile `ψ_g(y) = g(−log y)√y` (`ofTest`), with
  `ψ̂_g(½+it) = 𝓕g(−t/2π)` (`hMellin_ofTest_half`); hence a square-integrable `F` with
  `∫ ψ̂_g(½+it) F(t) dt = 0` for all test functions vanishes almost everywhere
  (`ae_eq_zero_of_integral_hMellin_ofTest`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate ContDiff FourierTransform

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

/-- A height profile with a smooth profile function. -/
structure SmoothHeightProfile extends HeightProfile where
  smooth : ContDiff ℝ ∞ toFun

namespace SmoothHeightProfile

variable (ψ : SmoothHeightProfile)

theorem deriv_eq_zero_of_lt {y : ℝ} (hy : y < ψ.lower) : deriv ψ.toFun y = 0 := by
  have h : ψ.toFun =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hy] with x hx
    exact ψ.eq_zero_of_lt x hx
  rw [h.deriv_eq, deriv_const]

theorem deriv_eq_zero_of_gt {y : ℝ} (hy : ψ.upper < y) : deriv ψ.toFun y = 0 := by
  have h : ψ.toFun =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact ψ.eq_zero_of_gt x hx
  rw [h.deriv_eq, deriv_const]

/-- **The Euler operator** `θψ = y ψ'`. -/
def theta : SmoothHeightProfile where
  toFun y := (y : ℂ) * deriv ψ.toFun y
  lower := ψ.lower
  upper := ψ.upper
  lower_pos := ψ.lower_pos
  lower_le_upper := ψ.lower_le_upper
  continuous := Complex.continuous_ofReal.mul (ψ.smooth.continuous_deriv (by simp))
  eq_zero_of_lt y hy := by rw [ψ.deriv_eq_zero_of_lt hy, mul_zero]
  eq_zero_of_gt y hy := by rw [ψ.deriv_eq_zero_of_gt hy, mul_zero]
  smooth := Complex.ofRealCLM.contDiff.mul (contDiff_infty_iff_deriv.1 ψ.smooth).2

/-- **`(θψ)^(s) = s ψ̂(s)`.** -/
theorem hMellin_theta (s : ℂ) :
    hMellin ψ.theta.toFun s = s * hMellin ψ.toFun s := by
  set α := ψ.lower / 2
  set β := ψ.upper + 1
  have hα : 0 < α := by simp only [α]; linarith [ψ.lower_pos]
  have hαl : α < ψ.lower := by simp only [α]; linarith [ψ.lower_pos]
  have hβ : ψ.upper ≤ β := by simp only [β]; linarith
  have hαβ : α ≤ β := by linarith [ψ.lower_le_upper]
  rw [ψ.theta.toHeightProfile.hMellin_eq_intervalIntegral hα hαl hβ,
    ψ.toHeightProfile.hMellin_eq_intervalIntegral hα hαl hβ]
  have hpos : ∀ y ∈ uIcc α β, 0 < y := fun y hy => by
    rw [uIcc_of_le hαβ] at hy; exact lt_of_lt_of_le hα hy.1
  have hu : ∀ y ∈ uIcc α β, HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
      ((-s) * (y : ℂ) ^ (-s - 1)) y := fun y hy => by
    have h := (Complex.hasStrictDerivAt_cpow_const (c := -s)
      (Complex.ofReal_mem_slitPlane.2 (hpos y hy))).hasDerivAt
    exact h.comp_ofReal
  have hv : ∀ y ∈ uIcc α β, HasDerivAt ψ.toFun (deriv ψ.toFun y) y := fun y _ =>
    (ψ.smooth.differentiable (by simp) y).hasDerivAt
  have hcu : ContinuousOn (fun y : ℝ => (-s) * (y : ℂ) ^ (-s - 1)) (uIcc α β) := fun y hy =>
    (continuous_const.continuousAt.mul (continuousAt_ofReal_cpow_const y _
      (Or.inr (hpos y hy).ne'))).continuousWithinAt
  have hbp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hcu.intervalIntegrable) ((ψ.smooth.continuous_deriv (by simp)).intervalIntegrable _ _)
  have hβ0 : ψ.toFun β = 0 := ψ.eq_zero_of_gt β (by simp only [β]; linarith)
  have hα0 : ψ.toFun α = 0 := ψ.eq_zero_of_lt α hαl
  rw [hβ0, hα0, mul_zero, mul_zero, sub_zero, zero_sub] at hbp
  have hlhs : ∫ y in α..β, (y : ℂ) ^ (-s - 1) * ψ.theta.toFun y =
      ∫ y in α..β, (y : ℂ) ^ (-s) * deriv ψ.toFun y := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (hpos y hy).ne'
    show (y : ℂ) ^ (-s - 1) * ((y : ℂ) * deriv ψ.toFun y) = _
    have e : (y : ℂ) ^ (-s) = (y : ℂ) ^ (-s - 1) * y := by
      conv_lhs => rw [show -s = (-s - 1) + 1 by ring]
      rw [Complex.cpow_add _ _ hy0, Complex.cpow_one]
    rw [e, mul_assoc]
  rw [hlhs, hbp, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun y _ => ?_
  ring

/-- The iterated Euler operator. -/
def thetaIter : ℕ → SmoothHeightProfile → SmoothHeightProfile
  | 0, ψ => ψ
  | k + 1, ψ => (thetaIter k ψ).theta

theorem hMellin_thetaIter (k : ℕ) (s : ℂ) :
    hMellin (thetaIter k ψ).toFun s = s ^ k * hMellin ψ.toFun s := by
  induction k with
  | zero => simp [thetaIter]
  | succ k ih => rw [thetaIter, hMellin_theta, ih, pow_succ]; ring

/-- **Super-polynomial decay of `ψ̂` on vertical strips.** -/
theorem exists_bound_hMellin_pow (k : ℕ) (σ₀ σ₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ →
      ‖hMellin ψ.toFun s‖ * (1 + |s.im|) ^ k ≤ C := by
  obtain ⟨C₀, hC₀, h₀⟩ := ψ.toHeightProfile.exists_bound_hMellin_zero σ₀ σ₁
  obtain ⟨Ck, hCk, hk⟩ := (thetaIter k ψ).toHeightProfile.exists_bound_hMellin_zero σ₀ σ₁
  refine ⟨2 ^ k * (C₀ + Ck), by positivity, fun s hs0 hs1 => ?_⟩
  have e0 := h₀ s hs0 hs1
  have ek := hk s hs0 hs1
  rw [show (thetaIter k ψ).toHeightProfile.toFun = (thetaIter k ψ).toFun from rfl,
    hMellin_thetaIter, norm_mul, norm_pow] at ek
  have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hpow : (1 + |s.im|) ^ k ≤ 2 ^ k * (1 + ‖s‖ ^ k) := by
    calc (1 + |s.im|) ^ k ≤ (1 + ‖s‖) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ (2 * max 1 ‖s‖) ^ k := pow_le_pow_left₀ (by positivity)
          (by linarith [le_max_left 1 ‖s‖, le_max_right 1 ‖s‖]) k
      _ = 2 ^ k * max 1 ‖s‖ ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + ‖s‖ ^ k) := by
          gcongr
          rcases le_total 1 ‖s‖ with h | h
          · rw [max_eq_right h]; linarith [pow_nonneg (norm_nonneg s) k]
          · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (norm_nonneg s) k]
  calc ‖hMellin ψ.toFun s‖ * (1 + |s.im|) ^ k
      ≤ ‖hMellin ψ.toFun s‖ * (2 ^ k * (1 + ‖s‖ ^ k)) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = 2 ^ k * (‖hMellin ψ.toFun s‖ + ‖s‖ ^ k * ‖hMellin ψ.toFun s‖) := by ring
    _ ≤ 2 ^ k * (C₀ + Ck) := by gcongr

/-! ## Profiles from test functions -/

theorem exists_bound_of_hasCompactSupport {g : ℝ → ℂ} (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ u, R < |u| → g u = 0 := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun u hu => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith [le_max_left R 0]

/-- The radius of a compactly supported function. -/
def testRadius {g : ℝ → ℂ} (hgc : HasCompactSupport g) : ℝ :=
  Classical.choose (exists_bound_of_hasCompactSupport hgc)

theorem testRadius_nonneg {g : ℝ → ℂ} (hgc : HasCompactSupport g) : 0 ≤ testRadius hgc :=
  (Classical.choose_spec (exists_bound_of_hasCompactSupport hgc)).1

theorem eq_zero_of_testRadius_lt {g : ℝ → ℂ} (hgc : HasCompactSupport g) {u : ℝ}
    (hu : testRadius hgc < |u|) : g u = 0 :=
  (Classical.choose_spec (exists_bound_of_hasCompactSupport hgc)).2 u hu

/-- **The profile of a test function** `ψ_g(y) = g(−log y)√y`. -/
def ofTest (g : ℝ → ℂ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    SmoothHeightProfile where
  toFun y := if 0 < y then g (-Real.log y) * (Real.sqrt y : ℂ) else 0
  lower := Real.exp (-(testRadius hgc + 1))
  upper := Real.exp (testRadius hgc + 1)
  lower_pos := Real.exp_pos _
  lower_le_upper := Real.exp_le_exp.mpr (by linarith [testRadius_nonneg hgc])
  continuous := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    rcases lt_or_ge 0 x with hx | hx
    · have h : (fun y : ℝ => if 0 < y then g (-Real.log y) * (Real.sqrt y : ℂ) else 0) =ᶠ[𝓝 x]
          fun y => g (-Real.log y) * (Real.sqrt y : ℂ) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        rw [if_pos (show (0 : ℝ) < y from hy)]
      refine ContinuousAt.congr ?_ h.symm
      exact (hgs.continuous.continuousAt.comp (Real.continuousAt_log hx.ne').neg).mul
        (Complex.continuous_ofReal.continuousAt.comp Real.continuous_sqrt.continuousAt)
    · have hlow : x < Real.exp (-(testRadius hgc + 1)) := lt_of_le_of_lt hx (Real.exp_pos _)
      have h : (fun y : ℝ => if 0 < y then g (-Real.log y) * (Real.sqrt y : ℂ) else 0) =ᶠ[𝓝 x]
          fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hlow] with y hy
        split_ifs with hy0
        · rw [eq_zero_of_testRadius_lt hgc, zero_mul]
          have hlog : Real.log y < -(testRadius hgc + 1) := by
            rw [Real.log_lt_iff_lt_exp hy0]; exact hy
          have hR := testRadius_nonneg hgc
          rw [abs_of_pos (by linarith)]
          linarith
        · rfl
      exact continuousAt_const.congr h.symm
  eq_zero_of_lt y hy := by
    split_ifs with hy0
    · rw [eq_zero_of_testRadius_lt hgc, zero_mul]
      have hlog : Real.log y < -(testRadius hgc + 1) := by
        rw [Real.log_lt_iff_lt_exp hy0]; exact hy
      have hR := testRadius_nonneg hgc
      rw [abs_of_pos (by linarith)]
      linarith
    · rfl
  eq_zero_of_gt y hy := by
    have hy0 : 0 < y := lt_trans (Real.exp_pos _) hy
    simp only [if_pos hy0]
    rw [eq_zero_of_testRadius_lt hgc, zero_mul]
    have hlog : testRadius hgc + 1 < Real.log y := by
      rw [Real.lt_log_iff_exp_lt hy0]; exact hy
    rw [abs_of_neg (by linarith [testRadius_nonneg hgc])]
    linarith
  smooth := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge 0 x with hx | hx
    · have h : (fun y : ℝ => if 0 < y then g (-Real.log y) * (Real.sqrt y : ℂ) else 0) =ᶠ[𝓝 x]
          fun y => g (-Real.log y) * (Real.sqrt y : ℂ) := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        rw [if_pos (show (0 : ℝ) < y from hy)]
      refine ContDiffAt.congr_of_eventuallyEq ?_ h
      exact (hgs.contDiffAt.comp x (Real.contDiffAt_log.2 hx.ne').neg).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_sqrt hx.ne'))
    · have hlow : x < Real.exp (-(testRadius hgc + 1)) := lt_of_le_of_lt hx (Real.exp_pos _)
      have h : (fun y : ℝ => if 0 < y then g (-Real.log y) * (Real.sqrt y : ℂ) else 0) =ᶠ[𝓝 x]
          fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hlow] with y hy
        split_ifs with hy0
        · rw [eq_zero_of_testRadius_lt hgc, zero_mul]
          have hlog : Real.log y < -(testRadius hgc + 1) := by
            rw [Real.log_lt_iff_lt_exp hy0]; exact hy
          have hR := testRadius_nonneg hgc
          rw [abs_of_pos (by linarith)]
          linarith
        · rfl
      exact contDiffAt_const.congr_of_eventuallyEq h

/-- **On the critical line the Mellin transform of `ψ_g` is the Fourier transform of `g`**:
`ψ̂_g(½+it) = 𝓕g(−t/2π)`. -/
theorem hMellin_ofTest_half (g : ℝ → ℂ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (t : ℝ) :
    hMellin (ofTest g hgc hgs).toFun (1 / 2 + t * Complex.I) = 𝓕 g (-t / (2 * Real.pi)) := by
  rw [hMellin, mellin_eq_fourier]
  have hre : (-(1 / 2 + t * Complex.I) : ℂ).re = -(1 / 2) := by simp
  have him : (-(1 / 2 + t * Complex.I) : ℂ).im = -t := by simp
  rw [hre, him]
  have hfun : (fun u : ℝ => Real.exp (-(-(1 / 2 : ℝ)) * u) •
      (ofTest g hgc hgs).toFun (Real.exp (-u))) = g := by
    funext u
    have hpos : 0 < Real.exp (-u) := Real.exp_pos _
    show (Real.exp (-(-(1 / 2)) * u) : ℝ) •
        (if 0 < Real.exp (-u) then g (-Real.log (Real.exp (-u))) *
          (Real.sqrt (Real.exp (-u)) : ℂ) else 0) = g u
    rw [if_pos hpos, Real.log_exp, neg_neg, Real.sqrt_eq_rpow, ← Real.exp_mul, Complex.real_smul,
      mul_left_comm, ← Complex.ofReal_mul, ← Real.exp_add]
    rw [show (1 / 2 : ℝ) * u + -u * (1 / 2) = 0 by ring, Real.exp_zero, Complex.ofReal_one,
      mul_one, neg_neg]
  rw [hfun]

/-- **Density on the critical line**: a square-integrable `F` with `∫ ψ̂_g(½+it) F(t) dt = 0` for
every test function `g` vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_hMellin_ofTest {F : ℝ → ℂ} (hF : MemLp F 2)
    (h : ∀ (g : ℝ → ℂ) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g),
      ∫ t : ℝ, hMellin (ofTest g hgc hgs).toFun (1 / 2 + t * Complex.I) * F t = 0) :
    F =ᵐ[volume] 0 := by
  have hc : (-(2 * Real.pi) : ℝ) ≠ 0 := by have := Real.pi_pos; linarith
  set G : ℝ → ℂ := fun ξ => F (-(2 * Real.pi) * ξ)
  have hqmp := MeasureTheory.Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) hc
  have hGm : AEStronglyMeasurable G volume := by
    have := hF.1.comp_quasiMeasurePreserving hqmp
    have e : G = F ∘ fun x => -(2 * Real.pi) • x := by
      funext x; simp [G, smul_eq_mul]
    rw [e]
    exact this
  have hG : MemLp G 2 := by
    refine (memLp_two_iff_integrable_sq_norm hGm).2 ?_
    have hi := (memLp_two_iff_integrable_sq_norm hF.1).1 hF
    exact hi.comp_mul_left' hc
  have hG0 : G =ᵐ[volume] 0 := by
    refine Kuznetsov.ae_eq_zero_of_integral_fourier_mul_eq_zero hG fun g hgc hgs => ?_
    have h1 := h g hgc hgs
    have h2 := Measure.integral_comp_mul_left
      (fun t : ℝ => hMellin (ofTest g hgc hgs).toFun (1 / 2 + t * Complex.I) * F t)
      (-(2 * Real.pi))
    rw [h1, smul_zero] at h2
    rw [← h2]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [G]
    rw [show (((-(2 * Real.pi) * ξ : ℝ)) : ℂ) = ((-(2 * Real.pi) * ξ : ℝ) : ℂ) from rfl,
      hMellin_ofTest_half]
    congr 2
    field_simp
  have hqmp' := MeasureTheory.Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (inv_ne_zero hc)
  filter_upwards [hqmp'.ae hG0] with t ht
  simp only [G, Pi.zero_apply, smul_eq_mul] at ht
  rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at ht

end SmoothHeightProfile

end

end GaloisForLFunctions.RHTower.DeckPointPair
