import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheHamburgerPolesReadOneAtom
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheThetaSmoothedWeightsArePinned

/-!
# The cone is pinned at every atom

**Theorem** (`exists_abs_sub_vonMangoldt_le_exp`). There are absolute constants `C, K` with

  `|λ(n) − Λ(n)| ≤ C exp(K n − c/1104)`

for every `c ≥ 2`, every `λ ∈ 𝒜(c)` and every integer `2 ≤ n ≤ e^{2c − 1/6}`. So effective uniqueness holds
with an explicit rate, and it covers all integers up to a fixed multiple of `c`.

Mechanism. On the cone, `Φ_L` is near null, so Cauchy–Schwarz on the positive form reads `λ − Λ` against
`Φ_L ⋆ Y` for any test `Y`, with no positivity needed on the second slot. Take `Y` to be the truncated Gaussian
test `Y_t`. Its size, form and zero bound are uniform in `t ≥ 1`, so the reading of `Φ ⋆ Y_t` is small on a
whole ray, up to the tail `e^{−L/4}` of `Y_t`, which is only exponentially small. That reading is Hamburger's
series, and the quantitative Hamburger theorem turns its smallness into the bound on each atom.

The doubly exponential ceiling of the near-null vector enters only through the exponential tail of `Y_t`, which
sets the rate.
-/

open MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.Zeta23

local notation "𝔽" => xiShiftedGammaTest

/-! ### The Gaussian test is uniformly bounded -/

theorem contDiff_gaussTest (t : ℝ) : ContDiff ℝ 2 (gaussTest t) := by
  unfold gaussTest
  fun_prop

theorem gaussTest_pos (t v : ℝ) : 0 < gaussTest t v := by
  unfold gaussTest
  positivity

theorem hasDerivAt_gaussTest (t v : ℝ) :
    HasDerivAt (gaussTest t)
      (gaussTest t v * (-(3 / 2) + 2 * (π * t ^ 2 * Real.exp (-(2 * v))))) v := by
  have e1 : HasDerivAt (fun v : ℝ => Real.exp (-(3 / 2 * v))) (Real.exp (-(3 / 2 * v)) * (-(3 / 2))) v := by
    simpa using ((hasDerivAt_id v).const_mul (3 / 2 : ℝ)).neg.exp
  have e2 : HasDerivAt (fun v : ℝ => Real.exp (-(2 * v))) (Real.exp (-(2 * v)) * (-2)) v := by
    simpa using ((hasDerivAt_id v).const_mul (2 : ℝ)).neg.exp
  have e3 : HasDerivAt (fun v : ℝ => -(π * t ^ 2 * Real.exp (-(2 * v))))
      (-(π * t ^ 2 * (Real.exp (-(2 * v)) * (-2)))) v := (e2.const_mul (π * t ^ 2)).neg
  have h := (e1.const_mul (2 : ℝ)).mul e3.exp
  unfold gaussTest
  refine h.congr_deriv ?_
  ring

/-- The exponent of `Y_t` at the far left beats `|v|`. -/
theorem six_mul_abs_le {t v : ℝ} (ht : 1 ≤ t) (hv : v ≤ 0) :
    6 * |v| ≤ π * t ^ 2 * Real.exp (-(2 * v)) := by
  rw [abs_of_nonpos hv]
  have h1 := Real.add_one_le_exp (-(2 * v))
  have hpi := Real.pi_gt_three
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have hE : 0 < Real.exp (-(2 * v)) := Real.exp_pos _
  have h2 : 3 * Real.exp (-(2 * v)) ≤ π * t ^ 2 * Real.exp (-(2 * v)) := by
    refine mul_le_mul_of_nonneg_right ?_ hE.le
    nlinarith
  linarith

theorem abs_gaussTest_le {t : ℝ} (ht : 1 ≤ t) (v : ℝ) :
    |gaussTest t v| ≤ 2 * Real.exp (-(3 / 2 * |v|)) := by
  rw [abs_of_pos (gaussTest_pos t v)]
  unfold gaussTest
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
    have h : Real.exp (-(π * t ^ 2 * Real.exp (-(2 * v)))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have : 0 ≤ π * t ^ 2 * Real.exp (-(2 * v)) := by positivity
        linarith)
    have hp := Real.exp_pos (-(3 / 2 * v))
    nlinarith
  · have hz := six_mul_abs_le ht hv
    have h : Real.exp (-(π * t ^ 2 * Real.exp (-(2 * v)))) ≤ Real.exp (-(3 * |v|)) :=
      Real.exp_le_exp.mpr (by
        have := abs_nonneg v
        linarith)
    have e : Real.exp (-(3 / 2 * |v|)) = Real.exp (-(3 / 2 * v)) * Real.exp (-(3 * |v|)) := by
      rw [← Real.exp_add, abs_of_nonpos hv]
      congr 1
      ring
    rw [e]
    have hp := Real.exp_pos (-(3 / 2 * v))
    calc 2 * Real.exp (-(3 / 2 * v)) * Real.exp (-(π * t ^ 2 * Real.exp (-(2 * v))))
        ≤ 2 * Real.exp (-(3 / 2 * v)) * Real.exp (-(3 * |v|)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring

theorem mul_exp_neg_le_one (y : ℝ) : y * Real.exp (-y) ≤ 1 := by
  have h := Real.add_one_le_exp y
  have hp := Real.exp_pos y
  rw [Real.exp_neg]
  have : y * (Real.exp y)⁻¹ = y / Real.exp y := rfl
  rw [this, div_le_one hp]
  linarith

theorem abs_deriv_gaussTest_le {t : ℝ} (ht : 1 ≤ t) (v : ℝ) :
    |deriv (gaussTest t) v| ≤ 11 * Real.exp (-(3 / 2 * |v|)) := by
  rw [(hasDerivAt_gaussTest t v).deriv]
  obtain ⟨z, hz⟩ : ∃ z, z = π * t ^ 2 * Real.exp (-(2 * v)) := ⟨_, rfl⟩
  have hz0 : 0 < z := by rw [hz]; positivity
  rw [← hz]
  have hY : gaussTest t v = 2 * Real.exp (-(3 / 2 * v)) * Real.exp (-z) := by
    rw [hz]
    rfl
  rw [abs_mul, abs_of_pos (gaussTest_pos t v), hY]
  have hlin : |-(3 / 2 : ℝ) + 2 * z| ≤ 3 / 2 + 2 * z := by
    rw [abs_le]
    constructor <;> linarith
  have hp := Real.exp_pos (-(3 / 2 * v))
  have hB : 2 * Real.exp (-(3 / 2 * v)) * Real.exp (-z) * |-(3 / 2 : ℝ) + 2 * z| ≤
      Real.exp (-(3 / 2 * v)) * ((3 + 4 * z) * Real.exp (-z)) := by
    calc 2 * Real.exp (-(3 / 2 * v)) * Real.exp (-z) * |-(3 / 2 : ℝ) + 2 * z|
        ≤ 2 * Real.exp (-(3 / 2 * v)) * Real.exp (-z) * (3 / 2 + 2 * z) :=
          mul_le_mul_of_nonneg_left hlin (by positivity)
      _ = _ := by ring
  refine hB.trans ?_
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
    have h1 := mul_exp_neg_le_one z
    have h2 : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : (3 + 4 * z) * Real.exp (-z) ≤ 11 := by nlinarith
    calc _ ≤ Real.exp (-(3 / 2 * v)) * 11 := mul_le_mul_of_nonneg_left h3 hp.le
      _ = _ := by ring
  · have hzv := six_mul_abs_le ht hv
    rw [← hz] at hzv
    have h1 := mul_exp_neg_le_one (z / 2)
    have h2 : Real.exp (-(z / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : (3 + 4 * z) * Real.exp (-(z / 2)) ≤ 11 := by nlinarith
    have h4 : Real.exp (-(z / 2)) ≤ Real.exp (-(3 * |v|)) := Real.exp_le_exp.mpr (by linarith)
    have e1 : Real.exp (-z) = Real.exp (-(z / 2)) * Real.exp (-(z / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(3 / 2 * |v|)) = Real.exp (-(3 / 2 * v)) * Real.exp (-(3 * |v|)) := by
      rw [← Real.exp_add, abs_of_nonpos hv]
      congr 1
      ring
    rw [e2, e1]
    have hq := Real.exp_pos (-(z / 2))
    calc Real.exp (-(3 / 2 * v)) * ((3 + 4 * z) * (Real.exp (-(z / 2)) * Real.exp (-(z / 2))))
        = Real.exp (-(3 / 2 * v)) * (((3 + 4 * z) * Real.exp (-(z / 2))) * Real.exp (-(z / 2))) := by
          ring
      _ ≤ Real.exp (-(3 / 2 * v)) * (11 * Real.exp (-(3 * |v|))) := by
          refine mul_le_mul_of_nonneg_left ?_ hp.le
          exact mul_le_mul h3 h4 hq.le (by norm_num)
      _ = _ := by ring

/-! ### The truncated Gaussian test: form and zero size -/

/-- The truncated Gaussian test `Y_{t,L}`. -/
def gaussTrunc (t L : ℝ) : ℝ → ℝ := truncTest (gaussTest t) L

theorem abs_gaussTrunc_le {t : ℝ} (ht : 1 ≤ t) (L u : ℝ) :
    |gaussTrunc t L u| ≤ 2 * Real.exp (-(3 / 2 * |u|)) :=
  (abs_truncTest_le _ L u).trans (abs_gaussTest_le ht u)

theorem exp_three_halves_le (u : ℝ) : Real.exp (-(3 / 2 * |u|)) ≤ Real.exp (-|u|) :=
  Real.exp_le_exp.mpr (by have := abs_nonneg u; linarith)

theorem abs_gaussTrunc_le_two {t : ℝ} (ht : 1 ≤ t) (L u : ℝ) : |gaussTrunc t L u| ≤ 2 := by
  refine (abs_gaussTrunc_le ht L u).trans ?_
  have : Real.exp (-(3 / 2 * |u|)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := abs_nonneg u; linarith)
  linarith

theorem integrable_exp_neg_abs' : Integrable fun u : ℝ => Real.exp (-|u|) :=
  integrable_exp_neg_abs

theorem integral_abs_gaussTrunc_le {t : ℝ} (ht : 1 ≤ t) (L : ℝ) :
    ∫ u, |gaussTrunc t L u| ≤ 2 * absMass := by
  have h : ∫ u, |gaussTrunc t L u| ≤ ∫ u, 2 * Real.exp (-|u|) :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (integrable_exp_neg_abs.const_mul 2) (Eventually.of_forall fun u => by
        have h1 := abs_gaussTrunc_le ht L u
        have h2 := exp_three_halves_le u
        simp only
        linarith)
  rwa [integral_const_mul] at h

/-- The zero size of the truncated Gaussian test is bounded uniformly in `t` and `L`. -/
theorem zero_size_gaussTrunc_le {Λc : ℝ} (hΛ0 : 0 ≤ Λc)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λc) {t : ℝ} (ht : 1 ≤ t) (L : ℝ) :
    (∫ u : ℝ, ‖((gaussTrunc t L u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|)) +
        ∫ u : ℝ, ‖((deriv (gaussTrunc t L) u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) ≤
      (13 + 4 * Λc) * absMass := by
  have hI := integrable_exp_neg_abs
  have hmul : ∀ u : ℝ, Real.exp (-(3 / 2 * |u|)) * Real.exp (1 / 2 * |u|) = Real.exp (-|u|) := by
    intro u
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : (∫ u : ℝ, ‖((gaussTrunc t L u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|)) ≤
      ∫ u : ℝ, 2 * Real.exp (-|u|) :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) (hI.const_mul 2)
      (Eventually.of_forall fun u => by
        simp only
        rw [Complex.norm_real, Real.norm_eq_abs, ← hmul u, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (abs_gaussTrunc_le ht L u) (Real.exp_pos _).le)
  have h2 : (∫ u : ℝ, ‖((deriv (gaussTrunc t L) u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|)) ≤
      ∫ u : ℝ, (11 + 4 * Λc) * Real.exp (-|u|) :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) (hI.const_mul _)
      (Eventually.of_forall fun u => by
        simp only
        rw [Complex.norm_real, Real.norm_eq_abs, ← hmul u, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        unfold gaussTrunc
        rw [deriv_truncTest (contDiff_gaussTest t)]
        refine (abs_truncTestDeriv_le hΛ L u).trans ?_
        have a1 := abs_deriv_gaussTest_le ht u
        have a2 := abs_gaussTest_le ht u
        have a3 : 2 * Λc * |gaussTest t u| ≤ 2 * Λc * (2 * Real.exp (-(3 / 2 * |u|))) :=
          mul_le_mul_of_nonneg_left a2 (by positivity)
        linarith)
  rw [integral_const_mul] at h1 h2
  change _ ≤ 2 * absMass at h1
  change _ ≤ (11 + 4 * Λc) * absMass at h2
  linarith

theorem contDiff_gaussTrunc (t L : ℝ) : ContDiff ℝ 2 (gaussTrunc t L) :=
  contDiff_truncTest (contDiff_gaussTest t) L

theorem hasCompactSupport_gaussTrunc (t L : ℝ) : HasCompactSupport (gaussTrunc t L) :=
  hasCompactSupport_truncTest _ L

/-- The form of the truncated Gaussian test on the cone. -/
theorem coneForm_gaussTrunc_le {Λc : ℝ} (hΛ0 : 0 ≤ Λc)
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λc) {t : ℝ} (ht : 1 ≤ t) {c L : ℝ}
    (hL0 : 0 ≤ L) (hc : L + 1 / 12 ≤ c) {lam : ℕ → ℝ} (hlam : WeilPositiveFullUpTo lam c) :
    coneForm lam (fun u => (gaussTrunc t L u : ℂ)) ≤
      (5 / 4) * zetaInvSqSum * ((13 + 4 * Λc) * absMass) ^ 2 +
        (Real.exp (L + L + 1) + 1) * ((4 * L + boxConst) * (2 * (2 * (2 * absMass)))) := by
  have hE := absMass_nonneg
  have hmain := coneForm_le_of_bounds (contDiff_gaussTrunc t L) (hasCompactSupport_gaussTrunc t L)
    hL0 (fun u hu => truncTest_eq_zero hu.le) (abs_gaussTrunc_le_two ht L)
    (integral_abs_gaussTrunc_le ht L) hc hlam
  refine hmain.trans ?_
  have hE0 : 0 ≤ (13 + 4 * Λc) * absMass := by positivity
  have hb : ∀ ρ : zetaZeroConfig.carrier,
      (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (gaussTrunc t L u : ℂ)) (gammaOf ρ)‖ ≤
          (13 + 4 * Λc) * absMass ∧
        (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (gaussTrunc t L u : ℂ))
          ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ (13 + 4 * Λc) * absMass := fun ρ => by
    obtain ⟨h1, h2⟩ := zero_bound_real_test (contDiff_gaussTrunc t L)
      (hasCompactSupport_gaussTrunc t L) ρ
    have h3 := zero_size_gaussTrunc_le hΛ0 hΛ ht L
    exact ⟨h1.trans h3, h2.trans h3⟩
  have hW := norm_W_le_of_zero_bounds hE0 hE0 (fun ρ => ⟨(hb ρ).1, (hb ρ).2⟩)
  have hre := (Complex.abs_re_le_norm _).trans hW
  have e : (5 / 4) * zetaInvSqSum * ((13 + 4 * Λc) * absMass) ^ 2 =
      (5 / 4) * zetaInvSqSum * (((13 + 4 * Λc) * absMass) * ((13 + 4 * Λc) * absMass)) := by ring
  rw [e]
  linarith

/-! ### The window correlation against the full correlation -/

/-- The decay constant of `Φ`. -/
def phiConst : ℝ := decayConst * gammaScale 0

theorem phiConst_nonneg : 0 ≤ phiConst := mul_nonneg decayConst_nonneg (gammaScale_nonneg 0)

theorem abs_phi_tail_le {X x : ℝ} (h : X ≤ |x|) :
    |𝔽 0 x| ≤ phiConst * doubleExpTail X * Real.exp (-(3 / 2 * |x|)) := by
  have h1 := abs_mul_exp_le_of_tail 0 h
  have hE := Real.exp_pos (1 / 2 * |x|)
  have e : Real.exp (-(3 / 2 * |x|)) * Real.exp (1 / 2 * |x|) = Real.exp (-|x|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine le_of_mul_le_mul_right ?_ hE
  refine h1.trans (le_of_eq ?_)
  unfold phiConst
  rw [← e]
  ring

theorem abs_phi_le (x : ℝ) : |𝔽 0 x| ≤ phiConst * Real.exp (-(3 / 2 * |x|)) := by
  have h := abs_phi_tail_le (abs_nonneg x)
  refine h.trans ?_
  have h1 := doubleExpTail_le_one 0
  have h2 := phiConst_nonneg
  have h3 := Real.exp_pos (-(3 / 2 * |x|))
  have : phiConst * doubleExpTail 0 ≤ phiConst * 1 := mul_le_mul_of_nonneg_left h1 h2
  nlinarith

theorem doubleExpTail_le_exp {X : ℝ} (hX : 0 ≤ X) : doubleExpTail X ≤ Real.exp (-(X / 4)) := by
  unfold doubleExpTail
  refine Real.exp_le_exp.mpr ?_
  have h1 := Real.add_one_le_exp (2 * X)
  have hpi := Real.pi_gt_three
  have h2 : 1 / 2 * Real.exp (2 * X) ≤ Real.pi / 6 * Real.exp (2 * X) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have e : -(Real.pi / 6) * Real.exp (2 * X) = -(Real.pi / 6 * Real.exp (2 * X)) := by ring
  rw [e]
  nlinarith

theorem abs_sub_truncTest_le (F : ℝ → ℝ) (L u : ℝ) : |F u - truncTest F L u| ≤ |F u| := by
  have e : F u - truncTest F L u = F u * (1 - bulkCutoff L u) := by
    unfold truncTest
    ring
  rw [e, abs_mul]
  have h1 := bulkCutoff_nonneg L u
  have h2 := bulkCutoff_le_one L u
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 - bulkCutoff L u)]
  exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)

theorem exp_neg_shift_le (s y : ℝ) :
    Real.exp (-(5 / 4 * |s - y|)) ≤ Real.exp (5 / 4 * |s|) * Real.exp (-(5 / 4 * |y|)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h : |y| ≤ |s| + |s - y| := by
    have := abs_sub_abs_le_abs_sub y s
    rw [abs_sub_comm y s] at this
    linarith
  linarith

/-- The mass of the slowest weight used in the comparison. -/
def quarterMass : ℝ := ∫ s : ℝ, Real.exp (-(1 / 4 * |s|))

theorem quarterMass_nonneg : 0 ≤ quarterMass := integral_nonneg fun _ => (Real.exp_pos _).le

theorem integrable_quarter : Integrable fun s : ℝ => Real.exp (-(1 / 4 * |s|)) :=
  integrable_exp_neg_mul_abs_fam (κ := 1 / 4) (by norm_num)

/-- **The truncations change the correlation by an exponentially small, decaying amount.** Uniformly in
`t ≥ 1`. -/
theorem abs_crossCorr_gauss_sub_le {t : ℝ} (ht : 1 ≤ t) {L : ℝ} (hL : 1 ≤ L) (y : ℝ) :
    |crossCorr (𝔽 0) (gaussTest t) y - crossCorr (truncTest (𝔽 0) L) (gaussTrunc t L) y| ≤
      4 * phiConst * quarterMass * Real.exp (-((L - 1) / 4)) * Real.exp (-(5 / 4 * |y|)) := by
  have hP := phiConst_nonneg
  obtain ⟨Cd, -, hFd⟩ := exists_decayBound_xiShiftedGammaTest
  have hFc : Continuous (𝔽 0) := (hFd 0).1.continuous
  have hYc : Continuous (gaussTest t) := (contDiff_gaussTest t).continuous
  have hXc : Continuous (truncTest (𝔽 0) L) := (contDiff_truncTest (hFd 0).1 L).continuous
  have hBc : Continuous (gaussTrunc t L) := (contDiff_gaussTrunc t L).continuous
  obtain ⟨ε, hε⟩ : ∃ ε, ε = Real.exp (-((L - 1) / 4)) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hε]; exact (Real.exp_pos _).le
  rw [← hε]
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = Real.exp (-(5 / 4 * |y|)) := ⟨_, rfl⟩
  have hY₀0 : 0 ≤ Y₀ := by rw [hY₀]; exact (Real.exp_pos _).le
  rw [← hY₀]
  -- the two weights
  have hshift : ∀ s : ℝ, Real.exp (-(3 / 2 * |s - y|)) ≤ Real.exp (5 / 4 * |s|) * Y₀ := fun s => by
    rw [hY₀]
    refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_shift_le s y)
    have := abs_nonneg (s - y)
    linarith
  have hweight : ∀ s : ℝ, Real.exp (-(3 / 2 * |s|)) * Real.exp (5 / 4 * |s|) =
      Real.exp (-(1 / 4 * |s|)) := fun s => by
    rw [← Real.exp_add]
    congr 1
    ring
  -- the first difference
  have hP1 : ∀ s : ℝ, |𝔽 0 s - truncTest (𝔽 0) L s| ≤ phiConst * ε * Real.exp (-(3 / 2 * |s|)) := by
    intro s
    rcases le_or_gt |s| (L - 1) with hs | hs
    · rw [truncTest_eq_self hs, sub_self, abs_zero]
      positivity
    · refine (abs_sub_truncTest_le _ L s).trans ((abs_phi_tail_le hs.le).trans ?_)
      have h1 := doubleExpTail_le_exp (by linarith : 0 ≤ L - 1)
      rw [← hε] at h1
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hP) (Real.exp_pos _).le
  -- the second difference
  have hP2 : ∀ v : ℝ, |gaussTest t v - gaussTrunc t L v| ≤ 2 * ε * Real.exp (-(5 / 4 * |v|)) := by
    intro v
    rcases le_or_gt |v| (L - 1) with hv | hv
    · unfold gaussTrunc
      rw [truncTest_eq_self hv, sub_self, abs_zero]
      positivity
    · refine (abs_sub_truncTest_le _ L v).trans ((abs_gaussTest_le ht v).trans ?_)
      have e : Real.exp (-(3 / 2 * |v|)) = Real.exp (-(|v| / 4)) * Real.exp (-(5 / 4 * |v|)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      have h1 : Real.exp (-(|v| / 4)) ≤ ε := by
        rw [hε]
        exact Real.exp_le_exp.mpr (by linarith)
      have h2 := Real.exp_pos (-(5 / 4 * |v|))
      nlinarith
  have hpt : ∀ s : ℝ, |𝔽 0 s * gaussTest t (s - y) - truncTest (𝔽 0) L s * gaussTrunc t L (s - y)| ≤
      4 * phiConst * ε * Y₀ * Real.exp (-(1 / 4 * |s|)) := by
    intro s
    have e : 𝔽 0 s * gaussTest t (s - y) - truncTest (𝔽 0) L s * gaussTrunc t L (s - y) =
        (𝔽 0 s - truncTest (𝔽 0) L s) * gaussTest t (s - y) +
          truncTest (𝔽 0) L s * (gaussTest t (s - y) - gaussTrunc t L (s - y)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hA : |truncTest (𝔽 0) L s| ≤ phiConst * Real.exp (-(3 / 2 * |s|)) :=
      (abs_truncTest_le _ L s).trans (abs_phi_le s)
    have hB1 : |gaussTest t (s - y)| ≤ 2 * (Real.exp (5 / 4 * |s|) * Y₀) :=
      (abs_gaussTest_le ht _).trans (mul_le_mul_of_nonneg_left (hshift s) (by norm_num))
    have hB2 : |gaussTest t (s - y) - gaussTrunc t L (s - y)| ≤
        2 * ε * (Real.exp (5 / 4 * |s|) * Y₀) := by
      refine (hP2 _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [hY₀]
      exact exp_neg_shift_le s y
    have hE1 := Real.exp_pos (5 / 4 * |s|)
    have hE2 := Real.exp_pos (-(3 / 2 * |s|))
    have t1 := mul_le_mul (hP1 s) hB1 (abs_nonneg _) (by positivity)
    have t2 := mul_le_mul hA hB2 (abs_nonneg _) (by positivity)
    rw [← hweight s]
    calc _ ≤ phiConst * ε * Real.exp (-(3 / 2 * |s|)) * (2 * (Real.exp (5 / 4 * |s|) * Y₀)) +
          phiConst * Real.exp (-(3 / 2 * |s|)) * (2 * ε * (Real.exp (5 / 4 * |s|) * Y₀)) :=
          add_le_add t1 t2
      _ = _ := by ring
  have hi1 : Integrable fun s => 𝔽 0 s * gaussTest t (s - y) := by
    refine (integrable_quarter.const_mul (2 * phiConst)).mono'
      (hFc.mul (hYc.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_phi_le s
    have h2 := abs_gaussTest_le ht (s - y)
    have h3 : Real.exp (-(3 / 2 * |s - y|)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := abs_nonneg (s - y); linarith)
    have h4 : Real.exp (-(3 / 2 * |s|)) ≤ Real.exp (-(1 / 4 * |s|)) :=
      Real.exp_le_exp.mpr (by have := abs_nonneg s; linarith)
    have h5 : |gaussTest t (s - y)| ≤ 2 := by linarith
    have h6 : |𝔽 0 s| ≤ phiConst * Real.exp (-(1 / 4 * |s|)) :=
      h1.trans (mul_le_mul_of_nonneg_left h4 hP)
    calc |𝔽 0 s| * |gaussTest t (s - y)| ≤ (phiConst * Real.exp (-(1 / 4 * |s|))) * 2 :=
          mul_le_mul h6 h5 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hi2 : Integrable fun s => truncTest (𝔽 0) L s * gaussTrunc t L (s - y) :=
    integrable_translate_prod hXc (hasCompactSupport_truncTest _ L) hBc y
  unfold crossCorr
  rw [← integral_sub hi1 hi2]
  refine (abs_integral_le_integral_abs).trans ?_
  have hmono : ∫ s, |𝔽 0 s * gaussTest t (s - y) - truncTest (𝔽 0) L s * gaussTrunc t L (s - y)| ≤
      ∫ s, 4 * phiConst * ε * Y₀ * Real.exp (-(1 / 4 * |s|)) :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (integrable_quarter.const_mul _) (Eventually.of_forall hpt)
  rw [integral_const_mul] at hmono
  refine hmono.trans (le_of_eq ?_)
  unfold quarterMass
  ring

/-! ### The window defect -/

/-- The deviation of `λ` from `Λ` on the integers inside the box, extended by zero. -/
def windowDefect (lam : ℕ → ℝ) (L : ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n ∧ (n : ℝ) ≤ Real.exp (2 * L) then lam n - (ArithmeticFunction.vonMangoldt n : ℝ) else 0

theorem windowDefect_one (lam : ℕ → ℝ) (L : ℝ) : windowDefect lam L 1 = 0 := by
  unfold windowDefect
  simp

theorem abs_windowDefect_le {lam : ℕ → ℝ} {c L : ℝ} (hL0 : 0 ≤ L) (hLc : L + 1 / 12 ≤ c)
    (h : WeilPositiveFullUpTo lam c) (n : ℕ) (_hn : 1 ≤ n) :
    |windowDefect lam L n| ≤ (4 * L + boxConst + 1) * Real.sqrt n := by
  have hC := boxConst_nonneg
  have hs := Real.sqrt_nonneg (n : ℝ)
  unfold windowDefect
  split_ifs with hin
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have h1 := abs_sub_vonMangoldt_div_sqrt_le h hLc hin.1 hin.2
    rw [div_le_iff₀ hsp] at h1
    nlinarith
  · rw [abs_zero]
    positivity

/-- The reading of a sequence against the Gaussian test, as a real series. -/
theorem readS_ofReal {δ : ℕ → ℝ} {V : ℝ} (hV : 0 ≤ V) (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n)
    {t : ℝ} (ht : 1 ≤ t) :
    readS δ (t : ℂ) = ((∑' n : ℕ, δ (n + 1) *
      ((crossCorr (𝔽 0) (gaussTest t) (Real.log ((n + 1 : ℕ) : ℝ)) +
        crossCorr (𝔽 0) (gaussTest t) (-Real.log ((n + 1 : ℕ) : ℝ))) /
          Real.sqrt ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
  have hre : 1 ≤ ((t : ℂ)).re := by simpa using ht
  have hsum := summable_readS hV hδ hre
  unfold readS
  rw [hsum.tsum_prod, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  change ∑' k : ℕ, (δ (n + 1) : ℂ) * kerC ((idxN (n, k) : ℕ) : ℝ) (t : ℂ) = _
  rw [tsum_mul_left]
  have hk := hasSum_atomReading (n := n + 1) (Nat.succ_pos n) ht
  have hfun : (fun k : ℕ => kerC ((idxN (n, k) : ℕ) : ℝ) (t : ℂ)) = fun k : ℕ =>
      ((ratKer (((k + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) t +
        expKer (((k + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) t : ℝ) : ℂ) := by
    funext k
    rw [kerC_ofReal]
    unfold idxN
    simp only
    rw [Nat.cast_mul]
  have := (Complex.hasSum_ofReal.mpr hk).tsum_eq
  rw [hfun, this]
  push_cast
  ring

theorem exp_neg_five_fourths_log (n : ℕ) :
    Real.exp (-(5 / 4 * |Real.log ((n + 1 : ℕ) : ℝ)|)) = 1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ) := by
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    push_cast
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  rw [abs_of_nonneg (Real.log_nonneg hn)]
  have e : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [e]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.rpow_def_of_pos hpos, Real.exp_neg, one_div]
  congr 2
  ring

/-- The sum over the atoms of the decaying weight. -/
def atomMass : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ)

theorem summable_atomMass : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ) := by
  have := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 5 / 4))
  simpa using this

theorem atomMass_nonneg : 0 ≤ atomMass := tsum_nonneg fun n => by positivity

/-! ### The reading on the cone -/

/-- `e^{3c/2} √(ceiling(c)) ≤ K e^{−c}`: the near-null vector beats any fixed exponential. -/
theorem exp_mul_sqrt_ceiling_le {c : ℝ} (hc : 2 ≤ c) :
    Real.exp (3 / 2 * c) * Real.sqrt (marginCeiling c) ≤
      Real.exp (13 / 3 + 8) * Real.exp (-c) := by
  have hs : Real.sqrt (marginCeiling c) =
      Real.exp ((3 * c - Real.pi / 6 * Real.exp (2 * (c - 13 / 12))) / 2) := by
    unfold marginCeiling
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [hs, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  obtain ⟨y, hy⟩ : ∃ y, y = 2 * (c - 13 / 12) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  rw [← hy]
  have h1 := Real.quadratic_le_exp_of_nonneg hy0
  have hpi := Real.pi_gt_three
  have h2 : 1 / 2 * Real.exp y ≤ Real.pi / 6 * Real.exp y :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hc' : c = y / 2 + 13 / 12 := by rw [hy]; ring
  rw [hc']
  nlinarith [sq_nonneg (y - 8)]

/-- **The Gaussian reading is small on the cone.** Uniformly in `t ≥ 1`, with the window defect of any
`λ ∈ 𝒜(c)`. -/
theorem exists_norm_readS_windowDefect_le :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (c : ℝ) (lam : ℕ → ℝ), 2 ≤ c → WeilPositiveFullUpTo lam c →
      ∀ t : ℝ, 1 ≤ t → ‖readS (windowDefect lam (c - 1 / 12)) (t : ℂ)‖ ≤
        K₁ * (1 + c) * Real.exp (-(c / 4)) := by
  obtain ⟨C₀, hC₀, hpin⟩ := exists_uniform_pinning
  obtain ⟨Λc, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hbox := boxConst_nonneg
  have hmass := absMass_nonneg
  have hZs := zetaInvSqSum_nonneg
  have hP := phiConst_nonneg
  have hQ := quarterMass_nonneg
  have hA := atomMass_nonneg
  obtain ⟨E₀, hE₀⟩ : ∃ E₀, E₀ = (13 + 4 * Λc) * absMass := ⟨_, rfl⟩
  have hE₀0 : 0 ≤ E₀ := by rw [hE₀]; positivity
  obtain ⟨A₃, hA₃⟩ : ∃ A₃, A₃ = (5 / 4) * zetaInvSqSum * E₀ ^ 2 +
    2 * Real.exp 1 * ((4 + boxConst) * (8 * absMass)) := ⟨_, rfl⟩
  have hA₃0 : 0 ≤ A₃ := by rw [hA₃]; positivity
  obtain ⟨D, hD⟩ : ∃ D, D = 4 * phiConst * quarterMass := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  refine ⟨C₀ * (E₀ + Real.sqrt A₃) * Real.exp (13 / 3 + 8) +
    (5 + boxConst) * (2 * D * Real.exp (13 / 48) * atomMass), by positivity, ?_⟩
  intro c lam hc hlam t ht
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = c - 1 / 12 := ⟨_, rfl⟩
  rw [← hL]
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hLc : L + 1 / 12 ≤ c := by rw [hL]; linarith
  have hLle : L ≤ c := by rw [hL]; linarith
  obtain ⟨V, hV⟩ : ∃ V, V = 4 * L + boxConst + 1 := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  have hVc : V ≤ (5 + boxConst) * (1 + c) := by rw [hV]; nlinarith
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = windowDefect lam L := ⟨_, rfl⟩
  rw [← hδdef]
  have hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n := by
    intro n hn
    rw [hδdef, hV]
    exact abs_windowDefect_le hL0 hLc hlam n hn
  have hδzero : ∀ n : ℕ, Real.exp (2 * L) < n → δ n = 0 := by
    intro n hn
    rw [hδdef]
    unfold windowDefect
    exact if_neg fun h => absurd h.2 (not_le.mpr hn)
  -- the pinned reading
  obtain ⟨Y, hY⟩ : ∃ Y, Y = gaussTrunc t L := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = truncTest (𝔽 0) L := ⟨_, rfl⟩
  have hform := coneForm_gaussTrunc_le hΛ0 hΛ ht hL0 hLc hlam
  rw [← hE₀] at hform
  obtain ⟨CY, hCY⟩ : ∃ CY, CY = A₃ * Real.exp (3 * c) := ⟨_, rfl⟩
  have hCY0 : 0 ≤ CY := by rw [hCY]; positivity
  have hformle : (5 / 4) * zetaInvSqSum * E₀ ^ 2 + (Real.exp (L + L + 1) + 1) *
      ((4 * L + boxConst) * (2 * (2 * (2 * absMass)))) ≤ CY := by
    have hrhs : CY = (5 / 4) * zetaInvSqSum * E₀ ^ 2 * Real.exp (3 * c) +
        2 * Real.exp 1 * ((4 + boxConst) * (8 * absMass)) * Real.exp (3 * c) := by
      rw [hCY, hA₃]
      ring
    rw [hrhs]
    have he3 : 1 ≤ Real.exp (3 * c) := Real.one_le_exp (by positivity)
    have h1 : (5 / 4) * zetaInvSqSum * E₀ ^ 2 ≤ (5 / 4) * zetaInvSqSum * E₀ ^ 2 * Real.exp (3 * c) :=
      le_mul_of_one_le_right (by positivity) he3
    have h2 : Real.exp (L + L + 1) + 1 ≤ 2 * Real.exp 1 * Real.exp (2 * c) := by
      have ha : Real.exp (L + L + 1) ≤ Real.exp 1 * Real.exp (2 * c) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have hb : (1 : ℝ) ≤ Real.exp 1 * Real.exp (2 * c) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      linarith
    have h3 : 4 * L + boxConst ≤ (4 + boxConst) * Real.exp c := by
      have h4 := Real.add_one_le_exp c
      nlinarith
    have e3 : Real.exp (3 * c) = Real.exp (2 * c) * Real.exp c := by
      rw [← Real.exp_add]
      ring_nf
    have hn : 0 ≤ 4 * L + boxConst := by positivity
    have h5 : (Real.exp (L + L + 1) + 1) * ((4 * L + boxConst) * (2 * (2 * (2 * absMass)))) ≤
        (2 * Real.exp 1 * Real.exp (2 * c)) * (((4 + boxConst) * Real.exp c) * (8 * absMass)) := by
      have e8 : 2 * (2 * (2 * absMass)) = 8 * absMass := by ring
      rw [e8]
      exact mul_le_mul h2 (mul_le_mul_of_nonneg_right h3 (by positivity)) (by positivity)
        (by positivity)
    refine add_le_add h1 (h5.trans (le_of_eq ?_))
    rw [e3]
    ring
  have hzero : ∀ ρ : zetaZeroConfig.carrier,
      (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) (gammaOf ρ)‖ ≤ E₀ ∧
        (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (Y u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤ E₀ := by
    intro ρ
    rw [hY, hE₀]
    obtain ⟨h1, h2⟩ := zero_bound_real_test (contDiff_gaussTrunc t L)
      (hasCompactSupport_gaussTrunc t L) ρ
    have h3 := zero_size_gaussTrunc_le hΛ0 hΛ ht L
    exact ⟨h1.trans h3, h2.trans h3⟩
  have hYs : ∀ u, c < |u| → Y u = 0 := fun u hu => by
    rw [hY]
    exact truncTest_eq_zero (hLle.trans hu.le)
  have hpinned := hpin c lam Y CY E₀ (by linarith) hlam
    (by rw [hY]; exact contDiff_gaussTrunc t L) (by rw [hY]; exact hasCompactSupport_gaussTrunc t L)
    hYs hCY0 (by rw [hY]; exact hform.trans hformle) hE₀0 hzero
  rw [← hL, ← hX] at hpinned
  -- the size of the pinned reading
  have hsqrt : Real.sqrt CY = Real.sqrt A₃ * Real.exp (3 / 2 * c) := by
    rw [hCY, Real.sqrt_mul hA₃0]
    congr 1
    rw [show Real.exp (3 * c) = Real.exp (3 / 2 * c) * Real.exp (3 / 2 * c) by
      rw [← Real.exp_add]; ring_nf, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hsz : C₀ * (E₀ + Real.sqrt CY) * Real.sqrt (marginCeiling c) ≤
      C₀ * (E₀ + Real.sqrt A₃) * Real.exp (13 / 3 + 8) * Real.exp (-c) := by
    have h32 : 1 ≤ Real.exp (3 / 2 * c) := Real.one_le_exp (by positivity)
    have h1 : E₀ + Real.sqrt CY ≤ (E₀ + Real.sqrt A₃) * Real.exp (3 / 2 * c) := by
      rw [hsqrt, add_mul]
      have := le_mul_of_one_le_right hE₀0 h32
      linarith
    have h2 := exp_mul_sqrt_ceiling_le hc
    have hsM := Real.sqrt_nonneg (marginCeiling c)
    have hsA := Real.sqrt_nonneg A₃
    calc C₀ * (E₀ + Real.sqrt CY) * Real.sqrt (marginCeiling c)
        ≤ C₀ * ((E₀ + Real.sqrt A₃) * Real.exp (3 / 2 * c)) * Real.sqrt (marginCeiling c) := by
          gcongr
      _ = C₀ * (E₀ + Real.sqrt A₃) * (Real.exp (3 / 2 * c) * Real.sqrt (marginCeiling c)) := by ring
      _ ≤ C₀ * (E₀ + Real.sqrt A₃) * (Real.exp (13 / 3 + 8) * Real.exp (-c)) := by gcongr
      _ = _ := by ring
  -- the two series
  obtain ⟨g, hg⟩ : ∃ g, g = crossCorr (𝔽 0) (gaussTest t) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = crossCorr X Y := ⟨_, rfl⟩
  have hGzero : ∀ y : ℝ, L + L < |y| → G y = 0 := by
    intro y hy
    rw [hG, hX, hY]
    exact crossCorr_eq_zero (fun u hu => truncTest_eq_zero hu.le) (fun u hu => truncTest_eq_zero hu.le) hy
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈Real.exp (2 * L)⌉₊ := ⟨_, rfl⟩
  have hNge : Real.exp (2 * L) ≤ N := by rw [hN]; exact Nat.le_ceil _
  have hδN : ∀ n, n ∉ Finset.range N → δ (n + 1) = 0 := by
    intro n hn
    refine hδzero _ ?_
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast not_lt.mp (by simpa using hn)
    push_cast
    linarith
  have hS1 : Summable fun n : ℕ => δ (n + 1) * ((g (Real.log ((n + 1 : ℕ) : ℝ)) +
      g (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
    summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by rw [hδN n hn, zero_mul]
  have hS2 : Summable fun n : ℕ => δ (n + 1) * ((G (Real.log ((n + 1 : ℕ) : ℝ)) +
      G (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
    summable_of_ne_finset_zero (s := Finset.range N) fun n hn => by rw [hδN n hn, zero_mul]
  -- the atom pairing is the second series
  have hpair : atomPairing (fun n => lam n - (ArithmeticFunction.vonMangoldt n : ℝ)) G =
      ∑' n : ℕ, δ (n + 1) * ((G (Real.log ((n + 1 : ℕ) : ℝ)) +
        G (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
    unfold atomPairing
    have hterm : ∀ n : ℕ, (if 2 ≤ n + 1 then (lam (n + 1) -
        (ArithmeticFunction.vonMangoldt (n + 1) : ℝ)) / Real.sqrt ((n + 1 : ℕ) : ℝ) else 0) *
        (G (Real.log ((n + 1 : ℕ) : ℝ)) + G (-Real.log ((n + 1 : ℕ) : ℝ))) =
        δ (n + 1) * ((G (Real.log ((n + 1 : ℕ) : ℝ)) +
          G (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
      intro n
      by_cases h2 : 2 ≤ n + 1
      · rw [if_pos h2]
        by_cases hle : ((n + 1 : ℕ) : ℝ) ≤ Real.exp (2 * L)
        · have hd : δ (n + 1) = lam (n + 1) - (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) := by
            rw [hδdef]
            unfold windowDefect
            exact if_pos ⟨h2, hle⟩
          rw [hd]
          ring
        · have hd : δ (n + 1) = 0 := hδzero _ (not_le.mp hle)
          have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
          have hlt : 2 * L < Real.log ((n + 1 : ℕ) : ℝ) :=
            (Real.lt_log_iff_exp_lt hpos).mpr (not_le.mp hle)
          have hab : L + L < |Real.log ((n + 1 : ℕ) : ℝ)| := by
            have := le_abs_self (Real.log ((n + 1 : ℕ) : ℝ))
            linarith
          have hab' : L + L < |-Real.log ((n + 1 : ℕ) : ℝ)| := by rwa [abs_neg]
          rw [hd, hGzero _ hab, hGzero _ hab']
          simp
      · have hn0 : n = 0 := by omega
        subst hn0
        rw [if_neg h2]
        have hd : δ (0 + 1) = 0 := by
          rw [hδdef]
          exact windowDefect_one lam L
        rw [hd]
        simp
    have hsumm : Summable fun n : ℕ => (if 2 ≤ n then (lam n -
        (ArithmeticFunction.vonMangoldt n : ℝ)) / Real.sqrt n else 0) *
        (G (Real.log n) + G (-Real.log n)) := by
      refine (summable_nat_add_iff 1).mp ?_
      simp only [hterm]
      exact hS2
    rw [hsumm.tsum_eq_zero_add]
    simp only [hterm]
    simp
  -- the comparison
  have hdiff : ∀ n : ℕ, ‖δ (n + 1) * ((g (Real.log ((n + 1 : ℕ) : ℝ)) +
      g (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)) -
      δ (n + 1) * ((G (Real.log ((n + 1 : ℕ) : ℝ)) +
      G (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ))‖ ≤
      V * (2 * (D * Real.exp (-((L - 1) / 4)))) * (1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ)) := by
    intro n
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hsp : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hpos
    have hc₁ := abs_crossCorr_gauss_sub_le ht hL1 (Real.log ((n + 1 : ℕ) : ℝ))
    have hc₂ := abs_crossCorr_gauss_sub_le ht hL1 (-Real.log ((n + 1 : ℕ) : ℝ))
    rw [abs_neg, exp_neg_five_fourths_log, ← hD] at hc₂
    rw [exp_neg_five_fourths_log, ← hD] at hc₁
    rw [← hX, ← hY, ← hG, ← hg] at hc₁ hc₂
    have e : δ (n + 1) * ((g (Real.log ((n + 1 : ℕ) : ℝ)) + g (-Real.log ((n + 1 : ℕ) : ℝ))) /
        Real.sqrt ((n + 1 : ℕ) : ℝ)) - δ (n + 1) * ((G (Real.log ((n + 1 : ℕ) : ℝ)) +
        G (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)) =
        (δ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)) * ((g (Real.log ((n + 1 : ℕ) : ℝ)) -
          G (Real.log ((n + 1 : ℕ) : ℝ))) + (g (-Real.log ((n + 1 : ℕ) : ℝ)) -
          G (-Real.log ((n + 1 : ℕ) : ℝ)))) := by
      field_simp
      ring
    rw [e, Real.norm_eq_abs, abs_mul]
    have hd : |δ (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ)| ≤ V := by
      rw [abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
      exact hδ (n + 1) (Nat.succ_pos n)
    have hsum := abs_add_le (g (Real.log ((n + 1 : ℕ) : ℝ)) - G (Real.log ((n + 1 : ℕ) : ℝ)))
      (g (-Real.log ((n + 1 : ℕ) : ℝ)) - G (-Real.log ((n + 1 : ℕ) : ℝ)))
    have hq : 0 ≤ D * Real.exp (-((L - 1) / 4)) * (1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ)) := by positivity
    calc _ ≤ V * (D * Real.exp (-((L - 1) / 4)) * (1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ)) +
          D * Real.exp (-((L - 1) / 4)) * (1 / ((n : ℝ) + 1) ^ (5 / 4 : ℝ))) :=
          mul_le_mul hd (hsum.trans (add_le_add hc₁ hc₂)) (abs_nonneg _) hV0
      _ = _ := by ring
  have hcomp : ‖∑' n : ℕ, (δ (n + 1) * ((g (Real.log ((n + 1 : ℕ) : ℝ)) +
      g (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)) -
      δ (n + 1) * ((G (Real.log ((n + 1 : ℕ) : ℝ)) +
      G (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)))‖ ≤
      V * (2 * (D * Real.exp (-((L - 1) / 4)))) * atomMass :=
    tsum_of_norm_bounded (summable_atomMass.hasSum.mul_left _) hdiff
  rw [hS1.tsum_sub hS2] at hcomp
  -- assembling
  rw [readS_ofReal hV0 hδ ht, Complex.norm_real, Real.norm_eq_abs, ← hg]
  rw [← hG] at hpinned
  rw [hpair] at hpinned
  have htot := abs_sub_abs_le_abs_sub
    (∑' n : ℕ, δ (n + 1) * ((g (Real.log ((n + 1 : ℕ) : ℝ)) +
      g (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)))
    (∑' n : ℕ, δ (n + 1) * ((G (Real.log ((n + 1 : ℕ) : ℝ)) +
      G (-Real.log ((n + 1 : ℕ) : ℝ))) / Real.sqrt ((n + 1 : ℕ) : ℝ)))
  rw [Real.norm_eq_abs] at hcomp
  have hexp1 : Real.exp (-((L - 1) / 4)) = Real.exp (13 / 48) * Real.exp (-(c / 4)) := by
    rw [← Real.exp_add, hL]
    congr 1
    ring
  have hexp2 : Real.exp (-c) ≤ Real.exp (-(c / 4)) := Real.exp_le_exp.mpr (by linarith)
  have hEc := Real.exp_pos (-(c / 4))
  have hK1 : 0 ≤ C₀ * (E₀ + Real.sqrt A₃) * Real.exp (13 / 3 + 8) := by positivity
  have hb1 : C₀ * (E₀ + Real.sqrt A₃) * Real.exp (13 / 3 + 8) * Real.exp (-c) ≤
      C₀ * (E₀ + Real.sqrt A₃) * Real.exp (13 / 3 + 8) * ((1 + c) * Real.exp (-(c / 4))) := by
    refine mul_le_mul_of_nonneg_left ?_ hK1
    have : Real.exp (-(c / 4)) ≤ (1 + c) * Real.exp (-(c / 4)) :=
      le_mul_of_one_le_left hEc.le (by linarith)
    linarith
  have hb2 : V * (2 * (D * Real.exp (-((L - 1) / 4)))) * atomMass ≤
      (5 + boxConst) * (2 * D * Real.exp (13 / 48) * atomMass) * ((1 + c) * Real.exp (-(c / 4))) := by
    rw [hexp1]
    have hq : 0 ≤ 2 * D * Real.exp (13 / 48) * atomMass * Real.exp (-(c / 4)) := by positivity
    calc V * (2 * (D * (Real.exp (13 / 48) * Real.exp (-(c / 4))))) * atomMass
        = V * (2 * D * Real.exp (13 / 48) * atomMass * Real.exp (-(c / 4))) := by ring
      _ ≤ ((5 + boxConst) * (1 + c)) * (2 * D * Real.exp (13 / 48) * atomMass * Real.exp (-(c / 4))) :=
          mul_le_mul_of_nonneg_right hVc hq
      _ = _ := by ring
  have e4 : (C₀ * (E₀ + Real.sqrt A₃) * Real.exp (13 / 3 + 8) +
      (5 + boxConst) * (2 * D * Real.exp (13 / 48) * atomMass)) * (1 + c) * Real.exp (-(c / 4)) =
      C₀ * (E₀ + Real.sqrt A₃) * Real.exp (13 / 3 + 8) * ((1 + c) * Real.exp (-(c / 4))) +
      (5 + boxConst) * (2 * D * Real.exp (13 / 48) * atomMass) * ((1 + c) * Real.exp (-(c / 4))) := by
    ring
  rw [e4]
  linarith

/-! ### Effective uniqueness -/

/-- **Effective uniqueness of the window cone.** There are absolute constants `C, K` with
`|λ(n) − Λ(n)| ≤ C exp(K n − c/1104)` for every `c ≥ 2`, `λ ∈ 𝒜(c)` and every integer `n ≥ 2` inside the
box `n ≤ e^{2(c − 1/12)}`. -/
theorem exists_abs_sub_vonMangoldt_le_exp :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (c : ℝ) (lam : ℕ → ℝ), 2 ≤ c → WeilPositiveFullUpTo lam c →
      ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ Real.exp (2 * (c - 1 / 12)) →
        |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| ≤ C * Real.exp (K * n - c / 1104) := by
  obtain ⟨CH, KH, hCH, hKH, hHam⟩ := exists_abs_le_of_readS_small
  obtain ⟨K₁, hK₁, hread⟩ := exists_norm_readS_windowDefect_le
  have hbox := boxConst_nonneg
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = 8 * K₁ + 1 := ⟨_, rfl⟩
  have hK₂1 : 1 ≤ K₂ := by rw [hK₂]; linarith
  have hK₂0 : 0 ≤ K₂ := by linarith
  refine ⟨(CH + 1) * ((5 + boxConst) * 1104) * K₂ ^ (1 / 69 : ℝ), KH + 1, by positivity, by positivity, ?_⟩
  intro c lam hc hlam n hn hnin
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨L, hL⟩ : ∃ L, L = c - 1 / 12 := ⟨_, rfl⟩
  rw [← hL] at hnin
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  have hLc : L + 1 / 12 ≤ c := by rw [hL]; linarith
  obtain ⟨V, hV⟩ : ∃ V, V = 4 * L + boxConst + 1 := ⟨_, rfl⟩
  have hV1 : 1 ≤ V := by rw [hV]; linarith
  have hV0 : 0 ≤ V := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = windowDefect lam L := ⟨_, rfl⟩
  have hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n := fun m hm => by
    rw [hδdef, hV]
    exact abs_windowDefect_le hL0 hLc hlam m hm
  have hδ1 : δ 1 = 0 := by rw [hδdef]; exact windowDefect_one lam L
  have hδn : δ n = lam n - (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [hδdef]
    unfold windowDefect
    exact if_pos ⟨hn, hnin⟩
  obtain ⟨η, hη⟩ : ∃ η, η = K₂ * Real.exp (-(c / 8)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hS : ∀ t : ℝ, 2 ≤ t → ‖readS δ (t : ℂ)‖ ≤ η := by
    intro t ht
    rw [hδdef, hL]
    refine (hread c lam hc hlam t (by linarith)).trans ?_
    have h1 : 1 + c ≤ 8 * Real.exp (c / 8) := by
      have := Real.add_one_le_exp (c / 8)
      linarith
    have e : Real.exp (c / 8) * Real.exp (-(c / 4)) = Real.exp (-(c / 8)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hE := Real.exp_pos (-(c / 4))
    rw [hη, hK₂]
    calc K₁ * (1 + c) * Real.exp (-(c / 4))
        ≤ K₁ * (8 * Real.exp (c / 8)) * Real.exp (-(c / 4)) := by gcongr
      _ = 8 * K₁ * (Real.exp (c / 8) * Real.exp (-(c / 4))) := by ring
      _ = 8 * K₁ * Real.exp (-(c / 8)) := by rw [e]
      _ ≤ _ := by
          have := Real.exp_pos (-(c / 8))
          nlinarith
  have hn1 : 1 ≤ n := by omega
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- both regimes of `η`
  have hbound : |δ n| ≤ (CH + 1) * V * η ^ (1 / 69 : ℝ) * Real.exp ((KH + 1) * n) := by
    have hp : 0 < η ^ (1 / 69 : ℝ) := Real.rpow_pos_of_pos hη0 _
    rcases le_or_gt η 1 with h1 | h1
    · have h := hHam δ V η hV1 hη0 h1 hδ1 hδ hS n hn1
      refine h.trans ?_
      have ha : CH * V * η ^ (1 / 69 : ℝ) ≤ (CH + 1) * V * η ^ (1 / 69 : ℝ) := by
        gcongr
        linarith
      have hb : Real.exp (KH * n) ≤ Real.exp ((KH + 1) * n) :=
        Real.exp_le_exp.mpr (by nlinarith)
      exact mul_le_mul ha hb (Real.exp_pos _).le (by positivity)
    · have h := hδ n hn1
      have hpow : 1 ≤ η ^ (1 / 69 : ℝ) := Real.one_le_rpow h1.le (by norm_num)
      have hsq : Real.sqrt n ≤ Real.exp ((KH + 1) * n) := by
        have h2 : Real.sqrt n ≤ (n : ℝ) + 1 := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
        have h3 := Real.add_one_le_exp (n : ℝ)
        have h4 : Real.exp (n : ℝ) ≤ Real.exp ((KH + 1) * n) :=
          Real.exp_le_exp.mpr (by nlinarith)
        linarith
      have hE := Real.exp_pos ((KH + 1) * (n : ℝ))
      calc |δ n| ≤ V * Real.exp ((KH + 1) * n) :=
            h.trans (mul_le_mul_of_nonneg_left hsq hV0)
        _ ≤ (CH + 1) * V * η ^ (1 / 69 : ℝ) * Real.exp ((KH + 1) * n) := by
            refine mul_le_mul_of_nonneg_right ?_ hE.le
            have hCV : V ≤ (CH + 1) * V := le_mul_of_one_le_left hV0 (by linarith)
            exact hCV.trans (le_mul_of_one_le_right (by positivity) hpow)
  rw [← hδn]
  refine hbound.trans ?_
  have hηp : η ^ (1 / 69 : ℝ) = K₂ ^ (1 / 69 : ℝ) * Real.exp (-(c / 552)) := by
    rw [hη, Real.mul_rpow hK₂0 (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  have hVle : V ≤ (5 + boxConst) * 1104 * Real.exp (c / 1104) := by
    have h1 := Real.add_one_le_exp (c / 1104)
    have h2 : V ≤ (5 + boxConst) * (1 + c) := by
      rw [hV, hL]
      nlinarith
    have h3 : 1 + c ≤ 1104 * Real.exp (c / 1104) := by linarith
    calc V ≤ (5 + boxConst) * (1 + c) := h2
      _ ≤ (5 + boxConst) * (1104 * Real.exp (c / 1104)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hexp : Real.exp (c / 1104) * Real.exp (-(c / 552)) * Real.exp ((KH + 1) * n) =
      Real.exp ((KH + 1) * n - c / 1104) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hηp, ← hexp]
  have hK₂p : 0 ≤ K₂ ^ (1 / 69 : ℝ) := by positivity
  have hE1 := Real.exp_pos (-(c / 552))
  have hE2 := Real.exp_pos ((KH + 1) * (n : ℝ))
  calc (CH + 1) * V * (K₂ ^ (1 / 69 : ℝ) * Real.exp (-(c / 552))) * Real.exp ((KH + 1) * n)
      ≤ (CH + 1) * ((5 + boxConst) * 1104 * Real.exp (c / 1104)) *
          (K₂ ^ (1 / 69 : ℝ) * Real.exp (-(c / 552))) * Real.exp ((KH + 1) * n) := by
        gcongr
    _ = _ := by ring

/-- **The cone pins every integer up to a fixed multiple of the aperture.** With the constants of the main
theorem, all `2 ≤ n` with `K n ≤ c/2208` inside the box satisfy `|λ(n) − Λ(n)| ≤ C exp(−c/2208)`. -/
theorem exists_abs_sub_vonMangoldt_le_of_le_aperture :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (c : ℝ) (lam : ℕ → ℝ), 2 ≤ c → WeilPositiveFullUpTo lam c →
      ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ Real.exp (2 * (c - 1 / 12)) → K * n ≤ c / 2208 →
        |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| ≤ C * Real.exp (-(c / 2208)) := by
  obtain ⟨C, K, hC, hK, h⟩ := exists_abs_sub_vonMangoldt_le_exp
  refine ⟨C, K, hC, hK, fun c lam hc hlam n hn hin hle => ?_⟩
  refine (h c lam hc hlam n hn hin).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact Real.exp_le_exp.mpr (by linarith)

/-- **The bands close at a rate.** Every two points of `𝒜(c)` agree at `n` up to `2 C exp(K n − c/1104)`. -/
theorem exists_abs_sub_le_of_mem_cone :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (c : ℝ) (lam lam' : ℕ → ℝ), 2 ≤ c → WeilPositiveFullUpTo lam c →
      WeilPositiveFullUpTo lam' c → ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ Real.exp (2 * (c - 1 / 12)) →
        |lam n - lam' n| ≤ C * Real.exp (K * n - c / 1104) := by
  obtain ⟨C, K, hC, hK, h⟩ := exists_abs_sub_vonMangoldt_le_exp
  refine ⟨2 * C, K, by positivity, hK, fun c lam lam' hc h₁ h₂ n hn hin => ?_⟩
  have a := h c lam hc h₁ n hn hin
  have b := h c lam' hc h₂ n hn hin
  have t := abs_sub_le (lam n) (ArithmeticFunction.vonMangoldt n : ℝ) (lam' n)
  rw [abs_sub_comm (ArithmeticFunction.vonMangoldt n : ℝ) (lam' n)] at t
  linarith

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
