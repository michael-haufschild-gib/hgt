import GaloisForLFunctions.RHTower.XiMassCausticComplexWindow
import GaloisForLFunctions.RHTower.XiMassJetTransport
import GaloisForLFunctions.RHTower.XiMassJetFourierIdentity
import GaloisForLFunctions.HTGeometry.PrincipalRootPerturbation
import GaloisForLFunctions.HTGeometry.CauchyFirstOrderStep

/-!
# The jet profile on a complex window disc, and its height derivative

The exterior exponent of the jet profile is the real part of the propagation radius, and the
principal root moves by at most the argument perturbation divided by itself.  A bounded complex
perturbation of the height therefore costs only a bounded factor, even though the argument itself
moves by `O(h)`.  The window bound consequently holds on a disc of bounded radius about every real
window point, and Cauchy's estimate turns it into a bound for the height derivative.
-/

open Complex Metric

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **The jet profile on a complex disc about a real window point.** -/
theorem exists_norm_xiMassJetIterate_windowC_le {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (n : ℕ) :
    ∃ C u₀ : ℝ, 0 < C ∧ xiMassWindowThreshold a ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ h : ℝ,
      |h - xiMassSpacelikeSharpSlope a * u| ≤ Real.sqrt u / 4 → ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n ((h : ℂ) + w)‖
        ≤ C / Real.sqrt u ^ (n + 1) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  obtain ⟨C₀, u₀, hC₀, hu₀, hcaus⟩ := exists_norm_xiCausticIterate_windowC_le ha hsigma n
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  set κ : ℝ := xiMassSpacelikeSharpSlope a with hκdef
  set κ' : ℝ := (1 + κ) / 2 with hκ'def
  have hκ'1 : 1 < κ' := by rw [hκ'def]; linarith
  have hκ'κ : κ' < κ := by rw [hκ'def]; linarith
  have hgap : (0 : ℝ) < κ' ^ 2 - 1 := by nlinarith
  have hroot : (0 : ℝ) < Real.sqrt (κ' ^ 2 - 1) := Real.sqrt_pos.2 hgap
  set c₁ : ℝ := (2 * κ + 3) / Real.sqrt (κ' ^ 2 - 1) with hc₁def
  have hc₁0 : (0 : ℝ) ≤ c₁ := by rw [hc₁def]; positivity
  refine ⟨C₀ * Real.exp (a * c₁), max (max u₀ 16) (max 1 ((4 * (κ - κ')) ⁻¹ ^ 2 + 1)),
    by positivity, ?_, ?_⟩
  · exact le_trans hu₀ (le_trans (le_max_left _ _) (le_max_left _ _))
  intro u hu h hh w hw
  have hu0' : u₀ ≤ u := le_trans (by simp) hu
  have hu16 : (16 : ℝ) ≤ u := le_trans (by simp) hu
  have hugap : ((4 * (κ - κ')) ⁻¹ ^ 2 + 1 : ℝ) ≤ u := le_trans (by simp) hu
  have huw : xiMassWindowThreshold a ≤ u := le_trans hu₀ hu0'
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hrsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  have hr4 : (4 : ℝ) ≤ Real.sqrt u := by
    nlinarith [hrsq, hr0, hu16]
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set m : ℂ := ((κ * u : ℝ) : ℂ) with hmdef
  -- the offset from the balance ray
  set w' : ℂ := (((h - κ * u : ℝ)) : ℂ) + w with hw'def
  have hζ : ((h : ℝ) : ℂ) + w = m + w' := by
    rw [hw'def, hmdef]
    push_cast
    ring
  have hw'norm : ‖w'‖ ≤ Real.sqrt u / 2 := by
    have h1 : ‖w'‖ ≤ ‖(((h - κ * u : ℝ)) : ℂ)‖ + ‖w‖ := by
      rw [hw'def]
      exact norm_add_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    have h3 : (1 : ℝ) ≤ Real.sqrt u / 4 := by linarith
    linarith [hh]
  -- the height is deep in the spacelike cone
  have hhlow : κ' * u ≤ h := by
    have habs := (abs_le.mp hh).1
    have hstep : Real.sqrt u / 4 ≤ (κ - κ') * u := by
      have hinv : (4 * (κ - κ'))⁻¹ ≤ Real.sqrt u := by
        have hpos : (0 : ℝ) < 4 * (κ - κ') := by linarith
        nlinarith [hugap, hrsq, hr0, sq_nonneg ((4 * (κ - κ'))⁻¹)]
      have hne : κ - κ' ≠ 0 := ne_of_gt (by linarith)
      have hmul : (4 * (κ - κ'))⁻¹ * (4 * (κ - κ')) = 1 := by
        field_simp
      have h1 : 1 ≤ Real.sqrt u * (4 * (κ - κ')) := by
        have hstep := mul_le_mul_of_nonneg_right hinv
          (by linarith : (0 : ℝ) ≤ 4 * (κ - κ'))
        rwa [hmul] at hstep
      have h2 := mul_le_mul_of_nonneg_right h1 hr0.le
      nlinarith [h2, hrsq, hr0]
    linarith
  have hhu : u ≤ h := by nlinarith
  have hhpos : (0 : ℝ) < h := by nlinarith
  have hhigh : h ≤ (κ + 1) * u := by
    have habs := (abs_le.mp hh).2
    have hsr : Real.sqrt u ≤ u := by nlinarith [hrsq, hr0, hu1]
    linarith [habs, hsr, hu0, hκ1]
  -- the gap at the real point
  have hgapu : Real.sqrt (κ' ^ 2 - 1) * u ≤ Real.sqrt (h ^ 2 - u ^ 2) := by
    have hsq : (Real.sqrt (κ' ^ 2 - 1) * u) ^ 2 ≤ h ^ 2 - u ^ 2 := by
      have hs : Real.sqrt (κ' ^ 2 - 1) ^ 2 = κ' ^ 2 - 1 := Real.sq_sqrt hgap.le
      have hh2 : (κ' * u) ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ (by positivity) hhlow 2
      nlinarith [hh2, hs]
    have hnn : (0 : ℝ) ≤ Real.sqrt (κ' ^ 2 - 1) * u := by positivity
    nlinarith [Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ h ^ 2 - u ^ 2),
      Real.sqrt_nonneg (h ^ 2 - u ^ 2), hsq, hnn]
  have hgap0 : (0 : ℝ) < Real.sqrt (h ^ 2 - u ^ 2) := lt_of_lt_of_le (by positivity) hgapu
  -- both propagation arguments are spacelike
  have hmemζ : ((h : ℝ) : ℂ) + w ∈ xiMassHeightRegion τ := by
    rw [hτdef, hζ]
    refine window_subset_xiMassHeightRegion (sigma := sigma) ha huw ?_
    have hid : m + w' - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) = w' := by
      rw [hmdef, hκdef]; ring
    rw [hid]
    linarith [hw'norm, hr0]
  have hmemh : ((h : ℝ) : ℂ) ∈ xiMassHeightRegion τ := by
    rw [hτdef]
    refine window_subset_xiMassHeightRegion (sigma := sigma) ha huw ?_
    have hid : ((h : ℝ) : ℂ) - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)
        = (((h - κ * u : ℝ)) : ℂ) := by rw [hκdef]; push_cast; ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs]
    linarith [hh, hr0]
  have hreζ : (0 : ℝ) < (τ ^ 2 + (((h : ℝ) : ℂ) + w) ^ 2).re := hmemζ
  have hreh : (0 : ℝ) < (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2).re := hmemh
  -- the real point's root dominates the full gap
  have hrootge : Real.sqrt (h ^ 2 - u ^ 2)
      ≤ HTGeometry.csqrtRe (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2) := by
    have hpropeq : τ ^ 2 + ((h : ℝ) : ℂ) ^ 2
        = xiMassSpacelikePropagationArgument sigma u h := by
      rw [xiMassSpacelikePropagationArgument_eq, hτdef]
    rw [hpropeq]
    have hmono : Real.sqrt (h ^ 2 - u ^ 2) ≤ Real.sqrt (h ^ 2 - u ^ 2 + sigma ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg sigma])
    exact le_trans hmono (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu0.le hhu)
  -- the perturbation of the argument
  have hdiff : ‖(τ ^ 2 + (((h : ℝ) : ℂ) + w) ^ 2) - (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2)‖
      ≤ (2 * κ + 3) * u := by
    have hid : (τ ^ 2 + (((h : ℝ) : ℂ) + w) ^ 2) - (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2)
        = 2 * ((h : ℝ) : ℂ) * w + w ^ 2 := by ring
    rw [hid]
    have h1 : ‖2 * ((h : ℝ) : ℂ) * w + w ^ 2‖ ≤ ‖2 * ((h : ℝ) : ℂ) * w‖ + ‖w ^ 2‖ :=
      norm_add_le _ _
    have h2 : ‖2 * ((h : ℝ) : ℂ) * w‖ = 2 * |h| * ‖w‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    have h3 : ‖w ^ 2‖ = ‖w‖ ^ 2 := norm_pow w 2
    rw [h2, h3, abs_of_pos hhpos] at h1
    have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w, hw]
    nlinarith [h1, hhigh, hu1, hw, norm_nonneg w]
  -- the exterior exponent survives the perturbation
  have hcs : HTGeometry.csqrtRe (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2) - c₁
      ≤ HTGeometry.csqrtRe (τ ^ 2 + (((h : ℝ) : ℂ) + w) ^ 2) := by
    refine le_trans ?_ (HTGeometry.csqrtRe_sub_le hreζ hreh)
    have hle : ‖(τ ^ 2 + (((h : ℝ) : ℂ) + w) ^ 2) - (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2)‖
        / HTGeometry.csqrtRe (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2) ≤ c₁ := by
      have hden : (0 : ℝ) < HTGeometry.csqrtRe (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2) :=
        HTGeometry.csqrtRe_pos hreh
      rw [div_le_iff₀ hden, hc₁def]
      have hstep : Real.sqrt (κ' ^ 2 - 1) * u
          ≤ HTGeometry.csqrtRe (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2) := le_trans hgapu hrootge
      have hmul : (2 * κ + 3) * u
          ≤ (2 * κ + 3) / Real.sqrt (κ' ^ 2 - 1) * (Real.sqrt (κ' ^ 2 - 1) * u) := by
        rw [div_mul_eq_mul_div, mul_comm (Real.sqrt (κ' ^ 2 - 1)) u, ← mul_assoc,
          mul_div_assoc, div_self (ne_of_gt hroot), mul_one]
      refine le_trans hdiff (le_trans hmul ?_)
      refine mul_le_mul_of_nonneg_left hstep ?_
      positivity
    linarith
  -- assemble
  have hgauge := xiMassJetIterate_eqOn ha0 τ n hmemζ
  rw [hgauge]
  have hexpnorm : ‖Complex.exp (-(a : ℂ) * xiMassHeightRadius τ (((h : ℝ) : ℂ) + w))‖
      = Real.exp (-(a * HTGeometry.csqrtRe (τ ^ 2 + (((h : ℝ) : ℂ) + w) ^ 2))) := by
    rw [Complex.norm_exp]
    congr 1
    have hre := re_mul_xiMassHeightRadius a τ (((h : ℝ) : ℂ) + w)
    have hneg : (-(a : ℂ) * xiMassHeightRadius τ (((h : ℝ) : ℂ) + w))
        = -((a : ℂ) * xiMassHeightRadius τ (((h : ℝ) : ℂ) + w)) := by ring
    rw [hneg, Complex.neg_re, hre]
  have hcausbd : ‖xiCausticIterate a τ n (((h : ℝ) : ℂ) + w)‖ ≤ C₀ / Real.sqrt u ^ (n + 1) := by
    rw [hζ, hτdef, hmdef, hκdef]
    exact hcaus u hu0' w' hw'norm
  have hexple : Real.exp (-(a * HTGeometry.csqrtRe (τ ^ 2 + (((h : ℝ) : ℂ) + w) ^ 2)))
      ≤ Real.exp (a * c₁) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [hcs, hrootge, ha0]
  rw [norm_mul, hexpnorm]
  calc Real.exp (-(a * HTGeometry.csqrtRe (τ ^ 2 + (((h : ℝ) : ℂ) + w) ^ 2)))
        * ‖xiCausticIterate a τ n (((h : ℝ) : ℂ) + w)‖
      ≤ (Real.exp (a * c₁) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))
        * (C₀ / Real.sqrt u ^ (n + 1)) := by
        exact mul_le_mul hexple hcausbd (norm_nonneg _) (by positivity)
    _ = C₀ * Real.exp (a * c₁) / Real.sqrt u ^ (n + 1)
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by ring

/-- A closed disc inside the region gives the Cauchy hypothesis for the jet profile. -/
theorem diffContOnCl_xiMassJetIterate {a : ℝ} (ha : 0 < a) {τ ζ : ℂ} {δ : ℝ} (k : ℕ)
    (hsub : closedBall ζ δ ⊆ xiMassHeightRegion τ) :
    DiffContOnCl ℂ (xiMassJetIterate a τ k) (ball ζ δ) := by
  have hd := differentiableOn_xiMassJetIterate ha τ k
  refine ⟨hd.mono (le_trans ball_subset_closedBall hsub), ?_⟩
  exact hd.continuousOn.mono (le_trans closure_ball_subset_closedBall hsub)

set_option maxHeartbeats 1000000 in
/-- **The height derivative of the jet profile in the window.**  Cauchy's estimate at bounded radius
turns the complex window bound into a bound for the derivative, with the same exterior exponent. -/
theorem exists_norm_deriv_xiMassJetIterate_window_le {a sigma : ℝ} (ha : 1 / 2 < a)
    (hsigma : 0 < sigma) (n : ℕ) :
    ∃ C u₀ : ℝ, 0 < C ∧ 1 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ h : ℝ,
      |h - xiMassSpacelikeSharpSlope a * u| ≤ Real.sqrt u / 8 →
      ‖deriv (xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n) ((h : ℝ) : ℂ)‖
        ≤ C / Real.sqrt u ^ (n + 1) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  obtain ⟨C, u₀, hC, hu₀, hbnd⟩ := exists_norm_xiMassJetIterate_windowC_le ha hsigma n
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  refine ⟨2 * C, max u₀ 64, by positivity, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro u hu h hh
  have hu0' : u₀ ≤ u := le_trans (le_max_left _ _) hu
  have hu64 : (64 : ℝ) ≤ u := le_trans (le_max_right _ _) hu
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hr0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hrsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  have hr8 : (8 : ℝ) ≤ Real.sqrt u := by nlinarith [hrsq, hr0, hu64]
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set M : ℝ := C / Real.sqrt u ^ (n + 1)
    * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) with hMdef
  have hMnn : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  have hquarter : |h - xiMassSpacelikeSharpSlope a * u| ≤ Real.sqrt u / 4 := by
    linarith [hh, hr0]
  have hsphere : ∀ ζ ∈ sphere ((h : ℝ) : ℂ) (1 / 2 : ℝ),
      ‖xiMassJetIterate a τ n ζ‖ ≤ M := by
    intro ζ hζ
    have hnorm : ‖ζ - ((h : ℝ) : ℂ)‖ = (1 / 2 : ℝ) := by
      rw [mem_sphere_iff_norm] at hζ
      exact hζ
    have hle : ‖ζ - ((h : ℝ) : ℂ)‖ ≤ 1 := by rw [hnorm]; norm_num
    have hid : ζ = ((h : ℝ) : ℂ) + (ζ - ((h : ℝ) : ℂ)) := by ring
    rw [hid, hτdef, hMdef]
    exact hbnd u hu0' h hquarter (ζ - ((h : ℝ) : ℂ)) hle
  have hsub : closedBall ((h : ℝ) : ℂ) (1 / 2 : ℝ) ⊆ xiMassHeightRegion τ := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    rw [hτdef]
    refine window_subset_xiMassHeightRegion (sigma := sigma) ha
      (le_trans hu₀ hu0') ?_
    have htri : ‖v - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)‖
        ≤ ‖v - ((h : ℝ) : ℂ)‖ + ‖((h : ℝ) : ℂ) - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)‖ := by
      have := norm_add_le (v - ((h : ℝ) : ℂ))
        (((h : ℝ) : ℂ) - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ))
      simpa using this
    have hid : ((h : ℝ) : ℂ) - (((xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ)
        = (((h - xiMassSpacelikeSharpSlope a * u : ℝ)) : ℂ) := by push_cast; ring
    rw [hid, Complex.norm_real, Real.norm_eq_abs] at htri
    linarith [hh, hv, hr8]
  have hcauchy := HTGeometry.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := xiMassJetIterate a τ n) (z := ((h : ℝ) : ℂ)) (R := (1 / 2 : ℝ)) (M := M)
    (by norm_num) (diffContOnCl_xiMassJetIterate ha0 n hsub) hsphere
  refine le_trans hcauchy (le_of_eq ?_)
  rw [hMdef]
  field_simp

end

end RHTower
