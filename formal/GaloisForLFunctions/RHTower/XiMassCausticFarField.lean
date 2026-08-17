import GaloisForLFunctions.RHTower.XiMassJetTransport

/-!
# The caustic jet in the far field

Past the balance ray the jet needs no gain, only no loss.  On `h ≥ κ_B u` the spacelike gap is
already proportional to the height itself, `h² − u² ≥ (1 − κ_B^{-2})h²`, so on unit discs about such
a point the propagation rate is `≍ h`, the caustic coefficients are bounded by absolute constants
and the conjugated carrier is bounded.  The Cauchy iteration on unit discs then gives

`‖Φ_n(h)‖ ≤ C_n`,   hence   `‖(4a⁴ − ∂²)ⁿ F(h)‖ ≤ C_n·e^{-a√(h²−u²)}` ,

with no power of the height at all.  This is the card's "beyond the window, exponential action decay
absorbs every fixed polynomial loss from `P_N`", in a form with no loss to absorb.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- The far-field propagation rate constant. -/
def xiMassFarRate (a : ℝ) : ℝ :=
  Real.sqrt ((1 - 1 / xiMassSpacelikeSharpSlope a ^ 2) / 2)

/-- The far-field gap fraction. -/
def xiMassFarGap (a : ℝ) : ℝ := 1 - 1 / xiMassSpacelikeSharpSlope a ^ 2

theorem xiMassFarGap_pos {a : ℝ} (ha : 1 / 2 < a) : 0 < xiMassFarGap a := by
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hκ0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a := by linarith
  rw [xiMassFarGap, sub_pos, div_lt_one (by positivity)]
  nlinarith

theorem xiMassFarGap_le_one {a : ℝ} (ha : 1 / 2 < a) : xiMassFarGap a ≤ 1 := by
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hκ0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a := by linarith
  rw [xiMassFarGap]
  have : (0 : ℝ) < 1 / xiMassSpacelikeSharpSlope a ^ 2 := by positivity
  linarith

theorem xiMassFarRate_pos {a : ℝ} (ha : 1 / 2 < a) : 0 < xiMassFarRate a := by
  have hg := xiMassFarGap_pos ha
  rw [xiMassFarGap] at hg
  rw [xiMassFarRate]
  exact Real.sqrt_pos.2 (by linarith)

theorem xiMassFarRate_sq {a : ℝ} (ha : 1 / 2 < a) :
    xiMassFarRate a ^ 2 = xiMassFarGap a / 2 := by
  have hg := xiMassFarGap_pos ha
  rw [xiMassFarRate, xiMassFarGap] at *
  exact Real.sq_sqrt (by linarith)

/-- The far-field height threshold. -/
def xiMassFarThreshold (a : ℝ) : ℝ := max 1 (6 / xiMassFarGap a)

theorem one_le_xiMassFarThreshold (a : ℝ) : 1 ≤ xiMassFarThreshold a := le_max_left _ _

/-- **The far field has a propagation argument proportional to the height squared.** -/
theorem re_propagation_ge_far {a sigma u h : ℝ} (ha : 1 / 2 < a) (hu : 0 < u)
    (hcone : xiMassSpacelikeSharpSlope a * u ≤ h) (hh : xiMassFarThreshold a ≤ h)
    {s : ℂ} (hs : ‖s‖ ≤ 1) :
    xiMassFarGap a / 2 * h ^ 2
      ≤ (((sigma : ℂ) + (u : ℂ) * Complex.I) ^ 2 + (((h : ℝ) : ℂ) + s) ^ 2).re := by
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hκ0 : (0 : ℝ) < xiMassSpacelikeSharpSlope a := by linarith
  have hg0 : (0 : ℝ) < xiMassFarGap a := xiMassFarGap_pos ha
  have hh1 : (1 : ℝ) ≤ h := le_trans (one_le_xiMassFarThreshold a) hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hh6 : 6 / xiMassFarGap a ≤ h := le_trans (le_max_right _ _) hh
  have hgap : xiMassFarGap a * h ^ 2 ≤ h ^ 2 - u ^ 2 := by
    have hul : u ≤ h / xiMassSpacelikeSharpSlope a := by
      rw [le_div_iff₀ hκ0]
      nlinarith [hcone]
    have husq : u ^ 2 ≤ h ^ 2 / xiMassSpacelikeSharpSlope a ^ 2 := by
      have h1 : u ^ 2 ≤ (h / xiMassSpacelikeSharpSlope a) ^ 2 := by nlinarith [hu.le, hul]
      calc u ^ 2 ≤ (h / xiMassSpacelikeSharpSlope a) ^ 2 := h1
        _ = h ^ 2 / xiMassSpacelikeSharpSlope a ^ 2 := by rw [div_pow]
    rw [xiMassFarGap]
    have hdiv : h ^ 2 / xiMassSpacelikeSharpSlope a ^ 2
        = 1 / xiMassSpacelikeSharpSlope a ^ 2 * h ^ 2 := by ring
    rw [hdiv] at husq
    nlinarith [husq]
  have hre : (((sigma : ℂ) + (u : ℂ) * Complex.I) ^ 2 + (((h : ℝ) : ℂ) + s) ^ 2).re
      = sigma ^ 2 + (h ^ 2 - u ^ 2) + 2 * h * s.re + (s ^ 2).re := by
    have hexp : ((sigma : ℂ) + (u : ℂ) * Complex.I) ^ 2 + (((h : ℝ) : ℂ) + s) ^ 2
        = (((sigma ^ 2 + (h ^ 2 - u ^ 2) : ℝ)) : ℂ) + ((2 * h : ℝ) : ℂ) * s + s ^ 2
          + (((2 * sigma * u : ℝ)) : ℂ) * Complex.I := by
      push_cast
      linear_combination Complex.I_sq * ((u : ℂ) ^ 2)
    rw [hexp]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hsre : |s.re| ≤ 1 := le_trans (Complex.abs_re_le_norm s) hs
  have hs2 : |(s ^ 2).re| ≤ 1 := by
    have h1 : |(s ^ 2).re| ≤ ‖s ^ 2‖ := Complex.abs_re_le_norm _
    have h2 : ‖s ^ 2‖ ≤ 1 := by
      rw [norm_pow]
      nlinarith [norm_nonneg s, hs]
    linarith
  have hmid : -(2 * h) ≤ 2 * h * s.re := by
    have hlow := (abs_le.mp hsre).1
    nlinarith [hh0]
  have hlow2 : -1 ≤ (s ^ 2).re := (abs_le.mp hs2).1
  have hslack : 2 * h + 1 ≤ xiMassFarGap a / 2 * h ^ 2 := by
    have hkey : 6 ≤ xiMassFarGap a * h := by
      rw [div_le_iff₀ hg0] at hh6
      linarith
    nlinarith [hkey, hh1, hh0]
  rw [hre]
  nlinarith [sq_nonneg sigma, hgap, hmid, hlow2, hslack]

/-- **The far-field propagation rate.** -/
theorem xiMassFarRate_mul_le_csqrtRe {a sigma u h : ℝ} (ha : 1 / 2 < a) (hu : 0 < u)
    (hcone : xiMassSpacelikeSharpSlope a * u ≤ h) (hh : xiMassFarThreshold a ≤ h)
    {s : ℂ} (hs : ‖s‖ ≤ 1) :
    xiMassFarRate a * h
      ≤ HTGeometry.csqrtRe (((sigma : ℂ) + (u : ℂ) * Complex.I) ^ 2 + (((h : ℝ) : ℂ) + s) ^ 2) := by
  have hg0 : (0 : ℝ) < xiMassFarGap a := xiMassFarGap_pos ha
  have hh1 : (1 : ℝ) ≤ h := le_trans (one_le_xiMassFarThreshold a) hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hrate0 : (0 : ℝ) < xiMassFarRate a := xiMassFarRate_pos ha
  set z : ℂ := ((sigma : ℂ) + (u : ℂ) * Complex.I) ^ 2 + (((h : ℝ) : ℂ) + s) ^ 2 with hzdef
  have hlow : xiMassFarGap a / 2 * h ^ 2 ≤ z.re := re_propagation_ge_far ha hu hcone hh hs
  have hzre : (0 : ℝ) < z.re := lt_of_lt_of_le (by positivity) hlow
  have hsq := HTGeometry.re_le_sq_csqrtRe hzre
  have hcpos : (0 : ℝ) < HTGeometry.csqrtRe z := HTGeometry.csqrtRe_pos hzre
  have hkey : (xiMassFarRate a * h) ^ 2 ≤ HTGeometry.csqrtRe z ^ 2 := by
    have hexp : (xiMassFarRate a * h) ^ 2 = xiMassFarGap a / 2 * h ^ 2 := by
      rw [mul_pow, xiMassFarRate_sq ha]
    rw [hexp]
    linarith
  nlinarith [hkey, hrate0, hh0, hcpos]

/-- **The far field lies inside the region.** -/
theorem far_mem_xiMassHeightRegion {a sigma u h : ℝ} (ha : 1 / 2 < a) (hu : 0 < u)
    (hcone : xiMassSpacelikeSharpSlope a * u ≤ h) (hh : xiMassFarThreshold a ≤ h)
    {s : ℂ} (hs : ‖s‖ ≤ 1) :
    (((h : ℝ) : ℂ) + s) ∈ xiMassHeightRegion ((sigma : ℂ) + (u : ℂ) * Complex.I) := by
  have hg0 : (0 : ℝ) < xiMassFarGap a := xiMassFarGap_pos ha
  have hh1 : (1 : ℝ) ≤ h := le_trans (one_le_xiMassFarThreshold a) hh
  have hlow := re_propagation_ge_far (sigma := sigma) ha hu hcone hh hs
  rw [mem_xiMassHeightRegion]
  have : (0 : ℝ) < xiMassFarGap a / 2 * h ^ 2 := by positivity
  linarith

set_option maxHeartbeats 2000000 in
/-- **The far-field caustic bound.**  On `h ≥ κ_B u` the jet iterate is bounded by a constant, so
the jet costs nothing at all outside the balance window. -/
theorem exists_norm_xiMassJetIterate_far_le {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (n : ℕ) :
    ∃ C u₀ : ℝ, 0 < C ∧ 1 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ h : ℝ,
      xiMassSpacelikeSharpSlope a * u ≤ h → xiMassFarThreshold a ≤ h →
      ‖xiMassJetIterate a ((sigma : ℂ) + (u : ℂ) * Complex.I) n ((h : ℝ) : ℂ)‖
        ≤ C * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hκ1 : 1 < xiMassSpacelikeSharpSlope a := one_lt_xiMassSpacelikeSharpSlope ha
  have hg0 : (0 : ℝ) < xiMassFarGap a := xiMassFarGap_pos ha
  set ρ : ℝ := xiMassFarRate a with hρdef
  have hρ0 : (0 : ℝ) < ρ := xiMassFarRate_pos ha
  set γ₂ : ℝ := 4 * a / ρ with hγdef
  have hγ0 : (0 : ℝ) < γ₂ := by rw [hγdef]; positivity
  set Cz : ℝ := 4 * a ^ 4 + 8 * a ^ 2 / xiMassFarGap a + a * (1 / ρ + 4 / ρ ^ 3) with hCzdef
  have hCz0 : (0 : ℝ) < Cz := by rw [hCzdef]; positivity
  set Cg : ℝ := 2 * a * (sigma + 1) / ρ
    * (Real.exp (1 / (2 * (a * ρ))) * Real.sqrt (2 * Real.pi / (a * ρ))) with hCgdef
  have hCg0 : (0 : ℝ) < Cg := by rw [hCgdef]; positivity
  refine ⟨Cg * (Cz + γ₂ * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) ^ 2) ^ n, 1, by positivity, le_rfl, ?_⟩
  intro u hu h hcone hh
  have hu0 : (0 : ℝ) < u := by linarith
  have hh1 : (1 : ℝ) ≤ h := le_trans (one_le_xiMassFarThreshold a) hh
  have hh0 : (0 : ℝ) < h := by linarith
  have huh : u ≤ h := le_trans (by nlinarith) hcone
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hnδ : (n : ℝ) * δ + δ = 1 := by rw [hδdef]; field_simp
  have hnear : ∀ ζ : ℂ, ‖ζ - ((h : ℝ) : ℂ)‖ ≤ (n : ℝ) * δ + δ → ‖ζ - ((h : ℝ) : ℂ)‖ ≤ 1 := by
    intro ζ hζ; linarith [hnδ]
  have hshift : ∀ ζ : ℂ, ζ = ((h : ℝ) : ℂ) + (ζ - ((h : ℝ) : ℂ)) := fun ζ => by ring
  -- the pointwise far-field estimates
  have hpt : ∀ s : ℂ, ‖s‖ ≤ 1 →
      ‖xiCausticCoeffZero a τ (((h : ℝ) : ℂ) + s)‖ ≤ Cz
      ∧ ‖xiCausticCoeffOne a τ (((h : ℝ) : ℂ) + s)‖ ≤ γ₂
      ∧ ‖xiMassConjugatedCarrier a τ (((h : ℝ) : ℂ) + s)‖ ≤ Cg := by
    intro s hs
    set w : ℂ := ((h : ℝ) : ℂ) + s with hwdef
    have hzre : (0 : ℝ) < (τ ^ 2 + w ^ 2).re := by
      have hlow := re_propagation_ge_far (sigma := sigma) ha hu0 hcone hh hs
      have : (0 : ℝ) < xiMassFarGap a / 2 * h ^ 2 := by positivity
      rw [hτdef, hwdef]
      linarith [hlow]
    have hR : ρ * h ≤ HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) := by
      rw [hτdef, hwdef, hρdef]
      exact xiMassFarRate_mul_le_csqrtRe ha hu0 hcone hh hs
    have hZre : (xiMassHeightRadius τ w).re = HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) := by
      rw [xiMassHeightRadius, HTGeometry.csqrt_re]
    have hZnorm : ρ * h ≤ ‖xiMassHeightRadius τ w‖ := by
      refine le_trans hR ?_
      have hb := Complex.abs_re_le_norm (xiMassHeightRadius τ w)
      rw [hZre] at hb
      exact le_trans (le_abs_self _) hb
    have hZpos : (0 : ℝ) < ‖xiMassHeightRadius τ w‖ := lt_of_lt_of_le (by positivity) hZnorm
    have hwnorm : ‖w‖ ≤ 2 * h := by
      have h1 : ‖w‖ ≤ ‖((h : ℝ) : ℂ)‖ + ‖s‖ := by rw [hwdef]; exact norm_add_le _ _
      have h2 : ‖((h : ℝ) : ℂ)‖ = h := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
      rw [h2] at h1
      linarith [hs, hh1]
    have hanorm : ‖(a : ℂ)‖ = a := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    refine ⟨?_, ?_, ?_⟩
    · -- the zeroth-order coefficient
      have hznorm : xiMassFarGap a / 2 * h ^ 2 ≤ ‖τ ^ 2 + w ^ 2‖ := by
        have hlow := re_propagation_ge_far (sigma := sigma) ha hu0 hcone hh hs
        have hb := Complex.abs_re_le_norm (τ ^ 2 + w ^ 2)
        rw [hτdef, hwdef] at *
        exact le_trans hlow (le_trans (le_abs_self _) hb)
      have hsym : ‖xiMassCausticSymbolC a τ w‖ ≤ 4 * a ^ 4 + 8 * a ^ 2 / xiMassFarGap a := by
        have hquot : ‖(a : ℂ) ^ 2 * w ^ 2 / (τ ^ 2 + w ^ 2)‖ ≤ 8 * a ^ 2 / xiMassFarGap a := by
          rw [norm_div, norm_mul, norm_pow, norm_pow, hanorm]
          have hnum : a ^ 2 * ‖w‖ ^ 2 ≤ a ^ 2 * (2 * h) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwnorm 2) (by positivity)
          have hs1 : a ^ 2 * ‖w‖ ^ 2 / ‖τ ^ 2 + w ^ 2‖
              ≤ a ^ 2 * (2 * h) ^ 2 / ‖τ ^ 2 + w ^ 2‖ :=
            div_le_div_of_nonneg_right hnum (norm_nonneg _)
          have hs2 : a ^ 2 * (2 * h) ^ 2 / ‖τ ^ 2 + w ^ 2‖
              ≤ a ^ 2 * (2 * h) ^ 2 / (xiMassFarGap a / 2 * h ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hznorm
          have hval : a ^ 2 * (2 * h) ^ 2 / (xiMassFarGap a / 2 * h ^ 2)
              = 8 * a ^ 2 / xiMassFarGap a := by
            field_simp
            ring
          linarith [hs1, hs2, hval.le, hval.ge]
        have hbase : ‖4 * (a : ℂ) ^ 4‖ = 4 * a ^ 4 := by
          rw [show (4 : ℂ) * (a : ℂ) ^ 4 = ((4 * a ^ 4 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        rw [xiMassCausticSymbolC]
        calc ‖4 * (a : ℂ) ^ 4 - (a : ℂ) ^ 2 * w ^ 2 / (τ ^ 2 + w ^ 2)‖
            ≤ ‖4 * (a : ℂ) ^ 4‖ + ‖(a : ℂ) ^ 2 * w ^ 2 / (τ ^ 2 + w ^ 2)‖ := norm_sub_le _ _
          _ ≤ 4 * a ^ 4 + 8 * a ^ 2 / xiMassFarGap a := by rw [hbase]; linarith
      have hcurv : ‖(a : ℂ) * (1 / xiMassHeightRadius τ w
            - w ^ 2 / xiMassHeightRadius τ w ^ 3)‖ ≤ a * (1 / ρ + 4 / ρ ^ 3) := by
        have h1 : ‖1 / xiMassHeightRadius τ w‖ ≤ 1 / (ρ * h) := by
          rw [norm_div, norm_one]
          exact div_le_div_of_nonneg_left zero_le_one (by positivity) hZnorm
        have h2 : ‖w ^ 2 / xiMassHeightRadius τ w ^ 3‖ ≤ (2 * h) ^ 2 / (ρ * h) ^ 3 := by
          rw [norm_div, norm_pow, norm_pow]
          have hnum : ‖w‖ ^ 2 ≤ (2 * h) ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hwnorm 2
          have hden : (ρ * h) ^ 3 ≤ ‖xiMassHeightRadius τ w‖ ^ 3 :=
            pow_le_pow_left₀ (by positivity) hZnorm 3
          have hs1 : ‖w‖ ^ 2 / ‖xiMassHeightRadius τ w‖ ^ 3
              ≤ (2 * h) ^ 2 / ‖xiMassHeightRadius τ w‖ ^ 3 :=
            div_le_div_of_nonneg_right hnum (by positivity)
          have hs2 : (2 * h) ^ 2 / ‖xiMassHeightRadius τ w‖ ^ 3 ≤ (2 * h) ^ 2 / (ρ * h) ^ 3 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
          linarith
        have hsum : ‖1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3‖
            ≤ 1 / (ρ * h) + (2 * h) ^ 2 / (ρ * h) ^ 3 := by
          refine le_trans (norm_sub_le _ _) ?_
          linarith
        have hval : 1 / (ρ * h) + (2 * h) ^ 2 / (ρ * h) ^ 3 = (1 / ρ + 4 / ρ ^ 3) / h := by
          field_simp
          ring
        rw [norm_mul, hanorm]
        have hstep := mul_le_mul_of_nonneg_left hsum ha0.le
        have hdiv : (1 / ρ + 4 / ρ ^ 3) / h ≤ (1 / ρ + 4 / ρ ^ 3) := by
          rw [div_le_iff₀ hh0]
          have hpos : (0 : ℝ) < 1 / ρ + 4 / ρ ^ 3 := by positivity
          nlinarith [hh1, hpos]
        calc a * ‖1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3‖
            ≤ a * (1 / (ρ * h) + (2 * h) ^ 2 / (ρ * h) ^ 3) := hstep
          _ = a * ((1 / ρ + 4 / ρ ^ 3) / h) := by rw [hval]
          _ ≤ a * (1 / ρ + 4 / ρ ^ 3) := mul_le_mul_of_nonneg_left hdiv ha0.le
      rw [xiCausticCoeffZero, hCzdef]
      calc ‖xiMassCausticSymbolC a τ w
              + (a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3)‖
          ≤ ‖xiMassCausticSymbolC a τ w‖
            + ‖(a : ℂ) * (1 / xiMassHeightRadius τ w
                - w ^ 2 / xiMassHeightRadius τ w ^ 3)‖ := norm_add_le _ _
        _ ≤ 4 * a ^ 4 + 8 * a ^ 2 / xiMassFarGap a + a * (1 / ρ + 4 / ρ ^ 3) := by linarith
    · -- the transport coefficient
      rw [xiCausticCoeffOne, xiMassRadiusRate, norm_mul, norm_div, hγdef]
      have hcoef : ‖2 * (a : ℂ)‖ = 2 * a := by
        rw [show (2 : ℂ) * (a : ℂ) = ((2 * a : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hcoef]
      have hs1 : ‖w‖ / ‖xiMassHeightRadius τ w‖ ≤ 2 * h / ‖xiMassHeightRadius τ w‖ :=
        div_le_div_of_nonneg_right hwnorm (norm_nonneg _)
      have hs2 : 2 * h / ‖xiMassHeightRadius τ w‖ ≤ 2 * h / (ρ * h) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hZnorm
      have hval : 2 * h / (ρ * h) = 2 / ρ := by field_simp
      have hfin : 2 * a * (‖w‖ / ‖xiMassHeightRadius τ w‖) ≤ 2 * a * (2 / ρ) :=
        mul_le_mul_of_nonneg_left (by linarith [hs1, hs2, hval.le, hval.ge]) (by positivity)
      calc 2 * a * (‖w‖ / ‖xiMassHeightRadius τ w‖) ≤ 2 * a * (2 / ρ) := hfin
        _ = 4 * a / ρ := by ring
    · -- the conjugated carrier
      have hmain := norm_xiMassConjugatedCarrier_le (a := a) (τ := τ) (w := w) ha0 hzre
      set R : ℝ := HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) with hRdef
      have hR0 : (0 : ℝ) < R := HTGeometry.csqrtRe_pos hzre
      have hRh : ρ * h ≤ R := hR
      have hRu : ρ * u ≤ R := le_trans (by nlinarith [hρ0, huh]) hRh
      have hR1 : ρ ≤ R := le_trans (by nlinarith [hρ0, hh1]) hRh
      have hτnorm : ‖τ‖ ≤ (sigma + 1) * u := by
        have h1 : ‖τ‖ ≤ ‖(sigma : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ := by
          rw [hτdef]; exact norm_add_le _ _
        have h2 : ‖(sigma : ℂ)‖ = sigma := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsigma]
        have h3 : ‖(u : ℂ) * Complex.I‖ = u := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hu0]
        rw [h2, h3] at h1
        nlinarith [h1, hsigma.le, hu]
      have hf1 : 2 * a * ‖τ‖ / R ≤ 2 * a * (sigma + 1) / ρ := by
        have hnum : 2 * a * ‖τ‖ ≤ 2 * a * ((sigma + 1) * u) :=
          mul_le_mul_of_nonneg_left hτnorm (by positivity)
        have hs1 : 2 * a * ‖τ‖ / R ≤ 2 * a * ((sigma + 1) * u) / R :=
          div_le_div_of_nonneg_right hnum hR0.le
        have hs2 : 2 * a * ((sigma + 1) * u) / R ≤ 2 * a * ((sigma + 1) * u) / (ρ * u) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hRu
        have hval : 2 * a * ((sigma + 1) * u) / (ρ * u) = 2 * a * (sigma + 1) / ρ := by
          field_simp
        linarith [hs1, hs2, hval.le, hval.ge]
      have hf2 : Real.exp (1 / (2 * (a * R))) ≤ Real.exp (1 / (2 * (a * ρ))) := by
        refine Real.exp_le_exp.2 ?_
        exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by nlinarith [hR1, ha0])
      have hf3 : Real.sqrt (2 * Real.pi / (a * R)) ≤ Real.sqrt (2 * Real.pi / (a * ρ)) := by
        refine Real.sqrt_le_sqrt ?_
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [hR1, ha0])
      have hprod : Real.exp (1 / (2 * (a * R))) * Real.sqrt (2 * Real.pi / (a * R))
          ≤ Real.exp (1 / (2 * (a * ρ))) * Real.sqrt (2 * Real.pi / (a * ρ)) :=
        mul_le_mul hf2 hf3 (Real.sqrt_nonneg _) (Real.exp_pos _).le
      rw [hCgdef]
      exact le_trans hmain (mul_le_mul hf1 hprod (by positivity) (by positivity))
  -- the Cauchy iteration on unit-scale discs
  have hiter := norm_xiCausticIterate_le (a := a) ha0 (τ := τ) (z₀ := ((h : ℝ) : ℂ)) (δ := δ)
    (M := Cg) (ε := Cz) (γ := γ₂) n hδ0 hCg0.le
    (fun ζ hζ v hv => by
      rw [mem_closedBall, dist_eq_norm] at hv
      have hvz : ‖v - ((h : ℝ) : ℂ)‖ ≤ 1 := by
        have htri : ‖v - ((h : ℝ) : ℂ)‖ ≤ ‖v - ζ‖ + ‖ζ - ((h : ℝ) : ℂ)‖ := by
          have := norm_add_le (v - ζ) (ζ - ((h : ℝ) : ℂ))
          simpa using this
        linarith [hnδ]
      have := far_mem_xiMassHeightRegion (sigma := sigma) ha hu0 hcone hh
        (s := v - ((h : ℝ) : ℂ)) hvz
      rw [hτdef]
      rwa [← hshift v] at this)
    (fun ζ hζ => by
      have h := (hpt (ζ - ((h : ℝ) : ℂ)) (hnear ζ (by linarith [hδ0.le]))).1
      rwa [← hshift ζ] at h)
    (fun ζ hζ => by
      have h := (hpt (ζ - ((h : ℝ) : ℂ)) (hnear ζ (by linarith [hδ0.le]))).2.1
      rwa [← hshift ζ] at h)
    (fun ζ hζ => by
      have h := (hpt (ζ - ((h : ℝ) : ℂ)) (hnear ζ (by linarith [hδ0.le]))).2.2
      rwa [← hshift ζ] at h)
  have hstepval : Cz + γ₂ / δ + 2 / δ ^ 2
      = Cz + γ₂ * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) ^ 2 := by
    rw [hδdef]
    field_simp
  rw [hstepval] at hiter
  -- transport back to the profile
  have hmem : ((h : ℝ) : ℂ) ∈ xiMassHeightRegion τ := by
    have := far_mem_xiMassHeightRegion (sigma := sigma) ha hu0 hcone hh (s := 0) (by simp)
    rw [hτdef]
    simpa using this
  have hgauge := xiMassJetIterate_eqOn ha0 τ n hmem
  rw [hgauge]
  have hpropeq : τ ^ 2 + ((h : ℝ) : ℂ) ^ 2 = xiMassSpacelikePropagationArgument sigma u h := by
    rw [xiMassSpacelikePropagationArgument_eq, hτdef]
  have hexpnorm : ‖Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ))‖
      = Real.exp (-(a * HTGeometry.csqrtRe (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2))) := by
    rw [Complex.norm_exp]
    congr 1
    have hre := re_mul_xiMassHeightRadius a τ ((h : ℝ) : ℂ)
    have hneg : (-(a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ))
        = -((a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ)) := by ring
    rw [hneg, Complex.neg_re, hre]
  have hgap : Real.sqrt (h ^ 2 - u ^ 2)
      ≤ HTGeometry.csqrtRe (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2) := by
    rw [hpropeq]
    have hmono : Real.sqrt (h ^ 2 - u ^ 2) ≤ Real.sqrt (h ^ 2 - u ^ 2 + sigma ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg sigma])
    exact le_trans hmono (sqrt_fullGap_le_csqrtRe_propagationArgument hsigma hu0.le huh)
  have hexple : Real.exp (-(a * HTGeometry.csqrtRe (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2)))
      ≤ Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [hgap, ha0]
  calc ‖Complex.exp (-(a : ℂ) * xiMassHeightRadius τ ((h : ℝ) : ℂ))
          * xiCausticIterate a τ n ((h : ℝ) : ℂ)‖
      = Real.exp (-(a * HTGeometry.csqrtRe (τ ^ 2 + ((h : ℝ) : ℂ) ^ 2)))
        * ‖xiCausticIterate a τ n ((h : ℝ) : ℂ)‖ := by rw [norm_mul, hexpnorm]
    _ ≤ Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))
        * (Cg * (Cz + γ₂ * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) ^ 2) ^ n) :=
        mul_le_mul hexple hiter (norm_nonneg _) (Real.exp_pos _).le
    _ = Cg * (Cz + γ₂ * ((n : ℝ) + 1) + 2 * ((n : ℝ) + 1) ^ 2) ^ n
        * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by ring

end

end RHTower
