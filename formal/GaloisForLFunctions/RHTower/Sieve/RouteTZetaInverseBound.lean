import GaloisForLFunctions.RHTower.Sieve.RouteTZetaZeroFreeMonotonicity
import GaloisForLFunctions.HTGeometry.BallLogarithm

/-!
# Reciprocal zeta bound from the Route-T zero-free region

The pointwise Route-T region is made uniform on a Harnack disc by taking its width at the upper
ordinate `γ + 1`.  The disc is centred at `1 + δ + iγ`, has outer radius `43δ/40`, and contains the
whole horizontal segment down to `1 - δ/20`.  Its left edge remains strictly inside the certified
zero-free region `1 - δ/10`.  Borel--Carathéodory then transports the three-four-one lower bound at
the centre across that segment.
-/

namespace RHTower.Sieve

open Complex Metric
open GaloisForLFunctions.HTGeometry

noncomputable section

def routeTInverseHeight (γ : ℝ) : ℝ := γ + 1

def routeTInverseDelta (A γ : ℝ) : ℝ :=
  routeTZeroFreeDelta A (routeTInverseHeight γ)

def routeTInverseOuterRadius (A γ : ℝ) : ℝ :=
  43 / 40 * routeTInverseDelta A γ

def routeTInverseInnerRadius (A γ : ℝ) : ℝ :=
  21 / 20 * routeTInverseDelta A γ

def routeTInverseAnchor (A γ : ℝ) : ℂ :=
  ((1 + routeTInverseDelta A γ : ℝ) : ℂ) + (γ : ℂ) * Complex.I

/-- Fixed height beyond which the Route-T depth premise is automatic by construction. -/
def routeTInverseBaseHeight : ℝ :=
  ((2 ^ (routeTBandDepthRootThreshold ^ 10 + 1) : ℕ) : ℝ) + 100001

theorem routeTInverseBaseHeight_ge : 100001 ≤ routeTInverseBaseHeight := by
  unfold routeTInverseBaseHeight
  have hnonneg :
      (0 : ℝ) ≤ ((2 ^ (routeTBandDepthRootThreshold ^ 10 + 1) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  linarith

theorem routeTInverseBaseDepth :
    routeTBandDepthRootThreshold ^ 10 ≤
      routeTBinaryHeight (routeTInverseBaseHeight - 1) := by
  let K := routeTBandDepthRootThreshold ^ 10
  let P : ℕ := 2 ^ (K + 1)
  have hpow : 2 ^ K < P := by
    dsimp only [P]
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self K)
  have hclog : K < Nat.clog 2 P :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hpow
  have hbinary : K ≤ routeTBinaryHeight (P : ℝ) := by
    unfold routeTBinaryHeight
    rw [Nat.ceil_natCast]
    omega
  have hheight : (P : ℝ) ≤ routeTInverseBaseHeight - 1 := by
    change (P : ℝ) ≤ ((2 ^ (K + 1) : ℕ) : ℝ) + 100001 - 1
    have hP : P = 2 ^ (K + 1) := rfl
    rw [← hP]
    have hP0 : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg _
    linarith
  exact hbinary.trans (routeTBinaryHeight_mono hheight)

theorem routeTInverseDelta_pos (A γ : ℝ) : 0 < routeTInverseDelta A γ := by
  exact routeTZeroFreeDelta_pos A (routeTInverseHeight γ)

theorem routeTInverseDelta_le_sixteenth (A γ : ℝ) :
    routeTInverseDelta A γ ≤ 1 / 16 := by
  exact routeTZeroFreeDelta_le_sixteenth A (routeTInverseHeight γ)

theorem routeTInverseOuterRadius_pos (A γ : ℝ) :
    0 < routeTInverseOuterRadius A γ := by
  unfold routeTInverseOuterRadius
  exact mul_pos (by norm_num) (routeTInverseDelta_pos A γ)

theorem routeTInverseOuterRadius_lt_one (A γ : ℝ) :
    routeTInverseOuterRadius A γ < 1 := by
  have hδ := routeTInverseDelta_le_sixteenth A γ
  unfold routeTInverseOuterRadius
  nlinarith

theorem routeTInverseInnerRadius_nonneg (A γ : ℝ) :
    0 ≤ routeTInverseInnerRadius A γ := by
  unfold routeTInverseInnerRadius
  exact mul_nonneg (by norm_num) (routeTInverseDelta_pos A γ).le

theorem routeTInverseInnerRadius_lt_outer (A γ : ℝ) :
    routeTInverseInnerRadius A γ < routeTInverseOuterRadius A γ := by
  have hδ := routeTInverseDelta_pos A γ
  unfold routeTInverseInnerRadius routeTInverseOuterRadius
  nlinarith

private theorem routeT_inverse_ball_coordinates {A γ : ℝ} {w : ℂ}
    (hw : w ∈ ball (routeTInverseAnchor A γ) (routeTInverseOuterRadius A γ)) :
    γ - 1 < w.im ∧ w.im < γ + 1 ∧
      1 - 3 / 40 * routeTInverseDelta A γ < w.re ∧
      w.re < 1 + routeTInverseDelta A γ + routeTInverseOuterRadius A γ := by
  have hd : ‖w - routeTInverseAnchor A γ‖ < routeTInverseOuterRadius A γ := by
    simpa [dist_eq_norm] using hw
  have hre := Complex.abs_re_le_norm (w - routeTInverseAnchor A γ)
  have him := Complex.abs_im_le_norm (w - routeTInverseAnchor A γ)
  have hanchorRe : (routeTInverseAnchor A γ).re = 1 + routeTInverseDelta A γ := by
    simp [routeTInverseAnchor]
  have hanchorIm : (routeTInverseAnchor A γ).im = γ := by
    simp [routeTInverseAnchor]
  rw [Complex.sub_re, hanchorRe] at hre
  rw [Complex.sub_im, hanchorIm] at him
  have hre' := abs_lt.mp (lt_of_le_of_lt hre hd)
  have him' := abs_lt.mp (lt_of_le_of_lt him hd)
  have hR1 := routeTInverseOuterRadius_lt_one A γ
  have hleft :
      1 - 3 / 40 * routeTInverseDelta A γ =
        1 + routeTInverseDelta A γ - routeTInverseOuterRadius A γ := by
    unfold routeTInverseOuterRadius
    ring
  rw [hleft]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 800000 in
/-- **Uniform zero-free Harnack disc.**  Width monotonicity absorbs every shell jump inside the
unit ordinate band. -/
theorem routeT_zero_free_inverse_ball
    {A γ : ℝ}
    (hA : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A)
    (hγ : 100001 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight (γ - 1)) :
    ∀ w ∈ ball (routeTInverseAnchor A γ) (routeTInverseOuterRadius A γ),
      riemannZeta w ≠ 0 := by
  intro w hw
  obtain ⟨hylo, hyhi, hrelo, _hrehi⟩ := routeT_inverse_ball_coordinates hw
  have hy100 : 100000 ≤ w.im := by linarith
  have hybase : 8 * Real.pi + 1 ≤ w.im := by
    have hpi := Real.pi_lt_d2
    linarith
  have hlargeY : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight w.im :=
    hlarge.trans (routeTBinaryHeight_mono (by linarith : γ - 1 ≤ w.im))
  have hwidth : routeTZeroFreeWidth A (γ + 1) ≤ routeTZeroFreeWidth A w.im := by
    exact routeTZeroFreeWidth_antitone hybase hyhi.le
  have hdeltaWidth :
      routeTZeroFreeWidth A (γ + 1) = routeTInverseDelta A γ / 10 := by
    rfl
  by_cases hright : 1 ≤ w.re
  · exact riemannZeta_ne_zero_of_one_le_re hright
  · have hnearUpper : 1 - routeTZeroFreeWidth A (γ + 1) < w.re := by
      rw [hdeltaWidth]
      linarith
    have hnear : 1 - routeTZeroFreeWidth A w.im < w.re := by
      linarith
    have hz := riemannZeta_ne_zero_routeT_region hA hy100 hlargeY (le_of_not_ge hright) hnear
    have hwdecomp : ((w.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = w :=
      Complex.re_add_im w
    rw [hwdecomp] at hz
    exact hz

private theorem routeTInverseOuterRadius_lt_stripWidth {A γ : ℝ}
    (hγ : 0 ≤ γ) :
    routeTInverseOuterRadius A γ < routeTStripWidth (routeTBandShell γ) := by
  let H := routeTInverseHeight γ
  let Q := routeTZeroFreeBudget A H
  let R := routeTLandauRadius H
  have hQ := routeTZeroFreeBudget_ge A H
  have hQ0 : 0 < Q := by simpa only [Q] using routeTZeroFreeBudget_pos A H
  have hR0 : 0 < R := by simpa only [R] using routeTLandauRadius_pos H
  have hden : (10000 : ℝ) ≤ 10000 * Q ^ 2 := by nlinarith
  have hden0 : 0 < 10000 * Q ^ 2 := by positivity
  have hδle : routeTInverseDelta A γ ≤ R / 10000 := by
    dsimp only [routeTInverseDelta, H, R, Q, routeTInverseHeight]
    unfold routeTZeroFreeDelta
    exact div_le_div_of_nonneg_left hR0.le (by norm_num) hden
  have houterR : routeTInverseOuterRadius A γ < R := by
    unfold routeTInverseOuterRadius
    have hscaled := mul_le_mul_of_nonneg_left hδle (by norm_num : (0 : ℝ) ≤ 43 / 40)
    nlinarith
  have hwidth := routeTBandWidth_antitone
    (show γ ≤ 4 * H by dsimp only [H, routeTInverseHeight]; linarith)
  have hRwidth : R < routeTStripWidth (routeTBandShell γ) := by
    dsimp only [R, routeTLandauRadius]
    have hpos := routeTStripWidth_pos (routeTBandShell (4 * H))
    linarith
  exact houterR.trans hRwidth

/-- Route-T growth on the full Harnack disc. -/
theorem norm_riemannZeta_le_routeT_inverse_ball
    {A γ : ℝ} (hγ : 100001 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight (γ - 1))
    {w : ℂ} (hw : w ∈ ball (routeTInverseAnchor A γ) (routeTInverseOuterRadius A γ)) :
    ‖riemannZeta w‖ ≤ routeTBandGrowthBound γ := by
  obtain ⟨hylo, hyhi, hrelo, hrehi⟩ := routeT_inverse_ball_coordinates hw
  have hlargeγ : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight γ :=
    hlarge.trans (routeTBinaryHeight_mono (by linarith : γ - 1 ≤ γ))
  have hstrip := routeTInverseOuterRadius_lt_stripWidth (A := A) (by linarith : 0 ≤ γ)
  have hσlo : routeTStripAbscissa (routeTBandShell γ) ≤ w.re := by
    unfold routeTStripAbscissa
    have hδ := routeTInverseDelta_pos A γ
    unfold routeTInverseOuterRadius at hstrip
    linarith
  have hδ := routeTInverseDelta_le_sixteenth A γ
  have hσhi : w.re ≤ 2 := by
    unfold routeTInverseOuterRadius at hrehi
    nlinarith
  have hrect := norm_riemannZeta_le_routeT_band_rectangle (by linarith) hlargeγ hylo.le hyhi.le
    hσlo hσhi
  have hwdecomp : ((w.re : ℝ) : ℂ) + Complex.I * (w.im : ℂ) = w := by
    rw [mul_comm]
    exact Complex.re_add_im w
  rw [hwdecomp] at hrect
  exact hrect

/-- Three-four-one supplies an explicit lower anchor on the right of the abscissa. -/
theorem routeT_inverse_anchor_lower
    {A γ : ℝ} (hγ : 100001 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight (γ - 1)) :
    Real.exp (-(2 * routeTZeroFreeBudget A (routeTInverseHeight γ) ^ 2)) ≤
      ‖riemannZeta (routeTInverseAnchor A γ)‖ := by
  let H := routeTInverseHeight γ
  let Q := routeTZeroFreeBudget A H
  let δ := routeTInverseDelta A γ
  have hγ100 : 100000 ≤ γ := by linarith
  have hbase : 8 * Real.pi + 1 ≤ γ := by
    have hpi := Real.pi_lt_d2
    linarith
  have hlargeγ : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight γ :=
    hlarge.trans (routeTBinaryHeight_mono (by linarith : γ - 1 ≤ γ))
  have hδ0 : 0 < δ := by simpa only [δ] using routeTInverseDelta_pos A γ
  have hδ16 : δ ≤ 1 / 16 := by
    simpa only [δ] using routeTInverseDelta_le_sixteenth A γ
  have hPhiMono : routeTLandauPhi γ ≤ routeTLandauPhi H := by
    exact routeTLandauPhi_mono hbase (by simp [H, routeTInverseHeight])
  have hBγ := routeT_landau_disc_growth_second
    (γ := γ) (δ := δ) hγ100 hlargeγ hδ0 hδ16
    (w := (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I))
    (Metric.mem_ball_self (routeTLandauRadius_pos γ))
  have hB :
      ‖riemannZeta (((1 + δ : ℝ) : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤
        routeTLandauPhi H := by
    have hcast : ((2 * γ : ℝ) : ℂ) = (2 * γ : ℂ) := by push_cast; ring
    rw [hcast] at hBγ
    exact hBγ.le.trans hPhiMono
  have hneg := neg_log_norm_riemannZeta_le_of
    (σ := 1 + δ) (t := γ) (Φ := routeTLandauPhi H) (by linarith) hB
  have hlogPhi : Real.log (routeTLandauPhi H) ≤ Q ^ 2 := by
    simpa only [Q] using routeT_log_phi_le_budget_sq A H
  have hlogδ : Real.log (1 + 1 / δ) ≤ Q ^ 2 := by
    simpa only [δ, routeTInverseDelta, H] using routeT_log_delta_le_budget_sq A H
  have hQ := routeTZeroFreeBudget_ge A H
  have hQsq : (6 : ℝ) ≤ Q ^ 2 := by nlinarith
  have hneg' :
      -Real.log ‖riemannZeta (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤
        2 * Q ^ 2 := by
    have hδrw : (1 + δ : ℝ) - 1 = δ := by ring
    rw [hδrw] at hneg
    nlinarith
  have hnonzero :
      riemannZeta (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hnormpos :
      0 < ‖riemannZeta (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr hnonzero
  have hloglower :
      -(2 * Q ^ 2) ≤
        Real.log ‖riemannZeta (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := by
    linarith
  have hexp := Real.exp_le_exp.mpr hloglower
  rw [Real.exp_log hnormpos] at hexp
  simpa only [H, Q, δ, routeTInverseAnchor] using hexp

set_option maxHeartbeats 800000 in
/-- **Quantitative minimum modulus on the Route-T inner segment.** -/
theorem exp_neg_routeT_budget_sq_le_norm_riemannZeta
    {A γ σ : ℝ}
    (hA : ∀ x : ℝ, 1 < x → x ≤ 2 →
      (-deriv riemannZeta (x : ℂ) / riemannZeta (x : ℂ)).re ≤ 1 / (x - 1) + A)
    (hγ : 100001 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight (γ - 1))
    (hσlo : 1 - routeTInverseDelta A γ / 20 ≤ σ)
    (hσhi : σ ≤ 1 + routeTInverseDelta A γ) :
    Real.exp (-(400 * routeTZeroFreeBudget A (routeTInverseHeight γ) ^ 2)) ≤
      ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ := by
  let H := routeTInverseHeight γ
  let Q := routeTZeroFreeBudget A H
  let δ := routeTInverseDelta A γ
  let c := routeTInverseAnchor A γ
  let R := routeTInverseOuterRadius A γ
  let r := routeTInverseInnerRadius A γ
  let M := routeTBandGrowthBound γ
  let m := Real.exp (-(2 * Q ^ 2))
  have hδ0 : 0 < δ := by simpa only [δ] using routeTInverseDelta_pos A γ
  have hR0 : 0 < R := by simpa only [R] using routeTInverseOuterRadius_pos A γ
  have hr0 : 0 ≤ r := by simpa only [r] using routeTInverseInnerRadius_nonneg A γ
  have hrR : r < R := by simpa only [r, R] using routeTInverseInnerRadius_lt_outer A γ
  have hfree : ∀ w ∈ ball c R, riemannZeta w ≠ 0 := by
    simpa only [c, R] using routeT_zero_free_inverse_ball hA hγ hlarge
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c R) := by
    intro w hw
    obtain ⟨hylo, _hyhi, _hrelo, _hrehi⟩ :=
      routeT_inverse_ball_coordinates (A := A) (γ := γ) (w := w) (by simpa only [c, R] using hw)
    have hwone : w ≠ 1 := by
      intro heq
      subst heq
      simp at hylo
      linarith
    exact (differentiableAt_riemannZeta hwone).differentiableWithinAt
  have hM : ∀ w ∈ ball c R, ‖riemannZeta w‖ ≤ M := by
    intro w hw
    exact norm_riemannZeta_le_routeT_inverse_ball hγ hlarge (by simpa only [c, R] using hw)
  have hm0 : 0 < m := by dsimp only [m]; positivity
  have hm : m ≤ ‖riemannZeta c‖ := by
    simpa only [m, Q, H, c] using routeT_inverse_anchor_lower (A := A) hγ hlarge
  let z : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I
  have hzdist : ‖z - c‖ ≤ r := by
    have hdiffz : z - c = (((σ - (1 + δ) : ℝ)) : ℂ) := by
      dsimp only [z, c, routeTInverseAnchor, δ]
      push_cast
      ring
    rw [hdiffz, Complex.norm_real, Real.norm_eq_abs]
    have hleft : -(21 / 20 * δ) ≤ σ - (1 + δ) := by
      change 1 - δ / 20 ≤ σ at hσlo
      linarith
    have hright : σ - (1 + δ) ≤ 21 / 20 * δ := by
      change σ ≤ 1 + δ at hσhi
      linarith
    rw [abs_le]
    simpa only [r, routeTInverseInnerRadius] using And.intro hleft hright
  have hBC := norm_lower_bound_of_ball hr0 hrR hdiff hfree hM hm0 hm hzdist
  have hbase : 8 * Real.pi + 1 ≤ γ := by
    have hpi := Real.pi_lt_d2
    linarith
  have hPhiMono : routeTLandauPhi γ ≤ routeTLandauPhi H := by
    exact routeTLandauPhi_mono hbase (by simp [H, routeTInverseHeight])
  have hMPhi : M ≤ routeTLandauPhi H := by
    exact (routeTBandGrowthBound_lt_landauPhi_first γ).le.trans hPhiMono
  have hMone : 1 ≤ M := by
    simpa only [M] using routeTBandGrowthBound_one_le γ
  have hMpos : 0 < M := by linarith
  have hlogM : Real.log M ≤ Q ^ 2 := by
    have hlog := Real.log_le_log hMpos hMPhi
    have hbudget : Real.log (routeTLandauPhi H) ≤ Q ^ 2 := by
      simpa only [Q] using routeT_log_phi_le_budget_sq A H
    exact hlog.trans hbudget
  have hlogm : Real.log m = -(2 * Q ^ 2) := by
    dsimp only [m]
    rw [Real.log_exp]
  have hlogRatio : Real.log (M / m) ≤ 3 * Q ^ 2 := by
    rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hm0), hlogm]
    linarith
  have hQ := routeTZeroFreeBudget_ge A H
  have hQsq : (1 : ℝ) ≤ Q ^ 2 := by nlinarith
  have hratio : r / (R - r) = 42 := by
    dsimp only [r, R, routeTInverseInnerRadius, routeTInverseOuterRadius, δ]
    have hδne : routeTInverseDelta A γ ≠ 0 := ne_of_gt (routeTInverseDelta_pos A γ)
    field_simp [hδne]
    ring
  have htransport :
      2 * (Real.log (M / m) + 1) * r / (R - r) ≤ 336 * Q ^ 2 := by
    rw [show 2 * (Real.log (M / m) + 1) * r / (R - r) =
        2 * (Real.log (M / m) + 1) * (r / (R - r)) by ring, hratio]
    nlinarith
  have hfloor :
      Real.exp (-(400 * Q ^ 2)) ≤
        m * Real.exp (-(2 * (Real.log (M / m) + 1) * r / (R - r))) := by
    dsimp only [m]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hfloor.trans (by simpa only [z] using hBC)

/-- **Route-T reciprocal-zeta bound on the inner segment.** -/
theorem norm_inv_riemannZeta_le_routeT
    {A γ σ : ℝ}
    (hA : ∀ x : ℝ, 1 < x → x ≤ 2 →
      (-deriv riemannZeta (x : ℂ) / riemannZeta (x : ℂ)).re ≤ 1 / (x - 1) + A)
    (hγ : 100001 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight (γ - 1))
    (hσlo : 1 - routeTInverseDelta A γ / 20 ≤ σ)
    (hσhi : σ ≤ 1 + routeTInverseDelta A γ) :
    ‖(riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I))⁻¹‖ ≤
      Real.exp (400 * routeTZeroFreeBudget A (routeTInverseHeight γ) ^ 2) := by
  have hlow := exp_neg_routeT_budget_sq_le_norm_riemannZeta
    hA hγ hlarge hσlo hσhi
  have hnonzero := routeT_zero_free_inverse_ball hA hγ hlarge
  have hpoint :
      ((σ : ℂ) + (γ : ℂ) * Complex.I) ∈
        ball (routeTInverseAnchor A γ) (routeTInverseOuterRadius A γ) := by
    rw [mem_ball_iff_norm]
    have hdiff :
        (σ : ℂ) + (γ : ℂ) * Complex.I - routeTInverseAnchor A γ =
          (((σ - (1 + routeTInverseDelta A γ) : ℝ)) : ℂ) := by
      simp only [routeTInverseAnchor]
      push_cast
      ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
    have hδ := routeTInverseDelta_pos A γ
    have habs : |σ - (1 + routeTInverseDelta A γ)| ≤
        21 / 20 * routeTInverseDelta A γ := by
      rw [abs_le]
      constructor <;> linarith
    have hinner := routeTInverseInnerRadius_lt_outer A γ
    unfold routeTInverseInnerRadius at hinner
    exact lt_of_le_of_lt habs hinner
  have hz := hnonzero _ hpoint
  have hnormpos : 0 < ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr hz
  rw [norm_inv, inv_eq_one_div, div_le_iff₀ hnormpos]
  have hmul := mul_le_mul_of_nonneg_left hlow
    (Real.exp_nonneg (400 * routeTZeroFreeBudget A (routeTInverseHeight γ) ^ 2))
  have hcancel :
      Real.exp (400 * routeTZeroFreeBudget A (routeTInverseHeight γ) ^ 2) *
          Real.exp (-(400 * routeTZeroFreeBudget A (routeTInverseHeight γ) ^ 2)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hcancel] at hmul
  exact hmul

/-- **Absolute-height Route-T reciprocal bound.** -/
theorem norm_inv_riemannZeta_le_routeT_abs
    {A γ σ : ℝ}
    (hA : ∀ x : ℝ, 1 < x → x ≤ 2 →
      (-deriv riemannZeta (x : ℂ) / riemannZeta (x : ℂ)).re ≤ 1 / (x - 1) + A)
    (hγ : 100001 ≤ |γ|)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight (|γ| - 1))
    (hσlo : 1 - routeTInverseDelta A |γ| / 20 ≤ σ)
    (hσhi : σ ≤ 1 + routeTInverseDelta A |γ|) :
    ‖(riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I))⁻¹‖ ≤
      Real.exp (400 * routeTZeroFreeBudget A (routeTInverseHeight |γ|) ^ 2) := by
  rcases le_or_gt 0 γ with hγ0 | hγ0
  · have habs : |γ| = γ := abs_of_nonneg hγ0
    rw [habs] at hγ hlarge hσlo hσhi ⊢
    exact norm_inv_riemannZeta_le_routeT hA hγ hlarge hσlo hσhi
  · have habs : |γ| = -γ := abs_of_neg hγ0
    rw [habs] at hγ hlarge hσlo hσhi ⊢
    have hpos := norm_inv_riemannZeta_le_routeT
      (A := A) (γ := -γ) (σ := σ) hA hγ hlarge hσlo hσhi
    have hc :
        ((σ : ℂ) + (γ : ℂ) * Complex.I) =
          (starRingEnd ℂ) ((σ : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> simp
    rw [hc, riemannZeta_conj]
    simpa using hpos

/-- Existence form with the absolute pole constant hidden. -/
theorem exists_norm_inv_riemannZeta_le_routeT_abs :
    ∃ A : ℝ, ∀ γ σ : ℝ,
      100001 ≤ |γ| →
      routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight (|γ| - 1) →
      1 - routeTInverseDelta A |γ| / 20 ≤ σ →
      σ ≤ 1 + routeTInverseDelta A |γ| →
      ‖(riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I))⁻¹‖ ≤
        Real.exp (400 * routeTZeroFreeBudget A (routeTInverseHeight |γ|) ^ 2) := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  exact ⟨A, fun _γ _σ hγ hlarge hσlo hσhi =>
    norm_inv_riemannZeta_le_routeT_abs hA hγ hlarge hσlo hσhi⟩

end

end RHTower.Sieve
