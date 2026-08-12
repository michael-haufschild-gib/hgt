import GaloisForLFunctions.RHTower.Sieve.RouteTZetaBandRectangle
import GaloisForLFunctions.RHTower.Sieve.ZetaWideDLVP

/-!
# Route-T growth on the Landau discs

The common radius is half the Route-T width at height `4γ`.  Width antitonicity makes this radius
valid at heights `γ` and `2γ`; unit-band growth absorbs the vertical motion inside each disc.
-/

namespace RHTower.Sieve

open Complex Metric

noncomputable section

def routeTLandauRadius (γ : ℝ) : ℝ :=
  routeTStripWidth (routeTBandShell (4 * γ)) / 2

def routeTLandauPhi (γ : ℝ) : ℝ :=
  routeTBandGrowthBound γ + routeTBandGrowthBound (2 * γ) +
    routeTBandGrowthBound (4 * γ) + 1

theorem routeTLandauRadius_pos (γ : ℝ) : 0 < routeTLandauRadius γ := by
  unfold routeTLandauRadius
  exact div_pos (routeTStripWidth_pos _) (by norm_num)

theorem routeTLandauRadius_lt_half (γ : ℝ) : routeTLandauRadius γ < 1 / 2 := by
  unfold routeTLandauRadius
  linarith [routeTStripWidth_lt_one (routeTBandShell (4 * γ))]

theorem routeTLandauPhi_one_le (γ : ℝ) : 1 ≤ routeTLandauPhi γ := by
  have h1 := routeTBandGrowthBound_one_le γ
  have h2 := routeTBandGrowthBound_one_le (2 * γ)
  have h4 := routeTBandGrowthBound_one_le (4 * γ)
  unfold routeTLandauPhi
  linarith

theorem routeTBandGrowthBound_lt_landauPhi_first (γ : ℝ) :
    routeTBandGrowthBound γ < routeTLandauPhi γ := by
  have h2 := routeTBandGrowthBound_one_le (2 * γ)
  have h4 := routeTBandGrowthBound_one_le (4 * γ)
  unfold routeTLandauPhi
  linarith

theorem routeTBandGrowthBound_lt_landauPhi_second (γ : ℝ) :
    routeTBandGrowthBound (2 * γ) < routeTLandauPhi γ := by
  have h1 := routeTBandGrowthBound_one_le γ
  have h4 := routeTBandGrowthBound_one_le (4 * γ)
  unfold routeTLandauPhi
  linarith

theorem routeTBandGrowthBound_lt_landauPhi_fourth (γ : ℝ) :
    routeTBandGrowthBound (4 * γ) < routeTLandauPhi γ := by
  have h1 := routeTBandGrowthBound_one_le γ
  have h2 := routeTBandGrowthBound_one_le (2 * γ)
  unfold routeTLandauPhi
  linarith

/-- A Landau disc at any certified centre is controlled by that centre's rectangle. -/
theorem norm_riemannZeta_lt_routeT_landauPhi_of_ball
    {γ c δ : ℝ} (hγ : 100000 ≤ γ) (hcγ : γ ≤ c) (hc4 : c ≤ 4 * γ)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight γ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    (hcPhi : routeTBandGrowthBound c < routeTLandauPhi γ)
    {w : ℂ} (hw : w ∈ ball (((1 + δ : ℝ) : ℂ) + (c : ℂ) * Complex.I)
      (routeTLandauRadius γ)) :
    ‖riemannZeta w‖ < routeTLandauPhi γ := by
  have hγ0 : 0 < γ := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le hγ0 hcγ
  have hc100 : 100000 ≤ c := hγ.trans hcγ
  have hc4pos : 0 ≤ 4 * γ := by positivity
  have hlargec : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight c :=
    hlarge.trans (routeTBinaryHeight_mono hcγ)
  have hd : ‖w - (((1 + δ : ℝ) : ℂ) + (c : ℂ) * Complex.I)‖ <
      routeTLandauRadius γ := by simpa [dist_eq_norm] using hw
  have hcre : ((((1 + δ : ℝ) : ℂ) + (c : ℂ) * Complex.I)).re = 1 + δ := by simp
  have hcim : ((((1 + δ : ℝ) : ℂ) + (c : ℂ) * Complex.I)).im = c := by simp
  have hre : |w.re - (1 + δ)| < routeTLandauRadius γ := by
    have hh := Complex.abs_re_le_norm
      (w - (((1 + δ : ℝ) : ℂ) + (c : ℂ) * Complex.I))
    rw [Complex.sub_re, hcre] at hh
    exact lt_of_le_of_lt hh hd
  have him : |w.im - c| < routeTLandauRadius γ := by
    have hh := Complex.abs_im_le_norm
      (w - (((1 + δ : ℝ) : ℂ) + (c : ℂ) * Complex.I))
    rw [Complex.sub_im, hcim] at hh
    exact lt_of_le_of_lt hh hd
  have hre' := abs_lt.mp hre
  have him' := abs_lt.mp him
  have hradHalf := routeTLandauRadius_lt_half γ
  have hradOne : routeTLandauRadius γ ≤ 1 := by linarith
  have hylo : c - 1 ≤ w.im := by linarith [him'.1]
  have hyhi : w.im ≤ c + 1 := by linarith [him'.2]
  have hwidth : routeTStripWidth (routeTBandShell (4 * γ)) ≤
      routeTStripWidth (routeTBandShell c) := routeTBandWidth_antitone hc4
  have hσlo : routeTStripAbscissa (routeTBandShell c) ≤ w.re := by
    have hwidth0 := routeTStripWidth_pos (routeTBandShell (4 * γ))
    have hhalf : routeTStripWidth (routeTBandShell (4 * γ)) / 2 ≤
        routeTStripWidth (routeTBandShell c) := by linarith
    unfold routeTStripAbscissa
    have hlo := hre'.1
    unfold routeTLandauRadius at hlo
    linarith
  have hσhi : w.re ≤ 2 := by linarith [hre'.2, hradHalf, hδ]
  have hrect := norm_riemannZeta_le_routeT_band_rectangle hc100 hlargec hylo hyhi hσlo hσhi
  have hwdecomp : ((w.re : ℝ) : ℂ) + Complex.I * ((w.im : ℝ) : ℂ) = w := by
    rw [mul_comm]
    exact Complex.re_add_im w
  rw [hwdecomp] at hrect
  exact lt_of_le_of_lt hrect hcPhi

/-- Growth on the first Landau disc. -/
theorem routeT_landau_disc_growth_first
    {γ δ : ℝ} (hγ : 100000 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight γ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    {w : ℂ} (hw : w ∈ ball (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
      (routeTLandauRadius γ)) :
    ‖riemannZeta w‖ < routeTLandauPhi γ := by
  exact norm_riemannZeta_lt_routeT_landauPhi_of_ball hγ le_rfl (by linarith) hlarge
    hδ0 hδ (routeTBandGrowthBound_lt_landauPhi_first γ) hw

/-- Growth on the doubled-height Landau disc. -/
theorem routeT_landau_disc_growth_second
    {γ δ : ℝ} (hγ : 100000 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight γ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    {w : ℂ} (hw : w ∈ ball (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)
      (routeTLandauRadius γ)) :
    ‖riemannZeta w‖ < routeTLandauPhi γ := by
  exact norm_riemannZeta_lt_routeT_landauPhi_of_ball hγ (by linarith) (by linarith) hlarge
    hδ0 hδ (routeTBandGrowthBound_lt_landauPhi_second γ) hw

/-- Growth at four times the height, the third input of the DLVP inequality. -/
theorem routeT_landau_growth_fourth
    {γ δ : ℝ} (hγ : 100000 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight γ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16) :
    ‖riemannZeta (((1 + δ : ℝ) : ℂ) + ((4 * γ : ℝ) : ℂ) * Complex.I)‖ <
      routeTLandauPhi γ := by
  have hlarge4 : routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight (4 * γ) :=
    hlarge.trans (routeTBinaryHeight_mono (by linarith))
  have hrect := norm_riemannZeta_le_routeT_band_rectangle
    (t := 4 * γ) (y := 4 * γ) (σ := 1 + δ) (by linarith) hlarge4
    (by linarith) (by linarith) (by
      unfold routeTStripAbscissa
      linarith [routeTStripWidth_pos (routeTBandShell (4 * γ))]) (by linarith)
  have hrect' :
      ‖riemannZeta (((1 + δ : ℝ) : ℂ) + ((4 * γ : ℝ) : ℂ) * Complex.I)‖ ≤
        routeTBandGrowthBound (4 * γ) := by
    simpa only [mul_comm] using hrect
  exact lt_of_le_of_lt hrect' (routeTBandGrowthBound_lt_landauPhi_fourth γ)

end

end RHTower.Sieve
