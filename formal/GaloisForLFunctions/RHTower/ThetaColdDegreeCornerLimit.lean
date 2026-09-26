import GaloisForLFunctions.RHTower.ThetaColdDegreeEulerJets

/-!
# Signed cold-aperture / degree profile of the literal theta source

For every `u > 0`, take `L_n = (n + 1/2) / u`. The scaled curvature of the
Gamma-normalized literal theta moments converges to the third derivative of
`log(Phi(sqrt(u)))`. At `u = 9` that limit is negative, so actual theta moment
curvature is eventually negative along the joint diagonal.

This refutes global all-degree Gaussian-aperture convexity. It does not refute the
degree-zero GABTC conjecture or RH. The positive survivor is the exact signed
incoming-profile law, with every source and analytic premise discharged.
-/

open Real Set Filter Topology MeasureTheory
namespace RHTower.ThetaColdCorner
open ColdGamma
noncomputable section

def F (L : ℝ) (j : ℕ) : ℝ := sourceAverage L j thetaCuspFullSource

def scaledDifferenceOne (L : ℝ) (j : ℕ) : ℝ := L*(F L (j+1)-F L j)
def scaledDifferenceTwo (L : ℝ) (j : ℕ) : ℝ := L^2*(F L (j+2)-2*F L (j+1)+F L j)
def scaledDifferenceThree (L : ℝ) (j : ℕ) : ℝ :=
  L^3*(F L (j+3)-3*F L (j+2)+3*F L (j+1)-F L j)

theorem sourceMoment_eq_halfMoment (L : ℝ) (j : ℕ) :
    sourceMoment L j thetaCuspFullSource = thetaCuspGaussianApertureHalfMoment (-L) j := by
  unfold sourceMoment thetaCuspGaussianApertureHalfMoment
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [kernel, thetaCuspGaussianApertureDensity]
  ring

theorem F_pos {L : ℝ} (hL : 0 < L) (j : ℕ) : 0 < F L j := by
  unfold F sourceAverage
  rw [sourceMoment_eq_halfMoment]
  exact div_pos (thetaCuspGaussianApertureHalfMoment_pos (by linarith) j)
    (coldGaussianHalfMoment_pos hL j)

theorem gammaRatio_eq_F {L : ℝ} (hL : 0 < L) (j : ℕ) :
    thetaCuspGaussianApertureGammaRatio (-L) j = F L (j+1)/(L*F L j) := by
  unfold F sourceAverage
  rw [sourceMoment_eq_halfMoment, sourceMoment_eq_halfMoment, coldGaussianHalfMoment_succ hL]
  unfold thetaCuspGaussianApertureGammaRatio
  field_simp [hL.ne', (thetaCuspGaussianApertureGammaShape_pos j).ne',
    (coldGaussianHalfMoment_pos hL j).ne',
    (thetaCuspGaussianApertureHalfMoment_pos (show -L ≤ 0 by linarith) j).ne']

theorem scaledDifferenceOne_eq {L : ℝ} (hL : 0 < L) (j : ℕ) :
    scaledDifferenceOne L j = sourceAverage L j eulerJetOne/
      (thetaCuspGaussianApertureGammaShape j/L) := by
  have h := source_difference_one hL j
  unfold scaledDifferenceOne F
  field_simp [hL.ne', (thetaCuspGaussianApertureGammaShape_pos j).ne']
  linear_combination h

theorem scaledDifferenceTwo_eq {L : ℝ} (hL : 0 < L) (j : ℕ) :
    scaledDifferenceTwo L j = sourceAverage L j eulerJetTwo/
      ((thetaCuspGaussianApertureGammaShape j/L)*((thetaCuspGaussianApertureGammaShape j+1)/L)) := by
  have h := source_difference_two hL j
  have hA := thetaCuspGaussianApertureGammaShape_pos j
  unfold scaledDifferenceTwo F
  field_simp [hL.ne', hA.ne', (show thetaCuspGaussianApertureGammaShape j+1 ≠ 0 by positivity)]
  linear_combination h

theorem scaledDifferenceThree_eq {L : ℝ} (hL : 0 < L) (j : ℕ) :
    scaledDifferenceThree L j = sourceAverage L j eulerJetThree/
      ((thetaCuspGaussianApertureGammaShape j/L)*((thetaCuspGaussianApertureGammaShape j+1)/L)*
        ((thetaCuspGaussianApertureGammaShape j+2)/L)) := by
  have h := source_difference_three hL j
  have hA := thetaCuspGaussianApertureGammaShape_pos j
  unfold scaledDifferenceThree F
  field_simp [hL.ne', hA.ne', (show thetaCuspGaussianApertureGammaShape j+1 ≠ 0 by positivity),
    (show thetaCuspGaussianApertureGammaShape j+2 ≠ 0 by positivity)]
  linear_combination h

/-- Exact rational identity before taking the joint limit. -/
theorem scaled_curvature_eq {L : ℝ} (hL : 0 < L) (j : ℕ) :
    L^4*thetaCuspGaussianApertureRatioCurvature (-L) j =
      (F L j^2*scaledDifferenceThree L j-
        3*F L j*scaledDifferenceOne L j*scaledDifferenceTwo L j+
        2*(scaledDifferenceOne L j)^3+
        L⁻¹*(F L j*scaledDifferenceOne L j*scaledDifferenceThree L j+
          (scaledDifferenceOne L j)^2*scaledDifferenceTwo L j-
          2*F L j*(scaledDifferenceTwo L j)^2))/(F L j*F L (j+1)*F L (j+2)) := by
  simp only [thetaCuspGaussianApertureRatioCurvature, gammaRatio_eq_F hL,
    scaledDifferenceOne, scaledDifferenceTwo, scaledDifferenceThree, Nat.add_assoc]
  field_simp [hL.ne', (F_pos hL j).ne', (F_pos hL (j+1)).ne', (F_pos hL (j+2)).ne']
  ring

/-- Rate of the joint degree/cold-aperture diagonal centered at squared position `u`. -/
def coldRate (u : ℝ) (j : ℕ) : ℝ := thetaCuspGaussianApertureGammaShape j/u

theorem coldRate_pos {u : ℝ} (hu : 0 < u) (j : ℕ) : 0 < coldRate u j :=
  div_pos (thetaCuspGaussianApertureGammaShape_pos j) hu

theorem tendsto_coldRate_inv {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (coldRate u n)⁻¹) atTop (𝓝 0) := by
  have hA : Tendsto (fun n : ℕ => thetaCuspGaussianApertureGammaShape n) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h := (tendsto_inv_atTop_zero.comp hA).const_mul u
  convert! h using 1
  · funext n
    dsimp only [Function.comp_def]
    unfold coldRate
    field_simp
  · ring

theorem shape_div_coldRate {u : ℝ} (hu : 0 < u) (j : ℕ) :
    thetaCuspGaussianApertureGammaShape j/coldRate u j = u := by
  unfold coldRate
  field_simp [(thetaCuspGaussianApertureGammaShape_pos j).ne']

theorem tendsto_shifted_shape_ratio {u : ℝ} (hu : 0 < u) (k : ℕ) :
    Tendsto (fun n : ℕ => thetaCuspGaussianApertureGammaShape (n+k)/coldRate u n) atTop (𝓝 u) := by
  have h := (tendsto_coldRate_inv hu).const_mul (k:ℝ)
  have hh := (tendsto_const_nhds (x := u) (f := atTop)).add h
  convert! hh using 1
  · funext n
    rw [thetaCuspGaussianApertureGammaShape_add, add_div, shape_div_coldRate hu]
    ring
  · ring

theorem tendsto_F_shifted {u : ℝ} (hu : 0 < u) (k : ℕ) :
    Tendsto (fun n => F (coldRate u n) (n+k)) atTop (𝓝 (thetaCuspFullSource (Real.sqrt u))) := by
  obtain ⟨B, hB⟩ := bounded_source
  exact tendsto_sourceAverage contDiff_thetaCuspFullSource.continuous hB hu.le
    (coldRate_pos hu) (tendsto_coldRate_inv hu) (tendsto_shifted_shape_ratio hu k)

theorem tendsto_euler_average {u : ℝ} (hu : 0 < u) {H : ℝ → ℝ}
    (hH : Continuous H) (hB : ∃ B, ∀ x, |H x| ≤ B) :
    Tendsto (fun n => sourceAverage (coldRate u n) n H) atTop (𝓝 (H (Real.sqrt u))) := by
  obtain ⟨B, hB⟩ := hB
  exact tendsto_sourceAverage hH hB hu.le (coldRate_pos hu) (tendsto_coldRate_inv hu)
    (by simpa only [Nat.add_zero] using tendsto_shifted_shape_ratio hu 0)

theorem tendsto_scaledDifferenceOne {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n => scaledDifferenceOne (coldRate u n) n) atTop
      (𝓝 (eulerJetOne (Real.sqrt u)/u)) := by
  have h := (tendsto_euler_average hu continuous_eulerJetOne bounded_eulerJetOne).div
    (tendsto_shifted_shape_ratio hu 0) hu.ne'
  simpa only [Nat.add_zero, scaledDifferenceOne_eq (coldRate_pos hu _)] using! h

theorem tendsto_scaledDifferenceTwo {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n => scaledDifferenceTwo (coldRate u n) n) atTop
      (𝓝 (eulerJetTwo (Real.sqrt u)/u^2)) := by
  have h := (tendsto_euler_average hu continuous_eulerJetTwo bounded_eulerJetTwo).div
    ((tendsto_shifted_shape_ratio hu 0).mul (tendsto_shifted_shape_ratio hu 1)) (mul_ne_zero hu.ne' hu.ne')
  simpa only [Nat.add_zero, thetaCuspGaussianApertureGammaShape_add, Nat.cast_one, ← pow_two,
    scaledDifferenceTwo_eq (coldRate_pos hu _)] using! h

theorem tendsto_scaledDifferenceThree {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n => scaledDifferenceThree (coldRate u n) n) atTop
      (𝓝 (eulerJetThree (Real.sqrt u)/u^3)) := by
  have h := (tendsto_euler_average hu continuous_eulerJetThree bounded_eulerJetThree).div
    (((tendsto_shifted_shape_ratio hu 0).mul (tendsto_shifted_shape_ratio hu 1)).mul
      (tendsto_shifted_shape_ratio hu 2)) (mul_ne_zero (mul_ne_zero hu.ne' hu.ne') hu.ne')
  convert! h using 1
  · funext n
    rw [scaledDifferenceThree_eq (coldRate_pos hu _)]
    simp only [Pi.div_apply, Nat.add_zero, thetaCuspGaussianApertureGammaShape_add, Nat.cast_one, Nat.cast_ofNat]
  · congr 1
    ring


/-- Exact signed incoming profile for every positive squared spatial position. -/
theorem tendsto_scaled_theta_curvature {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (coldRate u n)^4*
      thetaCuspGaussianApertureRatioCurvature (-(coldRate u n)) n) atTop
      (𝓝 (iteratedDeriv 3 squareLog u)) := by
  have h0 : Tendsto (fun n => F (coldRate u n) n) atTop
      (𝓝 (thetaCuspFullSource (Real.sqrt u))) := by
    simpa only [Nat.add_zero] using tendsto_F_shifted hu 0
  have hF1 := tendsto_F_shifted hu 1
  have hF2 := tendsto_F_shifted hu 2
  have h1 := tendsto_scaledDifferenceOne hu
  have h2 := tendsto_scaledDifferenceTwo hu
  have h3 := tendsto_scaledDifferenceThree hu
  have hmain := (((h0.pow 2).mul h3).sub (((h0.mul h1).mul h2).const_mul 3)).add
    ((h1.pow 3).const_mul 2)
  have hrem := (((h0.mul h1).mul h3).add ((h1.pow 2).mul h2)).sub
    ((h0.mul (h2.pow 2)).const_mul 2)
  have hn := hmain.add ((tendsto_coldRate_inv hu).mul hrem)
  have hphi := (thetaCuspFullSource_pos_all (Real.sqrt u)).ne'
  have h := hn.div ((h0.mul hF1).mul hF2) (mul_ne_zero (mul_ne_zero hphi hphi) hphi)
  convert! h using 1
  · funext n
    rw [scaled_curvature_eq (coldRate_pos hu n)]
    simp only [Pi.div_apply]
    ring
  · congr 1
    rw [← euler_profile_eq_log_third hu]
    field_simp [hu.ne', hphi]
    ring

/-- The literal theta source has negative curvature along the exact cold/degree diagonal. -/
theorem eventually_negative_theta_diagonal :
    ∀ᶠ n : ℕ in atTop,
      thetaCuspGaussianApertureRatioCurvature (-(coldRate 9 n)) n < 0 := by
  have h := (tendsto_scaled_theta_curvature (by norm_num : (0:ℝ) < 9)).eventually
    (gt_mem_nhds squareLog_third_nine_neg)
  filter_upwards [h] with n hn
  by_contra hs
  have hnonneg := mul_nonneg (pow_nonneg (coldRate_pos (by norm_num : (0:ℝ)<9) n).le 4)
    (le_of_not_gt hs)
  linarith

/-- Closed literal-source obstruction to global all-degree Gaussian-aperture convexity. -/
theorem not_all_degree_aperture_curvature_nonnegative :
    ¬ ∀ lambda : ℝ, lambda ≤ 0 → ∀ j : ℕ,
      0 ≤ thetaCuspGaussianApertureRatioCurvature lambda j := by
  intro h
  obtain ⟨n, hn⟩ := eventually_negative_theta_diagonal.exists
  have hrate := coldRate_pos (by norm_num : (0:ℝ)<9) n
  have hpos := h (-(coldRate 9 n)) (by linarith) n
  linarith

end
end RHTower.ThetaColdCorner
