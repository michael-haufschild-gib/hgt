import GaloisForLFunctions.RHTower.IsolatedDeepZeroHodgeIndex

/-!
# The exact conductor–forcing gap

The odd detector's squared signal is at most `N² exp(2δa)/2`, where `N`
is its established norm bound. A successful companion-forcing certificate
therefore requires `768 A log(|γ|+3) < exp(2δa)`. This cannot coexist with
the conductor horizon when `0 ≤ δ ≤ 1/2`. The separation holds at every
height, without an asymptotic threshold.
-/

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open RHTower

/-- The exact majorant used by the polar-corrected companion-forcing theorem. -/
def companionCost (a δ R γ A : ℝ) : ℝ :=
  384 * A * Real.log (|γ| + 3) * deepZeroNormBound a δ ^ 2 *
    (1 + Real.exp a / (1 + R)) +
  768 * Real.exp a * A * Real.log (|γ| + 3) * deepZeroNormBound a δ ^ 2 *
    (polarCorrectionBound a γ + polarCorrectionBound a γ ^ 2)

/-- Signal relative to the detector norm, uniformly in the edge width. -/
theorem deepZeroEnergy_le_norm_exp {a δ w : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ)
    (hw : 0 < w) (hwa : w ≤ a / 4) :
    deepZeroEnergyBound a δ w ≤ deepZeroNormBound a δ / 2 * Real.exp (δ * a) := by
  have hwa' : w ≤ a := by linarith only [ha, hwa]
  have hx : 0 ≤ δ * (a - 2 * w) := mul_nonneg hδ (by linarith only [hwa, ha])
  have hxy : δ * (a - 2 * w) ≤ δ * a :=
    mul_le_mul_of_nonneg_left (by linarith only [hw]) hδ
  have hs0 : 0 ≤ Real.sinh (δ * (a - 2 * w)) := Real.sinh_nonneg_iff.mpr hx
  have hs : Real.sinh (δ * (a - 2 * w)) ≤ Real.sinh (δ * a) :=
    Real.sinh_le_sinh.mpr hxy
  have hs2 : Real.sinh (δ * (a - 2 * w)) ^ 2 ≤ Real.cosh (δ * a) ^ 2 := by
    have hh := pow_le_pow_left₀ hs0 hs 2
    nlinarith only [hh, Real.cosh_sq (δ * a)]
  have hr : (w * a) ^ (5 / 2 : ℝ) ≤ a ^ 5 := by
    calc (w * a) ^ (5 / 2 : ℝ) ≤ (a ^ 2) ^ (5 / 2 : ℝ) := by
          apply Real.rpow_le_rpow (mul_nonneg hw.le ha.le) _ (by norm_num)
          nlinarith only [mul_le_mul_of_nonneg_right hwa' ha.le]
      _ = a ^ 5 := by
        rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le]
        norm_num
  have hpoly : a ^ 5 ≤ a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3 := by
    have h1 : 0 ≤ δ ^ 2 * a ^ 5 := mul_nonneg (sq_nonneg _) (pow_nonneg ha.le _)
    have h2 : 0 ≤ 10 * δ * a ^ 4 := by positivity
    have h3 : 0 ≤ 20 * a ^ 3 := by positivity
    linarith only [h1, h2, h3]
  have hN : 2 * a * Real.cosh (δ * a) * a ^ 5 ≤ deepZeroNormBound a δ :=
    mul_le_mul_of_nonneg_left hpoly (by positivity)
  have hcosh : Real.cosh (δ * a) ≤ Real.exp (δ * a) := by
    have hsinh : 0 ≤ Real.sinh (δ * a) := Real.sinh_nonneg_iff.mpr (mul_nonneg hδ ha.le)
    linarith only [Real.cosh_add_sinh (δ * a), hsinh]
  calc deepZeroEnergyBound a δ w
      ≤ a * a ^ 5 * Real.cosh (δ * a) ^ 2 := by
        unfold deepZeroEnergyBound
        exact mul_le_mul (mul_le_mul hwa' hr (Real.rpow_nonneg (mul_nonneg hw.le ha.le) _)
          ha.le) hs2 (sq_nonneg _) (mul_nonneg ha.le (pow_nonneg ha.le _))
    _ = (2 * a * Real.cosh (δ * a) * a ^ 5) / 2 * Real.cosh (δ * a) := by ring
    _ ≤ deepZeroNormBound a δ / 2 * Real.cosh (δ * a) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hN (by norm_num))
        (Real.cosh_pos _).le
    _ ≤ deepZeroNormBound a δ / 2 * Real.exp (δ * a) :=
      mul_le_mul_of_nonneg_left hcosh (div_nonneg (deepZeroNormBound_nonneg ha.le hδ) (by norm_num))

/-- Explicit signal-to-noise ceiling before comparison with the conductor horizon. -/
theorem two_mul_deepZeroEnergy_sq_le {a δ w : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ)
    (hw : 0 < w) (hwa : w ≤ a / 4) :
    2 * deepZeroEnergyBound a δ w ^ 2 ≤
      deepZeroNormBound a δ ^ 2 / 2 * Real.exp (2 * δ * a) := by
  have hE : 0 ≤ deepZeroEnergyBound a δ w := by unfold deepZeroEnergyBound; positivity
  have hs := pow_le_pow_left₀ hE (deepZeroEnergy_le_norm_exp ha hδ hw hwa) 2
  have hexp : Real.exp (δ * a) ^ 2 = Real.exp (2 * δ * a) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he : (deepZeroNormBound a δ / 2 * Real.exp (δ * a)) ^ 2 =
      deepZeroNormBound a δ ^ 2 / 4 * Real.exp (2 * δ * a) := by
    rw [mul_pow, div_pow, hexp]
    norm_num
  rw [he] at hs
  linarith only [hs]

/-- Every successful companion certificate must cross this explicit exponential threshold. -/
theorem forcing_requires_exponential_aperture {a δ w R γ A : ℝ}
    (ha : 0 < a) (hδ : 0 ≤ δ) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hR : 0 ≤ R) (hA : 1 ≤ A)
    (hforce : companionCost a δ R γ A < 2 * deepZeroEnergyBound a δ w ^ 2) :
    768 * A * Real.log (|γ| + 3) < Real.exp (2 * δ * a) := by
  have hlog : 0 < Real.log (|γ| + 3) := Real.log_pos (by linarith [abs_nonneg γ])
  have hN : 0 < deepZeroNormBound a δ := by unfold deepZeroNormBound; positivity
  have hcorr := polarCorrectionBound_nonneg ha γ
  have hcost : 384 * A * Real.log (|γ| + 3) * deepZeroNormBound a δ ^ 2 ≤
      companionCost a δ R γ A := by
    unfold companionCost
    have hbase : 0 ≤ 384 * A * Real.log (|γ| + 3) * deepZeroNormBound a δ ^ 2 := by positivity
    have hextra : 0 ≤ 768 * Real.exp a * A * Real.log (|γ| + 3) * deepZeroNormBound a δ ^ 2 *
        (polarCorrectionBound a γ + polarCorrectionBound a γ ^ 2) := by positivity
    have hratio : 0 ≤ Real.exp a / (1 + R) := by positivity
    nlinarith only [hextra, mul_nonneg hbase hratio]
  have hbound := lt_of_le_of_lt hcost hforce
  have hsignal := two_mul_deepZeroEnergy_sq_le ha hδ hw hwa
  have hN2 := sq_pos_of_pos hN
  apply (mul_lt_mul_right hN2).mp
  linarith only [hbound, hsignal]

/-- The conductor horizon and the exact sufficient forcing criterion have no common aperture. -/
theorem conductor_forcing_disjoint {a δ w R γ A C ε : ℝ}
    (ha : 0 < a) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hw : 0 < w) (hwa : w ≤ a / 4) (hR : 0 ≤ R) (hA : 1 ≤ A)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    ¬ (C + (4 + ε) * Real.exp a + 2 ≤ Real.log (1 + |γ| / 8) ∧
      companionCost a δ R γ A < 2 * deepZeroEnergyBound a δ w ^ 2) := by
  rintro ⟨hhorizon, hforce⟩
  have hnecessary := forcing_requires_exponential_aperture ha hδ hw hwa hR hA hforce
  have hexp : Real.exp (2 * δ * a) ≤ Real.exp a :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hδhalf)])
  have hlogcmp : Real.log (1 + |γ| / 8) ≤ Real.log (|γ| + 3) :=
    Real.log_le_log (by positivity) (by linarith [abs_nonneg γ])
  have hlog : 0 ≤ Real.log (|γ| + 3) := Real.log_nonneg (by linarith [abs_nonneg γ])
  have hAlog : Real.log (|γ| + 3) ≤ A * Real.log (|γ| + 3) :=
    le_mul_of_one_le_left hlog hA
  have heps : 0 ≤ ε * Real.exp a := mul_nonneg hε (Real.exp_pos _).le
  have hpos := Real.exp_pos a
  nlinarith only [hhorizon, hnecessary, hexp, hlogcmp, hAlog, hC, heps, hpos]

end GaloisForLFunctions.ConjugateDiagonalGeometry
