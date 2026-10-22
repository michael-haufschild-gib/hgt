import GaloisForLFunctions.RHTower.CCM.CCMActualHeadSupportedCoherentGamma

/-!
# Physical stability of the complete coherent Gamma cost

The estimate acts on the complete prime-plus-terminal field before taking its
norm. Every cross term is retained. This permits exact finite-codimension source
corrections without assuming continuity of the unbounded Gamma form energy.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology
noncomputable section
namespace RHTower

def ccmCoherentGammaPhysicalBound (T : ℝ) (N : ℕ) : ℝ :=
  ∫ r : ℝ, 2 * (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
    ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2) *
      ccmGammaHigherBinetDualDensity |r|

private theorem bound_integrable (T : ℝ) (N : ℕ) :
    Integrable (fun r : ℝ => 2 * (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
      ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2) *
        ccmGammaHigherBinetDualDensity |r|) := by
  have h := ((integrable_ccmOutgoingQuantileGammaChiSquareDensity N).add
    (integrable_ccmActualHeadQuantileTerminalDensity_sq_mul_dual T N)).const_mul 2
  convert h using 1
  funext r
  simp only [Pi.add_apply]
  ring

theorem ccmCoherentGammaPhysicalBound_nonneg (T : ℝ) (N : ℕ) :
    0 ≤ ccmCoherentGammaPhysicalBound T N := by
  apply integral_nonneg
  intro r
  exact mul_nonneg (mul_nonneg (by positivity) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r))

theorem ccmActualHeadQuantileCompletedCoherentField_sub
    (T : ℝ) (N : ℕ) (f g : SoninL2) (r : ℝ) :
    ccmActualHeadQuantileCompletedCoherentField T N (f-g) r =
      ccmActualHeadQuantileCompletedCoherentField T N f r -
        ccmActualHeadQuantileCompletedCoherentField T N g r := by
  simp only [ccmActualHeadQuantileCompletedCoherentField,
    ccmActualHeadQuantileBulkCoherentField, ccmActualHeadQuantileCellCoherentField,
    ccmActualHeadQuantileTerminalCoherentField, map_sub, smul_sub, Finset.sum_sub_distrib]
  abel

private theorem field_norm_le (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ≤
      (ccmOutgoingQuantileDisplacementDensity N r +
        |ccmActualHeadQuantileTerminalDisplacementDensity T N r|) * ‖f‖ := by
  calc
    _ ≤ ‖ccmActualHeadQuantileBulkCoherentField N f r‖ +
        ‖ccmActualHeadQuantileTerminalCoherentField T N f r‖ := norm_add_le _ _
    _ ≤ ccmOutgoingQuantileDisplacementDensity N r * ‖f‖ +
        |ccmActualHeadQuantileTerminalDisplacementDensity T N r| * ‖f‖ :=
      add_le_add (norm_ccmActualHeadQuantileBulkCoherentField_le N f r)
        (norm_ccmActualHeadQuantileTerminalCoherentField_le T N f r)
    _ = _ := by ring

private theorem density_sub_bound (T : ℝ) (N : ℕ) (f g : SoninL2) (r : ℝ)
    (P : SoninL2 →L[ℂ] SoninL2) (hP : ∀ v, ‖P v‖ ≤ ‖v‖) :
    |‖P (ccmActualHeadQuantileCompletedCoherentField T N f r)‖ ^ 2 *
        ccmGammaHigherBinetDualDensity |r| -
      ‖P (ccmActualHeadQuantileCompletedCoherentField T N g r)‖ ^ 2 *
        (ccmGammaHigherBinetDualDensity |r|)| ≤
      (2 * (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
        ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2) *
          ccmGammaHigherBinetDualDensity |r|) * ‖f-g‖ * (‖f‖+‖g‖) := by
  let V := fun f r => P (ccmActualHeadQuantileCompletedCoherentField T N f r)
  let b := ccmOutgoingQuantileDisplacementDensity N r +
    |ccmActualHeadQuantileTerminalDisplacementDensity T N r|
  have hb : 0 ≤ b := add_nonneg (ccmOutgoingQuantileDisplacementDensity_nonneg N r)
    (abs_nonneg _)
  have hd : 0 ≤ ccmGammaHigherBinetDualDensity |r| :=
    ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
  have hn : |‖V f r‖-‖V g r‖| ≤ b * ‖f-g‖ := by
    have h := abs_norm_sub_norm_le (V f r) (V g r)
    have hsub : V f r - V g r = V (f-g) r := by
      dsimp only [V]
      rw [← map_sub, ← ccmActualHeadQuantileCompletedCoherentField_sub]
    rw [hsub] at h
    exact h.trans ((hP _).trans (field_norm_le T N (f-g) r))
  have hs : ‖V f r‖+‖V g r‖ ≤ b * (‖f‖+‖g‖) := by
    have hf := (hP _).trans (field_norm_le T N f r)
    have hg := (hP _).trans (field_norm_le T N g r)
    change ‖V f r‖ ≤ b*‖f‖ at hf
    change ‖V g r‖ ≤ b*‖g‖ at hg
    nlinarith
  have hp := mul_le_mul hn hs (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg hb (norm_nonneg _))
  have hb2 : b ^ 2 ≤ 2 * (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
      ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2) := by
    dsimp [b]
    nlinarith [sq_nonneg (ccmOutgoingQuantileDisplacementDensity N r -
      |ccmActualHeadQuantileTerminalDisplacementDensity T N r|),
      sq_abs (ccmActualHeadQuantileTerminalDisplacementDensity T N r)]
  have hp' : |‖V f r‖ ^ 2-‖V g r‖ ^ 2| ≤
      b ^ 2 * ‖f-g‖ * (‖f‖+‖g‖) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    rw [mul_comm (‖V f r‖+‖V g r‖)]
    calc
      _ ≤ (b * ‖f-g‖) * (b * (‖f‖+‖g‖)) := hp
      _ = _ := by ring
  have hfinal := (mul_le_mul_of_nonneg_right hp' hd).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hb2 (norm_nonneg (f-g)))
        (add_nonneg (norm_nonneg f) (norm_nonneg g))) hd)
  rw [← sub_mul, abs_mul, abs_of_nonneg hd]
  calc
    _ ≤ (2 * (ccmOutgoingQuantileDisplacementDensity N r ^ 2 +
        ccmActualHeadQuantileTerminalDisplacementDensity T N r ^ 2) *
          ‖f-g‖ * (‖f‖+‖g‖)) * ccmGammaHigherBinetDualDensity |r| := hfinal
    _ = _ := by ring

/-- A coefficient-uniform bound for perturbing the complete coherent cost.
The constant depends only on the literal finite packet and its terminal cell. -/
theorem abs_ccmActualHeadCoherentGammaCost_sub_le
    (T : ℝ) (N : ℕ) (f g : SoninL2) :
    |ccmActualHeadCoherentQuantileGammaChiSquare T N f -
      ccmActualHeadCoherentQuantileGammaChiSquare T N g| ≤
      ccmCoherentGammaPhysicalBound T N * ‖f-g‖ * (‖f‖+‖g‖) := by
  have hf := integrable_ccmActualHeadCoherentQuantileGammaChiSquareDensity T N f
  have hg := integrable_ccmActualHeadCoherentQuantileGammaChiSquareDensity T N g
  have hB := ((bound_integrable T N).mul_const ‖f-g‖).mul_const (‖f‖+‖g‖)
  unfold ccmActualHeadCoherentQuantileGammaChiSquare
  rw [← integral_sub hf hg]
  apply (abs_integral_le_integral_abs).trans
  have h := integral_mono (hf.sub hg).abs hB
    (fun r => density_sub_bound T N f g r (ContinuousLinearMap.id ℂ SoninL2) (fun _ => le_rfl))
  simp only [Pi.sub_apply] at h
  rw [integral_mul_const, integral_mul_const] at h
  exact h

theorem norm_ccmIncrementSupportProjection_le (a : SuzukiPositiveAperture)
    (r : ℝ) (f : SoninL2) : ‖ccmIncrementSupportProjection a r f‖ ≤ ‖f‖ := by
  have h := norm_sq_ccmIncrementSupportProjection a r f
  nlinarith [sq_nonneg ‖f-ccmIncrementSupportProjection a r f‖,
    norm_nonneg f, norm_nonneg (ccmIncrementSupportProjection a r f)]

/-- The same bound applies after the actual increment-support projection,
including every cross term in the surviving field. -/
theorem abs_ccmActualHeadSupportedCoherentGammaCost_sub_le
    (a : SuzukiPositiveAperture) (N : ℕ) (f g : SoninL2) :
    |ccmActualHeadSupportedCoherentGammaCost a N f -
      ccmActualHeadSupportedCoherentGammaCost a N g| ≤
      ccmCoherentGammaPhysicalBound (2*a.1) N * ‖f-g‖ * (‖f‖+‖g‖) := by
  have hf := integrable_ccmActualHeadSupportedCoherentGammaDensity a N f
  have hg := integrable_ccmActualHeadSupportedCoherentGammaDensity a N g
  have hB := ((bound_integrable (2*a.1) N).mul_const ‖f-g‖).mul_const (‖f‖+‖g‖)
  unfold ccmActualHeadSupportedCoherentGammaCost
  rw [← integral_sub hf hg]
  apply (abs_integral_le_integral_abs).trans
  have h := integral_mono (hf.sub hg).abs hB (fun r =>
    density_sub_bound (2*a.1) N f g r (ccmIncrementSupportProjection a r)
      (norm_ccmIncrementSupportProjection_le a r))
  simp only [Pi.sub_apply] at h
  rw [integral_mul_const, integral_mul_const] at h
  exact h

end RHTower
