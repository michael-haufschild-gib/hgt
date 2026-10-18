import GaloisForLFunctions.BiScaleUncertainty.PositiveDiagonalCovariance
import GaloisForLFunctions.RHTower.BurnolBaseFirstJetAdmission
import GaloisForLFunctions.RHTower.EulerFisherPoincareBoundary

/-!
# Exact full-source trace of a Burnol first-jet damping shell

The shell between native times `t` and `ct` is the difference of two complete
covariances. Every prime depth is retained. Its trace is exactly one quarter of
the difference of the two real Euler logarithms, with no Xi-divisor premise.
-/

open Filter Topology ContinuousLinearMap
open scoped NNReal InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.HTGeometry
noncomputable section

def burnolFirstJetDampingWeight (t : ℝ) (pe : RoutePPrimitiveIndex) : ℝ :=
  Real.exp (-2 * max t 0 * xiGammaEulerPrimitiveLogFrequency pe)

theorem burnolFirstJetDampingWeight_mem_unitInterval (t : ℝ) (pe : RoutePPrimitiveIndex) :
    0 ≤ burnolFirstJetDampingWeight t pe ∧ burnolFirstJetDampingWeight t pe ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
  have hm := le_max_right t 0
  have hl := (xiGammaEulerPrimitiveLogFrequency_pos pe).le
  nlinarith [mul_nonneg hm hl]

def burnolFirstJetShellWeight (c t : ℝ) (pe : RoutePPrimitiveIndex) : ℝ :=
  burnolFirstJetDampingWeight t pe - burnolFirstJetDampingWeight (c * max t 0) pe

theorem burnolFirstJetShellWeight_mem_unitInterval {c : ℝ} (hc : 1 ≤ c)
    (t : ℝ) (pe : RoutePPrimitiveIndex) :
    0 ≤ burnolFirstJetShellWeight c t pe ∧ burnolFirstJetShellWeight c t pe ≤ 1 := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hm : 0 ≤ max t 0 := le_max_right _ _
  have hcm : 0 ≤ c * max t 0 := mul_nonneg hc0 hm
  have htime : max t 0 ≤ c * max t 0 := by nlinarith
  have hmono : burnolFirstJetDampingWeight (c * max t 0) pe ≤
      burnolFirstJetDampingWeight t pe := by
    unfold burnolFirstJetDampingWeight
    rw [max_eq_left hcm]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right htime
      (xiGammaEulerPrimitiveLogFrequency_pos pe).le]
  have h1 := burnolFirstJetDampingWeight_mem_unitInterval t pe
  have h2 := burnolFirstJetDampingWeight_mem_unitInterval (c * max t 0) pe
  unfold burnolFirstJetShellWeight
  exact ⟨sub_nonneg.mpr hmono, by linarith⟩

/-- Native first-jet covariance after positive damping. -/
def burnolFirstJetDampedCovariance (t : ℝ) : routePBurnolHalfLineL2 →L[ℂ] routePBurnolHalfLineL2 :=
  weightedSourceCovariance burnolBaseFirstJetSynthesis (burnolFirstJetDampingWeight t)
    (burnolFirstJetDampingWeight_mem_unitInterval t)

/-- Positive full covariance associated with two damping scales. -/
def burnolFirstJetDampingShell (c : ℝ) (hc : 1 ≤ c) (t : ℝ) :
    routePBurnolHalfLineL2 →L[ℂ] routePBurnolHalfLineL2 :=
  weightedSourceCovariance burnolBaseFirstJetSynthesis (burnolFirstJetShellWeight c t)
    (burnolFirstJetShellWeight_mem_unitInterval hc t)

theorem burnolFirstJetDampingShell_isPositive {c : ℝ} (hc : 1 ≤ c) (t : ℝ) :
    (burnolFirstJetDampingShell c hc t).IsPositive := weightedSourceCovariance_isPositive _ _ _

/-- The two complete covariances are subtracted before taking any trace. -/
theorem burnolFirstJetDampingShell_eq_sub {c : ℝ} (hc : 1 ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    burnolFirstJetDampingShell c hc t =
      burnolFirstJetDampedCovariance t - burnolFirstJetDampedCovariance (c * t) := by
  have h := weightedSourceCovariance_sub burnolBaseFirstJetSynthesis
    (burnolFirstJetDampingWeight t) (burnolFirstJetDampingWeight (c * max t 0))
    (burnolFirstJetDampingWeight_mem_unitInterval t)
    (burnolFirstJetDampingWeight_mem_unitInterval (c * max t 0))
    (burnolFirstJetShellWeight_mem_unitInterval hc t)
  unfold burnolFirstJetDampingShell burnolFirstJetDampedCovariance burnolFirstJetShellWeight
  simpa only [max_eq_left ht] using h

theorem norm_sq_burnolBaseFirstJetField_eq_eulerWeight (pe : RoutePPrimitiveIndex) :
    ‖burnolBaseFirstJetField pe‖ ^ 2 = eulerPrimePowerWeight 1 pe / 4 := by
  rw [norm_sq_burnolBaseFirstJetField, eulerPrimePowerWeight, eulerPrimePowerNat]
  simp only [Real.rpow_neg_one, Nat.cast_pow, Nat.cast_mul, mul_inv_rev, inv_pow,
    pow_succ, one_div]
  ring

theorem burnolFirstJetDamped_column_energy {t : ℝ} (ht : 0 < t) (pe : RoutePPrimitiveIndex) :
    burnolFirstJetDampingWeight t pe * ‖burnolBaseFirstJetField pe‖ ^ 2 =
      eulerPrimePowerWeight (1 + 2 * t) pe / 4 := by
  have hn : (0 : ℝ) < (eulerPrimePowerNat pe : ℝ) := by
    exact_mod_cast pow_pos pe.1.property.pos (pe.2 + 1)
  have hl : xiGammaEulerPrimitiveLogFrequency pe = Real.log (eulerPrimePowerNat pe) := rfl
  rw [norm_sq_burnolBaseFirstJetField_eq_eulerWeight, burnolFirstJetDampingWeight,
    max_eq_left ht.le, hl]
  unfold eulerPrimePowerWeight
  rw [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hn]
  rw [show Real.log (eulerPrimePowerNat pe : ℝ) * (-(1 + 2 * t)) =
      -2 * t * Real.log (eulerPrimePowerNat pe : ℝ) +
        Real.log (eulerPrimePowerNat pe : ℝ) * (-1) by ring, Real.exp_add]
  ring

private theorem summable_eulerWeight {b : ℝ} (hb : 1 < b) :
    Summable (eulerPrimePowerWeight b) := by
  have h := summable_abs_eulerPrimePower_moment 0 b hb
  apply h.congr
  intro pe
  rw [pow_zero, mul_one, abs_of_nonneg]
  unfold eulerPrimePowerWeight
  positivity

theorem summable_burnolFirstJetDamped_column_energy {t : ℝ} (ht : 0 < t) :
    Summable (fun pe => burnolFirstJetDampingWeight t pe * ‖burnolBaseFirstJetField pe‖ ^ 2) :=
  ((summable_eulerWeight (by linarith : 1 < 1 + 2 * t)).div_const 4).congr
    fun pe => (burnolFirstJetDamped_column_energy ht pe).symm

theorem burnolFirstJetShell_column_energy {c : ℝ} (hc : 1 ≤ c) {t : ℝ} (ht : 0 < t)
    (pe : RoutePPrimitiveIndex) :
    burnolFirstJetShellWeight c t pe * ‖burnolBaseFirstJetField pe‖ ^ 2 =
      (eulerPrimePowerWeight (1 + 2 * t) pe - eulerPrimePowerWeight (1 + 2 * (c * t)) pe) / 4 := by
  have hct : 0 < c * t := mul_pos (lt_of_lt_of_le zero_lt_one hc) ht
  rw [burnolFirstJetShellWeight, max_eq_left ht.le, sub_mul,
    burnolFirstJetDamped_column_energy ht, burnolFirstJetDamped_column_energy hct]
  ring

theorem summable_burnolFirstJetShell_column_energy {c : ℝ} (hc : 1 ≤ c) {t : ℝ} (ht : 0 < t) :
    Summable (fun pe => burnolFirstJetShellWeight c t pe * ‖burnolBaseFirstJetField pe‖ ^ 2) := by
  have hct : 0 < c * t := mul_pos (lt_of_lt_of_le zero_lt_one hc) ht
  have h := (summable_burnolFirstJetDamped_column_energy ht).sub
    (summable_burnolFirstJetDamped_column_energy hct)
  simpa only [burnolFirstJetShellWeight, max_eq_left ht.le, sub_mul] using h

private theorem burnolFirstJet_basis (pe : RoutePPrimitiveIndex) :
    burnolBaseFirstJetSynthesis (HilbertSchmidt.lpBasis RoutePPrimitiveIndex pe) =
      burnolBaseFirstJetField pe := by
  classical
  rw [HilbertSchmidt.lpBasis_apply, burnolBaseFirstJetSynthesis_single, one_smul]

/-- The first jet follows the original physical weighted-translation semigroup. -/
theorem burnolWeightedShift_firstJetField (t : ℝ≥0) (pe : RoutePPrimitiveIndex) :
    burnolWeightedShift t (burnolBaseFirstJetField pe) =
      (Real.exp (-(t : ℝ) * xiGammaEulerPrimitiveLogFrequency pe) : ℂ) •
        burnolBaseFirstJetField pe := by
  simp only [burnolBaseFirstJetField, map_smul, burnolWeightedShift_baseField, neg_mul]
  module

theorem weightedFirstJetSynthesis_eq_native (t : ℝ≥0) :
    weightedSourceSynthesis burnolBaseFirstJetSynthesis (burnolFirstJetDampingWeight t)
      (burnolFirstJetDampingWeight_mem_unitInterval t) =
        burnolWeightedShift t ∘L burnolBaseFirstJetSynthesis := by
  classical
  let A := weightedSourceSynthesis burnolBaseFirstJetSynthesis (burnolFirstJetDampingWeight t)
    (burnolFirstJetDampingWeight_mem_unitInterval t)
  let B := burnolWeightedShift t ∘L burnolBaseFirstJetSynthesis
  have hb (pe : RoutePPrimitiveIndex) :
      A (HilbertSchmidt.lpBasis RoutePPrimitiveIndex pe) =
        B (HilbertSchmidt.lpBasis RoutePPrimitiveIndex pe) := by
    dsimp only [A, B]
    rw [weightedSourceSynthesis_basis, comp_apply, burnolFirstJet_basis,
      burnolWeightedShift_firstJetField]
    have he : Real.exp (-2 * (t : ℝ) * xiGammaEulerPrimitiveLogFrequency pe) =
        Real.exp (-(t : ℝ) * xiGammaEulerPrimitiveLogFrequency pe) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [burnolFirstJetDampingWeight, max_eq_left t.coe_nonneg, he,
      Real.sqrt_sq (Real.exp_nonneg _)]
  have hsingle (pe : RoutePPrimitiveIndex) (z : ℂ) :
      A (lp.single 2 pe z) = B (lp.single 2 pe z) := by
    have h1 := hb pe
    rw [HilbertSchmidt.lpBasis_apply] at h1
    have he : (lp.single 2 pe z : CoefficientSpace RoutePPrimitiveIndex) =
        z • lp.single 2 pe (1 : ℂ) := by simp [← lp.single_smul]
    rw [he, map_smul, map_smul, h1]
  apply ContinuousLinearMap.ext
  intro x
  have hA := (lp.hasSum_single (by norm_num) x).mapL A
  have hB := (lp.hasSum_single (by norm_num) x).mapL B
  simp only [hsingle] at hA
  exact hA.unique hB

/-- Identification with the native physical covariance, before taking a diagonal or trace. -/
theorem burnolFirstJetDampedCovariance_eq_native (t : ℝ≥0) :
    burnolFirstJetDampedCovariance t =
      rangeCovariance (burnolWeightedShift t ∘L burnolBaseFirstJetSynthesis) := by
  rw [burnolFirstJetDampedCovariance, weightedSourceCovariance, weightedFirstJetSynthesis_eq_native]

theorem burnolFirstJetDampingShell_memSchattenClass_one {c : ℝ} (hc : 1 ≤ c)
    {t : ℝ} (ht : 0 < t) : MemSchattenClass 1 (burnolFirstJetDampingShell c hc t) := by
  apply weightedSourceCovariance_memSchattenClass_one
  simpa only [burnolFirstJet_basis] using summable_burnolFirstJetShell_column_energy hc ht

/-- Exact trace of the full shell, including every prime-power depth. -/
theorem re_opTrace_burnolFirstJetDampingShell {c : ℝ} (hc : 1 ≤ c) {t : ℝ} (ht : 0 < t) :
    (opTrace (burnolFirstJetDampingShell c hc t)).re =
      (eulerLogMoment (1 + 2 * t) - eulerLogMoment (1 + 2 * (c * t))) / 4 := by
  have hct : 0 < c * t := mul_pos (lt_of_lt_of_le zero_lt_one hc) ht
  have henergy : Summable (fun pe => burnolFirstJetShellWeight c t pe *
      ‖burnolBaseFirstJetSynthesis (HilbertSchmidt.lpBasis RoutePPrimitiveIndex pe)‖ ^ 2) := by
    simpa only [burnolFirstJet_basis] using summable_burnolFirstJetShell_column_energy hc ht
  rw [burnolFirstJetDampingShell, re_opTrace_weightedSourceCovariance _ _ _ henergy]
  simp only [burnolFirstJet_basis, burnolFirstJetShell_column_energy hc ht]
  rw [tsum_div_const, Summable.tsum_sub (summable_eulerWeight (by linarith))
    (summable_eulerWeight (by linarith)), ← eulerLogMoment_eq_tsum, ← eulerLogMoment_eq_tsum]

/-- The finite-shell covariance tends strongly to zero on every physical vector. -/
theorem tendsto_burnolFirstJetDampingShell_apply_zero {c : ℝ} (hc : 1 ≤ c)
    (x : routePBurnolHalfLineL2) :
    Tendsto (fun t => burnolFirstJetDampingShell c hc t x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_weightedSourceCovariance_zero
  intro pe
  have hcont : ContinuousAt (fun t => burnolFirstJetShellWeight c t pe) 0 := by
    unfold burnolFirstJetShellWeight burnolFirstJetDampingWeight
    fun_prop
  simpa only [burnolFirstJetShellWeight, burnolFirstJetDampingWeight, max_self, mul_zero,
    zero_mul, Real.exp_zero, sub_self] using hcont.tendsto.mono_left nhdsWithin_le_nhds

end
end RHTower
