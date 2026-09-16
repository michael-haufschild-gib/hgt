import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamFrequencyTensor

/-! The literal source-pole cochain exposed by the off-frequency Einstein defect. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet

namespace RHTower.D4BMModularCore

open D4BMHorizon D4BMVectorStream D4BMQuadraticMixedSource D4BMMetricReconstruction
open ComplexCoordinateMetricTwoJet

set_option autoImplicit false
noncomputable section

private def defectMatrix (T R : Fin 2 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, T 0, T 1;
    0, 0, R 0, R 1;
    T 0, R 0, 0, 0;
    T 1, R 1, 0, 0]

private def frequencyMetricJetCombination (c : ℂ)
    (K L : CoordinateMetricTwoJet 4 ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  ofSpace (toSpace K - c • toSpace L)

private theorem cosmological_frequencyMetricJetCombination
    (J K L : CoordinateMetricTwoJet 4 ℂ) (hJ : J.metric.det ≠ 0)
    (c Λ : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological J
      (frequencyMetricJetCombination c K L) Λ i j =
      CoordinateMetricTwoJet.Linearization.cosmological J K Λ i j -
        c * CoordinateMetricTwoJet.Linearization.cosmological J L Λ i j := by
  simp only [CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv _ _ hJ,
    frequencyMetricJetCombination, toSpace_ofSpace, map_sub, map_smul]
  change _ + Λ * (K.metric i j - c * L.metric i j) = _
  simp only [smul_eq_mul]
  ring

/-- The exact quotient of the off-frequency defect by its source-pole factor.
Its radial entries retain the original mixed source current. -/
def frequencyDefectCochain (q : XiZeroCopy) (branch : Bool) (w r B : ℂ)
    (z : Point) : Matrix (Fin 4) (Fin 4) ℂ :=
  let v := 2 * physicalRate q branch
  let f := r ^ 2 - 1
  let P := forcedStreamValue q branch r B
  let P1 := forcedStreamFirst q branch r B
  let C := fun k => current (physicalRate q branch) r B
    (fullSquareCovector q k z) (fullGradientCovector q branch k z)
  let T := fun k => f / (2 * r ^ 2) * (w + v) *
    (r ^ 2 / f * P1 k z - 2 * r / f ^ 2 * P k z)
  let R := fun k => -C k / (r ^ 2 * f) +
    w / (2 * r ^ 2 * f) * (w + v) * r ^ 2 / f * P k z
  defectMatrix T R

/-- The full mixed frozen metric pencil at fixed radial profile frequency. -/
def frozenMixedMetricJet (q : XiZeroCopy) (branch : Bool) (w r B : ℂ)
    (z : Point) : CoordinateMetricTwoJet 4 ℂ :=
  frequencyMetricJetCombination (physicalRate q branch * (physicalRate q branch - 1) / 4)
    (frozenStreamMetricJet w (2 * physicalRate q branch) r (B ^ 2) false
      (fullAngularCovector q branch) z)
    (frozenStreamMetricJet w (2 * physicalRate q branch) r (B ^ 2) true
      (fullSquareCovector q) z)

/-- Literal metric realization of the scaled source-pole defect: the difference
between the frequency-`w` frozen pencil and its physical-frequency value. -/
def frozenMixedDifferenceJet (q : XiZeroCopy) (branch : Bool) (w r B : ℂ)
    (z : Point) : CoordinateMetricTwoJet 4 ℂ :=
  frequencyMetricJetCombination 1 (frozenMixedMetricJet q branch w r B z)
    (frozenMixedMetricJet q branch (2 * physicalRate q branch) r B z)

private theorem time_factor (v w r P P1 : ℂ) :
    (r ^ 2 - 1) / (2 * r ^ 2) * (w ^ 2 - v ^ 2) *
        (r ^ 2 / (r ^ 2 - 1) * P1 - 2 * r / (r ^ 2 - 1) ^ 2 * P) =
      (w - v) * ((r ^ 2 - 1) / (2 * r ^ 2) * (w + v) *
        (r ^ 2 / (r ^ 2 - 1) * P1 - 2 * r / (r ^ 2 - 1) ^ 2 * P)) := by
  ring

private theorem radial_factor (v w r P C : ℂ) :
    -(w - v) / (r ^ 2 * (r ^ 2 - 1)) * C +
        w / (2 * r ^ 2 * (r ^ 2 - 1)) * (w ^ 2 - v ^ 2) * r ^ 2 /
          (r ^ 2 - 1) * P =
      (w - v) * (-C / (r ^ 2 * (r ^ 2 - 1)) +
        w / (2 * r ^ 2 * (r ^ 2 - 1)) * (w + v) * r ^ 2 /
          (r ^ 2 - 1) * P) := by
  ring

private theorem defectMatrix_factor (a : ℂ) (T R T' R' : Fin 2 → ℂ)
    (hT : ∀ k, T k = a * T' k) (hR : ∀ k, R k = a * R' k) :
    defectMatrix T R = a • defectMatrix T' R' := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals dsimp only [defectMatrix, Matrix.smul_apply, smul_eq_mul]
  all_goals first | exact hT 0 | exact hT 1 | exact hR 0 | exact hR 1 | norm_num

/-- The full off-frequency Einstein defect has precisely one source-pole factor. -/
theorem frequencyDefectTensor_factor (q : XiZeroCopy) (branch : Bool) (w r B : ℂ)
    (z : Point) :
    frequencyDefectTensor q branch w r B z =
      (w - 2 * physicalRate q branch) • frequencyDefectCochain q branch w r B z := by
  let v := 2 * physicalRate q branch
  let P := forcedStreamValue q branch r B
  let P1 := forcedStreamFirst q branch r B
  let C := fun k => current (physicalRate q branch) r B
    (fullSquareCovector q k z) (fullGradientCovector q branch k z)
  let T := fun k => (r ^ 2 - 1) / (2 * r ^ 2) * (w ^ 2 - v ^ 2) *
    (r ^ 2 / (r ^ 2 - 1) * P1 k z - 2 * r / (r ^ 2 - 1) ^ 2 * P k z)
  let R := fun k => -(w - v) / (r ^ 2 * (r ^ 2 - 1)) * C k +
    w / (2 * r ^ 2 * (r ^ 2 - 1)) * (w ^ 2 - v ^ 2) * r ^ 2 /
      (r ^ 2 - 1) * P k z
  let T' := fun k => (r ^ 2 - 1) / (2 * r ^ 2) * (w + v) *
    (r ^ 2 / (r ^ 2 - 1) * P1 k z - 2 * r / (r ^ 2 - 1) ^ 2 * P k z)
  let R' := fun k => -C k / (r ^ 2 * (r ^ 2 - 1)) +
    w / (2 * r ^ 2 * (r ^ 2 - 1)) * (w + v) * r ^ 2 /
      (r ^ 2 - 1) * P k z
  have htime (k : Fin 2) :
      T k = (w - v) * T' k := by
    exact time_factor v w r (P k z) (P1 k z)
  have hradius (k : Fin 2) :
      R k = (w - v) * R' k := by
    exact radial_factor v w r (P k z) (C k)
  change defectMatrix T R = (w - v) • defectMatrix T' R'
  exact defectMatrix_factor (w - v) T R T' R' htime hradius

/-- The literal frozen Einstein pencil plus complete mixed source equals the source-pole factor
times the residue cochain. -/
theorem frozen_stream_cosmological_source_factor (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (B w : ℂ) (i j : Fin 4) :
    let s := physicalRate q branch
    let r := (p.val 1 : ℂ)
    let z := angularPoint p.val
    let E := fun K => CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.jet r (p.val 3)) K (-3) i j
    E (frozenStreamMetricJet w (2 * s) r (B ^ 2) false (fullAngularCovector q branch) z) -
      (s * (s - 1) / 4) *
        E (frozenStreamMetricJet w (2 * s) r (B ^ 2) true (fullSquareCovector q) z) +
      literalMixedSource q branch r B z i j =
      (w - 2 * s) * frequencyDefectCochain q branch w r B z i j := by
  dsimp only
  rw [frozen_stream_cosmological_source]
  have h := congrFun (congrFun (frequencyDefectTensor_factor q branch w (p.val 1) B
    (angularPoint p.val)) i) j
  simpa only [Matrix.smul_apply, smul_eq_mul] using h

/-- The scaled defect cochain is the exact cosmological Einstein residual of a
literal difference of complete frozen metric two-jets. No causal inverse or
endpoint condition is used. -/
theorem frozenMixedDifferenceJet_cosmological (q : XiZeroCopy) (branch : Bool)
    (p : D4BMBackground.ExteriorPoint) (B w : ℂ) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological
      (D4BMBackground.jet (p.val 1) (p.val 3))
      (frozenMixedDifferenceJet q branch w (p.val 1) B (angularPoint p.val)) (-3) i j =
      (w - 2 * physicalRate q branch) *
        frequencyDefectCochain q branch w (p.val 1) B (angularPoint p.val) i j := by
  have hdet : (D4BMBackground.jet (p.val 1) (p.val 3)).metric.det ≠ 0 := by
    have hr : (p.val 1 : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
    have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
    have hf : (p.val 1 : ℂ) ^ 2 - 1 ≠ 0 := by
      exact_mod_cast (by nlinarith [p.property.1] : (p.val 1) ^ 2 - 1 ≠ 0)
    change (D4BMBackground.metric (p.val 1) (p.val 3)).det ≠ 0
    rw [D4BMBackground.metric_det _ _ hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ (inv_ne_zero hy)))
  have hw := frozen_stream_cosmological_source_factor q branch p B w i j
  have hv := frozen_stream_cosmological_source_factor q branch p B
    (2 * physicalRate q branch) i j
  dsimp only at hw hv
  unfold frozenMixedDifferenceJet
  rw [cosmological_frequencyMetricJetCombination _ _ _ hdet]
  unfold frozenMixedMetricJet
  rw [cosmological_frequencyMetricJetCombination _ _ _ hdet,
    cosmological_frequencyMetricJetCombination _ _ _ hdet]
  linear_combination hw - hv

end

end RHTower.D4BMModularCore
