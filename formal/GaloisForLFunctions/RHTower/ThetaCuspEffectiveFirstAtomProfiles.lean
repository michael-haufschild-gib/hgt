import GaloisForLFunctions.RHTower.ThetaCuspEffectiveTailScale
import GaloisForLFunctions.HTGeometry.FirstAtomOddTailAlgebra

/-! # Pointwise first-atom Gaussian profiles on the explicit tail -/
namespace RHTower
noncomputable section

/-- The physical tail lies in the inverse-scale interval of the polynomial reserve. -/
theorem inverseScale_bounds_of_thirty_le {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ∧
      (thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≤ 1/30 := by
  have hp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  constructor
  · positivity
  · apply (inv_le_iff_one_le_mul₀ hp).mpr
    linarith

/-- Exact first-atom normalized moment 1 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_1_eq_profile {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 1 x =
      HTGeometry.firstAtomOddTailProfile1 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^2-6*q := by nlinarith
  have hu := inverseScale_bounds_of_thirty_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/30 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_2, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile1, HTGeometry.firstAtomOddTailNumerator1,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring

/-- Exact first-atom normalized moment 2 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_2_eq_profile {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 2 x =
      HTGeometry.firstAtomOddTailProfile2 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^2-6*q := by nlinarith
  have hu := inverseScale_bounds_of_thirty_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/30 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_4, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile2, HTGeometry.firstAtomOddTailNumerator2,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring

/-- Exact first-atom normalized moment 3 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_3_eq_profile {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 3 x =
      HTGeometry.firstAtomOddTailProfile3 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^2-6*q := by nlinarith
  have hu := inverseScale_bounds_of_thirty_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/30 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_6, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile3, HTGeometry.firstAtomOddTailNumerator3,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring

/-- Exact first-atom normalized moment 4 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_4_eq_profile {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 4 x =
      HTGeometry.firstAtomOddTailProfile4 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^2-6*q := by nlinarith
  have hu := inverseScale_bounds_of_thirty_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/30 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_8, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile4, HTGeometry.firstAtomOddTailNumerator4,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring

/-- Exact first-atom normalized moment 5 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_5_eq_profile {x : ℝ}
    (hq : 30 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 5 x =
      HTGeometry.firstAtomOddTailProfile5 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^2-6*q := by nlinarith
  have hu := inverseScale_bounds_of_thirty_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/30 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_10, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile5, HTGeometry.firstAtomOddTailNumerator5,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring

end
end RHTower
