import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEffectiveTailScale
import GaloisForLFunctions.HTGeometry.FirstAtomOddScaleSevenBounds

/-! # Pointwise first-atom Gaussian profiles on the explicit tail -/
namespace RHTower
noncomputable section

/-- The physical tail lies in the inverse-scale interval of the polynomial reserve. -/
theorem inverseScale_bounds_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ∧
      (thetaCuspSingleAtomReflectionScale 1 x)⁻¹ ≤ 1/7 := by
  have hp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  constructor
  · positivity
  · apply (inv_le_iff_one_le_mul₀ hp).mpr
    linarith

/-- Exact first-atom normalized moment 1 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_1_eq_profile_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 1 x =
      HTGeometry.firstAtomOddTailProfile1 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by nlinarith
  have hu := inverseScale_bounds_of_seven_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/7 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_2, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile1, HTGeometry.firstAtomOddTailNumerator1,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring

/-- Exact first-atom normalized moment 2 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_2_eq_profile_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 2 x =
      HTGeometry.firstAtomOddTailProfile2 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by nlinarith
  have hu := inverseScale_bounds_of_seven_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/7 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_4, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile2, HTGeometry.firstAtomOddTailNumerator2,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring

/-- Exact first-atom normalized moment 3 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_3_eq_profile_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 3 x =
      HTGeometry.firstAtomOddTailProfile3 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by nlinarith
  have hu := inverseScale_bounds_of_seven_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/7 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_6, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile3, HTGeometry.firstAtomOddTailNumerator3,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring

/-- Exact first-atom normalized moment 4 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_4_eq_profile_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 4 x =
      HTGeometry.firstAtomOddTailProfile4 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by nlinarith
  have hu := inverseScale_bounds_of_seven_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/7 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_8, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile4, HTGeometry.firstAtomOddTailNumerator4,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring

/-- Exact first-atom normalized moment 5 in inverse physical scale. -/
theorem thetaCuspFirstAtomScaledEvenJet_5_eq_profile_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspFirstAtomScaledEvenJet 5 x =
      HTGeometry.firstAtomOddTailProfile5 ((thetaCuspSingleAtomReflectionScale 1 x)⁻¹) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hp : 0 < q := by dsimp [q]; linarith
  have hs : 0 < 4*q^(2 : ℕ)-6*q := by nlinarith
  have hu := inverseScale_bounds_of_seven_le hq
  have hd : 0 < 4-6*q⁻¹ := by change 0 ≤ q⁻¹ ∧ q⁻¹ ≤ 1/7 at hu; linarith [hu.2]
  unfold thetaCuspFirstAtomScaledEvenJet
  norm_num only [Nat.reduceMul]
  rw [thetaCuspFirstAtomReflectionJet_10, thetaCuspSourceTerm_one_eq_scale_profile]
  dsimp [HTGeometry.firstAtomOddTailProfile5, HTGeometry.firstAtomOddTailNumerator5,
    HTGeometry.firstAtomOddTailDenominator]
  change _ = _
  field_simp [Real.exp_ne_zero, hp.ne', hs.ne', hd.ne', q]
  <;> ring


/-- Odd first-atom reflection jets vanish exactly, at every order and every center. -/
theorem thetaCuspFirstAtomReflectionJet_odd_zero {n : ℕ} (hn : Odd n) (x : ℝ) :
    thetaCuspFirstAtomReflectionJet n x = 0 := by
  apply iteratedDeriv_zero_of_even_real_of_odd _ hn
  intro t
  simp only [sub_eq_add_neg, neg_neg]
  exact mul_comm _ _

/-- The zeroth first-atom reflection jet is exactly its mass squared. -/
theorem thetaCuspFirstAtomReflectionJet_zero (x : ℝ) :
    thetaCuspFirstAtomReflectionJet 0 x = thetaCuspSourceTerm x 1^(2 : ℕ) := by
  simp only [thetaCuspFirstAtomReflectionJet, iteratedDeriv_zero, add_zero, sub_zero, pow_two]

/-- Uniform entrywise first-atom bounds at physical scale at least seven. -/
theorem thetaCuspFirstAtomScaledEvenJet_bounds_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspFirstAtomScaledEvenJet 1 x| ≤ 9 ∧
    |thetaCuspFirstAtomScaledEvenJet 2 x| ≤ 210 ∧
    |thetaCuspFirstAtomScaledEvenJet 3 x| ≤ 8500 ∧
    |thetaCuspFirstAtomScaledEvenJet 4 x| ≤ 500000 ∧
    |thetaCuspFirstAtomScaledEvenJet 5 x| ≤ 40000000 := by
  have hu := inverseScale_bounds_of_seven_le hq
  have h1 := HTGeometry.firstAtomOddScaleSeven_profile1_bounds hu.1 hu.2
  have h2 := HTGeometry.firstAtomOddScaleSeven_profile2_bounds hu.1 hu.2
  have h3 := HTGeometry.firstAtomOddScaleSeven_profile3_bounds hu.1 hu.2
  have h4 := HTGeometry.firstAtomOddScaleSeven_profile4_bounds hu.1 hu.2
  have h5 := HTGeometry.firstAtomOddScaleSeven_profile5_bounds hu.1 hu.2
  rw [thetaCuspFirstAtomScaledEvenJet_1_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_2_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_3_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_4_eq_profile_of_seven_le hq,
    thetaCuspFirstAtomScaledEvenJet_5_eq_profile_of_seven_le hq]
  exact ⟨by simpa only [abs_of_nonneg h1.1] using h1.2, by simpa only [abs_of_nonneg h2.1] using h2.2, by simpa only [abs_of_nonneg h3.1] using h3.2, by simpa only [abs_of_nonneg h4.1] using h4.2, by simpa only [abs_of_nonneg h5.1] using h5.2⟩

end
end RHTower
