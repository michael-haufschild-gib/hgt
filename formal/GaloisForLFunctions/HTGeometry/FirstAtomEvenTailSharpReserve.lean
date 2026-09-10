import GaloisForLFunctions.HTGeometry.FirstAtomEvenTailExtendedReserve
/-!
# A stronger reserved determinant floor at scale eighteen

The exact existing certificate in `z = 1 - 30*u` retains each odd-power
lower bound when `u ≤ 1/18`. Together with the denominator ceiling this
gives a floor of `1/4000`, large enough to absorb the complete reflected
linear and quadratic likelihood errors at scale eighteen.
-/
namespace HTGeometry
noncomputable section
/-- The exact certificate retains a stronger reserve on the scale-eighteen ray. -/
theorem firstAtomEvenTailBalancedDet_lower_of_eighteen {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/18) :
    (1/4000 : ℝ) ≤ firstAtomEvenTailBalancedDet u := by
  have hD : 0 < firstAtomOddTailDenominator u := by
    unfold firstAtomOddTailDenominator
    exact sq_pos_of_pos (by linarith)
  let z := 1-30*u
  have hz : -(2/3 : ℝ) ≤ z := by dsimp only [z]; linarith
  have hp (n : ℕ) : -(2/3 : ℝ)^n ≤ z^n := by
    by_cases hz0 : 0 ≤ z
    · exact (neg_nonpos.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2/3) n)).trans (pow_nonneg hz0 n)
    · have hza : |z| ≤ (2/3 : ℝ) := by rw [abs_of_neg (lt_of_not_ge hz0)]; linarith
      have h : |z^n| ≤ (2/3 : ℝ)^n := by
        simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg z) hza n
      exact (abs_le.mp h).1
  have hDu : firstAtomOddTailDenominator u ≤ 16 := by
    unfold firstAtomOddTailDenominator
    nlinarith [sq_nonneg u]
  have hD4 : firstAtomOddTailDenominator u^4 ≤ (16 : ℝ)^4 :=
    pow_le_pow_left₀ hD.le hDu 4
  have hid : 10000*firstAtomEvenTailReserveNumerator u-
      (32 : ℝ)^12*firstAtomOddTailDenominator u^4 =
    (354255354766547092947695828992/1171875 : ℝ)*z^0 +
    (2508957298178177584104143323136/10546875 : ℝ)*z^1 +
    (956695124815744944344110465024/10546875 : ℝ)*z^2 +
    (226415409359974459457060995072/10546875 : ℝ)*z^3 +
    (7294307573291460416864518144/2109375 : ℝ)*z^4 +
    (4200607945192158422915612672/10546875 : ℝ)*z^5 +
    (117325328497964755491749888/3515625 : ℝ)*z^6 +
    (21414592093379284147634176/10546875 : ℝ)*z^7 +
    (932874188172374759702528/10546875 : ℝ)*z^8 +
    (628590543391900565504/234375 : ℝ)*z^9 +
    (114229676951335862272/2109375 : ℝ)*z^10 +
    (1436413883089682432/2109375 : ℝ)*z^11 +
    (10870313118072832/2109375 : ℝ)*z^12 +
    (60009283059712/2109375 : ℝ)*z^13 +
    (60129542144/703125 : ℝ)*z^14 := by
    dsimp only [z]
    unfold firstAtomEvenTailReserveNumerator firstAtomOddTailDenominator
    ring
  have hr : 0 ≤ 10000*firstAtomEvenTailReserveNumerator u-
      (5/2)*(32 : ℝ)^12*firstAtomOddTailDenominator u^4 := by
    rw [show 10000*firstAtomEvenTailReserveNumerator u-
        (5/2)*(32 : ℝ)^12*firstAtomOddTailDenominator u^4 =
        (10000*firstAtomEvenTailReserveNumerator u-(32 : ℝ)^12*firstAtomOddTailDenominator u^4)-
          (3/2)*(32 : ℝ)^12*firstAtomOddTailDenominator u^4 by ring, hid]
    nlinarith only [hD4, hp 1,hp 3,hp 5,hp 7,hp 9,hp 11,hp 13,
      sq_nonneg z,sq_nonneg (z^2),sq_nonneg (z^3),sq_nonneg (z^4),
      sq_nonneg (z^5),sq_nonneg (z^6),sq_nonneg (z^7)]
  rw [firstAtomEvenTailBalancedDet_eq_ratio u hD.ne']
  apply (le_div_iff₀ (by positivity : 0 < (32 : ℝ)^12*firstAtomOddTailDenominator u^4)).mpr
  nlinarith only [hr]

/-- The sixth profile remains bounded on the extended scale-twenty-one ray. -/
theorem firstAtomEvenTailProfile_six_abs_le_of_eighteen {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/18) :
    |firstAtomEvenTailProfile 6 u| ≤ 4000000000 := by
  have hd : 11/3 ≤ 4-6*u := by linarith
  have hD : 67/5 ≤ firstAtomOddTailDenominator u := by
    unfold firstAtomOddTailDenominator
    nlinarith [sq_nonneg (4-6*u-11/3)]
  have hp (n : ℕ) : 0 ≤ u^n ∧ u^n ≤ (1/18 : ℝ)^n :=
    ⟨pow_nonneg hu0 n, pow_le_pow_left₀ hu0 hu1 n⟩
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have h6 := hp 6
  have h7 := hp 7
  norm_num at h1 h2 h3 h4 h5 h6 h7
  have hN : |firstAtomEvenTailNumerator6 u| ≤ 53000000000 := by
    unfold firstAtomEvenTailNumerator6
    apply abs_le.mpr
    constructor <;> nlinarith only [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2]
  norm_num [firstAtomEvenTailProfile]
  rw [abs_div, abs_of_pos (by linarith : 0 < firstAtomOddTailDenominator u)]
  apply (div_le_iff₀ (by linarith : 0 < firstAtomOddTailDenominator u)).mpr
  nlinarith only [hD, hN]

/-- Balancing makes every reserved entry small enough for a uniform perturbation estimate. -/
theorem firstAtomEvenTailBalanced_abs_le_of_eighteen {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/18) (k : Fin 7) :
    |firstAtomEvenTailBalanced k u| ≤ 4 := by
  have hu7 : u ≤ 1/7 := by linarith
  have h1 := firstAtomOddScaleSeven_profile1_bounds hu0 hu7
  have h2 := firstAtomOddScaleSeven_profile2_bounds hu0 hu7
  have h3 := firstAtomOddScaleSeven_profile3_bounds hu0 hu7
  have h4 := firstAtomOddScaleSeven_profile4_bounds hu0 hu7
  have h5 := firstAtomOddScaleSeven_profile5_bounds hu0 hu7
  have h6 := firstAtomEvenTailProfile_six_abs_le_of_eighteen hu0 hu1
  have h6' : |firstAtomEvenTailProfile 6 u / (32 : ℝ)^6-100000000/(32 : ℝ)^6| ≤ 4 := by
    have ht := abs_sub (firstAtomEvenTailProfile 6 u / (32 : ℝ)^6) (100000000/(32 : ℝ)^6)
    norm_num [abs_div] at ht
    linarith
  fin_cases k
  · norm_num [firstAtomEvenTailBalanced, firstAtomEvenTailProfile]
  · norm_num [firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h1.1]
    linarith [h1.2]
  · norm_num [firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h2.1]
    linarith [h2.2]
  · norm_num [firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h3.1]
    linarith [h3.2]
  · norm_num [firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h4.1]
    linarith [h4.2]
  · norm_num [firstAtomEvenTailBalanced, firstAtomEvenTailProfile, abs_div, abs_of_nonneg h5.1]
    linarith [h5.2]
  · simpa [firstAtomEvenTailBalanced] using h6'

end
end HTGeometry
