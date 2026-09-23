import GaloisForLFunctions.HTGeometry.FirstAtomEvenTailReserve
/-!
# Extended first-atom even reserve

The existing exact determinant identity retains its positive reserve on
`0 ≤ u ≤ 1/15`: its constant term dominates the sum of its odd coefficients,
while even powers remain nonnegative. Entry bounds on `u ≤ 1/21` support
complete-source perturbation without discarding the balancing factors.
-/

namespace HTGeometry
noncomputable section

/-- The exact reserved determinant stays above the same floor through scale fifteen. -/
theorem firstAtomEvenTailBalancedDet_lower_of_fifteen {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/15) :
    (1/10000 : ℝ) ≤ firstAtomEvenTailBalancedDet u := by
  have hD : 0 < firstAtomOddTailDenominator u := by
    unfold firstAtomOddTailDenominator
    exact sq_pos_of_pos (by linarith)
  let z := 1-30*u
  have hz : |z| ≤ 1 := by
    apply abs_le.mpr
    dsimp only [z]
    constructor <;> linarith
  have hp (n : ℕ) : -1 ≤ z^n := by
    have h : |z^n| ≤ 1 := by
      simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg z) hz n
    exact (abs_le.mp h).1
  have hid : 10000*firstAtomEvenTailReserveNumerator u-
      (32 : ℝ)^(12 : ℕ)*firstAtomOddTailDenominator u^(4 : ℕ) =
    (354255354766547092947695828992/1171875 : ℝ)*z^(0 : ℕ) +
    (2508957298178177584104143323136/10546875 : ℝ)*z^(1 : ℕ) +
    (956695124815744944344110465024/10546875 : ℝ)*z^(2 : ℕ) +
    (226415409359974459457060995072/10546875 : ℝ)*z^(3 : ℕ) +
    (7294307573291460416864518144/2109375 : ℝ)*z^(4 : ℕ) +
    (4200607945192158422915612672/10546875 : ℝ)*z^(5 : ℕ) +
    (117325328497964755491749888/3515625 : ℝ)*z^(6 : ℕ) +
    (21414592093379284147634176/10546875 : ℝ)*z^(7 : ℕ) +
    (932874188172374759702528/10546875 : ℝ)*z^(8 : ℕ) +
    (628590543391900565504/234375 : ℝ)*z^(9 : ℕ) +
    (114229676951335862272/2109375 : ℝ)*z^(10 : ℕ) +
    (1436413883089682432/2109375 : ℝ)*z^(11 : ℕ) +
    (10870313118072832/2109375 : ℝ)*z^(12 : ℕ) +
    (60009283059712/2109375 : ℝ)*z^(13 : ℕ) +
    (60129542144/703125 : ℝ)*z^(14 : ℕ) := by
    dsimp only [z]
    unfold firstAtomEvenTailReserveNumerator firstAtomOddTailDenominator
    ring
  have hr : 0 ≤ 10000*firstAtomEvenTailReserveNumerator u-
      (32 : ℝ)^(12 : ℕ)*firstAtomOddTailDenominator u^(4 : ℕ) := by
    rw [hid]
    nlinarith only [hp 1,hp 3,hp 5,hp 7,hp 9,hp 11,hp 13,
      sq_nonneg z,sq_nonneg (z^(2 : ℕ)),sq_nonneg (z^(3 : ℕ)),sq_nonneg (z^(4 : ℕ)),
      sq_nonneg (z^(5 : ℕ)),sq_nonneg (z^(6 : ℕ)),sq_nonneg (z^(7 : ℕ))]
  rw [firstAtomEvenTailBalancedDet_eq_ratio u hD.ne']
  apply (le_div_iff₀ (by positivity : 0 < (32 : ℝ)^(12 : ℕ)*firstAtomOddTailDenominator u^(4 : ℕ))).mpr
  nlinarith only [hr]

/-- The sixth profile remains bounded on the extended scale-twenty-one ray. -/
theorem firstAtomEvenTailProfile_six_abs_le_of_twentyOne {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/21) :
    |firstAtomEvenTailProfile 6 u| ≤ 4000000000 := by
  have hd : 26/7 ≤ 4-6*u := by linarith
  have hD : 27/2 ≤ firstAtomOddTailDenominator u := by
    unfold firstAtomOddTailDenominator
    nlinarith [sq_nonneg (4-6*u-26/7)]
  have hp (n : ℕ) : 0 ≤ u^n ∧ u^n ≤ (1/21 : ℝ)^n :=
    ⟨pow_nonneg hu0 n, pow_le_pow_left₀ hu0 hu1 n⟩
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have h6 := hp 6
  have h7 := hp 7
  norm_num at h1 h2 h3 h4 h5 h6 h7
  have hN : |firstAtomEvenTailNumerator6 u| ≤ 54000000000 := by
    unfold firstAtomEvenTailNumerator6
    apply abs_le.mpr
    constructor <;> nlinarith only [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2]
  norm_num [firstAtomEvenTailProfile]
  rw [abs_div, abs_of_pos (by linarith : 0 < firstAtomOddTailDenominator u)]
  apply (div_le_iff₀ (by linarith : 0 < firstAtomOddTailDenominator u)).mpr
  nlinarith only [hD, hN]

/-- Balancing makes every reserved entry small enough for a uniform perturbation estimate. -/
theorem firstAtomEvenTailBalanced_abs_le_of_twentyOne {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/21) (k : Fin 7) :
    |firstAtomEvenTailBalanced k u| ≤ 4 := by
  have hu7 : u ≤ 1/7 := by linarith
  have h1 := firstAtomOddScaleSeven_profile1_bounds hu0 hu7
  have h2 := firstAtomOddScaleSeven_profile2_bounds hu0 hu7
  have h3 := firstAtomOddScaleSeven_profile3_bounds hu0 hu7
  have h4 := firstAtomOddScaleSeven_profile4_bounds hu0 hu7
  have h5 := firstAtomOddScaleSeven_profile5_bounds hu0 hu7
  have h6 := firstAtomEvenTailProfile_six_abs_le_of_twentyOne hu0 hu1
  have h6' : |firstAtomEvenTailProfile 6 u / (32 : ℝ)^(6 : ℕ)-100000000/(32 : ℝ)^(6 : ℕ)| ≤ 4 := by
    have ht := abs_sub (firstAtomEvenTailProfile 6 u / (32 : ℝ)^(6 : ℕ)) (100000000/(32 : ℝ)^(6 : ℕ))
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
