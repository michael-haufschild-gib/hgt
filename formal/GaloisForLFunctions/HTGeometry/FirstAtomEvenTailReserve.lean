import GaloisForLFunctions.HTGeometry.FirstAtomOddScaleSevenBounds
import GaloisForLFunctions.HTGeometry.HankelFourDeterminant

/-! # Exact first-atom even rank-four reserve on physical scale thirty -/
namespace HTGeometry
noncomputable section
open GaloisForLFunctions.HTGeometry
set_option maxHeartbeats 3000000

/-- The seventh signed moment retains the full twelfth-derivative numerator. -/
def firstAtomEvenTailNumerator6 (u : ℝ) : ℝ :=
  (43599790080 : ℝ)*(u)^0 +
    (-239798845440 : ℝ)*(u)^1 +
    (886529064960 : ℝ)*(u)^2 +
    (-1280916848640 : ℝ)*(u)^3 +
    (603009318912 : ℝ)*(u)^4 +
    (-75547148288 : ℝ)*(u)^5 +
    (1408303104 : ℝ)*(u)^6 +
    (-491520 : ℝ)*(u)^7

/-- All seven even moments, with the exact common denominator. -/
def firstAtomEvenTailProfile (k : Fin 7) (u : ℝ) : ℝ :=
  match k.val with
  | 0 => 1
  | 1 => firstAtomOddTailProfile1 u
  | 2 => firstAtomOddTailProfile2 u
  | 3 => firstAtomOddTailProfile3 u
  | 4 => firstAtomOddTailProfile4 u
  | 5 => firstAtomOddTailProfile5 u
  | _ => firstAtomEvenTailNumerator6 u / firstAtomOddTailDenominator u

/-- Balanced entries reserve one hundred million in the original last normalized coordinate. -/
def firstAtomEvenTailBalanced (k : Fin 7) (u : ℝ) : ℝ :=
  firstAtomEvenTailProfile k u / (32 : ℝ)^k.val -
    if k.val = 6 then 100000000/(32 : ℝ)^6 else 0

/-- The determinant of the balanced first-atom reserve matrix. -/
def firstAtomEvenTailBalancedDet (u : ℝ) : ℝ :=
  hankelFourDet (firstAtomEvenTailBalanced 0 u) (firstAtomEvenTailBalanced 1 u)
    (firstAtomEvenTailBalanced 2 u) (firstAtomEvenTailBalanced 3 u)
    (firstAtomEvenTailBalanced 4 u) (firstAtomEvenTailBalanced 5 u) (firstAtomEvenTailBalanced 6 u)

/-- Exact common-denominator numerator, including the last-coordinate reserve. -/
def firstAtomEvenTailReserveNumerator (u : ℝ) : ℝ :=
  (73181031038724341760 : ℝ)*(u)^0 +
    (-1589905688489675980800 : ℝ)*(u)^1 +
    (16710964264412601384960 : ℝ)*(u)^2 +
    (-109498791137393655152640 : ℝ)*(u)^3 +
    (490916038663711940935680 : ℝ)*(u)^4 +
    (-1574108555788415800442880 : ℝ)*(u)^5 +
    (3669211928323772047687680 : ℝ)*(u)^6 +
    (-6214959571530568213463040 : ℝ)*(u)^7 +
    (7554530181257636924620800 : ℝ)*(u)^8 +
    (-6420844592432812759449600 : ℝ)*(u)^9 +
    (3660583483455636190003200 : ℝ)*(u)^10 +
    (-1319845633904996882841600 : ℝ)*(u)^11 +
    (293937397852752838656000 : ℝ)*(u)^12 +
    (-47265445215020777472000 : ℝ)*(u)^13 +
    (4090278912838336512000 : ℝ)*(u)^14

/-- All scale factors and the reserved last coordinate remain in the exact determinant. -/
theorem firstAtomEvenTailBalancedDet_eq_ratio (u : ℝ) (hD : firstAtomOddTailDenominator u ≠ 0) :
    firstAtomEvenTailBalancedDet u =
      firstAtomEvenTailReserveNumerator u / ((32 : ℝ)^12*firstAtomOddTailDenominator u^4) := by
  unfold firstAtomEvenTailBalancedDet
  norm_num [firstAtomEvenTailBalanced, firstAtomEvenTailProfile]
  unfold firstAtomOddTailProfile1 firstAtomOddTailProfile2 firstAtomOddTailProfile3
    firstAtomOddTailProfile4 firstAtomOddTailProfile5 firstAtomOddTailNumerator1
    firstAtomOddTailNumerator2 firstAtomOddTailNumerator3 firstAtomOddTailNumerator4
    firstAtomOddTailNumerator5 firstAtomEvenTailNumerator6 firstAtomEvenTailReserveNumerator
    hankelFourDet
  field_simp [hD]
  unfold firstAtomOddTailDenominator
  ring

/-- The full four-dimensional first-atom determinant has a fixed rational reserve. -/
theorem firstAtomEvenTailBalancedDet_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/30) :
    (1/10000 : ℝ) ≤ firstAtomEvenTailBalancedDet u := by
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddTailDenominator_lower hu0 hu1
    linarith
  have hz : 0 ≤ 1-30*u := by linarith
  have hid : 10000*firstAtomEvenTailReserveNumerator u-
      (32 : ℝ)^12*firstAtomOddTailDenominator u^4 =
    (354255354766547092947695828992/1171875 : ℝ)*(1-30*u)^0 +
    (2508957298178177584104143323136/10546875 : ℝ)*(1-30*u)^1 +
    (956695124815744944344110465024/10546875 : ℝ)*(1-30*u)^2 +
    (226415409359974459457060995072/10546875 : ℝ)*(1-30*u)^3 +
    (7294307573291460416864518144/2109375 : ℝ)*(1-30*u)^4 +
    (4200607945192158422915612672/10546875 : ℝ)*(1-30*u)^5 +
    (117325328497964755491749888/3515625 : ℝ)*(1-30*u)^6 +
    (21414592093379284147634176/10546875 : ℝ)*(1-30*u)^7 +
    (932874188172374759702528/10546875 : ℝ)*(1-30*u)^8 +
    (628590543391900565504/234375 : ℝ)*(1-30*u)^9 +
    (114229676951335862272/2109375 : ℝ)*(1-30*u)^10 +
    (1436413883089682432/2109375 : ℝ)*(1-30*u)^11 +
    (10870313118072832/2109375 : ℝ)*(1-30*u)^12 +
    (60009283059712/2109375 : ℝ)*(1-30*u)^13 +
    (60129542144/703125 : ℝ)*(1-30*u)^14 := by
    unfold firstAtomEvenTailReserveNumerator firstAtomOddTailDenominator
    ring
  have hr : 0 ≤ 10000*firstAtomEvenTailReserveNumerator u-
      (32 : ℝ)^12*firstAtomOddTailDenominator u^4 := by
    rw [hid]
    positivity
  rw [firstAtomEvenTailBalancedDet_eq_ratio u hD.ne']
  apply (le_div_iff₀ (by positivity : 0 < (32 : ℝ)^12*firstAtomOddTailDenominator u^4)).mpr
  nlinarith only [hr]

/-- A fixed denominator margin keeps the new twelfth entry bounded. -/
theorem firstAtomEvenTailProfile_six_abs_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/30) :
    |firstAtomEvenTailProfile 6 u| ≤ 4000000000 := by
  have hd : 19/5 ≤ 4-6*u := by linarith
  have hD : 14 ≤ firstAtomOddTailDenominator u := by
    unfold firstAtomOddTailDenominator
    nlinarith [sq_nonneg (4-6*u-19/5)]
  have hp (n : ℕ) : 0 ≤ u^n ∧ u^n ≤ (1/30 : ℝ)^n :=
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
theorem firstAtomEvenTailBalanced_abs_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/30) (k : Fin 7) :
    |firstAtomEvenTailBalanced k u| ≤ 4 := by
  have hu7 : u ≤ 1/7 := by linarith
  have h1 := firstAtomOddScaleSeven_profile1_bounds hu0 hu7
  have h2 := firstAtomOddScaleSeven_profile2_bounds hu0 hu7
  have h3 := firstAtomOddScaleSeven_profile3_bounds hu0 hu7
  have h4 := firstAtomOddScaleSeven_profile4_bounds hu0 hu7
  have h5 := firstAtomOddScaleSeven_profile5_bounds hu0 hu7
  have h6 := firstAtomEvenTailProfile_six_abs_le hu0 hu1
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
