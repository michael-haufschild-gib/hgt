import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBalancedMean
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanLeadingMinorDescent

/-!
# Balanced logarithmic prefix comparison over number fields

The global selected-minor descent compares every weighted logarithmic leading product in both
directions for two simultaneous Siegel forms in one integral orbit.  A finite maximum over prefix
lengths makes the comparison uniform.  Determinant balancing can then turn these global prefix
bounds into placewise diagonal bounds without a false lower bound at any single embedding.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n k : ℕ}

omit [NumberField K] in
/-- The simultaneous leading Jacobi product is the product of the corresponding arbitrary-place
weights. -/
theorem numberFieldArchimedeanLeadingJacobiProduct_eq_prod_weight
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (hk : k ≤ n)
    (w : InfinitePlace K) :
    numberFieldArchimedeanLeadingJacobiProduct J hk w =
      ∏ i : Fin k, numberFieldArchimedeanJacobiWeight J (Fin.castLE hk i) w := by
  rw [numberFieldArchimedeanLeadingJacobiProduct]
  split_ifs with hw
  · simp only [numberFieldArchimedeanJacobiWeight, dif_pos hw]
  · simp only [numberFieldArchimedeanJacobiWeight, dif_neg hw]

omit [NumberField K] in
/-- A leading determinant computed from simultaneous Jacobi data is its leading Jacobi product. -/
theorem numberFieldArchimedeanLeadingDet_eq_leadingJacobiProduct
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (hk : k ≤ n)
    (w : InfinitePlace K) :
    numberFieldArchimedeanLeadingDet A hk w =
      numberFieldArchimedeanLeadingJacobiProduct J hk w := by
  rw [numberFieldArchimedeanLeadingDet,
    numberFieldArchimedeanLeadingJacobiProduct]
  split_ifs with hw
  · rw [← J.realJacobiData_form ⟨w, hw⟩,
      det_leadingBlock_form hk (J.realJacobiData ⟨w, hw⟩)]
    rfl
  · let wc : {w : InfinitePlace K // w.IsComplex} :=
      ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
    have hdet := complexDetLeadingBlock_form hk (J.complexJacobiData wc)
    rw [J.complexJacobiData_form wc] at hdet
    calc
      (complexLeadingBlock hk
          (A.1.2 wc : Matrix (Fin n) (Fin n) ℂ)).det.re =
          (((∏ i : Fin k, (J.complexJacobiData wc).d (Fin.castLE hk i) : ℝ) : ℂ)).re :=
        congrArg Complex.re hdet
      _ = ∏ i : Fin k, (J.complexD wc (Fin.castLE hk i)).re := by
        rw [Complex.ofReal_re]
        rfl

/-- Weighted logarithmic mean of the first `k` Jacobi weights. -/
def numberFieldArchimedeanLogPrefixMean
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (hk : k ≤ n) : ℝ :=
  ∑ i : Fin k, numberFieldWeightedPlaceMean
    (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J (Fin.castLE hk i) w))

omit [NumberField K] in
/-- The logarithm of a positive leading Jacobi product is the sum of logarithmic weights. -/
theorem log_numberFieldArchimedeanLeadingJacobiProduct
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (hk : k ≤ n)
    (w : InfinitePlace K) :
    Real.log (numberFieldArchimedeanLeadingJacobiProduct J hk w) =
      ∑ i : Fin k,
        Real.log (numberFieldArchimedeanJacobiWeight J (Fin.castLE hk i) w) := by
  rw [numberFieldArchimedeanLeadingJacobiProduct_eq_prod_weight]
  exact Real.log_prod fun i _ ↦
    (numberFieldArchimedeanJacobiWeight_pos J (Fin.castLE hk i) w).ne'

/-- Prefix means are the weighted mean of the logarithmic leading Jacobi product. -/
theorem numberFieldArchimedeanLogPrefixMean_eq
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (hk : k ≤ n) :
    numberFieldArchimedeanLogPrefixMean J hk =
      numberFieldWeightedPlaceMean
        (fun w ↦ Real.log (numberFieldArchimedeanLeadingJacobiProduct J hk w)) := by
  rw [numberFieldArchimedeanLogPrefixMean, sum_numberFieldWeightedPlaceMean]
  congr 1
  funext w
  exact (log_numberFieldArchimedeanLeadingJacobiProduct J hk w).symm

/-- Unnormalized form of the prefix-mean identity. -/
theorem numberFieldInfinitePlaceWeight_mul_logPrefixMean
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (hk : k ≤ n) :
    numberFieldInfinitePlaceWeight (K := K) *
        numberFieldArchimedeanLogPrefixMean J hk =
      ∑ w : InfinitePlace K, (mult w : ℝ) *
        Real.log (numberFieldArchimedeanLeadingJacobiProduct J hk w) := by
  rw [numberFieldArchimedeanLogPrefixMean_eq, numberFieldWeightedPlaceMean]
  field_simp [ne_of_gt (numberFieldInfinitePlaceWeight_pos (K := K))]

/-- Consecutive logarithmic prefix means differ by the corresponding coordinate mean. -/
theorem numberFieldArchimedeanLogPrefixMean_succ_sub
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (i : Fin n) :
    numberFieldArchimedeanLogPrefixMean J i.isLt -
        numberFieldArchimedeanLogPrefixMean J (Nat.le_of_succ_le i.isLt) =
      numberFieldWeightedPlaceMean
        (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J i w)) := by
  let f : Fin n → ℝ := fun j ↦ numberFieldWeightedPlaceMean
    (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J j w))
  change (∑ j : Fin (i.1 + 1), f (Fin.castLE i.isLt j)) -
      (∑ j : Fin i.1, f (Fin.castLE (Nat.le_of_succ_le i.isLt) j)) = f i
  rw [Fin.sum_univ_castSucc]
  have hhead : (∑ j : Fin i.1,
      f (Fin.castLE i.isLt j.castSucc)) =
      ∑ j : Fin i.1, f (Fin.castLE (Nat.le_of_succ_le i.isLt) j) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
  rw [hhead]
  have hlast : Fin.castLE i.isLt (Fin.last i.1) = i := Fin.ext rfl
  rw [hlast]
  ring

/-- **Uniform global prefix comparison.**  Two simultaneous Siegel decompositions in one
`SL_n(𝒦_K)` orbit have uniformly comparable weighted logarithmic prefix products. -/
theorem exists_numberFieldArchimedean_logPrefixComparisonBound
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀
      (A : numberFieldArchimedeanPositiveForms K n)
      (J : NumberFieldArchimedeanJacobiData A)
      (g : Matrix.SpecialLinearGroup (Fin n) (RingOfIntegers K))
      (J' : NumberFieldArchimedeanJacobiData (g • A)),
      J.IsSiegel t u → J'.IsSiegel t u →
      ∀ (k : ℕ) (hk : k ≤ n),
        |numberFieldArchimedeanLogPrefixMean J hk -
          numberFieldArchimedeanLogPrefixMean J' hk| ≤ B := by
  obtain ⟨c, hc, hdesc⟩ :=
    exists_numberFieldArchimedean_globalLeadingMinor_descent
      (K := K) n t u ht
  let E : Fin (n + 1) → ℝ := fun k ↦
    Real.log ((Nat.factorial k.1 : ℝ) * (t ^ n) ^ k.1) - Real.log (c ^ k.1)
  let B : ℝ := ∑ k : Fin (n + 1), |E k|
  have hB : 0 ≤ B := Finset.sum_nonneg fun k _ ↦ abs_nonneg (E k)
  refine ⟨B, hB, ?_⟩
  intro A J g J' hJ hJ' k hk
  let k' : Fin (n + 1) := ⟨k, Nat.lt_succ_iff.mpr hk⟩
  have hEk : E k' ≤ B := by
    exact le_trans (le_abs_self (E k'))
      (Finset.single_le_sum (fun i _ ↦ abs_nonneg (E i)) (Finset.mem_univ k'))
  have hfwd := (hdesc A J hJ g k hk).choose_spec.2
  have hrevRaw :=
    (hdesc (g • A) J' hJ' g⁻¹ k hk).choose_spec.2
  have hrev :
      (∑ w : InfinitePlace K, (mult w : ℝ) *
          Real.log (numberFieldArchimedeanLeadingJacobiProduct J' hk w)) ≤
        numberFieldInfinitePlaceWeight (K := K) * E k' +
          ∑ w : InfinitePlace K, (mult w : ℝ) *
            Real.log (numberFieldArchimedeanLeadingJacobiProduct J hk w) := by
    simpa [E, k', numberFieldInfinitePlaceWeight,
      numberFieldArchimedeanLeadingDet_eq_leadingJacobiProduct J hk] using hrevRaw
  have hfwd' :
      (∑ w : InfinitePlace K, (mult w : ℝ) *
          Real.log (numberFieldArchimedeanLeadingJacobiProduct J hk w)) ≤
        numberFieldInfinitePlaceWeight (K := K) * E k' +
          ∑ w : InfinitePlace K, (mult w : ℝ) *
            Real.log (numberFieldArchimedeanLeadingJacobiProduct J' hk w) := by
    simpa [E, k', numberFieldInfinitePlaceWeight,
      numberFieldArchimedeanLeadingDet_eq_leadingJacobiProduct J' hk] using hfwd
  have hW : 0 < numberFieldInfinitePlaceWeight (K := K) :=
    numberFieldInfinitePlaceWeight_pos (K := K)
  rw [← numberFieldInfinitePlaceWeight_mul_logPrefixMean J hk,
    ← numberFieldInfinitePlaceWeight_mul_logPrefixMean J' hk] at hfwd' hrev
  rw [abs_le]
  constructor
  · have :
        -E k' ≤ numberFieldArchimedeanLogPrefixMean J hk -
          numberFieldArchimedeanLogPrefixMean J' hk := by
      nlinarith
    linarith
  · have :
        numberFieldArchimedeanLogPrefixMean J hk -
          numberFieldArchimedeanLogPrefixMean J' hk ≤ E k' := by
      nlinarith
    linarith

/-- **Placewise diagonal comparison from global prefixes.**  Determinant-balanced simultaneous
Siegel decompositions in one integral orbit have uniformly comparable Jacobi weights at every
infinite place.  The comparison is obtained only after the global product-formula summation. -/
theorem exists_numberFieldArchimedean_detBalancedDiagonalComparison
    (K : Type*) [Field K] [NumberField K]
    (m : ℕ) (t u R : ℝ) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀
      (A : numberFieldArchimedeanPositiveForms K (m + 1))
      (J : NumberFieldArchimedeanJacobiData A)
      (g : Matrix.SpecialLinearGroup (Fin (m + 1)) (RingOfIntegers K))
      (J' : NumberFieldArchimedeanJacobiData (g • A)),
      J.IsSiegel t u → J'.IsSiegel t u →
      J.IsDetBalanced R → J'.IsDetBalanced R →
      ∀ (i : Fin (m + 1)) (w : InfinitePlace K),
        numberFieldArchimedeanJacobiWeight J i w ≤
            C * numberFieldArchimedeanJacobiWeight J' i w ∧
          numberFieldArchimedeanJacobiWeight J' i w ≤
            C * numberFieldArchimedeanJacobiWeight J i w := by
  obtain ⟨B, hB, hprefix⟩ :=
    exists_numberFieldArchimedean_logPrefixComparisonBound K (m + 1) t u ht
  let C := Real.exp (4 * R + 2 * B)
  refine ⟨C, Real.exp_pos _, ?_⟩
  intro A J g J' hJ hJ' hbal hbal' i w
  obtain ⟨a, ha⟩ := hbal
  obtain ⟨a', ha'⟩ := hbal'
  have hma := numberFieldArchimedeanDetBalanced_mean_sub_witness_le J R a ha i
  have hma' := numberFieldArchimedeanDetBalanced_mean_sub_witness_le J' R a' ha' i
  let p : InfinitePlace K → ℝ :=
    numberFieldCenteredPlaceProfileAverage
      (fun j v ↦ Real.log (numberFieldArchimedeanJacobiWeight J j v))
  have hp :
      numberFieldCenteredPlaceProfileAverage
          (fun j v ↦ Real.log (numberFieldArchimedeanJacobiWeight J' j v)) w = p w :=
    numberFieldCenteredJacobiProfile_smul J g J' w
  have hlocal := ha i w
  have hlocal' := ha' i w
  rw [hp] at hlocal'
  let M := numberFieldWeightedPlaceMean
    (fun v ↦ Real.log (numberFieldArchimedeanJacobiWeight J i v))
  let M' := numberFieldWeightedPlaceMean
    (fun v ↦ Real.log (numberFieldArchimedeanJacobiWeight J' i v))
  have hp1 := hprefix A J g J' hJ hJ' (i.1 + 1) i.isLt
  have hp0 := hprefix A J g J' hJ hJ' i.1 (Nat.le_of_succ_le i.isLt)
  have hmean : |M - M'| ≤ 2 * B := by
    change
      |numberFieldWeightedPlaceMean
            (fun v ↦ Real.log (numberFieldArchimedeanJacobiWeight J i v)) -
        numberFieldWeightedPlaceMean
            (fun v ↦ Real.log (numberFieldArchimedeanJacobiWeight J' i v))| ≤ 2 * B
    rw [← numberFieldArchimedeanLogPrefixMean_succ_sub J i,
      ← numberFieldArchimedeanLogPrefixMean_succ_sub J' i]
    have hp1' := abs_le.mp hp1
    have hp0' := abs_le.mp hp0
    rw [abs_le]
    constructor <;> linarith
  have hlog :
      |Real.log (numberFieldArchimedeanJacobiWeight J i w) -
          Real.log (numberFieldArchimedeanJacobiWeight J' i w)| ≤
        4 * R + 2 * B := by
    change |M - a i| ≤ R at hma
    change |M' - a' i| ≤ R at hma'
    change
      |Real.log (numberFieldArchimedeanJacobiWeight J i w) - (a i + p w)| ≤ R
        at hlocal
    change
      |Real.log (numberFieldArchimedeanJacobiWeight J' i w) - (a' i + p w)| ≤ R
        at hlocal'
    have hlocalB := abs_le.mp hlocal
    have hlocalB' := abs_le.mp hlocal'
    have hmaB := abs_le.mp hma
    have hmaB' := abs_le.mp hma'
    have hmeanB := abs_le.mp hmean
    rw [abs_le]
    constructor <;> linarith
  have hd : 0 < numberFieldArchimedeanJacobiWeight J i w :=
    numberFieldArchimedeanJacobiWeight_pos J i w
  have hd' : 0 < numberFieldArchimedeanJacobiWeight J' i w :=
    numberFieldArchimedeanJacobiWeight_pos J' i w
  have hlogB := abs_le.mp hlog
  constructor
  · have hexp := Real.exp_le_exp.mpr hlogB.2
    rw [Real.exp_sub, Real.exp_log hd, Real.exp_log hd'] at hexp
    exact (div_le_iff₀ hd').mp hexp
  · have hexp := Real.exp_le_exp.mpr (show
        Real.log (numberFieldArchimedeanJacobiWeight J' i w) -
            Real.log (numberFieldArchimedeanJacobiWeight J i w) ≤ 4 * R + 2 * B by
      linarith [hlogB.1])
    rw [Real.exp_sub, Real.exp_log hd', Real.exp_log hd] at hexp
    exact (div_le_iff₀ hd).mp hexp

end

end GaloisForLFunctions.HTGeometry
