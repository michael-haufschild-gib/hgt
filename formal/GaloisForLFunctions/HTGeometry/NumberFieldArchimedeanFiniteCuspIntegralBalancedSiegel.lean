import GaloisForLFunctions.HTGeometry.NumberFieldRankTwoCuspShearJacobiReduction

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Exact weight preservation transports multiplicative relative-balance bounds to additive
relative determinant-profile balance. -/
theorem NumberFieldArchimedeanJacobiData.isBalancedRelativeTo_of_weight_eq
    {A A₁ A₂ : numberFieldArchimedeanPositiveForms K 2}
    (J : NumberFieldArchimedeanJacobiData A)
    (J₁ : NumberFieldArchimedeanJacobiData A₁)
    (J₂ : NumberFieldArchimedeanJacobiData A₂) (R : ℝ)
    (hweight : ∀ i w,
      numberFieldArchimedeanJacobiWeight J₂ i w =
        numberFieldArchimedeanJacobiWeight J₁ i w)
    (hbounds : ∀ i w,
      Real.exp (-R) *
            (Real.exp (numberFieldWeightedPlaceMean
                (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))) *
              Real.exp (numberFieldCenteredPlaceProfileAverage
                (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)) ≤
          numberFieldArchimedeanJacobiWeight J₁ i w ∧
        numberFieldArchimedeanJacobiWeight J₁ i w ≤
          Real.exp R *
            (Real.exp (numberFieldWeightedPlaceMean
                (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))) *
              Real.exp (numberFieldCenteredPlaceProfileAverage
                (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w))) :
    J₂.IsBalancedRelativeTo J R := by
  intro i w
  rw [hweight i w]
  exact abs_log_sub_le_of_exp_mul_le
    (numberFieldArchimedeanJacobiWeight_pos J₁ i w)
    (s := numberFieldWeightedPlaceMean
        (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v)) +
      numberFieldCenteredPlaceProfileAverage
        (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)
    (C := R)
    (by simpa [Real.exp_add] using (hbounds i w).1)
    (by simpa [Real.exp_add] using (hbounds i w).2)

/-- Exact Jacobi-weight preservation implies exact centered determinant-profile preservation. -/
theorem numberFieldCenteredJacobiProfile_eq_of_weight_eq
    {A A' : numberFieldArchimedeanPositiveForms K 2}
    (J : NumberFieldArchimedeanJacobiData A)
    (J' : NumberFieldArchimedeanJacobiData A')
    (hweight : ∀ i w,
      numberFieldArchimedeanJacobiWeight J' i w =
        numberFieldArchimedeanJacobiWeight J i w)
    (w : InfinitePlace K) :
    numberFieldCenteredPlaceProfileAverage
        (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J' j v)) w =
      numberFieldCenteredPlaceProfileAverage
        (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w := by
  congr 1
  funext i v
  rw [hweight i v]

/-- Cusp-relative determinant-one unit balancing followed by an `I⁻²` upper shear is one literal
integral action before entering the cusp chart. -/
theorem numberFieldRankTwoCuspChart_shear_unitSpecialLinear_smul
    (c : numberFieldRankTwoCuspType K) (a : K)
    (ha : a ∈ numberFieldRankTwoCuspShearIdeal c)
    (u : Fin 2 → (𝓞 K)ˣ) (hu : ∏ i, u i = 1)
    (B : numberFieldArchimedeanPositiveForms K 2) :
    numberFieldRankTwoCuspChart
        (numberFieldRankTwoCuspRepresentative K c).1
        (numberFieldRankTwoCuspRepresentative K c).2
        ((transposeSpecialLinearOfDetOne
            (numberFieldRankTwoCuspShearIntegralMatrix c a ha)
            (numberFieldRankTwoCuspShearIntegralMatrix_det c a ha) *
          numberFieldRankTwoCuspUnitSpecialLinear c u hu) • B) =
      numberFieldRankTwoUpperShearTransposeSpecialLinear a •
        (numberFieldUnitSpecialLinear u hu •
          numberFieldRankTwoCuspChart
            (numberFieldRankTwoCuspRepresentative K c).1
            (numberFieldRankTwoCuspRepresentative K c).2 B) := by
  rw [mul_smul, numberFieldRankTwoCuspChart_shearSpecialLinear_smul,
    numberFieldRankTwoCuspChart_unitSpecialLinear_smul]

/-- In rank two, relative determinant-profile balance, one adjacent weighted-mean bound, and one
bounded strict-upper entry at every infinite place give a determinant-balanced Siegel point. -/
theorem numberFieldRankTwo_isDetBalancedSiegel_of_relative
    {A A' : numberFieldArchimedeanPositiveForms K 2}
    (J : NumberFieldArchimedeanJacobiData A)
    (J' : NumberFieldArchimedeanJacobiData A')
    (Cmean U R : ℝ)
    (hmean :
      numberFieldWeightedPlaceMean
          (fun w => Real.log (numberFieldArchimedeanJacobiWeight J 0 w)) -
        numberFieldWeightedPlaceMean
          (fun w => Real.log (numberFieldArchimedeanJacobiWeight J 1 w)) ≤ Cmean)
    (hrelative : J'.IsBalancedRelativeTo J R)
    (hcenter : ∀ w : InfinitePlace K,
      numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J' j v)) w =
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)
    (hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, |J'.realU w 0 1| ≤ U)
    (hcomplex : ∀ w : {w : InfinitePlace K // w.IsComplex},
      ‖J'.complexU w 0 1‖ ≤ U) :
    NumberFieldArchimedeanIsDetBalancedSiegel
      (Real.exp (max (Cmean + 2 * R) 0)) (max U 1) R A' := by
  refine ⟨J', ?_⟩
  have hu : 0 ≤ max U 1 := zero_le_one.trans (le_max_right _ _)
  have hdiag (w : InfinitePlace K) :
      numberFieldArchimedeanJacobiWeight J' (0 : Fin 2) w ≤
        Real.exp (max (Cmean + 2 * R) 0) *
          numberFieldArchimedeanJacobiWeight J' (1 : Fin 2) w := by
    have hratio := hrelative.log_ratio_sub_mean_le
      (0 : Fin 2) (1 : Fin 2) w
    have hupp :
        Real.log (numberFieldArchimedeanJacobiWeight J' (0 : Fin 2) w) -
            Real.log (numberFieldArchimedeanJacobiWeight J' (1 : Fin 2) w) ≤
          max (Cmean + 2 * R) 0 := by
      have habs := (abs_le.mp hratio).2
      have hsum :
          Real.log (numberFieldArchimedeanJacobiWeight J' (0 : Fin 2) w) -
              Real.log (numberFieldArchimedeanJacobiWeight J' (1 : Fin 2) w) ≤
            Cmean + 2 * R := by
        linarith [hmean]
      exact hsum.trans (le_max_left _ _)
    have hexp := Real.exp_le_exp.mpr hupp
    have hw0 := numberFieldArchimedeanJacobiWeight_pos J' (0 : Fin 2) w
    have hw1 := numberFieldArchimedeanJacobiWeight_pos J' (1 : Fin 2) w
    rw [Real.exp_sub, Real.exp_log hw0, Real.exp_log hw1] at hexp
    exact (div_le_iff₀ hw1).mp hexp
  have hrealAll : ∀ w (i j : Fin 2), |J'.realU w i j| ≤ max U 1 := by
    intro w i j
    by_cases hij : i < j
    · have hi : i = (0 : Fin 2) := Fin.ext (by omega)
      have hj : j = (1 : Fin 2) := Fin.ext (by omega)
      subst i
      subst j
      exact (hreal w).trans (le_max_left _ _)
    · by_cases hji : j < i
      · rw [J'.realUpper w i j hji, abs_zero]
        exact hu
      · have hijEq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
        subst j
        rw [J'.realUnit, abs_one]
        exact le_max_right _ _
  have hcomplexAll : ∀ w (i j : Fin 2), ‖J'.complexU w i j‖ ≤ max U 1 := by
    intro w i j
    by_cases hij : i < j
    · have hi : i = (0 : Fin 2) := Fin.ext (by omega)
      have hj : j = (1 : Fin 2) := Fin.ext (by omega)
      subst i
      subst j
      exact (hcomplex w).trans (le_max_left _ _)
    · by_cases hji : j < i
      · rw [J'.complexUpper w i j hji, norm_zero]
        exact hu
      · have hijEq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
        subst j
        rw [J'.complexUnit, norm_one]
        exact le_max_right _ _
  constructor
  · rw [J'.isSiegel_iff]
    constructor
    · constructor
      · intro w i j hij
        have hi : i = (0 : Fin 2) := Fin.ext (by omega)
        have hj : j = (1 : Fin 2) := Fin.ext (by omega)
        subst i
        subst j
        simpa [numberFieldArchimedeanJacobiWeight, w.2] using hdiag w.1
      · exact hrealAll
    · constructor
      · intro w i j hij
        have hi : i = (0 : Fin 2) := Fin.ext (by omega)
        have hj : j = (1 : Fin 2) := Fin.ext (by omega)
        subst i
        subst j
        have hnr : ¬w.1.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr w.2
        simpa [numberFieldArchimedeanJacobiWeight, hnr] using hdiag w.1
      · exact hcomplexAll
  · refine ⟨fun i => numberFieldWeightedPlaceMean
        (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v)), ?_⟩
    intro i w
    rw [hcenter w]
    exact hrelative i w

/-- Every rank-two positive archimedean form has one literal integral translate whose chart at a
member of the fixed finite cusp family is uniformly determinant-balanced Siegel. -/
theorem exists_uniform_numberFieldArchimedean_finiteCusp_integralBalancedSiegel
    (K : Type*) [Field K] [NumberField K] :
    ∃ t u R : ℝ, 1 ≤ t ∧ 0 ≤ u ∧ 0 ≤ R ∧
      ∀ A : numberFieldArchimedeanPositiveForms K 2,
        ∃ c : numberFieldRankTwoCuspType K,
          ∃ h : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K),
            NumberFieldArchimedeanIsDetBalancedSiegel t u R
              (numberFieldRankTwoCuspChart
                (numberFieldRankTwoCuspRepresentative K c).1
                (numberFieldRankTwoCuspRepresentative K c).2 (h • A)) := by
  obtain ⟨Cmean, hheight⟩ :=
    exists_uniform_numberFieldArchimedean_finiteCusp_headMeanRatio K
  obtain ⟨Rb, hRb, hbalance⟩ :=
    exists_numberFieldArchimedeanJacobiUnitConj_balancingRadius_of_data (K := K)
  obtain ⟨U, hU, hreduce⟩ :=
    exists_uniform_numberFieldRankTwoCuspJacobiUpperShearReduction K
  let R : ℝ := 2 * (1 + 1 : ℝ) * Rb
  let t : ℝ := Real.exp (max (Cmean + 2 * R) 0)
  let u : ℝ := max U 1
  have ht : 1 ≤ t := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_le_exp.mpr (le_max_right _ _)
  have hu : 0 ≤ u := hU.trans (le_max_left _ _)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  refine ⟨t, u, R, ht, hu, hR, ?_⟩
  intro A
  obtain ⟨c, h0, J, hmean⟩ := hheight A
  let A0 := numberFieldRankTwoCuspChart
    (numberFieldRankTwoCuspRepresentative K c).1
    (numberFieldRankTwoCuspRepresentative K c).2 (h0 • A)
  obtain ⟨units, hunits, J1, hbounds⟩ := hbalance 1 A0 J
  let A1 := (numberFieldUnitSpecialLinear units hunits) • A0
  obtain ⟨a, ha, hreal, hcomplex⟩ := hreduce c A1 J1
  let g2 : Matrix.SpecialLinearGroup (Fin 2) K :=
    numberFieldRankTwoUpperShearTransposeSpecialLinear a
  let J2 : NumberFieldArchimedeanJacobiData (g2 • A1) :=
    numberFieldRankTwoArchimedeanJacobiUpperShear A1 J1 a
  let hUnit : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) :=
    numberFieldRankTwoCuspUnitSpecialLinear c units hunits
  let hShear : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) :=
    transposeSpecialLinearOfDetOne
      (numberFieldRankTwoCuspShearIntegralMatrix c a ha)
      (numberFieldRankTwoCuspShearIntegralMatrix_det c a ha)
  let h : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) := hShear * hUnit * h0
  have hform :
      numberFieldRankTwoCuspChart
          (numberFieldRankTwoCuspRepresentative K c).1
          (numberFieldRankTwoCuspRepresentative K c).2 (h • A) =
        g2 • A1 := by
    rw [show h • A = (hShear * hUnit) • (h0 • A) by simp [h, mul_smul]]
    change numberFieldRankTwoCuspChart
        (numberFieldRankTwoCuspRepresentative K c).1
        (numberFieldRankTwoCuspRepresentative K c).2
        ((transposeSpecialLinearOfDetOne
            (numberFieldRankTwoCuspShearIntegralMatrix c a ha)
            (numberFieldRankTwoCuspShearIntegralMatrix_det c a ha) *
          numberFieldRankTwoCuspUnitSpecialLinear c units hunits) • (h0 • A)) =
      numberFieldRankTwoUpperShearTransposeSpecialLinear a •
        (numberFieldUnitSpecialLinear units hunits • A0)
    exact numberFieldRankTwoCuspChart_shear_unitSpecialLinear_smul
      c a ha units hunits (h0 • A)
  refine ⟨c, h, ?_⟩
  rw [hform]
  have hweight (i : Fin 2) (w : InfinitePlace K) :
      numberFieldArchimedeanJacobiWeight J2 i w =
        numberFieldArchimedeanJacobiWeight J1 i w := by
    exact numberFieldRankTwoArchimedeanJacobiUpperShear_weight A1 J1 a i w
  have hcenter (w : InfinitePlace K) :
      numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J2 j v)) w =
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w := by
    calc
      _ = numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J1 j v)) w :=
        numberFieldCenteredJacobiProfile_eq_of_weight_eq J1 J2 hweight w
      _ = _ := numberFieldCenteredJacobiProfile_smul J
        (numberFieldUnitSpecialLinear units hunits) J1 w
  have hrelative : J2.IsBalancedRelativeTo J R := by
    apply J.isBalancedRelativeTo_of_weight_eq J1 J2 R hweight
    intro i w
    simpa [R] using hbounds i w
  change NumberFieldArchimedeanIsDetBalancedSiegel
    (Real.exp (max (Cmean + 2 * R) 0)) (max U 1) R (g2 • A1)
  exact numberFieldRankTwo_isDetBalancedSiegel_of_relative
    J J2 Cmean U R hmean hrelative hcenter hreal hcomplex

end

end GaloisForLFunctions.HTGeometry
