import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanFiniteCuspHeight
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanGreedyBalancedReduction
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBalancedSiegelFiniteness

/-!
# Determinant-balanced Siegel reduction inside finite cusp charts

The uniform adjacent weighted-mean bound at a finite cusp is converted to a pointwise local
Siegel bound by determinant-one unit balancing.  Mixed unipotent size reduction then bounds every
real and complex upper entry without changing the balanced Jacobi weights.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- A finite-cusp weighted-mean bound becomes a uniform determinant-balanced Siegel bound after
determinant-one unit balancing and mixed unipotent size reduction inside the cusp chart. -/
theorem exists_uniform_numberFieldArchimedean_finiteCusp_balancedSiegel
    (K : Type*) [Field K] [NumberField K] :
    ∃ t u R : ℝ, 1 ≤ t ∧ 0 ≤ u ∧ 0 ≤ R ∧
      ∀ A : numberFieldArchimedeanPositiveForms K 2,
        ∃ c : numberFieldRankTwoCuspType K,
          ∃ h : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K),
            ∃ g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K),
              NumberFieldArchimedeanIsDetBalancedSiegel t u R
                (g • numberFieldRankTwoCuspChart
                  (numberFieldRankTwoCuspRepresentative K c).1
                  (numberFieldRankTwoCuspRepresentative K c).2 (h • A)) := by
  obtain ⟨Cmean, hheight⟩ :=
    exists_uniform_numberFieldArchimedean_finiteCusp_headMeanRatio K
  obtain ⟨Rb, hRb, hbalance⟩ :=
    exists_numberFieldArchimedeanJacobiUnitConj_balancingRadius_of_data (K := K)
  obtain ⟨U, hU, hreduce⟩ :=
    exists_numberFieldArchimedeanJacobi_sizeReductionRadius K
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
  obtain ⟨c, h, J, hmean⟩ := hheight A
  let A0 := numberFieldRankTwoCuspChart
    (numberFieldRankTwoCuspRepresentative K c).1
    (numberFieldRankTwoCuspRepresentative K c).2 (h • A)
  obtain ⟨units, hunits, J1, hbounds⟩ := hbalance 1 A0 J
  let A1 := (numberFieldUnitSpecialLinear units hunits) • A0
  obtain ⟨N, hNdet, hN, hreal, hcomplex⟩ := hreduce 2 A1 J1
  let g2 : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) :=
    numberFieldTransposeSpecialLinear N hNdet
  let J2 : NumberFieldArchimedeanJacobiData (g2 • A1) :=
    numberFieldArchimedeanJacobiTransposeConj A1 J1 N hNdet hN
  let g : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) :=
    g2 * numberFieldUnitSpecialLinear units hunits
  have hform : g • A0 = g2 • A1 := by
    simp [g, A1, mul_smul]
  refine ⟨c, h, g, ?_⟩
  rw [hform]
  refine ⟨J2, ?_⟩
  have hweight (i : Fin 2) (w : InfinitePlace K) :
      numberFieldArchimedeanJacobiWeight J2 i w =
        numberFieldArchimedeanJacobiWeight J1 i w := by
    exact numberFieldArchimedeanJacobiWeight_transposeConj
      A1 J1 N hNdet hN i w
  have hcenter (w : InfinitePlace K) :
      numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J2 j v)) w =
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w := by
    calc
      _ = numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J1 j v)) w :=
        numberFieldCenteredJacobiProfile_smul J1 g2 J2 w
      _ = _ := numberFieldCenteredJacobiProfile_smul J
        (numberFieldUnitSpecialLinear units hunits) J1 w
  have hrelative : J2.IsBalancedRelativeTo J R := by
    intro i w
    have hb := hbounds i w
    rw [hweight i w]
    exact abs_log_sub_le_of_exp_mul_le
      (numberFieldArchimedeanJacobiWeight_pos J1 i w)
      (s := numberFieldWeightedPlaceMean
          (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v)) +
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)
      (C := R)
      (by simpa [R, Real.exp_add] using hb.1)
      (by simpa [R, Real.exp_add] using hb.2)
  have hdiag (w : InfinitePlace K) :
      numberFieldArchimedeanJacobiWeight J2 (0 : Fin 2) w ≤
        t * numberFieldArchimedeanJacobiWeight J2 (1 : Fin 2) w := by
    have hratio := hrelative.log_ratio_sub_mean_le
      (0 : Fin 2) (1 : Fin 2) w
    have hupp :
        Real.log (numberFieldArchimedeanJacobiWeight J2 (0 : Fin 2) w) -
            Real.log (numberFieldArchimedeanJacobiWeight J2 (1 : Fin 2) w) ≤
          max (Cmean + 2 * R) 0 := by
      have habs := (abs_le.mp hratio).2
      have hsum :
          Real.log (numberFieldArchimedeanJacobiWeight J2 (0 : Fin 2) w) -
              Real.log (numberFieldArchimedeanJacobiWeight J2 (1 : Fin 2) w) ≤
            Cmean + 2 * R := by
        linarith [hmean]
      exact hsum.trans (le_max_left _ _)
    have hexp := Real.exp_le_exp.mpr hupp
    have hw0 := numberFieldArchimedeanJacobiWeight_pos J2 (0 : Fin 2) w
    have hw1 := numberFieldArchimedeanJacobiWeight_pos J2 (1 : Fin 2) w
    rw [Real.exp_sub, Real.exp_log hw0, Real.exp_log hw1] at hexp
    exact (div_le_iff₀ hw1).mp (by simpa [t] using hexp)
  have hrealAll : ∀ w (i j : Fin 2), |J2.realU w i j| ≤ u := by
    intro w i j
    by_cases hij : i < j
    · exact (hreal w i j hij).trans (le_max_left _ _)
    · by_cases hji : j < i
      · rw [J2.realUpper w i j hji, abs_zero]
        exact hu
      · have hijEq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
        subst j
        rw [J2.realUnit, abs_one]
        exact le_max_right _ _
  have hcomplexAll : ∀ w (i j : Fin 2), ‖J2.complexU w i j‖ ≤ u := by
    intro w i j
    by_cases hij : i < j
    · exact (hcomplex w i j hij).trans (le_max_left _ _)
    · by_cases hji : j < i
      · rw [J2.complexUpper w i j hji, norm_zero]
        exact hu
      · have hijEq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
        subst j
        rw [J2.complexUnit, norm_one]
        exact le_max_right _ _
  constructor
  · rw [J2.isSiegel_iff]
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

end

end GaloisForLFunctions.HTGeometry
