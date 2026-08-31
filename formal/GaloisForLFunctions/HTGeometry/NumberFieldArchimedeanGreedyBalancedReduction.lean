import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBalancedSizeReduction
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanJacobiSchur
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanGreedySizeReduction

/-!
# Greedy determinant-balanced archimedean reduction

The generic unit-balancing layer must consume the same simultaneous Jacobi decomposition produced
by recursive primitive minimization.  This module supplies that specified-data interface and then
assembles one mass-greedy, determinant-balanced, size-reduced chain.  No independently chosen
Jacobi witness remains between those stages.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Unit balancing is available for any specified simultaneous Jacobi decomposition. -/
theorem exists_numberFieldArchimedeanJacobiUnitConj_balancingRadius_of_data :
    ∃ R : ℝ, 0 < R ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K (m + 1))
      (J : NumberFieldArchimedeanJacobiData A),
      ∃ u : Fin (m + 1) → (𝓞 K)ˣ,
        ∃ hu : ∏ i, u i = 1,
          ∃ J' : NumberFieldArchimedeanJacobiData
              ((numberFieldUnitSpecialLinear u hu) • A),
            ∀ i w,
              Real.exp (-(2 * (m + 1 : ℝ) * R)) *
                    (Real.exp (numberFieldWeightedPlaceMean
                        (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))) *
                      Real.exp (numberFieldCenteredPlaceProfileAverage
                        (fun j v => Real.log
                          (numberFieldArchimedeanJacobiWeight J j v)) w)) ≤
                numberFieldArchimedeanJacobiWeight J' i w ∧
              numberFieldArchimedeanJacobiWeight J' i w ≤
                Real.exp (2 * (m + 1 : ℝ) * R) *
                    (Real.exp (numberFieldWeightedPlaceMean
                        (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))) *
                      Real.exp (numberFieldCenteredPlaceProfileAverage
                        (fun j v => Real.log
                          (numberFieldArchimedeanJacobiWeight J j v)) w)) := by
  obtain ⟨R, hR, hbalance⟩ :=
    exists_numberFieldDetOneUnit_positiveWeight_balancingRadius (K := K)
  refine ⟨R, hR, ?_⟩
  intro m A J
  obtain ⟨u, hu, hbounds⟩ := hbalance m
    (fun i w => numberFieldArchimedeanJacobiWeight J i w)
    (fun i w => numberFieldArchimedeanJacobiWeight_pos J i w)
  let J' : NumberFieldArchimedeanJacobiData
      ((numberFieldUnitSpecialLinear u hu) • A) :=
    numberFieldArchimedeanJacobiUnitConj A J u hu
  refine ⟨u, hu, J', ?_⟩
  intro i w
  rw [show numberFieldArchimedeanJacobiWeight J' i w =
      numberFieldArchimedeanJacobiWeight J i w *
        (w (((u i : 𝓞 K) : K))) ^ 2 by
    exact numberFieldArchimedeanJacobiWeight_unitConj A J u hu i w]
  exact hbounds i w

/-- Target Jacobi weights are balanced around the coordinate means and common place profile of a
specified source decomposition.  This retains the source identity needed by the ratio step. -/
def NumberFieldArchimedeanJacobiData.IsBalancedRelativeTo
    {m : ℕ} {A A' : numberFieldArchimedeanPositiveForms K (m + 1)}
    (J' : NumberFieldArchimedeanJacobiData A')
    (J : NumberFieldArchimedeanJacobiData A) (R : ℝ) : Prop :=
  ∀ i w,
    |Real.log (numberFieldArchimedeanJacobiWeight J' i w) -
      (numberFieldWeightedPlaceMean
          (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v)) +
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)| ≤ R

/-- Relative balancing cancels the common place profile exactly, leaving twice the radius in every
same-place logarithmic weight ratio. -/
theorem NumberFieldArchimedeanJacobiData.IsBalancedRelativeTo.log_ratio_sub_mean_le
    {m : ℕ} {A A' : numberFieldArchimedeanPositiveForms K (m + 1)}
    {J' : NumberFieldArchimedeanJacobiData A'}
    {J : NumberFieldArchimedeanJacobiData A} {R : ℝ}
    (h : J'.IsBalancedRelativeTo J R) (i j : Fin (m + 1))
    (w : InfinitePlace K) :
    |(Real.log (numberFieldArchimedeanJacobiWeight J' i w) -
        Real.log (numberFieldArchimedeanJacobiWeight J' j w)) -
      (numberFieldWeightedPlaceMean
          (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v)) -
        numberFieldWeightedPlaceMean
          (fun v => Real.log (numberFieldArchimedeanJacobiWeight J j v)))| ≤ 2 * R := by
  let p := numberFieldCenteredPlaceProfileAverage
    (fun q v => Real.log (numberFieldArchimedeanJacobiWeight J q v)) w
  let ai := numberFieldWeightedPlaceMean
    (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))
  let aj := numberFieldWeightedPlaceMean
    (fun v => Real.log (numberFieldArchimedeanJacobiWeight J j v))
  let xi := Real.log (numberFieldArchimedeanJacobiWeight J' i w) - (ai + p)
  let xj := Real.log (numberFieldArchimedeanJacobiWeight J' j w) - (aj + p)
  have hxi : |xi| ≤ R := h i w
  have hxj : |xj| ≤ R := h j w
  have htriangle : |xi - xj| ≤ |xi| + |xj| := abs_sub _ _
  have heq :
      (Real.log (numberFieldArchimedeanJacobiWeight J' i w) -
          Real.log (numberFieldArchimedeanJacobiWeight J' j w)) - (ai - aj) =
        xi - xj := by
    dsimp only [xi, xj]
    ring
  rw [heq]
  linarith

/-- Exponentiated form of the exact relative-balance ratio law. -/
theorem NumberFieldArchimedeanJacobiData.IsBalancedRelativeTo.weight_ratio_bounds
    {m : ℕ} {A A' : numberFieldArchimedeanPositiveForms K (m + 1)}
    {J' : NumberFieldArchimedeanJacobiData A'}
    {J : NumberFieldArchimedeanJacobiData A} {R : ℝ}
    (h : J'.IsBalancedRelativeTo J R) (i j : Fin (m + 1))
    (w : InfinitePlace K) :
    let d := numberFieldWeightedPlaceMean
        (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v)) -
      numberFieldWeightedPlaceMean
        (fun v => Real.log (numberFieldArchimedeanJacobiWeight J j v))
    Real.exp (-2 * R) * Real.exp d ≤
        numberFieldArchimedeanJacobiWeight J' i w /
          numberFieldArchimedeanJacobiWeight J' j w ∧
      numberFieldArchimedeanJacobiWeight J' i w /
          numberFieldArchimedeanJacobiWeight J' j w ≤
        Real.exp (2 * R) * Real.exp d := by
  dsimp only
  let wi := numberFieldArchimedeanJacobiWeight J' i w
  let wj := numberFieldArchimedeanJacobiWeight J' j w
  let d := numberFieldWeightedPlaceMean
      (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v)) -
    numberFieldWeightedPlaceMean
      (fun v => Real.log (numberFieldArchimedeanJacobiWeight J j v))
  have habs : |(Real.log wi - Real.log wj) - d| ≤ 2 * R :=
    h.log_ratio_sub_mean_le i j w
  have hle := abs_le.mp habs
  have hwi : 0 < wi := numberFieldArchimedeanJacobiWeight_pos J' i w
  have hwj : 0 < wj := numberFieldArchimedeanJacobiWeight_pos J' j w
  have hexp : Real.exp (Real.log wi - Real.log wj) = wi / wj := by
    rw [Real.exp_sub, Real.exp_log hwi, Real.exp_log hwj]
  constructor
  · have hlower : -2 * R + d ≤ Real.log wi - Real.log wj := by linarith
    have hexplower := Real.exp_le_exp.mpr hlower
    rw [Real.exp_add, hexp] at hexplower
    simpa only [wi, wj, d] using hexplower
  · have hupper : Real.log wi - Real.log wj ≤ 2 * R + d := by linarith
    have hexpupper := Real.exp_le_exp.mpr hupper
    rw [Real.exp_add, hexp] at hexpupper
    simpa only [wi, wj, d] using hexpupper

/-- One unconditional chain starts with the complete mass-greedy flag, balances that exact
decomposition, then restores uniform real/complex upper-unipotent bounds without changing its
balanced Jacobi weights. -/
theorem exists_numberFieldArchimedean_massGreedyBalancedSizeReductionRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K (m + 1)),
      ∃ (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (𝓞 K)) (hB : B.det = 1),
        let A₀ := numberFieldArchimedeanPositiveConj
          (transposeSpecialLinearOfDetOne B hB) A
        ∃ J₀ : NumberFieldArchimedeanJacobiData A₀,
          J₀.IsMassGreedy (m + 1) A₀ ∧
          ∃ u : Fin (m + 1) → (𝓞 K)ˣ,
            ∃ hu : ∏ i, u i = 1,
              let A₁ := (numberFieldUnitSpecialLinear u hu) • A₀
              ∃ g₂ : Matrix.SpecialLinearGroup (Fin (m + 1)) (𝓞 K),
                ∃ J₂ : NumberFieldArchimedeanJacobiData (g₂ • A₁),
                  (∀ w i j, i < j → |J₂.realU w i j| ≤ C) ∧
                  (∀ w i j, i < j → ‖J₂.complexU w i j‖ ≤ C) ∧
                  J₂.IsDetBalanced (2 * (m + 1 : ℝ) * R) ∧
                  J₂.IsBalancedRelativeTo J₀ (2 * (m + 1 : ℝ) * R) := by
  obtain ⟨R, hR, hbalance⟩ :=
    exists_numberFieldArchimedeanJacobiUnitConj_balancingRadius_of_data (K := K)
  obtain ⟨C, hC, hreduce⟩ :=
    exists_numberFieldArchimedeanJacobi_sizeReductionRadius K
  refine ⟨R, C, hR, hC, ?_⟩
  intro m A
  obtain ⟨B, hB, J₀, hgreedy⟩ :=
    exists_numberFieldArchimedean_massGreedyJacobi K (m + 1) A
  let A₀ := numberFieldArchimedeanPositiveConj
    (transposeSpecialLinearOfDetOne B hB) A
  obtain ⟨u, hu, J₁, hbounds⟩ := hbalance m A₀ J₀
  let A₁ := (numberFieldUnitSpecialLinear u hu) • A₀
  obtain ⟨N, hNdet, hN, hreal, hcomplex⟩ := hreduce (m + 1) A₁ J₁
  let g₂ : Matrix.SpecialLinearGroup (Fin (m + 1)) (𝓞 K) :=
    numberFieldTransposeSpecialLinear N hNdet
  let J₂ : NumberFieldArchimedeanJacobiData (g₂ • A₁) :=
    numberFieldArchimedeanJacobiTransposeConj A₁ J₁ N hNdet hN
  refine ⟨B, hB, J₀, hgreedy, u, hu, g₂, J₂, hreal, hcomplex, ?_⟩
  have hcenter (w : InfinitePlace K) :
      numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₂ j v)) w =
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₀ j v)) w := by
    calc
      _ = numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₁ j v)) w :=
        numberFieldCenteredJacobiProfile_smul J₁ g₂ J₂ w
      _ = _ := numberFieldCenteredJacobiProfile_smul J₀
        (numberFieldUnitSpecialLinear u hu) J₁ w
  have hrelative : J₂.IsBalancedRelativeTo J₀ (2 * (m + 1 : ℝ) * R) := by
    intro i w
    have hweight : numberFieldArchimedeanJacobiWeight J₂ i w =
        numberFieldArchimedeanJacobiWeight J₁ i w := by
      exact numberFieldArchimedeanJacobiWeight_transposeConj A₁ J₁ N hNdet hN i w
    have hb := hbounds i w
    exact abs_log_sub_le_of_exp_mul_le
      (numberFieldArchimedeanJacobiWeight_pos J₂ i w)
      (s := numberFieldWeightedPlaceMean
          (fun v => Real.log (numberFieldArchimedeanJacobiWeight J₀ i v)) +
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₀ j v)) w)
      (C := 2 * (m + 1 : ℝ) * R)
      (by simpa [Real.exp_add, hweight] using hb.1)
      (by simpa [Real.exp_add, hweight] using hb.2)
  refine ⟨?_, hrelative⟩
  let a : Fin (m + 1) → ℝ := fun i =>
    numberFieldWeightedPlaceMean
      (fun v => Real.log (numberFieldArchimedeanJacobiWeight J₀ i v))
  refine ⟨a, ?_⟩
  intro i w
  rw [hcenter w]
  exact hrelative i w

/-- Complete reduced-greedy-to-balanced chain.  Unlike the preceding assembly, the greedy source
itself is already mixed size reduced; the same source is then unit balanced and the target is size
reduced again without changing its balanced weights. -/
theorem exists_numberFieldArchimedean_sizeReducedMassGreedyBalancedRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K (m + 1)),
      ∃ (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (𝓞 K)) (hB : B.det = 1),
        let A₀ := numberFieldArchimedeanPositiveConj
          (transposeSpecialLinearOfDetOne B hB) A
        ∃ (N : Matrix (Fin (m + 1)) (Fin (m + 1)) (𝓞 K)) (hNdet : N.det = 1)
          (_hN : IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N)),
          let A₁ := (numberFieldTransposeSpecialLinear N hNdet) • A₀
          ∃ J₁ : NumberFieldArchimedeanJacobiData A₁,
            J₁.IsMassGreedy (m + 1) A₁ ∧
            (∀ w i j, i < j → |J₁.realU w i j| ≤ C) ∧
            (∀ w i j, i < j → ‖J₁.complexU w i j‖ ≤ C) ∧
            ∃ u : Fin (m + 1) → (𝓞 K)ˣ,
              ∃ hu : ∏ i, u i = 1,
                let A₂ := (numberFieldUnitSpecialLinear u hu) • A₁
                ∃ g₃ : Matrix.SpecialLinearGroup (Fin (m + 1)) (𝓞 K),
                  ∃ J₃ : NumberFieldArchimedeanJacobiData (g₃ • A₂),
                    (∀ w i j, i < j → |J₃.realU w i j| ≤ C) ∧
                    (∀ w i j, i < j → ‖J₃.complexU w i j‖ ≤ C) ∧
                    J₃.IsDetBalanced (2 * (m + 1 : ℝ) * R) ∧
                    J₃.IsBalancedRelativeTo J₁ (2 * (m + 1 : ℝ) * R) := by
  obtain ⟨R, hR, hbalance⟩ :=
    exists_numberFieldArchimedeanJacobiUnitConj_balancingRadius_of_data (K := K)
  obtain ⟨C₁, hC₁, hsource⟩ :=
    exists_numberFieldArchimedean_massGreedySizeReducedJacobiRadius K
  obtain ⟨C₃, hC₃, hreduce⟩ :=
    exists_numberFieldArchimedeanJacobi_sizeReductionRadius K
  let C := max C₁ C₃
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  refine ⟨R, C, hR, hC, ?_⟩
  intro m A
  obtain ⟨B, hB, N, hNdet, hN, J₁, hgreedy, hreal₁, hcomplex₁⟩ :=
    hsource (m + 1) A
  let A₀ := numberFieldArchimedeanPositiveConj
    (transposeSpecialLinearOfDetOne B hB) A
  let A₁ := (numberFieldTransposeSpecialLinear N hNdet) • A₀
  obtain ⟨u, hu, J₂, hbounds⟩ := hbalance m A₁ J₁
  let A₂ := (numberFieldUnitSpecialLinear u hu) • A₁
  obtain ⟨N₃, hN₃det, hN₃, hreal₃, hcomplex₃⟩ := hreduce (m + 1) A₂ J₂
  let g₃ : Matrix.SpecialLinearGroup (Fin (m + 1)) (𝓞 K) :=
    numberFieldTransposeSpecialLinear N₃ hN₃det
  let J₃ : NumberFieldArchimedeanJacobiData (g₃ • A₂) :=
    numberFieldArchimedeanJacobiTransposeConj A₂ J₂ N₃ hN₃det hN₃
  have hreal₁' : ∀ w i j, i < j → |J₁.realU w i j| ≤ C := by
    intro w i j hij
    exact (hreal₁ w i j hij).trans (le_max_left _ _)
  have hcomplex₁' : ∀ w i j, i < j → ‖J₁.complexU w i j‖ ≤ C := by
    intro w i j hij
    exact (hcomplex₁ w i j hij).trans (le_max_left _ _)
  have hreal₃' : ∀ w i j, i < j → |J₃.realU w i j| ≤ C := by
    intro w i j hij
    exact (hreal₃ w i j hij).trans (le_max_right _ _)
  have hcomplex₃' : ∀ w i j, i < j → ‖J₃.complexU w i j‖ ≤ C := by
    intro w i j hij
    exact (hcomplex₃ w i j hij).trans (le_max_right _ _)
  refine ⟨B, hB, N, hNdet, hN, J₁, hgreedy, hreal₁', hcomplex₁',
    u, hu, g₃, J₃, hreal₃', hcomplex₃', ?_⟩
  have hcenter (w : InfinitePlace K) :
      numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₃ j v)) w =
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₁ j v)) w := by
    calc
      _ = numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₂ j v)) w :=
        numberFieldCenteredJacobiProfile_smul J₂ g₃ J₃ w
      _ = _ := numberFieldCenteredJacobiProfile_smul J₁
        (numberFieldUnitSpecialLinear u hu) J₂ w
  have hrelative : J₃.IsBalancedRelativeTo J₁ (2 * (m + 1 : ℝ) * R) := by
    intro i w
    have hweight : numberFieldArchimedeanJacobiWeight J₃ i w =
        numberFieldArchimedeanJacobiWeight J₂ i w := by
      exact numberFieldArchimedeanJacobiWeight_transposeConj
        A₂ J₂ N₃ hN₃det hN₃ i w
    have hb := hbounds i w
    exact abs_log_sub_le_of_exp_mul_le
      (numberFieldArchimedeanJacobiWeight_pos J₃ i w)
      (s := numberFieldWeightedPlaceMean
          (fun v => Real.log (numberFieldArchimedeanJacobiWeight J₁ i v)) +
        numberFieldCenteredPlaceProfileAverage
          (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J₁ j v)) w)
      (C := 2 * (m + 1 : ℝ) * R)
      (by simpa [Real.exp_add, hweight] using hb.1)
      (by simpa [Real.exp_add, hweight] using hb.2)
  refine ⟨?_, hrelative⟩
  let a : Fin (m + 1) → ℝ := fun i =>
    numberFieldWeightedPlaceMean
      (fun v => Real.log (numberFieldArchimedeanJacobiWeight J₁ i v))
  refine ⟨a, ?_⟩
  intro i w
  rw [hcenter w]
  exact hrelative i w

end

end GaloisForLFunctions.HTGeometry
