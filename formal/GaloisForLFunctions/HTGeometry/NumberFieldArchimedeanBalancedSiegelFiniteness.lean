import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBalancedSiegelLocal
import GaloisForLFunctions.HTGeometry.NumberFieldIntegerFiniteness

/-!
# Siegel finiteness for determinant-balanced number-field forms

The local bounded-isometry argument is fed by two global product-formula consequences: same-index
diagonal comparison from leading minors, and inverse-entry support comparison from the norm of a
nonzero algebraic integer.  This produces one bound for every real and complex embedding of every
integral transition matrix, hence a finite transition set by Minkowski discreteness.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Uniform mixed-embedding bound for transitions between determinant-balanced simultaneous
Siegel forms. -/
theorem exists_numberFieldArchimedean_detBalancedSiegelTransitionBound
    (K : Type*) [Field K] [NumberField K]
    (m : ℕ) (t u R : ℝ) (ht : 1 ≤ t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀
      (A : numberFieldArchimedeanPositiveForms K (m + 1))
      (J : NumberFieldArchimedeanJacobiData A)
      (g : Matrix.SpecialLinearGroup (Fin (m + 1)) (RingOfIntegers K))
      (J' : NumberFieldArchimedeanJacobiData (g • A)),
      J.IsSiegel t u → J'.IsSiegel t u →
      J.IsDetBalanced R → J'.IsDetBalanced R →
      ((∀ i j, ∀ w : {w : InfinitePlace K // w.IsReal},
          |InfinitePlace.embedding_of_isReal w.2
            (((g : Matrix (Fin (m + 1)) (Fin (m + 1)) (RingOfIntegers K)) i j :
              RingOfIntegers K) : K)| ≤ B) ∧
        ∀ i j, ∀ w : {w : InfinitePlace K // w.IsComplex},
          ‖w.1.embedding
            (((g : Matrix (Fin (m + 1)) (Fin (m + 1)) (RingOfIntegers K)) i j :
              RingOfIntegers K) : K)‖ ≤ B) := by
  let n := m + 1
  obtain ⟨C, hC, hcmp⟩ :=
    exists_numberFieldArchimedean_detBalancedDiagonalComparison K m t u R ht
  obtain ⟨Q, hQ, hinv⟩ :=
    exists_numberFieldArchimedean_nonzeroInverseEntryWeightComparison K m t u R ht
  obtain ⟨Cur, hCur⟩ := exists_unipotent_inv_bound n u
  obtain ⟨Cuc, hCuc⟩ := exists_complex_unipotent_inv_bound n u
  let Cu : ℝ := max (max Cur Cuc) 0
  have hCu : 0 ≤ Cu := le_max_right _ _
  have hCur' : ∀ U ∈ unipotentBall n u, ∀ i j, |U⁻¹ i j| ≤ Cu :=
    fun U hU i j ↦ (hCur U hU i j).trans
      ((le_max_left Cur Cuc).trans (le_max_left _ _))
  have hCuc' : ∀ U ∈ complexUnipotentBall n u, ∀ i j, ‖U⁻¹ i j‖ ≤ Cu :=
    fun U hU i j ↦ (hCuc U hU i j).trans
      ((le_max_right Cur Cuc).trans (le_max_left _ _))
  let B₀ : ℝ := (n : ℝ) * ((n : ℝ) *
    (Cu * Real.sqrt (C * (t ^ n * ((C * Q) * t ^ n)))) * u)
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨B, hB, ?_⟩
  intro A J g J' hJ hJ' hbal hbal'
  have hcmpAll := hcmp A J g J' hJ hJ' hbal hbal'
  have hinvAll := hinv A J g J' hJ hJ' hbal hbal'
  constructor
  · intro i j w
    let G := numberFieldRealOrderMatrixAt w
      (g : Matrix (Fin n) (Fin n) (RingOfIntegers K))
    let D := numberFieldRealOrderMatrixAt w
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (RingOfIntegers K)) :
        Matrix (Fin n) (Fin n) (RingOfIntegers K))
    let γ := Matrix.transpose G
    let δ := Matrix.transpose D
    have hDG : D * G = 1 := by
      dsimp [D, G]
      rw [← numberFieldRealOrderMatrixAt_mul, Matrix.adjugate_mul, g.2, one_smul,
        numberFieldRealOrderMatrixAt_one]
    have hGD : G * D = 1 := by
      dsimp [D, G]
      rw [← numberFieldRealOrderMatrixAt_mul, Matrix.mul_adjugate, g.2, one_smul,
        numberFieldRealOrderMatrixAt_one]
    have hγδ : γ * δ = 1 := by
      simpa [γ, δ] using congrArg Matrix.transpose hDG
    have hδγ : δ * γ = 1 := by
      simpa [γ, δ] using congrArg Matrix.transpose hGD
    have hform : (J'.realJacobiData w).form =
        Matrix.transpose γ * (J.realJacobiData w).form * γ := by
      rw [J'.realJacobiData_form, J.realJacobiData_form]
      change G * (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) * Matrix.transpose G = _
      simp [γ]
    have hcmpLocal (q : Fin n) :
        (J'.realJacobiData w).d q ≤ C * (J.realJacobiData w).d q := by
      simpa [n, numberFieldArchimedeanJacobiWeight, w.2,
        NumberFieldArchimedeanJacobiData.realJacobiData] using (hcmpAll q w.1).2
    have hδLocal (a b : Fin n) (δab : δ a b ≠ 0) :
        (J.realJacobiData w).d a ≤ (C * Q) * (J.realJacobiData w).d b := by
      have hab :
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (RingOfIntegers K)) :
            Matrix (Fin n) (Fin n) (RingOfIntegers K)) b a ≠ 0 := by
        rw [Matrix.SpecialLinearGroup.coe_inv]
        intro hz
        apply δab
        simp [δ, D, numberFieldRealOrderMatrixAt, hz]
      have hq := hinvAll a b hab w.1
      have hc := (hcmpAll a w.1).1
      simpa [n, numberFieldArchimedeanJacobiWeight, w.2,
        NumberFieldArchimedeanJacobiData.realJacobiData, mul_assoc] using
        hc.trans (mul_le_mul_of_nonneg_left hq hC.le)
    have hU : ∀ a b, |(J.realJacobiData w).U⁻¹ a b| ≤ Cu :=
      hCur' (J.realJacobiData w).U
        ⟨(J.realJacobiData w).upper, (J.realJacobiData w).unit, (hJ.1 w).2⟩
    have hb := real_siegelTransition_entry_bound_of_inverseSupport ht hC
      (mul_pos hC hQ) hCu (hJ.1 w) (hJ'.1 w) hγδ hδγ hform
      hcmpLocal hδLocal hU j i
    have heval : γ j i = InfinitePlace.embedding_of_isReal w.2
        (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i j :
          RingOfIntegers K) : K) := rfl
    rw [heval] at hb
    exact hb.trans (le_max_left _ _)
  · intro i j w
    let G := numberFieldComplexOrderMatrixAt w
      (g : Matrix (Fin n) (Fin n) (RingOfIntegers K))
    let D := numberFieldComplexOrderMatrixAt w
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (RingOfIntegers K)) :
        Matrix (Fin n) (Fin n) (RingOfIntegers K))
    let γ := Matrix.conjTranspose G
    let δ := Matrix.conjTranspose D
    have hDG : D * G = 1 := by
      dsimp [D, G]
      rw [← numberFieldComplexOrderMatrixAt_mul, Matrix.adjugate_mul, g.2, one_smul,
        numberFieldComplexOrderMatrixAt_one]
    have hGD : G * D = 1 := by
      dsimp [D, G]
      rw [← numberFieldComplexOrderMatrixAt_mul, Matrix.mul_adjugate, g.2, one_smul,
        numberFieldComplexOrderMatrixAt_one]
    have hγδ : γ * δ = 1 := by
      simpa [γ, δ] using congrArg Matrix.conjTranspose hDG
    have hδγ : δ * γ = 1 := by
      simpa [γ, δ] using congrArg Matrix.conjTranspose hGD
    have hform : (J'.complexJacobiData w).form =
        Matrix.conjTranspose γ * (J.complexJacobiData w).form * γ := by
      rw [J'.complexJacobiData_form, J.complexJacobiData_form]
      change G * (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) * Matrix.conjTranspose G = _
      simp [γ]
    have hcmpLocal (q : Fin n) :
        (J'.complexJacobiData w).d q ≤ C * (J.complexJacobiData w).d q := by
      have hnr : ¬w.1.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr w.2
      simpa [n, numberFieldArchimedeanJacobiWeight, hnr,
        NumberFieldArchimedeanJacobiData.complexJacobiData] using (hcmpAll q w.1).2
    have hδLocal (a b : Fin n) (δab : δ a b ≠ 0) :
        (J.complexJacobiData w).d a ≤ (C * Q) * (J.complexJacobiData w).d b := by
      have hab :
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) (RingOfIntegers K)) :
            Matrix (Fin n) (Fin n) (RingOfIntegers K)) b a ≠ 0 := by
        rw [Matrix.SpecialLinearGroup.coe_inv]
        intro hz
        apply δab
        simp [δ, D, numberFieldComplexOrderMatrixAt, hz]
      have hq := hinvAll a b hab w.1
      have hc := (hcmpAll a w.1).1
      have hnr : ¬w.1.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr w.2
      simpa [n, numberFieldArchimedeanJacobiWeight, hnr,
        NumberFieldArchimedeanJacobiData.complexJacobiData, mul_assoc] using
        hc.trans (mul_le_mul_of_nonneg_left hq hC.le)
    have hU : ∀ a b, ‖(J.complexJacobiData w).U⁻¹ a b‖ ≤ Cu :=
      hCuc' (J.complexJacobiData w).U
        ⟨(J.complexJacobiData w).upper, (J.complexJacobiData w).unit, (hJ.2 w).2⟩
    have hb := complex_siegelTransition_entry_bound_of_inverseSupport ht hC
      (mul_pos hC hQ) hCu (hJ.2 w) (hJ'.2 w) hγδ hδγ hform
      hcmpLocal hδLocal hU j i
    have heval : ‖γ j i‖ = ‖w.1.embedding
        (((g : Matrix (Fin n) (Fin n) (RingOfIntegers K)) i j :
          RingOfIntegers K) : K)‖ := by
      simp [γ, G, numberFieldComplexOrderMatrixAt]
    rw [heval] at hb
    exact hb.trans (le_max_left _ _)

/-- Determinant-balanced simultaneous Siegel forms. -/
def NumberFieldArchimedeanIsDetBalancedSiegel
    {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (t u R : ℝ) (A : numberFieldArchimedeanPositiveForms K (m + 1)) : Prop :=
  ∃ J : NumberFieldArchimedeanJacobiData A,
    J.IsSiegel t u ∧ J.IsDetBalanced R

/-- **Finite overlap for determinant-balanced number-field Siegel forms.** -/
theorem finite_numberFieldArchimedean_detBalancedSiegelTransitionSet
    (K : Type*) [Field K] [NumberField K]
    (m : ℕ) (t u R : ℝ) (ht : 1 ≤ t) :
    {g : Matrix.SpecialLinearGroup (Fin (m + 1)) (RingOfIntegers K) |
      ∃ A : numberFieldArchimedeanPositiveForms K (m + 1),
        NumberFieldArchimedeanIsDetBalancedSiegel t u R A ∧
          NumberFieldArchimedeanIsDetBalancedSiegel t u R (g • A)}.Finite := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_numberFieldArchimedean_detBalancedSiegelTransitionBound K m t u R ht
  let T : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) (RingOfIntegers K)) :=
    {M |
      (∀ i j, ∀ w : {w : InfinitePlace K // w.IsReal},
        |InfinitePlace.embedding_of_isReal w.2 (M i j : K)| ≤ B) ∧
      ∀ i j, ∀ w : {w : InfinitePlace K // w.IsComplex},
        ‖w.1.embedding (M i j : K)‖ ≤ B}
  have hT : T.Finite :=
    finite_numberFieldIntegerMatrix_of_archimedean_bound (m + 1) B hB
  refine (hT.preimage
    (f := fun g : Matrix.SpecialLinearGroup (Fin (m + 1)) (RingOfIntegers K) ↦
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (RingOfIntegers K))) ?_).subset ?_
  · intro g _ h _ hgh
    exact Subtype.ext hgh
  · rintro g ⟨A, ⟨J, hJ, hbal⟩, J', hJ', hbal'⟩
    exact hbound A J g J' hJ hJ' hbal hbal'

end

end GaloisForLFunctions.HTGeometry
