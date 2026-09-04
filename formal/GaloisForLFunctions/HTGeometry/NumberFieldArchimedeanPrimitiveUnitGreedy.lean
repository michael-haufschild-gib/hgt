import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanGreedyFlag
import GaloisForLFunctions.HTGeometry.NumberFieldUnitPositiveWeightBalancing

/-!
# Unit-scaled competitors for primitive-minimal archimedean flags

Recursive primitive minimality may be tested against a coordinate vector scaled by any number-ring
unit.  A compensating inverse unit in the preceding coordinate makes this comparison an exact
determinant-one diagonal congruence.  Single-unit Dirichlet balancing then bounds the greedy head
by the multiplicity-weighted geometric mean of the next form diagonal.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder Matrix NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Product-one unit tuple scaling the first two coordinates inversely. -/
def numberFieldHeadSecondUnitTuple {m : ℕ} (u : (𝓞 K)ˣ) :
    Fin (m + 2) → (𝓞 K)ˣ :=
  Fin.cons u⁻¹ (Fin.cons u (fun _ ↦ 1))

omit [NumberField K] in
@[simp]
theorem numberFieldHeadSecondUnitTuple_zero {m : ℕ} (u : (𝓞 K)ˣ) :
    numberFieldHeadSecondUnitTuple (m := m) u (0 : Fin (m + 2)) = u⁻¹ := rfl

omit [NumberField K] in
@[simp]
theorem numberFieldHeadSecondUnitTuple_one {m : ℕ} (u : (𝓞 K)ˣ) :
    numberFieldHeadSecondUnitTuple (m := m) u (1 : Fin (m + 2)) = u := rfl

omit [NumberField K] in
theorem prod_numberFieldHeadSecondUnitTuple {m : ℕ} (u : (𝓞 K)ˣ) :
    ∏ i, numberFieldHeadSecondUnitTuple (m := m) u i = 1 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp [numberFieldHeadSecondUnitTuple]

omit [NumberField K] in
theorem transpose_numberFieldUnitDiagonal
    {n : ℕ} (u : Fin n → (𝓞 K)ˣ) :
    Matrix.transpose (numberFieldUnitDiagonal u) = numberFieldUnitDiagonal u := by
  ext i j
  by_cases h : i = j
  · subst j
    rfl
  · simp [numberFieldUnitDiagonal, Matrix.transpose_apply, h, Ne.symm h]

/-- A recursively primitive-minimal form is no larger at its head than at the second coordinate
after any inverse determinant-one unit rescaling of those two coordinates. -/
theorem NumberFieldArchimedeanGreedyFlag.head_energy_le_unitConj_second
    {m : ℕ} (A : numberFieldArchimedeanPositiveForms K (m + 2))
    (hgreedy : NumberFieldArchimedeanGreedyFlag (m + 2) A)
    (u : (𝓞 K)ˣ) :
    numberFieldArchimedeanEnergy A
        (numberFieldIntegerVectorEmbedding K
          (numberFieldCoordinateBasis (K := K) (0 : Fin (m + 2)))) ≤
      numberFieldArchimedeanEnergy
        ((numberFieldUnitSpecialLinear
          (numberFieldHeadSecondUnitTuple (m := m) u)
          (prod_numberFieldHeadSecondUnitTuple (m := m) u)) • A)
        (numberFieldIntegerVectorEmbedding K
          (numberFieldCoordinateBasis (K := K) (1 : Fin (m + 2)))) := by
  let v := numberFieldHeadSecondUnitTuple (m := m) u
  have hv : ∏ i, v i = 1 := prod_numberFieldHeadSecondUnitTuple (m := m) u
  let D : Matrix (Fin (m + 2)) (Fin (m + 2)) (𝓞 K) :=
    numberFieldUnitDiagonal v
  have hD : D.det = 1 := det_numberFieldUnitDiagonal_eq_one v hv
  have hprim : ∃ p : Fin (m + 2) → 𝓞 K,
      ∑ i, p i *
        (D.mulVec (numberFieldCoordinateBasis (K := K) (1 : Fin (m + 2)))) i = 1 :=
    detOne_mulVec_coordinateBasis_primitive D hD (1 : Fin (m + 2))
  have hmin := hgreedy.1
    (D.mulVec (numberFieldCoordinateBasis (K := K) (1 : Fin (m + 2)))) hprim
  have heq : transposeSpecialLinearOfDetOne D hD =
      numberFieldUnitSpecialLinear v hv := by
    apply Subtype.ext
    exact transpose_numberFieldUnitDiagonal v
  rw [← heq]
  rw [numberFieldArchimedeanEnergy_transposeSpecialLinear]
  exact hmin

/-- Recursive primitive minimality plus one-unit Dirichlet balancing controls the first-coordinate
energy by the multiplicity-weighted geometric mean of the second form diagonal. -/
theorem exists_numberFieldArchimedean_greedyHeadGeometricBoundRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ R : ℝ, 0 < R ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K (m + 2)),
      NumberFieldArchimedeanGreedyFlag (m + 2) A →
      numberFieldArchimedeanEnergy A
          (numberFieldIntegerVectorEmbedding K
            (numberFieldCoordinateBasis (K := K) (0 : Fin (m + 2)))) ≤
        ((Fintype.card {w : InfinitePlace K // w.IsReal} +
            Fintype.card {w : InfinitePlace K // w.IsComplex} : ℕ) : ℝ) *
          Real.exp (2 * R) *
          Real.exp (numberFieldWeightedPlaceMean (fun w ↦
            Real.log (numberFieldArchimedeanDiagonalWeight A
              (1 : Fin (m + 2)) w))) := by
  obtain ⟨R, hR, hbalance⟩ :=
    exists_numberFieldUnit_positiveWeight_balancingRadius (K := K)
  refine ⟨R, hR, ?_⟩
  intro m A hgreedy
  let a : InfinitePlace K → ℝ := fun w ↦
    numberFieldArchimedeanDiagonalWeight A (1 : Fin (m + 2)) w
  have ha : ∀ w, 0 < a w := fun w ↦
    numberFieldArchimedeanDiagonalWeight_pos A (1 : Fin (m + 2)) w
  obtain ⟨u, hu⟩ := hbalance a ha
  let v := numberFieldHeadSecondUnitTuple (m := m) u
  have hv : ∏ i, v i = 1 := prod_numberFieldHeadSecondUnitTuple (m := m) u
  let A' : numberFieldArchimedeanPositiveForms K (m + 2) :=
    (numberFieldUnitSpecialLinear v hv) • A
  have hhead :
      numberFieldArchimedeanEnergy A
          (numberFieldIntegerVectorEmbedding K
            (numberFieldCoordinateBasis (K := K) (0 : Fin (m + 2)))) ≤
        numberFieldArchimedeanEnergy A'
          (numberFieldIntegerVectorEmbedding K
            (numberFieldCoordinateBasis (K := K) (1 : Fin (m + 2)))) := by
    exact hgreedy.head_energy_le_unitConj_second A u
  rw [numberFieldArchimedeanEnergy_coordinateBasis A'
    (1 : Fin (m + 2))] at hhead
  let C : ℝ := Real.exp (2 * R) *
    Real.exp (numberFieldWeightedPlaceMean (fun w ↦ Real.log (a w)))
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal},
      (A'.1.1 w : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
          (1 : Fin (m + 2)) (1 : Fin (m + 2)) ≤ C := by
    intro w
    have hw := (hu w.1).2
    have hdiag := numberFieldArchimedeanDiagonalWeight_unitConj
      v hv A (1 : Fin (m + 2)) w.1
    have hvone : v (1 : Fin (m + 2)) = u := by rfl
    rw [hvone] at hdiag
    change numberFieldArchimedeanDiagonalWeight A'
        (1 : Fin (m + 2)) w.1 = _ at hdiag
    rw [← hdiag] at hw
    simpa [numberFieldArchimedeanDiagonalWeight, w.2, C] using hw
  have hcomplex : ∀ w : {w : InfinitePlace K // w.IsComplex},
      ((A'.1.2 w : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)
          (1 : Fin (m + 2)) (1 : Fin (m + 2))).re ≤ C := by
    intro w
    have hw := (hu w.1).2
    have hdiag := numberFieldArchimedeanDiagonalWeight_unitConj
      v hv A (1 : Fin (m + 2)) w.1
    have hvone : v (1 : Fin (m + 2)) = u := by rfl
    rw [hvone] at hdiag
    change numberFieldArchimedeanDiagonalWeight A'
        (1 : Fin (m + 2)) w.1 = _ at hdiag
    rw [← hdiag] at hw
    have hnreal : ¬w.1.IsReal :=
      InfinitePlace.not_isReal_iff_isComplex.mpr w.2
    simpa [numberFieldArchimedeanDiagonalWeight, hnreal, C] using hw
  calc
    numberFieldArchimedeanEnergy A
        (numberFieldIntegerVectorEmbedding K
          (numberFieldCoordinateBasis (K := K) (0 : Fin (m + 2)))) ≤
        (∑ _w : {w : InfinitePlace K // w.IsReal}, C) +
          ∑ _w : {w : InfinitePlace K // w.IsComplex}, C :=
      hhead.trans (add_le_add
        (Finset.sum_le_sum fun w _ ↦ hreal w)
        (Finset.sum_le_sum fun w _ ↦ hcomplex w))
    _ = ((Fintype.card {w : InfinitePlace K // w.IsReal} +
            Fintype.card {w : InfinitePlace K // w.IsComplex} : ℕ) : ℝ) * C := by
      simp [Nat.cast_add]
      ring
    _ = ((Fintype.card {w : InfinitePlace K // w.IsReal} +
            Fintype.card {w : InfinitePlace K // w.IsComplex} : ℕ) : ℝ) *
          Real.exp (2 * R) *
          Real.exp (numberFieldWeightedPlaceMean (fun w ↦
            Real.log (numberFieldArchimedeanDiagonalWeight A
              (1 : Fin (m + 2)) w))) := by
      dsimp [C, a]
      ring

end

end GaloisForLFunctions.HTGeometry
