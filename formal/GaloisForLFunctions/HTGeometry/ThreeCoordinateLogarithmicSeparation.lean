import GaloisForLFunctions.HTGeometry.ThreeCoordinateAlgebraicIntersection
import GaloisForLFunctions.HTGeometry.DerivationAlgebraicStability
import GaloisForLFunctions.HTGeometry.FreeCoordinateAlgebraicConstantDescent
import GaloisForLFunctions.HTGeometry.FreeJetTranslationFixedField

/-!
# Logarithmic-derivative separation for three coordinate faces

Let three algebraically independent coordinates carry their coordinate derivations.  If nonzero
algebraic branches on the `(x,y)` and `(x,z)` faces multiply to an algebraic branch on the `(y,z)`
face, differentiating the product identity shows that the logarithmic derivatives of the first
branch in the `x` and `y` directions lie in two pair fields at once.  The exact algebraic-matroid
intersection theorem then descends them to the corresponding one-coordinate algebraic closures.

This is the differential core of three-field rank-one factorization.  No regularity or relative
algebraic-closure hypothesis is assumed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

/-- A coordinate derivation preserves algebraicity over every coordinate subfield. -/
theorem isAlgebraic_derivation_of_coordinateFrame
    {C L ι : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
    [DecidableEq ι] (v : ι → L) (D : ι → Derivation C L L)
    (hD : ∀ i j, D i (v j) = algebraMap C L (if j = i then 1 else 0))
    (i : ι) (S : Set ι) {u : L}
    (hu : IsAlgebraic (IntermediateField.adjoin C (v '' S)) u) :
    IsAlgebraic (IntermediateField.adjoin C (v '' S)) (D i u) := by
  apply mem_algebraicClosure_iff.mp
  apply derivationBase_mem_algebraicClosure_adjoin (D i)
  · rintro _ ⟨j, hj, rfl⟩
    rw [hD]
    exact (IntermediateField.adjoin C (v '' S)).algebraMap_mem _
  · exact mem_algebraicClosure_iff.mpr hu

/-- A coordinate derivative absent from a coordinate subfield kills every algebraic branch over
that subfield. -/
theorem coordinateDerivation_eq_zero_of_isAlgebraic_pair
    {C L ι : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
    [DecidableEq ι] (v : ι → L) (D : ι → Derivation C L L)
    (hD : ∀ i j, D i (v j) = algebraMap C L (if j = i then 1 else 0))
    {i : ι} {S : Set ι} (hi : i ∉ S) {u : L}
    (hu : IsAlgebraic (IntermediateField.adjoin C (v '' S)) u) :
    D i u = 0 := by
  apply derivationBase_eq_zero_of_isAlgebraic_adjoin (D i) (S := v '' S)
  · rintro _ ⟨j, hj, rfl⟩
    rw [hD, if_neg]
    · simp
    · intro hji
      exact hi (hji ▸ hj)
  · exact hu

/-- **Three-face logarithmic separation.**  For `A(x,y) B(x,z) = Q(y,z)`, the `x`- and
`y`-logarithmic derivatives of `A` are algebraic over `C(x)` and `C(y)`, respectively. -/
theorem threeCoordinate_logarithmicDerivative_separation
    {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
    (v : Fin 3 → L) (hv : AlgebraicIndependent C v)
    (D : Fin 3 → Derivation C L L)
    (hD : ∀ i j, D i (v j) = algebraMap C L (if j = i then 1 else 0))
    {A B Q : L} (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hA : IsAlgebraic (IntermediateField.adjoin C (v '' ({0, 1} : Set (Fin 3)))) A)
    (hB : IsAlgebraic (IntermediateField.adjoin C (v '' ({0, 2} : Set (Fin 3)))) B)
    (hQ : IsAlgebraic (IntermediateField.adjoin C (v '' ({1, 2} : Set (Fin 3)))) Q)
    (hprod : A * B = Q) :
    IsAlgebraic (IntermediateField.adjoin C ({v 0} : Set L)) (D 0 A / A) ∧
      IsAlgebraic (IntermediateField.adjoin C ({v 1} : Set L)) (D 1 A / A) := by
  have hQ0 : Q ≠ 0 := by rw [← hprod]; exact mul_ne_zero hA0 hB0
  have hDAx := isAlgebraic_derivation_of_coordinateFrame v D hD 0
    ({0, 1} : Set (Fin 3)) hA
  have hDBx := isAlgebraic_derivation_of_coordinateFrame v D hD 0
    ({0, 2} : Set (Fin 3)) hB
  have hDAy := isAlgebraic_derivation_of_coordinateFrame v D hD 1
    ({0, 1} : Set (Fin 3)) hA
  have hDQy := isAlgebraic_derivation_of_coordinateFrame v D hD 1
    ({1, 2} : Set (Fin 3)) hQ
  have hqxA : IsAlgebraic
      (IntermediateField.adjoin C (v '' ({0, 1} : Set (Fin 3)))) (D 0 A / A) :=
    mem_algebraicClosure_iff.mp ((algebraicClosure
      (IntermediateField.adjoin C (v '' ({0, 1} : Set (Fin 3)))) L).div_mem
        (mem_algebraicClosure_iff.mpr hDAx) (mem_algebraicClosure_iff.mpr hA))
  have hqxB : IsAlgebraic
      (IntermediateField.adjoin C (v '' ({0, 2} : Set (Fin 3)))) (-(D 0 B / B)) :=
    mem_algebraicClosure_iff.mp ((algebraicClosure
      (IntermediateField.adjoin C (v '' ({0, 2} : Set (Fin 3)))) L).neg_mem
        ((algebraicClosure
          (IntermediateField.adjoin C (v '' ({0, 2} : Set (Fin 3)))) L).div_mem
            (mem_algebraicClosure_iff.mpr hDBx) (mem_algebraicClosure_iff.mpr hB)))
  have hqyA : IsAlgebraic
      (IntermediateField.adjoin C (v '' ({0, 1} : Set (Fin 3)))) (D 1 A / A) :=
    mem_algebraicClosure_iff.mp ((algebraicClosure
      (IntermediateField.adjoin C (v '' ({0, 1} : Set (Fin 3)))) L).div_mem
        (mem_algebraicClosure_iff.mpr hDAy) (mem_algebraicClosure_iff.mpr hA))
  have hqyQ : IsAlgebraic
      (IntermediateField.adjoin C (v '' ({1, 2} : Set (Fin 3)))) (D 1 Q / Q) :=
    mem_algebraicClosure_iff.mp ((algebraicClosure
      (IntermediateField.adjoin C (v '' ({1, 2} : Set (Fin 3)))) L).div_mem
        (mem_algebraicClosure_iff.mpr hDQy) (mem_algebraicClosure_iff.mpr hQ))
  have hDxQ : D 0 Q = 0 :=
    coordinateDerivation_eq_zero_of_isAlgebraic_pair v D hD (by simp) hQ
  have hDyB : D 1 B = 0 :=
    coordinateDerivation_eq_zero_of_isAlgebraic_pair v D hD (by simp) hB
  have hqx : D 0 A / A = -(D 0 B / B) := by
    have h := congrArg (D 0) hprod
    rw [Derivation.leibniz, hDxQ] at h
    simp only [smul_eq_mul] at h
    field_simp [hA0, hB0]
    linear_combination h
  have hqy : D 1 A / A = D 1 Q / Q := by
    have h := congrArg (D 1) hprod
    rw [Derivation.leibniz, hDyB] at h
    simp only [smul_eq_mul, mul_zero, zero_add] at h
    apply (div_eq_div_iff hA0 hQ0).2
    calc
      D 1 A * Q = D 1 A * (A * B) := by rw [hprod]
      _ = A * (B * D 1 A) := by ring
      _ = A * D 1 Q := by rw [h]
      _ = D 1 Q * A := by ring
  constructor
  · apply isAlgebraic_over_commonCoordinate_of_independent
      (i := 0) (j := 1) (k := 2) v hv (by decide) hqxA
    rw [hqx]
    exact hqxB
  · apply isAlgebraic_over_commonCoordinate_of_independent
      (i := 1) (j := 0) (k := 2) v hv (by decide)
    · have hpair : v '' ({1, 0} : Set (Fin 3)) = v '' ({0, 1} : Set (Fin 3)) := by
        ext x
        simp [or_comm]
      rw [hpair]
      exact hqyA
    · rw [hqy]
      exact hqyQ

/-- A free coordinate embedded in the fixed algebraic closure of the free rational field. -/
def algebraicClosureFreeCoordinate
    (C σ : Type*) [Field C] (i : σ) : FreeCoordinateAlgebraicClosure C σ :=
  algebraMap (FreeCoordinateRationalField C σ)
    (FreeCoordinateAlgebraicClosure C σ) (freeCoordinate C σ i)

/-- Free coordinates remain algebraically independent after embedding in their algebraic closure.
-/
theorem algebraicIndependent_algebraicClosureFreeCoordinate
    (C σ : Type*) [Field C] :
    AlgebraicIndependent C (algebraicClosureFreeCoordinate C σ) := by
  let K := FreeCoordinateRationalField C σ
  let L := FreeCoordinateAlgebraicClosure C σ
  let incl : K →ₐ[C] L := IsScalarTower.toAlgHom C K L
  have h := (algebraicIndependent_freeCoordinate C σ).map'
    (f := incl) incl.injective
  exact h

@[simp]
theorem freeCoordinateAlgebraicClosureDerivation_coordinate
    {C σ : Type*} [Field C] [CharZero C] [DecidableEq σ] (i j : σ) :
    freeCoordinateAlgebraicClosureDerivation i
        (algebraicClosureFreeCoordinate C σ j) =
      algebraMap C (FreeCoordinateAlgebraicClosure C σ)
        (if j = i then 1 else 0) := by
  classical
  rw [algebraicClosureFreeCoordinate,
    freeCoordinateAlgebraicClosureDerivation_algebraMap]
  by_cases hji : j = i
  · subst j
    rw [freeCoordinateDerivation_freeCoordinate_self, if_pos rfl]
    simp
  · rw [freeCoordinateDerivation_freeCoordinate_of_ne hji, if_neg hji]
    simp

/-- **Literal three-coordinate logarithmic separation.**  The abstract theorem specialized to the
canonical algebraic closure of `C(x,y,z)` and its commuting coordinate derivations. -/
theorem freeCoordinate_three_logarithmicDerivative_separation
    {C : Type*} [Field C] [CharZero C]
    {A B Q : FreeCoordinateAlgebraicClosure C (Fin 3)} (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hA : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({0, 1} : Set (Fin 3)))) A)
    (hB : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({0, 2} : Set (Fin 3)))) B)
    (hQ : IsAlgebraic (IntermediateField.adjoin C
      (algebraicClosureFreeCoordinate C (Fin 3) '' ({1, 2} : Set (Fin 3)))) Q)
    (hprod : A * B = Q) :
    IsAlgebraic (IntermediateField.adjoin C
      ({algebraicClosureFreeCoordinate C (Fin 3) 0} : Set _))
        (freeCoordinateAlgebraicClosureDerivation 0 A / A) ∧
      IsAlgebraic (IntermediateField.adjoin C
        ({algebraicClosureFreeCoordinate C (Fin 3) 1} : Set _))
          (freeCoordinateAlgebraicClosureDerivation 1 A / A) := by
  exact threeCoordinate_logarithmicDerivative_separation
    (algebraicClosureFreeCoordinate C (Fin 3))
    (algebraicIndependent_algebraicClosureFreeCoordinate C (Fin 3))
    (fun i => freeCoordinateAlgebraicClosureDerivation i)
    (fun i j => freeCoordinateAlgebraicClosureDerivation_coordinate i j)
    hA0 hB0 hA hB hQ hprod

end

end GaloisForLFunctions.HTGeometry
