import GaloisForLFunctions.HTGeometry.AlgebraicDerivationMapUniqueness
import GaloisForLFunctions.HTGeometry.DerivationPrescription

/-!
# Transport of a logarithmic coordinate derivation

On a field algebraic over two independent coordinates, prescribe the logarithmic derivative in
the first coordinate and zero derivative in the second.  If a target derivation has those same
two values under an embedding, algebraic uniqueness forces exact intertwining on the complete
source field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A logarithmic coordinate derivation on an algebraic two-coordinate field is uniquely
transported by generator agreement. -/
theorem exists_logCoordinateDerivation_intertwining_of_isAlgebraic_adjoin
    {C A L : Type*} [Field C] [CharZero C] [Field A] [CharZero A]
    [Field L] [Algebra C A] [Algebra C L]
    (x : Fin 2 → A) (hx : AlgebraicIndependent C x)
    [Algebra.IsAlgebraic (IntermediateField.adjoin C (Set.range x)) A]
    (rho : A →ₐ[C] L) (DL : Derivation C L L) (c : C)
    (hzero : DL (rho (x 0)) = rho (algebraMap C A c * x 0))
    (hone : DL (rho (x 1)) = 0) :
    ∃ D : Derivation C A A,
      D (x 0) = algebraMap C A c * x 0 ∧
      D (x 1) = 0 ∧
      ∀ y : A, rho (D y) = DL (rho y) := by
  obtain ⟨P, hP⟩ := exists_derivation_prescribed hx
    (fun i : Fin 2 => if i = 0 then 1 else 0)
  let D : Derivation C A A := (algebraMap C A c * x 0) • P
  have hDzero : D (x 0) = algebraMap C A c * x 0 := by
    simp [D, hP]
  have hDone : D (x 1) = 0 := by
    simp [D, hP, show (1 : Fin 2) ≠ 0 by decide]
  refine ⟨D, hDzero, hDone, ?_⟩
  apply derivation_map_eq_of_isAlgebraic_adjoin x rho D DL
  intro i
  by_cases hi : i = 0
  · subst i
    rw [hDzero]
    exact hzero.symm
  · have hi1 : i = 1 := by
      apply Fin.ext
      have hil := i.isLt
      omega
    subst i
    rw [hDone, map_zero]
    exact hone.symm

/-- Tower form: prescribe the logarithmic coordinate derivation on a two-generator base field,
extend it across an algebraic field, and transport it uniquely through a target embedding. -/
theorem exists_logCoordinateDerivation_intertwining_of_isAlgebraic_tower
    {C F A L : Type*} [Field C] [CharZero C] [Field F] [CharZero F]
    [Field A] [CharZero A] [Field L]
    [Algebra C F] [Algebra F A] [Algebra C A] [IsScalarTower C F A]
    [Algebra C L] [Algebra.IsAlgebraic F A]
    (x : Fin 2 → F) (hx : AlgebraicIndependent C x)
    (hxTop : IntermediateField.adjoin C (Set.range x) = ⊤)
    (rho : A →ₐ[C] L) (DL : Derivation C L L) (c : C)
    (hzero : DL (rho (algebraMap F A (x 0))) =
      rho (algebraMap C A c * algebraMap F A (x 0)))
    (hone : DL (rho (algebraMap F A (x 1))) = 0) :
    ∃ D : Derivation C A A,
      D (algebraMap F A (x 0)) =
        algebraMap C A c * algebraMap F A (x 0) ∧
      D (algebraMap F A (x 1)) = 0 ∧
      ∀ y : A, rho (D y) = DL (rho y) := by
  obtain ⟨P, hP⟩ := exists_derivation_prescribed hx
    (fun i : Fin 2 => if i = 0 then 1 else 0)
  let D₀ : Derivation C F F := (algebraMap C F c * x 0) • P
  have hD₀zero : D₀ (x 0) = algebraMap C F c * x 0 := by
    simp [D₀, hP]
  have hD₀one : D₀ (x 1) = 0 := by
    simp [D₀, hP, show (1 : Fin 2) ≠ 0 by decide]
  letI : Algebra.IsIntegral F A := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable F A := by infer_instance
  obtain ⟨D, hD⟩ := exists_derivation_extension (K := C) (F := F) (L := A) D₀
  have hDzero : D (algebraMap F A (x 0)) =
      algebraMap C A c * algebraMap F A (x 0) := by
    rw [hD, hD₀zero, map_mul]
    congr 1
    exact (IsScalarTower.algebraMap_apply C F A c).symm
  have hDone : D (algebraMap F A (x 1)) = 0 := by
    rw [hD, hD₀one, map_zero]
  refine ⟨D, hDzero, hDone, ?_⟩
  apply derivation_map_eq_of_isAlgebraic_tower_adjoin x hxTop rho D DL
  intro i
  by_cases hi : i = 0
  · subst i
    rw [hDzero]
    exact hzero.symm
  · have hi1 : i = 1 := by
      apply Fin.ext
      have hil := i.isLt
      omega
    subst i
    rw [hDone, map_zero]
    exact hone.symm

/-- Coefficient-field form of the tower transport: logarithmic scaling may be any element of the
two-coordinate base field, not only a scalar constant. -/
theorem exists_logCoordinateDerivation_intertwining_of_isAlgebraic_tower_coefficient
    {C F A L : Type*} [Field C] [CharZero C] [Field F] [CharZero F]
    [Field A] [CharZero A] [Field L]
    [Algebra C F] [Algebra F A] [Algebra C A] [IsScalarTower C F A]
    [Algebra C L] [Algebra.IsAlgebraic F A]
    (x : Fin 2 → F) (hx : AlgebraicIndependent C x)
    (hxTop : IntermediateField.adjoin C (Set.range x) = ⊤)
    (rho : A →ₐ[C] L) (DL : Derivation C L L) (c : F)
    (hzero : DL (rho (algebraMap F A (x 0))) =
      rho (algebraMap F A c * algebraMap F A (x 0)))
    (hone : DL (rho (algebraMap F A (x 1))) = 0) :
    ∃ D : Derivation C A A,
      D (algebraMap F A (x 0)) =
        algebraMap F A c * algebraMap F A (x 0) ∧
      D (algebraMap F A (x 1)) = 0 ∧
      ∀ y : A, rho (D y) = DL (rho y) := by
  obtain ⟨P, hP⟩ := exists_derivation_prescribed hx
    (fun i : Fin 2 => if i = 0 then 1 else 0)
  let D₀ : Derivation C F F := (c * x 0) • P
  have hD₀zero : D₀ (x 0) = c * x 0 := by
    simp [D₀, hP]
  have hD₀one : D₀ (x 1) = 0 := by
    simp [D₀, hP, show (1 : Fin 2) ≠ 0 by decide]
  letI : Algebra.IsIntegral F A := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable F A := by infer_instance
  obtain ⟨D, hD⟩ := exists_derivation_extension (K := C) (F := F) (L := A) D₀
  have hDzero : D (algebraMap F A (x 0)) =
      algebraMap F A c * algebraMap F A (x 0) := by
    rw [hD, hD₀zero, map_mul]
  have hDone : D (algebraMap F A (x 1)) = 0 := by
    rw [hD, hD₀one, map_zero]
  refine ⟨D, hDzero, hDone, ?_⟩
  apply derivation_map_eq_of_isAlgebraic_tower_adjoin x hxTop rho D DL
  intro i
  by_cases hi : i = 0
  · subst i
    rw [hDzero]
    exact hzero.symm
  · have hi1 : i = 1 := by
      apply Fin.ext
      have hil := i.isLt
      omega
    subst i
    rw [hDone, map_zero]
    exact hone.symm

end

end GaloisForLFunctions.HTGeometry
