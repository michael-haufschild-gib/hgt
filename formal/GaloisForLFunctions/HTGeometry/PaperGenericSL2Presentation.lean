import GaloisForLFunctions.HTGeometry.GenericSpecialLinearTorsor
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.FrameQuotientMap
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.DeterminantUFD

/-!
# The source determinant algebra is a polynomial extension of the native SL₂ torsor

An explicit presentation equivalence identifies the source's five generators
with the four entries of the native generic determinant-one matrix and an
independent polynomial variable. This transfers the proved domain and unique
factorization results to an existing differential-Galois coordinate algebra.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

/-- The native generic determinant-one matrix as a source frame. -/
def paperGenericSL2Frame : FrameLift.Frame (genericSL ℂ 2) where
  a := torsorMatrix ℂ 2 0 0
  d := torsorMatrix ℂ 2 1 0
  b := torsorMatrix ℂ 2 0 1
  c := torsorMatrix ℂ 2 1 1
  determinant := by simpa [Matrix.det_fin_two] using (det_torsorMatrix (I := ℂ) (N := 2))

/-- Map the source determinant ring to a polynomial extension of the native torsor. -/
def paperDeterminantToSL2Polynomial : Obstruction.C ℂ →ₐ[ℂ] Polynomial (genericSL ℂ 2) :=
  (paperGenericSL2Frame.map Polynomial.C).quotientMap Polynomial.X

/-- The source determinant coordinates arranged as the native generic matrix. -/
def paperSL2SourceMatrix : Matrix (Fin 2) (Fin 2) (Obstruction.C ℂ) :=
  !![Obstruction.cX ℂ 0, Obstruction.cX ℂ 2;
    Obstruction.cX ℂ 1, Obstruction.cX ℂ 3]

private def nativePolynomialMap :
    MvPolynomial (Fin 2 × Fin 2) ℂ →ₐ[ℂ] Obstruction.C ℂ :=
  MvPolynomial.aeval (fun ij => paperSL2SourceMatrix ij.1 ij.2)

private theorem nativePolynomialMap_relation :
    nativePolynomialMap ((fundamentalMatrix ℂ 2).det - 1) = 0 := by
  simpa [nativePolynomialMap, fundamentalMatrix, Matrix.det_fin_two, paperSL2SourceMatrix] using
    Obstruction.c_relation ℂ

/-- The four native matrix coordinates map back to the source determinant coordinates. -/
def paperSL2ToDeterminant : genericSL ℂ 2 →ₐ[ℂ] Obstruction.C ℂ :=
  Ideal.Quotient.liftₐ (slRelation ℂ 2) nativePolynomialMap (by
    have h : slRelation ℂ 2 ≤ RingHom.ker nativePolynomialMap.toRingHom := by
      rw [slRelation, Ideal.span_singleton_le_iff_mem]
      exact nativePolynomialMap_relation
    exact fun _ hp => h hp)

@[simp] theorem paperSL2ToDeterminant_matrix (i j : Fin 2) :
    paperSL2ToDeterminant (torsorMatrix ℂ 2 i j) = paperSL2SourceMatrix i j := by
  change nativePolynomialMap (MvPolynomial.X (i, j)) = _
  simp [nativePolynomialMap]

/-- Extend the inverse map by sending the independent variable to the source's fifth coordinate. -/
def paperSL2PolynomialToDeterminant : Polynomial (genericSL ℂ 2) →ₐ[ℂ] Obstruction.C ℂ :=
  Polynomial.eval₂AlgHom paperSL2ToDeterminant (Obstruction.cX ℂ 4) (fun _ => Commute.all _ _)

@[simp] theorem paperSL2PolynomialToDeterminant_C (q : genericSL ℂ 2) :
    paperSL2PolynomialToDeterminant (Polynomial.C q) = paperSL2ToDeterminant q := by
  simp [paperSL2PolynomialToDeterminant, Polynomial.eval₂AlgHom_apply]

@[simp] theorem paperSL2PolynomialToDeterminant_X :
    paperSL2PolynomialToDeterminant Polynomial.X = Obstruction.cX ℂ 4 := by
  simp [paperSL2PolynomialToDeterminant, Polynomial.eval₂AlgHom_apply]

theorem paperSL2PolynomialToDeterminant_comp :
    paperSL2PolynomialToDeterminant.comp paperDeterminantToSL2Polynomial =
      AlgHom.id ℂ (Obstruction.C ℂ) := by
  apply FrameLift.determinant_algHom_ext
  intro i
  fin_cases i <;>
    simp [paperDeterminantToSL2Polynomial, paperGenericSL2Frame, FrameLift.Frame.map,
      paperSL2SourceMatrix]

private theorem forward_on_native_matrix (i j : Fin 2) :
    paperDeterminantToSL2Polynomial (paperSL2SourceMatrix i j) =
      Polynomial.C (torsorMatrix ℂ 2 i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [paperDeterminantToSL2Polynomial, paperGenericSL2Frame, FrameLift.Frame.map,
      paperSL2SourceMatrix]

theorem paperDeterminantToSL2Polynomial_comp :
    paperDeterminantToSL2Polynomial.comp paperSL2PolynomialToDeterminant =
      AlgHom.id ℂ (Polynomial (genericSL ℂ 2)) := by
  apply Polynomial.algHom_ext'
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    change paperDeterminantToSL2Polynomial
      (paperSL2PolynomialToDeterminant (Polynomial.C (torsorMatrix ℂ 2 i j))) =
        Polynomial.C (torsorMatrix ℂ 2 i j)
    rw [paperSL2PolynomialToDeterminant_C, paperSL2ToDeterminant_matrix,
      forward_on_native_matrix]
  · simp [paperDeterminantToSL2Polynomial, paperGenericSL2Frame, FrameLift.Frame.map]

/-- Exact equivalence with the native generic SL₂ coordinate algebra plus one free variable. -/
def paperGenericSL2PolynomialEquiv :
    Obstruction.C ℂ ≃ₐ[ℂ] Polynomial (genericSL ℂ 2) :=
  AlgEquiv.ofAlgHom paperDeterminantToSL2Polynomial paperSL2PolynomialToDeterminant
    paperDeterminantToSL2Polynomial_comp paperSL2PolynomialToDeterminant_comp

/-- The native polynomial extension is a domain, by the proved source determinant theorem. -/
instance paperGenericSL2PolynomialDomain : IsDomain (Polynomial (genericSL ℂ 2)) :=
  Function.Injective.isDomain paperGenericSL2PolynomialEquiv.symm.toRingHom
    paperGenericSL2PolynomialEquiv.symm.injective

/-- The original native generic SL₂ torsor ring is a domain. -/
instance paperGenericSL2Domain : IsDomain (genericSL ℂ 2) :=
  Function.Injective.isDomain Polynomial.C Polynomial.C_injective

/-- Unique factorization transfers across the actual presentation equivalence. -/
instance paperGenericSL2PolynomialUFD : UniqueFactorizationMonoid (Polynomial (genericSL ℂ 2)) :=
  paperGenericSL2PolynomialEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance

end

end GaloisForLFunctions.HTGeometry
