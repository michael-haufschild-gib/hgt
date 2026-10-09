import GaloisForLFunctions.HTGeometry.PaperAffinePointRepresentation
import GaloisForLFunctions.HTGeometry.PaperPointFiberObstruction

/-!
# Polynomial parametrizations that cannot extend to ambient coordinates

Every exact complex fibre has polynomial coordinates in three variables, and
its inverse coordinates are restrictions of four-variable polynomials. The
actual algebra equivalence supplies both directions. Nevertheless, no ambient
polynomial coordinate system sends this embedded point set to a hyperplane.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate MvPolynomial

noncomputable section

/-- Ordinary complex points satisfying the exact fibre equation. -/
abbrev PaperFiberPoints (t : ℂ) := {x : Fin 4 → ℂ // x ∈ paperPointFiber t}

/-- The source's proved fibre algebra equivalence gives actual three-variable point coordinates. -/
def paperFiberPointEquiv (t : ℂ) : PaperFiberPoints t ≃ (Fin 3 → ℂ) :=
  (show PaperFiberPoints t ≃ AffineVarietyPoint (fiberIdeal t) from
    { toFun := fun x => ⟨x.val, by rw [paperPointFiber_zeroLocus]; exact x.property⟩
      invFun := fun x => ⟨x.val, by rw [← paperPointFiber_zeroLocus]; exact x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    (paperAffinePointPolynomialEquiv (fiberIdeal t) (exactFiberEquiv t))

/-- Polynomial coordinates of the actual parametrization into the ambient four-space. -/
def paperFiberParametrizationCoordinate (t : ℂ) (i : Fin 4) : R 3 :=
  exactFiberEquiv t (Ideal.Quotient.mk (fiberIdeal t) (X i))

/-- The parametrization of every complex fibre is polynomial in three free parameters. -/
theorem paperFiberPointEquiv_symm_polynomial (t : ℂ) (y : Fin 3 → ℂ) (i : Fin 4) :
    ((paperFiberPointEquiv t).symm y).val i = aeval y (paperFiberParametrizationCoordinate t i) := rfl

/-- A polynomial representative of each inverse coordinate, supplied by quotient surjectivity. -/
def paperFiberPointInverseCoordinate (t : ℂ) (i : Fin 3) : R 4 :=
  (Ideal.Quotient.mkₐ_surjective ℂ (fiberIdeal t) ((exactFiberEquiv t).symm (X i))).choose

/-- The chosen inverse polynomial represents the exact inverse algebra coordinate. -/
theorem paperFiberPointInverseCoordinate_mk (t : ℂ) (i : Fin 3) :
    Ideal.Quotient.mk (fiberIdeal t) (paperFiberPointInverseCoordinate t i) =
      (exactFiberEquiv t).symm (X i) :=
  (Ideal.Quotient.mkₐ_surjective ℂ (fiberIdeal t) ((exactFiberEquiv t).symm (X i))).choose_spec

/-- Inverse point coordinates are restrictions of ambient polynomials. -/
theorem paperFiberPointEquiv_polynomial (t : ℂ) (x : PaperFiberPoints t) (i : Fin 3) :
    paperFiberPointEquiv t x i = aeval x.val (paperFiberPointInverseCoordinate t i) := by
  let xp : AffineVarietyPoint (fiberIdeal t) :=
    ⟨x.val, by rw [paperPointFiber_zeroLocus]; exact x.property⟩
  change affineVarietyPointEvaluation (fiberIdeal t) xp ((exactFiberEquiv t).symm (X i)) = _
  rw [← paperFiberPointInverseCoordinate_mk]
  exact affineVarietyPointEvaluation_mk _ _ _

/-- Polynomial intrinsic coordinates exist at every level, but cannot straighten its embedding. -/
theorem paperFiber_polynomial_coordinates_without_ambient_rectification (t : ℂ) :
    (∃ e : PaperFiberPoints t ≃ (Fin 3 → ℂ),
      (∀ i : Fin 4, ∃ p : R 3, ∀ y : Fin 3 → ℂ, (e.symm y).val i = aeval y p) ∧
      (∀ i : Fin 3, ∃ p : R 4, ∀ x : PaperFiberPoints t, e x i = aeval x.val p)) ∧
    ¬ ∃ e : AmbientMaps.PolynomialEquiv ℂ (Fin 4) (Fin 4),
      e.toPointMap '' paperPointFiber t = paperPointHyperplane := by
  refine ⟨⟨paperFiberPointEquiv t, ?_, ?_⟩, paperPointFiber_no_polynomial_coordinates t⟩
  · intro i
    exact ⟨paperFiberParametrizationCoordinate t i, fun y => paperFiberPointEquiv_symm_polynomial t y i⟩
  · intro i
    exact ⟨paperFiberPointInverseCoordinate t i, fun x => paperFiberPointEquiv_polynomial t x i⟩

end

end GaloisForLFunctions.HTGeometry
