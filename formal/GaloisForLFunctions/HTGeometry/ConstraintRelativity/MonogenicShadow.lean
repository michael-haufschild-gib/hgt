import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.MonogenicKaehler

/-!
# The monogenic law-discriminant observer shadow

For a monic `f ∈ B[T]` and `A = B[T]/(f)` the relative differentials have the two-term conormal
presentation

`A →^{f'(t)} A → Ω[A⁄B] → 0`,

so `Ω[A⁄B] ≅ A/(f'(t))`, the first homology of the conormal complex is the annihilator of `f'(t)`,
and the determinant of the presentation is the norm `N_{A/B}(f'(t))`, which for a separable power
basis is the discriminant up to sign.

On a split fibre the character observer is the Vandermonde matrix of the roots, so its determinant
is the oriented root product `Δ_f = ∏_{i<j}(r_j − r_i)`, whose square is the discriminant and whose
vanishing locus is exactly the ramification locus.  Orientation, positive magnitude and support are
again the three successive shadows `Δ ↦ |Δ|² ↦ [Δ = 0]`.
-/

namespace HTGeometry.ConstraintRelativity

open Polynomial Matrix

/-! ## The conormal presentation -/

section Conormal

variable {B : Type*} [CommRing B] (f : B[X])

/-- The image of multiplication by the different is the different ideal. -/
theorem range_mulLeft_rootDifferent :
    LinearMap.range (LinearMap.mulLeft (AdjoinRoot f) (rootDifferent f))
      = (Ideal.span {rootDifferent f} : Ideal (AdjoinRoot f)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact Ideal.mem_span_singleton'.2 ⟨x, by rw [LinearMap.mulLeft_apply]; ring⟩
  · rw [Ideal.span_le]
    rintro _ rfl
    exact ⟨1, by rw [LinearMap.mulLeft_apply, mul_one]⟩

/-- **The conormal presentation.**  The cokernel of multiplication by `f'(t)` is the module of
relative differentials. -/
noncomputable def conormalCokerEquiv :
    (AdjoinRoot f ⧸ LinearMap.range (LinearMap.mulLeft (AdjoinRoot f) (rootDifferent f)))
      ≃ₗ[AdjoinRoot f] Ω[AdjoinRoot f⁄B] :=
  (Submodule.quotEquivOfEq _ _ (range_mulLeft_rootDifferent f)).trans
    (kaehlerEquivMonogenic f).symm

/-- **The first conormal homology.**  The kernel of the presentation map is the annihilator of the
different. -/
theorem mem_ker_mulLeft_rootDifferent (x : AdjoinRoot f) :
    x ∈ LinearMap.ker (LinearMap.mulLeft (AdjoinRoot f) (rootDifferent f))
      ↔ rootDifferent f * x = 0 := Iff.rfl

/-- The determinant of the presentation is the norm of the different. -/
theorem norm_rootDifferent_eq_det [Module.Free B (AdjoinRoot f)]
    [Module.Finite B (AdjoinRoot f)] :
    Algebra.norm B (rootDifferent f)
      = LinearMap.det (Algebra.lmul B (AdjoinRoot f) (rootDifferent f)) := rfl

end Conormal

/-! ## The discriminant of a separable power basis -/

section Discriminant

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (pb : PowerBasis K L)

/-- **Card `(6)`.**  The discriminant of a separable power basis is, up to sign, the norm of the
different `f'(t)`.  This is the determinant of the conormal presentation of `Ω[L⁄K]`. -/
theorem discr_eq_norm_different [Algebra.IsSeparable K L] :
    Algebra.discr K pb.basis
      = (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2)
        * Algebra.norm K (aeval pb.gen (minpoly K pb.gen).derivative) := by
  haveI : Module.Finite K L := Module.Finite.of_basis pb.basis
  exact Algebra.discr_powerBasis_eq_norm K pb

end Discriminant

/-! ## The split-fibre character observer -/

section Vandermonde

variable {C : Type*} [CommRing C] {n : ℕ}

/-- The character observer of a split fibre, read in the monomial basis, is the Vandermonde
matrix of the roots. -/
theorem characterObserver_matrix (r : Fin n → C) (i j : Fin n) :
    Matrix.vandermonde r i j = r i ^ (j : ℕ) := rfl

/-- **Card `(9)`.**  The observer determinant is the oriented root product. -/
theorem det_characterObserver (r : Fin n → C) :
    (Matrix.vandermonde r).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (r j - r i) :=
  Matrix.det_vandermonde r

/-- The framed discriminant of a split fibre: the squared oriented root product. -/
def fibreDiscriminant (r : Fin n → C) : C := ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (r j - r i) ^ 2

/-- **Card `(10)`.**  The square of the observer determinant is the discriminant. -/
theorem sq_det_characterObserver (r : Fin n → C) :
    (Matrix.vandermonde r).det ^ 2 = fibreDiscriminant r := by
  rw [det_characterObserver, fibreDiscriminant, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => (Finset.prod_pow _ _ _).symm

/-- **The degeneracy locus.**  The observer is invertible exactly off the discriminant locus. -/
theorem det_characterObserver_ne_zero_iff [IsDomain C] (r : Fin n → C) :
    (Matrix.vandermonde r).det ≠ 0 ↔ Function.Injective r := by
  rw [Matrix.det_vandermonde_ne_zero_iff]

end Vandermonde

/-! ## The conditioning law and the three shadows -/

section Conditioning

variable {n : ℕ}

/-- **Card `(11)`.**  The magnitude of the observer determinant is the square root of the magnitude
of the discriminant; since the product of the singular values of a square matrix is the magnitude
of its determinant, this is the exact product-conditioning law. -/
theorem abs_det_characterObserver (r : Fin n → ℂ) :
    ‖(Matrix.vandermonde r).det‖ = Real.sqrt ‖fibreDiscriminant r‖ := by
  rw [← sq_det_characterObserver, norm_pow]
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- **Card `(13)`, first shadow.**  Positive magnitude forgets the orientation of the root
product. -/
theorem fibreOrientation_forgets (r : Fin n → ℂ) (hr : (Matrix.vandermonde r).det ≠ 0) :
    ∃ z : ℂ, z ≠ (Matrix.vandermonde r).det ∧
      ‖z‖ = ‖(Matrix.vandermonde r).det‖ := by
  refine ⟨-(Matrix.vandermonde r).det, fun h => hr ?_, by simp⟩
  linear_combination (-1 / 2 : ℂ) * h

/-- **Card `(13)`, second shadow.**  Support forgets the magnitude. -/
theorem fibreSupport_forgets : ∃ a b : ℂ, ((a = 0) ↔ (b = 0)) ∧ ‖a‖ ≠ ‖b‖ :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- **Card `(13)`, the tower.**  The support shadow factors through the magnitude shadow. -/
theorem fibreShadow_tower (r : Fin n → ℂ) :
    ((Matrix.vandermonde r).det = 0) ↔ (‖(Matrix.vandermonde r).det‖ = 0) := by
  simp

end Conditioning

end HTGeometry.ConstraintRelativity
