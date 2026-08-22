import GaloisForLFunctions.HTGeometry.AlgebraicOrbitCoordinates

/-!
# The Lagrange coefficient matrix descends to the algebraic numbers

`AlgebraicOrbitCoordinates` writes the Schrödinger orbit as a linear combination of the spectral
phases with the coefficient matrix `M i j = (ℓ_j(H) *ᵥ Ω) i`.  Here that matrix is exhibited as the
image of a matrix over any base field mapping into `ℂ` which contains the entries of `H`, the
eigenvalues and the entries of `Ω`.  For a rational Hamiltonian with an algebraic spectrum and a
rational input the base field can be taken to be the field of algebraic numbers, which is exactly
what the transcendence bound needs: the change of coordinates between computational and spectral
coordinates is algebraic.

## Main results

* `map_lagrangeBasis` — the Lagrange basis commutes with a field embedding.
* `map_aeval_matrix` — a polynomial in a matrix commutes with a ring embedding.
* `map_lagrangeStateMatrixOver` — **the coefficient matrix is defined over the base field.**
-/

open Matrix Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace AlgebraicOrbit

set_option linter.unusedSectionVars false

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Transport along a ring homomorphism -/

/-- `mulVec` commutes with a ring homomorphism. -/
theorem map_mulVec {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : Matrix α α R) (v : α → R) (i : α) :
    φ ((A *ᵥ v) i) = ((A.map φ) *ᵥ fun k => φ (v k)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => map_mul _ _ _

/-- A polynomial in a matrix commutes with a ring homomorphism. -/
theorem map_aeval_matrix {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : Matrix α α R) (p : R[X]) :
    (Polynomial.aeval A p).map φ = Polynomial.aeval (A.map φ) (p.map φ) := by
  have h1 : Polynomial.aeval A p
      = Polynomial.eval₂ (algebraMap R (Matrix α α R)) A p := rfl
  have h2 : ((φ.mapMatrix : Matrix α α R →+* Matrix α α S).comp
      (algebraMap R (Matrix α α R)))
      = (algebraMap S (Matrix α α S)).comp φ := by
    refine RingHom.ext fun a => ?_
    show ((algebraMap R (Matrix α α R) a).map φ) = algebraMap S (Matrix α α S) (φ a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  calc (Polynomial.aeval A p).map φ
      = (φ.mapMatrix : Matrix α α R →+* Matrix α α S)
          (Polynomial.eval₂ (algebraMap R (Matrix α α R)) A p) := by rw [h1]; rfl
    _ = Polynomial.eval₂ ((φ.mapMatrix : Matrix α α R →+* Matrix α α S).comp
          (algebraMap R (Matrix α α R))) (A.map φ) p := by
        rw [Polynomial.hom_eval₂]
        rfl
    _ = Polynomial.eval₂ ((algebraMap S (Matrix α α S)).comp φ) (A.map φ) p := by rw [h2]
    _ = Polynomial.aeval (A.map φ) (p.map φ) := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map]

/-- The Lagrange interpolation basis commutes with a field embedding. -/
theorem map_lagrangeBasis {F E : Type*} [Field F] [Field E] (φ : F →+* E) (s : Finset α)
    (v : α → F) (i : α) :
    (Lagrange.basis s v i).map φ = Lagrange.basis s (fun k => φ (v k)) i := by
  classical
  rw [Lagrange.basis, Lagrange.basis, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Lagrange.basisDivisor, Lagrange.basisDivisor, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_inv₀, map_sub]

/-! ### The coefficient matrix over a base field -/

variable {K : Type*} [Field K] [Algebra K ℂ]

/-- The Lagrange coefficient matrix, formed over a base field. -/
def lagrangeStateMatrixOver (HK : Matrix α α K) (lamK : α → K) (ΩK : α → K) : Matrix α α K :=
  Matrix.of fun i j =>
    ((Polynomial.aeval HK (Lagrange.basis Finset.univ lamK j)) *ᵥ ΩK) i

/-- **The coefficient matrix of the orbit is defined over the base field.** -/
theorem map_lagrangeStateMatrixOver {H : Matrix α α ℂ} {lam : α → ℝ} {Ω : α → ℂ}
    (HK : Matrix α α K) (lamK : α → K) (ΩK : α → K)
    (hH : HK.map (algebraMap K ℂ) = H)
    (hlam : ∀ i, algebraMap K ℂ (lamK i) = spectralNodes lam i)
    (hΩ : ∀ i, algebraMap K ℂ (ΩK i) = Ω i) :
    (lagrangeStateMatrixOver HK lamK ΩK).map (algebraMap K ℂ) = lagrangeStateMatrix H lam Ω := by
  classical
  ext i j
  rw [Matrix.map_apply]
  show algebraMap K ℂ (((Polynomial.aeval HK (Lagrange.basis Finset.univ lamK j)) *ᵥ ΩK) i)
      = lagrangeStateMatrix H lam Ω i j
  have hnodes : (fun k => algebraMap K ℂ (lamK k)) = spectralNodes lam := funext hlam
  have hOm : (fun k => algebraMap K ℂ (ΩK k)) = Ω := funext hΩ
  rw [map_mulVec (algebraMap K ℂ : K →+* ℂ), lagrangeStateMatrix_apply,
    map_aeval_matrix (algebraMap K ℂ : K →+* ℂ), map_lagrangeBasis, hH, hnodes, hOm]

end

end AlgebraicOrbit

end GaloisForLFunctions.HTGeometry
