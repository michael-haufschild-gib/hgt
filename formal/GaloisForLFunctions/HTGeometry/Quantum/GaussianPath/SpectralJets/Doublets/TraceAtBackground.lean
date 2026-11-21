import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.RectangularBranches
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.TraceMinors

/-! # Independent longitudinal responses detected without ordering eigenvalues -/
open Matrix MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {m n D d : ℕ} {R : Type*} [CommRing R]

/-- A rectangular trace determinant in the background couplings alone. -/
def fieldTraceMinor (M : Matrix (Fin D) (Fin D) (MvPolynomial (Fin m) R))
    (u : Fin D → Fin n → R) (w : Fin d → List (Fin n)) (L : ℕ) (k : Fin d → Fin D) :=
  traceMinor M (fun i => fieldRow M u L (w i)) k

/-- A simple Hermitian specialization has independent same-order field responses exactly
when some monomial trace determinant is nonzero. The same finite family of polynomial
tests applies at all choices of background parameters. -/
theorem fieldTrace_iff (M : Matrix (Fin D) (Fin D) (MvPolynomial (Fin m) R))
    (u : Fin D → Fin n → R) (w : Fin d → List (Fin n)) (L : ℕ) (hw : ∀ i, (w i).length=L)
    (φ : R →+* ℂ) (x : Fin m → ℂ) (hH : ((eval₂Hom φ x).mapMatrix M).IsHermitian)
    (hs : ((eval₂Hom φ x).mapMatrix M).charpoly.Separable) :
    (∃ k, eval₂Hom φ x (fieldTraceMinor M u w L k) ≠ 0) ↔
      hasFieldMinor ((eval₂Hom φ x).mapMatrix M) (fun j => φ ∘ u j) w := by
  let H := (eval₂Hom φ x).mapMatrix M
  let E (j : Fin D) := (hH.eigenvalues j:ℂ)
  let p := fieldCharacteristic H (fun j => φ ∘ u j)
  let A := Matrix.of fun i j => eval (fun o : Option (Fin n) => o.elim (E j) 0) (jetRow p L (some (w i)))
  have hi : Function.Injective E := by
    rw [hH.charpoly_eq] at hs
    exact Polynomial.separable_prod_X_sub_C_iff.mp hs
  have ht (j : ℕ) : eval₂Hom φ x (M^j).trace=∑ s, E s^j := by
    rw [←trace_mapMatrix,map_pow]
    exact trace_pow_eq_sum_eigenvalues_pow hH j
  have he (k : Fin d → Fin D) : eval₂Hom φ x (fieldTraceMinor M u w L k) =
      ((A*Matrix.vandermonde E).submatrix id k).det := by
    rw [fieldTraceMinor,eval_traceMinor M _ k φ x E ht]
    simp only [eval_fieldRow]
    rfl
  simp_rw [he]
  exact (power_minor_iff A E hi).trans (cleared_minor_iff_field H hH hs (fun j => φ ∘ u j) w L hw)

#print axioms fieldTrace_iff
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
