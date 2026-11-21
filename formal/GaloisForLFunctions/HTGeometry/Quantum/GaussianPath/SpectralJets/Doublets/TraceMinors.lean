import GaloisForLFunctions.HTGeometry.CauchyBinet
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.LinearPencil
import Mathlib.LinearAlgebra.Vandermonde

/-! # Polynomial trace detectors for rectangular spectral derivative matrices -/
open Matrix MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {ι R : Type*} [Fintype ι] [CommRing R] {D d : ℕ}

/-- Weight each row by a power of the eigenvalue before summing over the spectrum.
The resulting determinant is independent of the ordering of the levels. -/
def traceMinor (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (b : Fin d → MvPolynomial (Option ι) R) (k : Fin d → Fin D) : MvPolynomial ι R :=
  (Matrix.of fun i j => spectralSum M (b i*(X none)^(k j).val)).det

theorem traceMinor_degree [Nontrivial R] (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (b : Fin d → MvPolynomial (Option ι) R)
    (B : ℕ) (hb : ∀ i, (b i).totalDegree ≤ B) (k : Fin d → Fin D) :
    (traceMinor M b k).totalDegree ≤ d*(B+D-1) := by
  apply determinant_degree
  intro i j
  apply (spectralSum_degree M hM _).trans
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_X_pow]
  have := hb i
  have := (k j).isLt
  omega

theorem eval_traceMinor (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (b : Fin d → MvPolynomial (Option ι) R) (k : Fin d → Fin D)
    (φ : R →+* ℂ) (x : ι → ℂ) (E : Fin D → ℂ)
    (htr : ∀ j : ℕ, eval₂Hom φ x (M^j).trace = ∑ s, E s^j) :
    eval₂Hom φ x (traceMinor M b k) =
      (((Matrix.of fun i s => eval₂ φ (fun o : Option ι => o.elim (E s) x) (b i)) *
          Matrix.vandermonde E).submatrix id k).det := by
  rw [traceMinor,RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change eval₂Hom φ x (spectralSum M _) = _
  rw [eval_spectralSum M φ x E htr]
  simp only [Matrix.submatrix_apply,id_eq,Matrix.mul_apply,Matrix.vandermonde_apply,
    Matrix.of_apply,eval₂_mul,eval₂_pow,eval₂_X,Option.elim_none]

private theorem minor_of_product (A : Matrix (Fin d) (Fin D) ℂ) (B : Matrix (Fin D) (Fin d) ℂ)
    (h : (A*B).det ≠ 0) : ∃ s : Fin d → Fin D, (A.submatrix id s).det≠0 := by
  by_contra! hn
  have hz := factorial_mul_det_mul A B
  simp only [hn,zero_mul,Finset.sum_const_zero] at hz
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) h hz

/-- Power traces detect exactly the maximal rectangular rank at every simple spectrum.
The inverse Vandermonde interpolates the selected columns. Cauchy–Binet extracts
a minor using monomial weights, which preserves integral coefficients. -/
theorem power_minor_iff (A : Matrix (Fin d) (Fin D) ℂ) (E : Fin D → ℂ) (hE : Function.Injective E) :
    (∃ k : Fin d → Fin D, ((A*Matrix.vandermonde E).submatrix id k).det ≠ 0) ↔
      ∃ s : Fin d → Fin D, (A.submatrix id s).det ≠ 0 := by
  let V := Matrix.vandermonde E
  have hV : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hE)
  constructor
  · rintro ⟨k,hk⟩
    exact minor_of_product A (V.submatrix id k) hk
  · rintro ⟨s,hs⟩
    apply minor_of_product (A*V) ((V⁻¹).submatrix id s)
    have he : (A*V)*V⁻¹ = A := by rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hV,Matrix.mul_one]
    change (((A*V)*V⁻¹).submatrix id s).det ≠ 0
    rwa [he]

#print axioms power_minor_iff
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
