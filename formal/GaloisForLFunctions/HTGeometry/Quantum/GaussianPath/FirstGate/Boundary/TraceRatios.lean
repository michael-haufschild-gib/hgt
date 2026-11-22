import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.TraceMinors

/-! # An integral trace determinant for pairwise distinction of root responses -/
open Matrix MvPolynomial
open GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
variable {ι R : Type*} [Fintype ι] [CommRing R] {D : ℕ}

/-- The i-th row is the i-th power of a ratio with its common denominator cleared. -/
def ratioTrace (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (b c : MvPolynomial (Option ι) R) :=
  traceMinor M (fun i : Fin D => b^i.val*c^(D-1-i.val)) id

/-- A collision between two energies forces the trace determinant to vanish,
independently of the numerator and denominator used to label their slopes. -/
theorem ratioTrace_simple (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (b c : MvPolynomial (Option ι) R) (φ : R→+*ℂ) (x : ι→ℂ) (E : Fin D→ℂ)
    (htr : ∀ j : ℕ, eval₂Hom φ x (M^j).trace=∑ s, E s^j)
    (h : eval₂Hom φ x (ratioTrace M b c)≠0) : Function.Injective E := by
  rw [ratioTrace,eval_traceMinor M _ _ φ x E htr,Matrix.submatrix_id_id,Matrix.det_mul] at h
  exact Matrix.det_vandermonde_ne_zero_iff.mp (right_ne_zero_of_mul h)

/-- The trace determinant factors into the energy Vandermonde, the response
Vandermonde and a product of nonzero denominators. -/
theorem ratioTrace_distinguishes (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (b c : MvPolynomial (Option ι) R) (φ : R→+*ℂ) (x : ι→ℂ) (E v : Fin D→ℂ)
    (hE : Function.Injective E) (htr : ∀ j : ℕ, eval₂Hom φ x (M^j).trace=∑ s, E s^j)
    (hc : ∀ j, eval₂ φ (fun o : Option ι => o.elim (E j) x) c ≠ 0)
    (hb : ∀ j, eval₂ φ (fun o : Option ι => o.elim (E j) x) b =
      v j * eval₂ φ (fun o : Option ι => o.elim (E j) x) c) :
    eval₂Hom φ x (ratioTrace M b c)≠0 ↔ Function.Injective v := by
  let t (j : Fin D) := eval₂ φ (fun o : Option ι => o.elim (E j) x) c
  have hA : (Matrix.of fun (i j : Fin D) => eval₂ φ (fun o : Option ι => o.elim (E j) x)
      (b^i.val*c^(D-1-i.val))) =
      (Matrix.vandermonde v).transpose * diagonal (fun j => (t j)^(D-1)) := by
    ext i j
    rw [Matrix.mul_diagonal,Matrix.transpose_apply,Matrix.vandermonde_apply,Matrix.of_apply]
    simp only [eval₂_mul,eval₂_pow,hb,mul_pow,t]
    rw [mul_assoc,←pow_add,show i.val+(D-1-i.val)=D-1 by have := i.isLt; omega]
  have hprod : (∏ j, (t j)^(D-1))≠0 := Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hc j))
  rw [ratioTrace,eval_traceMinor M _ _ φ x E htr,hA]
  change (((Matrix.vandermonde v).transpose*diagonal (fun j => (t j)^(D-1))) *
    Matrix.vandermonde E).det≠0 ↔ _
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal,Matrix.det_transpose]
  simp only [ne_eq,mul_eq_zero,not_or,hprod,Matrix.det_vandermonde_ne_zero_iff.mpr hE,
    not_false_eq_true,and_true]
  exact Matrix.det_vandermonde_ne_zero_iff

#print axioms ratioTrace_distinguishes
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
