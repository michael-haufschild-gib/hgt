import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.LineRoots

/-! # Polynomial pencils for varying a background or a single field -/
open Matrix MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
variable {m D : ℕ}
private abbrev Mat (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- Hold the single field fixed and vary the background coefficients. -/
def fixedFieldPencil (P : Fin m→Mat D) (Z : Mat D) (t : ℝ) :
    Matrix (Fin D) (Fin D) (MvPolynomial (Fin m) ℂ) :=
  spectralGenericMatrix P + C.mapMatrix ((t:ℂ) • Z)

theorem eval_fixedFieldPencil (P : Fin m→Mat D) (Z : Mat D) (t : ℝ) (θ : Fin m→ℝ) :
    (eval (fun i => (θ i:ℂ))).mapMatrix (fixedFieldPencil P Z t)=spectralEnsembleMatrix P θ+(t:ℂ) • Z := by
  rw [fixedFieldPencil,map_add,mapMatrix_spectralGenericMatrix]
  congr 1
  ext i j
  change eval (fun a : Fin m => (θ a:ℂ)) (C (((t:ℂ) • Z) i j))=((t:ℂ) • Z) i j
  rw [eval_C]

/-- Hold the background fixed and vary one scalar field. -/
def variableFieldPencil (H Z : Mat D) : Matrix (Fin D) (Fin D) (MvPolynomial Unit ℂ) :=
  fun i j => C (H i j)+X ()*C (Z i j)

theorem eval_variableFieldPencil (H Z : Mat D) (t : ℝ) :
    (eval (fun _ : Unit => (t:ℂ))).mapMatrix (variableFieldPencil H Z)=H+(t:ℂ) • Z := by
  ext i j
  change eval (fun _ : Unit => (t:ℂ)) (C (H i j)+X ()*C (Z i j))=H i j+(t:ℂ)*Z i j
  simp only [map_add,map_mul,eval_C,eval_X]

/-- Evaluating the trace of a pencil power computes the power trace of
the evaluated matrix. -/
theorem eval_trace_of_map {ι : Type*} (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι→ℂ) {H : Mat D} (h : (eval x).mapMatrix M=H) (k : ℕ) :
    eval x (M^k).trace=(H^k).trace := by rw [←trace_mapMatrix,map_pow,h]

end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
