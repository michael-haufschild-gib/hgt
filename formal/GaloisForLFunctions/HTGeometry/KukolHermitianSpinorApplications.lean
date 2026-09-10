import GaloisForLFunctions.HTGeometry.KukolUnipotentLorentz
import GaloisForLFunctions.HTGeometry.HiggsSpinorNullCone
import GaloisForLFunctions.HTGeometry.UnipotentParameterSubgroup

/-!
# Unipotent tube geometry in Hermitian and spinor coordinates

The Lorentz action used by Kukol, arXiv:2609.10214, is implemented by the
corpus's upper-unipotent matrices acting by Hermitian congruence. Its quadratic
is exactly the existing Hermitian determinant. The same identification places
Higgs spinor event matrices on the null cone and gives their exact stabilizer:
a nontrivial shear fixes a spinor event precisely when its first component vanishes.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped Matrix ComplexConjugate

/-- Light-cone coordinates represented by the existing Hermitian Lorentz matrix. -/
def kukolHermitian (x : KukolLightCone ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  lorentzHermitianMatrix ((x.1+x.2.1)/2) x.2.2.re x.2.2.im ((x.1-x.2.1)/2)

theorem kukolHermitian_entries (x : KukolLightCone ℂ) :
    kukolHermitian x = !![(x.1 : ℂ), x.2.2; star x.2.2, (x.2.1 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> simp [kukolHermitian, lorentzHermitianMatrix] <;> ring

theorem kukolHermitian_det (x : KukolLightCone ℂ) :
    (kukolHermitian x).det = (kukolQuadratic x : ℂ) := by
  rw [kukolHermitian_entries, Matrix.det_fin_two]
  apply Complex.ext
  · simp [kukolQuadratic, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  · simp [kukolQuadratic, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring

/-- The corpus's upper-unipotent matrices implement Kukol's action by Hermitian congruence. -/
theorem kukolHermitian_action (u : ℂ) (x : KukolLightCone ℂ) :
    kukolHermitian (kukolAction u x) =
      (unipotentUpper u)ᴴ * kukolHermitian x * unipotentUpper u := by
  simp only [kukolHermitian_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [kukolAction, unipotentUpper, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.real_smul] <;> ring

/-- Spinor event coordinates in the same light-cone carrier. -/
def kukolSpinorCoordinates (H : Fin 2 → ℂ) : KukolLightCone ℂ :=
  (Complex.normSq (H 0), Complex.normSq (H 1), H 0 * star (H 1))

theorem kukolHermitian_spinor (H : Fin 2 → ℂ) :
    kukolHermitian (kukolSpinorCoordinates H) = higgsSpinorEventMatrix H := by
  rw [kukolHermitian_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> simp [kukolSpinorCoordinates, higgsSpinorEventMatrix,
      Matrix.vecMulVec_apply, Complex.normSq_apply] <;> ring

theorem kukolSpinorCoordinates_null (H : Fin 2 → ℂ) :
    kukolQuadratic (kukolSpinorCoordinates H) = 0 := by
  have h := higgsSpinorEventMatrix_det H
  rw [← kukolHermitian_spinor, kukolHermitian_det] at h
  exact_mod_cast h

/-- Every complex spinor receives a null-preserving unipotent orbit. -/
theorem kukolAction_spinor_null (u : ℂ) (H : Fin 2 → ℂ) :
    kukolQuadratic (kukolAction u (kukolSpinorCoordinates H)) = 0 := by
  rw [kukolQuadratic_action, kukolSpinorCoordinates_null]

/-- A spinor event has a free unipotent orbit exactly when its first component is nonzero. -/
theorem kukolAction_spinor_stabilizer (u : ℂ) (H : Fin 2 → ℂ) :
    kukolAction u (kukolSpinorCoordinates H) = kukolSpinorCoordinates H ↔
      u = 0 ∨ H 0 = 0 := by
  rw [kukolAction_stabilizer_iff]
  simp only [kukolSpinorCoordinates, Complex.normSq_eq_zero]
  constructor
  · rintro (h | ⟨h,_⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h, by simp [h]⟩

end GaloisForLFunctions.HTGeometry
