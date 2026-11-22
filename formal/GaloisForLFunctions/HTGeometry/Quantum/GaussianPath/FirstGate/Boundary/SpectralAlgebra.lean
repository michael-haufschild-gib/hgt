import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.GaussianDistinction
import Mathlib.LinearAlgebra.Lagrange

/-! # Spectral functions of the dephased first-site Z -/
open Matrix Polynomial MeasureTheory
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Express the specified list of energy-basis diagonal entries in the
physical register basis. -/
def spectralFunction (V : unitary (Mat I)) (f : I→ℂ) : Mat I :=
  Unitary.conjStarAlgAut ℂ _ V (diagonal f)

/-- Polynomial evaluation commutes with the diagonal embedding and with
conjugation back to the physical register. -/
theorem spectral_aeval (V : unitary (Mat I)) (z : I→ℂ) (Q : Polynomial ℂ) :
    aeval (spectralFunction V z) Q=spectralFunction V (fun j => Q.eval (z j)) := by
  unfold spectralFunction
  rw [aeval_algHom_apply]
  apply congrArg (Unitary.conjStarAlgAut ℂ _ V)
  let δ := Matrix.diagonalAlgHom (n := I) (α := ℂ) (R := ℂ)
  change aeval (δ z) Q=_
  rw [aeval_algHom_apply,Polynomial.aeval_pi_apply]
  rfl

/-- The energy-diagonal entries of Z on the first spin. -/
def firstZProfile {n : ℕ} (p : PathShell n) (j : Fin (n+2)→Bool) : ℂ :=
  let V : Mat (Fin (n+2)→Bool) := (isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvectorUnitary
  let Z : Mat (Fin (n+2)→Bool) := finitePauliMatrix (pauliZLabel (0:Fin (n+2)))
  (star V*Z*V) j j

/-- Interpolation identifies energy-basis diagonal operators with polynomials
of degree less than the number of energies in any separating diagonal. -/
theorem spectral_interpolation (V : unitary (Mat I)) (z f : I→ℂ) (hz : Function.Injective z) :
    ∃! P : Polynomial ℂ, P.degree < (Fintype.card I:ℕ) ∧
      aeval (spectralFunction V z) P=spectralFunction V f := by
  classical
  let p := Lagrange.interpolate Finset.univ z f
  have hnodes : Set.InjOn z (↑(Finset.univ : Finset I)) := hz.injOn
  have he (P : Polynomial ℂ) :
      aeval (spectralFunction V z) P=spectralFunction V f ↔ ∀ j, P.eval (z j)=f j := by
    rw [spectral_aeval]
    unfold spectralFunction
    constructor
    · intro h j
      have hd : diagonal (fun i => P.eval (z i))=diagonal f := (Unitary.conjStarAlgAut ℂ _ V).injective h
      simpa only [diagonal_apply_eq] using congrArg (fun A : Mat I => A j j) hd
    · intro h
      rw [show (fun j => P.eval (z j))=f from funext h]
  refine ⟨p,⟨by simpa only [Finset.card_univ] using Lagrange.degree_interpolate_lt f hnodes,
    (he p).mpr (fun j => Lagrange.eval_interpolate_at_node f hnodes (Finset.mem_univ j))⟩,?_⟩
  intro P hp
  exact (Lagrange.eq_interpolate_iff f hnodes).mp ⟨by simpa only [Finset.card_univ] using hp.1,
    fun j _ => (he P).mp hp.2 j⟩

/-- On each Gaussian prefix every prescribed complex spectral profile is a
unique polynomial of degree below 2ᴺ in the dephased first-site Z. -/
theorem gaussian_firstZ_spectral_algebra : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n : ℕ,
    let hH := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)).isHermitian
    let V := hH.eigenvectorUnitary
    let z := firstZProfile (pathPauliDisorderShell ω n)
    ∀ f : (Fin (n+2)→Bool) → ℂ, ∃! P : Polynomial ℂ, P.degree < (2^(n+2):ℕ) ∧
      aeval (spectralFunction V z) P=spectralFunction V f := by
  filter_upwards [gaussian_firstZ_distinguishes] with ω hω n
  intro hH V z f
  have hz : Function.Injective z := fun i j hij => hω n (congrArg Complex.re hij)
  simpa using spectral_interpolation V z f hz

#print axioms gaussian_firstZ_spectral_algebra
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
