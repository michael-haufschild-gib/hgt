import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DistinctSubsets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Laboratory
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.Timeline
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.BondTies

/-! # Exterior characters on the original physical excursion -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
open AngularWindings.PhysicalTubes PrecisionReturns PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The unshifted phases are read in the Hamiltonian's own eigenbasis.
The modulus removes the optimizing scalar at every exterior degree. -/
theorem laboratory_fit (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) {e t : ℝ}
    (hfit : t∈laboratoryDates H W e) (hc : 0≤1-e^2/2) (q : ℕ) (hq : q≤Fintype.card I) :
    let V := H.2.isHermitian.eigenvectorUnitary
    let p (i : I) := Complex.exp (((-t*H.2.isHermitian.eigenvalues i:ℝ):ℂ)*Complex.I)
    ((Fintype.card I).choose q:ℝ)*(1-e^2/2)^min q (Fintype.card I-q)
      ≤ ‖subsetCharacter (star (V⁻¹*W*V).val) p q‖ := by
  intro V p
  rw [laboratoryDates_eq] at hfit
  obtain ⟨g,hg⟩ := hfit
  let A (i : I) := -H.2.isHermitian.eigenvalues i/(2*π)
  let θ (i : I) := 2*π*(t*A i-g)
  let f (i : I) := Complex.exp ((θ i:ℂ)*Complex.I)
  let z := Complex.exp (((-(2*π*g):ℝ):ℂ)*Complex.I)
  have hz : ‖z‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hθ (i : I) : θ i= -(2*π*g)+(-t*H.2.isHermitian.eigenvalues i) := by
    dsimp only [θ,A]
    field_simp [pi_ne_zero]
    ring
  have hsplit : f=fun i => z*p i := by
    funext i
    simp only [f,z,p,hθ,Complex.ofReal_add,add_mul,Complex.exp_add]
  have h := diagonal_fit (V⁻¹*W*V) (anglePacket θ) f rfl hc hg q hq
  simpa only [hsplit,subsetCharacter_smul,norm_mul,norm_pow,hz,one_pow,one_mul] using h

/-- From the original robust crossing, every circuit realizing the first
affordable date passes all exterior tests with its own principal minors. -/
theorem first_return_characters (k : ℕ) (ω : PathPauliDisorder) :
    let K := k+3
    let H := generator (pathPauliDisorderShell ω (k+1))
    let σ := Iterated.crossing H (nearHilbertContinuousCircuitBudget K) 0
    let V := H.2.isHermitian.eigenvectorUnitary
    ∀ s : ℕ, let v := firstVisit H σ s (1/10)
      let p (i) := Complex.exp (((-v*H.2.isHermitian.eigenvalues i:ℝ):ℂ)*Complex.I)
      (∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧ v∈laboratoryDates H C.eval (1/10)) ∧
        ∀ C : TwoQubitCircuit K, v∈laboratoryDates H C.eval (1/10) → ∀ q : ℕ, q ≤ 2^K →
          ((2^K).choose q:ℝ)*(199/200)^min q (2^K-q)
            ≤ ‖subsetCharacter (star (V⁻¹*C.eval*V).val) p q‖ := by
  intro K H σ V s v p
  constructor
  · obtain ⟨_,z,hz,C,hC,hfit⟩ := (firstVisit_isLeast H σ s (by norm_num : (0:ℝ)<1/10)).1
    exact ⟨C,hC,z,hz,hfit⟩
  intro C hf q hq
  have hd : Fintype.card (Fin K → Bool)=2^K := by simp
  have h := laboratory_fit (I:=Fin K → Bool) H C.eval hf (by norm_num) q (hd ▸ hq)
  norm_num only [hd,show (1:ℝ)-(1/10)^2/2=199/200 by norm_num] at h
  exact h

#print axioms first_return_characters
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
