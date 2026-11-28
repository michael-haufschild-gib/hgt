import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Transversals.Gaps
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.FirstReturn

/-! # Prescribed disjoint pairs at the original physical first return -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
open AngularWindings.PhysicalTubes PrecisionReturns PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Every choice of disjoint pairs gives a character on its own gap
frequencies, with fixed weights of squared sum at most one. -/
theorem paired_laboratory (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) {e v : ℝ}
    (hv : v∈laboratoryDates H W e) (hc : 0≤1-e^2/2) {q : ℕ} (f : Fin q × Bool ↪ I) :
    let V := H.2.isHermitian.eigenvectorUnitary
    let p i := Complex.exp (((-v*H.2.isHermitian.eigenvalues i:ℝ):ℂ)*Complex.I)
    (1-e^2/2)^q≤halfAmplitude^q*‖pairCharacter (V⁻¹*W*V) f p‖ ∧
      (∑ x : Fin q → Bool, ‖pairWeight (V⁻¹*W*V) f x‖^2)≤1 := by
  intro V p
  rw [laboratoryDates_eq] at hv
  obtain ⟨g,hg⟩ := hv
  let A (i : I) := -H.2.isHermitian.eigenvalues i/(2*π)
  let θ (i : I) := 2*π*(v*A i-g)
  let z := Complex.exp (((-(2*π*g):ℝ):ℂ)*Complex.I)
  have hz : ‖z‖=1 := Complex.norm_exp_ofReal_mul_I _
  have hθ (i : I) : θ i= -(2*π*g)+(-v*H.2.isHermitian.eigenvalues i) := by
    dsimp only [θ,A]
    field_simp [pi_ne_zero]
    ring
  have hp : (fun i => Complex.exp ((θ i:ℂ)*Complex.I))=fun i => z*p i := by
    funext i
    simp only [z,p,hθ,Complex.ofReal_add,add_mul,Complex.exp_add]
  have h := diagonal_transversals (V⁻¹*W*V) (anglePacket θ) _ rfl hg hc f
  simpa only [hp,common_phase,norm_mul,norm_pow,hz,one_pow,one_mul] using h

/-- A single circuit realizing the first affordable date passes the
transversal tests for every pairing, including pairings selected after
observing the spectrum and the circuit. -/
theorem first_return_transversals (k : ℕ) (ω : PathPauliDisorder) :
    let K := k+3
    let H := generator (pathPauliDisorderShell ω (k+1))
    let σ := Iterated.crossing H (nearHilbertContinuousCircuitBudget K) 0
    let V := H.2.isHermitian.eigenvectorUnitary
    ∀ s : ℕ, let v := firstVisit H σ s (1/10)
      (∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧ v∈laboratoryDates H C.eval (1/10)) ∧
        ∀ C : TwoQubitCircuit K, v∈laboratoryDates H C.eval (1/10) →
          ∀ (q : ℕ) (f : Fin q × Bool ↪ (Fin K → Bool)),
            (199/200:ℝ)^q ≤ halfAmplitude^q*
              ‖∑ x : Fin q → Bool, pairWeight (V⁻¹*C.eval*V) f x*
                Complex.exp (((-v*gapEnergy H.2.isHermitian.eigenvalues f x:ℝ):ℂ)*Complex.I)‖ ∧
              (∑ x : Fin q → Bool, ‖pairWeight (V⁻¹*C.eval*V) f x‖^2) ≤ 1 := by
  intro K H σ V s v
  refine ⟨(first_return_characters k ω s).1,?_⟩
  intro C hv q f
  have h := paired_laboratory (I:=Fin K → Bool) H C.eval hv (by norm_num) f
  dsimp only at h
  rw [pair_character_norm_gaps] at h
  simpa only [show (1:ℝ)-(1/10)^2/2=199/200 by norm_num] using h

#print axioms first_return_transversals
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.Transversals
