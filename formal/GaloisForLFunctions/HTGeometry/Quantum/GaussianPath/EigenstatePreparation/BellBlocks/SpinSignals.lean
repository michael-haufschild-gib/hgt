import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EigenstatePreparation.BellBlocks.DimerSignals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldApproximation
import GaloisForLFunctions.HTGeometry.TwoLocalPauliAnticommutingFan

/-! # Bloch coordinates in every energy eigenstate of a path Hamiltonian -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
noncomputable section
variable {n : ℕ}
private abbrev Reg (n : ℕ) := Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ

/-- The reference dimer has commuting XX and ZZ stabilizers of distinct strengths. -/
def dimerModel (u : PathShell n) (e : Fin (n+1)) : Reg n :=
  let R := pathHamiltonianOnSites ({e.castSucc,e.succ}ᶜ) u
  let X := finitePauliMatrix (couplingWord e (0,0))
  let Z := finitePauliMatrix (couplingWord e (2,2))
  R+(X+(Z+Z))

private theorem signed_mul {S : Type*} [Fintype S] [DecidableEq S]
    (P Q : S → Option (Fin 3)) :
    finitePauliMatrix P*finitePauliMatrix Q =
      finitePauliConjugationSign P Q • (finitePauliMatrix Q*finitePauliMatrix P) := by
  calc _ = (finitePauliMatrix P*finitePauliMatrix Q*finitePauliMatrix P)*finitePauliMatrix P := by
         rw [mul_assoc (finitePauliMatrix P*finitePauliMatrix Q),finitePauliMatrix_mul_self,mul_one]
       _ = _ := by rw [finitePauliMatrix_conj,Matrix.smul_mul]

/-- All three Bloch components on the first spin of the dimer are
bounded by the same measured local Hamiltonian replacement error. -/
theorem dimer_bloch_signal (u : PathShell n) (e : Fin (n+1)) (a : Fin 3) (i : Fin (n+2) → Bool) :
    let H : selfAdjoint (Reg n) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    ‖energyDiagonal H (finitePauliMatrix (onsiteWord e.castSucc a)) i‖ ≤
      ‖dimerModel u e-pathHamiltonian u‖ := by
  intro H
  let S : Finset (Fin (n+2)) := {e.castSucc,e.succ}
  let R := pathHamiltonianOnSites Sᶜ u
  let T (b : Fin 3) := finitePauliMatrix (couplingWord e (b,b))
  let C (b : Fin 3) := finitePauliMatrix (onsiteWord e.castSucc b)
  have hne : e.castSucc ≠ e.succ := by intro h; have := congrArg Fin.val h; change e.val=e.val+1 at this; omega
  have hT b : IsSiteSupported S (T b) := by
    apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro v hv
    have h : v≠e.castSucc ∧ v≠e.succ := by simpa [S] using hv
    simp [couplingWord,h.1,h.2]
  have hC b : IsSiteSupported S (C b) := by
    apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro v hv
    have h : v≠e.castSucc ∧ v≠e.succ := by simpa [S] using hv
    simp [onsiteWord,h.1]
  have hR := pathHamiltonianOnSites_isSiteSupported Sᶜ u
  have hRT b : Commute R (T b) := commute_of_isSiteSupported_disjoint disjoint_compl_left hR (hT b)
  have hRC b : Commute R (C b) := commute_of_isSiteSupported_disjoint disjoint_compl_left hR (hC b)
  have hpair (b : Fin 3) : couplingWord e (b,b)=pairLabel e.castSucc e.succ b b := rfl
  have hab : Commute (T 0) (T 2) := by
    have h := signed_mul (couplingWord e (0,0)) (couplingWord e (2,2))
    rw [hpair,finitePauliConjugationSign_pairLabel _ hne] at h
    simpa only [T,←hpair] using (by
      simpa [couplingWord,hne,Ne.symm hne,boolPauliConjugationSign] using h :
        finitePauliMatrix (pairLabel e.castSucc e.succ 0 0)*T 2=T 2*finitePauliMatrix (pairLabel e.castSucc e.succ 0 0))
  have hsame b : Commute (C b) (T b) := by
    have h := signed_mul (pairLabel e.castSucc e.succ b b) (onsiteWord e.castSucc b)
    rw [finitePauliConjugationSign_pairLabel _ hne] at h
    exact ((show Commute (T b) (C b) by
      simpa [T,C,hpair,onsiteWord,Ne.symm hne,boolPauliConjugationSign] using h)).symm
  have hanti (b c : Fin 3) (hc : b≠c) : C b*T c= -(T c*C b) := by
    have h := signed_mul (pairLabel e.castSucc e.succ c c) (onsiteWord e.castSucc b)
    rw [finitePauliConjugationSign_pairLabel _ hne] at h
    have h' : T c*C b= -(C b*T c) := by
      simpa [T,C,hpair,onsiteWord,Ne.symm hne,boolPauliConjugationSign,Ne.symm hc] using h
    rw [h',neg_neg]
  have hs b : T b*T b=1 := finitePauliMatrix_mul_self _
  have hn b : ‖T b‖≤1 := (norm_finitePauliMatrix _).le
  have hm b : ‖C b‖≤1 := (norm_finitePauliMatrix _).le
  change ‖energyDiagonal H (C a) i‖≤‖(R+(T 0+(T 2+T 2)))-H.val‖
  fin_cases a
  · exact commuting_first_signal H R (T 0) (T 2) (C 0) i hab (hRT 2) (hRC 0)
      (hsame 0) (hanti 0 2 (by decide)) (hs 2) (hn 2) (hm 0)
  · exact anticommuting_signal H R (T 0) (T 2) (C 1) i hab (hRT 0) (hRT 2) (hRC 1)
      (hanti 1 0 (by decide)) (hanti 1 2 (by decide)) (hs 0) (hs 2) (hn 0) (hn 2) (hm 1)
  · exact commuting_second_signal H R (T 0) (T 2) (C 2) i hab (hRT 0) (hRC 2)
      (hanti 2 0 (by decide)) (hsame 2) (hs 0) (hn 0) (hm 2)

#print axioms dimer_bloch_signal
end
end GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
