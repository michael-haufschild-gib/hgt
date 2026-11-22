import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.FourFlows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEnergies
import GaloisForLFunctions.HTGeometry.FinitePauliConjugationLaw
import GaloisForLFunctions.HTGeometry.NearestNeighborPathSpectrumRealRelationEscape

/-! # Conjugating the physical coefficient vector by local X flips -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section

def mask {N : ℕ} (S : Finset (Fin N)) (i : Fin N) : Option (Fin 3) := if i ∈ S then some 0 else none
def flip {N : ℕ} (S : Finset (Fin N)) : Register N := finitePauliMatrix (mask S)

theorem flip_supported {N : ℕ} (S : Finset (Fin N)) : IsSiteSupported S (flip S) :=
  finitePauliMatrix_isSiteSupported_of_eq_none S (mask S) (fun i hi => if_neg hi)

def axisSign {N : ℕ} (S : Finset (Fin N)) (i : Fin N) (a : Fin 3) : ℝ :=
  if i ∈ S ∧ a ≠ 0 then -1 else 1

/-- Signs multiply across the occupied sites of a Pauli word. -/
def wordSign {n : ℕ} (S : Finset (Fin (n+2))) : PathLabel n → ℝ
  | .inl (i,a) => axisSign S i a
  | .inr (e,a,b) => axisSign S e.castSucc a*axisSign S e.succ b

theorem wordSign_abs {n : ℕ} (S : Finset (Fin (n+2))) (l : PathLabel n) : |wordSign S l|=1 := by
  have h (i a) : |axisSign S i a|=1 := by unfold axisSign; split <;> norm_num
  rcases l with ⟨i,a⟩|⟨e,a,b⟩
  · exact h i a
  · simp only [wordSign,abs_mul,h,mul_one]

private theorem local_sign {N : ℕ} (S : Finset (Fin N)) (i : Fin N) (a : Fin 3) :
    boolPauliConjugationSign (mask S i) (some a)=(axisSign S i a:ℂ) := by
  by_cases hi : i ∈ S <;> by_cases ha : a=0 <;> simp [boolPauliConjugationSign,mask,axisSign,hi,ha,eq_comm]

private theorem word_sign {n : ℕ} (S : Finset (Fin (n+2))) (l : PathLabel n) :
    finitePauliConjugationSign (mask S) (pathWord l)=(wordSign S l:ℂ) := by
  classical
  rcases l with ⟨i,a⟩|⟨e,a,b⟩
  · rw [finitePauliConjugationSign,Finset.prod_eq_single i]
    · simpa only [pathWord,onsiteWord,if_pos rfl,wordSign] using local_sign S i a
    · intro j _ hj; simp [pathWord,onsiteWord,hj,boolPauliConjugationSign]
    · simp
  · have hne : e.castSucc ≠ e.succ := fun h => by have := congrArg Fin.val h; simp at this
    have h (i) : boolPauliConjugationSign (mask S i) (pathWord (.inr (e,a,b)) i)=
        (if i=e.castSucc then (axisSign S i a:ℂ) else 1)*(if i=e.succ then (axisSign S i b:ℂ) else 1) := by
      by_cases hl : i=e.castSucc
      · subst i; simp [pathWord,couplingWord,hne,local_sign]
      · by_cases hr : i=e.succ
        · subst i; simp [pathWord,couplingWord,hne.symm,local_sign]
        · simp [pathWord,couplingWord,hl,hr,boolPauliConjugationSign]
    rw [finitePauliConjugationSign]
    simp only [h,Finset.prod_mul_distrib,wordSign,Complex.ofReal_mul]
    simp

def signedShell {n : ℕ} (S : Finset (Fin (n+2))) (u : PathShell n) : PathShell n :=
  WithLp.toLp 2 fun l => wordSign S l*u l

theorem conjugate_hamiltonian {n : ℕ} (S : Finset (Fin (n+2))) (u : PathShell n) :
    flip S*pathHamiltonian u*flip S=pathHamiltonian (signedShell S u) := by
  rw [pathHamiltonian_eq_sum,pathHamiltonian_eq_sum,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  have he := finitePauliMatrix_conj (mask S) (pathWord l)
  rw [word_sign] at he
  simp only [flip,Matrix.mul_smul,Matrix.smul_mul,he,smul_smul]
  change _=(((wordSign S l*u l:ℝ):ℂ)) • _
  rw [Complex.ofReal_mul,mul_comm (u l:ℂ)]

/-- Only terms odd under both independent spin flips survive the echo. -/
def mixedShell {n : ℕ} (S T : Finset (Fin (n+2))) (u : PathShell n) : PathShell n :=
  WithLp.toLp 2 fun l => (1-wordSign S l)*(1-wordSign T l)*u l

theorem mixed_hamiltonian {n : ℕ} (S T : Finset (Fin (n+2))) (u : PathShell n) :
    pathHamiltonian u-pathHamiltonian (signedShell S u)+pathHamiltonian (signedShell S (signedShell T u))-
      pathHamiltonian (signedShell T u)=pathHamiltonian (mixedShell S T u) := by
  simp only [pathHamiltonian_eq_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  change (u l:ℂ) • _-((wordSign S l*u l:ℝ):ℂ) • _+((wordSign S l*(wordSign T l*u l):ℝ):ℂ) • _-
    ((wordSign T l*u l:ℝ):ℂ) • _=(((1-wordSign S l)*(1-wordSign T l)*u l:ℝ):ℂ) • _
  rw [←sub_smul,←add_smul,←sub_smul]
  congr 1
  push_cast
  ring

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
