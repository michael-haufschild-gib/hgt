import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.Packets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliContextuality
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification

/-! # Two commuting half-chain generators meeting at a conserved spin -/
open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open WeakBonds DiagonalSynthesis
open private supported_sum supported_pauli from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.Packets
noncomputable section
variable {n : ℕ}

/-- Retain onsite terms up to the left endpoint and bonds through
the cut bond. Only its right endpoint is shared with the other half. -/
def onLeft (a : Fin (n+1)) : PathLabel n→Prop
  | .inl (i,_) => i≤a.castSucc
  | .inr (e,_) => e≤a

open scoped Classical in
/-- Remove all coefficients outside a selected set of Pauli labels. -/
def restricted (P : PathLabel n→Prop) (u : PathShell n) : PathShell n :=
  WithLp.toLp 2 fun l => if P l then u l else 0

theorem restricted_eq {P : PathLabel n→Prop} (u : PathShell n) {l : PathLabel n} (hl : P l) :
    restricted P u l=u l := if_pos hl

theorem restricted_zero {P : PathLabel n→Prop} (u : PathShell n) {l : PathLabel n} (hl : ¬P l) :
    restricted P u l=0 := if_neg hl

theorem sum_restricted (P : PathLabel n→Prop) (u : PathShell n) :
    pathHamiltonian u=pathHamiltonian (restricted P u)+pathHamiltonian (restricted (fun l => ¬P l) u) := by
  classical
  simp only [pathHamiltonian_eq_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro l _
  by_cases hl : P l <;> simp [restricted,hl]

/-- Every surviving word at the specified site is identity or Z. -/
def longitudinalAt (q : Fin (n+2)) (u : PathShell n) :=
  ∀ l, u l≠0 → pathWord l q=none ∨ pathWord l q=some 2

private theorem left_none (a : Fin (n+1)) (l : PathLabel n) (h : onLeft a l) {i : Fin (n+2)}
    (hi : a.succ < i) : pathWord l i=none := by
  rcases l with ⟨j,p⟩|⟨e,p⟩
  · change j≤a.castSucc at h
    have hne : i≠j := by intro he; subst i; exact (lt_of_lt_of_le a.castSucc_lt_succ hi.le).not_ge h
    simp [pathWord,onsiteWord,hne]
  · change e≤a at h
    have h₁ : i≠e.castSucc := by
      intro he
      subst i
      exact (Nat.not_lt_of_ge (Nat.le_succ_of_le h)) hi
    have h₂ : i≠e.succ := by
      intro he
      subst i
      exact (Nat.not_lt_of_ge (Nat.succ_le_succ h)) hi
    simp [pathWord,couplingWord,h₁,h₂]

private theorem right_none (a : Fin (n+1)) (l : PathLabel n) (h : ¬onLeft a l) {i : Fin (n+2)}
    (hi : i<a.succ) : pathWord l i=none := by
  rcases l with ⟨j,p⟩|⟨e,p⟩
  · change ¬j≤a.castSucc at h
    have hne : i≠j := by intro he; subst i; exact h (show j.val≤a.val from Nat.le_of_lt_succ hi)
    simp [pathWord,onsiteWord,hne]
  · change ¬e.val≤a.val at h
    have h₁ : i≠e.castSucc := by intro he; have hh := congrArg Fin.val he; change i.val<a.val+1 at hi; change i.val=e.val at hh; omega
    have h₂ : i≠e.succ := by intro he; have hh := congrArg Fin.val he; change i.val<a.val+1 at hi; change i.val=e.val+1 at hh; omega
    simp [pathWord,couplingWord,h₁,h₂]

private theorem restricted_supported (P : PathLabel n→Prop) (S : Finset (Fin (n+2))) (u : PathShell n)
    (hs : ∀ l, P l → ∀ i∉S, pathWord l i=none) :
    IsSiteSupported (A:=fun _ : Fin (n+2) => Bool) S (pathHamiltonian (restricted P u)) := by
  classical
  rw [pathHamiltonian_eq_sum]
  apply supported_sum
  intro l _
  change IsSiteSupported S (((if P l then u l else 0 : ℝ):ℂ) • finitePauliMatrix (pathWord l))
  split_ifs with h
  · exact supported_pauli _ (hs l h) _
  · rw [Complex.ofReal_zero,zero_smul]; exact IsSiteSupported.zero S

/-- Splitting at a longitudinal spin preserves the Hamiltonian exactly.
The two pieces overlap in one site, where every nonzero Pauli term has
the same axis. Their propagators can therefore be compiled separately. -/
theorem conserved_split (a : Fin (n+1)) (u : PathShell n) (h : longitudinalAt a.succ u) :
    let L := pathHamiltonian (restricted (onLeft a) u)
    let R := pathHamiltonian (restricted (fun l => ¬onLeft a l) u)
    pathHamiltonian u=L+R ∧ Commute L R ∧
      IsSiteSupported (A:=fun _ : Fin (n+2) => Bool) (Iic a.succ) L ∧
      IsSiteSupported (A:=fun _ : Fin (n+2) => Bool) (Ici a.succ) R := by
  classical
  intro L R
  refine ⟨sum_restricted _ _,?_,restricted_supported _ _ _ (fun l hl i hi => left_none a l hl (lt_of_not_ge (fun hh => hi (mem_Iic.mpr hh)))),
    restricted_supported _ _ _ (fun l hl i hi => right_none a l hl (lt_of_not_ge (fun hh => hi (mem_Ici.mpr hh))))⟩
  dsimp only [L,R]
  rw [pathHamiltonian_eq_sum,pathHamiltonian_eq_sum]
  apply Commute.sum_left
  intro l _
  apply Commute.sum_right
  intro m _
  by_cases hh : ¬onLeft a l
  · rw [restricted_zero u hh,Complex.ofReal_zero,zero_smul]; exact Commute.zero_left _
  have hl := not_not.mp hh
  rw [restricted_eq u hl]
  by_cases hm : onLeft a m
  · rw [restricted_zero (P:=fun x => ¬onLeft a x) u (not_not_intro hm),Complex.ofReal_zero,zero_smul]; exact Commute.zero_right _
  rw [restricted_eq (P:=fun x => ¬onLeft a x) u hm]
  by_cases hul : u l=0
  · simp [hul]
  by_cases hum : u m=0
  · simp [hum]
  apply Commute.smul_right
  apply Commute.smul_left
  apply (finitePauli_commute_iff_sign ..).mpr
  apply prod_eq_one
  intro i _
  apply if_pos
  rcases lt_trichotomy i a.succ with hi|rfl|hi
  · exact Or.inr (Or.inl (right_none a m hm hi))
  · rcases h l hul with hl'|hl'
    · exact Or.inl hl'
    rcases h m hum with hm'|hm'
    · exact Or.inr (Or.inl hm')
    · exact Or.inr (Or.inr (hl'.trans hm'.symm))
  · exact Or.inl (left_none a l hl hi)

#print axioms conserved_split
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
