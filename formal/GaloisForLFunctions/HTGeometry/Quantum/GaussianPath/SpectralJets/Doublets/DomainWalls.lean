import GaloisForLFunctions.HTGeometry.BaseThreeSignSeparation
import GaloisForLFunctions.HTGeometry.PathDiagonalCarrier

/-! # Isolated complementary doublets of a nearest-neighbour Ising chain -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- The Boolean bond records whether the two neighboring spins disagree. -/
def walls {n : ℕ} (s : Fin (n+1) → Bool) (i : Fin n) : Bool :=
  xor (s i.castSucc) (s i.succ)

def reverseSpins {n : ℕ} (s : Fin n → Bool) (i : Fin n) : Bool := !(s i)

private theorem walls_reverse {n : ℕ} (s : Fin (n+1) → Bool) : walls (reverseSpins s) = walls s := by
  funext i
  dsimp only [walls,reverseSpins]
  cases s i.castSucc <;> cases s i.succ <;> rfl

private theorem reconstruct {n : ℕ} {s t : Fin (n+1) → Bool}
    (h0 : s 0 = t 0) (h : walls s = walls t) : s=t := by
  funext i
  induction i using Fin.induction with
  | zero => exact h0
  | succ i ih =>
    have he := congrFun h i
    change xor (s i.castSucc) (s i.succ) = xor (t i.castSucc) (t i.succ) at he
    rw [ih] at he
    cases t i.castSucc <;> cases s i.succ <;> cases t i.succ <;> simp_all

/-- The full bond record determines the spin configuration up to its global sign. -/
theorem walls_eq_iff {n : ℕ} (s t : Fin (n+1) → Bool) :
    walls s = walls t ↔ s=t ∨ s=reverseSpins t := by
  constructor
  · intro h
    by_cases h0 : s 0 = t 0
    · exact Or.inl (reconstruct h0 h)
    · apply Or.inr
      apply reconstruct _ (h.trans (walls_reverse t).symm)
      dsimp only [reverseSpins]
      cases hs : s 0 <;> cases ht : t 0 <;> simp_all
  · rintro (rfl|rfl)
    · rfl
    · exact walls_reverse t

/-- No onsite field is present. The successive ZZ bond weights are 1,3,9,… . -/
def isingShell (n : ℕ) : PathShell n := WithLp.toLp 2 fun l => match l with
  | .inl _ => 0
  | .inr (i,ab) => if ab=(2,2) then (3:ℝ)^i.val else 0

def bondEnergy {n : ℕ} (s : Fin (n+1) → Bool) : ℝ :=
  ∑ i, (3:ℝ)^i.val * siteSign (walls s) i

/-- The bond code is the actual diagonal of a physical path generator. -/
theorem diagonal_ising (n : ℕ) :
    pathHamiltonian (isingShell n) = Matrix.diagonal (fun s => (bondEnergy s:ℂ)) := by
  rw [pathHamiltonian_eq_diagonal (isingShell n) (by
    rintro (⟨i,a⟩|⟨i,ab⟩) h
    · rfl
    · exact if_neg h)]
  apply congrArg Matrix.diagonal
  funext s
  apply congrArg Complex.ofReal
  have hsite (i : Fin (n+2)) : isingShell n (.inl (i,2)) = 0 := rfl
  have hedge (e : Fin (n+1)) : isingShell n (.inr (e,2,2)) = (3:ℝ)^e.val := by
    change (if ((2,2) : Fin 3 × Fin 3) = (2,2) then _ else _) = _
    rw [if_pos rfl]
  simp only [pathDiagEnergy,hsite,hedge,zero_mul,Finset.sum_const_zero,zero_add,bondEnergy]
  apply Finset.sum_congr rfl
  intro i _
  have hne : i.castSucc ≠ i.succ := fun he => by have hh := congrArg Fin.val he; simp at hh
  simp only [siteSign,walls,zSetSign,Finset.prod_insert (Finset.notMem_singleton.mpr hne),Finset.prod_singleton]
  cases s i.castSucc <;> cases s i.succ <;> simp

/-- Every distinct complementary pair is separated from every other pair
by an energy gap of at least two, uniformly in the chain length. -/
theorem bond_gap {n : ℕ} (s t : Fin (n+1) → Bool) (hs : s≠t) (ht : s≠reverseSpins t) :
    2 ≤ |bondEnergy s-bondEnergy t| := by
  have h : walls s ≠ walls t := fun he => ((walls_eq_iff s t).mp he).elim hs ht
  simpa only [bondEnergy,←Finset.sum_sub_distrib,←mul_sub] using two_le_abs_sum_signDiff h

#print axioms diagonal_ising
#print axioms bond_gap
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
