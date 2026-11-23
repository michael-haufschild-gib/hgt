import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.CoordinateSubsequence

/-! # Partition of the occupation basis into increasing arithmetic progressions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

private theorem index_pred (n : ℕ+) : number (n.val-1) = n := by
  apply PNat.coe_injective
  change n.val-1+1 = n.val
  have hn := n.pos
  omega

/-- Lane j consists of the occupations r k+j+1, indexed by positive integers k+1. -/
def progression {r : ℕ} (j : Fin r) : ℕ+ ↪ ℕ+ where
  toFun n := number (r*(n.val-1)+j.val)
  inj' := by
    intro x y h
    have hr : 0 < r := (Nat.zero_le j.val).trans_lt j.isLt
    have he := Nat.add_right_cancel (number_injective h)
    have hxy : x.val-1 = y.val-1 := Nat.eq_of_mul_eq_mul_left hr he
    exact (index_pred x).symm.trans ((congrArg number hxy).trans (index_pred y))

theorem progression_apply {r : ℕ} (j : Fin r) (k : ℕ) :
    progression j (number k) = number (r*k+j.val) := by
  change number (r*(k+1-1)+j.val) = _
  rw [Nat.add_sub_cancel]

theorem progression_one {r : ℕ} (j : Fin r) : progression j 1 = number j.val := by
  change number (r*0+j.val) = _
  rw [Nat.mul_zero,Nat.zero_add]

theorem progression_increases {r : ℕ} (j : Fin r) (n : ℕ+) : n ≤ progression j n := by
  obtain ⟨k,rfl⟩ := number_surjective n
  rw [progression_apply]
  change k+1 ≤ r*k+j.val+1
  have hr : 1 ≤ r := (Nat.zero_le j.val).trans_lt j.isLt
  have hk := Nat.mul_le_mul_right k hr
  rw [Nat.one_mul] at hk
  omega

/-- Distinct lanes occupy disjoint sets of shells. -/
theorem progression_separate {r : ℕ} {i j : Fin r} (hij : i ≠ j) (x y : ℕ+) :
    progression i x ≠ progression j y := by
  intro eqn
  have he := congrArg (fun k => k % r) (number_injective eqn)
  have hm (a : ℕ) (b : Fin r) : (r*a+b.val)%r = b.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt b.isLt]
  change (r*(x.val-1)+i.val)%r = (r*(y.val-1)+j.val)%r at he
  rw [hm,hm] at he
  exact hij (Fin.ext he)

#print axioms progression_increases
#print axioms progression_separate

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
