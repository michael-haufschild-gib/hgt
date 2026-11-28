import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting.Isometry

/-! # Endpoint amplitudes of an isometric coassociative split -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting

open Finset

/-- Equality of the coefficient products under the two bracketings of three outputs. -/
def coassociative (F : Kernel) := ∀ a b c, F (a*b) c * F a b = F a (b*c) * F b c

theorem bracketings_iff (F : Kernel) :
    (∀ (f : Gas) a b c, F a b * wave F f (a*b,c) = F b c * wave F f (a,b*c)) ↔ coassociative F := by
  constructor
  · intro h a b c
    have e := h (lp.single 2 (a*(b*c)) (1:ℂ)) a b c
    simpa only [wave,mul_assoc a b c,lp.single_apply,Pi.single_eq_same,mul_one,
      mul_comm (F a b),mul_comm (F b c)] using e
  · intro h f a b c
    unfold wave
    rw [mul_assoc a b c]
    linear_combination f (a*(b*c)) * h a b c

private theorem shell_nonneg (F : Kernel) (n : ℕ+) (x : ℕ+ × ℕ+) : 0 ≤ shell F n x := by
  rw [shell]
  split_ifs <;> positivity

theorem occupied (F : Kernel) (h : normalized F) (n : ℕ+) :
    ∃ a b, a*b=n ∧ F a b≠0 := by
  by_contra! off
  have zero (x : ℕ+ × ℕ+) : shell F n x=0 := by
    by_cases p : x.1*x.2=n
    · simp [shell,p,off x.1 x.2 p]
    · simp [shell,p]
  have eqn := (h n).tsum_eq
  rw [tsum_congr zero,tsum_zero] at eqn
  exact zero_ne_one eqn

theorem vacuum_unit (F : Kernel) (h : normalized F) : ‖F 1 1‖^2=1 := by
  have eqn := (h 1).tsum_eq
  rw [tsum_eq_single ((1,1):ℕ+ × ℕ+)] at eqn
  · simpa [shell] using eqn
  · intro x ne
    apply if_neg
    intro p
    have prod : x.1.val*x.2.val=1 := congrArg PNat.val p
    obtain ⟨ha,hb⟩ := mul_eq_one.mp prod
    exact ne (Prod.ext (PNat.coe_injective ha) (PNat.coe_injective hb))

theorem exclusive (F : Kernel) (h : normalized F) {a b c d : ℕ+}
    (prod : a*b=c*d) (unit : ‖F a b‖^2=1) (nz : F c d≠0) : (c,d)=(a,b) := by
  by_contra ne
  have bound := (h (a*b)).summable.sum_le_tsum ({(c,d),(a,b)}:Finset (ℕ+ × ℕ+))
    (fun x _ => shell_nonneg F _ x)
  rw [sum_pair ne,(h (a*b)).tsum_eq] at bound
  simp [shell,prod.symm,unit] at bound
  exact nz bound

theorem left_endpoint (F : Kernel) (h : coassociative F) (n : ℕ+) (nz : F n 1≠0) :
    F n 1=F 1 1 := by
  have he := h n 1 1
  simp only [mul_one] at he
  exact mul_left_cancel₀ nz he

theorem right_endpoint (F : Kernel) (h : coassociative F) (n : ℕ+) (nz : F 1 n≠0) :
    F 1 n=F 1 1 := by
  have he := h 1 1 n
  simp only [one_mul] at he
  exact (mul_left_cancel₀ nz he).symm

#print axioms bracketings_iff
#print axioms occupied
#print axioms exclusive
#print axioms vacuum_unit
#print axioms left_endpoint
#print axioms right_endpoint

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting
