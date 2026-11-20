import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuDeterminant
import GaloisForLFunctions.RHTower.PrimeArchHausdorffBernsteinKMSRH
import Mathlib.Algebra.Polynomial.Coeff

/-!
# The signed fixed-point spectrum of permutation powers

For the permutation character of the symmetric group, pairing its kth
power with the sign character isolates two set-partition counts. The
determinant of a diagonal matrix plus the all-ones matrix kills every
other signed binomial moment. This gives an exact threshold in the
finite character formula used by Slonim for tensor multiplicities.
-/

namespace GaloisForLFunctions.SymmetricCharacters
open Finset Matrix Polynomial
noncomputable section
open scoped Classical
variable {α R : Type*} [Fintype α] [CommRing R]

private theorem fixed_point_enumerator [DecidableEq α] (w : α → R) :
    (∑ σ : Equiv.Perm α, ((Equiv.Perm.sign σ:ℤ):R)*
      ∏ i ∈ univ.filter (fun i => σ i=i), (w i+1)) =
    (∏ i, w i)+∑ i, ∏ j ∈ univ.erase i, w j := by
  let M : Matrix α α R := diagonal w+vecMulVec (fun _ => 1) (fun _ => 1)
  have hdet : M.det=(∏ i, w i)+∑ i, ∏ j ∈ univ.erase i, w j := by
    simpa only [one_mul] using HTGeometry.bgv_det_diagonal_add_vecMulVec w (fun _ => 1) (fun _ => 1)
  rw [←hdet,det_apply']
  apply sum_congr rfl
  intro σ _
  congr 1
  rw [prod_filter]
  apply prod_congr rfl
  intro i _
  by_cases hi : σ i=i <;> simp [M,diagonal_apply,vecMulVec,hi]

/-- In the signed multivariate fixed-point enumerator only the full
monomial and its one-coordinate deletions survive. -/
theorem signed_fixed_point_enumerator (w : α → R) :
    (∑ σ : Equiv.Perm α, ((Equiv.Perm.sign σ:ℤ):R)*
      ∏ i ∈ univ.filter (fun i => σ i=i), (w i+1)) =
    (∏ i, w i)+∑ i, ∏ j ∈ univ.erase i, w j :=
  fixed_point_enumerator w

/-- Number of fixed letters in the defining symmetric-group action. -/
abbrev permutationFixedLetters {n : ℕ} (σ : Equiv.Perm (Fin n)) := (univ.filter (fun i => σ i=i)).card

/-- The two nonzero signed binomial moments, with all boundary cases
included. Here the permutation degree is n+1. -/
theorem signed_fixed_point_choose (n r : ℕ) :
    (∑ σ : Equiv.Perm (Fin (n+1)), (Equiv.Perm.sign σ:ℤ)*((permutationFixedLetters σ).choose r:ℤ)) =
      (if r=n+1 then 1 else 0)+(n+1:ℤ)*(if r=n then 1 else 0) := by
  have h := fixed_point_enumerator (fun _ : Fin (n+1) => (X:ℤ[X]))
  simp only [prod_const,card_univ,Fintype.card_fin,card_erase_of_mem (mem_univ _),
    Nat.add_sub_cancel,sum_const,nsmul_eq_mul] at h
  let shift (σ : Equiv.Perm (Fin (n+1))) := ((X:ℤ[X])+1)^permutationFixedLetters σ
  have hn : (C (n+1:ℤ) : ℤ[X]) = ((n+1:ℕ):ℤ[X]) := by
    rw [map_add,map_natCast,map_one,Nat.cast_succ]
  have he : (∑ σ : Equiv.Perm (Fin (n+1)),
      C (Equiv.Perm.sign σ:ℤ)*((X:ℤ[X])+1)^permutationFixedLetters σ) =
      X^(n+1)+C (n+1:ℤ)*X^n := by
    rw [hn]
    calc
      _ = ∑ σ : Equiv.Perm (Fin (n+1)), ((Equiv.Perm.sign σ : ℤ) : ℤ[X]) * shift σ :=
        sum_congr rfl fun σ _ => congrArg (fun c : ℤ[X] => c * shift σ)
          (map_intCast C (Equiv.Perm.sign σ : ℤ))
      _ = _ := h
  have hc := congrArg (fun P : ℤ[X] => P.coeff r) he
  simpa only [finset_sum_coeff,coeff_C_mul,coeff_X_add_one_pow,coeff_add,coeff_X_pow] using hc

/-- The sign-weighted kth power of the permutation character equals the
group order times S(k,n)+S(k,n+1). In particular its first nonzero
moment is exactly k=n. -/
theorem signed_fixed_point_power (n k : ℕ) :
    (∑ σ : Equiv.Perm (Fin (n+1)), (Equiv.Perm.sign σ:ℤ)*(permutationFixedLetters σ:ℤ)^k) =
      ((n+1).factorial:ℤ)*((Nat.stirlingSecond k n:ℤ)+(Nat.stirlingSecond k (n+1):ℤ)) := by
  let a (r : ℕ) : ℤ := (Nat.stirlingSecond k r:ℤ)*(r.factorial:ℤ)
  have hexpand (m : ℕ) : (m:ℤ)^k=∑ r ∈ range (k+1), a r*(m.choose r:ℤ) := by
    have he := congrArg (fun t : ℕ => (t:ℤ)) (_root_.RHTower.pow_eq_sum_stirlingSecond_descFactorial m k)
    simpa only [a,Nat.cast_pow,Nat.cast_sum,Nat.cast_mul,Nat.descFactorial_eq_factorial_mul_choose,
      mul_assoc] using he
  have hselect (j : ℕ) : (∑ r ∈ range (k+1), if r=j then a r else 0)=a j := by
    by_cases hj : j<k+1
    · simp [mem_range,hj]
    · have hzero := Nat.stirlingSecond_eq_zero_of_lt (by omega : k<j)
      simp [mem_range,hj,a,hzero]
  calc
    _ = ∑ σ : Equiv.Perm (Fin (n+1)), ∑ r ∈ range (k+1),
        a r*((Equiv.Perm.sign σ:ℤ)*((permutationFixedLetters σ).choose r:ℤ)) := by
      apply sum_congr rfl
      intro σ _
      rw [hexpand,mul_sum]
      exact sum_congr rfl fun r _ => by ring
    _ = ∑ r ∈ range (k+1), a r*((if r=n+1 then 1 else 0)+(n+1:ℤ)*(if r=n then 1 else 0)) := by
      rw [sum_comm]
      simp_rw [←mul_sum,signed_fixed_point_choose]
    _ = a (n+1)+(n+1:ℤ)*a n := by
      rw [←hselect (n+1),←hselect n,mul_sum,←sum_add_distrib]
      exact sum_congr rfl fun r _ => by split_ifs <;> ring
    _ = _ := by simp only [a,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]; ring

/-- The first nonzero signed power occurs at n on n+1 letters. -/
theorem first_signed_fixed_point_power (n : ℕ) :
    (∀ k<n, (∑ σ : Equiv.Perm (Fin (n+1)), (Equiv.Perm.sign σ:ℤ)*(permutationFixedLetters σ:ℤ)^k)=0) ∧
    (∑ σ : Equiv.Perm (Fin (n+1)), (Equiv.Perm.sign σ:ℤ)*(permutationFixedLetters σ:ℤ)^n)=
      ((n+1).factorial:ℤ) := by
  constructor
  · intro k hk
    rw [signed_fixed_point_power,Nat.stirlingSecond_eq_zero_of_lt hk,
      Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_of_lt hk)]
    simp
  · rw [signed_fixed_point_power,Nat.stirlingSecond_self,Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
    simp

end
end GaloisForLFunctions.SymmetricCharacters
