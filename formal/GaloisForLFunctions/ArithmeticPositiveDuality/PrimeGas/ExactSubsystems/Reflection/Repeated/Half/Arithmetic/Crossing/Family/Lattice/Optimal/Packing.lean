import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Optimal.Coefficients
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse.Temperature

/-! # Realizing signed frequency coefficients with one energy level per magnitude -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Optimal

open Finset Real

/-- The sign of the coefficient chooses which side of the mean carries its copies. -/
private def oriented : ℤ → ℤ → ℤ
  | .ofNat _, k => k
  | .negSucc _, k => -k

private theorem moment (c k : ℤ) : (c.natAbs : ℤ)*oriented c k=c*k := by
  cases c with
  | ofNat n => simp [oriented]
  | negSucc n =>
    change ((n+1 : ℕ) : ℤ)*(-k)=Int.negSucc n*k
    rw [Int.negSucc_eq]
    push_cast
    ring

private theorem wave (c k : ℤ) (x : ℝ) :
    (c.natAbs : ℝ)*oddTerm x (oriented c k : ℤ)= (c : ℝ)*oddTerm x k := by
  have neg (z : ℝ) : oddTerm x (-z)= -oddTerm x z := by
    simp only [oddTerm,mul_neg,neg_mul,neg_neg,neg_sub]
  cases c with
  | ofNat n => simp [oriented]
  | negSucc n =>
    change ((n+1 : ℕ) : ℝ)*oddTerm x ((-k : ℤ) : ℝ)=(Int.negSucc n : ℝ)*oddTerm x k
    rw [Int.negSucc_eq,Int.cast_neg,neg]
    push_cast
    ring

/-- A centered Laurent response supported on the first m positive frequencies
uses at most m distinct physical prime-power energies, regardless of degeneracies. -/
theorem packed_response (p : Nat.Primes) (T : Finset ℚ) :
    ∃ (n : ℕ) (a : Fin n → ℕ), (univ.image (primeModes p a)).card≤T.card+2 ∧
      ∀ t : ℝ, oddTrace (centered (primeModes p a)) t=profile T (t*log p.val) := by
  classical
  obtain ⟨c,zero,response⟩ := bounded_coefficients T
  let m := T.card+2
  let I := (j : Fin m) × Fin (c j).natAbs
  let e := (Fintype.equivFin I).symm
  let k (j : Fin m) : ℤ := oriented (c j) (j.val+1)
  let a (j : Fin m) : ℕ := ((m : ℤ)+k j).toNat
  have lift (j : Fin m) : (a j : ℤ)=(m : ℤ)+k j := by
    apply Int.toNat_of_nonneg
    have bound := j.isLt
    unfold k
    cases c j <;> simp only [oriented] <;> omega
  let signed (i : Fin (Fintype.card I)) : ℤ := k (e i).1
  let occ (i : Fin (Fintype.card I)) := a (e i).1
  have total : (∑ i, signed i)=0 := by
    rw [show (∑ i, signed i)=∑ i : I, k i.1 from Equiv.sum_comp e (fun i => k i.1)]
    rw [Fintype.sum_sigma]
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,k,moment] using zero
  have totalR : (∑ i, (signed i : ℝ))=0 := by rw [← Int.cast_sum,total,Int.cast_zero]
  have shift : levels occ=fun i => 1*(signed i : ℝ)+(m : ℝ) := by
    funext i
    simpa only [levels,occ,signed,Int.cast_natCast,Int.cast_add,one_mul,add_comm] using
      congrArg (fun z : ℤ => (z : ℝ)) (lift (e i).1)
  have coeffs (x : ℝ) : (∑ i, oddTerm x (signed i : ℝ))=profile T x := by
    rw [show (∑ i, oddTerm x (signed i : ℝ))=∑ i : I, oddTerm x (k i.1 : ℝ) from
      Equiv.sum_comp e (fun i => oddTerm x (k i.1 : ℝ)),Fintype.sum_sigma]
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,k,wave,Int.cast_add,
      Int.cast_natCast,Int.cast_one] using response x
  refine ⟨_,occ,?_,fun t => ?_⟩
  · have sub : univ.image (primeModes p occ) ⊆ univ.image (primeModes p a) := by
      rintro _ hi
      obtain ⟨i,_,rfl⟩ := mem_image.mp hi
      exact mem_image.mpr ⟨(e i).1,mem_univ _,rfl⟩
    exact (card_le_card sub).trans (card_image_le.trans (by rw [card_univ,Fintype.card_fin]))
  · rw [Sparse.mode_grid,centered_affine,shift,centered_affine,centered_eq_of_sum_zero totalR]
    have scale (z : ℝ) : oddTerm t (log p.val*z)=oddTerm (t*log p.val) z := by
      simp only [oddTerm,mul_assoc,neg_mul]
    simpa only [oddTrace,one_mul,scale] using coeffs (t*log p.val)

#print axioms packed_response

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Optimal
