import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RefinementTail
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Digit sums in the remainder's energy counting function

The even missing-winding period makes every remaining product a square.
Counting radial labels at successive windings gives the sum of the
quotients of the square-root cutoff by positive radix powers.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks DyadicAperture.Binary

/-- Ratio between successive square roots of the primitive omitted products. -/
def tailRadix (t : ExceptionalTime) (j : ℕ) : ℕ+ := (block t)^(windingOrder (refined t j)/2)

private theorem order_even (v : ExceptionalTime) : 2 ∣ windingOrder v := by
  obtain ⟨d,hd⟩ := order_dyadic v
  cases d with
  | zero => exact ((order_nontrivial v).ne' (hd.trans (pow_zero 2))).elim
  | succ d => exact ⟨2^d,hd.trans (pow_succ' 2 d)⟩

theorem radix_gt_one (t : ExceptionalTime) (j : ℕ) : 1 < (tailRadix t j).val :=
  one_lt_pow₀ (block_nontrivial t) (Nat.div_pos (order_nontrivial _) (by norm_num)).ne'

theorem radix_sq (t : ExceptionalTime) (j : ℕ) :
    (tailRadix t j)^2 = (block t)^(windingOrder (refined t j)) := by
  rw [tailRadix,← pow_mul,Nat.div_mul_cancel (order_even _)]

theorem tail_square (t : ExceptionalTime) (j : ℕ) (x : leastWords t) (p : TailIndex) :
    tailWord t j x p false * tailWord t j x p true = ((tailRadix t j)^(p.2.1+1)*p.2.2)^2 := by
  rw [tail_product,pow_mul,← radix_sq,mul_pow,← pow_mul,← pow_mul,Nat.mul_comm 2]

/-- The exact coordinates in one square shell; the common radial label is forced. -/
def squareShellBasis (t : ExceptionalTime) (j : ℕ) (x : leastWords t) (N : ℕ+) :
    {y : {w // remainder t j w} // y.val false*y.val true = N^2} ≃
      Bool × {i : ℕ // (tailRadix t j).val^(i+1) ∣ N.val} := by
  let C := (tailRadix t j).val
  let e := tailBasis t j x
  have h (p : TailIndex) : C^(p.2.1+1)*p.2.2.val = N.val ↔ (e p).val false*(e p).val true = N^2 := by
    change _ ↔ tailWord t j x p false*tailWord t j x p true = _
    rw [tail_square]
    constructor
    · intro he
      exact congrArg (·^2) (PNat.coe_injective he)
    · intro he
      exact Nat.pow_left_injective (by norm_num : (2:ℕ) ≠ 0) (congrArg PNat.val he)
  apply (e.subtypeEquiv h).symm.trans
  refine ⟨fun p => (p.val.1,⟨p.val.2.1,p.val.2.2.val,p.property.symm⟩),?_,?_,?_⟩
  · rintro ⟨r,i,hi⟩
    have hp : 0 < C^(i+1) := pow_pos (Nat.zero_lt_one.trans (radix_gt_one t j)) _
    exact ⟨(r,i,⟨N.val/C^(i+1),Nat.div_pos (Nat.le_of_dvd N.pos hi) hp⟩),Nat.mul_div_cancel' hi⟩
  · rintro ⟨⟨r,i,n⟩,he⟩
    apply Subtype.ext
    change (r,i,(⟨N.val/C^(i+1),_⟩ : ℕ+)) = (r,i,n)
    have hn : N.val/C^(i+1) = n.val := by
      rw [← he,Nat.mul_div_cancel_left _ (pow_pos (Nat.zero_lt_one.trans (radix_gt_one t j)) _)]
    exact congrArg (fun v : ℕ+ => (r,i,v)) (PNat.coe_injective hn)
  · rintro ⟨r,⟨i,hi⟩⟩
    rfl

def countingStates (t : ExceptionalTime) (j X : ℕ) :=
  {y : {w // remainder t j w} // (y.val false*y.val true).val ≤ X^2}

private abbrev DigitsIndex (C X : ℕ) :=
  Bool × ((i : Fin (Nat.log C X+1)) × Fin (X/C^(i.val+1)))

private def countEquiv (C : ℕ) (hC : 1 < C) (X : ℕ) :
    {p : TailIndex // C^(p.2.1+1)*p.2.2.val ≤ X} ≃ DigitsIndex C X where
  toFun p := by
    obtain ⟨⟨r,i,n⟩,hp⟩ := p
    have hpow : C^(i+1) ≤ X := (Nat.le_mul_of_pos_right _ n.pos).trans hp
    have hi := Nat.le_log_of_pow_le hC hpow
    have hn : n.val ≤ X/C^(i+1) :=
      (Nat.le_div_iff_mul_le (pow_pos (by omega) _)).mpr ((Nat.mul_comm _ _).le.trans hp)
    refine ⟨r,⟨i,by omega⟩,⟨n.val-1,?_⟩⟩
    change n.val-1 < X/C^(i+1)
    have := n.pos
    omega
  invFun p := by
    obtain ⟨r,i,n⟩ := p
    refine ⟨(r,i.val,⟨n.val+1,Nat.succ_pos _⟩),?_⟩
    change C^(i.val+1)*(n.val+1) ≤ X
    rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le (pow_pos (by omega) _)).mp n.isLt
  left_inv := by
    rintro ⟨⟨r,i,⟨n,hn⟩⟩,hp⟩
    apply Subtype.ext
    change (r,i,(⟨n-1+1,_⟩ : ℕ+)) = (r,i,(⟨n,hn⟩ : ℕ+))
    congr 2
    exact PNat.coe_injective (by change n-1+1 = n; omega)
  right_inv := by rintro ⟨r,⟨i,hi⟩,⟨n,hn⟩⟩; rfl

private def statesEquiv (t : ExceptionalTime) (j X : ℕ) (x : leastWords t) :
    countingStates t j X ≃ DigitsIndex (tailRadix t j).val X := by
  let e := tailBasis t j x
  let C := (tailRadix t j).val
  have h (p : TailIndex) : C^(p.2.1+1)*p.2.2.val ≤ X ↔ ((e p).val false*(e p).val true).val ≤ X^2 := by
    change _ ↔ (tailWord t j x p false*tailWord t j x p true).val ≤ _
    rw [tail_square,PNat.pow_coe,PNat.mul_coe,PNat.pow_coe]
    exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num : (2:ℕ) ≠ 0)).symm
  exact (e.subtypeEquiv h).symm.trans (countEquiv C (radix_gt_one t j) X)

instance (t : ExceptionalTime) (j X : ℕ) : Finite (countingStates t j X) := by
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  exact Finite.of_equiv _ (statesEquiv t j X ⟨x,hx⟩).symm

/-- Actual number of remaining basis occupations through product X². -/
theorem count_floor_sum (t : ExceptionalTime) (j X : ℕ) :
    Nat.card (countingStates t j X) =
      2*∑ i ∈ Finset.range (Nat.log (tailRadix t j).val X+1), X/(tailRadix t j).val^(i+1) := by
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  rw [Nat.card_congr (statesEquiv t j X ⟨x,hx⟩)]
  unfold DigitsIndex
  rw [Nat.card_prod,Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card,Fintype.card_bool,Fintype.card_fin]
  exact congrArg (2*·) (Fin.sum_univ_eq_sum_range (fun i : ℕ => X/(tailRadix t j).val^(i+1)) _)

theorem count_digit_law (t : ExceptionalTime) (j X : ℕ) :
    ((tailRadix t j).val-1)*Nat.card (countingStates t j X) =
      2*(X-((tailRadix t j).val.digits X).sum) := by
  rw [count_floor_sum,mul_left_comm,Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]

#print axioms squareShellBasis
#print axioms tail_square
#print axioms count_floor_sum
#print axioms count_digit_law

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
