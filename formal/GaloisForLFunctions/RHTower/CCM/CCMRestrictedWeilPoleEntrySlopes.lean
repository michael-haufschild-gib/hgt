import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCutoffAtoms

/-!
# Opposite parity slopes at a prime-power entry

The exact new odd and even energy corrections vanish at entry. Their slopes
are respectively positive and negative at every genuine prime power, with
explicit squared exponential factors. These are the derivative jumps between
adjacent frozen pole expressions, not a permanent sign for an older atom.
-/

open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace RHTower

private theorem entry_inverse (n : ℕ) (hn : 2 ≤ n) :
    1/(n:ℝ) = Real.exp (-(ccmWeilIntegerEntry n hn).1)^(2 : ℕ) := by
  rw [← exp_two_mul_ccmWeilIntegerEntry n hn,one_div,← Real.exp_neg,← Real.exp_nat_mul]
  congr 1
  ring

private theorem atom_diagonal_deriv (n : ℕ) (s : ℝ) :
    HasDerivAt (ccmWeilPolePrimeDiagonalAtom n)
      (2*ArithmeticFunction.vonMangoldt n*(Real.exp s/n+Real.exp (-s))) s := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-s)) s := by
    simpa only [Pi.neg_apply,id_eq,mul_neg_one] using! (hasDerivAt_id s).neg.exp
  convert! (((Real.hasDerivAt_exp s).div_const n).sub he).const_mul
    (2*ArithmeticFunction.vonMangoldt n) using 1
  simp only [sub_neg_eq_add]

private theorem atom_cross_deriv (n : ℕ) (s : ℝ) :
    HasDerivAt (ccmWeilPolePrimeCrossAtom n)
      (2*ArithmeticFunction.vonMangoldt n*(1+1/(n:ℝ))) s := by
  convert! (((hasDerivAt_id s).const_mul 2).sub_const (Real.log n)).const_mul
    (ArithmeticFunction.vonMangoldt n*(1+1/(n:ℝ))) using 1
  ring

/-- At entry, the odd-energy change has the nonnegative exact slope
`4 Lambda(n) (1-exp(-b))²`, where `b=log(n)/2`. -/
theorem hasDerivAt_ccmWeilOddPole_entry_atom (n : ℕ) (hn : 2 ≤ n) :
    HasDerivAt (fun s => 2*(-ccmWeilPolePrimeDiagonalAtom n s+ccmWeilPolePrimeCrossAtom n s))
      (4*ArithmeticFunction.vonMangoldt n*(1-Real.exp (-(ccmWeilIntegerEntry n hn).1))^(2 : ℕ))
      (ccmWeilIntegerEntry n hn).1 := by
  let b := ccmWeilIntegerEntry n hn
  have he : Real.exp b.1/n = Real.exp (-b.1) := by
    rw [← exp_two_mul_ccmWeilIntegerEntry n hn,← Real.exp_sub]
    congr 1
    dsimp [b]
    ring
  convert! (((atom_diagonal_deriv n b.1).neg).add (atom_cross_deriv n b.1)).const_mul 2 using 1
  rw [he,entry_inverse n hn]
  dsimp [b]
  ring

/-- At entry, the even-energy change has the nonpositive exact slope
`-4 Lambda(n) (1+exp(-b))²`. -/
theorem hasDerivAt_ccmWeilEvenPole_entry_atom (n : ℕ) (hn : 2 ≤ n) :
    HasDerivAt (fun s => 2*(-ccmWeilPolePrimeDiagonalAtom n s-ccmWeilPolePrimeCrossAtom n s))
      (-4*ArithmeticFunction.vonMangoldt n*(1+Real.exp (-(ccmWeilIntegerEntry n hn).1))^(2 : ℕ))
      (ccmWeilIntegerEntry n hn).1 := by
  let b := ccmWeilIntegerEntry n hn
  have he : Real.exp b.1/n = Real.exp (-b.1) := by
    rw [← exp_two_mul_ccmWeilIntegerEntry n hn,← Real.exp_sub]
    congr 1
    dsimp [b]
    ring
  convert! (((atom_diagonal_deriv n b.1).neg).sub (atom_cross_deriv n b.1)).const_mul 2 using 1
  rw [he,entry_inverse n hn]
  dsimp [b]
  ring

/-- The odd slope jump is strictly positive exactly at genuine prime powers. -/
theorem ccmWeilOddPole_entry_slope_pos_iff (n : ℕ) (hn : 2 ≤ n) :
    0 < 4*ArithmeticFunction.vonMangoldt n*(1-Real.exp (-(ccmWeilIntegerEntry n hn).1))^(2 : ℕ) ↔
      IsPrimePow n := by
  have he : 0 < 1-Real.exp (-(ccmWeilIntegerEntry n hn).1) := by
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (ccmWeilIntegerEntry n hn).2)
    linarith
  rw [mul_pos_iff_of_pos_right (sq_pos_of_pos he),mul_pos_iff_of_pos_left (by norm_num : (0:ℝ) < 4),
    ArithmeticFunction.vonMangoldt_pos_iff]

/-- The adjacent frozen odd energies have exactly the positive entry slope jump. -/
theorem hasDerivAt_ccmWeilOddPoleChamber_succ_jump (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊ = ⌊Real.exp (2*a.1)⌋₊+1)
    (hn : 2 ≤ ⌊Real.exp (2*a.1)⌋₊+1) :
    HasDerivAt (fun s => ccmWeilOddPoleChamber b s-ccmWeilOddPoleChamber a s)
      (4*ArithmeticFunction.vonMangoldt (⌊Real.exp (2*a.1)⌋₊+1)*
        (1-Real.exp (-(ccmWeilIntegerEntry (⌊Real.exp (2*a.1)⌋₊+1) hn).1))^(2 : ℕ))
      (ccmWeilIntegerEntry (⌊Real.exp (2*a.1)⌋₊+1) hn).1 := by
  have he : (fun s => ccmWeilOddPoleChamber b s-ccmWeilOddPoleChamber a s) =
      (fun s => 2*(-ccmWeilPolePrimeDiagonalAtom (⌊Real.exp (2*a.1)⌋₊+1) s+
        ccmWeilPolePrimeCrossAtom (⌊Real.exp (2*a.1)⌋₊+1) s)) := by
    funext s
    have hA := ccmWeilPoleChamberDiagonal_succ_cutoff a b hf s
    have hC := ccmWeilPoleChamberCross_succ_cutoff a b hf s
    unfold ccmWeilOddPoleChamber
    linarith
  rw [he]
  exact hasDerivAt_ccmWeilOddPole_entry_atom _ hn

/-- The even entry slope is strictly negative exactly at genuine prime powers. -/
theorem ccmWeilEvenPole_entry_slope_neg_iff (n : ℕ) (hn : 2 ≤ n) :
    -4*ArithmeticFunction.vonMangoldt n*(1+Real.exp (-(ccmWeilIntegerEntry n hn).1))^(2 : ℕ) < 0 ↔
      IsPrimePow n := by
  have he : 0 < 1+Real.exp (-(ccmWeilIntegerEntry n hn).1) := by positivity
  have hs := sq_pos_of_pos he
  constructor
  · intro h
    apply ArithmeticFunction.vonMangoldt_pos_iff.mp
    have hm := ArithmeticFunction.vonMangoldt_nonneg (n:=n)
    by_contra hnot
    have hz : ArithmeticFunction.vonMangoldt n = 0 := le_antisymm (le_of_not_gt hnot) hm
    rw [hz] at h
    norm_num at h
  · intro h
    have hm := ArithmeticFunction.vonMangoldt_pos_iff.mpr h
    have hh := mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hm) hs
    nlinarith

/-- The adjacent frozen even energies have exactly the negative entry slope jump. -/
theorem hasDerivAt_ccmWeilEvenPoleChamber_succ_jump (a b : SuzukiPositiveAperture)
    (hf : ⌊Real.exp (2*b.1)⌋₊ = ⌊Real.exp (2*a.1)⌋₊+1)
    (hn : 2 ≤ ⌊Real.exp (2*a.1)⌋₊+1) :
    HasDerivAt (fun s => 2*(ccmWeilPoleChamberDiagonal b s+ccmWeilPoleChamberCross b s)-
      2*(ccmWeilPoleChamberDiagonal a s+ccmWeilPoleChamberCross a s))
      (-4*ArithmeticFunction.vonMangoldt (⌊Real.exp (2*a.1)⌋₊+1)*
        (1+Real.exp (-(ccmWeilIntegerEntry (⌊Real.exp (2*a.1)⌋₊+1) hn).1))^(2 : ℕ))
      (ccmWeilIntegerEntry (⌊Real.exp (2*a.1)⌋₊+1) hn).1 := by
  have he : (fun s => 2*(ccmWeilPoleChamberDiagonal b s+ccmWeilPoleChamberCross b s)-
      2*(ccmWeilPoleChamberDiagonal a s+ccmWeilPoleChamberCross a s)) =
      (fun s => 2*(-ccmWeilPolePrimeDiagonalAtom (⌊Real.exp (2*a.1)⌋₊+1) s-
        ccmWeilPolePrimeCrossAtom (⌊Real.exp (2*a.1)⌋₊+1) s)) := by
    funext s
    have hA := ccmWeilPoleChamberDiagonal_succ_cutoff a b hf s
    have hC := ccmWeilPoleChamberCross_succ_cutoff a b hf s
    linarith
  rw [he]
  exact hasDerivAt_ccmWeilEvenPole_entry_atom _ hn

end RHTower
