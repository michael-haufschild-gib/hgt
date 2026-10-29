import GaloisForLFunctions.SignedArithmeticHodgeTheory.EveryGeneratorCutoffStopsAtAnActualDyadicCell

/-!
# Generator cutoffs are logarithmic block averages

Every column of the whole-orbit projection is supported on one finite integer
block. The block is the actual dyadic translate of its stopping cell, with
logarithmic lengths as averaging weights. The support of a projected original
cell stays below twice its original label, independently of the cutoff.
-/

noncomputable section
open RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "W" => logCellShift 2
local notation "e" => fun n : ℕ+ => (lp.single 2 n (1 : ℂ) : CellH)
local notation "P" => logCellGeneratorHead

/-- The stopping label is the integer quotient at the stopping level. -/
theorem logCellStoppingAncestor_div (A n : ℕ+) :
    (n : ℕ) / 2 ^ (logCellStoppingAncestor A n).1 =
      ((logCellStoppingAncestor A n).2 : ℕ) := by
  have h : ∀ m : ℕ, ∀ hm : 0 < m,
      m / 2 ^ (logCellStoppingAncestor A ⟨m, hm⟩).1 =
        ((logCellStoppingAncestor A ⟨m, hm⟩).2 : ℕ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hcut : m < 2 * (A : ℕ)
      · rw [logCellStoppingAncestor_of_lt A ⟨m, hm⟩ hcut]
        simp only [pow_zero, Nat.div_one]
        rfl
      · rw [logCellStoppingAncestor_of_ge A ⟨m, hm⟩
          (by change 2 * (A : ℕ) ≤ m; omega)]
        simp only [pow_succ', ← Nat.div_div_eq_div_mul]
        exact ih (m / 2) (Nat.div_lt_self hm (by norm_num)) (by have := A.pos; omega)
  exact h n n.pos

/-- A label in the stopping band determines its entire translated block. -/
theorem logCellStoppingAncestor_eq_of_div (A a : ℕ+) (ha : (A : ℕ) ≤ (a : ℕ))
    (ha' : (a : ℕ) < 2 * (A : ℕ)) (j : ℕ) (m : ℕ+)
    (hm : (m : ℕ) / 2 ^ j = (a : ℕ)) : logCellStoppingAncestor A m = (j, a) := by
  induction j generalizing m with
  | zero =>
    have hma : m = a := PNat.eq (by simpa only [pow_zero, Nat.div_one] using hm)
    rw [hma, logCellStoppingAncestor_of_lt A a ha']
  | succ j ih =>
    have hquot : ((m : ℕ) / 2) / 2 ^ j = (a : ℕ) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
      exact hm
    have hpar : (A : ℕ) ≤ (m : ℕ) / 2 :=
      ha.trans (by rw [← hquot]; exact Nat.div_le_self _ _)
    have hge : 2 * (A : ℕ) ≤ (m : ℕ) := by omega
    let b : ℕ+ := ⟨(m : ℕ) / 2, by have := A.pos; omega⟩
    have hb : logCellStoppingAncestor A b = (j, a) := ih b hquot
    rw [logCellStoppingAncestor_of_ge A m hge, hb]

/-- Every original cell in a stopping block has the same stopping ancestor. -/
theorem logCellStoppingAncestor_eq_of_same_block (A n m : ℕ+)
    (hm : (m : ℕ) / 2 ^ (logCellStoppingAncestor A n).1 =
      ((logCellStoppingAncestor A n).2 : ℕ)) :
    logCellStoppingAncestor A m = logCellStoppingAncestor A n := by
  by_cases hj : (logCellStoppingAncestor A n).1 = 0
  · have hn' := logCellStoppingAncestor_div A n
    rw [hj, pow_zero, Nat.div_one] at hm hn'
    have hmn : m = n := PNat.eq (hm.trans hn'.symm)
    rw [hmn]
  · have hnA : (A : ℕ) ≤ (n : ℕ) := by
      by_contra h
      have hn : (n : ℕ) < 2 * (A : ℕ) := by have := A.pos; omega
      have hs := logCellStoppingAncestor_of_lt A n hn
      exact hj (congrArg Prod.fst hs)
    exact logCellStoppingAncestor_eq_of_div A _ (le_logCellStoppingAncestor_label A n hnA)
      (logCellStoppingAncestor_label_lt A n) _ m hm

/-- An actual translated cell consists of the cells in its integer dyadic block. -/
theorem logCellDyadic_pow_single_apply (j : ℕ) (a m : ℕ+) :
    ((W ^ j) (e a)) m =
      if (m : ℕ) / 2 ^ j = (a : ℕ) then
        (Real.sqrt (logCell m / logCell a) : ℂ) else 0 := by
  classical
  cases j with
  | zero =>
    simp only [pow_zero, one_apply_eq_self, Nat.div_one, lp.single_apply, Pi.single_apply]
    by_cases hma : m = a
    · subst m
      simp only [ite_true, div_self (logCell_pos a.pos).ne', Real.sqrt_one, Complex.ofReal_one]
    · rw [if_neg hma, if_neg (fun h => hma (PNat.eq h))]
  | succ j =>
    rw [← logCellShift_two_pow_succ]
    exact logCellShift_single_apply (by have := one_lt_pow₀ (by norm_num : (1 : ℕ) < 2)
      (by omega : j + 1 ≠ 0); omega) a m

/-- The normalized stopping cell has the literal square-root length coordinates. -/
theorem logCellStoppingVector_apply (A n m : ℕ+) :
    logCellStoppingVector A n m =
      if (m : ℕ) / 2 ^ (logCellStoppingAncestor A n).1 =
          ((logCellStoppingAncestor A n).2 : ℕ) then
        (Real.sqrt (logCell m / logCell (logCellStoppingAncestor A n).2) : ℂ) else 0 := by
  exact logCellDyadic_pow_single_apply _ _ _

/-- Projection onto a stopping cell has the positive square-root length coefficient. -/
theorem logCellGeneratorHead_single_eq_sqrt_stopping (A n : ℕ+) :
    P A (e n) =
      (Real.sqrt (logCell n / logCell (logCellStoppingAncestor A n).2) : ℂ) •
        logCellStoppingVector A n := by
  rw [logCellGeneratorHead_single_eq_stopping, lp.inner_single_right,
    logCellStoppingVector_apply, if_pos (logCellStoppingAncestor_div A n),
    RCLike.inner_apply, Complex.conj_ofReal, one_mul]

/-- The whole-orbit cutoff has an explicit real, nonnegative block matrix. -/
theorem logCellGeneratorHead_single_apply (A n m : ℕ+) :
    (P A (e n)) m =
      if (m : ℕ) / 2 ^ (logCellStoppingAncestor A n).1 =
          ((logCellStoppingAncestor A n).2 : ℕ) then
        ((Real.sqrt (logCell n / logCell (logCellStoppingAncestor A n).2) *
          Real.sqrt (logCell m / logCell (logCellStoppingAncestor A n).2) : ℝ) : ℂ)
      else 0 := by
  rw [logCellGeneratorHead_single_eq_sqrt_stopping]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, logCellStoppingVector_apply]
  split_ifs <;> simp only [Complex.ofReal_mul, mul_zero]

/-- Two positive labels in one stopping block are within a factor of two. -/
theorem lt_twice_of_logCellStopping_block (A n m : ℕ+)
    (hm : (m : ℕ) / 2 ^ (logCellStoppingAncestor A n).1 =
      ((logCellStoppingAncestor A n).2 : ℕ)) : (m : ℕ) < 2 * (n : ℕ) := by
  let b := 2 ^ (logCellStoppingAncestor A n).1
  let a := ((logCellStoppingAncestor A n).2 : ℕ)
  have hb : 0 < b := Nat.pow_pos (by norm_num)
  have hn : (n : ℕ) / b = a := logCellStoppingAncestor_div A n
  have hnlo : a * b ≤ (n : ℕ) := (Nat.le_div_iff_mul_le hb).mp hn.ge
  have hmhi : (m : ℕ) < (a + 1) * b := (Nat.div_lt_iff_lt_mul hb).mp (by
    change (m : ℕ) / b < a + 1
    change (m : ℕ) / b = a at hm
    omega)
  have ha : 1 ≤ a := (logCellStoppingAncestor A n).2.pos
  have hbn : b ≤ (n : ℕ) := (by simpa only [one_mul] using Nat.mul_le_mul_right b ha).trans hnlo
  rw [Nat.add_mul, one_mul] at hmhi
  omega

/-- A projected original cell cannot create support at or beyond twice its label. -/
theorem logCellGeneratorHead_single_apply_eq_zero (A n m : ℕ+)
    (hm : 2 * (n : ℕ) ≤ (m : ℕ)) : (P A (e n)) m = 0 := by
  rw [logCellGeneratorHead_single_apply, if_neg]
  intro h
  exact (not_lt_of_ge hm) (lt_twice_of_logCellStopping_block A n m h)

/-- A coordinate row reads the actual stopping-cell average of the source. -/
theorem logCellGeneratorHead_apply_eq_stopping_inner (A n : ℕ+) (x : CellH) :
    (P A x) n =
      (Real.sqrt (logCell n / logCell (logCellStoppingAncestor A n).2) : ℂ) *
        inner ℂ (logCellStoppingVector A n) x := by
  have hi := inner_logCellGeneratorHead A (e n) x
  rw [logCellGeneratorHead_single_eq_sqrt_stopping, inner_smul_left,
    Complex.conj_ofReal, lp.inner_single_left, RCLike.inner_apply, star_one, mul_one] at hi
  exact hi.symm

/-- An original cell inside a translated dyadic block. -/
def logCellDyadicBlockCell (j : ℕ) (a : ℕ+) (r : Fin (2 ^ j)) : ℕ+ :=
  ⟨(a : ℕ) * 2 ^ j + r, by have := a.pos; positivity⟩

theorem logCellDyadicBlockCell_div (j : ℕ) (a : ℕ+) (r : Fin (2 ^ j)) :
    (logCellDyadicBlockCell j a r : ℕ) / 2 ^ j = (a : ℕ) := by
  change ((a : ℕ) * 2 ^ j + r) / 2 ^ j = (a : ℕ)
  exact div_block

/-- Every translated cell is an explicit finite sum of original cells. -/
theorem logCellDyadic_pow_single_eq_sum (j : ℕ) (a : ℕ+) :
    (W ^ j) (e a) = ∑ r : Fin (2 ^ j),
      (Real.sqrt (logCell (logCellDyadicBlockCell j a r) / logCell a) : ℂ) •
        e (logCellDyadicBlockCell j a r) := by
  cases j with
  | zero =>
    simp only [pow_zero, one_apply_eq_self, Fin.sum_univ_one]
    have hcell : logCellDyadicBlockCell 0 a 0 = a := by
      apply PNat.eq
      change (a : ℕ) * 2 ^ 0 + 0 = (a : ℕ)
      omega
    rw [hcell, div_self (logCell_pos a.pos).ne', Real.sqrt_one, Complex.ofReal_one, one_smul]
  | succ j =>
    rw [← logCellShift_two_pow_succ]
    have hp : 2 ≤ 2 ^ (j + 1) := by
      have := one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) (by omega : j + 1 ≠ 0)
      omega
    have h := divBlockOp_single_eq_sum (by positivity : 0 < 2 ^ (j + 1))
      (norm_logCellWeight_le_one hp) a
    simpa only [logCellShift, logCellWeight, div_block, logCellDyadicBlockCell,
      Nat.toPNat] using h

private theorem sqrt_weighted_column {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    Real.sqrt u * Real.sqrt (u / w) * Real.sqrt (v / w) = (u / w) * Real.sqrt v := by
  apply (sq_eq_sq₀ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)) (mul_nonneg (div_nonneg hu.le hw.le) (Real.sqrt_nonneg _))).mp
  simp only [mul_pow, Real.sq_sqrt hu.le, Real.sq_sqrt hv.le,
    Real.sq_sqrt (div_nonneg hu.le hw.le), Real.sq_sqrt (div_nonneg hv.le hw.le)]
  ring

/-- A unit physical cell is redistributed as its length divided by the stopping-block length. -/
theorem logCellGeneratorHead_weighted_single (A n : ℕ+) :
    P A ((Real.sqrt (logCell n) : ℂ) • e n) =
      ∑ r : Fin (2 ^ (logCellStoppingAncestor A n).1),
        (((logCell n / logCell (logCellStoppingAncestor A n).2) *
          Real.sqrt (logCell (logCellDyadicBlockCell (logCellStoppingAncestor A n).1
            (logCellStoppingAncestor A n).2 r)) : ℝ) : ℂ) •
        e (logCellDyadicBlockCell (logCellStoppingAncestor A n).1
          (logCellStoppingAncestor A n).2 r) := by
  rw [map_smul, logCellGeneratorHead_single_eq_sqrt_stopping, logCellStoppingVector,
    logCellDyadic_pow_single_eq_sum, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [smul_smul]
  congr 1
  exact_mod_cast sqrt_weighted_column (logCell_pos n.pos)
    (logCell_pos (logCellDyadicBlockCell _ _ r).pos)
    (logCell_pos (logCellStoppingAncestor A n).2.pos)

/-- The averaging weights are the original logarithmic lengths and sum to one. -/
theorem sum_logCellDyadicBlock_weights (j : ℕ) (a : ℕ+) :
    ∑ r : Fin (2 ^ j), logCell (logCellDyadicBlockCell j a r) / logCell a = 1 := by
  rw [← Finset.sum_div]
  have hs : (∑ r : Fin (2 ^ j), logCell (logCellDyadicBlockCell j a r)) = logCell a :=
    sum_logCell_block (by positivity) a.pos
  rw [hs, div_self (logCell_pos a.pos).ne']

/-- Physical cell height is the Hilbert coordinate divided by square-root cell length. -/
def logCellPhysicalHeight (x : CellH) (n : ℕ+) : ℂ :=
  x n / (Real.sqrt (logCell n) : ℂ)

private theorem sqrt_ratio_product {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    Real.sqrt (u / w) * Real.sqrt (v / w) =
      Real.sqrt u * (v / w) / Real.sqrt v := by
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hv.le hw.le))
      (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (div_nonneg hu.le hw.le),
    Real.sq_sqrt (div_nonneg hv.le hw.le), div_pow, mul_pow,
    Real.sq_sqrt hu.le, Real.sq_sqrt hv.le]
  field_simp
  <;> ring

/-- The cutoff is literal logarithmic mass averaging on each stopping block. -/
theorem logCellGeneratorHead_physicalHeight (A n : ℕ+) (x : CellH) :
    logCellPhysicalHeight (P A x) n =
      ∑ r : Fin (2 ^ (logCellStoppingAncestor A n).1),
        ((logCell (logCellDyadicBlockCell (logCellStoppingAncestor A n).1
            (logCellStoppingAncestor A n).2 r) /
          logCell (logCellStoppingAncestor A n).2 : ℝ) : ℂ) *
        logCellPhysicalHeight x (logCellDyadicBlockCell (logCellStoppingAncestor A n).1
          (logCellStoppingAncestor A n).2 r) := by
  let j := (logCellStoppingAncestor A n).1
  let a := (logCellStoppingAncestor A n).2
  have hrow : (P A x) n = (Real.sqrt (logCell n) : ℂ) *
      ∑ r : Fin (2 ^ j), ((logCell (logCellDyadicBlockCell j a r) / logCell a : ℝ) : ℂ) *
        logCellPhysicalHeight x (logCellDyadicBlockCell j a r) := by
    rw [logCellGeneratorHead_apply_eq_stopping_inner, logCellStoppingVector,
      logCellDyadic_pow_single_eq_sum, sum_inner, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [inner_smul_left, Complex.conj_ofReal, lp.inner_single_left,
      RCLike.inner_apply, star_one, mul_one]
    have he : (Real.sqrt (logCell n / logCell a) : ℂ) *
        (Real.sqrt (logCell (logCellDyadicBlockCell j a r) / logCell a) : ℂ) =
        (Real.sqrt (logCell n) : ℂ) *
          ((logCell (logCellDyadicBlockCell j a r) / logCell a : ℝ) : ℂ) /
            (Real.sqrt (logCell (logCellDyadicBlockCell j a r)) : ℂ) := by
      exact_mod_cast sqrt_ratio_product (logCell_pos n.pos)
        (logCell_pos (logCellDyadicBlockCell j a r).pos) (logCell_pos a.pos)
    rw [← mul_assoc, he, logCellPhysicalHeight]
    ring
  change (P A x) n / (Real.sqrt (logCell n) : ℂ) = _
  rw [hrow]
  have hn : (Real.sqrt (logCell n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (logCell_pos n.pos)).ne'
  field_simp

/-- The projected physical height is constant on the entire stopping block. -/
theorem logCellGeneratorHead_height_eq_of_same_block (A n m : ℕ+) (x : CellH)
    (hm : (m : ℕ) / 2 ^ (logCellStoppingAncestor A n).1 =
      ((logCellStoppingAncestor A n).2 : ℕ)) :
    logCellPhysicalHeight (P A x) m = logCellPhysicalHeight (P A x) n := by
  rw [logCellGeneratorHead_physicalHeight, logCellGeneratorHead_physicalHeight,
    logCellStoppingAncestor_eq_of_same_block A n m hm]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_single_eq_sqrt_stopping
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_single_apply
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_single_apply_eq_zero
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_apply_eq_stopping_inner

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_physicalHeight

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_weighted_single

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellStoppingAncestor_eq_of_same_block
