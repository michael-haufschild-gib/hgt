import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.Stabilization

/-! # Independence of every triple if normalized readings are infinite -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real Set

private theorem pair_finite {t : ℝ} (ht : 0<t) (a b : ℕ+) (diff : energy a ≠ energy b)
    (A B : ℤ) (some : A ≠ 0 ∨ B ≠ 0)
    (sum : (A : ℝ)*shellPower t a+(B : ℝ)*shellPower t b=0) : (accumulated t).Finite := by
  have first {x y : ℝ} (yp : y ≠ 0) {i j : ℤ} (nz : i ≠ 0 ∨ j ≠ 0)
      (eq : (i : ℝ)*x+(j : ℝ)*y=0) : i ≠ 0 := by
    intro zero
    rw [zero,Int.cast_zero,zero_mul,zero_add] at eq
    exact (nz.resolve_left (not_not.mpr zero)) (Int.cast_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right yp))
  have reverse : (B : ℝ)*shellPower t b+(A : ℝ)*shellPower t a=0 := (add_comm _ _).trans sum
  have larger (n m : ℕ+) (lt : energy m<energy n) (i j : ℤ) (nz : i ≠ 0)
      (eq : (i : ℝ)*shellPower t n+(j : ℝ)*shellPower t m=0) : (accumulated t).Finite := by
    apply algebraic_gap_finite n m lt ht
    have ratio : relativePower t n m=((-(j : ℚ)/i : ℚ) : ℝ) := by
      rw [relativePower,Rat.cast_div,Rat.cast_neg,Rat.cast_intCast,Rat.cast_intCast]
      apply (div_eq_div_iff (shellPower_pos t m).ne' (Int.cast_ne_zero.mpr nz)).mpr
      linear_combination eq
    rw [ratio]
    exact isAlgebraic_rat ℚ _
  rcases lt_or_gt_of_ne diff with lt | gt
  · exact larger b a lt B A (first (shellPower_pos t a).ne' some.symm reverse) reverse
  · exact larger a b gt A B (first (shellPower_pos t b).ne' some sum) sum

private theorem nonzero_relation_finite {t : ℝ} (ht : 0<t) (a b c : ℕ+)
    (ab : energy a ≠ energy b) (ac : energy a ≠ energy c) (bc : energy b ≠ energy c)
    (A B C : ℤ) (some : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0)
    (sum : (A : ℝ)*shellPower t a+(B : ℝ)*shellPower t b+(C : ℝ)*shellPower t c=0) :
    (accumulated t).Finite := by
  by_cases ha : A=0
  · exact pair_finite ht b c bc B C (some.resolve_left (not_not.mpr ha))
      (by simpa only [ha,Int.cast_zero,zero_mul,zero_add] using sum)
  by_cases hb : B=0
  · exact pair_finite ht a c ac A C (Or.inl ha) (by simpa only [hb,Int.cast_zero,zero_mul,add_zero] using sum)
  by_cases hc : C=0
  · exact pair_finite ht a b ab A B (Or.inl ha) (by simpa only [hc,Int.cast_zero,zero_mul,add_zero] using sum)
  have order : (energy a<energy b ∧ energy a<energy c) ∨
      (energy b<energy a ∧ energy b<energy c) ∨ (energy c<energy a ∧ energy c<energy b) := by
    rcases lt_or_gt_of_ne ab with h | h
    · rcases lt_or_gt_of_ne ac with g | g
      · exact Or.inl ⟨h,g⟩
      · exact Or.inr (Or.inr ⟨g,g.trans h⟩)
    · rcases lt_or_gt_of_ne bc with g | g
      · exact Or.inr (Or.inl ⟨h,g⟩)
      · exact Or.inr (Or.inr ⟨g.trans h,g⟩)
  rcases order with aMin | bMin | cMin
  · apply three_shell_finite b c a aMin.1 aMin.2 bc B C (-A) hb hc (neg_ne_zero.mpr ha) ht
    unfold shellRelation
    rw [Int.cast_neg]
    linear_combination sum
  · apply three_shell_finite a c b bMin.1 bMin.2 ac A C (-B) ha hc (neg_ne_zero.mpr hb) ht
    unfold shellRelation
    rw [Int.cast_neg]
    linear_combination sum
  · apply three_shell_finite a b c cMin.1 cMin.2 ab A B (-C) ha hb (neg_ne_zero.mpr hc) ht
    unfold shellRelation
    rw [Int.cast_neg]
    linear_combination sum

/-- Infinite accumulation requires rational independence of every triple of
distinct shell coordinates, including triples containing the vacuum shell. -/
theorem triple_independent {t : ℝ} (ht : 0<t) (inf : (accumulated t).Infinite)
    (a b c : ℕ+) (ab : energy a ≠ energy b) (ac : energy a ≠ energy c) (bc : energy b ≠ energy c) :
    LinearIndependent ℚ ![shellPower t a,shellPower t b,shellPower t c] := by
  apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
  apply Fintype.linearIndependent_iff.mpr
  intro g zero i
  have sum : (g 0 : ℝ)*shellPower t a+(g 1 : ℝ)*shellPower t b+(g 2 : ℝ)*shellPower t c=0 := by
    simpa only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,zsmul_eq_mul] using zero
  have vanish : ¬(g 0 ≠ 0 ∨ g 1 ≠ 0 ∨ g 2 ≠ 0) := fun some =>
    inf (nonzero_relation_finite ht a b c ab ac bc _ _ _ some sum)
  push Not at vanish
  fin_cases i
  exacts [vanish.1,vanish.2.1,vanish.2.2]

#print axioms triple_independent

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
