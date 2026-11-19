import GaloisForLFunctions.FiniteFreeProbability.JensenSectorTheorem

/-!
# Exact Jensen sector of a symmetric quartet

The roots z, conjugate z, -z and -conjugate z give an even symbol.
After applying it to a monomial, removing the forced zero power leaves
a quadratic in the squared coordinate. Testing that quadratic jointly
slightly enlarges the sector obtained by testing the two pairs separately.
-/

open Polynomial
namespace FiniteFreeProbability

noncomputable section

/-- Even quartic with its quadratic coefficient written as minus twice the middle parameter. -/
private def biquad (A B D : ℝ) : ℝ[X] := C A * X^4 - C (2*B)*X^2 + C D

private theorem even_quadratic_splits {u : ℝ} (hu : 0 ≤ u) :
    ((X : ℝ[X])^2 - C u).Splits := by
  have he : (X : ℝ[X])^2-C u = (X-C (Real.sqrt u))*(X+C (Real.sqrt u)) := by
    rw [show u = Real.sqrt u ^ 2 from (Real.sq_sqrt hu).symm, map_pow]
    ring
  rw [he]
  exact (Splits.X_sub_C _).mul (by simpa only [sub_neg_eq_add, C_neg, sub_neg_eq_add] using
    (Splits.X_sub_C (-Real.sqrt u)))

/-- For positive leading and constant coefficients a biquadratic splits exactly
when its two squared roots are positive and real. -/
private theorem biquad_splits_iff {A B D : ℝ} (hA : 0 < A) (hD : 0 < D) :
    (biquad A B D).Splits ↔ 0 < B ∧ A*D ≤ B^2 := by
  constructor
  · intro hs
    have hd : (biquad A B D).degree ≠ 0 := by
      have htop := le_natDegree_of_ne_zero (show (biquad A B D).coeff 4 ≠ 0 by simpa [biquad] using hA.ne')
      intro hzero
      have hz := natDegree_eq_zero_of_degree_le_zero hzero.le
      omega
    obtain ⟨x,hx⟩ := hs.exists_eval_eq_zero hd
    have he : A*x^4-2*B*x^2+D = 0 := by simpa only [biquad, eval_add, eval_sub, eval_mul,
      eval_C, eval_pow, eval_X] using hx
    constructor
    · by_contra! hn
      nlinarith only [he,hD, mul_nonneg hA.le (pow_nonneg (sq_nonneg x) 2),
        mul_nonpos_of_nonpos_of_nonneg hn (sq_nonneg x)]
    · have H : B^2-A*D = (A*x^2-B)^2 := by linear_combination -A*he
      linarith only [H, sq_nonneg (A*x^2-B)]
  · rintro ⟨hB,hdisc⟩
    let v := Real.sqrt (B^2-A*D)
    have hv : v^2 = B^2-A*D := Real.sq_sqrt (sub_nonneg.mpr hdisc)
    have hvB : v ≤ B := by nlinarith only [hv,mul_pos hA hD,hB,Real.sqrt_nonneg (B^2-A*D)]
    let t := (B-v)/A
    let u := (B+v)/A
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hvB) hA.le
    have hu : 0 ≤ u := div_nonneg (add_nonneg hB.le (Real.sqrt_nonneg _)) hA.le
    have hs : A*(t+u) = 2*B := by dsimp [t,u]; field_simp; ring
    have hp : A*t*u = D := by
      dsimp [t,u]; field_simp; nlinarith only [hv]
    have he : biquad A B D = C A*((X^2-C t)*(X^2-C u)) := by
      rw [biquad, ← hs, ← hp, map_add, map_mul, map_mul, map_mul]
      ring
    rw [he]
    exact ((even_quadratic_splits ht).mul (even_quadratic_splits hu)).C_mul _

/-- Real quartet symbol with squared root w and its conjugate. -/
def squaredPairSymbol (w : ℂ) : ℝ[X] := biquad 1 w.re (Complex.normSq w)

private theorem diffOp_biquad (A B D : ℝ) (k : ℕ) :
    diffOp (biquad A B D) (X^(k+4)) = X^k * biquad D
      (B * ((k : ℝ)+4)*((k : ℝ)+3))
      (A * ((k : ℝ)+4)*((k : ℝ)+3)*((k : ℝ)+2)*((k : ℝ)+1)) := by
  have hdeg : (biquad A B D).natDegree ≤ 4 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp [biquad, coeff_X_pow, show j ≠ 4 by omega, show j ≠ 2 by omega, show j ≠ 0 by omega,
      show 4 ≠ j by omega, show 2 ≠ j by omega, show 0 ≠ j by omega, coeff_C]
  rw [diffOp_eq_sum _ _ (n := 5) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iterate_derivative_X_pow_eq_C_mul]
  norm_num [biquad, coeff_X_pow, Nat.descFactorial_succ, Nat.cast_succ, map_mul, pow_add]
  <;> ring

/-- The exact sector for a quartet, in the squared spectral coordinate. -/
def InSquaredJensenSector (d : ℕ) (w : ℂ) : Prop :=
  0 < w.re ∧ ((d : ℝ)-2)*((d : ℝ)-3)*Complex.normSq w ≤ (d : ℝ)*((d : ℝ)-1)*w.re^2

/-- For every degree at least four the squared-coordinate sector is necessary and
sufficient for the complete quartet to have a real-rooted Jensen polynomial. -/
theorem squaredPairSymbol_splits_iff (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (diffOp (squaredPairSymbol w) (X^(k+4))).Splits ↔ InSquaredJensenSector (k+4) w := by
  let A := (k : ℝ)+4
  let B := (k : ℝ)+3
  let D := (k : ℝ)+2
  let E := (k : ℝ)+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hN := Complex.normSq_pos.mpr hw
  have Hpos : 0 < A*B := mul_pos hA hB
  rw [squaredPairSymbol, diffOp_biquad, one_mul]
  change (X^k * biquad (Complex.normSq w) (w.re*A*B) (A*B*D*E)).Splits ↔ _
  have hn : biquad (Complex.normSq w) (w.re*A*B) (A*B*D*E) ≠ 0 := by
    intro hz
    have he := congrArg (fun q : ℝ[X] => q.coeff 4) hz
    simpa [biquad, hN.ne'] using he
  rw [splits_mul (pow_ne_zero _ X_ne_zero) hn, and_iff_right (Splits.X_pow k),
    biquad_splits_iff hN (by positivity), InSquaredJensenSector]
  push_cast
  change (0 < w.re*A*B ∧ _) ↔ 0 < w.re ∧ _
  have hh : (k : ℝ)+4-1 = B := by dsimp [B]; ring
  have hh' : (k : ℝ)+4-2 = D := by dsimp [D]; ring
  have hh'' : (k : ℝ)+4-3 = E := by dsimp [E]; ring
  rw [hh,hh',hh'', mul_pos_iff_of_pos_right hB, mul_pos_iff_of_pos_right hA]
  apply and_congr_right
  intro _
  change Complex.normSq w*(A*B*D*E) ≤ (w.re*A*B)^2 ↔ D*E*Complex.normSq w ≤ A*B*w.re^2
  rw [show Complex.normSq w*(A*B*D*E) = (D*E*Complex.normSq w)*(A*B) by ring,
    show (w.re*A*B)^2 = (A*B*w.re^2)*(A*B) by ring, mul_le_mul_iff_left₀ Hpos]

/-- A square of an actual spectral coordinate has the explicit quartet test. -/
theorem squaredJensenSector_square (d : ℕ) (z : ℂ) :
    InSquaredJensenSector d (z^2) ↔ z.im^2 < z.re^2 ∧
      ((d : ℝ)-2)*((d : ℝ)-3)*(z.re^2+z.im^2)^2 ≤
        (d : ℝ)*((d : ℝ)-1)*(z.re^2-z.im^2)^2 := by
  simp only [InSquaredJensenSector, map_pow, Complex.sq_re, Complex.normSq_apply]
  rw [← sq, ← sq, sub_pos]

#print axioms squaredPairSymbol_splits_iff
#print axioms squaredJensenSector_square

end

end FiniteFreeProbability
