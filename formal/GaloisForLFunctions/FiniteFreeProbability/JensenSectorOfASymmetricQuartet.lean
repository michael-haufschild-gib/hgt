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
    calc
      _ = X^2-(C (Real.sqrt u))^2 := by rw [← map_pow, Real.sq_sqrt hu]
      _ = _ := by ring
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
  have hre : (z^2).re = z.re^2-z.im^2 := by simp only [sq, Complex.mul_re]
  rw [InSquaredJensenSector, hre, map_pow, Complex.normSq_apply, sub_pos]
  simp only [sq]

private theorem irreducible_factor {p f : ℝ[X]} (hi : Irreducible p) (hf : ¬ IsUnit f)
    (hd : f ∣ p) : ∃ c : ℝ, p = C c*f := by
  obtain ⟨g,hg⟩ := hd
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.mp ((hi.isUnit_or_isUnit hg).resolve_left hf)
  exact ⟨c, by rw [hg, ← hc, mul_comm]⟩

private theorem expand_pair (w : ℂ) : expand ℝ 2 (pairSymbol w) = squaredPairSymbol w := by
  simp only [pairSymbol, map_add, map_sub, map_mul, map_pow, expand_C, expand_X, squaredPairSymbol,
    biquad, C_1, one_mul]
  ring

private theorem irreducible_expand_splits (k : ℕ) {p : ℝ[X]} (hi : Irreducible p)
    (hsec : ∀ w : ℂ, aeval w p = 0 → InSquaredJensenSector (k+4) w) :
    (diffOp (expand ℝ 2 p) (X^(k+4))).Splits := by
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p (degree_pos_of_irreducible hi).ne'
  have h := hsec w hw
  by_cases hr : w.im = 0
  · have hw' : (w.re : ℂ) = w := Complex.ext rfl (by simpa using hr.symm)
    have hval : p.IsRoot w.re := by
      have he : (p.map Complex.ofRealHom).eval (w.re : ℂ) = 0 := by
        rw [hw']
        exact (eval_map_algebraMap p w).trans hw
      rw [eval_map_apply] at he
      exact Complex.ofReal_injective he
    obtain ⟨c,hc⟩ := irreducible_factor hi (not_isUnit_X_sub_C w.re) (dvd_iff_isRoot.mpr hval)
    rw [hc, map_mul, expand_C, map_sub, expand_X, expand_C, diffOp_C_mul_left]
    apply Splits.C_mul
    have h₀ : ((X : ℝ[X])^2-C w.re).coeff 0 ≠ 0 := by simp [h.1.ne']
    have hdeg : ((X : ℝ[X])^2-C w.re).natDegree ≤ 2 :=
      (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow_le _) (by simp))
    apply (splits_diffOp_X_pow_iff_of_natDegree_le_two hdeg h₀ (k+2)).mpr
    simp only [coeff_sub, coeff_C, coeff_X_pow, ↓reduceIte, sub_zero, zero_sub, sub_self,
      zero_pow (by decide : 2 ≠ 0), mul_zero, mul_one]
    have hpos := h.1
    positivity
  · have hd : pairSymbol w ∣ p := by
      simpa only [pairSymbol, Complex.normSq_eq_norm_sq] using
        p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hw hr
    have hnot : ¬ IsUnit (pairSymbol w) := by
      rintro hu
      obtain ⟨c,-,hc⟩ := Polynomial.isUnit_iff.mp hu
      have he := congrArg (fun q : ℝ[X] => q.coeff 2) hc
      simpa [pairSymbol] using he
    obtain ⟨c,hc⟩ := irreducible_factor hi hnot hd
    rw [hc, map_mul, expand_C, expand_pair, diffOp_C_mul_left]
    exact ((squaredPairSymbol_splits_iff k (fun he => by simp [he] at hr)).mpr h).C_mul _

/-- The signed-pair sector suffices for arbitrary even symbols. Each irreducible
factor of the polynomial in the squared coordinate contributes either one real
pair or one full quartet, and Walsh convolution multiplies the admissible symbols. -/
theorem splits_diffOp_expand_two_of_squared_sector (k : ℕ) (p : ℝ[X]) (hp : p.coeff 0 ≠ 0)
    (hsec : ∀ w : ℂ, aeval w p = 0 → InSquaredJensenSector (k+4) w) :
    (diffOp (expand ℝ 2 p) (X^(k+4))).Splits := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at hp
  | unit u hu =>
    obtain ⟨c,-,rfl⟩ := Polynomial.isUnit_iff.mp hu
    rw [expand_C]
    have he : diffOp (C c) (X^(k+4)) = C c*X^(k+4) := by
      simpa [diffOp] using diffOp_C_mul_left c 1 ((X : ℝ[X])^(k+4))
    rw [he]
    exact (Splits.X_pow _).C_mul _
  | mul a i _ hi ih =>
    rw [mul_coeff_zero] at hp
    have hi0 : i.coeff 0 ≠ 0 := left_ne_zero_of_mul hp
    have ha0 : a.coeff 0 ≠ 0 := right_ne_zero_of_mul hp
    have hroot (w : ℂ) : aeval w i = 0 ∨ aeval w a = 0 → InSquaredJensenSector (k+4) w := by
      intro hw
      apply hsec w
      rw [map_mul, mul_eq_zero]
      exact hw
    rw [map_mul]
    apply splits_diffOp_mul_X_pow
    · simpa [coeff_expand (by decide : 0 < 2)] using hi0
    · simpa [coeff_expand (by decide : 0 < 2)] using ha0
    · exact irreducible_expand_splits k hi fun w hw => hroot w (Or.inl hw)
    · exact ih ha0 fun w hw => hroot w (Or.inr hw)

#print axioms splits_diffOp_expand_two_of_squared_sector
#print axioms squaredPairSymbol_splits_iff
#print axioms squaredJensenSector_square

end

end FiniteFreeProbability
