import GaloisForLFunctions.RHTower.RouteEFixedOrderTwoGradeOverpayment

/-!
# Uniform cofactor-cutoff stability of the nonlinear source

Extending the cofactor cutoff of the entire odd-numerator adjacent-pair block
below prime `q` costs at most `6/q` at critical order. Literal coefficients
`μ(a)μ(qd)` and the full nonlinear kernel are retained. The associated signed
moment aggregate has cofactor-completion error at most `3A` when `A < q`.
These bounds control cofactor completion, not the original signed blocks or RH.
-/

namespace RHTower
noncomputable section
open scoped BigOperators

private theorem abs_sum_cutoff_tail_le
    (f : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ d : ℕ, 1 ≤ d → |f d| ≤ C / (d : ℝ) ^ (2 : ℕ))
    {q Q : ℕ} (hq : 2 ≤ q) (hQ : q ≤ Q) :
    |(∑ d ∈ Finset.Ioo 0 Q, f d) - ∑ d ∈ Finset.Ioo 0 q, f d| ≤
      C / ((q - 1 : ℕ) : ℝ) := by
  have hset : Finset.Ioo 0 Q = Finset.Ioo 0 q ∪ Finset.Ioo (q - 1) Q := by
    ext d
    simp only [Finset.mem_union, Finset.mem_Ioo]
    omega
  have hdisj : Disjoint (Finset.Ioo 0 q) (Finset.Ioo (q - 1) Q) := by
    apply Finset.disjoint_left.mpr
    intro d hd he
    simp only [Finset.mem_Ioo] at hd he
    omega
  rw [hset, Finset.sum_union hdisj, add_sub_cancel_left]
  calc
    _ ≤ ∑ d ∈ Finset.Ioo (q - 1) Q, |f d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioo (q - 1) Q, C / (d : ℝ) ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact hf d (by have := (Finset.mem_Ioo.mp hd).1; omega)
    _ = C * ∑ d ∈ Finset.Ioo (q - 1) Q, 1 / (d : ℝ) ^ (2 : ℕ) := by
      simp only [div_eq_mul_inv, one_mul, Finset.mul_sum]
    _ ≤ C * (1 / ((q - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (routeE_invSqTail_Ioo_le (q - 1) Q (by omega)) hC
    _ = _ := by ring

/-- A denominator-cofactor tail, uniformly in the numerator and exponent. -/
theorem routeE_coprimeMobiusMoment_cutoff_tail
    {s : ℝ} (hs : 2 ≤ s) (a : ℕ) {q Q : ℕ} (hq : 2 ≤ q) (hQ : q ≤ Q) :
    |routeE_coprimeMobiusMoment s a Q - routeE_coprimeMobiusMoment s a q| ≤
      1 / ((q - 1 : ℕ) : ℝ) := by
  unfold routeE_coprimeMobiusMoment
  exact abs_sum_cutoff_tail_le _ (by norm_num : (0 : ℝ) ≤ 1)
    (fun d hd => routeE_momentTerm_abs_le_invSq hs a hd) hq hQ

/-- The signed odd-core moment appearing in completed adjacent-pair linearization. -/
def routeE_completedCoreMomentSum (s : ℝ) (A q : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Icc 1 A).filter Odd,
    (ArithmeticFunction.moebius a : ℝ) * (a : ℝ) *
      (2 * routeE_coprimeMobiusMoment s (2 * a) q - routeE_coprimeMobiusMoment s a q)

/-- Each weighted core changes by at most three once its cofactor cutoff exceeds it. -/
private theorem completedCoreMoment_term_tail
    {s : ℝ} (hs : 2 ≤ s) {a q Q : ℕ} (hq : 2 ≤ q) (haq : a < q) (hQ : q ≤ Q) :
    |(ArithmeticFunction.moebius a : ℝ) * (a : ℝ) *
        (2 * routeE_coprimeMobiusMoment s (2 * a) Q - routeE_coprimeMobiusMoment s a Q) -
      (ArithmeticFunction.moebius a : ℝ) * (a : ℝ) *
        (2 * routeE_coprimeMobiusMoment s (2 * a) q - routeE_coprimeMobiusMoment s a q)| ≤ 3 := by
  let b : ℝ := ((q - 1 : ℕ) : ℝ)
  have hb : 0 < b := by dsimp [b]; exact_mod_cast (show 0 < q - 1 by omega)
  have hab : (a : ℝ) ≤ b := by
    dsimp [b]
    exact_mod_cast (show a ≤ q - 1 by omega)
  have h1 := abs_le.mp (routeE_coprimeMobiusMoment_cutoff_tail hs a hq hQ)
  have h2 := abs_le.mp (routeE_coprimeMobiusMoment_cutoff_tail hs (2 * a) hq hQ)
  have hbracket : |(2 * routeE_coprimeMobiusMoment s (2 * a) Q -
        routeE_coprimeMobiusMoment s a Q) -
      (2 * routeE_coprimeMobiusMoment s (2 * a) q -
        routeE_coprimeMobiusMoment s a q)| ≤ 3 / b := by
    dsimp [b]
    simp only [div_eq_mul_inv, one_mul] at h1 h2 ⊢
    apply abs_le.mpr
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hmu : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
  have hweight : |(ArithmeticFunction.moebius a : ℝ) * (a : ℝ)| ≤ (a : ℝ) := by
    have haabs : |(a : ℝ)| = (a : ℝ) := abs_of_nonneg (Nat.cast_nonneg a)
    rw [abs_mul, haabs]
    simpa using mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  rw [← mul_sub, abs_mul]
  calc
    _ ≤ (a : ℝ) * (3 / b) :=
      mul_le_mul hweight hbracket (abs_nonneg _) (Nat.cast_nonneg a)
    _ ≤ b * (3 / b) := mul_le_mul_of_nonneg_right hab (by positivity)
    _ = 3 := by field_simp

/-- Cofactor completion changes the whole signed core sum by only a linear error.
The estimate is uniform in every later cofactor cutoff, with no cancellation premise. -/
theorem routeE_completedCoreMomentSum_cofactor_stability
    {s : ℝ} (hs : 2 ≤ s) (A : ℕ) {q Q : ℕ} (hAq : A < q) (hQ : q ≤ Q) :
    |routeE_completedCoreMomentSum s A Q - routeE_completedCoreMomentSum s A q| ≤
      3 * (A : ℝ) := by
  by_cases hA : A = 0
  · simp [hA, routeE_completedCoreMomentSum]
  have hq : 2 ≤ q := by omega
  unfold routeE_completedCoreMomentSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ (Finset.Icc 1 A).filter Odd,
        |(ArithmeticFunction.moebius a : ℝ) * (a : ℝ) *
            (2 * routeE_coprimeMobiusMoment s (2 * a) Q - routeE_coprimeMobiusMoment s a Q) -
          (ArithmeticFunction.moebius a : ℝ) * (a : ℝ) *
            (2 * routeE_coprimeMobiusMoment s (2 * a) q - routeE_coprimeMobiusMoment s a q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ (Finset.Icc 1 A).filter Odd, (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have haA := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
      exact completedCoreMoment_term_tail hs hq (haA.trans_lt hAq) hQ
    _ ≤ 3 * (A : ℝ) := by
      have hcard : (((Finset.Icc 1 A).filter Odd).card : ℝ) ≤ (A : ℝ) := by
        exact_mod_cast (Finset.card_filter_le (Finset.Icc 1 A) Odd).trans (by simp)
      simp only [Finset.sum_const, nsmul_eq_mul]
      linarith


/-- The literal nonlinear numerator fibre with a freely extended cofactor cutoff.
The coefficient remains `μ(a)μ(qd)`, including when `d` is divisible by `q`. -/
def routeE_integerNumeratorCutoffFibre (r : ℝ) (a : ℕ) (q : Nat.Primes) (Q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioo 0 Q,
    (if Nat.Coprime a d then
      (ArithmeticFunction.moebius a : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ) else 0) *
      routeEFixedOrderDifference r (a : ℝ) ((q : ℝ) * (d : ℝ))

/-- At the physical cutoff this is exactly the existing source fibre. -/
theorem routeE_integerNumeratorCutoffFibre_self (r : ℝ) (a : ℕ) (q : Nat.Primes) :
    routeE_integerNumeratorCutoffFibre r a q (q : ℕ) =
      routeEFixedOrderIntegerNumeratorFibre r a q := rfl

/-- Nonlinear cofactor completion has a uniform inverse-square tail. -/
theorem routeE_integerNumeratorCutoffFibre_tail
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (a : ℕ) (q : Nat.Primes)
    {Q : ℕ} (hQ : (q : ℕ) ≤ Q) :
    |routeE_integerNumeratorCutoffFibre r a q Q -
      routeE_integerNumeratorCutoffFibre r a q (q : ℕ)| ≤
      2 * (a : ℝ) * (q : ℝ) ^ (-(r + 1)) / (((q : ℕ) - 1 : ℕ) : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  have ht : 0 ≤ (q : ℝ) ^ (-(r + 1)) := Real.rpow_nonneg hq0.le _
  unfold routeE_integerNumeratorCutoffFibre
  apply abs_sum_cutoff_tail_le _ (by positivity) _ q.property.two_le hQ
  intro d hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hqd : 0 < (q : ℝ) * (d : ℝ) := mul_pos hq0 hd0
  have hK0 : 0 ≤ routeEFixedOrderDifference r (a : ℝ) ((q : ℝ) * (d : ℝ)) := by
    unfold routeEFixedOrderDifference
    apply sub_nonneg.mpr
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)])
    linarith
  have hK := sub_nonneg.mp
    (routeEFixedOrderDifference_linearization hr hr2 (Nat.cast_nonneg a) hqd).1
  have hdPow : (d : ℝ) ^ (-(r + 1)) ≤ 1 / (d : ℝ) ^ (2 : ℕ) := by
    calc
      _ ≤ (d : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
      _ = _ := by rw [Real.rpow_neg hd0.le, Real.rpow_ofNat]; ring
  have hcoef := routeE_integer_coeff_bound a q d
  calc
    _ = |if Nat.Coprime a d then
        (ArithmeticFunction.moebius a : ℝ) *
          (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ) else 0| *
        routeEFixedOrderDifference r (a : ℝ) ((q : ℝ) * (d : ℝ)) := by
      rw [abs_mul, abs_of_nonneg hK0]
    _ ≤ routeEFixedOrderDifference r (a : ℝ) ((q : ℝ) * (d : ℝ)) := by
      simpa using mul_le_mul_of_nonneg_right hcoef hK0
    _ ≤ r * (a : ℝ) * ((q : ℝ) * (d : ℝ)) ^ (-(r + 1)) := hK
    _ = (r * (a : ℝ) * (q : ℝ) ^ (-(r + 1))) * (d : ℝ) ^ (-(r + 1)) := by
      rw [Real.mul_rpow hq0.le hd0.le]
      ring
    _ ≤ (2 * (a : ℝ) * (q : ℝ) ^ (-(r + 1))) * (1 / (d : ℝ) ^ (2 : ℕ)) := by
      apply mul_le_mul _ hdPow (Real.rpow_nonneg hd0.le _) (by positivity)
      have := mul_le_mul_of_nonneg_right hr2
        (mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) ht)
      nlinarith only [this]
    _ = _ := by ring

/-- All odd-core adjacent pairs below one numerator cutoff, with literal coefficients. -/
def routeE_integerPairCutoffBlock (r : ℝ) (A : ℕ) (q : Nat.Primes) (Q : ℕ) : ℝ :=
  ∑ a ∈ (Finset.Icc 1 A).filter Odd,
    (routeE_integerNumeratorCutoffFibre r a q Q +
      routeE_integerNumeratorCutoffFibre r (2 * a) q Q)

/-- The entire nonlinear pair block has linear normalized cofactor error. -/
theorem routeE_integerPairCutoffBlock_stability
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (A : ℕ) (q : Nat.Primes)
    (hAq : A < (q : ℕ)) {Q : ℕ} (hQ : (q : ℕ) ≤ Q) :
    |routeE_integerPairCutoffBlock r A q Q -
      routeE_integerPairCutoffBlock r A q (q : ℕ)| ≤
      6 * (A : ℝ) * (q : ℝ) ^ (-(r + 1)) := by
  let t : ℝ := (q : ℝ) ^ (-(r + 1))
  let b : ℝ := (((q : ℕ) - 1 : ℕ) : ℝ)
  have hq2 := q.property.two_le
  have hb : 0 < b := by dsimp [b]; exact_mod_cast (show 0 < (q : ℕ) - 1 by omega)
  have ht : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold routeE_integerPairCutoffBlock
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ (Finset.Icc 1 A).filter Odd,
        |(routeE_integerNumeratorCutoffFibre r a q Q +
            routeE_integerNumeratorCutoffFibre r (2 * a) q Q) -
          (routeE_integerNumeratorCutoffFibre r a q (q : ℕ) +
            routeE_integerNumeratorCutoffFibre r (2 * a) q (q : ℕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ (Finset.Icc 1 A).filter Odd, (6 * t) := by
      apply Finset.sum_le_sum
      intro a ha
      have haA := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
      have hab : (a : ℝ) ≤ b := by
        dsimp [b]
        exact_mod_cast (show a ≤ (q : ℕ) - 1 by omega)
      have h1 := abs_le.mp (routeE_integerNumeratorCutoffFibre_tail hr hr2 a q hQ)
      have h2 := abs_le.mp (routeE_integerNumeratorCutoffFibre_tail hr hr2 (2 * a) q hQ)
      change -(2 * (a : ℝ) * t / b) ≤ _ ∧ _ ≤ 2 * (a : ℝ) * t / b at h1
      have h2' : -(4 * (a : ℝ) * t / b) ≤
          routeE_integerNumeratorCutoffFibre r (2 * a) q Q -
            routeE_integerNumeratorCutoffFibre r (2 * a) q (q : ℕ) ∧
          routeE_integerNumeratorCutoffFibre r (2 * a) q Q -
            routeE_integerNumeratorCutoffFibre r (2 * a) q (q : ℕ) ≤
          4 * (a : ℝ) * t / b := by
        change -(2 * ((2 * a : ℕ) : ℝ) * t / b) ≤ _ ∧
          _ ≤ 2 * ((2 * a : ℕ) : ℝ) * t / b at h2
        have hcast : (2 : ℝ) * ((2 * a : ℕ) : ℝ) = 4 * (a : ℝ) := by
          push_cast
          ring
        simpa only [hcast] using h2
      have hscale : 6 * (a : ℝ) * t / b ≤ 6 * t := by
        apply (div_le_iff₀ hb).mpr
        nlinarith [mul_le_mul_of_nonneg_right hab ht]
      simp only [div_eq_mul_inv] at h1 h2' hscale
      apply abs_le.mpr
      constructor <;> nlinarith only [h1.1, h1.2, h2'.1, h2'.2, hscale]
    _ ≤ 6 * (A : ℝ) * (q : ℝ) ^ (-(r + 1)) := by
      have hcard : (((Finset.Icc 1 A).filter Odd).card : ℝ) ≤ (A : ℝ) := by
        exact_mod_cast (Finset.card_filter_le (Finset.Icc 1 A) Odd).trans (by simp)
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp [t] at ht ⊢
      nlinarith only [mul_le_mul_of_nonneg_right hcard ht]

/-- At critical order the complete numerator block costs at most `6/q`
to extend to any cofactor cutoff. No Möbius-cancellation estimate is used. -/
theorem routeE_integerPairCutoffBlock_critical_tail
    (q : Nat.Primes) {Q : ℕ} (hQ : (q : ℕ) ≤ Q) :
    |routeE_integerPairCutoffBlock 1 ((q : ℕ) - 1) q Q -
      routeE_integerPairCutoffBlock 1 ((q : ℕ) - 1) q (q : ℕ)| ≤ 6 / (q : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  have hqnat := q.property.pos
  have h := routeE_integerPairCutoffBlock_stability (r := 1) (by norm_num) (by norm_num)
    ((q : ℕ) - 1) q (by omega) hQ
  have hle : (((q : ℕ) - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.sub_le (q : ℕ) 1
  refine h.trans ?_
  rw [show -((1 : ℝ) + 1) = -2 by ring, Real.rpow_neg hq0.le, Real.rpow_ofNat]
  apply (le_div_iff₀ hq0).mpr
  field_simp
  nlinarith

end
end RHTower
