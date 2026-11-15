import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerWordProbability

/-!
# Gauss word lengths, cylinder widths, and bounded-digit traces

The actual Gauss-word denominator probabilities telescope exactly after a
finite digit cutoff. Restricting all digits to `1,…,n` leaves at most
`(n/(n+1))^k` mass at word length `k`. The same estimate controls the sum
of reciprocal denominator squares, with factor two. The probabilities equal
the distances between the actual inverse-branch endpoints. Matrix row sums
give the logarithmic word-length bound.

These are the estimates of Lemma 4.2 and the unweighted cylinder contraction
underlying Lemma 4.3 of Gaster–Martínez-Granado–Simon, applied to the existing
Gauss word matrices. The finite-digit loss also makes the full even-word
trace family absolutely summable at exponent two.
-/

open Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundedDigits
noncomputable section

/-- Digits are stored one below their continued-fraction value. -/
def word {n k : ℕ} (a : Fin k → Fin n) : Word k := fun i => a i

/-- Total cylinder probability when every digit is at most `n`. -/
def mass (n k : ℕ) : ℝ := ∑ a : Fin k → Fin n, probability k (word a)

/-- Uniform mass retained by one bounded-digit step. -/
def retention (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

private theorem finite_successor_sum {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / ((c + d * (i + 1)) * (c + d * (i + 2)))) =
      (n : ℝ) / ((c + d) * (c + d * (n + 1))) := by
  have hcd : c + d ≠ 0 := (add_pos_of_nonneg_of_pos hc hd).ne'
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : c + d * ((n : ℝ) + 1) ≠ 0 := (by positivity : 0 < c + d * ((n : ℝ) + 1)).ne'
      have h2 : c + d * ((n : ℝ) + 2) ≠ 0 := (by positivity : 0 < c + d * ((n : ℝ) + 2)).ne'
      push_cast
      field_simp [hcd, h1, h2]
      ring

/-- Exact cutoff law for the successor probabilities of any actual Gauss word. -/
theorem successor_mass (n k : ℕ) (a : Word k) :
    (∑ i : Fin n, probability (k + 1) (Fin.cons (i : ℕ) a)) =
      (n : ℝ) /
        (((wordMatrix k a 1 0 : ℝ) + wordMatrix k a 1 1) *
          (wordMatrix k a 1 0 + wordMatrix k a 1 1 * ((n : ℝ) + 1))) := by
  have hd : (0 : ℝ) < wordMatrix k a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row k a).2
  have h := finite_successor_sum (Nat.cast_nonneg (wordMatrix k a 1 0)) hd n
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => probability (k + 1) (Fin.cons i a)) n]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [probability, wordMatrix_col_zero, wordMatrix_col_one,
    Fin.tail_cons, Fin.cons_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  congr 2
  ring

/-- Every parent word retains at most the uniform digit-cutoff fraction. -/
theorem successor_mass_le (n k : ℕ) (a : Word k) :
    (∑ i : Fin n, probability (k + 1) (Fin.cons (i : ℕ) a)) ≤
      retention n * probability k a := by
  have hd : (0 : ℝ) < wordMatrix k a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row k a).2
  have hc : (0 : ℝ) ≤ wordMatrix k a 1 0 := Nat.cast_nonneg _
  have hcd : (0 : ℝ) < wordMatrix k a 1 0 + wordMatrix k a 1 1 :=
    add_pos_of_nonneg_of_pos hc hd
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm : (n : ℝ) / (wordMatrix k a 1 0 + wordMatrix k a 1 1 * ((n : ℝ) + 1)) ≤
      (n : ℝ) / (wordMatrix k a 1 1 * ((n : ℝ) + 1)) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg n) (mul_pos hd hn) (le_add_of_nonneg_left hc)
  rw [successor_mass]
  calc
    _ = (1 / ((wordMatrix k a 1 0 : ℝ) + wordMatrix k a 1 1)) *
        ((n : ℝ) / (wordMatrix k a 1 0 + wordMatrix k a 1 1 * ((n : ℝ) + 1))) := by
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ ≤ (1 / ((wordMatrix k a 1 0 : ℝ) + wordMatrix k a 1 1)) *
        ((n : ℝ) / (wordMatrix k a 1 1 * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = retention n * probability k a := by
      rw [retention, probability]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring

private def splitWord (n k : ℕ) : (Fin (k + 1) → Fin n) ≃ ((Fin k → Fin n) × Fin n) where
  toFun a := (Fin.tail a, a 0)
  invFun p := Fin.cons p.2 p.1
  left_inv a := by simp
  right_inv p := by cases p; simp

private theorem mass_succ (n k : ℕ) :
    mass n (k + 1) = ∑ a : Fin k → Fin n, ∑ i : Fin n,
      probability (k + 1) (Fin.cons (i : ℕ) (word a)) := by
  rw [mass, ← (splitWord n k).symm.sum_comp
    (fun a => probability (k + 1) (word a)), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  refine Fin.cases ?_ (fun l => ?_) j <;> rfl

/-- Every bounded alphabet loses a fixed positive fraction of mass at each step. -/
theorem mass_le (n k : ℕ) : mass n k ≤ retention n ^ k := by
  induction k with
  | zero => simp [mass, probability, wordMatrix]
  | succ k ih =>
      rw [mass_succ]
      calc
        _ ≤ ∑ a : Fin k → Fin n, retention n * probability k (word a) :=
          Finset.sum_le_sum (fun a _ => successor_mass_le n k (word a))
        _ = retention n * mass n k := by rw [← Finset.mul_sum, mass]
        _ ≤ retention n * retention n ^ k :=
          mul_le_mul_of_nonneg_left ih (by unfold retention; positivity)
        _ = retention n ^ (k + 1) := by rw [pow_succ, mul_comm]

/-- The denominator inverse square is at most twice its exact word probability. -/
theorem denominator_inv_sq_le (k : ℕ) (a : Word k) :
    (wordMatrix k a 1 1 : ℝ)⁻¹ ^ 2 ≤ 2 * probability k a := by
  have hd : (0 : ℝ) < wordMatrix k a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row k a).2
  have hc : (0 : ℝ) ≤ wordMatrix k a 1 0 := Nat.cast_nonneg _
  have hcd : (wordMatrix k a 1 0 : ℝ) ≤ wordMatrix k a 1 1 :=
    by exact_mod_cast (wordMatrix_denominator_row k a).1
  have hsum : (0 : ℝ) < wordMatrix k a 1 0 + wordMatrix k a 1 1 :=
    add_pos_of_nonneg_of_pos hc hd
  rw [probability, mul_one_div]
  apply (le_div_iff₀ (mul_pos hd hsum)).mpr
  field_simp
  nlinarith only [hcd, hd]

/-- Bounded-digit denominator inverse squares have geometric decay in word length. -/
theorem sum_denominator_inv_sq_le (n k : ℕ) :
    (∑ a : Fin k → Fin n, (wordMatrix k (word a) 1 1 : ℝ)⁻¹ ^ 2) ≤
      2 * retention n ^ k := by
  calc
    _ ≤ ∑ a : Fin k → Fin n, 2 * probability k (word a) :=
      Finset.sum_le_sum (fun a _ => denominator_inv_sq_le k (word a))
    _ = 2 * mass n k := by rw [← Finset.mul_sum, mass]
    _ ≤ 2 * retention n ^ k := mul_le_mul_of_nonneg_left (mass_le n k) (by norm_num)

/-- Every fixed finite digit alphabet has vanishing cylinder mass at infinite word length. -/
theorem mass_tendsto_zero (n : ℕ) : Tendsto (mass n) atTop (𝓝 0) := by
  have h0 : 0 ≤ retention n := by unfold retention; positivity
  have h1 : retention n < 1 := by
    rw [retention, div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    linarith
  exact squeeze_zero (fun k => Finset.sum_nonneg (fun a _ => by unfold probability; positivity))
    (mass_le n) (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1)

#print axioms successor_mass
#print axioms mass_le
#print axioms sum_denominator_inv_sq_le
#print axioms mass_tendsto_zero

end
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundedDigits


/-!
# Length and cylinder bounds for actual Gauss words

The row sums of the integral Gauss matrix are bounded by the product of
one plus each continued-fraction digit. Its expanding multiplier therefore
satisfies the logarithmic word-length estimate in Lemma 4.2 of
Gaster–Martínez-Granado–Simon.
-/

open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordLengthBounds
noncomputable section

/-- Every row sum of a Gauss word is bounded by the product of its digit row-sum bounds. -/
theorem wordMatrix_rowSum_le (k : ℕ) (a : Word k) (i : Fin 2) :
    wordMatrix k a i 0 + wordMatrix k a i 1 ≤ ∏ j : Fin k, (a j + 2) := by
  induction k with
  | zero => fin_cases i <;> simp [wordMatrix, Matrix.one_apply]
  | succ k ih =>
      rw [wordMatrix_col_zero, wordMatrix_col_one, Fin.prod_univ_succ]
      have hc : wordMatrix k (Fin.tail a) i 0 ≤
          wordMatrix k (Fin.tail a) i 0 * (a 0 + 2) :=
        Nat.le_mul_of_pos_right _ (by omega)
      calc
        _ = wordMatrix k (Fin.tail a) i 0 +
            wordMatrix k (Fin.tail a) i 1 * (a 0 + 2) := by ring
        _ ≤ wordMatrix k (Fin.tail a) i 0 * (a 0 + 2) +
            wordMatrix k (Fin.tail a) i 1 * (a 0 + 2) := Nat.add_le_add_right hc _
        _ = (wordMatrix k (Fin.tail a) i 0 + wordMatrix k (Fin.tail a) i 1) * (a 0 + 2) :=
          (add_mul _ _ _).symm
        _ ≤ (∏ j : Fin k, (Fin.tail a j + 2)) * (a 0 + 2) :=
          Nat.mul_le_mul_right _ (ih (Fin.tail a))
        _ = _ := by rw [mul_comm]; rfl

/-- The actual expanding multiplier is bounded by one plus each actual digit. -/
theorem wordMultiplier_le_product (k : ℕ) (a : Word (k + 1)) :
    wordMultiplier k a ≤ ∏ j : Fin (k + 1), ((a j : ℝ) + 2) := by
  have hx := (fixedPoint_real_interval k a).2.le
  have hc : (0 : ℝ) ≤ wordMatrix (k + 1) a 1 0 := Nat.cast_nonneg _
  have hrow : ((wordMatrix (k + 1) a 1 0 + wordMatrix (k + 1) a 1 1 : ℕ) : ℝ) ≤
      ∏ j : Fin (k + 1), ((a j : ℝ) + 2) := by
    exact_mod_cast wordMatrix_rowSum_le (k + 1) a 1
  unfold wordMultiplier
  calc
    _ ≤ (wordMatrix (k + 1) a 1 0 : ℝ) * 1 + wordMatrix (k + 1) a 1 1 :=
      add_le_add (mul_le_mul_of_nonneg_left hx hc) le_rfl
    _ ≤ _ := by simpa only [mul_one, Nat.cast_add] using hrow

/-- The geometric logarithmic length obeys the continued-fraction digit bound. -/
theorem logarithmic_length_le (k : ℕ) (a : Word (k + 1)) :
    2 * Real.log (wordMultiplier k a) ≤
      2 * ∑ j : Fin (k + 1), Real.log ((a j : ℝ) + 2) := by
  have hd : (0 : ℝ) < wordMatrix (k + 1) a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row (k + 1) a).2
  have hl : 0 < wordMultiplier k a := hd.trans_le (denominator_le_wordMultiplier k a)
  have h := Real.log_le_log hl (wordMultiplier_le_product k a)
  rw [Real.log_prod (fun j _ => by positivity)] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num)

#print axioms wordMatrix_rowSum_le
#print axioms wordMultiplier_le_product
#print axioms logarithmic_length_le

end
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordLengthBounds


open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCylinderEndpoints
noncomputable section

private theorem real_fraction (k : ℕ) (a : Word k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    realWordMap k a x =
      ((wordMatrix k a 0 0 : ℝ) * x + wordMatrix k a 0 1) /
        ((wordMatrix k a 1 0 : ℝ) * x + wordMatrix k a 1 1) := by
  have hz : (x : ℂ) ∈ GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff.outer := by
    rw [GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff.outer,
      Metric.mem_closedBall, dist_eq_norm]
    have hn : ‖(x : ℂ) - 1‖ = |x - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hn, abs_le]
    constructor <;> linarith only [hx.1, hx.2]
  have h := wordMap_eq_fraction k a hz
  rw [wordMap_ofReal] at h
  simp only [wordNumerator, wordDenominator] at h
  exact_mod_cast h

/-- The exact word probability is the distance between its two real inverse-branch endpoints. -/
theorem endpoint_distance_eq_probability (k : ℕ) (a : Word k) :
    |realWordMap k a 1 - realWordMap k a 0| = probability k a := by
  have hd : (0 : ℝ) < wordMatrix k a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row k a).2
  have hcd : (0 : ℝ) < wordMatrix k a 1 0 + wordMatrix k a 1 1 := by positivity
  have hdet : (wordMatrix k a 0 0 : ℝ) * wordMatrix k a 1 1 -
      (wordMatrix k a 0 1 : ℝ) * wordMatrix k a 1 0 = (-1 : ℝ) ^ k := by
    exact_mod_cast wordMatrix_unimodular k a
  rw [real_fraction k a (x := 1) (by constructor <;> norm_num),
    real_fraction k a (x := 0) (by constructor <;> norm_num)]
  simp only [mul_one, mul_zero, zero_add]
  have he :
      ((wordMatrix k a 0 0 : ℝ) + wordMatrix k a 0 1) /
        (wordMatrix k a 1 0 + wordMatrix k a 1 1) -
      (wordMatrix k a 0 1 : ℝ) / wordMatrix k a 1 1 =
      (-1 : ℝ) ^ k /
        ((wordMatrix k a 1 1 : ℝ) * (wordMatrix k a 1 0 + wordMatrix k a 1 1)) := by
    rw [← hdet]
    field_simp [hd.ne', hcd.ne']
    ring
  rw [he, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (mul_pos hd hcd)]
  rfl

#print axioms endpoint_distance_eq_probability

end
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCylinderEndpoints


open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundedDigits
noncomputable section

private theorem retention_bounds (n : ℕ) : 0 ≤ retention n ∧ retention n < 1 := by
  constructor
  · unfold retention
    positivity
  · rw [retention, div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    linarith

private theorem multiplier_inv_sq_le (k : ℕ) (a : Word (k + 1)) :
    (wordMultiplier k a)⁻¹ ^ 2 ≤ (wordMatrix (k + 1) a 1 1 : ℝ)⁻¹ ^ 2 := by
  have hd : (0 : ℝ) < wordMatrix (k + 1) a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row (k + 1) a).2
  have hdl := denominator_le_wordMultiplier k a
  have hl : 0 < wordMultiplier k a := hd.trans_le hdl
  have hi : (wordMultiplier k a)⁻¹ ≤ (wordMatrix (k + 1) a 1 1 : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hd hdl
  exact pow_le_pow_left₀ (inv_nonneg.mpr hl.le) hi 2

/-- At exponent two, bounded-digit even-word traces still have geometric absolute mass decay. -/
theorem even_trace_mass_le (n k : ℕ) :
    (∑ a : Fin (2 * k + 2) → Fin n, ‖wordTrace (2 : ℂ) (2 * k + 1) (word a)‖) ≤
      (8 / 3 : ℝ) * retention n ^ (2 * k + 2) := by
  have hb (a : Fin (2 * k + 2) → Fin n) :
      ‖wordTrace (2 : ℂ) (2 * k + 1) (word a)‖ ≤
        (4 / 3 : ℝ) * (wordMatrix (2 * k + 2) (word a) 1 1 : ℝ)⁻¹ ^ 2 := by
    have h := norm_even_wordTrace_le (w := (2 : ℂ)) k (word a)
    have hp : wordMultiplier (2 * k + 1) (word a) ^ (-((2 : ℂ).re)) =
        (wordMultiplier (2 * k + 1) (word a))⁻¹ ^ 2 := by
      calc
        _ = wordMultiplier (2 * k + 1) (word a) ^ (-(2 : ℝ)) :=
          congrArg (fun y : ℝ => wordMultiplier (2 * k + 1) (word a) ^ (-y))
            (show (2 : ℂ).re = (2 : ℝ) by norm_num)
        _ = (wordMultiplier (2 * k + 1) (word a) ^ (2 : ℝ))⁻¹ :=
          Real.rpow_neg (zero_lt_one.trans (one_lt_wordMultiplier _ (word a))).le 2
        _ = (wordMultiplier (2 * k + 1) (word a) ^ (2 : ℕ))⁻¹ :=
          congrArg (fun x : ℝ => x⁻¹) (Real.rpow_two (wordMultiplier (2 * k + 1) (word a)))
        _ = _ := (inv_pow (wordMultiplier (2 * k + 1) (word a)) 2).symm
    rw [hp] at h
    exact h.trans (mul_le_mul_of_nonneg_left (multiplier_inv_sq_le _ (word a)) (by norm_num))
  calc
    _ ≤ ∑ a : Fin (2 * k + 2) → Fin n,
        (4 / 3 : ℝ) * (wordMatrix (2 * k + 2) (word a) 1 1 : ℝ)⁻¹ ^ 2 :=
      Finset.sum_le_sum (fun a _ => hb a)
    _ = (4 / 3 : ℝ) * ∑ a : Fin (2 * k + 2) → Fin n,
        (wordMatrix (2 * k + 2) (word a) 1 1 : ℝ)⁻¹ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 / 3 : ℝ) * (2 * retention n ^ (2 * k + 2)) :=
      mul_le_mul_of_nonneg_left (sum_denominator_inv_sq_le n (2 * k + 2)) (by norm_num)
    _ = _ := by ring

/-- The full bounded-alphabet even-word trace family is absolutely summable at exponent two. -/
theorem summable_bounded_even_traces (n : ℕ) :
    Summable (fun p : Σ k : ℕ, Fin (2 * k + 2) → Fin n =>
      ‖wordTrace (2 : ℂ) (2 * p.1 + 1) (word p.2)‖) := by
  have hr := retention_bounds n
  have hr2 : |retention n ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hp := mul_pos (sub_pos.mpr hr.2) (add_pos_of_pos_of_nonneg zero_lt_one hr.1)
    nlinarith only [hp]
  have hs := (summable_geometric_of_abs_lt_one hr2).mul_left
    ((8 / 3 : ℝ) * retention n ^ 2)
  have hlength : Summable (fun k : ℕ =>
      ∑ a : Fin (2 * k + 2) → Fin n, ‖wordTrace (2 : ℂ) (2 * k + 1) (word a)‖) := by
    apply hs.of_nonneg_of_le (fun k => Finset.sum_nonneg (fun a _ => norm_nonneg _))
    intro k
    calc
      _ ≤ (8 / 3 : ℝ) * retention n ^ (2 * k + 2) := even_trace_mass_le n k
      _ = ((8 / 3 : ℝ) * retention n ^ 2) * (retention n ^ 2) ^ k := by
        rw [pow_add, pow_mul]
        ring
  apply (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mpr
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype] using hlength

#print axioms even_trace_mass_le
#print axioms summable_bounded_even_traces

/-- Exponential word-length decay is bounded by twice the exact cylinder width. -/
theorem exp_neg_length_le_endpoint_distance (k : ℕ) (a : Word (k + 1)) :
    Real.exp (-(2 * Real.log (wordMultiplier k a))) ≤
      2 * |realWordMap (k + 1) a 1 - realWordMap (k + 1) a 0| := by
  have hd : (0 : ℝ) < wordMatrix (k + 1) a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row (k + 1) a).2
  have hl : 0 < wordMultiplier k a := hd.trans_le (denominator_le_wordMultiplier k a)
  have he : Real.exp (2 * Real.log (wordMultiplier k a)) = wordMultiplier k a ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log hl, pow_two]
  rw [Real.exp_neg, he, ← inv_pow, MayerCylinderEndpoints.endpoint_distance_eq_probability]
  exact (multiplier_inv_sq_le k a).trans (denominator_inv_sq_le (k + 1) a)

#print axioms exp_neg_length_le_endpoint_distance

end
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundedDigits
