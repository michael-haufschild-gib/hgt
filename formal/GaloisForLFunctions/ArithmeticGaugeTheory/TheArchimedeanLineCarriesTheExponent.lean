import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponent

/-!
# The archimedean line carries the gauge exponent

The vertical shifts `n ↦ n^{it}` form a line through the trivial point of the gauge torus, the
archimedean line (`verticalShift`, `ArithmeticCorrelationGeometry.twist_clockPhasePoint`). They are
the special points that the archimedean place adds to the Dirichlet characters. This file shows that
the gauge exponent cannot distinguish two points that differ by a vertical shift.

* **Summation of a power** (`sum_rpow_sub_one_le`). `Σ_{i < N} (i + 1)^{θ − 1} ≤ (1 + 1/θ)(N + 1)^θ`
  for `θ > 0`, by Bernoulli's inequality below `θ = 1` and monotonicity above.
* **Abel transfer** (`norm_sum_mul_le_of_partial_sums`). If the partial sums of `a` are
  `O((N + 1)^θ)` and the weight `w` is bounded by one with increments `O(1/(n + 1))`, then the
  partial sums of `a w` are `O((N + 1)^θ)` with an explicit constant.
* **Vertical shifts are slowly varying** (`norm_twist_verticalShift_succ_sub_le`).
  `‖(n + 1)^{it} − n^{it}‖ ≤ 2|t|/(n + 1)`.
* **Invariance** (`gaugeExponent_add_verticalShift`). For every source bounded by one, every gauge
  point `x` and every `t`, the exponent at `x + (vertical shift by t)` equals the exponent at `x`.
* **The archimedean line through the trivial point** (`gaugeExponent_moebius_verticalShift`,
  `riemannHypothesis_iff_gaugeExponent_moebius_verticalShift_le_half`). Every point `n^{it}` has
  Möbius exponent exactly `Θ`, and RH holds iff any one of them is typical.

So the archimedean line through `0` lies entirely inside or entirely outside the Möbius exceptional
set. The archimedean place cannot separate the trivial point from its vertical shifts; typicality is
decided by the finite part of the gauge torus.
-/

open MeasureTheory Finset Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### A power sum -/

/-- Bernoulli's tangent bound: `θ (i + 1)^{θ − 1} ≤ (i + 1)^θ − i^θ` for `0 < θ ≤ 1`. -/
theorem rpow_succ_sub_rpow_ge {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (i : ℕ) :
    θ * ((i : ℝ) + 1) ^ (θ - 1) ≤ ((i : ℝ) + 1) ^ θ - (i : ℝ) ^ θ := by
  set u : ℝ := (i : ℝ) + 1 with hu
  have hu1 : 1 ≤ u := by rw [hu]; linarith [i.cast_nonneg (α := ℝ)]
  have hu0 : 0 < u := by linarith
  have hs : -1 ≤ -1 / u := by
    rw [neg_div, neg_le_neg_iff, div_le_one hu0]
    exact hu1
  have hb := rpow_one_add_le_one_add_mul_self hs hθ.le hθ1
  have hi : (i : ℝ) = u * (1 + -1 / u) := by
    rw [hu]
    field_simp
    ring
  have hnn : 0 ≤ 1 + -1 / u := by linarith
  have hpow : (i : ℝ) ^ θ = u ^ θ * (1 + -1 / u) ^ θ := by
    rw [hi, Real.mul_rpow hu0.le hnn]
  have hsub : u ^ (θ - 1) = u ^ θ / u := Real.rpow_sub_one hu0.ne' θ
  rw [hpow, hsub]
  have hupos : 0 ≤ u ^ θ := Real.rpow_nonneg hu0.le θ
  have := mul_le_mul_of_nonneg_left hb hupos
  have heq : u ^ θ * (1 + θ * (-1 / u)) = u ^ θ - θ * (u ^ θ / u) := by
    field_simp
    ring
  linarith

/-- **A power sum.** For `θ > 0`, `Σ_{i < N} (i + 1)^{θ − 1} ≤ (1 + 1/θ)(N + 1)^θ`. -/
theorem sum_rpow_sub_one_le {θ : ℝ} (hθ : 0 < θ) (N : ℕ) :
    ∑ i ∈ range N, ((i : ℝ) + 1) ^ (θ - 1) ≤ (1 + 1 / θ) * ((N : ℝ) + 1) ^ θ := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
  have hpowN : 0 ≤ ((N : ℝ) + 1) ^ θ := Real.rpow_nonneg (by linarith) θ
  rcases le_or_gt θ 1 with hθ1 | hθ1
  · -- Telescoping against `(i + 1)^θ − i^θ`.
    have htel : ∑ i ∈ range N, (((i : ℝ) + 1) ^ θ - (i : ℝ) ^ θ) = (N : ℝ) ^ θ := by
      have := sum_range_sub (fun i : ℕ => (i : ℝ) ^ θ) N
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
      rw [this, Real.zero_rpow hθ.ne', sub_zero]
    have hle : ∑ i ∈ range N, ((i : ℝ) + 1) ^ (θ - 1) ≤ (N : ℝ) ^ θ / θ := by
      rw [le_div_iff₀ hθ, sum_mul, ← htel]
      exact sum_le_sum fun i _ => by rw [mul_comm]; exact rpow_succ_sub_rpow_ge hθ hθ1 i
    have hNle : (N : ℝ) ^ θ ≤ ((N : ℝ) + 1) ^ θ :=
      Real.rpow_le_rpow (N.cast_nonneg) (by linarith) hθ.le
    calc _ ≤ (N : ℝ) ^ θ / θ := hle
      _ ≤ ((N : ℝ) + 1) ^ θ / θ := div_le_div_of_nonneg_right hNle hθ.le
      _ ≤ (1 + 1 / θ) * ((N : ℝ) + 1) ^ θ := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_right (by linarith) hpowN
  · -- Each term is at most `(N + 1)^{θ − 1}`.
    have hterm : ∀ i ∈ range N, ((i : ℝ) + 1) ^ (θ - 1) ≤ ((N : ℝ) + 1) ^ (θ - 1) := by
      intro i hi
      have hiN : (i : ℝ) + 1 ≤ (N : ℝ) + 1 := by
        have := mem_range.mp hi
        have : (i : ℝ) < N := by exact_mod_cast this
        linarith
      exact Real.rpow_le_rpow (by positivity) hiN (by linarith)
    calc _ ≤ ∑ _i ∈ range N, ((N : ℝ) + 1) ^ (θ - 1) := sum_le_sum hterm
      _ = (N : ℝ) * ((N : ℝ) + 1) ^ (θ - 1) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (θ - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
      _ = ((N : ℝ) + 1) ^ θ := by
        rw [Real.rpow_sub_one (by linarith), mul_div_cancel₀ _ (by linarith)]
      _ ≤ (1 + 1 / θ) * ((N : ℝ) + 1) ^ θ := by
        have : (0 : ℝ) ≤ 1 / θ := by positivity
        nlinarith

/-! ### Abel transfer -/

/-- **Abel transfer.** Partial sums of `a` of size `O((N + 1)^θ)` stay of that size after
multiplication by a weight bounded by one whose increments are `O(1/(n + 1))`. -/
theorem norm_sum_mul_le_of_partial_sums {a w : ℕ → ℂ} {C B θ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hw : ∀ n, ‖w n‖ ≤ 1) (hdw : ∀ n, ‖w (n + 1) - w n‖ ≤ B / ((n : ℝ) + 1))
    (hS : ∀ N, ‖∑ n ∈ range (N + 1), a n‖ ≤ C * ((N : ℝ) + 1) ^ θ) (N : ℕ) :
    ‖∑ n ∈ range (N + 1), a n * w n‖ ≤ C * (1 + B * (1 + 1 / θ)) * ((N : ℝ) + 1) ^ θ := by
  have hparts := sum_range_by_parts w a (N + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hparts
  rw [show ∑ n ∈ range (N + 1), a n * w n = ∑ n ∈ range (N + 1), w n * a n from
    sum_congr rfl fun n _ => mul_comm _ _, hparts]
  have hhead : ‖w N * ∑ i ∈ range (N + 1), a i‖ ≤ C * ((N : ℝ) + 1) ^ θ := by
    rw [norm_mul]
    calc ‖w N‖ * ‖∑ i ∈ range (N + 1), a i‖ ≤ 1 * (C * ((N : ℝ) + 1) ^ θ) :=
          mul_le_mul (hw N) (hS N) (norm_nonneg _) zero_le_one
      _ = C * ((N : ℝ) + 1) ^ θ := one_mul _
  have htail : ‖∑ i ∈ range N, (w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j‖ ≤
      B * C * ((1 + 1 / θ) * ((N : ℝ) + 1) ^ θ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ range N, ‖(w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j‖
        ≤ ∑ i ∈ range N, B * C * ((i : ℝ) + 1) ^ (θ - 1) := by
          refine sum_le_sum fun i _ => ?_
          have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
          rw [norm_mul, Real.rpow_sub_one hi1.ne']
          calc ‖w (i + 1) - w i‖ * ‖∑ j ∈ range (i + 1), a j‖
              ≤ B / ((i : ℝ) + 1) * (C * ((i : ℝ) + 1) ^ θ) :=
                mul_le_mul (hdw i) (hS i) (norm_nonneg _) (div_nonneg hB hi1.le)
            _ = B * C * (((i : ℝ) + 1) ^ θ / ((i : ℝ) + 1)) := by ring
      _ = B * C * ∑ i ∈ range N, ((i : ℝ) + 1) ^ (θ - 1) := by rw [mul_sum]
      _ ≤ B * C * ((1 + 1 / θ) * ((N : ℝ) + 1) ^ θ) :=
          mul_le_mul_of_nonneg_left (sum_rpow_sub_one_le hθ N) (mul_nonneg hB hC)
  calc ‖w N * ∑ i ∈ range (N + 1), a i -
        ∑ i ∈ range N, (w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j‖
      ≤ ‖w N * ∑ i ∈ range (N + 1), a i‖ +
          ‖∑ i ∈ range N, (w (i + 1) - w i) * ∑ j ∈ range (i + 1), a j‖ := norm_sub_le _ _
    _ ≤ C * ((N : ℝ) + 1) ^ θ + B * C * ((1 + 1 / θ) * ((N : ℝ) + 1) ^ θ) := add_le_add hhead htail
    _ = C * (1 + B * (1 + 1 / θ)) * ((N : ℝ) + 1) ^ θ := by ring

/-! ### The archimedean line -/

/-- The vertical shift by `t`: the gauge point whose twist is `n^{it}`. -/
def verticalShift (t : ℝ) : GaugeTorus := HTGeometry.clockPhasePoint (fun p : ℕ => Real.log p) t

theorem twist_verticalShift (t : ℝ) (n : ℕ) :
    twist (verticalShift t) n = Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I) :=
  twist_clockPhasePoint t n

/-- `log(n + 1) − log n ≤ 2/(n + 1)`. -/
theorem log_succ_sub_log_le (n : ℕ) : Real.log ((n : ℝ) + 1) - Real.log n ≤ 2 / ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [← Real.log_div (by positivity) hn0.ne']
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) / n)
    have h1 : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    have h2 : (1 : ℝ) / n ≤ 2 / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ hn0 (by positivity)]
      linarith
    linarith

/-- **Vertical shifts are slowly varying**: `‖(n + 1)^{it} − n^{it}‖ ≤ 2|t|/(n + 1)`. -/
theorem norm_twist_verticalShift_succ_sub_le (t : ℝ) (n : ℕ) :
    ‖twist (verticalShift t) (n + 1) - twist (verticalShift t) n‖ ≤ 2 * |t| / ((n : ℝ) + 1) := by
  rw [twist_verticalShift, twist_verticalShift]
  set d : ℝ := t * Real.log ((n + 1 : ℕ) : ℝ) - t * Real.log n with hd
  have hsplit : Complex.exp (((t * Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * (d : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, hd]
    congr 2
    push_cast
    ring
  rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, hd, ← mul_sub, abs_mul]
  have hlog0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith))
  rw [abs_of_nonneg hlog0]
  have := log_succ_sub_log_le n
  push_cast at this ⊢
  calc |t| * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ |t| * (2 / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg t)
    _ = 2 * |t| / ((n : ℝ) + 1) := by ring

/-- Opposite vertical shifts cancel. -/
theorem twist_verticalShift_mul_neg (t : ℝ) (n : ℕ) :
    twist (verticalShift t) n * twist (verticalShift (-t)) n = 1 := by
  rw [twist_verticalShift, twist_verticalShift, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  push_cast
  ring

/-! ### Invariance of the gauge exponent -/

variable {a : ℕ → ℂ}

/-- **Transfer along the archimedean line.** A power bound of positive exponent at `x` holds at
`x + verticalShift t`. -/
theorem gaugePowerBound_add_verticalShift {x : GaugeTorus} {θ : ℝ} (hθ : 0 < θ)
    (h : GaugePowerBound a x θ) (t : ℝ) : GaugePowerBound a (x + verticalShift t) θ := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C * (1 + 2 * |t| * (1 + 1 / θ)), by positivity, fun N => ?_⟩
  have := norm_sum_mul_le_of_partial_sums (a := fun n => a n * twist x n)
    (w := twist (verticalShift t)) hθ hC (by positivity) (fun n => (norm_twist _ n).le)
    (norm_twist_verticalShift_succ_sub_le t) hb N
  simpa only [twist_add, mul_assoc] using this

/-- The gauge exponent does not increase along the archimedean line. -/
theorem gaugeExponent_add_verticalShift_le (ha : ∀ n, ‖a n‖ ≤ 1) (x : GaugeTorus) (t : ℝ) :
    gaugeExponent a (x + verticalShift t) ≤ gaugeExponent a x := by
  refine le_of_forall_gt fun θ hθ => ?_
  have hθ0 : 0 < θ := lt_of_le_of_lt (gaugeExponent_nonneg ha) hθ
  obtain ⟨θ', hθ'1, hθ'2⟩ := exists_between hθ
  have hθ'0 : 0 < θ' := lt_of_le_of_lt (gaugeExponent_nonneg ha) hθ'1
  exact lt_of_le_of_lt (gaugeExponent_le hθ'0.le (gaugePowerBound_add_verticalShift hθ'0
    (gaugePowerBound_of_gaugeExponent_lt ha hθ'1) t)) hθ'2

/-- Twists only see the positive integers' phases; shifting back recovers the original twist. -/
theorem gaugePowerBound_congr {x y : GaugeTorus} (hxy : ∀ n, twist x n = twist y n) {θ : ℝ}
    (h : GaugePowerBound a x θ) : GaugePowerBound a y θ := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun N => by simpa only [hxy] using hb N⟩

/-- **The gauge exponent is constant along archimedean lines.** -/
theorem gaugeExponent_add_verticalShift (ha : ∀ n, ‖a n‖ ≤ 1) (x : GaugeTorus) (t : ℝ) :
    gaugeExponent a (x + verticalShift t) = gaugeExponent a x := by
  refine le_antisymm (gaugeExponent_add_verticalShift_le ha x t) ?_
  have hback : ∀ n, twist (x + verticalShift t + verticalShift (-t)) n = twist x n := by
    intro n
    rw [twist_add, twist_add, mul_assoc, twist_verticalShift_mul_neg, mul_one]
  have hexp : gaugeExponent a (x + verticalShift t + verticalShift (-t)) = gaugeExponent a x := by
    unfold gaugeExponent exponentSet
    congr 1
    ext θ
    exact and_congr_right fun _ => ⟨gaugePowerBound_congr hback,
      gaugePowerBound_congr fun n => (hback n).symm⟩
  calc gaugeExponent a x = gaugeExponent a (x + verticalShift t + verticalShift (-t)) := hexp.symm
    _ ≤ gaugeExponent a (x + verticalShift t) :=
        gaugeExponent_add_verticalShift_le ha _ (-t)

/-- **The archimedean line through the trivial point.** Every vertical shift has Möbius exponent
`Θ`. -/
theorem gaugeExponent_moebius_verticalShift (t : ℝ) :
    gaugeExponent moebiusSource (verticalShift t) = RHTower.zetaZeroAbscissa := by
  have := gaugeExponent_add_verticalShift norm_moebiusSource_le 0 t
  rw [zero_add] at this
  rw [this, gaugeExponent_moebius_trivial]

/-- **RH is the typicality of any one point of the archimedean line.** -/
theorem riemannHypothesis_iff_gaugeExponent_moebius_verticalShift_le_half (t : ℝ) :
    RiemannHypothesis ↔ gaugeExponent moebiusSource (verticalShift t) ≤ 1 / 2 := by
  rw [gaugeExponent_moebius_verticalShift, ← gaugeExponent_moebius_trivial]
  exact riemannHypothesis_iff_gaugeExponent_moebius_trivial_le_half

end GaloisForLFunctions.ArithmeticGaugeTheory
