import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import GaloisForLFunctions.MultiplicativePositivityGeometry.ArithmeticRealization

/-!
# Weil's theorem for curves is positive definiteness on `ℤ`

For a curve datum over `𝔽_q` with normalized Frobenius eigenvalues `β_1, …, β_{2g}`, the
**normalized trace sequence** `τ(m) = Re Σ_i β_i^{|m|}`, `m ∈ ℤ`, is the prime side of the
explicit formula of the curve: `N_m = q^m + 1 − q^{m/2} τ(m)`. Its value at `0` is the integer
`2g`, the budget of the curve.

**Theorem** (`curve_rh_tfae`). The following are equivalent:

1. RH for the datum: `|β_i| = 1` for every `i`;
2. `τ` is an even positive-definite function on `ℤ`;
3. `|τ(m)| ≤ 2g` for every `m` — the two-point Gram form against the budget;
4. Hasse–Weil, `|N_m − q^m − 1| ≤ 2g q^{m/2}` for every `m ≥ 0`;
5. the Toeplitz forms of the power sums are nonnegative: Hodge index on the Frobenius span.

Under RH, `τ` is the cosine trace of the angle measure `Σ_i δ_{arg β_i}`, a positive measure of
mass `2g` on the circle (`traceSeq_eq_cosineTrace`); positive definiteness is the Fourier dual of its
positivity. Conversely, the two-point bound `|τ| ≤ τ(0)` bounds every power sum by `2g`, which
forces `|β_i| ≤ 1`, and the functional equation forces equality.

So over `𝔽_q` the arithmetic positive duality has its calibration: the prime side is a
positive-definite function on `ℤ` with integer mass `2g`, and Weil proves its positive definiteness
by counting sections. The golden datum `1 − 5X + 5X²`, with integer point counts, fails it
(`not_isEvenPosDef_goldenDatum_traceSeq`).
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open ArithmeticCastelnuovoSeveri MultiplicativePositivityGeometry

namespace CurveDatum'

open ArithmeticCastelnuovoSeveri.CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The normalized trace sequence `τ(m) = Re Σ_i β_i^{|m|}`. -/
def traceSeq (m : ℤ) : ℝ := D.trace m.natAbs

theorem traceSeq_zero : traceSeq D 0 = Fintype.card ι := by
  simp [traceSeq, D.trace_zero]

/-- `|N_m − q^m − 1| = q^{m/2} |τ(m)|`. -/
theorem abs_pointCount_sub (m : ℕ) :
    |D.pointCount m - D.q ^ m - 1| = D.sqrtq ^ m * |D.trace m| := by
  unfold CurveDatum.pointCount
  rw [show D.q ^ m + 1 - D.sqrtq ^ m * D.trace m - D.q ^ m - 1 = -(D.sqrtq ^ m * D.trace m) by
    ring, abs_neg, abs_mul, abs_of_pos (pow_pos D.sqrtq_pos m)]

/-- Under RH, `τ` is the cosine trace of the angles `arg β_i` with unit weights. -/
theorem traceSeq_eq_cosineTrace (hU : ∀ i, ‖D.β i‖ = 1) (m : ℤ) :
    traceSeq D m = cosineTrace (fun _ : ι => (1 : ℝ)) (fun i => Complex.arg (D.β i)) m := by
  unfold traceSeq cosineTrace CurveDatum.trace CurveDatum.powerSum
  rw [tsum_fintype, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hβ : D.β i = cexp ((Complex.arg (D.β i) : ℂ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (D.β i), hU i]
    simp
  rw [hβ, ← Complex.exp_nat_mul, one_mul,
    show ((m.natAbs : ℕ) : ℂ) * ((Complex.arg (D.β i) : ℂ) * I) =
      ((m.natAbs * Complex.arg (D.β i) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]
  rw [Nat.cast_natAbs, Int.cast_abs]
  rcases abs_choice (m : ℝ) with h | h <;> rw [h]
  · ring_nf
  · rw [neg_mul, Real.cos_neg]; ring_nf

/-- **RH ⇒ positive definiteness on `ℤ`.** -/
theorem traceSeq_isEvenPosDef_of_unitary (hU : ∀ i, ‖D.β i‖ = 1) :
    IsEvenPosDef (traceSeq D) := by
  have h := (isEvenPosDef_cosineTrace (fun _ => zero_le_one) (Summable.of_finite)
    (fun i => Complex.arg (D.β i))).comp_addMonoidHom (Int.castAddHom ℝ)
  have e : traceSeq D = (cosineTrace (fun _ : ι => (1 : ℝ)) fun i => Complex.arg (D.β i)) ∘
      Int.castAddHom ℝ := funext fun m => traceSeq_eq_cosineTrace D hU m
  rw [e]
  exact h

/-- **The budget bounds the power sums.** `|τ(m)| ≤ 2g` for all `m` forces RH. -/
theorem unitary_of_abs_traceSeq_le (h : ∀ m, |traceSeq D m| ≤ Fintype.card ι) :
    ∀ i, ‖D.β i‖ = 1 := by
  have hle : ∀ i, ‖D.β i‖ ≤ 1 := by
    intro i
    refine RHTower.WeilKloosterman.norm_le_of_power_sums_bound Finset.univ D.β
      (C := Fintype.card ι) (m0 := 0) zero_le_one (fun j _ => ?_) i (Finset.mem_univ i)
    rw [one_pow, mul_one]
    have hj := h j
    simp only [traceSeq, Int.natAbs_natCast] at hj
    rw [← CurveDatum.powerSum, D.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs]
    exact hj
  intro i
  have hfe := congrArg norm (D.β_fePerm i)
  rw [norm_mul, norm_one] at hfe
  have hi := hle i
  have hf := hle (D.fePerm i)
  nlinarith [norm_nonneg (D.β i), norm_nonneg (D.β (D.fePerm i))]

/-- **Weil's theorem for curves in positive-duality form.** -/
theorem curve_rh_tfae :
    [∀ i, ‖D.β i‖ = 1,
      IsEvenPosDef (traceSeq D),
      ∀ m, |traceSeq D m| ≤ Fintype.card ι,
      ∀ m : ℕ, |D.pointCount m - D.q ^ m - 1| ≤ Fintype.card ι * D.sqrtq ^ m,
      ∀ S d, 0 ≤ D.spanDefect S d].TFAE := by
  tfae_have 1 → 2 := traceSeq_isEvenPosDef_of_unitary D
  tfae_have 2 → 3 := fun hφ m => by
    have := hφ.abs_le_apply_zero m
    rwa [traceSeq_zero] at this
  tfae_have 3 → 1 := unitary_of_abs_traceSeq_le D
  tfae_have 3 → 4 := fun h m => by
    rw [abs_pointCount_sub, mul_comm]
    have := h m
    simp only [traceSeq, Int.natAbs_natCast] at this
    exact mul_le_mul_of_nonneg_right this (pow_nonneg D.sqrtq_pos.le m)
  tfae_have 4 → 3 := fun h m => by
    have hm := h m.natAbs
    rw [abs_pointCount_sub, mul_comm] at hm
    exact le_of_mul_le_mul_right hm (pow_pos D.sqrtq_pos _)
  tfae_have 1 ↔ 5 := D.hodgeIndexOnSpan_iff_unitary.symm
  tfae_finish

/-- **The golden datum fails positive definiteness**, although its point counts are integers. -/
theorem not_isEvenPosDef_goldenDatum_traceSeq : ¬ IsEvenPosDef (traceSeq goldenDatum) := by
  intro h
  exact goldenDatum_not_unitary (((curve_rh_tfae goldenDatum).out 1 0).mp h)

end CurveDatum'

end GaloisForLFunctions.ArithmeticPositiveDuality
