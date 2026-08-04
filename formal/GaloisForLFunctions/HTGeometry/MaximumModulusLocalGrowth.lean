import GaloisForLFunctions.HTGeometry.MaximumTermConcentration
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# The maximum modulus at a slightly larger radius

The maximum modulus at radius `r'` is bounded by the maximum term at a smaller radius `r`, at the
cost of the growth factor `(r'/r)^{ν(r')}` and one factor linear in the central index.  Both costs
are the standard ones: the first is the upper growth law for the maximum term, the second is the
comparison between the majorant and its largest term.

At the Wiman--Valiron scale `r' = r(1 + κ/ν(r))` the growth factor is
`exp(ν(r')·log(1 + κ/ν(r))) ≤ exp(κ·ν(r')/ν(r))`, so the whole bound is controlled as soon as the
central index does not jump between the two radii.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The majorant is monotone in the radius. -/
theorem coeffSum_mono (ha : EntireCoeffs a) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    coeffSum a r ≤ coeffSum a s := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  refine Summable.tsum_le_tsum ?_ (summable_term ha hr) (summable_term ha hs)
  intro n
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hr) hrs n) (norm_nonneg _)

/-- **The majorant costs `ν(2r) + 2` maximum terms.**  The doubling radius makes the geometric tail
contribute exactly one further term. -/
theorem coeffSum_le_maxTerm_mul_two (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    coeffSum a r ≤ maxTerm a r * ((centralIndex a (2 * r) : ℝ) + 2) := by
  have hlt : r < 2 * r := by linarith
  have h := coeffSum_le_maxTerm_mul_centralIndex ha hr hlt hn₀
  have hval : r / (2 * r) = 1 / 2 := by
    field_simp
  rw [hval] at h
  have harith : ((centralIndex a (2 * r) : ℝ) + 1) + (1 / 2) / (1 - 1 / 2)
      = (centralIndex a (2 * r) : ℝ) + 2 := by
    norm_num
    ring
  rwa [harith] at h

/-- **The maximum modulus at a larger radius, in terms of the maximum term at a smaller one.**

  `‖f w‖ ≤ μ(r) · (r'/r)^{ν(r')} · (ν(2r') + 2)`  for  `‖w‖ ≤ r'`. -/
theorem norm_coeffFun_le_maxTerm_mul (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    {r r' : ℝ} (hr : 0 < r) (hrr' : r ≤ r') {w : ℂ} (hw0 : 0 < ‖w‖) (hw : ‖w‖ ≤ r') :
    ‖coeffFun a w‖
      ≤ maxTerm a r * (r' / r) ^ (centralIndex a r') * ((centralIndex a (2 * r') : ℝ) + 2) := by
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
  have hstep₁ : ‖coeffFun a w‖ ≤ coeffSum a ‖w‖ := norm_coeffFun_le ha hw0
  have hstep₂ : coeffSum a ‖w‖ ≤ coeffSum a r' := coeffSum_mono ha hw0 hw
  have hstep₃ : coeffSum a r' ≤ maxTerm a r' * ((centralIndex a (2 * r') : ℝ) + 2) :=
    coeffSum_le_maxTerm_mul_two ha hn₀ hr'
  have hstep₄ : maxTerm a r' ≤ maxTerm a r * (r' / r) ^ (centralIndex a r') :=
    maxTerm_le_mul_pow ha hr hrr' hn₀
  have hnonneg : (0 : ℝ) ≤ (centralIndex a (2 * r') : ℝ) + 2 := by positivity
  calc ‖coeffFun a w‖ ≤ coeffSum a r' := le_trans hstep₁ hstep₂
    _ ≤ maxTerm a r' * ((centralIndex a (2 * r') : ℝ) + 2) := hstep₃
    _ ≤ (maxTerm a r * (r' / r) ^ (centralIndex a r')) * ((centralIndex a (2 * r') : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hstep₄ hnonneg

/-- **The growth factor at the Wiman--Valiron scale.**  With `r' = r(1 + κ/ν)` the factor
`(r'/r)^{ν(r')}` is at most `exp(κ · ν(r') / ν)`. -/
theorem growth_factor_le_exp {r r' κ ν : ℝ} {k : ℕ} (hr : 0 < r) (hν : 0 < ν)
    (hκ : 0 ≤ κ) (hr' : r' = r * (1 + κ / ν)) :
    (r' / r) ^ k ≤ Real.exp ((k : ℝ) * κ / ν) := by
  have hratio : r' / r = 1 + κ / ν := by
    rw [hr']
    field_simp
  have hpos : 0 < 1 + κ / ν := by positivity
  have hlog : Real.log (1 + κ / ν) ≤ κ / ν := by
    have := Real.add_one_le_exp (κ / ν)
    have hle : 1 + κ / ν ≤ Real.exp (κ / ν) := by linarith
    calc Real.log (1 + κ / ν) ≤ Real.log (Real.exp (κ / ν)) := Real.log_le_log hpos hle
      _ = κ / ν := Real.log_exp _
  rw [hratio]
  have hpow : (1 + κ / ν) ^ k = Real.exp ((k : ℝ) * Real.log (1 + κ / ν)) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hpos]
    exact (Real.rpow_natCast _ k).symm
  rw [hpow]
  refine Real.exp_le_exp.mpr ?_
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  calc (k : ℝ) * Real.log (1 + κ / ν) ≤ (k : ℝ) * (κ / ν) :=
        mul_le_mul_of_nonneg_left hlog hk0
    _ = (k : ℝ) * κ / ν := by ring

end GaloisForLFunctions.HTGeometry
