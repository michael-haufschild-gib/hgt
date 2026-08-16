import GaloisForLFunctions.HTGeometry.OrderOneEnvelope

/-!
# The real even quartet polynomial

For `tau` with `Re tau * Im tau ≠ 0` the polynomial

`Q(z) = (z^2 - tau^2) (z^2 - conj(tau)^2)`

is real, even, has no real zero, and has exactly the off-real quartet `{±tau, ±conj tau}` as its
zero set.  Multiplying an even real entire function of exact order one by `Q` therefore preserves
evenness, reality, and the order-one envelope, changes no real zero, and inserts the quartet.
-/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The order-one envelope contains the identity. -/
theorem orderOneEnvelope_id' : OrderOneEnvelope (fun s : ℂ => s) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 2, by positivity, fun s => ?_⟩
  have hs : 0 ≤ ‖s‖ := norm_nonneg s
  have hlogs : Real.log 2 ≤ Real.log (2 + ‖s‖) := Real.log_le_log (by norm_num) (by linarith)
  have hkey : ‖s‖ ≤ orderOneWeight (1 / Real.log 2) s := by
    rw [orderOneWeight]
    have hstep : Real.log 2 * ‖s‖ ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := by nlinarith
    have hpos : (0 : ℝ) < Real.log 2 := hlog2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith
  have hexp := Real.add_one_le_exp (orderOneWeight (1 / Real.log 2) s)
  linarith

/-- Powers of the identity lie in the order-one class. -/
theorem orderOneEnvelope_pow (n : ℕ) : OrderOneEnvelope (fun s : ℂ => s ^ n) := by
  induction n with
  | zero => simpa using orderOneEnvelope_const 1
  | succ n ih =>
      refine OrderOneEnvelope.congr (orderOneEnvelope_id'.mul ih) fun s => ?_
      rw [pow_succ]
      ring

/-- **Every polynomial has an order-one envelope.** -/
theorem orderOneEnvelope_polyEval (p : Polynomial ℂ) :
    OrderOneEnvelope (fun z : ℂ => Polynomial.eval z p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      refine OrderOneEnvelope.congr (hp.add hq) fun z => ?_
      rw [Polynomial.eval_add]
  | monomial n a =>
      refine OrderOneEnvelope.congr ((orderOneEnvelope_pow n).const_mul a) fun z => ?_
      rw [Polynomial.eval_monomial]

/-- The real even quartet polynomial. -/
def quartetPoly (τ : ℂ) : Polynomial ℂ :=
  (Polynomial.X ^ 2 - Polynomial.C (τ ^ 2)) *
    (Polynomial.X ^ 2 - Polynomial.C (((starRingEnd ℂ) τ) ^ 2))

theorem eval_quartetPoly (τ z : ℂ) :
    Polynomial.eval z (quartetPoly τ) = (z ^ 2 - τ ^ 2) * (z ^ 2 - ((starRingEnd ℂ) τ) ^ 2) := by
  simp [quartetPoly]

theorem quartetPoly_ne_zero (τ : ℂ) : quartetPoly τ ≠ 0 := by
  have h1 : (Polynomial.X ^ 2 - Polynomial.C (τ ^ 2) : Polynomial ℂ).Monic :=
    Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have h2 : (Polynomial.X ^ 2 - Polynomial.C (((starRingEnd ℂ) τ) ^ 2) : Polynomial ℂ).Monic :=
    Polynomial.monic_X_pow_sub_C _ two_ne_zero
  exact (h1.mul h2).ne_zero

/-- The quartet polynomial is even. -/
theorem eval_quartetPoly_neg (τ z : ℂ) :
    Polynomial.eval (-z) (quartetPoly τ) = Polynomial.eval z (quartetPoly τ) := by
  rw [eval_quartetPoly, eval_quartetPoly]
  ring

/-- The quartet polynomial is Schwarz-real. -/
theorem eval_quartetPoly_conj (τ z : ℂ) :
    Polynomial.eval ((starRingEnd ℂ) z) (quartetPoly τ)
      = (starRingEnd ℂ) (Polynomial.eval z (quartetPoly τ)) := by
  rw [eval_quartetPoly, eval_quartetPoly]
  simp only [map_mul, map_sub, map_pow, Complex.conj_conj]
  ring

/-- The zero set of the quartet polynomial. -/
theorem eval_quartetPoly_eq_zero_iff (τ z : ℂ) :
    Polynomial.eval z (quartetPoly τ) = 0 ↔
      z = τ ∨ z = -τ ∨ z = (starRingEnd ℂ) τ ∨ z = -((starRingEnd ℂ) τ) := by
  rw [eval_quartetPoly]
  have hfac : (z ^ 2 - τ ^ 2) * (z ^ 2 - ((starRingEnd ℂ) τ) ^ 2)
      = ((z - τ) * (z + τ)) * ((z - (starRingEnd ℂ) τ) * (z + (starRingEnd ℂ) τ)) := by ring
  rw [hfac]
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]
  tauto

theorem quartet_root (τ : ℂ) :
    Polynomial.eval τ (quartetPoly τ) = 0 ∧
      Polynomial.eval (-τ) (quartetPoly τ) = 0 ∧
      Polynomial.eval ((starRingEnd ℂ) τ) (quartetPoly τ) = 0 ∧
      Polynomial.eval (-((starRingEnd ℂ) τ)) (quartetPoly τ) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [eval_quartetPoly_eq_zero_iff] <;> tauto

/-- **The quartet polynomial has no real zero.** -/
theorem eval_quartetPoly_ne_zero_of_im_eq_zero {τ : ℂ} (hτ : τ.im ≠ 0) {z : ℂ}
    (hz : z.im = 0) : Polynomial.eval z (quartetPoly τ) ≠ 0 := by
  intro hcon
  rw [eval_quartetPoly_eq_zero_iff] at hcon
  rcases hcon with h | h | h | h
  · exact hτ (by rw [← h, hz])
  · exact hτ (by have := congrArg Complex.im h; simp at this; rw [hz] at this; linarith)
  · refine hτ ?_
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    rw [hz] at this
    linarith
  · refine hτ ?_
    have := congrArg Complex.im h
    simp only [Complex.neg_im, Complex.conj_im] at this
    rw [hz] at this
    linarith

end

end GaloisForLFunctions.HTGeometry
