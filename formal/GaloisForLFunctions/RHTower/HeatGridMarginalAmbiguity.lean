import GaloisForLFunctions.RHTower.HeatGridAliasingBoundary

/-!
# Two heat-grid marginals do not reconstruct a spectral packet

A rectangle switch gives two conjugation-closed four-atom packets in the
strict spectral parabola. Their traces agree on both entire sampling grids
but differ at an explicit positive time. This remains true for prime-log
steps, although paired individual heat coordinates are injective.
-/

namespace RHTower

noncomputable section

/-- Heat trace of a conjugate pair with common real part `A`. -/
def conjugatePairHeatTrace (A b t : ℝ) : ℝ :=
  (Complex.exp (-(t : ℂ) * ((A : ℂ) + (b : ℂ) * Complex.I)) +
    Complex.exp (-(t : ℂ) * ((A : ℂ) - (b : ℂ) * Complex.I))).re

theorem conjugatePairHeatTrace_eq (A b t : ℝ) :
    conjugatePairHeatTrace A b t = 2 * Real.exp (-t * A) * Real.cos (t * b) := by
  simp only [conjugatePairHeatTrace, Complex.add_re, Complex.exp_re,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.add_im, Complex.I_re, Complex.I_im]
  ring_nf
  rw [Real.cos_neg]
  ring

/-- One diagonal of the frequency rectangle, with its conjugates. -/
def heatRectangleLeft (A a b t : ℝ) : ℝ :=
  conjugatePairHeatTrace A 0 t + conjugatePairHeatTrace A (a + b) t

/-- The other diagonal, with its conjugates. -/
def heatRectangleRight (A a b t : ℝ) : ℝ :=
  conjugatePairHeatTrace A a t + conjugatePairHeatTrace A b t

theorem heatRectangle_eq_of_full_turn_left (A a b t : ℝ)
    (hc : Real.cos (t * a) = 1) (hs : Real.sin (t * a) = 0) :
    heatRectangleLeft A a b t = heatRectangleRight A a b t := by
  simp only [heatRectangleLeft, heatRectangleRight, conjugatePairHeatTrace_eq,
    mul_zero, Real.cos_zero, mul_one, mul_add, Real.cos_add, hc, hs]
  ring

theorem heatRectangle_eq_of_full_turn_right (A a b t : ℝ)
    (hc : Real.cos (t * b) = 1) (hs : Real.sin (t * b) = 0) :
    heatRectangleLeft A a b t = heatRectangleRight A a b t := by
  simpa [heatRectangleLeft, heatRectangleRight, add_comm] using
    heatRectangle_eq_of_full_turn_left A b a t hc hs

/-- Each entire marginal grid loses the rectangle coupling. -/
theorem heatRectangle_two_grid_equal (A : ℝ) {h k : ℝ}
    (hh : 0 < h) (hk : 0 < k) (n : ℕ) :
    heatRectangleLeft A (2 * Real.pi / h) (2 * Real.pi / k) (n * h) =
      heatRectangleRight A (2 * Real.pi / h) (2 * Real.pi / k) (n * h) ∧
    heatRectangleLeft A (2 * Real.pi / h) (2 * Real.pi / k) (n * k) =
      heatRectangleRight A (2 * Real.pi / h) (2 * Real.pi / k) (n * k) := by
  have phase {r : ℝ} (hr : 0 < r) :
      ((n : ℝ) * r) * (2 * Real.pi / r) = n * (2 * Real.pi) := by
    field_simp [ne_of_gt hr]
  constructor
  · exact heatRectangle_eq_of_full_turn_left _ _ _ _
      (by rw [phase hh, Real.cos_nat_mul_two_pi])
      (by rw [phase hh]; simpa only [zero_add, Real.sin_zero] using
        Real.sin_add_nat_mul_two_pi 0 n)
  · exact heatRectangle_eq_of_full_turn_right _ _ _ _
      (by rw [phase hk, Real.cos_nat_mul_two_pi])
      (by rw [phase hk]; simpa only [zero_add, Real.sin_zero] using
        Real.sin_add_nat_mul_two_pi 0 n)

/-- The two full traces differ at an explicit positive time. -/
theorem heatRectangle_strict_between_grids (A : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    heatRectangleRight A a b (2 * Real.pi / (a + b)) <
      heatRectangleLeft A a b (2 * Real.pi / (a + b)) := by
  let t := 2 * Real.pi / (a + b)
  have hab : 0 < a + b := add_pos ha hb
  have ht : 0 < t := div_pos Real.two_pi_pos hab
  have hsum : t * (a + b) = 2 * Real.pi := by
    dsimp [t]
    exact div_mul_cancel₀ _ (ne_of_gt hab)
  have hangle : t * a < 2 * Real.pi := by
    nlinarith [mul_pos ht hb]
  have hcos : Real.cos (t * a) < 1 := lt_of_le_of_ne (Real.cos_le_one _) (by
    intro heq
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt
      (by nlinarith [mul_pos ht ha, Real.pi_pos]) hangle).mp heq
    exact (ne_of_gt (mul_pos ht ha)) hz)
  have hcomp : t * b = 2 * Real.pi - t * a := by nlinarith [hsum]
  change heatRectangleRight A a b t < heatRectangleLeft A a b t
  simp only [heatRectangleLeft, heatRectangleRight, conjugatePairHeatTrace_eq,
    mul_zero, Real.cos_zero, mul_one, hsum, Real.cos_two_pi,
    hcomp, Real.cos_two_pi_sub]
  nlinarith [Real.exp_pos (-t * A)]

/-- The ambiguity uses only frequencies strictly inside the natural right parabola. -/
theorem heatRectangle_strict_parabolic {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ c ∈ ({0, a, b, a + b, -a, -b, -(a + b)} : Set ℝ),
      (((1 + (a + b) ^ 2 : ℝ) : ℂ) + (c : ℂ) * Complex.I).im ^ 2 <
        (((1 + (a + b) ^ 2 : ℝ) : ℂ) + (c : ℂ) * Complex.I).re := by
  intro c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, Complex.add_re, Complex.mul_re]
  have hab := mul_pos ha hb
  have hsq := sq_nonneg (a + b)
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> nlinarith

/-- Every pair of positive grid steps admits distinct strict-parabolic packet traces
with identical complete marginal observations. -/
theorem heat_two_grid_marginal_reconstruction_no_go {h k : ℝ}
    (hh : 0 < h) (hk : 0 < k) :
    ∃ A a b : ℝ,
      (∀ n : ℕ,
        heatRectangleLeft A a b (n * h) = heatRectangleRight A a b (n * h) ∧
        heatRectangleLeft A a b (n * k) = heatRectangleRight A a b (n * k)) ∧
      (∃ t : ℝ, 0 < t ∧ heatRectangleRight A a b t < heatRectangleLeft A a b t) ∧
      (∀ c ∈ ({0, a, b, a + b, -a, -b, -(a + b)} : Set ℝ),
        ((A : ℂ) + (c : ℂ) * Complex.I).im ^ 2 <
          ((A : ℂ) + (c : ℂ) * Complex.I).re) := by
  let a := 2 * Real.pi / h
  let b := 2 * Real.pi / k
  have ha : 0 < a := div_pos Real.two_pi_pos hh
  have hb : 0 < b := div_pos Real.two_pi_pos hk
  refine ⟨1 + (a + b) ^ 2, a, b,
    fun n => heatRectangle_two_grid_equal _ hh hk n,
    ⟨2 * Real.pi / (a + b), div_pos Real.two_pi_pos (add_pos ha hb),
      heatRectangle_strict_between_grids _ ha hb⟩,
    heatRectangle_strict_parabolic ha hb⟩

end

end RHTower
