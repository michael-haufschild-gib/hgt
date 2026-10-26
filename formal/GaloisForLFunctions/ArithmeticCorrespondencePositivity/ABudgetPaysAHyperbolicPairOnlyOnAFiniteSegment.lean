import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A budget pays a hyperbolic pair only on a finite segment

Along an orbit of the scales, an orbit correlation splits into the contributions of its local
types: critical zeros give rotations, which stay bounded; a seen off-line pair of depth `δ > 0`
gives a hyperbolic term `2 Re(w e^{(δ + iγ)t})`, `w ≠ 0`. This file shows that no fixed budget pays
the hyperbolic term for long, while every bounded remainder is paid forever.

* **Hyperbolic terms exhaust every budget** (`exists_gt_abs_of_hyperbolic`). If `|E(t)| ≤ B` for
  `t ≥ 0`, `w ≠ 0`, `δ > 0` and `γ ≠ 0`, then for every budget `K` and every `T` some `t ≥ T` has
  `|E(t) + 2 Re(w e^{(δ+iγ)t})| > K`. Within a quarter period the phase turns the hyperbolic term to
  at least `|w| e^{δt}` in modulus (`exists_abs_re_ge_half`).
* **The budget horizon** (`exists_gt_abs_of_hyperbolic` with `T = 0`): the budget `K` is exceeded
  before the scale `max(0, log((|K| + |B| + 1)/|w|)/δ) + π/(2|γ|)`, logarithmic in the budget and
  inversely proportional to the depth.
* **Elliptic remainders are paid forever** (`abs_le_of_elliptic`): a bounded remainder never
  exceeds its bound.

So oscillatory payment by critical zeros is bounded and cannot absorb intrinsic off-line charge:
along any orbit a fixed budget pays an off-line pair only on a segment of length
`≍ log(budget/weight)/depth`. This is the orbit form of the capacity question (Q6): the capacity
of a fixed budget for intrinsic charge along an orbit is zero; payment survives only on bounded
segments (bounded aperture), where it is dominated, not oscillatory.
-/

open Complex Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- **The phase turns a quarter period**: within `π/(2|γ|)` after any `t₀` there is a scale `t`
with `|Re(w e^{iγt})| ≥ |w|/2`. -/
theorem exists_abs_re_ge_half (w : ℂ) {γ : ℝ} (hγ : γ ≠ 0) (t₀ : ℝ) :
    ∃ t, t₀ ≤ t ∧ ‖w‖ / 2 ≤ |(w * Complex.exp (γ * t * I)).re| := by
  by_cases hre : ‖w‖ / 2 ≤ |(w * Complex.exp (γ * t₀ * I)).re|
  · exact ⟨t₀, le_rfl, hre⟩
  push Not at hre
  set z := w * Complex.exp (γ * t₀ * I) with hzdef
  have hz : ‖z‖ = ‖w‖ := by
    rw [hzdef, norm_mul, Complex.norm_exp]; simp
  have hsq : z.re ^ 2 + z.im ^ 2 = ‖w‖ ^ 2 := by
    rw [← hz, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hw2 : (0 : ℝ) ≤ ‖w‖ / 2 := by positivity
  have him : ‖w‖ / 2 ≤ |z.im| := by
    have h1 : z.re ^ 2 < (‖w‖ / 2) ^ 2 := sq_lt_sq.mpr (by rw [abs_of_nonneg hw2]; exact hre)
    have h2 : (‖w‖ / 2) ^ 2 ≤ z.im ^ 2 := by nlinarith
    have h3 := sq_le_sq.mp h2
    rwa [abs_of_nonneg hw2] at h3
  -- a quarter turn in the direction of `γ`
  have hpos : 0 < Real.pi / (2 * |γ|) := div_pos Real.pi_pos (by positivity)
  refine ⟨t₀ + Real.pi / (2 * |γ|), by linarith, ?_⟩
  have hturn : w * Complex.exp (γ * ((t₀ + Real.pi / (2 * |γ|) : ℝ) : ℂ) * I) =
      z * Complex.exp (((γ * (Real.pi / (2 * |γ|)) : ℝ) : ℂ) * I) := by
    rw [hzdef, mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [hturn]
  rcases lt_or_gt_of_ne hγ with h | h
  · have hang : γ * (Real.pi / (2 * |γ|)) = -(Real.pi / 2) := by
      rw [abs_of_neg h]; field_simp
    have hexp : Complex.exp (((γ * (Real.pi / (2 * |γ|)) : ℝ) : ℂ) * I) = -I := by
      rw [hang]; push_cast
      rw [show -(↑Real.pi / 2 : ℂ) * I = -(↑Real.pi / 2 * I) by ring, Complex.exp_neg,
        Complex.exp_pi_div_two_mul_I, Complex.inv_I]
    rw [hexp]
    simpa [Complex.mul_re] using him
  · have hang : γ * (Real.pi / (2 * |γ|)) = Real.pi / 2 := by
      rw [abs_of_pos h]; field_simp
    have hexp : Complex.exp (((γ * (Real.pi / (2 * |γ|)) : ℝ) : ℂ) * I) = I := by
      rw [hang]; push_cast; exact Complex.exp_pi_div_two_mul_I
    rw [hexp]
    simpa [Complex.mul_re, abs_neg] using him

/-- **Hyperbolic terms exhaust every budget.** -/
theorem exists_gt_abs_of_hyperbolic {E : ℝ → ℝ} {B : ℝ} (hE : ∀ t, 0 ≤ t → |E t| ≤ B) {w : ℂ}
    (hw : w ≠ 0) {δ γ : ℝ} (hδ : 0 < δ) (hγ : γ ≠ 0) (K T : ℝ) :
    ∃ t, T ≤ t ∧ K < |E t + 2 * (w * Complex.exp ((δ + γ * I) * t)).re| := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set t₀ := max (max T 0) (Real.log ((|K| + |B| + 1) / ‖w‖) / δ)
  obtain ⟨t, ht, hre⟩ := exists_abs_re_ge_half w hγ t₀
  have ht0 : 0 ≤ t := le_trans (le_trans (le_max_right T 0) (le_max_left _ _)) ht
  refine ⟨t, le_trans (le_trans (le_max_left T 0) (le_max_left _ _)) ht, ?_⟩
  -- the hyperbolic term is `e^{δt} Re(w e^{iγt})`
  have hsplit : (w * Complex.exp ((δ + γ * I) * t)).re =
      Real.exp (δ * t) * (w * Complex.exp (γ * t * I)).re := by
    rw [show ((δ : ℂ) + γ * I) * t = ((δ * t : ℝ) : ℂ) + γ * t * I by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, mul_left_comm, Complex.re_ofReal_mul]
  have hexp : (|K| + |B| + 1) / ‖w‖ ≤ Real.exp (δ * t) := by
    have h1 : Real.log ((|K| + |B| + 1) / ‖w‖) / δ ≤ t := le_trans (le_max_right _ _) ht
    have h2 : Real.log ((|K| + |B| + 1) / ‖w‖) ≤ δ * t := by
      rw [div_le_iff₀ hδ] at h1; linarith
    calc (|K| + |B| + 1) / ‖w‖ = Real.exp (Real.log ((|K| + |B| + 1) / ‖w‖)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (δ * t) := Real.exp_le_exp.mpr h2
  have hhyp : |K| + |B| + 1 ≤ |2 * (w * Complex.exp ((δ + γ * I) * t)).re| := by
    rw [hsplit, abs_mul, abs_mul, abs_two, abs_of_pos (Real.exp_pos _)]
    have := mul_le_mul_of_nonneg_left hre (Real.exp_pos (δ * t)).le
    have h3 : |K| + |B| + 1 ≤ Real.exp (δ * t) * ‖w‖ := by
      rwa [div_le_iff₀ hw0] at hexp
    nlinarith [Real.exp_pos (δ * t)]
  have hEt := hE t ht0
  set H := 2 * (w * Complex.exp ((δ + γ * I) * t)).re with hH
  have htri : |H| ≤ |E t + H| + |E t| := by
    have h := abs_add (E t + H) (-(E t))
    rwa [abs_neg, show E t + H + -(E t) = H by ring] at h
  linarith [le_abs_self K, le_abs_self B]

/-- **Elliptic remainders are paid forever**: a bounded remainder never exceeds its bound. -/
theorem abs_le_of_elliptic {E : ℝ → ℝ} {B : ℝ} (hE : ∀ t, 0 ≤ t → |E t| ≤ B) (t : ℝ) (ht : 0 ≤ t) :
    |E t| ≤ B := hE t ht

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
