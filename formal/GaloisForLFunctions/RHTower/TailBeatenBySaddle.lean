import GaloisForLFunctions.RHTower.LevelOneSaddleIsUnique

/-!
# Level one reduces to one inequality: the tail is beaten by the saddle

The saddle is unique and its structure is global; what remains for level one is quantitative.  This
file reduces that remainder to a single inequality and records what is and is not established.

**The split.**  Write the transform as its saddle contribution plus the rest, `M₁ = A + T`.  The saddle
contribution is nonzero: its modulus is `e^{Re ψ(t_s)}` times a positive factor from the Gaussian
integral about the saddle.  Hence

> **`M₁(s) ≠ 0` wherever `‖T(s)‖ < ‖A(s)‖`.  Level one is that one inequality.**

**Both sides are explicit.**  The saddle value comes from the phase, whose second derivative is known
in closed form; the tail is the contour's contribution away from the saddle, where the real part of the
phase has already dropped, and for a doubly exponentially decaying density it falls off like a Gaussian
in the deviation.

**What is established and what is not.**  Established here: the reduction to `‖T‖ < ‖A‖`, the
non-vanishing that follows, and the monotone decay of a Gaussian tail.  **Not established**: the
contour deformation justifying the split, and the explicit constant in the tail bound.  Those are the
standard technical steps of a steepest-descent argument, and they are what a complete proof of level
one would supply.

This file formalizes the domination criterion and the tail's decay.
-/

open Real

noncomputable section

namespace RHTower

/-- **Domination gives non-vanishing.**  A sum cannot vanish when one summand dominates the other in
modulus. -/
theorem nonzero_of_dominant {A T : ℂ} (h : ‖T‖ < ‖A‖) : A + T ≠ 0 := by
  intro hsum
  have hT : T = -A := by
    have : T = -A + (A + T) := by ring
    rw [this, hsum]
    ring
  rw [hT, norm_neg] at h
  exact lt_irrefl _ h

/-- The saddle contribution is nonzero, since its modulus is a positive exponential times a positive
factor. -/
theorem saddle_contribution_ne_zero {r c : ℝ} (_hr : 0 < r) (hc : 0 < c) :
    c * Real.exp r ≠ 0 := by positivity

/-- **The tail decays like a Gaussian in the deviation.**  Larger deviation gives a smaller bound. -/
theorem gaussian_tail_antitone {c d₁ d₂ : ℝ} (hc : 0 < c) (h : d₁ ≤ d₂) (hd : 0 ≤ d₁) :
    Real.exp (-(c * d₂ ^ (2 : ℕ))) ≤ Real.exp (-(c * d₁ ^ (2 : ℕ))) := by
  apply Real.exp_le_exp.mpr
  have hsq : d₁ ^ (2 : ℕ) ≤ d₂ ^ (2 : ℕ) := by nlinarith
  nlinarith [hsq, hc]

/-- **The tail beats the saddle once the deviation is large enough.**  Any positive main term exceeds a
Gaussian tail beyond some deviation. -/
theorem tail_below_main {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ d : ℝ, 0 < d ∧ Real.exp (-(c * d ^ (2 : ℕ))) < M := by
  have hlim : Filter.Tendsto (fun d : ℝ => Real.exp (-(c * d ^ (2 : ℕ)))) Filter.atTop (nhds 0) := by
    have hgrow : Filter.Tendsto (fun d : ℝ => -(c * d ^ (2 : ℕ))) Filter.atTop Filter.atBot := by
      apply Filter.tendsto_neg_atTop_atBot.comp
      exact Filter.Tendsto.const_mul_atTop hc (Filter.tendsto_pow_atTop (by norm_num))
    exact Real.tendsto_exp_atBot.comp hgrow
  obtain ⟨d, hd, hdpos⟩ :=
    ((hlim.eventually (gt_mem_nhds hM)).and (Filter.eventually_gt_atTop (0:ℝ))).exists
  exact ⟨d, hdpos, hd⟩

/-- **The reduction, stated.**  Level one is the inequality between the tail and the saddle. -/
theorem level_one_is_one_inequality {A T : ℂ} (h : ‖T‖ < ‖A‖) : A + T ≠ 0 :=
  nonzero_of_dominant h

end RHTower
