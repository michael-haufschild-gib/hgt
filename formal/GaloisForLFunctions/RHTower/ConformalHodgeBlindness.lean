import Mathlib

/-!
# Conformal completions are blind off their line

Let a real one-parameter family of linear maps `V c` act on a complex vector space, let `p` be a
seminorm that the flow scales conformally, `p (V c u) = exp (κ c) * p u`, and let `E` be a linear
functional that the flow scales by a complex character, `E (V c u) = exp (λ c) * E u`.

If `Re λ ≠ κ` and `E` is not identically zero, then `E` is not bounded by any multiple of `p`.
The rescaled flow orbit `exp (-λ c) • V c u₀` keeps `E` fixed while its `p`-size is
`exp ((κ - Re λ) c) * p u₀`, which tends to zero along one direction of `c`.

Consequence for the Hodge route (HF): every flow-natural Hodge seminorm on arithmetic `H¹` is
blind to spectral characters off its conformal line.  Positivity obtained from a conformal
(Kähler / Deninger–Singhof) structure therefore cannot see off-line zeros.  Faithfulness is a
separate input and carries the whole content of the Riemann hypothesis (STATUS CANNOT-462).
-/

open Real Filter Topology

namespace RHTower

/-- **Conformal blindness.**  A conformally scaled seminorm cannot bound a nonzero character of
off-line exponent. -/
theorem not_bounded_of_conformal_offLine {W : Type*} [AddCommGroup W] [Module ℂ W]
    (V : ℝ → W →ₗ[ℂ] W) (p : Seminorm ℂ W) (E : W →ₗ[ℂ] ℂ) (κ : ℝ) (lam : ℂ)
    (hp : ∀ c u, p (V c u) = Real.exp (κ * c) * p u)
    (hE : ∀ c u, E (V c u) = Complex.exp (lam * c) * E u)
    (hoff : lam.re ≠ κ) {u₀ : W} (hu₀ : E u₀ ≠ 0) :
    ¬ ∃ C : ℝ, ∀ u, ‖E u‖ ≤ C * p u := by
  rintro ⟨C, hC⟩
  -- the rescaled orbit keeps the character value fixed
  have hfix : ∀ c : ℝ, E (Complex.exp (-(lam * c)) • V c u₀) = E u₀ := by
    intro c
    rw [map_smul, hE, smul_eq_mul, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, one_mul]
  have hsize : ∀ c : ℝ, p (Complex.exp (-(lam * c)) • V c u₀) =
      Real.exp ((κ - lam.re) * c) * p u₀ := by
    intro c
    rw [map_smul_eq_mul, hp, Complex.norm_exp, ← mul_assoc, ← Real.exp_add]
    congr 2
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    ring
  -- choose the direction in which the conformal factor decays
  set δ : ℝ := κ - lam.re with hδ
  have hδne : δ ≠ 0 := by rw [hδ]; exact sub_ne_zero.mpr (Ne.symm hoff)
  have hpos : 0 < ‖E u₀‖ := norm_pos_iff.mpr hu₀
  have hbound : ∀ c : ℝ, ‖E u₀‖ ≤ C * (Real.exp (δ * c) * p u₀) := by
    intro c
    have := hC (Complex.exp (-(lam * c)) • V c u₀)
    rwa [hfix, hsize] at this
  -- the right-hand side tends to zero along `c = -t / δ`, `t → ∞`
  have hlim : Tendsto (fun t : ℝ => C * (Real.exp (δ * (-t / δ)) * p u₀)) atTop (𝓝 0) := by
    have hsimp : (fun t : ℝ => C * (Real.exp (δ * (-t / δ)) * p u₀)) =
        fun t : ℝ => (C * p u₀) * Real.exp (-t) := by
      funext t
      have : δ * (-t / δ) = -t := by field_simp
      rw [this]; ring
    rw [hsimp]
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (C * p u₀)
  have hge : ‖E u₀‖ ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun t => hbound (-t / δ))
  linarith

end RHTower
