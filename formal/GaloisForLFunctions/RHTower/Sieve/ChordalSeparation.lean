import GaloisForLFunctions.RHTower.Sieve.RootsOfUnityFrequencies

/-!
# Arc separation versus chordal separation

The Gram-row bound of `FrequencyGramRow.lean` is stated in terms of the *chordal* separation
`‖conj(ξ_r) ξ_t - 1‖` of two frequencies, whereas a sieve hypothesis is normally an *arc*
separation.  The two are comparable:

`‖exp(2πiα) - 1‖ = 2 |sin(πα)| ≥ 4|α|`  for `|α| ≤ 1/2`,

the inequality being Jordan's `sin t ≥ (2/π) t` on `[0, π/2]`.  So frequencies separated by `δ` in
arc length are separated by at least `4δ` in chord, and the reciprocal separations appearing in the
Gram row are bounded by `(4δ)^{-1}` times the corresponding harmonic weights.

This is the last elementary conversion between the two ways of stating a large sieve hypothesis.
-/

namespace RHTower.Sieve

open Real

/-- The chord subtended by an arc. -/
theorem norm_exp_I_sub_one (θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hsq : ‖Complex.exp (θ * Complex.I) - 1‖ ^ (2 : ℕ) = (2 * |Real.sin (θ / 2)|) ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.exp_mul_I]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.mul_I_re,
      Complex.mul_I_im, Complex.cos_ofReal_im, Complex.sin_ofReal_im]
    have hhalf : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ (2 : ℕ) := by
      have h := Real.cos_two_mul' (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at h
      have hpy := Real.sin_sq_add_cos_sq (θ / 2)
      nlinarith [h, hpy]
    have hsin : Real.sin θ ^ (2 : ℕ) = 1 - Real.cos θ ^ (2 : ℕ) := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [mul_pow, sq_abs]
    nlinarith [hhalf, hsin]
  have h1 : (0 : ℝ) ≤ ‖Complex.exp (θ * Complex.I) - 1‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith [hsq, h1, h2]

/-- **Arc separation dominates chordal separation.**  Jordan's inequality in sieve form. -/
theorem four_mul_le_norm_exp_two_pi_I_sub_one {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    4 * α ≤ ‖Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) - 1‖ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [norm_exp_I_sub_one]
  have hval : (2 * Real.pi * α) / 2 = Real.pi * α := by ring
  rw [hval]
  have hnn : 0 ≤ Real.pi * α := by positivity
  have hle : Real.pi * α ≤ Real.pi / 2 := by nlinarith [hpi, h1]
  have hjordan : 2 / Real.pi * (Real.pi * α) ≤ Real.sin (Real.pi * α) :=
    Real.mul_le_sin hnn hle
  have hsimp : 2 / Real.pi * (Real.pi * α) = 2 * α := by
    field_simp
  rw [hsimp] at hjordan
  have habs : Real.sin (Real.pi * α) ≤ |Real.sin (Real.pi * α)| := le_abs_self _
  linarith

end RHTower.Sieve
