import Mathlib

/-!
# Reflected Euler-factor modulus neutrality off the critical line

Scalar equality of the moduli of two reflected local Euler denominators does not force the
reflection displacement to vanish.  For any two radii `0 < rminus < rplus < 1`, a unit phase can
be chosen so that `|1-rplus exp(iθ)| = |1-rminus exp(iθ)|`.  Applying this to
`rplus = p^(-1/2+ε)` and `rminus = p^(-1/2-ε)` gives an exact off-line neutral phase at every prime.

This rules out scalar reflected-flank modulus balance as a source for the phase-independent prime
reflection energy.  A successful source-divisor coupling must retain additional prime-coordinate
or positive vector information.
-/

namespace RHTower

open Complex

lemma norm_one_sub_real_mul_exp_mul_I_sq (r θ : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 =
      1 + r ^ 2 - 2 * r * Real.cos θ := by
  rw [Complex.exp_ofReal_mul_I, Complex.sq_norm]
  simp [Complex.normSq_apply, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- Any two distinct radii in `(0,1)` admit a common unit phase at which the corresponding
linear Euler-factor denominators have equal modulus. -/
theorem exists_phase_norm_one_sub_mul_eq {rminus rplus : ℝ}
    (hrminus : 0 < rminus) (hord : rminus < rplus) (hrplus : rplus < 1) :
    ∃ θ : ℝ,
      Real.cos θ = (rplus + rminus) / 2 ∧
      ‖(1 : ℂ) - (rplus : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ =
        ‖(1 : ℂ) - (rminus : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
  let c : ℝ := (rplus + rminus) / 2
  have hcneg : -1 ≤ c := by dsimp [c]; linarith
  have hcpos : c ≤ 1 := by dsimp [c]; linarith
  refine ⟨Real.arccos c, Real.cos_arccos hcneg hcpos, ?_⟩
  have hsquares :
      ‖(1 : ℂ) - (rplus : ℂ) * Complex.exp ((Real.arccos c : ℂ) * Complex.I)‖ ^ 2 =
        ‖(1 : ℂ) - (rminus : ℂ) * Complex.exp ((Real.arccos c : ℂ) * Complex.I)‖ ^ 2 := by
    rw [norm_one_sub_real_mul_exp_mul_I_sq, norm_one_sub_real_mul_exp_mul_I_sq,
      Real.cos_arccos hcneg hcpos]
    dsimp [c]
    ring
  nlinarith [
    norm_nonneg ((1 : ℂ) - (rplus : ℂ) * Complex.exp ((Real.arccos c : ℂ) * Complex.I)),
    norm_nonneg ((1 : ℂ) - (rminus : ℂ) * Complex.exp ((Real.arccos c : ℂ) * Complex.I))]

/-- A single prime Euler factor has exact reflected-modulus-neutral phases at every genuine
horizontal displacement inside the critical strip. -/
theorem exists_prime_reflected_localFactor_modulus_neutral
    {p : ℕ} (hp : 1 < p) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ θ : ℝ,
      ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 + ε) : ℝ) : ℂ) *
          Complex.exp ((θ : ℂ) * Complex.I)‖ =
        ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 - ε) : ℝ) : ℂ) *
          Complex.exp ((θ : ℂ) * Complex.I)‖ := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := zero_lt_one.trans hpR
  have hminusPos : 0 < (p : ℝ) ^ (-1 / 2 - ε) := Real.rpow_pos_of_pos hp0 _
  have hord : (p : ℝ) ^ (-1 / 2 - ε) < (p : ℝ) ^ (-1 / 2 + ε) :=
    Real.rpow_lt_rpow_of_exponent_lt hpR (by linarith)
  have hplusOne : (p : ℝ) ^ (-1 / 2 + ε) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  obtain ⟨θ, -, hθ⟩ := exists_phase_norm_one_sub_mul_eq hminusPos hord hplusOne
  exact ⟨θ, hθ⟩

end RHTower
