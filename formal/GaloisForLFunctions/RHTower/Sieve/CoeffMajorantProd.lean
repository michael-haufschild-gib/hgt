import GaloisForLFunctions.RHTower.Sieve.CoeffMajorantScale

/-!
# The majorant as a single product

`tendsto_polyEdge_mul_exp_neg` handles expressions of the shape `(1 + a w⁹)(b + c w)`, and the
majorant is a *sum* of three such pieces.  Bounding the sum by one product costs nothing: the two
`w`-dependent pieces already share the factor `1 + a w⁹`, and the constant piece is at most that
factor times itself, since `1 + a w⁹ ≥ 1`.

Evaluating at `2w` rather than `w` only replaces `a` by `512a`, because `(2w)⁹ = 512w⁹`.
-/

namespace RHTower.Sieve

open Real

/-- **The majorant at `2w`, as a single product.** -/
theorem coeffMajorant_le_prod {C C' M₀ a w : ℝ} (hC : 0 ≤ C) (hM₀ : 0 ≤ M₀)
    (ha : 0 ≤ a) (hw : 0 ≤ w) :
    coeffMajorant C C' M₀ a (2 * w)
      ≤ (1 + (512 * a) * w ^ (9 : ℕ))
          * ((8 * C * Real.exp (22 / 4)
                + (8 * C' + 4 + 2 * C) * (2 * Real.exp (22 / 4)) * (5 / 2)
                + M₀ * (4 + 2 * C))
              + ((8 * C' + 4 + 2 * C) * (2 * Real.exp (22 / 4)) * 4) * w) := by
  have hexp : (0 : ℝ) < Real.exp (22 / 4) := Real.exp_pos _
  have hQ : (1 : ℝ) ≤ 1 + (512 * a) * w ^ (9 : ℕ) := by nlinarith [pow_nonneg hw 9]
  have hM : (0 : ℝ) ≤ M₀ * (4 + 2 * C) := by positivity
  have hpow : (2 * w) ^ (9 : ℕ) = 512 * w ^ (9 : ℕ) := by ring
  rw [coeffMajorant, hpow]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (1 + (512 * a) * w ^ (9 : ℕ)) - 1) hM]

end RHTower.Sieve
