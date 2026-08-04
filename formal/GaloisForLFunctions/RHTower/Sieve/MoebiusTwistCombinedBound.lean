import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistConcreteEdges
import GaloisForLFunctions.RHTower.Sieve.MoebiusCombinedBound

/-!
# Collapsing the twisted contour terms

The twist enters the three edge terms only through the truncation height, and

    twistHeight K τ = truncHeight K - |τ|  ≥  truncHeight K / 2   whenever  |τ| ≤ truncHeight K / 2.

So each term of the twisted bound is at most twice the corresponding untwisted term, and the whole
collapse of `MoebiusCombinedBound` transfers with the single factor `2`.  No estimate is repeated:
the twisted bound is deduced from the untwisted one.
-/

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

/-- The side condition of the twisted contour bound already places the twist inside half the
truncation height. -/
theorem abs_le_half_truncHeight {K : ℕ} {τ : ℝ} (hKτ : 5 + 4 * |τ| ≤ (K : ℝ)) :
    |τ| ≤ truncHeight K / 2 := by
  rw [truncHeight]; linarith

/-- **The three twisted terms, combined.**  Twice the untwisted collapse. -/
theorem combined_terms_twist_le {x C C' R E M₀ τ : ℝ}
    (hx1 : 1 ≤ Real.log x) (hx2 : 2 ≤ (Real.log x) ^ ((1 : ℝ) / 10)) (hx0 : 0 < x)
    (hy : Real.log (x + 1) ≤ 2 * Real.log x) (hx1le : Real.log x ≤ Real.log (x + 1))
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hR : 0 ≤ R) (hE : 0 ≤ E) (hM₀ : 0 ≤ M₀)
    (hgap : rightAbscissa (contourParam x) - leftAbscissa (contourParam x) ≤ 1)
    (hgapnn : 0 ≤ rightAbscissa (contourParam x) - leftAbscissa (contourParam x))
    (hcpos : 0 < leftAbscissa (contourParam x))
    (hτ : |τ| ≤ truncHeight (contourParam x) / 2) :
    2 * (R * (C * (x + 1) ^ rightAbscissa (contourParam x)))
          / twistHeight (contourParam x) τ
        + E * (C' * (x + 1) ^ rightAbscissa (contourParam x))
            / (twistHeight (contourParam x) τ) ^ (0 + 1)
            * (rightAbscissa (contourParam x) - leftAbscissa (contourParam x))
        + E * (C' * (x + 1) ^ rightAbscissa (contourParam x))
            / (twistHeight (contourParam x) τ) ^ (0 + 1)
            * (rightAbscissa (contourParam x) - leftAbscissa (contourParam x))
        + max M₀ E * (2 * (x ^ leftAbscissa (contourParam x) / leftAbscissa (contourParam x))
            + 2 * (C * (x + 1) ^ leftAbscissa (contourParam x)))
      ≤ 2 * ((x + 1) * (8 * R * C + 8 * E * C' + max M₀ E * (4 + 2 * C))
          * Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192))) := by
  have hbase := combined_terms_le hx1 hx2 hx0 hy hx1le hC hC' hR hE hM₀ hgap
  have hT4 := exp_div_four_le_truncHeight hx2
  have hTpos : (0 : ℝ) < truncHeight (contourParam x) :=
    lt_of_lt_of_le (by positivity) hT4
  have hTne : truncHeight (contourParam x) ≠ 0 := ne_of_gt hTpos
  have hTw : truncHeight (contourParam x) / 2 ≤ twistHeight (contourParam x) τ := by
    rw [twistHeight]; linarith
  have hTwpos : (0 : ℝ) < twistHeight (contourParam x) τ := by linarith
  have hdiv2 : ∀ A : ℝ, 0 ≤ A →
      A / twistHeight (contourParam x) τ ≤ 2 * (A / truncHeight (contourParam x)) := by
    intro A hA
    have hq : 0 ≤ A / truncHeight (contourParam x) := div_nonneg hA hTpos.le
    rw [div_le_iff₀ hTwpos]
    calc A = 2 * (A / truncHeight (contourParam x)) * (truncHeight (contourParam x) / 2) := by
          field_simp
      _ ≤ 2 * (A / truncHeight (contourParam x)) * twistHeight (contourParam x) τ :=
          mul_le_mul_of_nonneg_left hTw (by linarith)
  -- the three edge terms at most double
  have hxy : (0 : ℝ) < x + 1 := by linarith
  have hpowR : (0 : ℝ) < (x + 1) ^ rightAbscissa (contourParam x) := Real.rpow_pos_of_pos hxy _
  have hpowL : (0 : ℝ) < (x + 1) ^ leftAbscissa (contourParam x) := Real.rpow_pos_of_pos hxy _
  have hpowx : (0 : ℝ) < x ^ leftAbscissa (contourParam x) := Real.rpow_pos_of_pos hx0 _
  have hME : (0 : ℝ) ≤ max M₀ E := le_trans hM₀ (le_max_left _ _)
  have h1 := hdiv2 (2 * (R * (C * (x + 1) ^ rightAbscissa (contourParam x)))) (by positivity)
  have h2raw := hdiv2 (E * (C' * (x + 1) ^ rightAbscissa (contourParam x))) (by positivity)
  have h2 : E * (C' * (x + 1) ^ rightAbscissa (contourParam x))
        / (twistHeight (contourParam x) τ) ^ (0 + 1)
        * (rightAbscissa (contourParam x) - leftAbscissa (contourParam x))
      ≤ 2 * (E * (C' * (x + 1) ^ rightAbscissa (contourParam x))
          / (truncHeight (contourParam x)) ^ (0 + 1)
          * (rightAbscissa (contourParam x) - leftAbscissa (contourParam x))) := by
    rw [pow_one, pow_one]
    have := mul_le_mul_of_nonneg_right h2raw hgapnn
    linarith
  -- the left-edge term is unchanged and nonnegative
  have h4 : (0 : ℝ) ≤ max M₀ E
      * (2 * (x ^ leftAbscissa (contourParam x) / leftAbscissa (contourParam x))
        + 2 * (C * (x + 1) ^ leftAbscissa (contourParam x))) := by
    have : (0 : ℝ) ≤ 2 * (x ^ leftAbscissa (contourParam x) / leftAbscissa (contourParam x))
        + 2 * (C * (x + 1) ^ leftAbscissa (contourParam x)) := by positivity
    exact mul_nonneg hME this
  linarith

end RHTower.Sieve
