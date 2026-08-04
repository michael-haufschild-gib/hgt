import GaloisForLFunctions.RHTower.Sieve.MoebiusCombinedBound
import GaloisForLFunctions.RHTower.Sieve.PolyExpDecay
import GaloisForLFunctions.RHTower.Sieve.EdgeBoundAtChoice

/-!
# The coefficient, majorised by a polynomial

The coefficient of the combined bound is `8RC + 8EC' + max(M₀,E)(4+2C)`, built from the two edge
bounds.  At the balanced parameter both are polynomials in `t`, so the coefficient is majorised by
an explicit polynomial, and the product of that polynomial with the decaying exponential tends to
zero.
-/

namespace RHTower.Sieve

open Filter Topology Real

/-- The explicit majorant of the combined bound's coefficient. -/
noncomputable def coeffMajorant (C C' M₀ a t : ℝ) : ℝ :=
  8 * C * Real.exp (22 / 4) * (1 + a * t ^ 9)
    + (8 * C' + 4 + 2 * C) * (2 * Real.exp (22 / 4)) * ((1 + a * t ^ 9) * (5 / 2 + 2 * t))
    + M₀ * (4 + 2 * C)

/-- **The majorant against the decaying exponential.** -/
theorem tendsto_coeffMajorant_mul_exp_neg {C C' M₀ a κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun t : ℝ => coeffMajorant C C' M₀ a t * Real.exp (-(κ * t))) atTop (𝓝 0) := by
  have h9 : Tendsto (fun t : ℝ => (1 + a * t ^ 9) * Real.exp (-(κ * t))) atTop (𝓝 0) :=
    tendsto_poly9_mul_exp_neg hκ
  have hE : Tendsto (fun t : ℝ => (1 + a * t ^ 9) * (5 / 2 + 2 * t) * Real.exp (-(κ * t)))
      atTop (𝓝 0) := tendsto_polyEdge_mul_exp_neg hκ
  have h0 : Tendsto (fun t : ℝ => t ^ (0 : ℕ) * Real.exp (-(κ * t))) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_mul 0 hκ
  have hsum : Tendsto (fun t : ℝ =>
      (8 * C * Real.exp (22 / 4)) * ((1 + a * t ^ 9) * Real.exp (-(κ * t)))
        + ((8 * C' + 4 + 2 * C) * (2 * Real.exp (22 / 4)))
            * ((1 + a * t ^ 9) * (5 / 2 + 2 * t) * Real.exp (-(κ * t)))
        + (M₀ * (4 + 2 * C)) * (t ^ (0 : ℕ) * Real.exp (-(κ * t))))
      atTop (𝓝 ((8 * C * Real.exp (22 / 4)) * 0
        + ((8 * C' + 4 + 2 * C) * (2 * Real.exp (22 / 4))) * 0 + (M₀ * (4 + 2 * C)) * 0)) :=
    ((h9.const_mul _).add (hE.const_mul _)).add (h0.const_mul _)
  simp only [mul_zero, add_zero] at hsum
  refine hsum.congr fun t => ?_
  rw [coeffMajorant]
  ring

/-- **The coefficient is majorised.**  Both edge bounds are polynomials in `t` at the balanced
parameter, and `max` is bounded by the sum. -/
theorem coeff_le_coeffMajorant {x C C' M₀ : ℝ} (hx : 1 ≤ Real.log x)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hM₀ : 0 ≤ M₀) :
    8 * invZetaRightBound (contourParam x) * C
        + 8 * invZetaEdgeBound (contourParam x) * C'
        + max M₀ (invZetaEdgeBound (contourParam x)) * (4 + 2 * C)
      ≤ coeffMajorant C C' M₀ (1024 / zeroFreeConst) ((Real.log x) ^ ((1 : ℝ) / 10)) := by
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 10) with htdef
  have hA0 := zeroFreeConst_pos
  have ht1 : (1 : ℝ) ≤ t := Real.one_le_rpow hx (by norm_num)
  have hR := invZetaRightBound_contourParam_le hx
  have hE := invZetaEdgeBound_contourParam_le hx
  have hEnn : 0 ≤ invZetaEdgeBound (contourParam x) := invZetaEdgeBound_nonneg _
  have hpoly : 1024 * t ^ 9 / zeroFreeConst = (1024 / zeroFreeConst) * t ^ 9 := by ring
  rw [hpoly] at hR hE
  have hmax : max M₀ (invZetaEdgeBound (contourParam x))
      ≤ M₀ + invZetaEdgeBound (contourParam x) :=
    max_le (by linarith) (by linarith)
  have hc4 : (0 : ℝ) ≤ 4 + 2 * C := by linarith
  have hstep1 : 8 * invZetaRightBound (contourParam x) * C
      ≤ 8 * C * Real.exp (22 / 4) * (1 + (1024 / zeroFreeConst) * t ^ 9) := by
    nlinarith [hR, hC]
  have hstep2 : 8 * invZetaEdgeBound (contourParam x) * C'
      + max M₀ (invZetaEdgeBound (contourParam x)) * (4 + 2 * C)
      ≤ (8 * C' + 4 + 2 * C) * (2 * Real.exp (22 / 4))
          * ((1 + (1024 / zeroFreeConst) * t ^ 9) * (5 / 2 + 2 * t))
        + M₀ * (4 + 2 * C) := by
    have hmaxmul : max M₀ (invZetaEdgeBound (contourParam x)) * (4 + 2 * C)
        ≤ (M₀ + invZetaEdgeBound (contourParam x)) * (4 + 2 * C) :=
      mul_le_mul_of_nonneg_right hmax hc4
    nlinarith [hE, hC', hmaxmul, hc4]
  rw [coeffMajorant]
  linarith

end RHTower.Sieve
