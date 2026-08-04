import GaloisForLFunctions.RHTower.Sieve.RightSideTerm

/-!
# The three terms combined

At `K = contourParam (2N)` and decay order `j = 0` every term of the contour bound is the trivial
size `2N+1` times a decaying exponential.  The two rates differ enormously — `(1-c₀)t` for the
right-hand terms against `c₀t/8192` for the left edge — so the sum is bounded by the *slower* one,
and the whole bound takes the single form

    (2N+1) · [ 8·R(K)·C + 8·E(K)·C' + max(M₀, E(K))·(4 + 2C) ] · exp(-c₀ t / 8192).
-/

namespace RHTower.Sieve

open Real

/-- The slower of the two decay rates dominates. -/
theorem exp_right_le_exp_left {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-((1 - zeroFreeConst) * t)) ≤ Real.exp (-(zeroFreeConst * t / 8192)) := by
  have hA2 := zeroFreeConst_le_half
  have hA0 := zeroFreeConst_pos
  refine Real.exp_le_exp.2 ?_
  have hcoef : zeroFreeConst / 8192 ≤ 1 - zeroFreeConst := by linarith
  have := mul_le_mul_of_nonneg_right hcoef ht
  have hrw : zeroFreeConst / 8192 * t = zeroFreeConst * t / 8192 := by ring
  linarith [hrw ▸ this]

/-- The gap between the abscissae is at most one. -/
theorem gap_le_one {K : ℕ} (hlogK : 1 ≤ Real.log K) :
    rightAbscissa K - leftAbscissa K ≤ 1 := by
  have hA0 := zeroFreeConst_pos
  have hA2 := zeroFreeConst_le_half
  have hL0 : (0 : ℝ) < Real.log K := by linarith
  have hL9 : (1 : ℝ) ≤ (Real.log K) ^ 9 := one_le_pow₀ hlogK
  have h2small : zeroFreeConst / (2 * (Real.log K) ^ 9) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA2, hA0]
  have h16small : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ 1 / 32 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA2, hA0]
  have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log K) ^ 9) := by positivity
  rw [rightAbscissa, leftAbscissa]
  linarith

/-- **The three terms, combined.**  Each is bounded by the trivial size times the slower decay. -/
theorem combined_terms_le {x C C' R E M₀ : ℝ}
    (hx1 : 1 ≤ Real.log x) (hx2 : 2 ≤ (Real.log x) ^ ((1 : ℝ) / 10)) (hx0 : 0 < x)
    (hy : Real.log (x + 1) ≤ 2 * Real.log x) (hx1le : Real.log x ≤ Real.log (x + 1))
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hR : 0 ≤ R) (hE : 0 ≤ E) (hM₀ : 0 ≤ M₀)
    (hgap : rightAbscissa (contourParam x) - leftAbscissa (contourParam x) ≤ 1) :
    2 * (R * (C * (x + 1) ^ rightAbscissa (contourParam x))) / truncHeight (contourParam x)
        + E * (C' * (x + 1) ^ rightAbscissa (contourParam x))
            / (truncHeight (contourParam x)) ^ (0 + 1)
            * (rightAbscissa (contourParam x) - leftAbscissa (contourParam x))
        + E * (C' * (x + 1) ^ rightAbscissa (contourParam x))
            / (truncHeight (contourParam x)) ^ (0 + 1)
            * (rightAbscissa (contourParam x) - leftAbscissa (contourParam x))
        + max M₀ E * (2 * (x ^ leftAbscissa (contourParam x) / leftAbscissa (contourParam x))
            + 2 * (C * (x + 1) ^ leftAbscissa (contourParam x)))
      ≤ (x + 1) * (8 * R * C + 8 * E * C' + max M₀ E * (4 + 2 * C))
          * Real.exp (-(zeroFreeConst * (Real.log x) ^ ((1 : ℝ) / 10) / 8192)) := by
  set t : ℝ := (Real.log x) ^ ((1 : ℝ) / 10) with htdef
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hy0 : (0 : ℝ) < x + 1 := by linarith
  have hy1 : (0 : ℝ) ≤ Real.log (x + 1) := by linarith
  have hSlow := exp_right_le_exp_left ht0
  have hSpos : (0 : ℝ) < Real.exp (-(zeroFreeConst * t / 8192)) := Real.exp_pos _
  -- truncation
  have h1 : 2 * (R * (C * (x + 1) ^ rightAbscissa (contourParam x)))
      / truncHeight (contourParam x)
      ≤ 8 * (R * C) * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192)) := by
    have hrw : 2 * (R * (C * (x + 1) ^ rightAbscissa (contourParam x)))
        = (2 * (R * C)) * (x + 1) ^ rightAbscissa (contourParam x) := by ring
    rw [hrw]
    refine le_trans (rightSide_term_le hx2 hx1 hy0 hy1 hy (by positivity)) ?_
    have hstep : 4 * (2 * (R * C)) * (x + 1)
        * Real.exp (-((1 - zeroFreeConst) * t))
        ≤ 4 * (2 * (R * C)) * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192)) := by
      gcongr
    calc 4 * (2 * (R * C)) * (x + 1) * Real.exp (-((1 - zeroFreeConst) * t))
        ≤ 4 * (2 * (R * C)) * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192)) := hstep
      _ = 8 * (R * C) * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192)) := by ring
  -- one horizontal edge
  have h2 : E * (C' * (x + 1) ^ rightAbscissa (contourParam x))
      / (truncHeight (contourParam x)) ^ (0 + 1)
      * (rightAbscissa (contourParam x) - leftAbscissa (contourParam x))
      ≤ 4 * (E * C') * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192)) := by
    have hrw : E * (C' * (x + 1) ^ rightAbscissa (contourParam x))
        = (E * C') * (x + 1) ^ rightAbscissa (contourParam x) := by ring
    have hbase : (E * C') * (x + 1) ^ rightAbscissa (contourParam x)
        / truncHeight (contourParam x)
        ≤ 4 * (E * C') * (x + 1) * Real.exp (-((1 - zeroFreeConst) * t)) :=
      rightSide_term_le hx2 hx1 hy0 hy1 hy (by positivity)
    have hbase0 : (0 : ℝ) ≤ (E * C') * (x + 1) ^ rightAbscissa (contourParam x)
        / truncHeight (contourParam x) := by
      have hT : Real.exp t / 4 ≤ truncHeight (contourParam x) := exp_div_four_le_truncHeight hx2
      have hTpos : (0 : ℝ) < truncHeight (contourParam x) :=
        lt_of_lt_of_le (by positivity) hT
      have : (0 : ℝ) < (x + 1) ^ rightAbscissa (contourParam x) := Real.rpow_pos_of_pos hy0 _
      positivity
    have hgap0 : (0 : ℝ) ≤ rightAbscissa (contourParam x) - leftAbscissa (contourParam x) := by
      rw [rightAbscissa, leftAbscissa]
      have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log (contourParam x)) ^ 9) := by
        have hA0 := zeroFreeConst_pos
        have ht1 : (1 : ℝ) ≤ t := by linarith
        have hL1 : (1 : ℝ) ≤ Real.log (contourParam x) := le_trans ht1 (le_log_contourParam x)
        positivity
      have h2p : (0 : ℝ) < zeroFreeConst / (2 * (Real.log (contourParam x)) ^ 9) := by
        have hA0 := zeroFreeConst_pos
        have ht1 : (1 : ℝ) ≤ t := by linarith
        have hL1 : (1 : ℝ) ≤ Real.log (contourParam x) := le_trans ht1 (le_log_contourParam x)
        positivity
      linarith
    rw [hrw, pow_one]
    calc (E * C') * (x + 1) ^ rightAbscissa (contourParam x) / truncHeight (contourParam x)
          * (rightAbscissa (contourParam x) - leftAbscissa (contourParam x))
        ≤ (E * C') * (x + 1) ^ rightAbscissa (contourParam x) / truncHeight (contourParam x)
            * 1 := mul_le_mul_of_nonneg_left hgap hbase0
      _ = (E * C') * (x + 1) ^ rightAbscissa (contourParam x)
            / truncHeight (contourParam x) := by ring
      _ ≤ 4 * (E * C') * (x + 1) * Real.exp (-((1 - zeroFreeConst) * t)) := hbase
      _ ≤ 4 * (E * C') * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192)) := by gcongr
  -- the left edge
  have h4 : max M₀ E * (2 * (x ^ leftAbscissa (contourParam x) / leftAbscissa (contourParam x))
      + 2 * (C * (x + 1) ^ leftAbscissa (contourParam x)))
      ≤ max M₀ E * ((4 + 2 * C) * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192))) :=
    leftEdge_term_le hx1 hx0 hC (le_trans hM₀ (le_max_left _ _)) hy0 hx1le (by linarith)
  have hexpand : (x + 1) * (8 * R * C + 8 * E * C' + max M₀ E * (4 + 2 * C))
      * Real.exp (-(zeroFreeConst * t / 8192))
      = 8 * (R * C) * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192))
        + 4 * (E * C') * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192))
        + 4 * (E * C') * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192))
        + max M₀ E * ((4 + 2 * C) * (x + 1) * Real.exp (-(zeroFreeConst * t / 8192))) := by
    ring
  rw [hexpand]
  linarith

end RHTower.Sieve
