import GaloisForLFunctions.RHTower.Sieve.RouteTPolyMajorants
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

/-!
# The contour and truncation thresholds hold eventually

Both prefactors are a constant times a power of `L` times `(1 + log L)²`
(`Sieve/RouteTPolyMajorants`), so their logarithms are `O(1 + log L)`; multiplying by the
reciprocal-width budget `≍ L^{0.9}(1+log L)²` keeps them below `L^{0.99}`, and the truncation
exponent contributes only `L^{0.46}` against `L^{0.6}`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The logarithm of a polynomial-times-polylogarithm majorant. -/
theorem log_le_of_le_poly {X M L α : ℝ} (hX : 0 < X) (hM : 0 < M) (hL : 1 ≤ L) (hα : 0 ≤ α)
    (h : X ≤ M * L ^ α * (1 + Real.log L) ^ 2) :
    Real.log X ≤ (|Real.log M| + α + 2) * (1 + Real.log L) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL
  have hLa : (0 : ℝ) < L ^ α := Real.rpow_pos_of_pos hL0 _
  have hlog := Real.log_le_log hX h
  have hval : Real.log (M * L ^ α * (1 + Real.log L) ^ 2)
      = Real.log M + α * Real.log L + 2 * Real.log (1 + Real.log L) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (ne_of_gt hM) (ne_of_gt hLa),
      Real.log_rpow hL0, Real.log_pow]
    push_cast
    ring
  rw [hval] at hlog
  have hlog1 : Real.log (1 + Real.log L) ≤ Real.log L := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + Real.log L by linarith)
    linarith
  have habs : Real.log M ≤ |Real.log M| := le_abs_self _
  have habs0 : (0 : ℝ) ≤ |Real.log M| := abs_nonneg _
  nlinarith [hlog, hlog1, habs, habs0, hlogL, hα]

/-- **The contour threshold of the schedule.** -/
theorem eventually_contour_threshold {A C : ℝ} (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop,
      Real.log (9 * C * (1 + (4 + 2 * L) * routeTBudgetHat A L + 2 * L) * (9 * (2 + L)))
          * (6 * routeTBudgetHat A L) ≤ L ^ (0.99 : ℝ) := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  set G1 : ℝ := 211680 * routeTZeroFreeDeltaEnvelopeConstant A with hG1def
  have hG10 : (0 : ℝ) < G1 := by rw [hG1def]; positivity
  set M1 : ℝ := 243 * C * (3 + 6 * G1) with hM1def
  have hM10 : (0 : ℝ) < M1 := by rw [hM1def]; positivity
  set K1 : ℝ := 6 * G1 * (|Real.log M1| + 2.9 + 2) with hK1def
  have hfinal := eventually_const_mul_rpow_polylog_le_rpow (C := K1) (α := (0.9 : ℝ))
    (β := (0.99 : ℝ)) 3 (by norm_num)
  filter_upwards [hfinal, Filter.eventually_ge_atTop (1 : ℝ)] with L hK hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  have habs : |Real.log L| = Real.log L := abs_of_nonneg hlogL
  rw [habs] at hK
  set G : ℝ := routeTBudgetHat A L with hGdef
  have hG0 : (0 : ℝ) < G := routeTBudgetHat_pos hL1
  have hGle : G ≤ G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2 := by
    have hbase := routeTBudgetHat_le_polylog (A := A) hL1
    rw [habs] at hbase
    rw [hGdef, hG1def]
    nlinarith [hbase]
  set X : ℝ := 9 * C * (1 + (4 + 2 * L) * G + 2 * L) * (9 * (2 + L)) with hXdef
  have hX0 : (0 : ℝ) < X := by rw [hXdef]; positivity
  have hXle : X ≤ M1 * L ^ (2.9 : ℝ) * (1 + Real.log L) ^ 2 := by
    rw [hXdef, hM1def]
    exact contour_prefactor_le hC hL1 hG0 hG10 hGle
  have hlogX := log_le_of_le_poly hX0 hM10 hL1 (by norm_num) hXle
  have hB0 : (0 : ℝ) ≤ (|Real.log M1| + 2.9 + 2) * (1 + Real.log L) := by positivity
  have hstep1 : Real.log X * (6 * G) ≤ ((|Real.log M1| + 2.9 + 2) * (1 + Real.log L)) * (6 * G) :=
    mul_le_mul_of_nonneg_right hlogX (by positivity)
  have hstep2 : ((|Real.log M1| + 2.9 + 2) * (1 + Real.log L)) * (6 * G)
      ≤ ((|Real.log M1| + 2.9 + 2) * (1 + Real.log L))
        * (6 * (G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hB0
    linarith [hGle]
  have hval : ((|Real.log M1| + 2.9 + 2) * (1 + Real.log L))
        * (6 * (G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2))
      = K1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 3 := by
    rw [hK1def]; ring
  rw [hval] at hstep2
  linarith [hstep1, hstep2, hK]

/-- **The truncation threshold of the schedule.** -/
theorem eventually_trunc_threshold {A C : ℝ} (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop,
      routeTTruncHat L * L
        + Real.log (9 * C * (3 : ℝ) ^ routeTTruncHat L
            * (2 + L ^ 2 + (4 + 2 * L) * routeTBudgetHat A L) * (9 * (2 + L)))
        ≤ L ^ (0.6 : ℝ) := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hKpos := routeTWidthUpperConst_pos
  set G1 : ℝ := 211680 * routeTZeroFreeDeltaEnvelopeConstant A with hG1def
  have hG10 : (0 : ℝ) < G1 := by rw [hG1def]; positivity
  set M2 : ℝ := 729 * C * (3 + 6 * G1) with hM2def
  have hM20 : (0 : ℝ) < M2 := by rw [hM2def]; positivity
  set v1 : ℝ := 2 / (3 * routeTWidthUpperConst) with hv1def
  have hv10 : (0 : ℝ) < v1 := by rw [hv1def]; positivity
  have hlim1 := eventually_const_mul_rpow_polylog_le_rpow (C := v1) (α := (0.46 : ℝ))
    (β := (0.53 : ℝ)) 0 (by norm_num)
  have hlim2 := eventually_const_mul_rpow_polylog_le_rpow (C := |Real.log M2| + 3 + 2)
    (α := (0 : ℝ)) (β := (0.05 : ℝ)) 1 (by norm_num)
  have hlim3 := eventually_const_mul_rpow_polylog_le_rpow (C := 2) (α := (0.53 : ℝ))
    (β := (0.6 : ℝ)) 0 (by norm_num)
  have hvsmall : Tendsto (fun L : ℝ => v1 * L ^ (-(0.54 : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (0.54 : ℝ)) (by norm_num)).const_mul v1
    rw [mul_zero] at h
    exact h
  filter_upwards [hlim1, hlim2, hlim3,
    Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hvsmall,
    Filter.eventually_ge_atTop (1 : ℝ)] with L h1 h2 h3 hvle hL1
  have hL0 : (0 : ℝ) < L := by linarith
  have hlogL : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  have habs : |Real.log L| = Real.log L := abs_of_nonneg hlogL
  rw [habs] at h1 h2 h3
  simp only [pow_zero, mul_one, Real.rpow_zero, pow_one] at h1 h2 h3
  set G : ℝ := routeTBudgetHat A L with hGdef
  have hG0 : (0 : ℝ) < G := routeTBudgetHat_pos hL1
  have hGle : G ≤ G1 * L ^ (0.9 : ℝ) * (1 + Real.log L) ^ 2 := by
    have hbase := routeTBudgetHat_le_polylog (A := A) hL1
    rw [habs] at hbase
    rw [hGdef, hG1def]
    nlinarith [hbase]
  set v : ℝ := routeTTruncHat L with hvdef
  have hvle' : v ≤ v1 * L ^ (-(0.54 : ℝ)) := by rw [hvdef, hv1def]; exact routeTTruncHat_le hL1
  have hv0 : (0 : ℝ) < v := by
    rw [hvdef, routeTTruncHat]
    have hp : (0 : ℝ) < (L ^ (0.6 : ℝ) / Real.log 2) ^ ((9 : ℝ) / 10) := by
      have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have : (0 : ℝ) < L ^ (0.6 : ℝ) := Real.rpow_pos_of_pos hL0 _
      exact Real.rpow_pos_of_pos (by positivity) _
    positivity
  have hv1' : v ≤ 1 := le_trans hvle' hvle
  have h3v : (3 : ℝ) ^ v ≤ 3 := by
    have : (3 : ℝ) ^ v ≤ (3 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hv1'
    rwa [Real.rpow_one] at this
  -- the linear term
  have hvL : v * L ≤ v1 * L ^ (0.46 : ℝ) := by
    have hmul : v * L ≤ (v1 * L ^ (-(0.54 : ℝ))) * L := by
      exact mul_le_mul_of_nonneg_right hvle' hL0.le
    have hval : (v1 * L ^ (-(0.54 : ℝ))) * L = v1 * L ^ (0.46 : ℝ) := by
      rw [mul_assoc]
      congr 1
      have : L ^ (-(0.54 : ℝ)) * L = L ^ (-(0.54 : ℝ) + 1) := by
        rw [Real.rpow_add hL0, Real.rpow_one]
      rw [this]
      norm_num
    linarith [hmul, hval.le, hval.ge]
  -- the logarithmic term
  set Y : ℝ := 9 * C * (3 : ℝ) ^ v * (2 + L ^ 2 + (4 + 2 * L) * G) * (9 * (2 + L)) with hYdef
  have hY0 : (0 : ℝ) < Y := by
    have h3v0 : (0 : ℝ) < (3 : ℝ) ^ v := Real.rpow_pos_of_pos (by norm_num) _
    rw [hYdef]; positivity
  have hYle : Y ≤ M2 * L ^ (3 : ℝ) * (1 + Real.log L) ^ 2 := by
    rw [hYdef, hM2def]
    exact trunc_prefactor_le hC hL1 hG0 hG10 hGle h3v
  have hlogY := log_le_of_le_poly hY0 hM20 hL1 (by norm_num) hYle
  have h05 : L ^ (0.05 : ℝ) ≤ L ^ (0.53 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  linarith [hvL, hlogY, h1, h2, h3, h05]

end

end RHTower.Sieve
