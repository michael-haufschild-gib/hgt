import GaloisForLFunctions.RHTower.BaezDuarteFeatureNorm

/-!
# The normalized source angle

Dividing the coherent component of the spectral feature by the feature norm gives the angle
`angle_k = ‖Π_* Y_k‖ / ‖Y_k‖`.  Because the feature norm is comparable to `k^{-1/4}` in both
directions, the Báez--Duarte coefficient decay `c_k = O(k^{-3/4+ε})` and the angle decay
`angle_k = O(k^{-1/2+ε})` are the same statement.
-/

namespace RHTower

open Real MeasureTheory

noncomputable section

theorem sqrt_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

theorem sqrt_div_sqrt_eq {c : ℝ} (hc : 0 ≤ c) {x : ℝ} (hx : 0 < x) :
    Real.sqrt (c / Real.sqrt x) = Real.sqrt c * x ^ (-(1 : ℝ) / 4) := by
  rw [Real.sqrt_div hc, sqrt_sqrt_eq_rpow hx.le, div_eq_mul_inv]
  congr 1
  rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring, Real.rpow_neg hx.le]

theorem norm_bdFeatureLp_pos {k : ℕ} (hk : 7 ≤ k) : 0 < ‖bdFeatureLp k‖ := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have h := le_norm_bdFeatureLp_sq hk
  have hlow : (0 : ℝ) < (1 / (500 * squarefreeMobiusTotal 2)) / Real.sqrt (k : ℝ) := by positivity
  nlinarith [norm_nonneg (bdFeatureLp k)]

/-- The upper bound on the feature norm. -/
theorem norm_bdFeatureLp_le {k : ℕ} (hk : 1 ≤ k) :
    ‖bdFeatureLp k‖
      ≤ Real.sqrt (5 / (2 * squarefreeMobiusTotal 2)) * ((k : ℝ)) ^ (-(1 : ℝ) / 4) := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hs0 : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have h := norm_bdFeatureLp_sq_le hk
  have hsq : ‖bdFeatureLp k‖
      ≤ Real.sqrt ((5 / (2 * squarefreeMobiusTotal 2)) / Real.sqrt (k : ℝ)) := by
    rw [show ‖bdFeatureLp k‖ = Real.sqrt (‖bdFeatureLp k‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt h
  refine le_trans hsq (le_of_eq (sqrt_div_sqrt_eq (by positivity) hk0))

/-- The lower bound on the feature norm. -/
theorem le_norm_bdFeatureLp {k : ℕ} (hk : 7 ≤ k) :
    Real.sqrt (1 / (500 * squarefreeMobiusTotal 2)) * ((k : ℝ)) ^ (-(1 : ℝ) / 4)
      ≤ ‖bdFeatureLp k‖ := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have h := le_norm_bdFeatureLp_sq hk
  have hsq : Real.sqrt ((1 / (500 * squarefreeMobiusTotal 2)) / Real.sqrt (k : ℝ))
      ≤ ‖bdFeatureLp k‖ := by
    rw [show ‖bdFeatureLp k‖ = Real.sqrt (‖bdFeatureLp k‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt h
  refine le_trans (le_of_eq (sqrt_div_sqrt_eq (by positivity) hk0).symm) hsq

/-- **Equation (7l).**  The normalized coherent-source overlap of the spectral feature. -/
def bdAngle (k : ℕ) : ℝ :=
  ‖infiniteSignedChannelProjection (infiniteMobiusSignedWeightLp 2 (by norm_num)) (bdFeatureLp k)‖
    / ‖bdFeatureLp k‖

theorem bdAngle_nonneg (k : ℕ) : 0 ≤ bdAngle k :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

theorem norm_bdCoeff_eq_angle {k : ℕ} (hk : 7 ≤ k) :
    ‖bdCoeff k‖ = squarefreeMobiusTotal 2 * ‖bdFeatureLp k‖ * bdAngle k := by
  have hpos := norm_bdFeatureLp_pos hk
  rw [bdAngle, norm_bdCoeff_eq_channel]
  field_simp

theorem rpow_quarter_mul (ε : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ)) ^ (-(1 : ℝ) / 4) * ((k : ℝ)) ^ (-(1 : ℝ) / 2 + ε)
      = ((k : ℝ)) ^ (-(3 : ℝ) / 4 + ε) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [← Real.rpow_add hk0]
  congr 1
  ring

/-- **Equation (7m), unconditional half.**  The Báez--Duarte coefficient decay datum and the
normalized source-angle decay datum are the same datum. -/
theorem bdAngle_decay_iff (ε : ℝ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 7 ≤ k → ‖bdCoeff k‖ ≤ C * ((k : ℝ)) ^ (-(3 : ℝ) / 4 + ε))
      ↔ (∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 7 ≤ k →
          bdAngle k ≤ C * ((k : ℝ)) ^ (-(1 : ℝ) / 2 + ε)) := by
  have hZ : (0 : ℝ) < squarefreeMobiusTotal 2 := squarefreeMobiusTotal_pos (by norm_num)
  constructor
  · rintro ⟨C, hC0, hC⟩
    have ha0 : (0 : ℝ) < Real.sqrt (1 / (500 * squarefreeMobiusTotal 2)) := by positivity
    refine ⟨C / (squarefreeMobiusTotal 2 * Real.sqrt (1 / (500 * squarefreeMobiusTotal 2))),
      by positivity, ?_⟩
    intro k hk
    have hk1 : 1 ≤ k := by omega
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hpow : (0 : ℝ) < ((k : ℝ)) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hk0 _
    set a := Real.sqrt (1 / (500 * squarefreeMobiusTotal 2)) with ha
    have hP : (0 : ℝ) < squarefreeMobiusTotal 2 * a * ((k : ℝ)) ^ (-(1 : ℝ) / 4) := by positivity
    have hY := le_norm_bdFeatureLp hk
    have heq := norm_bdCoeff_eq_angle hk
    have hkey : squarefreeMobiusTotal 2 * a * ((k : ℝ)) ^ (-(1 : ℝ) / 4) * bdAngle k
        ≤ C * ((k : ℝ)) ^ (-(3 : ℝ) / 4 + ε) := by
      have hstep : squarefreeMobiusTotal 2 * (a * ((k : ℝ)) ^ (-(1 : ℝ) / 4)) * bdAngle k
          ≤ squarefreeMobiusTotal 2 * ‖bdFeatureLp k‖ * bdAngle k := by
        refine mul_le_mul_of_nonneg_right ?_ (bdAngle_nonneg k)
        exact mul_le_mul_of_nonneg_left hY hZ.le
      have hstep2 : squarefreeMobiusTotal 2 * ‖bdFeatureLp k‖ * bdAngle k
          ≤ C * ((k : ℝ)) ^ (-(3 : ℝ) / 4 + ε) := by
        rw [← heq]
        exact hC k hk
      calc squarefreeMobiusTotal 2 * a * ((k : ℝ)) ^ (-(1 : ℝ) / 4) * bdAngle k
          = squarefreeMobiusTotal 2 * (a * ((k : ℝ)) ^ (-(1 : ℝ) / 4)) * bdAngle k := by ring
        _ ≤ _ := le_trans hstep hstep2
    have hgoal : bdAngle k
        ≤ (C * ((k : ℝ)) ^ (-(3 : ℝ) / 4 + ε))
          / (squarefreeMobiusTotal 2 * a * ((k : ℝ)) ^ (-(1 : ℝ) / 4)) := by
      rw [le_div_iff₀ hP]
      linarith [hkey]
    refine le_trans hgoal (le_of_eq ?_)
    rw [← rpow_quarter_mul ε hk1]
    field_simp
  · rintro ⟨C, hC0, hC⟩
    have hb0 : (0 : ℝ) ≤ Real.sqrt (5 / (2 * squarefreeMobiusTotal 2)) := Real.sqrt_nonneg _
    refine ⟨squarefreeMobiusTotal 2 * Real.sqrt (5 / (2 * squarefreeMobiusTotal 2)) * C,
      by positivity, ?_⟩
    intro k hk
    have hk1 : 1 ≤ k := by omega
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    set b := Real.sqrt (5 / (2 * squarefreeMobiusTotal 2)) with hb
    have hY := norm_bdFeatureLp_le hk1
    have heq := norm_bdCoeff_eq_angle hk
    have hang := hC k hk
    have hstep : squarefreeMobiusTotal 2 * ‖bdFeatureLp k‖ * bdAngle k
        ≤ squarefreeMobiusTotal 2 * (b * ((k : ℝ)) ^ (-(1 : ℝ) / 4))
          * (C * ((k : ℝ)) ^ (-(1 : ℝ) / 2 + ε)) := by
      refine mul_le_mul ?_ hang (bdAngle_nonneg k) (by positivity)
      exact mul_le_mul_of_nonneg_left hY hZ.le
    have hfin : squarefreeMobiusTotal 2 * (b * ((k : ℝ)) ^ (-(1 : ℝ) / 4))
        * (C * ((k : ℝ)) ^ (-(1 : ℝ) / 2 + ε))
        = squarefreeMobiusTotal 2 * b * C * ((k : ℝ)) ^ (-(3 : ℝ) / 4 + ε) := by
      rw [← rpow_quarter_mul ε hk1]
      ring
    rw [heq]
    calc squarefreeMobiusTotal 2 * ‖bdFeatureLp k‖ * bdAngle k
        ≤ squarefreeMobiusTotal 2 * (b * ((k : ℝ)) ^ (-(1 : ℝ) / 4))
          * (C * ((k : ℝ)) ^ (-(1 : ℝ) / 2 + ε)) := hstep
      _ = squarefreeMobiusTotal 2 * b * C * ((k : ℝ)) ^ (-(3 : ℝ) / 4 + ε) := hfin

end

end RHTower
