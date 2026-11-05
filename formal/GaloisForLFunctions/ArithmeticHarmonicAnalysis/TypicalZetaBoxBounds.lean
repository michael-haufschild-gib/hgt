import GaloisForLFunctions.RHTower.ZetaTypicalHeightLogDeriv

/-!
# Polylogarithmic bounds near typical heights

Taking discs of radius `1 / (1 + log (4T))` in the vertical mean-square
estimate bounds the exceptional measure for the level `(1 + log (4T))⁴`
by `CT / (1 + log (4T))³`. Zero shadows and Borel–Carathéodory then control
the logarithmic derivative on fixed discs right of the critical line.
-/

open Complex Set MeasureTheory Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

noncomputable section

/-- The exponent whose power of `T` is the fourth power of `1 + log (4T)`. -/
def zetaPolylogLevel (T : ℝ) : ℝ :=
  4 * Real.log (1 + Real.log (4 * T)) / Real.log T

theorem zetaPolylogLevel_mul_log {T : ℝ} (hT : 1 < T) :
    zetaPolylogLevel T * Real.log T = 4 * Real.log (1 + Real.log (4 * T)) :=
  div_mul_cancel₀ _ (Real.log_pos hT).ne'

theorem zetaPolylogLevel_nonneg {T : ℝ} (hT : 1 < T) :
    0 ≤ zetaPolylogLevel T := by
  have hL : 1 ≤ 1 + Real.log (4 * T) := by
    linarith only [Real.log_nonneg (show 1 ≤ 4 * T by linarith)]
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hL))
    (Real.log_pos hT).le

theorem rpow_zetaPolylogLevel {T : ℝ} (hT : 1 < T) :
    T ^ zetaPolylogLevel T = (1 + Real.log (4 * T)) ^ (4 : ℕ) := by
  have hL : 0 < 1 + Real.log (4 * T) := by
    linarith only [Real.log_nonneg (show 1 ≤ 4 * T by linarith)]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hT), mul_comm,
    zetaPolylogLevel_mul_log hT, ← Real.log_pow _ 4]
  exact Real.exp_log (pow_pos hL 4)

/-- A shrinking mean-value disc gives a polylogarithmic local supremum. -/
theorem exists_volume_zetaLargeNear_polylog_le :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 6 ≤ T → 3 ≤ Real.log (4 * T) →
      volume (zetaLargeNear T ((1 + Real.log (4 * T)) ^ (4 : ℕ))) ≤
        ENNReal.ofReal (A * T / (1 + Real.log (4 * T)) ^ (3 : ℕ)) := by
  obtain ⟨C, hC, hmean⟩ := exists_integral_normSq_zeta_vertical_le
  obtain ⟨K, hK, hχ⟩ :=
    exists_norm_zetaChi_moving_left_line_le_rpow (d₀ := 1 / 4) (by norm_num) (by norm_num)
  let A := 8400 * C * (K ^ 2 * (Real.exp 1) ^ 2 + 1) / Real.pi
  refine ⟨A, by dsimp only [A]; positivity, ?_⟩
  intro T hT hlog
  let L := 1 + Real.log (4 * T)
  have hL4 : 4 ≤ L := by dsimp only [L]; linarith only [hlog]
  have hL : 0 < L := by linarith only [hL4]
  have hT0 : 0 < T := by linarith only [hT]
  have hr : 1 / L ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hL4
  have hpower : (4 * T) ^ (1 / L) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    rw [mul_one_div, div_le_iff₀ hL]
    dsimp only [L]
    linarith
  have hKpower : (K * (4 * T) ^ (1 / L)) ^ 2 + 1 ≤ K ^ 2 * (Real.exp 1) ^ 2 + 1 := by
    have h := pow_le_pow_left₀ (mul_nonneg hK (Real.rpow_nonneg (by positivity) _))
      (mul_le_mul_of_nonneg_left hpower hK) 2
    rw [mul_pow] at h
    linarith only [h]
  have hheight : (4 * T + 2) ^ 2 ≤ 25 * T ^ 2 := by
    nlinarith only [hT]
  have hvol := volume_zetaLargeNear_le hC hK (one_div_pos.mpr hL) hr hmean
    (fun d hd0 hd t => hχ d hd0 hd t) hT (pow_pos hL 4)
  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  change 21 * ((4 * T + 2) ^ 2 * ((K * (4 * T) ^ (1 / L)) ^ 2 + 1) *
    (4 * C * T * L ^ 3)) / (Real.pi * (1 / L) ^ 2 * (T / 2) ^ 2 * (L ^ 4) ^ 2) ≤
      A * T / L ^ 3
  calc
    _ ≤ 21 * (25 * T ^ 2 * (K ^ 2 * (Real.exp 1) ^ 2 + 1) *
        (4 * C * T * L ^ 3)) /
          (Real.pi * (1 / L) ^ 2 * (T / 2) ^ 2 * (L ^ 4) ^ 2) := by
      gcongr
    _ = A * T / L ^ 3 := by
      dsimp only [A]
      field_simp
      ring

/-- The polylogarithmic supremum fails on a set of asymptotic density zero. -/
theorem eventually_volume_zetaLargeNear_polylog_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop,
      volume (zetaLargeNear T ((1 + Real.log (4 * T)) ^ (4 : ℕ))) ≤
        ENNReal.ofReal (δ * T) := by
  obtain ⟨A, hA, hbound⟩ := exists_volume_zetaLargeNear_polylog_le
  have hlog : Tendsto (fun T : ℝ => Real.log (4 * T)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [eventually_ge_atTop (6 : ℝ),
    hlog.eventually_ge_atTop (max 3 (A / δ))] with T hT hlogT
  have hlog3 : 3 ≤ Real.log (4 * T) := (le_max_left _ _).trans hlogT
  have hscale : A / δ ≤ 1 + Real.log (4 * T) := by
    have h := (le_max_right 3 (A / δ)).trans hlogT
    linarith only [h]
  have hL : 1 ≤ 1 + Real.log (4 * T) := by linarith only [hlog3]
  have hcube : 1 + Real.log (4 * T) ≤ (1 + Real.log (4 * T)) ^ (3 : ℕ) := by
    nlinarith only [hL, sq_nonneg (Real.log (4 * T))]
  have hprice : A ≤ δ * (1 + Real.log (4 * T)) ^ (3 : ℕ) := by
    have h := (div_le_iff₀ hδ).mp (hscale.trans hcube)
    linarith only [h]
  refine (hbound T hT hlog3).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_iff₀ (by positivity)]
  have h := mul_le_mul_of_nonneg_right hprice (show 0 ≤ T by linarith only [hT])
  nlinarith only [h]

/-- Typical zero-free discs admit the polylogarithmic level outside a density-zero set. -/
theorem eventually_volume_not_zetaPolylogTypical_le {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop,
      volume {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η (zetaPolylogLevel T) T t} ≤
        ENNReal.ofReal (δ * T) := by
  filter_upwards [(tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually
      (eventually_volume_zetaZeroShadow_le (σ := 1 / 2 + η / 4) (ℓ := 2) (κ := δ / 4)
        (by linarith only [hη]) (by norm_num) (by positivity)),
    eventually_volume_zetaLargeNear_polylog_le (δ := δ / 2) (by positivity),
    eventually_ge_atTop (6 : ℝ)] with T hshadow hlarge hT
  rw [← rpow_zetaPolylogLevel (show 1 < T by linarith only [hT])] at hlarge
  have hsub : {t | t ∈ Icc T (2 * T) ∧ ¬ zetaTypicalHeight η (zetaPolylogLevel T) T t} ⊆
      (zetaZeroShadow (1 / 2 + η / 4) 2 ∩ Icc 0 (2 * T)) ∪
        zetaLargeNear T (T ^ zetaPolylogLevel T) := by
    rintro t ⟨ht, hnt⟩
    by_cases hs : t ∈ zetaZeroShadow (1 / 2 + η / 4) 2
    · exact Or.inl ⟨hs, by linarith only [ht.1, hT], ht.2⟩
    · by_cases hl : t ∈ zetaLargeNear T (T ^ zetaPolylogLevel T)
      · exact Or.inr hl
      · exact absurd ⟨ht, hs, hl⟩ hnt
  calc
    _ ≤ volume (zetaZeroShadow (1 / 2 + η / 4) 2 ∩ Icc 0 (2 * T)) +
        volume (zetaLargeNear T (T ^ zetaPolylogLevel T)) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (δ / 4 * (2 * T)) + ENNReal.ofReal (δ / 2 * T) :=
      add_le_add hshadow hlarge
    _ = ENNReal.ofReal (δ * T) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- On each fixed inner disc, the logarithmic derivative grows only as `log log T`. -/
theorem norm_logDeriv_le_of_zetaPolylogTypical {η T t : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t) (hη : 0 < η) (hη1 : η ≤ 1)
    (hT : 8 ≤ T) {s : ℂ} (hs : ‖s - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - η) :
    ‖logDeriv riemannZeta s‖ ≤
      24 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η ^ 2 := by
  have hT1 : 1 < T := by linarith only [hT]
  have hb := h.norm_logDeriv_le hη hη1 hT (zetaPolylogLevel_nonneg hT1) hs
  rwa [zetaPolylogLevel_mul_log hT1] at hb

/-- The upper bound holds throughout the half-strip within height distance two. -/
theorem norm_zeta_le_of_zetaPolylogTypical {η T t : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t) (hT : 1 < T)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hst : |s.im - t| ≤ 2) :
    ‖riemannZeta s‖ ≤ (1 + Real.log (4 * T)) ^ (4 : ℕ) + 2 := by
  have hb := h.norm_le hT.le hs hst
  rwa [rpow_zetaPolylogLevel hT] at hb

/-- The same typical disc has a lower bound by a fixed negative power of `log T`. -/
theorem norm_zeta_ge_of_zetaPolylogTypical {η T t : ℝ}
    (h : zetaTypicalHeight η (zetaPolylogLevel T) T t) (hη : 0 < η) (hη1 : η ≤ 1)
    (hT : 8 ≤ T) {s : ℂ} (hs : ‖s - (2 + (t : ℂ) * I)‖ ≤ 3 / 2 - η / 2) :
    Real.exp (-(12 * (4 * Real.log (1 + Real.log (4 * T)) + 9) / η)) / 3 ≤
      ‖riemannZeta s‖ := by
  have hT1 : 1 < T := by linarith only [hT]
  have hb := h.norm_ge hη hη1 hT (zetaPolylogLevel_nonneg hT1) hs
  rwa [zetaPolylogLevel_mul_log hT1] at hb

#print axioms exists_volume_zetaLargeNear_polylog_le
#print axioms eventually_volume_not_zetaPolylogTypical_le
#print axioms norm_logDeriv_le_of_zetaPolylogTypical
#print axioms norm_zeta_le_of_zetaPolylogTypical
#print axioms norm_zeta_ge_of_zetaPolylogTypical

end

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
