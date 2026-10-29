import GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyCriticalGrowth

/-!
# An iterated-log endpoint for the fixed Steklov profile

The existing logarithmic Denjoy–Carleman profile reaches overlap
`L (log L)^2 log(log L)`, where `L = log(log N)`. This is smaller than every
schedule `L (log L)^β`, `β > 2`, and uses the same complete Weil receiver.
The result improves the synthesis requirement; it does not prove positivity
of the actual complete form at this overlap.
-/

noncomputable section

open Filter Topology Asymptotics RHTower

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- The logarithmic endpoint schedule with one further divergent logarithm. -/
def endpointSuperGevreyRatio (N : ℕ) : ℝ :=
  Real.log (Real.log N) * Real.log (Real.log (Real.log N)) ^ 2 *
    Real.log (Real.log (Real.log (Real.log N)))

private theorem endpoint_loglog_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem endpoint_tripleLog_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (Real.log N))) atTop atTop :=
  Real.tendsto_log_atTop.comp endpoint_loglog_atTop

private theorem endpoint_fourthLog_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (Real.log N)))) atTop atTop :=
  Real.tendsto_log_atTop.comp endpoint_tripleLog_atTop

private theorem eventually_one_le_endpointSuperGevreyRatio :
    ∀ᶠ N : ℕ in atTop, 1 ≤ endpointSuperGevreyRatio N := by
  filter_upwards [endpoint_loglog_atTop.eventually_ge_atTop 1,
    endpoint_tripleLog_atTop.eventually_ge_atTop 1,
    endpoint_fourthLog_atTop.eventually_ge_atTop 1] with N hL hu hv
  have hu2 : (1 : ℝ) ≤ Real.log (Real.log (Real.log N)) ^ 2 := by
    nlinarith only [hu, sq_nonneg (Real.log (Real.log (Real.log N)) - 1)]
  have hb : (1 : ℝ) ≤ Real.log (Real.log N) * Real.log (Real.log (Real.log N)) ^ 2 := by
    simpa only [one_mul] using mul_le_mul hL hu2 zero_le_one (zero_le_one.trans hL)
  simpa only [one_mul, endpointSuperGevreyRatio] using
    mul_le_mul hb hv zero_le_one (zero_le_one.trans hb)

private theorem eventually_endpointSuperGevreyRatio_le_cube :
    ∀ᶠ N : ℕ in atTop, endpointSuperGevreyRatio N ≤ superGevreyRatio 3 N := by
  filter_upwards [endpoint_loglog_atTop.eventually_ge_atTop 0,
    endpoint_tripleLog_atTop.eventually_ge_atTop 1] with N hL hu
  have hlog : Real.log (Real.log (Real.log (Real.log N))) ≤
      Real.log (Real.log (Real.log N)) :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hu)).trans (by linarith)
  calc
    _ ≤ Real.log (Real.log N) * Real.log (Real.log (Real.log N)) ^ 2 *
        Real.log (Real.log (Real.log N)) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg hL (sq_nonneg _))
    _ = _ := by rw [superGevreyRatio, Real.rpow_ofNat]; ring

/-- The fixed-profile height still tends to infinity at the smaller overlap. -/
theorem endpointSuperGevreyHeight_atTop :
    Tendsto (fun N : ℕ => (N : ℝ) / endpointSuperGevreyRatio N) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (overlapGrowthSuperGevrey_of_two_lt (show (2 : ℝ) < 3 by norm_num)).1
  filter_upwards [eventually_endpointSuperGevreyRatio_le_cube,
    eventually_one_le_endpointSuperGevreyRatio] with N hle hpos
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (zero_lt_one.trans_le hpos) hle

/-- The exact growth condition of the existing complete synthesis theorem
holds at the iterated-log endpoint. -/
theorem overlapGrowthSuperGevrey_endpoint :
    OverlapGrowthSuperGevrey fun N : ℕ => (N : ℝ) / endpointSuperGevreyRatio N := by
  have hκ := endpointSuperGevreyHeight_atTop
  refine ⟨hκ, ?_⟩
  have hl := Real.tendsto_log_atTop.comp hκ
  have hll := Real.tendsto_log_atTop.comp hl
  have hlll := Real.tendsto_log_atTop.comp hll
  refine tendsto_atTop_mono' atTop ?_ endpoint_fourthLog_atTop
  filter_upwards [eventually_one_le_endpointSuperGevreyRatio,
    endpoint_loglog_atTop.eventually_ge_atTop 1,
    endpoint_tripleLog_atTop.eventually_ge_atTop 1,
    hκ.eventually_ge_atTop 1, hl.eventually_ge_atTop 1,
    hll.eventually_ge_atTop 1, hlll.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with N hc hL hu hκ1 hl1 hll1 hlll1 hN
  set c := endpointSuperGevreyRatio N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hκN : (N : ℝ) / c ≤ N := div_le_self hN0.le hc
  have hlN : Real.log ((N : ℝ) / c) ≤ Real.log N :=
    Real.log_le_log (zero_lt_one.trans_le hκ1) hκN
  have hllN : Real.log (Real.log ((N : ℝ) / c)) ≤ Real.log (Real.log N) :=
    Real.log_le_log (zero_lt_one.trans_le hl1) hlN
  have hlllN : Real.log (Real.log (Real.log ((N : ℝ) / c))) ≤
      Real.log (Real.log (Real.log N)) :=
    Real.log_le_log (zero_lt_one.trans_le hll1) hllN
  have hden : Real.log (Real.log ((N : ℝ) / c)) *
      Real.log (Real.log (Real.log ((N : ℝ) / c))) ^ 2 ≤
      Real.log (Real.log N) * Real.log (Real.log (Real.log N)) ^ 2 :=
    mul_le_mul hllN (pow_le_pow_left₀ (zero_le_one.trans hlll1) hlllN 2)
      (sq_nonneg _) (zero_le_one.trans hL)
  have hdpos : 0 < Real.log (Real.log ((N : ℝ) / c)) *
      Real.log (Real.log (Real.log ((N : ℝ) / c))) ^ 2 :=
    mul_pos (zero_lt_one.trans_le hll1) (sq_pos_of_pos (zero_lt_one.trans_le hlll1))
  rw [div_div_cancel₀ hN0.ne']
  calc
    _ = c / (Real.log (Real.log N) * Real.log (Real.log (Real.log N)) ^ 2) := by
      dsimp only [c, endpointSuperGevreyRatio]
      field_simp [(zero_lt_one.trans_le hL).ne', (zero_lt_one.trans_le hu).ne']
    _ ≤ _ := div_le_div_of_nonneg_left (zero_le_one.trans hc) hdpos hden

/-- The endpoint is strictly smaller than every previously displayed
power-log schedule with exponent greater than two. -/
theorem endpointSuperGevreyRatio_isLittleO {β : ℝ} (hβ : 2 < β) :
    endpointSuperGevreyRatio =o[atTop] superGevreyRatio β := by
  have hb : 0 < β - 2 := sub_pos.mpr hβ
  have ht := ((isLittleO_log_rpow_rpow_atTop (1 : ℝ) hb).tendsto_div_nhds_zero.comp
    endpoint_tripleLog_atTop)
  simp only [Function.comp_def, Real.rpow_one] at ht
  have hratio : Tendsto (fun N : ℕ => endpointSuperGevreyRatio N / superGevreyRatio β N)
      atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [endpoint_loglog_atTop.eventually_gt_atTop 0,
      endpoint_tripleLog_atTop.eventually_gt_atTop 0] with N hL hu
    have hp : Real.log (Real.log (Real.log N)) ^ β =
        Real.log (Real.log (Real.log N)) ^ (β - 2) *
          Real.log (Real.log (Real.log N)) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hu]
      congr 1
      norm_num
    dsimp only [endpointSuperGevreyRatio, superGevreyRatio]
    rw [hp]
    field_simp [hL.ne', hu.ne', (Real.rpow_pos_of_pos hu (β - 2)).ne']
  exact Asymptotics.isLittleO_of_tendsto'
    (by
      filter_upwards [endpoint_loglog_atTop.eventually_gt_atTop 0,
        endpoint_tripleLog_atTop.eventually_gt_atTop 0] with N hL hu
      intro hz
      exact absurd hz (mul_pos hL (Real.rpow_pos_of_pos hu β)).ne') hratio

/-- The same explicitly constructed profile gives an RH equivalence at
the smaller endpoint overlap, with no new regularity assumption. -/
theorem riemannHypothesis_iff_steklovDCProfile_nonneg_endpoint :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x
        (dilate ((N : ℝ) / endpointSuperGevreyRatio N) steklovDCProfile)) :=
  riemannHypothesis_iff_atomicFamilies_nonneg_of_superGevrey
    contDiff_steklovDCProfile steklovDCProfile_vanishesOff integral_steklovDCProfile
    (by norm_num) integral_abs_iteratedDeriv_steklovDCProfile_le
    overlapGrowthSuperGevrey_endpoint

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.endpointSuperGevreyRatio_isLittleO
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.riemannHypothesis_iff_steklovDCProfile_nonneg_endpoint
