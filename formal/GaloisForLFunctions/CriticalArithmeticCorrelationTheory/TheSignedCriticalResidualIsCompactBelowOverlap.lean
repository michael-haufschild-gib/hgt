import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCompleteCriticalResidueIsSupportedAtThePole
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheLimitingMixedStructure
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries

/-!
# The signed critical residual below overlap

Subtracting the polar finite part leaves a residual whose fixed conductor
entries vanish after energy normalization. Below the overlap scale, the
logarithm-free arithmetic bound has the summable square envelope
`C / (m³ l³)`. This retains the sign before taking a growing-conductor limit.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticHodgeTheoryOfDegenerations ArithmeticDegenerationTheory SpacingScaleHarmonicAnalysis

/-- The conductor-one finite part of the tilted spline. -/
def tiltedPolarFinitePart : ℝ :=
  ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
    (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))

/-- The actual conductor residual after subtraction of its signed polar part. -/
def signedCriticalConductorResidual (c : ℝ) (N m l : ℕ) : ℝ :=
  ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector m N) -
    completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N,
    normalizedRamanujanHorizonVector l N⟫ -
  (if m = 1 ∧ l = 1 then tiltedPolarFinitePart * (c / Real.log N) else 0)

/-- Energy normalization of the squared signed residual. -/
def signedCriticalRelativeSquare (c : ℝ) (N m l : ℕ) : ℝ :=
  signedCriticalConductorResidual c N m l ^ 2 /
    (completedConductorEnergy tiltedUnitSpline c m *
      completedConductorEnergy tiltedUnitSpline c l)

theorem signedCriticalRelativeSquare_nonneg {c : ℝ} (hc : 0 < c)
    (N : ℕ) {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    0 ≤ signedCriticalRelativeSquare c N m l :=
  div_nonneg (sq_nonneg _)
    (mul_nonneg (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline
      tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hc hm)
      (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline
        tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hc hl))

/-- Removing the polar finite part makes every fixed critical residue vanish. -/
theorem tendsto_seventh_mul_signedCriticalConductorResidual {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => c N ^ 7 * signedCriticalConductorResidual (c N) N m l)
      atTop (𝓝 0) := by
  have hres := tendsto_critical_completeWeil_residual contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hc hR hcrit hm hl
  change Tendsto _ atTop (𝓝 (if m = 1 ∧ l = 1 then tiltedPolarFinitePart else 0)) at hres
  have hz := hcrit.mul (hres.sub_const (if m = 1 ∧ l = 1 then tiltedPolarFinitePart else 0))
  simp only [sub_self, mul_zero] at hz
  apply hz.congr'
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hL
  change 0 < Real.log (N : ℝ) at hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  unfold signedCriticalConductorResidual
  split_ifs <;> (field_simp [hL.ne', hc0.ne'] <;> ring)

/-- Each fixed energy-normalized signed square tends to zero at every positive critical ratio. -/
theorem tendsto_signedCriticalRelativeSquare {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => signedCriticalRelativeSquare (c N) N m l) atTop (𝓝 0) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hEm : Tendsto (fun N : ℕ => c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) m)
      atTop (𝓝 (jordanCoefficient m)) := by
    apply ((tendsto_rpow_seven_mul_completedConductorEnergy_jordan m).comp hcinf).congr
    intro N
    dsimp only [Function.comp_def]
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  have hEl : Tendsto (fun N : ℕ => c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) l)
      atTop (𝓝 (jordanCoefficient l)) := by
    apply ((tendsto_rpow_seven_mul_completedConductorEnergy_jordan l).comp hcinf).congr
    intro N
    dsimp only [Function.comp_def]
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  have h := ((tendsto_seventh_mul_signedCriticalConductorResidual hc hR hcrit hm hl).pow 2).div
    (hEm.mul hEl) (mul_ne_zero (jordanCoefficient_pos hm).ne' (jordanCoefficient_pos hl).ne')
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] at h
  apply h.congr
  intro N
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  dsimp only [Pi.div_apply]
  calc
    _ = (c N ^ 7) ^ 2 * signedCriticalConductorResidual (c N) N m l ^ 2 /
        ((c N ^ 7) ^ 2 * (completedConductorEnergy tiltedUnitSpline (c N) m *
          completedConductorEnergy tiltedUnitSpline (c N) l)) := by ring
    _ = _ := mul_div_mul_left _ _ (pow_ne_zero 2 (pow_ne_zero 7 hc0.ne'))

/-- Below overlap, the rescaled conductor energy retains its seventh-power conductor floor. -/
theorem seventh_mul_completedConductorEnergy_ge_below_overlap {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) (hmc : (m : ℝ) ≤ c) :
    tiltedSplineSpectralFloorConstant * (m : ℝ) ^ 7 ≤
      c ^ 7 * completedConductorEnergy tiltedUnitSpline c m := by
  have hκ := tiltedSplineSpectralFloorConstant_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hratio : 1 ≤ (m : ℝ) / m.totient :=
    (one_le_div htot).mpr (by exact_mod_cast Nat.totient_le m)
  have hp : ((m : ℝ) / c) ^ 7 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hm0.le hc.le)
      ((div_le_one hc).mpr hmc) 7
  have hf := tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale hc hm
  rw [min_eq_right hp] at hf
  have hk : tiltedSplineSpectralFloorConstant ≤
      (2 * tiltedSplineTailConstant / ∫ u, tiltedUnitSpline u ^ 2) * ((m : ℝ) / m.totient) :=
    le_mul_of_one_le_right hκ.le hratio
  have hlow := (mul_le_mul_of_nonneg_right hk (by positivity)).trans hf
  have h := mul_le_mul_of_nonneg_left hlow (pow_nonneg hc.le 7)
  exact (le_of_eq (by field_simp [hc.ne'])).trans h

/-- Critical clocks make every conductor pair below overlap simultaneously admissible. -/
theorem eventually_below_overlap_pair_admissible {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop, ∀ m l : ℕ, (m : ℝ) ≤ c N → (l : ℝ) ≤ c N →
      max 2 (max m l) * max 2 (max m l) ≤ N ∧
      18 * (1 + Real.log (max 2 (max m l) : ℕ)) ≤ Real.log N ∧
      4 * (linearNearRowRadius (c N) + 1) ^ 2 ≤ N ∧ c N ^ 4 ≤ N := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have he := criticalCurve_pow_log_div_natCast hc hR hcrit 4 1
  simp only [pow_one] at he
  have he4 := criticalCurve_pow_log_div_natCast hc hR hcrit 4 0
  simp only [pow_zero, mul_one] at he4
  have hc2 := criticalCurve_sq_div_log hc hR hcrit
  filter_upwards [hcinf.eventually_ge_atTop 20,
    eventually_nearGram_admissible hc he 1 1,
    he4.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hc2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    eventually_ge_atTop 1] with N hc20 hrow h4 h2 hL hN
  change 0 < Real.log (N : ℝ) at hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hc4N : c N ^ 4 ≤ N := (div_le_one hN0).mp h4.le
  have hc2L : c N ^ 2 ≤ Real.log N := (div_le_one hL).mp h2.le
  intro m l hm hl
  have hmax : (max 2 (max m l) : ℕ) ≤ c N := by
    push_cast
    exact max_le (by linarith only [hc20]) (max_le hm hl)
  have hmax0 : (0 : ℝ) < (max 2 (max m l) : ℕ) := by
    have : (2 : ℝ) ≤ (max 2 (max m l) : ℕ) := by exact_mod_cast le_max_left 2 (max m l)
    linarith only [this]
  have hsq : ((max 2 (max m l) : ℕ) : ℝ) ^ 2 ≤ N :=
    (pow_le_pow_left₀ hmax0.le hmax 2).trans
      ((pow_le_pow_right₀ (hc N) (by norm_num : 2 ≤ 4)).trans hc4N)
  have hlog : Real.log (max 2 (max m l) : ℕ) ≤ c N :=
    (Real.log_le_log hmax0 hmax).trans
      ((Real.log_le_sub_one_of_pos hc0).trans (by linarith))
  have hpoly : 18 * (1 + c N) ≤ c N ^ 2 := by nlinarith only [hc20]
  refine ⟨?_, (mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog)
    (by norm_num : (0 : ℝ) ≤ 18)).trans (hpoly.trans hc2L), hrow.2.2, hc4N⟩
  exact_mod_cast (show ((max 2 (max m l) : ℕ) : ℝ) * (max 2 (max m l) : ℕ) ≤ N by
    simpa only [pow_two] using hsq)

/-- Every fixed critical ratio lies below every slightly larger logarithmic exponent. -/
theorem eventually_criticalCurve_le_log_rpow {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ}
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {α : ℝ} (hα : 1 / 8 < α) :
    ∀ᶠ N : ℕ in atTop, c N ≤ Real.log N ^ α := by
  have hL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hδ : 0 < 8 * α - 1 := by linarith only [hα]
  filter_upwards [hcrit.eventually (gt_mem_nhds (lt_add_one R)),
    ((tendsto_rpow_atTop hδ).comp hL).eventually_ge_atTop (R + 1),
    hL.eventually_gt_atTop 0] with N hratio hpower hL0
  change R + 1 ≤ Real.log N ^ (8 * α - 1) at hpower
  change 0 < Real.log N at hL0
  have hpow : c N ^ 8 ≤ (Real.log N ^ α) ^ 8 := by
    calc
      _ ≤ (R + 1) * Real.log N := (div_le_iff₀ hL0).mp hratio.le
      _ ≤ Real.log N ^ (8 * α - 1) * Real.log N :=
        mul_le_mul_of_nonneg_right hpower hL0.le
      _ = _ := by
        conv_lhs => rhs; rw [← Real.rpow_one (Real.log N)]
        rw [← Real.rpow_add hL0, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        congr 1
        push_cast
        ring
  exact (pow_le_pow_iff_left₀ (zero_le_one.trans (hc N))
    (Real.rpow_nonneg hL0.le α) (by norm_num : (8 : ℕ) ≠ 0)).mp hpow

/-- The normalized signed square has one summable conductor envelope below overlap. -/
theorem exists_signedCriticalRelativeSquare_envelope {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ m l : ℕ,
      0 < m → 0 < l → (m : ℝ) ≤ c N → (l : ℝ) ≤ c N →
      signedCriticalRelativeSquare (c N) N m l ≤ C / ((m : ℝ) ^ 3 * (l : ℝ) ^ 3) := by
  obtain ⟨K, hK, hbound⟩ := exists_completeWeil_bilinear_conductor_residual_log_free
    contDiff_tiltedUnitSpline tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos
  let B : ℝ := K * (R + 2) + |tiltedPolarFinitePart| * (R + 1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let κ : ℝ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  refine ⟨B ^ 2 / κ ^ 2, by positivity, ?_⟩
  have hsmall := criticalCurve_pow_log_div_natCast hc hR hcrit 18 1
  simp only [pow_one] at hsmall
  filter_upwards [eventually_below_overlap_pair_admissible hc hR hcrit,
    hcrit.eventually (gt_mem_nhds (lt_add_one R)),
    hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hadmiss hratio hsmallN hL
  change 0 < Real.log (N : ℝ) at hL
  intro m l hm hl hmc hlc
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨hmax, hlog, hrad, hc4N⟩ := hadmiss m l hmc hlc
  let r : ℝ := ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector m N) -
    completedConductorEnergy tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N,
    normalizedRamanujanHorizonVector l N⟫
  have hr := hbound hm hl hmax hlog (hc N) hrad hc4N
  change |r| ≤ _ at hr
  have hml : ((m : ℝ) * l) ^ 3 ≤ c N ^ 6 := by
    have hprod : (m : ℝ) * l ≤ c N ^ 2 :=
      (mul_le_mul hmc hlc hl0.le hc0.le).trans_eq (by ring)
    exact (pow_le_pow_left₀ (by positivity) hprod 3).trans_eq (by ring)
  have hraw : |c N ^ 7 * r| ≤ K * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2) * (R + 2) := by
    calc
      _ = c N ^ 7 * |r| := by rw [abs_mul, abs_of_pos (pow_pos hc0 7)]
      _ ≤ c N ^ 7 *
          (K * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2 * (c N / Real.log N) +
            ((m : ℝ) * l) ^ 5 * (c N ^ 5 * Real.log N / N))) :=
        mul_le_mul_of_nonneg_left hr (pow_nonneg hc0.le 7)
      _ = K * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2) *
          (c N ^ 8 / Real.log N + ((m : ℝ) * l) ^ 3 * (c N ^ 12 * Real.log N / N)) := by ring
      _ ≤ K * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2) *
          (c N ^ 8 / Real.log N + c N ^ 18 * Real.log N / N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add le_rfl
        exact (mul_le_mul_of_nonneg_right hml (by positivity)).trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hratio, hsmallN]) (by positivity)
  have hpolar : |c N ^ 7 *
      (if m = 1 ∧ l = 1 then tiltedPolarFinitePart * (c N / Real.log N) else 0)| ≤
      |tiltedPolarFinitePart| * (R + 1) := by
    split_ifs
    · calc
        _ = |tiltedPolarFinitePart| * (c N ^ 8 / Real.log N) := by
          rw [abs_mul, abs_of_pos (pow_pos hc0 7), abs_mul, abs_of_pos (div_pos hc0 hL)]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hratio.le (abs_nonneg _)
    · simp only [mul_zero, abs_zero]
      positivity
  have hmass : 1 ≤ (m : ℝ) ^ 2 * (l : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hm1) (one_le_pow₀ hl1)
  have hscaled : |c N ^ 7 * signedCriticalConductorResidual (c N) N m l| ≤
      B * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2) := by
    unfold signedCriticalConductorResidual
    rw [mul_sub]
    refine (abs_sub _ _).trans ((add_le_add hraw hpolar).trans ?_)
    have hp := le_mul_of_one_le_right
      (mul_nonneg (abs_nonneg tiltedPolarFinitePart) (by positivity : 0 ≤ R + 1)) hmass
    dsimp only [B]
    nlinarith only [hp]
  have hEm := seventh_mul_completedConductorEnergy_ge_below_overlap hc0 hm hmc
  have hEl := seventh_mul_completedConductorEnergy_ge_below_overlap hc0 hl hlc
  change κ * (m : ℝ) ^ 7 ≤ _ at hEm
  change κ * (l : ℝ) ^ 7 ≤ _ at hEl
  have hEm0 : 0 < c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) m :=
    (mul_pos hκ (pow_pos hm0 7)).trans_le hEm
  have hEl0 : 0 < c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) l :=
    (mul_pos hκ (pow_pos hl0 7)).trans_le hEl
  have hden : κ ^ 2 * (m : ℝ) ^ 7 * (l : ℝ) ^ 7 ≤
      (c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) m) *
        (c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) l) := by
    exact (le_of_eq (by ring)).trans (mul_le_mul hEm hEl (by positivity) hEm0.le)
  calc
    _ = |c N ^ 7 * signedCriticalConductorResidual (c N) N m l| ^ 2 /
        ((c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) m) *
          (c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) l)) := by
      rw [sq_abs]
      unfold signedCriticalRelativeSquare
      have heq : (c N ^ 7 * signedCriticalConductorResidual (c N) N m l) ^ 2 /
          ((c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) m) *
            (c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) l)) =
          (c N ^ 7) ^ 2 * signedCriticalConductorResidual (c N) N m l ^ 2 /
            ((c N ^ 7) ^ 2 * (completedConductorEnergy tiltedUnitSpline (c N) m *
              completedConductorEnergy tiltedUnitSpline (c N) l)) := by ring
      rw [heq, mul_div_mul_left _ _ (pow_ne_zero 2 (pow_ne_zero 7 hc0.ne'))]
    _ ≤ (B * ((m : ℝ) ^ 2 * (l : ℝ) ^ 2)) ^ 2 /
        (κ ^ 2 * (m : ℝ) ^ 7 * (l : ℝ) ^ 7) :=
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hscaled 2)
        (mul_nonneg hEm0.le hEl0.le)).trans
          (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden)
    _ = _ := by field_simp [hκ.ne', hm0.ne', hl0.ne']

/-- Extend the positive-conductor array below overlap by zero. -/
def belowOverlapSignedRelativeSquare (c : ℝ) (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  if 0 < p.1 ∧ 0 < p.2 ∧ (p.1 : ℝ) ≤ c ∧ (p.2 : ℝ) ≤ c then
    signedCriticalRelativeSquare c N p.1 p.2 else 0

theorem belowOverlapSignedRelativeSquare_nonneg {c : ℝ} (hc : 0 < c)
    (N : ℕ) (p : ℕ × ℕ) : 0 ≤ belowOverlapSignedRelativeSquare c N p := by
  unfold belowOverlapSignedRelativeSquare
  split_ifs with hp
  · exact signedCriticalRelativeSquare_nonneg hc N hp.1 hp.2.1
  · exact le_rfl

private theorem summable_inverse_cube_pair (C : ℝ) :
    Summable (fun p : ℕ × ℕ => C / ((p.1 : ℝ) ^ 3 * (p.2 : ℝ) ^ 3)) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp := Summable.mul_of_nonneg (f := fun n : ℕ => 1 / (n : ℝ) ^ 3)
    (g := fun n : ℕ => 1 / (n : ℝ) ^ 3) h h (fun _ => by positivity) (fun _ => by positivity)
  exact (hp.mul_left C).congr fun p => by ring

/-- The entire energy-normalized signed array below overlap tends to zero in squared sum. -/
theorem tendsto_tsum_belowOverlapSignedRelativeSquare {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => ∑' p : ℕ × ℕ, belowOverlapSignedRelativeSquare (c N) N p)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_signedCriticalRelativeSquare_envelope hc hR hcrit
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hpoint : ∀ p : ℕ × ℕ,
      Tendsto (fun N : ℕ => belowOverlapSignedRelativeSquare (c N) N p) atTop (𝓝 (0 : ℝ)) := by
    intro p
    by_cases hm : 0 < p.1
    · by_cases hl : 0 < p.2
      · apply (tendsto_signedCriticalRelativeSquare hc hR hcrit hm hl).congr'
        filter_upwards [hcinf.eventually_ge_atTop (p.1 : ℝ),
          hcinf.eventually_ge_atTop (p.2 : ℝ)] with N hmN hlN
        have hp : 0 < p.1 ∧ 0 < p.2 ∧ (p.1 : ℝ) ≤ c N ∧ (p.2 : ℝ) ≤ c N :=
          ⟨hm, hl, hmN, hlN⟩
        simp only [belowOverlapSignedRelativeSquare, if_pos hp]
      · simpa only [belowOverlapSignedRelativeSquare, hl, false_and, and_false, if_false] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [belowOverlapSignedRelativeSquare, hm, false_and, if_false] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hnorm : ∀ᶠ N : ℕ in atTop, ∀ p : ℕ × ℕ,
      ‖belowOverlapSignedRelativeSquare (c N) N p‖ ≤
        C / ((p.1 : ℝ) ^ 3 * (p.2 : ℝ) ^ 3) := by
    filter_upwards [hbound] with N hN
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg
      (belowOverlapSignedRelativeSquare_nonneg (zero_lt_one.trans_le (hc N)) N p)]
    unfold belowOverlapSignedRelativeSquare
    split_ifs with hp
    · exact hN p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    · positivity
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence (summable_inverse_cube_pair C) hpoint hnorm

/-- The zero-extended array is exactly the finite square below the overlap cutoff. -/
theorem tsum_belowOverlapSignedRelativeSquare_eq {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    (∑' p : ℕ × ℕ, belowOverlapSignedRelativeSquare c N p) =
      ∑ m ∈ Icc 1 ⌊c⌋₊, ∑ l ∈ Icc 1 ⌊c⌋₊, signedCriticalRelativeSquare c N m l := by
  have hsupport : ∀ p ∉ Icc 1 ⌊c⌋₊ ×ˢ Icc 1 ⌊c⌋₊,
      belowOverlapSignedRelativeSquare c N p = 0 := by
    intro p hp
    unfold belowOverlapSignedRelativeSquare
    apply if_neg
    intro h
    exact hp (mem_product.mpr ⟨mem_Icc.mpr ⟨h.1, Nat.le_floor h.2.2.1⟩,
      mem_Icc.mpr ⟨h.2.1, Nat.le_floor h.2.2.2⟩⟩)
  rw [tsum_eq_sum hsupport, Finset.sum_product]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro l hl
  have hmle : (m : ℝ) ≤ c :=
    (Nat.cast_le.mpr (mem_Icc.mp hm).2).trans (Nat.floor_le hc)
  have hlle : (l : ℝ) ≤ c :=
    (Nat.cast_le.mpr (mem_Icc.mp hl).2).trans (Nat.floor_le hc)
  exact if_pos ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hl).1, hmle, hlle⟩

/-- The actual moving conductor square has vanishing signed relative error at every critical ratio. -/
theorem tendsto_sum_signedCriticalRelativeSquare_below_overlap {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => ∑ m ∈ Icc 1 ⌊c N⌋₊, ∑ l ∈ Icc 1 ⌊c N⌋₊,
      signedCriticalRelativeSquare (c N) N m l) atTop (𝓝 0) :=
  (tendsto_tsum_belowOverlapSignedRelativeSquare hc hR hcrit).congr fun N =>
    tsum_belowOverlapSignedRelativeSquare_eq (zero_le_one.trans (hc N)) N

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_signedCriticalRelativeSquare
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_below_overlap_pair_admissible
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_signedCriticalRelativeSquare_envelope
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_tsum_belowOverlapSignedRelativeSquare
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_sum_signedCriticalRelativeSquare_below_overlap
