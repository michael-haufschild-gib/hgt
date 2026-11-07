import GaloisForLFunctions.CompletedArithmeticForms.BesselGammaSpectralFloor
import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairApertureRemainder
import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairGaussianCoercivityBoundary
import Mathlib.MeasureTheory.Function.Floor

/-!
# Gamma payment of the complete pair remainder

A fixed center interval supplies a first-atom Gamma reserve proportional
to the aperture. A rectangular cutoff growing linearly with frequency
makes the complete infinite remainder cost at most half that reserve.
The retained finite head still contains its signed unequal pairs.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms
open _root_.RHTower

/-- A fixed center interval supplies this aperture-independent Gamma coefficient. -/
def firstAtomApertureGammaReserve : ℝ :=
  4 * Real.pi ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * (Real.pi * Real.exp 1 + 1))

theorem firstAtomApertureGammaReserve_pos : 0 < firstAtomApertureGammaReserve := by
  unfold firstAtomApertureGammaReserve
  positivity

private theorem firstAtom_reserve_on_center_interval {r : ℝ} (hr : r ∈ Icc (1 / 2 : ℝ) 1)
    (b : ℝ) :
    4 * firstAtomApertureGammaReserve / Real.cosh (Real.pi * b / 2) ≤
      thetaPairCenterTailSpectrum 1 1 r b := by
  let q := Real.pi * Real.exp r
  have hr0 : 0 ≤ r := by linarith only [hr.1]
  have hq : 3 ≤ q :=
    Real.pi_gt_three.le.trans (le_mul_of_one_le_right Real.pi_pos.le (Real.one_le_exp hr0))
  have hqu : q ≤ Real.pi * Real.exp 1 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr.2) Real.pi_pos.le
  have hs : 1 ≤ Real.sqrt q := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ q by linarith only [hq])
    simpa only [Real.sqrt_one] using hh
  have hD : 2 ≤ q ^ 2 - 2 * q - 1 := by nlinarith only [hq]
  have hcoef : 4 ≤ 2 * Real.sqrt q * (q ^ 2 - 2 * q - 1) := by
    have hh := mul_le_mul hs hD (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg q)
    nlinarith only [hh]
  have he := Real.exp_le_exp.mpr (show -2 * (Real.pi * Real.exp 1 + 1) ≤ -2 * (q + 1) by
    linarith only [hqu])
  have hf : 4 * Real.exp (-2 * (Real.pi * Real.exp 1 + 1)) ≤ firstAtomGammaReserve q := by
    exact mul_le_mul hcoef he (Real.exp_pos _).le (by linarith only [hcoef])
  have hB := besselFirstAtomTailDensity_gamma_lower hq (b / 2)
  rw [show Real.pi * (b / 2) = Real.pi * b / 2 by ring] at hB
  have hlow := (div_le_div_of_nonneg_right hf (Real.cosh_pos _).le).trans hB
  have hh := mul_le_mul_of_nonneg_left hlow
    (by positivity : 0 ≤ 4 * Real.pi ^ (-(1 / 2 : ℝ)))
  rw [thetaPairCenterTailSpectrum_eq (by decide : 0 < 1) (by decide : 0 < 1) hr0 b]
  simp only [Nat.cast_one, Real.log_one, sub_self, mul_zero, Real.cos_zero, one_mul,
    thetaPairCenterTailAmplitude, mul_one]
  dsimp only [firstAtomApertureGammaReserve, q] at hh ⊢
  convert hh using 1
  ring

/-- The actual aperture-weighted first atom retains a Gamma reserve at every frequency. -/
theorem firstAtom_aperture_gamma_lower {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    a * firstAtomApertureGammaReserve / Real.cosh (Real.pi * b / 2) ≤
      thetaPairApertureSpectrum 1 1 a b := by
  have hC := firstAtomApertureGammaReserve_pos
  let f : ℝ → ℝ := fun r => thetaCuspCenterTailWeight a r * thetaPairCenterTailSpectrum 1 1 r b
  let L : ℝ := 2 * a * firstAtomApertureGammaReserve / Real.cosh (Real.pi * b / 2)
  have hi := integrableOn_weight_mul_thetaPairCenterTailSpectrum
    (by decide : 0 < 1) (by decide : 0 < 1) ha0 ha b
  have hind : Integrable ((Icc (1 / 2 : ℝ) 1).indicator (fun _ : ℝ => L)) :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hpoint (r : ℝ) : (Icc (1 / 2 : ℝ) 1).indicator (fun _ => L) r ≤ (Ioi 0).indicator f r := by
    by_cases hr : r ∈ Icc (1 / 2 : ℝ) 1
    · have hr0 : 0 < r := by linarith only [hr.1]
      rw [Set.indicator_of_mem hr, Set.indicator_of_mem (show r ∈ Ioi 0 from hr0)]
      have har : 0 ≤ a * r := mul_nonneg ha0 hr0.le
      have hweight : a / 2 ≤ thetaCuspCenterTailWeight a r := by
        have hs := Real.sinh_nonneg_iff.mpr har
        have hc := mul_le_mul_of_nonneg_left (Real.one_le_cosh (a * r)) har
        have hm := mul_le_mul_of_nonneg_left hr.1 ha0
        unfold thetaCuspCenterTailWeight
        nlinarith only [hs, hc, hm]
      have hh := mul_le_mul hweight (firstAtom_reserve_on_center_interval hr b)
        (by positivity : 0 ≤ 4 * firstAtomApertureGammaReserve / Real.cosh (Real.pi * b / 2))
        (thetaCuspCenterTailWeight_nonneg ha0 hr0.le)
      dsimp only [L, f]
      convert hh using 1
      ring
    · rw [Set.indicator_of_notMem hr]
      by_cases hr0 : r ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hr0]
        exact mul_nonneg (thetaCuspCenterTailWeight_nonneg ha0 hr0.le)
          (thetaPairCenterTailSpectrum_diagonal_pos (by decide : 0 < 1) hr0.le b).le
      · rw [Set.indicator_of_notMem hr0]
  have hh := integral_mono hind (hi.integrable_indicator measurableSet_Ioi) hpoint
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
    intervalIntegral.integral_const, integral_indicator measurableSet_Ioi] at hh
  change (1 - 1 / 2) * L ≤ thetaPairApertureSpectrum 1 1 a b at hh
  dsimp only [L] at hh
  convert hh using 1
  ring

/-- A uniform aperture coefficient for the existing rectangular remainder. -/
def gammaPairTailCost : ℝ :=
  144 * besselFirstAtomTailCost 0 / (1 - Real.exp (-Real.pi)) ^ 2

theorem gammaPairTailCost_nonneg : 0 ≤ gammaPairTailCost := by
  have hh := besselFirstAtomTailCost_nonneg 0
  unfold gammaPairTailCost
  positivity

/-- The fixed buffer pays half the explicit first-atom reserve. -/
def gammaPairBuffer : ℝ :=
  max 0 (Real.log (2 * (gammaPairTailCost + 1) / firstAtomApertureGammaReserve) / Real.pi)

/-- The number of retained ordinary atoms grows linearly with frequency. -/
def gammaPairCutoff (b : ℝ) : ℕ := ⌈|b| / 2 + gammaPairBuffer⌉₊

/-- The actual finite head at the frequency-dependent rectangular cutoff. -/
def gammaAdaptivePairHead (a b : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (gammaPairCutoff b) ×ˢ Finset.range (gammaPairCutoff b)),
    thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b

private theorem buffer_payment :
    gammaPairTailCost * Real.exp (-Real.pi * gammaPairBuffer) ≤ firstAtomApertureGammaReserve / 2 := by
  have hC := firstAtomApertureGammaReserve_pos
  have hD := gammaPairTailCost_nonneg
  have hD1 : 0 < gammaPairTailCost + 1 := by positivity
  have hR : 0 < 2 * (gammaPairTailCost + 1) / firstAtomApertureGammaReserve := by positivity
  have hlog : Real.log (2 * (gammaPairTailCost + 1) / firstAtomApertureGammaReserve) ≤
      Real.pi * gammaPairBuffer := by
    have hh := le_max_right (0 : ℝ)
      (Real.log (2 * (gammaPairTailCost + 1) / firstAtomApertureGammaReserve) / Real.pi)
    exact (div_le_iff₀ Real.pi_pos).mp hh |>.trans_eq (by ring)
  have he : Real.exp (-Real.pi * gammaPairBuffer) ≤
      firstAtomApertureGammaReserve / (2 * (gammaPairTailCost + 1)) := by
    have hh := Real.exp_le_exp.mpr (neg_le_neg hlog)
    have hr : Real.exp (-Real.log (2 * (gammaPairTailCost + 1) / firstAtomApertureGammaReserve)) =
        firstAtomApertureGammaReserve / (2 * (gammaPairTailCost + 1)) := by
      rw [Real.exp_neg, Real.exp_log hR]
      field_simp
    rw [hr] at hh
    convert hh using 1
    congr 1
    ring
  have hf : gammaPairTailCost *
      (firstAtomApertureGammaReserve / (2 * (gammaPairTailCost + 1))) ≤
        firstAtomApertureGammaReserve / 2 := by
    rw [mul_div_assoc, div_le_div_iff₀ (by positivity : 0 < 2 * (gammaPairTailCost + 1))
      (by norm_num : (0 : ℝ) < 2)]
    nlinarith only [hC]
  exact (mul_le_mul_of_nonneg_left he hD).trans hf

private theorem exp_abs_le_sech (b : ℝ) :
    Real.exp (-(Real.pi * |b| / 2)) ≤ 1 / Real.cosh (Real.pi * b / 2) := by
  have ht : 0 ≤ Real.pi * |b| / 2 := by positivity
  have hc : Real.cosh (Real.pi * b / 2) ≤ Real.exp (Real.pi * |b| / 2) := by
    rw [← Real.cosh_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num only [abs_ofNat]
    rw [Real.cosh_eq]
    have hh := Real.exp_le_exp.mpr (neg_le_self ht)
    linarith only [hh]
  have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (Real.cosh_pos _) hc
  simpa only [one_div, Real.exp_neg] using hh

/-- The whole infinite remainder costs at most half a fixed Gamma reserve, at every frequency. -/
theorem gammaAdaptivePair_remainder_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    |thetaFullApertureTail a b - gammaAdaptivePairHead a b| ≤
      a * firstAtomApertureGammaReserve / (2 * Real.cosh (Real.pi * b / 2)) := by
  have hreserve := firstAtomApertureGammaReserve_pos
  have hδ : 0 < 1 - Real.exp (-Real.pi) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos Real.pi_pos))
  have hden : (1 - Real.exp (-Real.pi)) ^ 2 ≤
      (9 - a ^ 2) ^ 2 * (1 - Real.exp (-Real.pi)) ^ 2 := by
    have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith only [ha0, ha]
    have hh : 1 ≤ (9 - a ^ 2) ^ 2 := by nlinarith only [ha2]
    exact le_mul_of_one_le_left (sq_nonneg _) hh
  have hraw := thetaFullApertureTail_remainder_le ha0 ha b (gammaPairCutoff b)
  have hbd : |thetaFullApertureTail a b - gammaAdaptivePairHead a b| ≤
      a * gammaPairTailCost * Real.exp (-Real.pi * ((gammaPairCutoff b : ℝ) + 1)) := by
    refine hraw.trans ?_
    have hC := besselFirstAtomTailCost_nonneg 0
    have hh := div_le_div_of_nonneg_left
      (by positivity : 0 ≤ 144 * a * besselFirstAtomTailCost 0 *
        Real.exp (-Real.pi * ((gammaPairCutoff b : ℝ) + 1))) (sq_pos_of_pos hδ) hden
    exact hh.trans_eq (by unfold gammaPairTailCost; ring)
  have hM : |b| / 2 + gammaPairBuffer ≤ (gammaPairCutoff b : ℝ) := Nat.le_ceil _
  have he : Real.exp (-Real.pi * ((gammaPairCutoff b : ℝ) + 1)) ≤
      Real.exp (-Real.pi * gammaPairBuffer) * Real.exp (-(Real.pi * |b| / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hM Real.pi_pos.le
    nlinarith only [hh, Real.pi_pos]
  have hD := gammaPairTailCost_nonneg
  calc
    _ ≤ a * gammaPairTailCost * Real.exp (-Real.pi * ((gammaPairCutoff b : ℝ) + 1)) := hbd
    _ ≤ a * gammaPairTailCost *
        (Real.exp (-Real.pi * gammaPairBuffer) * Real.exp (-(Real.pi * |b| / 2))) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg ha0 hD)
    _ = a * (gammaPairTailCost * Real.exp (-Real.pi * gammaPairBuffer)) *
        Real.exp (-(Real.pi * |b| / 2)) := by ring
    _ ≤ a * (firstAtomApertureGammaReserve / 2) * (1 / Real.cosh (Real.pi * b / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left buffer_payment ha0) (exp_abs_le_sech b)
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Half the first-atom reserve survives payment of every omitted ordinary pair. -/
theorem firstAtom_pays_gammaAdaptivePair_remainder {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (b : ℝ) :
    a * firstAtomApertureGammaReserve / (2 * Real.cosh (Real.pi * b / 2)) ≤
      thetaPairApertureSpectrum 1 1 a b -
        |thetaFullApertureTail a b - gammaAdaptivePairHead a b| := by
  have hfirst := firstAtom_aperture_gamma_lower ha0 ha b
  have htail := gammaAdaptivePair_remainder_le ha0 ha b
  have he : a * firstAtomApertureGammaReserve / Real.cosh (Real.pi * b / 2) =
      2 * (a * firstAtomApertureGammaReserve / (2 * Real.cosh (Real.pi * b / 2))) := by ring
  rw [he] at hfirst
  linarith only [hfirst, htail]

private theorem measurable_gammaAdaptivePairHead {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Measurable (gammaAdaptivePairHead a) := by
  let F : ℕ → ℝ → ℝ := fun M b =>
    ∑ p ∈ (Finset.range M ×ˢ Finset.range M),
      thetaPairApertureSpectrum (p.1 + 1) (p.2 + 1) a b
  have hF (M : ℕ) : Measurable (F M) := by
    exact Finset.measurable_sum _ fun p _ =>
      (thetaPairApertureSpectrum_continuous_and_decay
        (Nat.succ_pos p.1) (Nat.succ_pos p.2) ha0 ha).1.measurable
  have hM : Measurable gammaPairCutoff :=
    (((measurable_id.abs).div_const (2 : ℝ)).add_const gammaPairBuffer).nat_ceil
  exact (measurable_from_prod_countable_right (f := fun p : ℕ × ℝ => F p.1 p.2) hF).comp
    (hM.prodMk measurable_id)

private theorem continuous_thetaFullApertureTail {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    Continuous (thetaFullApertureTail a) := by
  have ha1 : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  have he : thetaFullApertureTail a = fun b => thetaCuspCenterMixedFourierCurrent a ha1 b / 2 := by
    funext b
    have hh := thetaCuspCenterMixedFourierCurrent_eq_two_mul_apertureTail ha0 ha b
    linarith only [hh]
  rw [he]
  exact (continuous_thetaCuspCenterMixedFourierCurrent a ha1).div_const 2

/-- The complete omitted pair sum is integrable in every polynomial degree. -/
theorem integrable_polynomial_gammaAdaptivePair_remainder {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (P : Polynomial ℝ) :
    Integrable (fun b : ℝ => P.eval b ^ 2 *
      |thetaFullApertureTail a b - gammaAdaptivePairHead a b|) := by
  have hC := firstAtomApertureGammaReserve_pos
  have hm : Measurable fun b : ℝ => P.eval b ^ 2 *
      |thetaFullApertureTail a b - gammaAdaptivePairHead a b| :=
    (by fun_prop : Measurable fun b : ℝ => P.eval b ^ 2).mul
      (((continuous_thetaFullApertureTail ha0 ha).measurable.sub
        (measurable_gammaAdaptivePairHead ha0 ha)).abs)
  apply ((integrable_polynomial_sq_sech P).const_mul
    (a * firstAtomApertureGammaReserve / 2)).mono' hm.aestronglyMeasurable
  filter_upwards with b
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))]
  have hh := mul_le_mul_of_nonneg_left (gammaAdaptivePair_remainder_le ha0 ha b)
    (sq_nonneg (P.eval b))
  exact hh.trans_eq (by ring)

/-- One Gamma reserve pays the whole infinite remainder in every polynomial degree. -/
theorem polynomial_gammaAdaptivePair_remainder_payment {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (P : Polynomial ℝ) :
    (∫ b : ℝ, P.eval b ^ 2 * |thetaFullApertureTail a b - gammaAdaptivePairHead a b|) ≤
      (a * firstAtomApertureGammaReserve / 2) *
        (∫ b : ℝ, P.eval b ^ 2 / Real.cosh (Real.pi * b / 2)) := by
  rw [← integral_const_mul]
  apply integral_mono (integrable_polynomial_gammaAdaptivePair_remainder ha0 ha P)
    ((integrable_polynomial_sq_sech P).const_mul _)
  intro b
  have hh := mul_le_mul_of_nonneg_left (gammaAdaptivePair_remainder_le ha0 ha b)
    (sq_nonneg (P.eval b))
  exact hh.trans_eq (by ring)

#print axioms firstAtom_aperture_gamma_lower
#print axioms gammaAdaptivePair_remainder_le
#print axioms firstAtom_pays_gammaAdaptivePair_remainder
#print axioms polynomial_gammaAdaptivePair_remainder_payment

end GaloisForLFunctions.CompletedArithmeticForms
