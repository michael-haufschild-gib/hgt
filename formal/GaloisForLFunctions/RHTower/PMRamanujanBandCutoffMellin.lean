import GaloisForLFunctions.RHTower.PMRamanujanBandEulerSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Literal cutoff Mellin transform of the complete Ramanujan band

Every denominator q occurs on the exact scale interval [q/2,q). Absolute
window integrals are summable by the complete arithmetic Euler majorant.
This proves integrability and the cleared cutoff identity, retaining the
q=1 subtraction. No small-damping energy ceiling or RH conclusion is claimed.
-/

open MeasureTheory Set Complex Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

def pmRamanujanBandScaleSymbol (ε : ℝ) (s : ℂ) (X : ℝ) : ℂ :=
  ∑ q ∈ Finset.Ioc ⌊X⌋₊ ⌊2*X⌋₊,
    pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s

theorem pmRamanujanBand_mem_scale_interval {X : ℝ} (hX : 1 ≤ X) (q : ℕ) :
    q ∈ Finset.Ioc ⌊X⌋₊ ⌊2*X⌋₊ ↔ X ∈ Ico ((q : ℝ)/2) (q : ℝ) := by
  rw [Finset.mem_Ioc, Nat.floor_lt (by linarith : 0 ≤ X),
    Nat.le_floor_iff (by linarith : 0 ≤ 2*X), Set.mem_Ico]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem pmRamanujanBandScaleSymbol_eq_tsum {X : ℝ} (hX : 1 ≤ X)
    (ε : ℝ) (s : ℂ) :
    pmRamanujanBandScaleSymbol ε s X = ∑' q : ℕ,
      if 2 ≤ q then (Ico ((q : ℝ)/2) (q : ℝ)).indicator
        (fun _ => pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s) X
      else 0 := by
  classical
  rw [tsum_eq_sum (s := Finset.Ioc ⌊X⌋₊ ⌊2*X⌋₊)]
  · apply Finset.sum_congr rfl
    intro q hq
    have hfloor : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).mpr hX
    have hq2 : 2 ≤ q := by have := (Finset.mem_Ioc.mp hq).1; omega
    rw [if_pos hq2, Set.indicator_of_mem ((pmRamanujanBand_mem_scale_interval hX q).mp hq)]
  · intro q hq
    split_ifs with hq2
    · exact Set.indicator_of_notMem
        (fun h => hq ((pmRamanujanBand_mem_scale_interval hX q).mpr h)) _
    · rfl

theorem integral_pmRamanujanBand_scale_interval {q : ℕ} (hq : 2 ≤ q)
    {r : ℂ} (hr : r ≠ 0) :
    (∫ X in Ico ((q : ℝ)/2) (q : ℝ), (X : ℂ)^(r-1)) =
      (q : ℂ)^r * (1-(2 : ℂ)^(-r))/r := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hle : (q : ℝ)/2 ≤ q := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc ((q : ℝ)/2) (q : ℝ) := by
    rw [Set.uIcc_of_le hle]
    intro h
    have := h.1
    linarith
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    integral_cpow (Or.inr ⟨by intro he; apply hr; linear_combination he, hzero⟩),
    sub_add_cancel]
  have hpow : (((q : ℝ)/2 : ℝ) : ℂ)^r = (q : ℂ)^r*(2 : ℂ)^(-r) := by
    have h := Complex.mul_cpow_ofReal_nonneg hqR.le
      (by norm_num : (0 : ℝ) ≤ 1/2) r
    simp only [Complex.ofReal_natCast, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, mul_one_div] at h
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat, h]
    rw [one_div, Complex.inv_cpow (2 : ℂ) r (by simpa using Real.pi_ne_zero.symm),
      Complex.cpow_neg]
  rw [hpow]
  push_cast
  ring

private theorem pmbc_integrable_power (r : ℂ) {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun X : ℝ => (X : ℂ)^(r-1)) (Ico a b) := by
  have hc : ContinuousOn (fun X : ℝ => (X : ℂ)^(r-1)) (Icc a b) := by
    intro X hX
    exact (Complex.continuousAt_ofReal_cpow_const X (r-1)
      (.inr (ne_of_gt (ha.trans_le hX.1)))).continuousWithinAt
  exact hc.integrableOn_Icc.mono_set Ico_subset_Icc_self

def pmRamanujanBandCutoffNormConstant (r : ℂ) : ℝ :=
  ∫ X in Ico (1/2 : ℝ) 1, ‖(X : ℂ)^(r-1)‖

theorem pmRamanujanBandCutoffNormConstant_nonneg (r : ℂ) :
    0 ≤ pmRamanujanBandCutoffNormConstant r :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem integral_norm_pmRamanujanBand_scale_interval {q : ℕ} (hq : 2 ≤ q) (r : ℂ) :
    (∫ X in Ico ((q : ℝ)/2) (q : ℝ), ‖(X : ℂ)^(r-1)‖) =
      (q : ℝ)^r.re * pmRamanujanBandCutoffNormConstant r := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hle : (q : ℝ)/2 ≤ q := by linarith
  have hbase : (1/2 : ℝ) ≤ 1 := by norm_num
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (f := fun X : ℝ => ‖(X : ℂ)^(r-1)‖) (a := (1/2 : ℝ)) (b := 1) (q : ℝ)
  simp only [smul_eq_mul, mul_one, mul_one_div] at hscale
  have he : (∫ X : ℝ in (1/2 : ℝ)..1, ‖(((q : ℝ)*X : ℝ) : ℂ)^(r-1)‖) =
      (q : ℝ)^(r.re-1) * ∫ X : ℝ in (1/2 : ℝ)..1, ‖(X : ℂ)^(r-1)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro X hX
    have hX' : X ∈ Icc (1/2 : ℝ) 1 := by simpa only [Set.uIcc_of_le hbase] using hX
    have hX0 : 0 ≤ X := by linarith [hX'.1]
    dsimp only
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hqR.le hX0, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hqR]
    simp only [Complex.sub_re, Complex.one_re]
  rw [pmRamanujanBandCutoffNormConstant, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hbase, ← hscale, he]
  have hp : (q : ℝ)*(q : ℝ)^(r.re-1) = (q : ℝ)^r.re := by
    calc
      _ = (q : ℝ)^(1 : ℝ)*(q : ℝ)^(r.re-1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hqR]; congr 1; ring
  rw [← mul_assoc, hp]

def pmRamanujanBandCutoffTerm (ε : ℝ) (z s : ℂ) (q : ℕ) (X : ℝ) : ℂ :=
  if 2 ≤ q then (Ico ((q : ℝ)/2) (q : ℝ)).indicator
    (fun X => (pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s) *
      (X : ℂ)^((ε : ℂ)+s-z-1)) X else 0

theorem integrable_pmRamanujanBandCutoffTerm (ε : ℝ) (z s : ℂ) (q : ℕ) :
    Integrable (pmRamanujanBandCutoffTerm ε z s q) := by
  change Integrable (fun X => pmRamanujanBandCutoffTerm ε z s q X)
  by_cases hq : 2 ≤ q
  · simp only [pmRamanujanBandCutoffTerm, if_pos hq]
    apply (integrable_indicator_iff measurableSet_Ico).mpr
    exact (pmbc_integrable_power ((ε : ℂ)+s-z)
      (by
        have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
        positivity)).const_mul _
  · simp only [pmRamanujanBandCutoffTerm, if_neg hq]
    exact integrable_zero _ _ _

theorem integral_norm_pmRamanujanBandCutoffTerm (ε : ℝ) (z s : ℂ) (q : ℕ) :
    (∫ X, ‖pmRamanujanBandCutoffTerm ε z s q X‖) =
      if 2 ≤ q then pmRamanujanBandCutoffNormConstant ((ε : ℂ)+s-z) *
        ‖pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s *
          (q : ℂ)^((ε : ℂ)+s-z)‖ else 0 := by
  classical
  by_cases hq : 2 ≤ q
  · simp only [pmRamanujanBandCutoffTerm, if_pos hq]
    have hind (X : ℝ) : ‖(Ico ((q : ℝ)/2) (q : ℝ)).indicator
        (fun X => (pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s) *
          (X : ℂ)^((ε : ℂ)+s-z-1)) X‖ =
      (Ico ((q : ℝ)/2) (q : ℝ)).indicator
        (fun X => ‖(pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s) *
          (X : ℂ)^((ε : ℂ)+s-z-1)‖) X := by
      by_cases hX : X ∈ Ico ((q : ℝ)/2) (q : ℝ) <;> simp [hX]
    simp_rw [hind]
    rw [integral_indicator measurableSet_Ico]
    simp_rw [norm_mul]
    rw [integral_const_mul, integral_norm_pmRamanujanBand_scale_interval hq,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < q)]
    ring
  · simp [pmRamanujanBandCutoffTerm, hq]

theorem summable_integral_norm_pmRamanujanBandCutoffTerm {ε : ℝ} (hε : 0 < ε)
    {z s : ℂ} (hz : 1 < z.re) (hs : s.re < 1) :
    Summable (fun q => ∫ X, ‖pmRamanujanBandCutoffTerm ε z s q X‖) := by
  have hC := pmRamanujanBandCutoffNormConstant_nonneg ((ε : ℂ)+s-z)
  apply Summable.of_nonneg_of_le (fun q => integral_nonneg (fun X => norm_nonneg _)) _
    ((summable_norm_pmRamanujanBandMellinTerm hε hz hs).mul_left
      (pmRamanujanBandCutoffNormConstant ((ε : ℂ)+s-z)))
  intro q
  rw [integral_norm_pmRamanujanBandCutoffTerm]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg hC (norm_nonneg _)

private theorem pmbc_integrable_tsum {F : ℕ → ℝ → ℂ}
    (hF : ∀ n, Integrable (F n))
    (hS : Summable (fun n => ∫ X, ‖F n X‖)) :
    Integrable (fun X => ∑' n, F n X) := by
  refine ⟨(AEMeasurable.tsum (fun n => (hF n).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun X => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun n => (hF n).aestronglyMeasurable.enorm)]
  have he (n : ℕ) : ∫⁻ X, ‖F n X‖ₑ = ‖∫ X, ‖F n X‖‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun X => norm_nonneg (F n X)))]
    simp only [coe_nnnorm]
  simp_rw [he]
  exact (ENNReal.tsum_coe_ne_top_iff_summable.2
    (NNReal.summable_coe.1 hS.abs)).lt_top

theorem integral_pmRamanujanBandCutoffTerm (ε : ℝ) (z s : ℂ)
    (hr : (ε : ℂ)+s-z ≠ 0) (q : ℕ) :
    (∫ X, pmRamanujanBandCutoffTerm ε z s q X) =
      ((1-(2 : ℂ)^(-((ε : ℂ)+s-z)))/((ε : ℂ)+s-z)) *
        (if 2 ≤ q then pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s *
          (q : ℂ)^((ε : ℂ)+s-z) else 0) := by
  by_cases hq : 2 ≤ q
  · simp only [pmRamanujanBandCutoffTerm, if_pos hq]
    rw [integral_indicator measurableSet_Ico, integral_const_mul,
      integral_pmRamanujanBand_scale_interval hq hr]
    ring
  · simp [pmRamanujanBandCutoffTerm, hq]

theorem tsum_pmRamanujanBandCutoffTerm (ε : ℝ) (z s : ℂ) (X : ℝ) :
    (∑' q, pmRamanujanBandCutoffTerm ε z s q X) =
      (Ici (1 : ℝ)).indicator
        (fun X => pmRamanujanBandScaleSymbol ε s X * (X : ℂ)^((ε : ℂ)+s-z-1)) X := by
  by_cases hX : 1 ≤ X
  · rw [Set.indicator_of_mem (show X ∈ Ici (1 : ℝ) from hX), pmRamanujanBandScaleSymbol_eq_tsum hX,
      ← tsum_mul_right]
    apply tsum_congr
    intro q
    by_cases hq : 2 ≤ q
    · by_cases hi : X ∈ Ico ((q : ℝ)/2) (q : ℝ) <;>
        simp [pmRamanujanBandCutoffTerm, hq, hi]
    · simp [pmRamanujanBandCutoffTerm, hq]
  · rw [Set.indicator_of_notMem (show X ∉ Ici (1 : ℝ) from hX)]
    have hz : ∀ q, pmRamanujanBandCutoffTerm ε z s q X = 0 := by
      intro q
      by_cases hq : 2 ≤ q
      · have hi : X ∉ Ico ((q : ℝ)/2) (q : ℝ) := by
          intro hi
          have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
          linarith [hi.1]
        simp [pmRamanujanBandCutoffTerm, hq, hi]
      · simp [pmRamanujanBandCutoffTerm, hq]
    simp only [hz, tsum_zero]

theorem integrableOn_pmRamanujanBandScaleSymbol_cpow {ε : ℝ} (hε : 0 < ε)
    {z s : ℂ} (hz : 1 < z.re) (hs : s.re < 1) :
    IntegrableOn (fun X : ℝ => pmRamanujanBandScaleSymbol ε s X *
      (X : ℂ)^((ε : ℂ)+s-z-1)) (Ici 1) := by
  apply (integrable_indicator_iff measurableSet_Ici).mp
  have h := pmbc_integrable_tsum (integrable_pmRamanujanBandCutoffTerm ε z s)
    (summable_integral_norm_pmRamanujanBandCutoffTerm hε hz hs)
  simpa only [tsum_pmRamanujanBandCutoffTerm] using h

private theorem pmbc_tsum_from_two {ε : ℝ} (hε : 0 < ε)
    {z s : ℂ} (hz : 1 < z.re) (hs : s.re < 1) :
    (∑' q : ℕ, if 2 ≤ q then pmPowerDampedRamanujanWeight ε q *
      pmRamanujanMellinSymbol q s * (q : ℂ)^((ε : ℂ)+s-z) else 0) =
    (∑' q : ℕ, pmPowerDampedRamanujanWeight ε q *
      pmRamanujanMellinSymbol q s * (q : ℂ)^((ε : ℂ)+s-z)) -
      pmPowerDampedDivisorDensity ε := by
  let g := fun q : ℕ => pmPowerDampedRamanujanWeight ε q *
    pmRamanujanMellinSymbol q s * (q : ℂ)^((ε : ℂ)+s-z)
  have h0 : g 0 = 0 := by simp [g, pmPowerDampedRamanujanWeight_zero]
  have h1 : g 1 = pmPowerDampedDivisorDensity ε := by
    simp [g, pmPowerDampedRamanujanWeight_one hε, pmRamanujanMellinSymbol]
  have hg : Summable g := (summable_norm_pmRamanujanBandMellinTerm hε hz hs).of_norm
  have he := hg.tsum_eq_add_tsum_ite 1
  have hi : (fun q => if q = 1 then 0 else g q) =
      (fun q => if 2 ≤ q then g q else 0) := by
    funext q
    by_cases hq0 : q = 0
    · subst q; simp [h0]
    by_cases hq1 : q = 1
    · subst q; simp
    · simp [hq1, show 2 ≤ q by omega]
  rw [hi, h1] at he
  change (∑' q, if 2 ≤ q then g q else 0) = (∑' q, g q) - _
  linear_combination -he

/-- Integrating the literal moving cutoff retains its exact q=1 subtraction. -/
theorem integral_pmRamanujanBandScaleSymbol_cpow {ε : ℝ} (hε : 0 < ε)
    {z s : ℂ} (hz : 1 < z.re) (hs : s.re < 1) (hr : (ε : ℂ)+s-z ≠ 0) :
    (∫ X in Ici (1 : ℝ), pmRamanujanBandScaleSymbol ε s X *
      (X : ℂ)^((ε : ℂ)+s-z-1)) =
    ((1-(2 : ℂ)^(-((ε : ℂ)+s-z)))/((ε : ℂ)+s-z)) *
      ((∑' q : ℕ, pmPowerDampedRamanujanWeight ε q *
        pmRamanujanMellinSymbol q s * (q : ℂ)^((ε : ℂ)+s-z)) -
        pmPowerDampedDivisorDensity ε) := by
  have hi := integral_tsum_of_summable_integral_norm
    (integrable_pmRamanujanBandCutoffTerm ε z s)
    (summable_integral_norm_pmRamanujanBandCutoffTerm hε hz hs)
  simp_rw [tsum_pmRamanujanBandCutoffTerm, integral_pmRamanujanBandCutoffTerm ε z s hr] at hi
  rw [integral_indicator measurableSet_Ici, tsum_mul_left, pmbc_tsum_from_two hε hz hs] at hi
  exact hi.symm

/-- The complete arithmetic Euler identity integrated over the actual cutoff scale. -/
theorem pmRamanujanBandCutoffMellin_cleared_eq {ε : ℝ} (hε : 0 < ε)
    {z s : ℂ} (hz : 1 < z.re) (hs : s.re < 9/16) (hr : (ε : ℂ)+s-z ≠ 0) :
    riemannZeta z * (∫ X in Ici (1 : ℝ), pmRamanujanBandScaleSymbol ε s X *
      (X : ℂ)^((ε : ℂ)+s-z-1)) =
    pmPowerDampedDivisorDensity ε *
      ((1-(2 : ℂ)^(-((ε : ℂ)+s-z)))/((ε : ℂ)+s-z)) *
      (riemannZeta (1+z-s) * pmRamanujanBandEulerCorrection ε z s - riemannZeta z) := by
  rw [integral_pmRamanujanBandScaleSymbol_cpow hε hz (by linarith) hr]
  have he := pmRamanujanBandMellinSeries_cleared_eq hε hz hs
  linear_combination ((1-(2 : ℂ)^(-((ε : ℂ)+s-z)))/((ε : ℂ)+s-z)) * he

end RHTower
