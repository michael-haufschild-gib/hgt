import GaloisForLFunctions.RHTower.SmoothConvexRapidExponentialFockPotential
import GaloisForLFunctions.RHTower.RapidExponentialMomentFock
import GaloisForLFunctions.RHTower.RapidExponentialFockCriticalPrimeSampling
import GaloisForLFunctions.RHTower.RapidExponentialFockPointedThetaCarrier
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier

/-!
# Exact smooth rapid exponential moment-Fock carrier

A flat-head `C∞` convex radial potential with exact exponential tail defines literal radial moments.
Uniform two-sided moment comparison gives a bounded diagonal equivalence with the unsmoothed rapid
carrier while preserving represented entire functions.  This transfers normalized critical-prime
sampling, compactness, non-Hilbert--Schmidt incidence, and the completed theta trace to the exact
smooth pointed Hilbert space.
-/

open Filter Topology Set MeasureTheory
open scoped Real

namespace RHTower

noncomputable section

def smoothConvexRapidExponentialFockMomentIntegrand (a : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  |r| ^ (2 * n + 1) * Real.exp (-2 * smoothConvexRapidExponentialFockPotential a r)

def smoothConvexRapidExponentialFockMoment (a : ℝ) (n : ℕ) : ℝ :=
  2 * Real.pi * ∫ r in Ioi 0, smoothConvexRapidExponentialFockMomentIntegrand a n r

private def rapidFockUnitHead (r : ℝ) : ℝ :=
  if 0 < r ∧ r ≤ 1 then 1 else 0

private theorem integrableOn_rapidFockUnitHead :
    IntegrableOn rapidFockUnitHead (Ioi (0 : ℝ)) := by
  rw [show rapidFockUnitHead = (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) by
    funext r
    simp [rapidFockUnitHead, indicator, mem_Ioc]]
  exact ((integrableOn_const (by simp [Real.volume_Ioc]) :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1))).integrable_indicator
      measurableSet_Ioc |>.integrableOn

private theorem integral_rapidFockUnitHead :
    (∫ r in Ioi (0 : ℝ), rapidFockUnitHead r) = 1 := by
  rw [show rapidFockUnitHead = (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) by
    funext r
    simp [rapidFockUnitHead, indicator, mem_Ioc],
    MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    show Ioc (0 : ℝ) 1 ∩ Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 from
      Set.inter_eq_left.mpr (fun r hr => hr.1)]
  simp

theorem continuous_smoothConvexRapidExponentialFockMomentIntegrand (a : ℝ) (n : ℕ) :
    Continuous (smoothConvexRapidExponentialFockMomentIntegrand a n) := by
  unfold smoothConvexRapidExponentialFockMomentIntegrand
  exact (continuous_abs.pow _).mul
    (Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_top_smoothConvexRapidExponentialFockPotential a).continuous))

theorem smoothConvexRapidExponentialFockMomentIntegrand_eq_tail
    {a : ℝ} (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    smoothConvexRapidExponentialFockMomentIntegrand a n r =
      rapidExponentialFockMomentIntegrand a n r := by
  unfold smoothConvexRapidExponentialFockMomentIntegrand
    rapidExponentialFockMomentIntegrand
  rw [smoothConvexRapidExponentialFockPotential_eq_tail hr]

private theorem smoothConvexRapidExponentialFockMomentIntegrand_le_one
    (a : ℝ) (n : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    smoothConvexRapidExponentialFockMomentIntegrand a n r ≤ 1 := by
  have hpow : |r| ^ (2 * n + 1) ≤ 1 := by
    rw [abs_of_pos hr0]
    exact pow_le_one₀ hr0.le hr1
  have hpot : 0 ≤ smoothConvexRapidExponentialFockPotential a r := by
    unfold smoothConvexRapidExponentialFockPotential
    positivity
  have hexp : Real.exp (-2 * smoothConvexRapidExponentialFockPotential a r) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  unfold smoothConvexRapidExponentialFockMomentIntegrand
  calc
    |r| ^ (2 * n + 1) * Real.exp (-2 * smoothConvexRapidExponentialFockPotential a r) ≤
        1 * 1 := mul_le_mul hpow hexp (by positivity) zero_le_one
    _ = 1 := one_mul 1

private theorem rapidExponentialFockMomentIntegrand_le_one
    (a : ℝ) (n : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    rapidExponentialFockMomentIntegrand a n r ≤ 1 := by
  have hpow : |r| ^ (2 * n + 1) ≤ 1 := by
    rw [abs_of_pos hr0]
    exact pow_le_one₀ hr0.le hr1
  have hpot : 0 ≤ rapidExponentialFockPotential a r := by
    unfold rapidExponentialFockPotential
    positivity
  have hexp : Real.exp (-2 * rapidExponentialFockPotential a r) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  unfold rapidExponentialFockMomentIntegrand
  calc
    |r| ^ (2 * n + 1) * Real.exp (-2 * rapidExponentialFockPotential a r) ≤
        1 * 1 := mul_le_mul hpow hexp (by positivity) zero_le_one
    _ = 1 := one_mul 1

private theorem smoothMomentIntegrand_le_rapid_add_head
    (a : ℝ) (n : ℕ) {r : ℝ} (hr : r ∈ Ioi (0 : ℝ)) :
    smoothConvexRapidExponentialFockMomentIntegrand a n r ≤
      rapidExponentialFockMomentIntegrand a n r + rapidFockUnitHead r := by
  have hr0 : 0 < r := hr
  by_cases hr1 : r ≤ 1
  · have hhead : rapidFockUnitHead r = 1 := by simp [rapidFockUnitHead, hr0, hr1]
    rw [hhead]
    exact (smoothConvexRapidExponentialFockMomentIntegrand_le_one a n hr0 hr1).trans
      (le_add_of_nonneg_left (by
        unfold rapidExponentialFockMomentIntegrand
        positivity))
  · have hrgt : 1 < r := lt_of_not_ge hr1
    have hhead : rapidFockUnitHead r = 0 := by simp [rapidFockUnitHead, hr1]
    rw [hhead, add_zero]
    exact (smoothConvexRapidExponentialFockMomentIntegrand_eq_tail n hrgt.le).le

private theorem rapidMomentIntegrand_le_smooth_add_head
    (a : ℝ) (n : ℕ) {r : ℝ} (hr : r ∈ Ioi (0 : ℝ)) :
    rapidExponentialFockMomentIntegrand a n r ≤
      smoothConvexRapidExponentialFockMomentIntegrand a n r + rapidFockUnitHead r := by
  have hr0 : 0 < r := hr
  by_cases hr1 : r ≤ 1
  · have hhead : rapidFockUnitHead r = 1 := by simp [rapidFockUnitHead, hr0, hr1]
    rw [hhead]
    exact (rapidExponentialFockMomentIntegrand_le_one a n hr0 hr1).trans
      (le_add_of_nonneg_left (by
        unfold smoothConvexRapidExponentialFockMomentIntegrand
        positivity))
  · have hrgt : 1 < r := lt_of_not_ge hr1
    have hhead : rapidFockUnitHead r = 0 := by simp [rapidFockUnitHead, hr1]
    rw [hhead, add_zero]
    exact (smoothConvexRapidExponentialFockMomentIntegrand_eq_tail n hrgt.le).ge

theorem integrableOn_smoothConvexRapidExponentialFockMomentIntegrand
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (smoothConvexRapidExponentialFockMomentIntegrand a n) (Ioi 0) := by
  have hhead : IntegrableOn
      (smoothConvexRapidExponentialFockMomentIntegrand a n) (Ioc 0 1) := by
    exact (continuous_smoothConvexRapidExponentialFockMomentIntegrand a n).integrableOn_Icc
      |>.mono_set (Ioc_subset_Icc_self)
  have htailRapid : IntegrableOn (rapidExponentialFockMomentIntegrand a n) (Ioi 1) :=
    (integrableOn_rapidExponentialFockMomentIntegrand ha n).mono_set (by
      intro r hr
      exact zero_lt_one.trans (by simpa using hr))
  have htail : IntegrableOn
      (smoothConvexRapidExponentialFockMomentIntegrand a n) (Ioi 1) := by
    refine htailRapid.congr_fun ?_ measurableSet_Ioi
    intro r hr
    exact (smoothConvexRapidExponentialFockMomentIntegrand_eq_tail n hr.le).symm
  have hu := hhead.union htail
  have hset : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext r
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact zero_lt_one.trans h
    · intro hr
      by_cases h : r ≤ 1
      · exact Or.inl ⟨hr, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [hset] at hu
  exact hu

theorem smoothConvexRapidExponentialFockMoment_le_rapid_add_two_pi
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    smoothConvexRapidExponentialFockMoment a n ≤
      rapidExponentialFockMoment a n + 2 * Real.pi := by
  have hs := integrableOn_smoothConvexRapidExponentialFockMomentIntegrand ha n
  have hr := integrableOn_rapidExponentialFockMomentIntegrand ha n
  have hh := integrableOn_rapidFockUnitHead
  have hi : (∫ r in Ioi (0 : ℝ), smoothConvexRapidExponentialFockMomentIntegrand a n r) ≤
      ∫ r in Ioi (0 : ℝ),
        (rapidExponentialFockMomentIntegrand a n r + rapidFockUnitHead r) := by
    apply setIntegral_mono_ae_restrict hs (hr.add hh)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr0
    exact smoothMomentIntegrand_le_rapid_add_head a n hr0
  have hadd : (∫ r in Ioi (0 : ℝ),
      (rapidExponentialFockMomentIntegrand a n r + rapidFockUnitHead r)) =
      (∫ r in Ioi (0 : ℝ), rapidExponentialFockMomentIntegrand a n r) + 1 := by
    rw [MeasureTheory.integral_add hr hh, integral_rapidFockUnitHead]
  rw [hadd] at hi
  change
    2 * Real.pi * (∫ r in Ioi 0, smoothConvexRapidExponentialFockMomentIntegrand a n r) ≤
      2 * Real.pi * (∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r) +
        2 * Real.pi
  calc
    2 * Real.pi * ∫ r in Ioi 0, smoothConvexRapidExponentialFockMomentIntegrand a n r ≤
        2 * Real.pi * ((∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r) + 1) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 2 * Real.pi * (∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r) +
        2 * Real.pi := by ring

theorem rapidExponentialFockMoment_le_smoothConvex_add_two_pi
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    rapidExponentialFockMoment a n ≤
      smoothConvexRapidExponentialFockMoment a n + 2 * Real.pi := by
  have hs := integrableOn_smoothConvexRapidExponentialFockMomentIntegrand ha n
  have hr := integrableOn_rapidExponentialFockMomentIntegrand ha n
  have hh := integrableOn_rapidFockUnitHead
  have hi : (∫ r in Ioi (0 : ℝ), rapidExponentialFockMomentIntegrand a n r) ≤
      ∫ r in Ioi (0 : ℝ),
        (smoothConvexRapidExponentialFockMomentIntegrand a n r + rapidFockUnitHead r) := by
    apply setIntegral_mono_ae_restrict hr (hs.add hh)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr0
    exact rapidMomentIntegrand_le_smooth_add_head a n hr0
  have hadd : (∫ r in Ioi (0 : ℝ),
      (smoothConvexRapidExponentialFockMomentIntegrand a n r + rapidFockUnitHead r)) =
      (∫ r in Ioi (0 : ℝ), smoothConvexRapidExponentialFockMomentIntegrand a n r) + 1 := by
    rw [MeasureTheory.integral_add hs hh, integral_rapidFockUnitHead]
  rw [hadd] at hi
  change
    2 * Real.pi * (∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r) ≤
      2 * Real.pi *
          (∫ r in Ioi 0, smoothConvexRapidExponentialFockMomentIntegrand a n r) +
        2 * Real.pi
  calc
    2 * Real.pi * ∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r ≤
        2 * Real.pi *
          ((∫ r in Ioi 0, smoothConvexRapidExponentialFockMomentIntegrand a n r) + 1) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 2 * Real.pi *
          (∫ r in Ioi 0, smoothConvexRapidExponentialFockMomentIntegrand a n r) +
        2 * Real.pi := by ring

theorem smoothConvexRapidExponentialFockMomentIntegrand_pos
    (a : ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < smoothConvexRapidExponentialFockMomentIntegrand a n r := by
  unfold smoothConvexRapidExponentialFockMomentIntegrand
  positivity

theorem smoothConvexRapidExponentialFockMoment_pos
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < smoothConvexRapidExponentialFockMoment a n := by
  have hfi := integrableOn_smoothConvexRapidExponentialFockMomentIntegrand ha n
  have hsupport : 0 < (volume.restrict (Ioi 0))
      (Function.support (smoothConvexRapidExponentialFockMomentIntegrand a n)) := by
    have hsubset : Ioc (1 : ℝ) 2 ⊆
        Function.support (smoothConvexRapidExponentialFockMomentIntegrand a n) := by
      intro r hr
      exact Function.mem_support.mpr
        (smoothConvexRapidExponentialFockMomentIntegrand_pos a n
          (zero_lt_one.trans hr.1)).ne'
    have hinterval : 0 < (volume.restrict (Ioi 0)) (Ioc (1 : ℝ) 2) := by
      rw [Measure.restrict_apply measurableSet_Ioc]
      norm_num [Ioc_inter_Ioi]
    exact hinterval.trans_le (measure_mono hsubset)
  have hwhole : 0 < ∫ r in Ioi 0,
      smoothConvexRapidExponentialFockMomentIntegrand a n r :=
    (integral_pos_iff_support_of_nonneg
      (fun r => by unfold smoothConvexRapidExponentialFockMomentIntegrand; positivity)
      hfi).2 hsupport
  rw [smoothConvexRapidExponentialFockMoment]
  positivity

/-- A unit tail annulus supplies a geometric lower bound uniform in degree. -/
theorem smoothConvexRapidExponentialFockMoment_lower_geometric
    {a R : ℝ} (ha : 0 < a) (hR : 1 ≤ R) (n : ℕ) :
    2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a (R + 1)) *
        R ^ (2 * n) ≤ smoothConvexRapidExponentialFockMoment a n := by
  let c : ℝ := Real.exp (-2 * rapidExponentialFockPotential a (R + 1)) * R ^ (2 * n)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hpoint : ∀ r ∈ Ioc R (R + 1),
      c ≤ smoothConvexRapidExponentialFockMomentIntegrand a n r := by
    intro r hr
    have hr0 : 0 < r := hR0.trans hr.1
    have hrOne : 1 ≤ r := hR.trans hr.1.le
    rw [smoothConvexRapidExponentialFockMomentIntegrand_eq_tail n hrOne]
    have hpot := rapidExponentialFockPotential_monoOn_nonneg ha.le hr.2
    have hexp : Real.exp (-2 * rapidExponentialFockPotential a (R + 1)) ≤
        Real.exp (-2 * rapidExponentialFockPotential a r) := by
      rw [Real.exp_le_exp]
      linarith
    have hpow : R ^ (2 * n) ≤ |r| ^ (2 * n + 1) := by
      rw [abs_of_pos hr0, pow_succ]
      calc
        R ^ (2 * n) ≤ r ^ (2 * n) := pow_le_pow_left₀ hR0.le hr.1.le _
        _ = r ^ (2 * n) * 1 := by ring
        _ ≤ r ^ (2 * n) * r :=
          mul_le_mul_of_nonneg_left (hR.trans hr.1.le) (by positivity)
    calc
      c ≤ Real.exp (-2 * rapidExponentialFockPotential a r) * |r| ^ (2 * n + 1) :=
        mul_le_mul hexp hpow (by positivity) (by positivity)
      _ = rapidExponentialFockMomentIntegrand a n r := by
        rw [rapidExponentialFockMomentIntegrand, mul_comm]
  have hconstInt : ∫ _r in Ioc R (R + 1), c = c := by
    rw [setIntegral_const]
    simp [c]
  have hfint := integrableOn_smoothConvexRapidExponentialFockMomentIntegrand ha n
  have hcint : IntegrableOn (fun _r : ℝ => c) (Ioc R (R + 1)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact continuous_const.intervalIntegrable _ _
  have hinterInt : ∫ r in Ioc R (R + 1), c ≤
      ∫ r in Ioc R (R + 1), smoothConvexRapidExponentialFockMomentIntegrand a n r := by
    apply setIntegral_mono_ae_restrict hcint
      (hfint.mono_set (fun r hr => hR0.trans hr.1))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hpoint r hr
  have hsubset : Ioc R (R + 1) ⊆ Ioi (0 : ℝ) := fun r hr => hR0.trans hr.1
  have htoWhole : ∫ r in Ioc R (R + 1),
      smoothConvexRapidExponentialFockMomentIntegrand a n r ≤
      ∫ r in Ioi 0, smoothConvexRapidExponentialFockMomentIntegrand a n r :=
    integral_mono_measure (Measure.restrict_mono hsubset le_rfl)
      (ae_of_all _ fun r => by
        unfold smoothConvexRapidExponentialFockMomentIntegrand
        positivity) hfint
  rw [smoothConvexRapidExponentialFockMoment]
  calc
    2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a (R + 1)) *
        R ^ (2 * n) = (2 * Real.pi) * c := by dsimp [c]; ring
    _ = (2 * Real.pi) * (∫ r in Ioc R (R + 1), c) := by rw [hconstInt]
    _ ≤ (2 * Real.pi) *
        (∫ r in Ioi 0, smoothConvexRapidExponentialFockMomentIntegrand a n r) :=
      mul_le_mul_of_nonneg_left (hinterInt.trans htoWhole) (by positivity)

/-- Uniform equivalence constant for unsmoothed and smooth rapid radial moments. -/
def smoothConvexRapidMomentComparisonBound (a : ℝ) : ℝ :=
  1 + Real.exp (2 * rapidExponentialFockPotential a 2)

theorem smoothConvexRapidMomentComparisonBound_pos (a : ℝ) :
    0 < smoothConvexRapidMomentComparisonBound a := by
  unfold smoothConvexRapidMomentComparisonBound
  positivity

private theorem two_pi_le_exp_tail_mul_rapidMoment
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    2 * Real.pi ≤ Real.exp (2 * rapidExponentialFockPotential a 2) *
      rapidExponentialFockMoment a n := by
  have hlower := rapidExponentialFockMoment_lower_geometric
    (a := a) (R := 1) ha (by norm_num) n
  have hlower' : 2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a 2) ≤
      rapidExponentialFockMoment a n := by
    convert hlower using 1 <;> norm_num
  have hmul := mul_le_mul_of_nonneg_left hlower'
    (Real.exp_pos (2 * rapidExponentialFockPotential a 2)).le
  calc
    2 * Real.pi = Real.exp (2 * rapidExponentialFockPotential a 2) *
        (2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a 2)) := by
      rw [show Real.exp (2 * rapidExponentialFockPotential a 2) *
          (2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a 2)) =
          2 * Real.pi *
            (Real.exp (2 * rapidExponentialFockPotential a 2) *
              Real.exp (-2 * rapidExponentialFockPotential a 2)) by ring,
        ← Real.exp_add]
      ring_nf
      simp
    _ ≤ Real.exp (2 * rapidExponentialFockPotential a 2) *
        rapidExponentialFockMoment a n := hmul

private theorem two_pi_le_exp_tail_mul_smoothMoment
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    2 * Real.pi ≤ Real.exp (2 * rapidExponentialFockPotential a 2) *
      smoothConvexRapidExponentialFockMoment a n := by
  have hlower := smoothConvexRapidExponentialFockMoment_lower_geometric
    (a := a) (R := 1) ha (by norm_num) n
  have hlower' : 2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a 2) ≤
      smoothConvexRapidExponentialFockMoment a n := by
    convert hlower using 1 <;> norm_num
  have hmul := mul_le_mul_of_nonneg_left hlower'
    (Real.exp_pos (2 * rapidExponentialFockPotential a 2)).le
  calc
    2 * Real.pi = Real.exp (2 * rapidExponentialFockPotential a 2) *
        (2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a 2)) := by
      rw [show Real.exp (2 * rapidExponentialFockPotential a 2) *
          (2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a 2)) =
          2 * Real.pi *
            (Real.exp (2 * rapidExponentialFockPotential a 2) *
              Real.exp (-2 * rapidExponentialFockPotential a 2)) by ring,
        ← Real.exp_add]
      ring_nf
      simp
    _ ≤ Real.exp (2 * rapidExponentialFockPotential a 2) *
        smoothConvexRapidExponentialFockMoment a n := hmul

theorem smoothConvexRapidExponentialFockMoment_le_comparison_mul_rapid
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    smoothConvexRapidExponentialFockMoment a n ≤
      smoothConvexRapidMomentComparisonBound a * rapidExponentialFockMoment a n := by
  calc
    smoothConvexRapidExponentialFockMoment a n ≤
        rapidExponentialFockMoment a n + 2 * Real.pi :=
      smoothConvexRapidExponentialFockMoment_le_rapid_add_two_pi ha n
    _ ≤ rapidExponentialFockMoment a n +
        Real.exp (2 * rapidExponentialFockPotential a 2) *
          rapidExponentialFockMoment a n :=
      add_le_add (le_refl _) (two_pi_le_exp_tail_mul_rapidMoment ha n)
    _ = smoothConvexRapidMomentComparisonBound a *
        rapidExponentialFockMoment a n := by
      unfold smoothConvexRapidMomentComparisonBound
      ring

theorem rapidExponentialFockMoment_le_comparison_mul_smooth
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    rapidExponentialFockMoment a n ≤
      smoothConvexRapidMomentComparisonBound a *
        smoothConvexRapidExponentialFockMoment a n := by
  calc
    rapidExponentialFockMoment a n ≤
        smoothConvexRapidExponentialFockMoment a n + 2 * Real.pi :=
      rapidExponentialFockMoment_le_smoothConvex_add_two_pi ha n
    _ ≤ smoothConvexRapidExponentialFockMoment a n +
        Real.exp (2 * rapidExponentialFockPotential a 2) *
          smoothConvexRapidExponentialFockMoment a n :=
      add_le_add (le_refl _) (two_pi_le_exp_tail_mul_smoothMoment ha n)
    _ = smoothConvexRapidMomentComparisonBound a *
        smoothConvexRapidExponentialFockMoment a n := by
      unfold smoothConvexRapidMomentComparisonBound
      ring

theorem norm_momentFockKernelCoeff_smoothConvexRapidExponential_sq
    {a : ℝ} (ha : 0 < a) (z : ℂ) (n : ℕ) :
    ‖momentFockKernelCoeff (smoothConvexRapidExponentialFockMoment a) z n‖ ^ (2 : ℝ) =
      ‖z‖ ^ (2 * n) / smoothConvexRapidExponentialFockMoment a n := by
  have hmoment := smoothConvexRapidExponentialFockMoment_pos ha n
  have hsqrt : Real.sqrt (smoothConvexRapidExponentialFockMoment a n) ≠ 0 :=
    (Real.sqrt_pos.2 hmoment).ne'
  rw [Real.rpow_two]
  simp only [momentFockKernelCoeff, norm_div, norm_pow, Complex.norm_conj,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [div_pow, ← pow_mul]
  field_simp [hsqrt]
  rw [Real.sq_sqrt hmoment.le]
  ring

/-- Exact smooth rapid radial moments instantiate the coefficient RKHS. -/
def smoothConvexRapidExponentialMomentFockData (a : ℝ) (ha : 0 < a) : MomentFockData where
  weight := smoothConvexRapidExponentialFockMoment a
  weight_pos := smoothConvexRapidExponentialFockMoment_pos ha
  kernel_summable := by
    intro z
    let R : ℝ := ‖z‖ + 1
    let A : ℝ := 2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a (R + 1))
    let q : ℝ := (‖z‖ / R) ^ 2
    have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
    have hR0 : 0 < R := zero_lt_one.trans_le hR
    have hA : 0 < A := by dsimp [A]; positivity
    have hratio : ‖z‖ / R < 1 := (div_lt_one hR0).2 (by dsimp [R]; linarith)
    have hq : ‖q‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [q]; positivity)]
      dsimp [q]
      nlinarith [div_nonneg (norm_nonneg z) hR0.le]
    have hgeom : Summable fun n : ℕ => A⁻¹ * q ^ n :=
      (summable_geometric_of_norm_lt_one hq).mul_left A⁻¹
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => A⁻¹ * q ^ n)
      (g := fun n : ℕ =>
        ‖momentFockKernelCoeff (smoothConvexRapidExponentialFockMoment a) z n‖ ^ (2 : ℝ))
      (fun n => by positivity) ?_ hgeom
    intro n
    rw [norm_momentFockKernelCoeff_smoothConvexRapidExponential_sq ha]
    have hlower : A * R ^ (2 * n) ≤ smoothConvexRapidExponentialFockMoment a n := by
      simpa [A] using smoothConvexRapidExponentialFockMoment_lower_geometric ha hR n
    have hden : 0 < A * R ^ (2 * n) := mul_pos hA (pow_pos hR0 _)
    calc
      ‖z‖ ^ (2 * n) / smoothConvexRapidExponentialFockMoment a n ≤
          ‖z‖ ^ (2 * n) / (A * R ^ (2 * n)) :=
        div_le_div_of_nonneg_left (by positivity) hden hlower
      _ = A⁻¹ * q ^ n := by
        dsimp [q]
        rw [← pow_mul, div_pow]
        field_simp [hA.ne', hR0.ne']

def smoothToRapidMomentMultiplier (a : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (rapidExponentialFockMoment a n /
    smoothConvexRapidExponentialFockMoment a n) : ℝ)

def rapidToSmoothMomentMultiplier (a : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (smoothConvexRapidExponentialFockMoment a n /
    rapidExponentialFockMoment a n) : ℝ)

theorem norm_smoothToRapidMomentMultiplier_le
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ‖smoothToRapidMomentMultiplier a n‖ ≤
      Real.sqrt (smoothConvexRapidMomentComparisonBound a) := by
  have hs := smoothConvexRapidExponentialFockMoment_pos ha n
  have hdiv : rapidExponentialFockMoment a n /
      smoothConvexRapidExponentialFockMoment a n ≤
        smoothConvexRapidMomentComparisonBound a := by
    rw [div_le_iff₀ hs]
    exact rapidExponentialFockMoment_le_comparison_mul_smooth ha n
  unfold smoothToRapidMomentMultiplier
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hdiv

theorem norm_rapidToSmoothMomentMultiplier_le
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ‖rapidToSmoothMomentMultiplier a n‖ ≤
      Real.sqrt (smoothConvexRapidMomentComparisonBound a) := by
  have hr := rapidExponentialFockMoment_pos ha n
  have hdiv : smoothConvexRapidExponentialFockMoment a n /
      rapidExponentialFockMoment a n ≤ smoothConvexRapidMomentComparisonBound a := by
    rw [div_le_iff₀ hr]
    exact smoothConvexRapidExponentialFockMoment_le_comparison_mul_rapid ha n
  unfold rapidToSmoothMomentMultiplier
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hdiv

theorem rapidToSmoothMomentMultiplier_mul_smoothToRapidMomentMultiplier
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    rapidToSmoothMomentMultiplier a n * smoothToRapidMomentMultiplier a n = 1 := by
  have hu := rapidExponentialFockMoment_pos ha n
  have hs := smoothConvexRapidExponentialFockMoment_pos ha n
  unfold rapidToSmoothMomentMultiplier smoothToRapidMomentMultiplier
  norm_cast
  rw [Real.sqrt_div hs.le, Real.sqrt_div hu.le]
  field_simp [(Real.sqrt_pos.2 hu).ne', (Real.sqrt_pos.2 hs).ne']

theorem smoothToRapidMomentMultiplier_mul_rapidToSmoothMomentMultiplier
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    smoothToRapidMomentMultiplier a n * rapidToSmoothMomentMultiplier a n = 1 := by
  rw [mul_comm, rapidToSmoothMomentMultiplier_mul_smoothToRapidMomentMultiplier ha n]

/-- Coefficient transport representing the same entire function in the unsmoothed moment basis. -/
def smoothToRapidMomentFockCLM (a : ℝ) (ha : 0 < a) : MomentFock →L[ℂ] MomentFock :=
  GaloisForLFunctions.lpDiagonalCLM (smoothToRapidMomentMultiplier a)
    (Real.sqrt_nonneg _) (norm_smoothToRapidMomentMultiplier_le ha)

/-- Inverse coefficient transport from the unsmoothed to the smooth moment basis. -/
def rapidToSmoothMomentFockCLM (a : ℝ) (ha : 0 < a) : MomentFock →L[ℂ] MomentFock :=
  GaloisForLFunctions.lpDiagonalCLM (rapidToSmoothMomentMultiplier a)
    (Real.sqrt_nonneg _) (norm_rapidToSmoothMomentMultiplier_le ha)

@[simp] theorem smoothToRapidMomentFockCLM_apply
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) :
    smoothToRapidMomentFockCLM a ha f n = smoothToRapidMomentMultiplier a n * f n := rfl

@[simp] theorem rapidToSmoothMomentFockCLM_apply
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) :
    rapidToSmoothMomentFockCLM a ha f n = rapidToSmoothMomentMultiplier a n * f n := rfl

/-- Bounded equivalence between exact smooth and unsmoothed moment coefficient realizations. -/
def smoothRapidMomentFockEquiv (a : ℝ) (ha : 0 < a) : MomentFock ≃L[ℂ] MomentFock :=
  ContinuousLinearEquiv.mk
    (LinearEquiv.mk (smoothToRapidMomentFockCLM a ha).toLinearMap
      (rapidToSmoothMomentFockCLM a ha)
      (by
        intro f
        ext n
        change rapidToSmoothMomentMultiplier a n *
          (smoothToRapidMomentMultiplier a n * f n) = f n
        rw [← mul_assoc,
          rapidToSmoothMomentMultiplier_mul_smoothToRapidMomentMultiplier ha n,
          one_mul])
      (by
        intro f
        ext n
        change smoothToRapidMomentMultiplier a n *
          (rapidToSmoothMomentMultiplier a n * f n) = f n
        rw [← mul_assoc,
          smoothToRapidMomentMultiplier_mul_rapidToSmoothMomentMultiplier ha n,
          one_mul]))
    (smoothToRapidMomentFockCLM a ha).continuous
    (rapidToSmoothMomentFockCLM a ha).continuous

theorem momentFockCoefficient_smoothToRapidMomentFockCLM
    {a : ℝ} (ha : 0 < a) (f : MomentFock) (n : ℕ) :
    momentFockCoefficient (rapidExponentialMomentFockData a ha)
        (smoothToRapidMomentFockCLM a ha f) n =
      momentFockCoefficient (smoothConvexRapidExponentialMomentFockData a ha) f n := by
  have hu := rapidExponentialFockMoment_pos ha n
  have hs := smoothConvexRapidExponentialFockMoment_pos ha n
  rw [momentFockCoefficient, momentFockCoefficient,
    smoothToRapidMomentFockCLM_apply]
  unfold smoothToRapidMomentMultiplier
  change ((Real.sqrt (rapidExponentialFockMoment a n /
      smoothConvexRapidExponentialFockMoment a n) : ℝ) : ℂ) * f n /
      (Real.sqrt (rapidExponentialFockMoment a n) : ℝ) =
    f n / (Real.sqrt (smoothConvexRapidExponentialFockMoment a n) : ℝ)
  rw [Real.sqrt_div hu.le]
  push_cast
  field_simp [(Real.sqrt_pos.2 hu).ne', (Real.sqrt_pos.2 hs).ne']

/-- The diagonal equivalence is semantic: it preserves the represented entire function exactly. -/
theorem momentFockFunction_smoothToRapidMomentFockCLM
    {a : ℝ} (ha : 0 < a) (f : MomentFock) :
    momentFockFunction (rapidExponentialMomentFockData a ha)
        (smoothToRapidMomentFockCLM a ha f) =
      momentFockFunction (smoothConvexRapidExponentialMomentFockData a ha) f := by
  unfold momentFockFunction
  congr 1
  funext n
  exact momentFockCoefficient_smoothToRapidMomentFockCLM ha f n

theorem momentFockEvaluation_smoothToRapidMomentFockCLM
    {a : ℝ} (ha : 0 < a) (f : MomentFock) (z : ℂ) :
    momentFockEvaluation (rapidExponentialMomentFockData a ha) z
        (smoothToRapidMomentFockCLM a ha f) =
      momentFockEvaluation (smoothConvexRapidExponentialMomentFockData a ha) z f := by
  rw [← momentFockFunction_eq_evaluation, ← momentFockFunction_eq_evaluation]
  exact congrFun (momentFockFunction_smoothToRapidMomentFockCLM ha f) z

theorem rapidToSmoothMomentFockCLM_kernel_smooth
    {a : ℝ} (ha : 0 < a) (z : ℂ) :
    rapidToSmoothMomentFockCLM a ha
        (momentFockKernel (smoothConvexRapidExponentialMomentFockData a ha) z) =
      momentFockKernel (rapidExponentialMomentFockData a ha) z := by
  ext n
  have hu := rapidExponentialFockMoment_pos ha n
  have hs := smoothConvexRapidExponentialFockMoment_pos ha n
  rw [rapidToSmoothMomentFockCLM_apply, momentFockKernel_apply,
    momentFockKernel_apply]
  unfold rapidToSmoothMomentMultiplier momentFockKernelCoeff
  change ((Real.sqrt (smoothConvexRapidExponentialFockMoment a n /
      rapidExponentialFockMoment a n) : ℝ) : ℂ) *
      ((starRingEnd ℂ z) ^ n /
        (Real.sqrt (smoothConvexRapidExponentialFockMoment a n) : ℝ)) =
    (starRingEnd ℂ z) ^ n /
      (Real.sqrt (rapidExponentialFockMoment a n) : ℝ)
  rw [Real.sqrt_div hs.le]
  push_cast
  field_simp [(Real.sqrt_pos.2 hu).ne', (Real.sqrt_pos.2 hs).ne']

theorem norm_rapidMomentFockKernel_le_sqrtComparison_mul_smooth
    {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ‖momentFockKernel (rapidExponentialMomentFockData a ha) z‖ ≤
      Real.sqrt (smoothConvexRapidMomentComparisonBound a) *
        ‖momentFockKernel (smoothConvexRapidExponentialMomentFockData a ha) z‖ := by
  rw [← rapidToSmoothMomentFockCLM_kernel_smooth ha z]
  calc
    ‖rapidToSmoothMomentFockCLM a ha
        (momentFockKernel (smoothConvexRapidExponentialMomentFockData a ha) z)‖ ≤
      ‖rapidToSmoothMomentFockCLM a ha‖ *
        ‖momentFockKernel (smoothConvexRapidExponentialMomentFockData a ha) z‖ :=
      (rapidToSmoothMomentFockCLM a ha).le_opNorm _
    _ ≤ Real.sqrt (smoothConvexRapidMomentComparisonBound a) *
        ‖momentFockKernel (smoothConvexRapidExponentialMomentFockData a ha) z‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa [rapidToSmoothMomentFockCLM] using
        GaloisForLFunctions.norm_lpDiagonalCLM_le
          (rapidToSmoothMomentMultiplier a)
          (Real.sqrt_nonneg _) (norm_rapidToSmoothMomentMultiplier_le ha)

/-- Ratio converting unsmoothed normalized evaluation to exact smooth normalized evaluation. -/
def smoothRapidNormalizedKernelRatio
    (a : ℝ) (ha : 0 < a) (p : Nat.Primes) : ℂ :=
  (‖momentFockKernel (rapidExponentialMomentFockData a ha)
      ((Real.log (p : ℝ) : ℝ) : ℂ)‖ /
    ‖momentFockKernel (smoothConvexRapidExponentialMomentFockData a ha)
      ((Real.log (p : ℝ) : ℝ) : ℂ)‖ : ℝ)

theorem norm_smoothRapidNormalizedKernelRatio_le
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    ‖smoothRapidNormalizedKernelRatio a ha p‖ ≤
      Real.sqrt (smoothConvexRapidMomentComparisonBound a) := by
  have hs : 0 < ‖momentFockKernel
      (smoothConvexRapidExponentialMomentFockData a ha)
      ((Real.log (p : ℝ) : ℝ) : ℂ)‖ :=
    norm_pos_iff.mpr (momentFockKernel_ne_zero _ _)
  unfold smoothRapidNormalizedKernelRatio
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hs.le)]
  rw [div_le_iff₀ hs]
  exact norm_rapidMomentFockKernel_le_sqrtComparison_mul_smooth ha _

theorem inner_normalizedSmoothKernel_eq_ratio_mul_rapid
    {a : ℝ} (ha : 0 < a) (f : MomentFock) (p : Nat.Primes) :
    inner ℂ
        (criticalPrimeMomentFockKernel
          (smoothConvexRapidExponentialMomentFockData a ha) p) f =
      smoothRapidNormalizedKernelRatio a ha p *
        inner ℂ
          (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha) p)
          (smoothToRapidMomentFockCLM a ha f) := by
  let z : ℂ := ((Real.log (p : ℝ) : ℝ) : ℂ)
  let ks := momentFockKernel (smoothConvexRapidExponentialMomentFockData a ha) z
  let ku := momentFockKernel (rapidExponentialMomentFockData a ha) z
  have hks : ks ≠ 0 := momentFockKernel_ne_zero _ _
  have hku : ku ≠ 0 := momentFockKernel_ne_zero _ _
  have heval : inner ℂ ku (smoothToRapidMomentFockCLM a ha f) = inner ℂ ks f := by
    simpa [ks, ku, z, momentFockEvaluation_apply] using
      momentFockEvaluation_smoothToRapidMomentFockCLM ha f z
  change inner ℂ ((‖ks‖ : ℂ)⁻¹ • ks) f =
    ((‖ku‖ / ‖ks‖ : ℝ) : ℂ) *
      inner ℂ ((‖ku‖ : ℂ)⁻¹ • ku) (smoothToRapidMomentFockCLM a ha f)
  rw [inner_smul_left, inner_smul_left]
  simp only [map_inv₀]
  rw [heval]
  push_cast
  field_simp [norm_ne_zero_iff.mpr hks, norm_ne_zero_iff.mpr hku]
  simp [mul_comm]

theorem criticalPrimeKernelRestriction_smooth_eq_ratio_mul_rapid
    {a : ℝ} (ha : 0 < a) (f : MomentFock) (p : Nat.Primes) :
    criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel
          (smoothConvexRapidExponentialMomentFockData a ha)) p f =
      smoothRapidNormalizedKernelRatio a ha p *
        criticalPrimeKernelRestriction
          (criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha)) p
          (smoothToRapidMomentFockCLM a ha f) := by
  rw [criticalPrimeKernelRestriction_apply, criticalPrimeKernelRestriction_apply,
    inner_normalizedSmoothKernel_eq_ratio_mul_rapid ha f p]
  ring

/-- Bounded diagonal converting rapid normalized samples to exact smooth normalized samples. -/
def smoothRapidPrimeSampleDiagonal (a : ℝ) (ha : 0 < a) :
    CriticalPrimeEllTwo →L[ℂ] CriticalPrimeEllTwo :=
  GaloisForLFunctions.lpDiagonalCLM (smoothRapidNormalizedKernelRatio a ha)
    (Real.sqrt_nonneg _) (norm_smoothRapidNormalizedKernelRatio_le ha)

@[simp] theorem smoothRapidPrimeSampleDiagonal_apply
    (a : ℝ) (ha : 0 < a) (g : CriticalPrimeEllTwo) (p : Nat.Primes) :
    smoothRapidPrimeSampleDiagonal a ha g p =
      smoothRapidNormalizedKernelRatio a ha p * g p := rfl

/-- Exact smooth normalized all-prime sampler, factored through the rapid tail-equivalent carrier. -/
def smoothCriticalPrimeSamplingOperator (a : ℝ) (ha : 0 < a) :
    MomentFock →L[ℂ] CriticalPrimeEllTwo :=
  (smoothRapidPrimeSampleDiagonal a ha).comp
    ((rapidCriticalPrimeSamplingOperator a ha).comp
      (smoothToRapidMomentFockCLM a ha))

@[simp] theorem smoothCriticalPrimeSamplingOperator_apply
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (p : Nat.Primes) :
    smoothCriticalPrimeSamplingOperator a ha f p =
      criticalPrimeKernelRestriction
        (criticalPrimeMomentFockKernel
          (smoothConvexRapidExponentialMomentFockData a ha)) p f := by
  rw [smoothCriticalPrimeSamplingOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, smoothRapidPrimeSampleDiagonal_apply,
    rapidCriticalPrimeSamplingOperator_apply]
  exact (criticalPrimeKernelRestriction_smooth_eq_ratio_mul_rapid ha f p).symm

theorem smoothCriticalPrimeSamplingOperator_isCompactOperator
    {a : ℝ} (ha : 0 < a) :
    IsCompactOperator (smoothCriticalPrimeSamplingOperator a ha) := by
  have hrapid := rapidCriticalPrimeSamplingOperator_isCompactOperator ha
  have hsource := hrapid.comp_clm (smoothToRapidMomentFockCLM a ha)
  have htarget := hsource.clm_comp (smoothRapidPrimeSampleDiagonal a ha)
  change IsCompactOperator (fun f : MomentFock =>
    smoothRapidPrimeSampleDiagonal a ha
      (rapidCriticalPrimeSamplingOperator a ha
        (smoothToRapidMomentFockCLM a ha f)))
  exact htarget

theorem adjoint_smoothCriticalPrimeSamplingOperator_coordinateBasis
    (a : ℝ) (ha : 0 < a) (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (smoothCriticalPrimeSamplingOperator a ha)
        (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
      (Real.sqrt (criticalPrimeSamplingWeight p) : ℂ) •
        criticalPrimeMomentFockKernel
          (smoothConvexRapidExponentialMomentFockData a ha) p := by
  classical
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right,
    HTGeometry.ellTwoCoordinateBasis_apply,
    lp.inner_single_right, smoothCriticalPrimeSamplingOperator_apply,
    criticalPrimeKernelRestriction_apply]
  rw [inner_smul_right]
  simp [RCLike.inner_apply]

theorem normSq_adjoint_smoothCriticalPrimeSamplingOperator_coordinateBasis
    (a : ℝ) (ha : 0 < a) (p : Nat.Primes) :
    ‖ContinuousLinearMap.adjoint (smoothCriticalPrimeSamplingOperator a ha)
        (HTGeometry.ellTwoCoordinateBasis Nat.Primes p)‖ ^ 2 =
      criticalPrimeSamplingWeight p := by
  rw [adjoint_smoothCriticalPrimeSamplingOperator_coordinateBasis,
    norm_smul, norm_criticalPrimeMomentFockKernel, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  exact (criticalPrimeSamplingWeight_pos p).le

theorem smoothCriticalPrimeSamplingOperator_not_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) :
    ¬ (smoothCriticalPrimeSamplingOperator a ha).IsHilbertSchmidt :=
  not_isHilbertSchmidt_of_adjoint_coordinate_normSq_eq_criticalPrimeSamplingWeight _
    (normSq_adjoint_smoothCriticalPrimeSamplingOperator_coordinateBasis a ha)

/-- Positive incidence of exact smooth normalized critical-prime evaluation. -/
def smoothCriticalPrimeSamplingIncidence (a : ℝ) (ha : 0 < a) :
    MomentFock →L[ℂ] MomentFock :=
  criticalPrimeSamplingIncidence (smoothCriticalPrimeSamplingOperator a ha)

theorem smoothCriticalPrimeSamplingIncidence_isPositive
    (a : ℝ) (ha : 0 < a) :
    (smoothCriticalPrimeSamplingIncidence a ha).IsPositive :=
  criticalPrimeSamplingIncidence_isPositive _

theorem smoothCriticalPrimeSamplingIncidence_isCompactOperator
    {a : ℝ} (ha : 0 < a) :
    IsCompactOperator (smoothCriticalPrimeSamplingIncidence a ha) :=
  criticalPrimeSamplingIncidence_isCompactOperator
    (smoothCriticalPrimeSamplingOperator_isCompactOperator ha)

theorem smoothCriticalPrimeSamplingIncidence_not_memSchattenClass_one
    (a : ℝ) (ha : 0 < a) :
    ¬ MemSchattenClass 1 (smoothCriticalPrimeSamplingIncidence a ha) :=
  criticalPrimeSamplingIncidence_not_memSchattenClass_one _
    (normSq_adjoint_smoothCriticalPrimeSamplingOperator_coordinateBasis a ha)

/-- Distinguished constant vector in the exact smooth rapid carrier. -/
def smoothConvexRapidExponentialMomentFockOne (a : ℝ) (ha : 0 < a) : MomentFock :=
  momentFockOne (smoothConvexRapidExponentialMomentFockData a ha)

theorem smoothToRapidMomentFockCLM_one
    (a : ℝ) (ha : 0 < a) :
    smoothToRapidMomentFockCLM a ha
        (smoothConvexRapidExponentialMomentFockOne a ha) =
      rapidExponentialMomentFockOne a ha := by
  ext n
  by_cases hn : n = 0
  · subst n
    have hu := rapidExponentialFockMoment_pos ha 0
    have hs := smoothConvexRapidExponentialFockMoment_pos ha 0
    rw [smoothToRapidMomentFockCLM_apply]
    unfold smoothConvexRapidExponentialMomentFockOne rapidExponentialMomentFockOne
    simp only [momentFockOne, lp.single_apply, Pi.single_apply, if_pos]
    unfold smoothToRapidMomentMultiplier
    change ((Real.sqrt (rapidExponentialFockMoment a 0 /
        smoothConvexRapidExponentialFockMoment a 0) : ℝ) : ℂ) *
        (Real.sqrt (smoothConvexRapidExponentialFockMoment a 0) : ℝ) =
      (Real.sqrt (rapidExponentialFockMoment a 0) : ℝ)
    rw [Real.sqrt_div hu.le]
    push_cast
    field_simp [(Real.sqrt_pos.2 hs).ne']
  · rw [smoothToRapidMomentFockCLM_apply]
    unfold smoothConvexRapidExponentialMomentFockOne rapidExponentialMomentFockOne
    simp [momentFockOne, lp.single_apply, hn]

theorem momentFockFunction_smoothConvexRapid_one
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    momentFockFunction (smoothConvexRapidExponentialMomentFockData a ha)
        (smoothConvexRapidExponentialMomentFockOne a ha) z = 1 :=
  momentFockFunction_one _ _

/-- Completed two-sided theta trace on the exact smooth rapid moment carrier. -/
def smoothConvexRapidExponentialMomentFockThetaTrace
    (a : ℝ) (ha : 0 < a) (f : MomentFock) : ℂ → ℂ :=
  rapidExponentialMomentFockThetaTrace a ha (smoothToRapidMomentFockCLM a ha f)

theorem differentiable_smoothConvexRapidExponentialMomentFockThetaTrace
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (f : MomentFock) :
    Differentiable ℂ (smoothConvexRapidExponentialMomentFockThetaTrace a ha f) :=
  differentiable_rapidExponentialMomentFockThetaTrace a ha haHalf _

/-- Compact-open continuous theta trace on the exact smooth carrier. -/
def smoothConvexRapidExponentialMomentFockThetaTraceCompactOpen
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) :
    MomentFock →L[ℂ] DeningerCompactOpenEntire :=
  (rapidExponentialMomentFockThetaTraceCompactOpen a ha haHalf).comp
    (smoothToRapidMomentFockCLM a ha)

@[simp] theorem smoothConvexRapidExponentialMomentFockThetaTraceCompactOpen_apply
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2)
    (f : MomentFock) (z : ℂ) :
    smoothConvexRapidExponentialMomentFockThetaTraceCompactOpen a ha haHalf f z =
      smoothConvexRapidExponentialMomentFockThetaTrace a ha f z := rfl

/-- Exact completed critical trace of the smooth carrier's distinguished constant vector. -/
theorem completedRiemannZeta₀_critical_eq_smoothConvexRapidThetaCarrier_one
    (a : ℝ) (ha : 0 < a) (haHalf : a < 1 / 2) (t : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * Complex.I) =
      smoothConvexRapidExponentialMomentFockThetaTraceCompactOpen a ha haHalf
        (smoothConvexRapidExponentialMomentFockOne a ha)
          ((t / (4 * Real.pi) : ℝ) : ℂ) / 2 := by
  rw [smoothConvexRapidExponentialMomentFockThetaTraceCompactOpen_apply]
  unfold smoothConvexRapidExponentialMomentFockThetaTrace
  rw [smoothToRapidMomentFockCLM_one]
  simpa using
    completedRiemannZeta₀_critical_eq_rapidExponentialMomentFockThetaTrace_one a ha t

end

end RHTower
