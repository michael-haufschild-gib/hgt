import Mathlib.MeasureTheory.Integral.Prod
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureTranslatedCellAverage
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSafeShiftRobinPlemelj
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureArchContourAsymptotic
import GaloisForLFunctions.RHTower.XiWardCubicPositiveShiftAveragedMultiplicity
import GaloisForLFunctions.RHTower.XiRectangleFold
import GaloisForLFunctions.RHTower.XiShiftLoewnerEulerSplit
import GaloisForLFunctions.RHTower.Sieve.LogNormSegment
import GaloisForLFunctions.HTGeometry.ClockVolterraOperator

/-!
# Source-first positive-shift and height-cell averaging for HCF

Positive real displacement averaging removes translated-predecessor collisions and recovers exact
Xi multiplicity after continuation.  Independently, one-cell height translation removes every
nonzero HCF Fourier alias.  This module proves that the two averages can be formed together before
divisor access.

On a safe Euler line, the phase average of the lattice-summed displacement covariance is exactly a
vertical rectangle integral of completed pole--Gamma--von-Mangoldt current increments.  Clamping
the displacement outside its integration interval gives the globally continuous extension needed
for Fubini without changing a single value inside that interval.
-/

open Complex LSeries Filter Topology Set MeasureTheory intervalIntegral
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Completed source-current increment on a safe vertical line.  Displacement is clamped only to
provide a globally continuous two-variable representative for compact-rectangle Fubini. -/
def xiWardCubicSafeHeightShiftIncrement
    (sigma a b eps t : ℝ) : ℂ :=
  xiWardCubicCompletedArithmeticCurrent
      (((sigma + clampTo a b eps : ℝ) : ℂ) + (t : ℂ) * I) -
    xiWardCubicCompletedArithmeticCurrent ((sigma : ℂ) + (t : ℂ) * I)

/-- The clamped pole--Gamma--von-Mangoldt increment is jointly continuous in displacement and
height throughout the safe Euler chamber. -/
theorem continuous_uncurry_xiWardCubicSafeHeightShiftIncrement
    {sigma a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hsigma : 1 < sigma) :
    Continuous (Function.uncurry (xiWardCubicSafeHeightShiftIncrement sigma a b)) := by
  let upper : ℝ × ℝ → ℂ := fun p =>
    (((sigma + clampTo a b p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I)
  let lower : ℝ × ℝ → ℂ := fun p =>
    ((sigma : ℂ) + (p.2 : ℂ) * I)
  have hu : Continuous upper := by
    dsimp [upper]
    have hc : Continuous (fun p : ℝ × ℝ => clampTo a b p.1) :=
      (continuous_clampTo a b).comp continuous_fst
    fun_prop (disch := assumption)
  have hl : Continuous lower := by
    dsimp [lower]
    fun_prop
  have huzero : ∀ p : ℝ × ℝ, xi (upper p) ≠ 0 := by
    intro p
    apply xi_ne_zero_of_one_le_re
    dsimp [upper]
    simp only [ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    have hclamp := (clampTo_mem hab p.1).1
    linarith
  have hlzero : ∀ p : ℝ × ℝ, xi (lower p) ≠ 0 := by
    intro p
    apply xi_ne_zero_of_one_le_re
    dsimp [lower]
    simp
    linarith
  have hlogu : Continuous (fun p : ℝ × ℝ => logDeriv xi (upper p)) := by
    have hbase : ContinuousOn (logDeriv xi) (range upper) :=
      continuousOn_logDeriv_xi (fun q hq => by
        obtain ⟨p, rfl⟩ := hq
        exact huzero p)
    have hcomp := hbase.comp hu.continuousOn
      (fun p (_ : p ∈ (univ : Set (ℝ × ℝ))) => mem_range_self p)
    rw [continuousOn_univ] at hcomp
    change Continuous (logDeriv xi ∘ upper)
    exact hcomp
  have hlogl : Continuous (fun p : ℝ × ℝ => logDeriv xi (lower p)) := by
    have hbase : ContinuousOn (logDeriv xi) (range lower) :=
      continuousOn_logDeriv_xi (fun q hq => by
        obtain ⟨p, rfl⟩ := hq
        exact hlzero p)
    have hcomp := hbase.comp hl.continuousOn
      (fun p (_ : p ∈ (univ : Set (ℝ × ℝ))) => mem_range_self p)
    rw [continuousOn_univ] at hcomp
    change Continuous (logDeriv xi ∘ lower)
    exact hcomp
  have hcurrentu : Continuous
      (fun p : ℝ × ℝ => xiWardCubicCompletedArithmeticCurrent (upper p)) := by
    convert hlogu using 1
    funext p
    have hsafe : 1 < (upper p).re := by
      dsimp [upper]
      have hclamp := (clampTo_mem hab p.1).1
      norm_num
      linarith
    rw [logDeriv_xi_eq_arithmetic hsafe]
    rfl
  have hcurrentl : Continuous
      (fun p : ℝ × ℝ => xiWardCubicCompletedArithmeticCurrent (lower p)) := by
    convert hlogl using 1
    funext p
    have hsafe : 1 < (lower p).re := by
      simpa [lower] using hsigma
    rw [logDeriv_xi_eq_arithmetic hsafe]
    rfl
  exact hcurrentu.sub hcurrentl

/-! ## Lightweight rectangle and unit-cell integration -/

/-- Compact-box Fubini for a jointly continuous complex integrand. -/
theorem intervalIntegral_swap_of_continuous_complex
    {F : ℝ → ℝ → ℂ} (hF : Continuous (Function.uncurry F))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, F x y) =
      ∫ y in c..d, ∫ x in a..b, F x y := by
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  haveI : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by simp [Real.volume_Ioc]⟩
  haveI : IsFiniteMeasure (volume.restrict (Ioc c d)) := ⟨by simp [Real.volume_Ioc]⟩
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  simp_rw [intervalIntegral.integral_of_le hcd, intervalIntegral.integral_of_le hab]
  refine MeasureTheory.integral_integral_swap ?_
  refine Integrable.mono' (integrable_const C) hF.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  exact hC p ⟨Ioc_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩

/-- Consecutive natural unit cells tile the interval from zero to their cutoff. -/
theorem intervalIntegral_sum_range_heightCells_eq
    {f : ℝ → ℂ} (hf : Continuous f) (K : ℕ) :
    (∫ v : ℝ in (0 : ℝ)..1,
      ∑ m ∈ Finset.range K, f ((m : ℝ) + v)) =
      ∫ y : ℝ in (0 : ℝ)..(K : ℝ), f y := by
  induction K with
  | zero => simp
  | succ K ih =>
      simp_rw [Finset.sum_range_succ]
      have hsumCont : Continuous (fun v : ℝ =>
          ∑ m ∈ Finset.range K, f ((m : ℝ) + v)) := by
        fun_prop
      have hcellCont : Continuous (fun v : ℝ => f ((K : ℝ) + v)) := by
        fun_prop
      rw [intervalIntegral.integral_add
        (hsumCont.intervalIntegrable _ _) (hcellCont.intervalIntegrable _ _)]
      rw [ih]
      have hshift :
          (∫ v : ℝ in (0 : ℝ)..1, f ((K : ℝ) + v)) =
            ∫ y : ℝ in (K : ℝ)..((K : ℝ) + 1), f y := by
        rw [intervalIntegral.integral_comp_add_left f (K : ℝ)]
        simp
      rw [hshift, Nat.cast_succ]
      exact intervalIntegral.integral_add_adjacent_intervals
        (a := (0 : ℝ)) (b := (K : ℝ)) (c := (K : ℝ) + 1)
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- Consecutive natural cells tile every interval with natural endpoints. -/
theorem intervalIntegral_sum_Ico_heightCells_eq
    {f : ℝ → ℂ} (hf : Continuous f) {A B : ℕ} (hAB : A ≤ B) :
    (∫ v : ℝ in (0 : ℝ)..1,
      ∑ m ∈ Finset.Ico A B, f ((m : ℝ) + v)) =
      ∫ y : ℝ in (A : ℝ)..(B : ℝ), f y := by
  have heq : (fun v : ℝ => ∑ m ∈ Finset.Ico A B, f ((m : ℝ) + v)) =
      fun v : ℝ =>
        (∑ m ∈ Finset.range B, f ((m : ℝ) + v)) -
          ∑ m ∈ Finset.range A, f ((m : ℝ) + v) := by
    funext v
    exact Finset.sum_Ico_eq_sub (fun m => f ((m : ℝ) + v)) hAB
  rw [heq]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral_sum_range_heightCells_eq hf B,
      intervalIntegral_sum_range_heightCells_eq hf A]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (0 : ℝ) (A : ℝ))
      (hf.intervalIntegrable (A : ℝ) (B : ℝ))]
    ring
  · exact (continuous_finsetSum (Finset.range B) fun m _ =>
      hf.comp (continuous_const.add continuous_id)).intervalIntegrable 0 1
  · exact (continuous_finsetSum (Finset.range A) fun m _ =>
      hf.comp (continuous_const.add continuous_id)).intervalIntegrable 0 1

/-- Parametric unit-cell tiling.  A phase integral of any continuous lattice-summed family equals
its ordinary vertical rectangle integral after Fubini. -/
theorem intervalIntegral_integral_sum_Ico_unitCells_eq_vertical
    {F : ℝ → ℝ → ℂ} (hF : Continuous (Function.uncurry F))
    {a b : ℝ} {A B : ℕ} (hab : a ≤ b) (hAB : A ≤ B) :
    (∫ theta : ℝ in (0 : ℝ)..1,
      ∫ eps : ℝ in a..b,
        ∑ m ∈ Finset.Ico A B, F eps ((m : ℝ) + theta)) =
      ∫ eps : ℝ in a..b,
        ∫ t : ℝ in (A : ℝ)..(B : ℝ), F eps t := by
  have hjoint : Continuous (Function.uncurry fun theta eps : ℝ =>
      ∑ m ∈ Finset.Ico A B, F eps ((m : ℝ) + theta)) := by
    change Continuous (fun p : ℝ × ℝ =>
      ∑ m ∈ Finset.Ico A B, F p.2 ((m : ℝ) + p.1))
    exact continuous_finsetSum (Finset.Ico A B) fun m _ => hF.comp
      ((continuous_snd : Continuous fun p : ℝ × ℝ => p.2).prodMk
        (continuous_const.add continuous_fst))
  calc
    (∫ theta : ℝ in (0 : ℝ)..1,
      ∫ eps : ℝ in a..b,
        ∑ m ∈ Finset.Ico A B, F eps ((m : ℝ) + theta)) =
        ∫ eps : ℝ in a..b,
          ∫ theta : ℝ in (0 : ℝ)..1,
            ∑ m ∈ Finset.Ico A B, F eps ((m : ℝ) + theta) := by
      exact intervalIntegral_swap_of_continuous_complex hjoint (by norm_num) hab
    _ = ∫ eps : ℝ in a..b,
        ∫ t : ℝ in (A : ℝ)..(B : ℝ), F eps t := by
      apply intervalIntegral.integral_congr
      intro eps heps
      exact intervalIntegral_sum_Ico_heightCells_eq
        (hF.comp (continuous_const.prodMk continuous_id)) hAB

/-- Source specialization: the two averages reduce exactly to one vertical rectangle of completed
arithmetic-current increments. -/
theorem integral_integral_sum_xiWardCubicSafeHeightShiftIncrement_eq_vertical
    {sigma a b : ℝ} {A B : ℕ} (hab : a ≤ b) (ha : 0 ≤ a) (hsigma : 1 < sigma)
    (hAB : A ≤ B) :
    (∫ theta : ℝ in (0 : ℝ)..1,
      ∫ eps : ℝ in a..b,
        ∑ m ∈ Finset.Ico A B,
          xiWardCubicSafeHeightShiftIncrement sigma a b eps ((m : ℝ) + theta)) =
      ∫ eps : ℝ in a..b,
        ∫ t : ℝ in (A : ℝ)..(B : ℝ),
          xiWardCubicSafeHeightShiftIncrement sigma a b eps t := by
  exact intervalIntegral_integral_sum_Ico_unitCells_eq_vertical
    (F := xiWardCubicSafeHeightShiftIncrement sigma a b)
    (continuous_uncurry_xiWardCubicSafeHeightShiftIncrement hab ha hsigma) hab hAB

/-- Lattice sum of the existing source-first positive-shift arithmetic average. -/
def xiWardCubicHeightCellShiftWeightedArithmeticAverage
    (sigma a b : ℝ) (A B : ℕ) (theta : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ico A B,
    xiWardCubicShiftWeightedArithmeticAverage
      ((sigma : ℂ) + (((m : ℝ) + theta : ℝ) : ℂ) * I) a b

/-- Exact double-average connector.  Phase averaging the existing positive-shift multiplicity
extractor equals a normalized vertical pole--Gamma--von-Mangoldt rectangle, wholly before divisor
continuation. -/
theorem integral_xiWardCubicHeightCellShiftWeightedArithmeticAverage_eq_vertical
    {sigma a b : ℝ} {A B : ℕ} (ha : 0 ≤ a) (hab : a < b) (hsigma : 1 < sigma)
    (hAB : A ≤ B) :
    (∫ theta : ℝ in (0 : ℝ)..1,
      xiWardCubicHeightCellShiftWeightedArithmeticAverage sigma a b A B theta) =
      ((((b - a)⁻¹ : ℝ) : ℂ)) *
        ∫ eps : ℝ in a..b,
          ∫ t : ℝ in (A : ℝ)..(B : ℝ),
            xiWardCubicSafeHeightShiftIncrement sigma a b eps t := by
  let c : ℂ := (((b - a)⁻¹ : ℝ) : ℂ)
  have hpoint (theta : ℝ) :
      xiWardCubicHeightCellShiftWeightedArithmeticAverage sigma a b A B theta =
        c * ∫ eps : ℝ in a..b,
          ∑ m ∈ Finset.Ico A B,
            xiWardCubicSafeHeightShiftIncrement sigma a b eps ((m : ℝ) + theta) := by
    have hinc :=
      continuous_uncurry_xiWardCubicSafeHeightShiftIncrement hab.le ha hsigma
    have havg (m : ℕ) :
        xiWardCubicShiftWeightedArithmeticAverage
            ((sigma : ℂ) + (((m : ℝ) + theta : ℝ) : ℂ) * I) a b =
          c * ∫ eps : ℝ in a..b,
            xiWardCubicSafeHeightShiftIncrement sigma a b eps ((m : ℝ) + theta) := by
      rw [xiWardCubicShiftWeightedArithmeticAverage_eq_incrementAverage _ ha hab]
      congr 1
      apply intervalIntegral.integral_congr
      intro eps heps
      rw [uIcc_of_le hab.le] at heps
      unfold xiWardCubicSafeHeightShiftIncrement
      dsimp only
      rw [clampTo_of_mem heps]
      congr 2
      push_cast
      ring
    rw [xiWardCubicHeightCellShiftWeightedArithmeticAverage]
    simp_rw [havg]
    rw [← Finset.mul_sum]
    congr 1
    rw [← intervalIntegral.integral_finsetSum]
    intro m hm
    exact (hinc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  calc
    (∫ theta : ℝ in (0 : ℝ)..1,
      xiWardCubicHeightCellShiftWeightedArithmeticAverage sigma a b A B theta) =
        ∫ theta : ℝ in (0 : ℝ)..1,
          c * ∫ eps : ℝ in a..b,
            ∑ m ∈ Finset.Ico A B,
              xiWardCubicSafeHeightShiftIncrement sigma a b eps ((m : ℝ) + theta) := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      exact hpoint theta
    _ = c * ∫ theta : ℝ in (0 : ℝ)..1,
        ∫ eps : ℝ in a..b,
          ∑ m ∈ Finset.Ico A B,
            xiWardCubicSafeHeightShiftIncrement sigma a b eps ((m : ℝ) + theta) := by
      rw [intervalIntegral.integral_const_mul]
    _ = c * ∫ eps : ℝ in a..b,
        ∫ t : ℝ in (A : ℝ)..(B : ℝ),
          xiWardCubicSafeHeightShiftIncrement sigma a b eps t := by
      rw [integral_integral_sum_xiWardCubicSafeHeightShiftIncrement_eq_vertical
        hab.le ha hsigma hAB]
    _ = ((((b - a)⁻¹ : ℝ) : ℂ)) *
        ∫ eps : ℝ in a..b,
          ∫ t : ℝ in (A : ℝ)..(B : ℝ),
            xiWardCubicSafeHeightShiftIncrement sigma a b eps t := rfl

/-! ## Identification with the HCF safe-shift Robin jet -/

/-- On the absolute-Euler chamber, the XiWard completed arithmetic current is exactly the negative
of the HCF von-Mangoldt-minus-archimedean carrier. -/
theorem xiWardCubicCompletedArithmeticCurrent_eq_neg_criticalFeatureEulerVMArchCarrier
    {s : ℂ} (hs : 1 < s.re) :
    xiWardCubicCompletedArithmeticCurrent s =
      -criticalFeatureEulerVMArchCarrier s := by
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have h0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have h1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hspos
  have hGd : DifferentiableAt ℂ Gammaℝ s := differentiableAt_Gammaℝ_of_re_pos hspos
  unfold xiWardCubicCompletedArithmeticCurrent criticalFeatureEulerVMArchCarrier
  rw [logDeriv_archFactor_split h0 h1 hG hGd]
  ring

/-- Exact diagonal separation law.  The raw HCF pole--Gamma--von-Mangoldt jet is twice the real
part of completed-current value minus its positive-shift diagonal finite part. -/
theorem criticalFeaturePoleGammaVMJet_eq_xiWardCubicRobinFinitePart (t : ℝ) :
    criticalFeaturePoleGammaVMJet t =
      2 * ((xiWardCubicCompletedArithmeticCurrent
            (criticalFeatureEulerVMArchPoint t)).re -
        (deriv xiWardCubicCompletedArithmeticCurrent
            (criticalFeatureEulerVMArchPoint t)).re) := by
  let s := criticalFeatureEulerVMArchPoint t
  have hs : 1 < s.re := by
    rw [show s.re = 3 / 2 by
      simp [s, criticalFeatureEulerVMArchPoint_re]]
    norm_num
  have hH : DifferentiableAt ℂ criticalFeatureEulerVMArchCarrier s := by
    simpa [s] using differentiableAt_criticalFeatureEulerVMArchCarrier t
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : xiWardCubicCompletedArithmeticCurrent =ᶠ[nhds s]
      fun z => -criticalFeatureEulerVMArchCarrier z := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact xiWardCubicCompletedArithmeticCurrent_eq_neg_criticalFeatureEulerVMArchCarrier hz
  have hvalue :=
    xiWardCubicCompletedArithmeticCurrent_eq_neg_criticalFeatureEulerVMArchCarrier hs
  have hderiv := Filter.EventuallyEq.deriv_eq hev
  have hnegderiv :
      deriv (fun z => -criticalFeatureEulerVMArchCarrier z) s =
        -deriv criticalFeatureEulerVMArchCarrier s :=
    hH.hasDerivAt.neg.deriv
  rw [criticalFeaturePoleGammaVMJet_eq_eulerVMArchJet]
  change 2 * ((deriv criticalFeatureEulerVMArchCarrier s).re -
      (criticalFeatureEulerVMArchCarrier s).re) = _
  rw [hderiv, hnegderiv, hvalue]
  simp
  ring

/-- The completed arithmetic current is differentiable at every HCF safe-line lattice point. -/
theorem hasDerivAt_xiWardCubicCompletedArithmeticCurrent_eulerVMArchPoint (t : ℝ) :
    HasDerivAt xiWardCubicCompletedArithmeticCurrent
      (deriv xiWardCubicCompletedArithmeticCurrent
        (criticalFeatureEulerVMArchPoint t))
      (criticalFeatureEulerVMArchPoint t) := by
  let s := criticalFeatureEulerVMArchPoint t
  have hs : 1 < s.re := by
    rw [show s.re = 3 / 2 by
      simp [s, criticalFeatureEulerVMArchPoint_re]]
    norm_num
  have hH : DifferentiableAt ℂ criticalFeatureEulerVMArchCarrier s := by
    simpa [s] using differentiableAt_criticalFeatureEulerVMArchCarrier t
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : xiWardCubicCompletedArithmeticCurrent =ᶠ[nhds s]
      fun z => -criticalFeatureEulerVMArchCarrier z := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact xiWardCubicCompletedArithmeticCurrent_eq_neg_criticalFeatureEulerVMArchCarrier hz
  have hneg : HasDerivAt (fun z => -criticalFeatureEulerVMArchCarrier z)
      (-deriv criticalFeatureEulerVMArchCarrier s) s := hH.hasDerivAt.neg
  have hcur : HasDerivAt xiWardCubicCompletedArithmeticCurrent
      (-deriv criticalFeatureEulerVMArchCarrier s) s := by
    exact hneg.congr_of_eventuallyEq hev
  convert hcur using 1
  exact hcur.deriv

/-- Submicroscopic positive shifts converge to the exact HCF Robin finite part.  This is the
source-side diagonal separator; the remaining quantitative task is a height-local upper estimate
for these finite-displacement expressions before taking the limit. -/
theorem tendsto_xiWardCubicRobinFinitePart_to_criticalFeaturePoleGammaVMJet (t : ℝ) :
    Tendsto
      (fun eps : ℂ =>
        2 * ((xiWardCubicCompletedArithmeticCurrent
              (criticalFeatureEulerVMArchPoint t)).re -
          (xiWardCubicShiftArithmeticCovariance
              (criticalFeatureEulerVMArchPoint t) eps).re))
      (𝓝[≠] 0)
      (𝓝 (criticalFeaturePoleGammaVMJet t)) := by
  have hcov := tendsto_xiWardCubicShiftArithmeticCovariance
    (hasDerivAt_xiWardCubicCompletedArithmeticCurrent_eulerVMArchPoint t)
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcov
  have hconst : Tendsto
      (fun _ : ℂ =>
        (xiWardCubicCompletedArithmeticCurrent
          (criticalFeatureEulerVMArchPoint t)).re)
      (𝓝[≠] 0)
      (𝓝 ((xiWardCubicCompletedArithmeticCurrent
        (criticalFeatureEulerVMArchPoint t)).re)) := tendsto_const_nhds
  have hcomb := (hconst.sub hre).const_mul (2 : ℝ)
  simpa only [Function.comp_apply,
    criticalFeaturePoleGammaVMJet_eq_xiWardCubicRobinFinitePart] using hcomb

/-! ## Finite-lattice submicroscopic separator -/

/-- Finite-displacement Robin jet written only from the completed arithmetic current and its
punctured positive-shift covariance. -/
def criticalFeatureXiWardCubicFiniteShiftRobinJet (t : ℝ) (eps : ℂ) : ℝ :=
  2 * ((xiWardCubicCompletedArithmeticCurrent
          (criticalFeatureEulerVMArchPoint t)).re -
    (xiWardCubicShiftArithmeticCovariance
          (criticalFeatureEulerVMArchPoint t) eps).re)

/-- The finite-displacement Robin jet converges pointwise to the HCF pole--Gamma--von-Mangoldt
jet. -/
theorem tendsto_criticalFeatureXiWardCubicFiniteShiftRobinJet (t : ℝ) :
    Tendsto (criticalFeatureXiWardCubicFiniteShiftRobinJet t) (𝓝[≠] 0)
      (𝓝 (criticalFeaturePoleGammaVMJet t)) := by
  change Tendsto
    (fun eps : ℂ =>
      2 * ((xiWardCubicCompletedArithmeticCurrent
              (criticalFeatureEulerVMArchPoint t)).re -
        (xiWardCubicShiftArithmeticCovariance
              (criticalFeatureEulerVMArchPoint t) eps).re))
    (𝓝[≠] 0) (𝓝 (criticalFeaturePoleGammaVMJet t))
  exact tendsto_xiWardCubicRobinFinitePart_to_criticalFeaturePoleGammaVMJet t

/-- Finite lattice sum of the pre-divisor submicroscopic Robin jets. -/
def criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget
    (K : Finset ℤ) (eps : ℂ) : ℝ :=
  ∑ k ∈ K, criticalFeatureXiWardCubicFiniteShiftRobinJet (k : ℝ) eps

/-- Shrinking the positive displacement after finite lattice summation recovers the exact
pole--Gamma--von-Mangoldt lattice budget. -/
theorem tendsto_criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget
    (K : Finset ℤ) :
    Tendsto (criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget K) (𝓝[≠] 0)
      (𝓝 (criticalFeaturePoleGammaVMLatticeBudget K)) := by
  change Tendsto
    (fun eps : ℂ =>
      ∑ k ∈ K, criticalFeatureXiWardCubicFiniteShiftRobinJet (k : ℝ) eps)
    (𝓝[≠] 0) (𝓝 (criticalFeaturePoleGammaVMLatticeBudget K))
  rw [criticalFeaturePoleGammaVMLatticeBudget]
  apply tendsto_finsetSum K
  intro k hk
  exact tendsto_criticalFeatureXiWardCubicFiniteShiftRobinJet (k : ℝ)

/-- Finite-displacement corrected source budget.  The first term is evaluated at a nonzero
submicroscopic shift; the thin-strip contour removes critical-line multiplicity without a zero
enumeration. -/
def criticalFeatureXiWardCubicFiniteShiftThinStripBudget
    (K : Finset ℤ) (eps : ℂ) (A B delta : ℝ) : ℝ :=
  ∑ k ∈ K, (criticalFeatureXiWardCubicFiniteShiftRobinJet (k : ℝ) eps -
    (criticalFeatureThinStripSourceContour (k : ℝ) A B delta).re)

/-- Exact finite-lattice landing: the positive-shift corrected source budget converges to the HCF
thin-strip pole--Gamma--von-Mangoldt budget. -/
theorem tendsto_criticalFeatureXiWardCubicFiniteShiftThinStripBudget
    (K : Finset ℤ) (A B delta : ℝ) :
    Tendsto
      (fun eps : ℂ =>
        criticalFeatureXiWardCubicFiniteShiftThinStripBudget K eps A B delta)
      (𝓝[≠] 0)
      (𝓝 (criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta)) := by
  change Tendsto
    (fun eps : ℂ =>
      ∑ k ∈ K, (criticalFeatureXiWardCubicFiniteShiftRobinJet (k : ℝ) eps -
        (criticalFeatureThinStripSourceContour (k : ℝ) A B delta).re))
    (𝓝[≠] 0)
    (𝓝 (criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta))
  rw [criticalFeatureThinStripPoleGammaVMLatticeBudget]
  apply tendsto_finsetSum K
  intro k hk
  exact (tendsto_criticalFeatureXiWardCubicFiniteShiftRobinJet (k : ℝ)).sub
    tendsto_const_nhds

/-- A uniform upper bound at all sufficiently small nonzero shifts survives the diagonal limit. -/
theorem criticalFeatureThinStripPoleGammaVMLatticeBudget_le_of_eventually_finiteShift
    (K : Finset ℤ) (A B delta C : ℝ)
    (hbound : ∀ᶠ eps : ℂ in 𝓝[≠] 0,
      criticalFeatureXiWardCubicFiniteShiftThinStripBudget K eps A B delta ≤ C) :
    criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta ≤ C :=
  le_of_tendsto
    (tendsto_criticalFeatureXiWardCubicFiniteShiftThinStripBudget K A B delta)
    hbound

/-- Receiver-facing form of the finite-shift gate for the conventional corrected HCF budget. -/
theorem criticalFeatureThinStripCorrectedLatticeBudget_le_of_eventually_finiteShift
    (K : Finset ℤ) (A B delta C : ℝ)
    (hbound : ∀ᶠ eps : ℂ in 𝓝[≠] 0,
      criticalFeatureXiWardCubicFiniteShiftThinStripBudget K eps A B delta ≤ C) :
    criticalFeatureThinStripCorrectedLatticeBudget K A B delta ≤ C := by
  rw [criticalFeatureThinStripCorrectedLatticeBudget_eq_poleGammaVM]
  exact criticalFeatureThinStripPoleGammaVMLatticeBudget_le_of_eventually_finiteShift
    K A B delta C hbound

/-! ## Uniform prime-channel elimination before the submicroscopic limit -/

/-- The logarithmically weighted von-Mangoldt series is uniformly bounded on the entire closed
half-plane to the right of the HCF safe line. -/
theorem norm_LSeries_logMul_vonMangoldt_of_threeHalves_le
    {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖LSeries (LSeries.logMul
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s‖ ≤
      ∑' n : ℕ, ‖LSeries.term
        (LSeries.logMul (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
        ((3 / 2 : ℝ) : ℂ) n‖ := by
  let f : ℕ → ℂ :=
    LSeries.logMul (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  have hsone : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  have habs : abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
    lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hsone)
  have hsum : LSeriesSummable f s := by
    simpa [f] using LSeriesSummable_logMul_of_lt_re habs
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    summable_norm_iff.mpr hsum
  have hbaseRe :
      abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) <
        (((3 / 2 : ℝ) : ℂ)).re := by
    have hone : (1 : ℝ) < 3 / 2 := by norm_num
    exact lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le
      (by exact_mod_cast hone)
  have hbaseSum : LSeriesSummable f ((3 / 2 : ℝ) : ℂ) := by
    simpa [f] using LSeriesSummable_logMul_of_lt_re hbaseRe
  have hbaseNorm : Summable
      (fun n : ℕ => ‖LSeries.term f ((3 / 2 : ℝ) : ℂ) n‖) :=
    summable_norm_iff.mpr hbaseSum
  calc
    ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := by
      rw [LSeries]
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ‖LSeries.term f ((3 / 2 : ℝ) : ℂ) n‖ := by
      apply hnorm.tsum_le_tsum _ hbaseNorm
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn, if_neg hn]
        apply div_le_div_of_nonneg_left (norm_nonneg _)
        · exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
        · apply Real.rpow_le_rpow_of_exponent_le
          · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          · simpa using hs
    _ = _ := by rfl

/-- Uniform derivative bound for the von-Mangoldt series on the same half-plane. -/
theorem norm_deriv_LSeries_vonMangoldt_of_threeHalves_le
    {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖deriv (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s‖ ≤
      ∑' n : ℕ, ‖LSeries.term
        (LSeries.logMul (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
        ((3 / 2 : ℝ) : ℂ) n‖ := by
  have hsone : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  have habs : abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
    lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hsone)
  rw [LSeries_deriv habs, norm_neg]
  exact norm_LSeries_logMul_vonMangoldt_of_threeHalves_le hs

/-- Every positive-real von-Mangoldt divided difference based on the HCF safe line is bounded by
the same logarithmically weighted absolute-convergence constant, uniformly in height and shift. -/
theorem norm_LSeries_vonMangoldt_positiveRealShiftQuotient_le
    (t eps : ℝ) (heps : 0 < eps) :
    ‖(LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (criticalFeatureEulerVMArchPoint t) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (criticalFeatureEulerVMArchPoint t + (eps : ℂ))) / (eps : ℂ)‖ ≤
      ∑' n : ℕ, ‖LSeries.term
        (LSeries.logMul (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
        ((3 / 2 : ℝ) : ℂ) n‖ := by
  let L : ℂ → ℂ :=
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  let z₀ : ℂ := criticalFeatureEulerVMArchPoint t
  let z₁ : ℂ := z₀ + (eps : ℂ)
  let M : ℝ := ∑' n : ℕ, ‖LSeries.term
    (LSeries.logMul (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
    ((3 / 2 : ℝ) : ℂ) n‖
  have hre (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      3 / 2 ≤ (z₀ + (u : ℂ) * (z₁ - z₀)).re := by
    rcases hu with ⟨hu0, hu1⟩
    simp [z₀, z₁, criticalFeatureEulerVMArchPoint]
    positivity
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      DifferentiableAt ℂ L (z₀ + (u : ℂ) * (z₁ - z₀)) := by
    have hone : 1 < (z₀ + (u : ℂ) * (z₁ - z₀)).re :=
      lt_of_lt_of_le (by norm_num) (hre u hu)
    exact (LSeries_hasDerivAt
      (lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le
        (by exact_mod_cast hone))).differentiableAt
  have hderiv (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      ‖deriv L (z₀ + (u : ℂ) * (z₁ - z₀))‖ ≤ M :=
    norm_deriv_LSeries_vonMangoldt_of_threeHalves_le (hre u hu)
  have hsegment := RHTower.Sieve.norm_sub_le_segment hdiff hderiv
  have hdist : ‖z₁ - z₀‖ = eps := by
    simp [z₁, abs_of_pos heps]
  have hquot : ‖(L z₀ - L z₁) / (eps : ℂ)‖ ≤ M := by
    rw [norm_div]
    rw [show ‖(eps : ℂ)‖ = eps by simp [abs_of_pos heps]]
    rw [div_le_iff₀ heps]
    rw [← hdist]
    rw [show ‖L z₀ - L z₁‖ = ‖L z₁ - L z₀‖ by
      rw [← norm_neg, neg_sub]]
    exact hsegment
  simpa [L, z₀, z₁, M] using hquot

/-- Von-Mangoldt part of the finite-displacement Robin jet. -/
def criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet
    (t eps : ℝ) : ℝ :=
  2 * (-LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (criticalFeatureEulerVMArchPoint t) -
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t) -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
            (criticalFeatureEulerVMArchPoint t + (eps : ℂ))) / (eps : ℂ)).re

/-- Pole--Gamma part of the same finite-displacement Robin jet. -/
def criticalFeatureXiWardCubicFiniteShiftPoleGammaJet
    (t eps : ℝ) : ℝ :=
  let s := criticalFeatureEulerVMArchPoint t
  2 * ((s⁻¹ + (s - 1)⁻¹ + logDeriv Gammaℝ s).re -
    ((((s + (eps : ℂ))⁻¹ - s⁻¹) +
        ((s + (eps : ℂ) - 1)⁻¹ - (s - 1)⁻¹) +
        (logDeriv Gammaℝ (s + (eps : ℂ)) - logDeriv Gammaℝ s)) /
      (eps : ℂ)).re)

/-- Exact finite-shift channel split before taking the submicroscopic limit. -/
theorem criticalFeatureXiWardCubicFiniteShiftRobinJet_eq_channels
    (t eps : ℝ) :
    criticalFeatureXiWardCubicFiniteShiftRobinJet t (eps : ℂ) =
      criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet t eps +
        criticalFeatureXiWardCubicFiniteShiftPoleGammaJet t eps := by
  rw [criticalFeatureXiWardCubicFiniteShiftRobinJet,
    criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet,
    criticalFeatureXiWardCubicFiniteShiftPoleGammaJet,
    xiWardCubicShiftArithmeticCovariance_eq_poleGamma_add_vonMangoldt]
  unfold xiWardCubicCompletedArithmeticCurrent
  simp only [sub_re, add_re, neg_re]
  ring

/-- Uniform pointwise bound for the finite-shift prime channel. -/
theorem abs_criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet_le
    (t eps : ℝ) (heps : 0 < eps) :
    |criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet t eps| ≤
      2 * criticalFeatureVonMangoldtUniformConstant := by
  let A :=
    (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (criticalFeatureEulerVMArchPoint t) -
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (criticalFeatureEulerVMArchPoint t + (eps : ℂ))) / (eps : ℂ)
  let B := LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    (criticalFeatureEulerVMArchPoint t)
  have hA := norm_LSeries_vonMangoldt_positiveRealShiftQuotient_le t eps heps
  have hB := norm_LSeries_vonMangoldt_criticalFeatureEulerVMArchPoint_le t
  change |2 * (-B - A).re| ≤ 2 * criticalFeatureVonMangoldtUniformConstant
  calc
    |2 * (-B - A).re| = 2 * |(-B - A).re| := by rw [abs_mul]; norm_num
    _ ≤ 2 * ‖-B - A‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ ≤ 2 * (‖B‖ + ‖A‖) := by
      gcongr
      simpa using norm_sub_le (-B) A
    _ ≤ 2 * criticalFeatureVonMangoldtUniformConstant := by
      dsimp [criticalFeatureVonMangoldtUniformConstant, A, B] at hA hB ⊢
      nlinarith

/-- Finite-shift von-Mangoldt channel summed over the HCF lattice. -/
def criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget
    (K : Finset ℤ) (eps : ℝ) : ℝ :=
  ∑ k ∈ K, criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet (k : ℝ) eps

/-- Finite-shift pole--Gamma channel summed over the HCF lattice. -/
def criticalFeatureXiWardCubicFiniteShiftPoleGammaLatticeBudget
    (K : Finset ℤ) (eps : ℝ) : ℝ :=
  ∑ k ∈ K, criticalFeatureXiWardCubicFiniteShiftPoleGammaJet (k : ℝ) eps

/-- The finite-shift lattice Robin budget splits exactly into prime and pole--Gamma channels. -/
theorem criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget_eq_channels
    (K : Finset ℤ) (eps : ℝ) :
    criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget K (eps : ℂ) =
      criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget K eps +
        criticalFeatureXiWardCubicFiniteShiftPoleGammaLatticeBudget K eps := by
  rw [criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget,
    criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget,
    criticalFeatureXiWardCubicFiniteShiftPoleGammaLatticeBudget,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact criticalFeatureXiWardCubicFiniteShiftRobinJet_eq_channels (k : ℝ) eps

/-- Uniform `O(card K)` bound for the prime channel, with no loss as the positive shift shrinks. -/
theorem abs_criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget_le
    (K : Finset ℤ) (eps : ℝ) (heps : 0 < eps) :
    |criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget K eps| ≤
      (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) := by
  rw [criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget]
  calc
    |∑ k ∈ K, criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet (k : ℝ) eps| ≤
        ∑ k ∈ K,
          |criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet (k : ℝ) eps| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ K, 2 * criticalFeatureVonMangoldtUniformConstant := by
      gcongr with k hk
      exact abs_criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet_le
        (k : ℝ) eps heps
    _ = (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) := by simp

/-- A positive real sequence converging to zero approaches the punctured complex origin.  This
lightweight sequential form avoids importing unrelated analytic infrastructure. -/
theorem tendsto_ofReal_positive_sequence_nhdsNE_zero
    (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n)
    (heps0 : Tendsto eps atTop (nhds 0)) :
    Tendsto (fun n => (eps n : ℂ)) atTop (𝓝[≠] 0) := by
  have hepsC : Tendsto (fun n => (eps n : ℂ)) atTop (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp heps0
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hepsC, Filter.Eventually.of_forall fun n => ?_⟩
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (heps n)))

/-- Along every positive submicroscopic schedule, the finite-shift prime jet converges to the
exact von-Mangoldt jet. -/
theorem tendsto_criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet
    (t : ℝ) (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n)
    (heps0 : Tendsto eps atTop (nhds 0)) :
    Tendsto
      (fun n => criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet t (eps n))
      atTop
      (nhds (2 *
        (-LSeries (LSeries.logMul
              (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)))
              (criticalFeatureEulerVMArchPoint t) -
          LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (criticalFeatureEulerVMArchPoint t)).re)) := by
  let L : ℂ → ℂ :=
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  let s : ℂ := criticalFeatureEulerVMArchPoint t
  have hs : 1 < s.re := by
    simp [s, criticalFeatureEulerVMArchPoint]
    norm_num
  have habs : abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < s.re :=
    lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hs)
  have hepsPunct := tendsto_ofReal_positive_sequence_nhdsNE_zero eps heps heps0
  have hslope := (LSeries_hasDerivAt habs).tendsto_slope_zero.comp hepsPunct
  have hslope' : Tendsto
      (fun n => (eps n : ℂ)⁻¹ * (L (s + (eps n : ℂ)) - L s))
      atTop (nhds (-LSeries (LSeries.logMul
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) s)) := by
    simpa only [Function.comp_def, smul_eq_mul, L] using hslope
  have hquot : Tendsto
      (fun n => (L s - L (s + (eps n : ℂ))) / (eps n : ℂ))
      atTop (nhds (LSeries (LSeries.logMul
        (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) s)) := by
    have hneg := hslope'.neg
    convert hneg using 1
    · funext n
      simp only [div_eq_mul_inv]
      ring
    · simp
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hquot
  have hconst : Tendsto (fun _ : ℕ => (-L s).re) atTop (nhds (-L s).re) :=
    tendsto_const_nhds
  have hcomb := (hconst.sub hre).const_mul (2 : ℝ)
  convert hcomb using 1
  · funext n
    simp [criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet, L, s]
  · simp [L, s]
    ring

/-- Finite lattice sums of the positive-shift prime channel converge to the existing exact prime
lattice budget. -/
theorem tendsto_criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget
    (K : Finset ℤ) (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n)
    (heps0 : Tendsto eps atTop (nhds 0)) :
    Tendsto
      (fun n => criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget K (eps n))
      atTop (nhds (criticalFeatureVonMangoldtLatticeBudget K)) := by
  rw [criticalFeatureVonMangoldtLatticeBudget]
  change Tendsto
    (fun n => ∑ k ∈ K,
      criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet (k : ℝ) (eps n))
    atTop
    (nhds (∑ k ∈ K, 2 *
      (-LSeries (LSeries.logMul
          (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)))
          (criticalFeatureEulerVMArchPoint (k : ℝ)) -
        LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (criticalFeatureEulerVMArchPoint (k : ℝ))).re))
  apply tendsto_finsetSum K
  intro k hk
  exact tendsto_criticalFeatureXiWardCubicFiniteShiftVonMangoldtJet
    (k : ℝ) eps heps heps0

/-- The finite-shift pole--Gamma lattice channel converges to the exact pole--Gamma lattice jet. -/
theorem tendsto_criticalFeatureXiWardCubicFiniteShiftPoleGammaLatticeBudget
    (K : Finset ℤ) (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n)
    (heps0 : Tendsto eps atTop (nhds 0)) :
    Tendsto
      (fun n => criticalFeatureXiWardCubicFiniteShiftPoleGammaLatticeBudget K (eps n))
      atTop (nhds (criticalFeaturePoleGammaLatticeBudget K)) := by
  have hfull :=
    (tendsto_criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget K).comp
      (tendsto_ofReal_positive_sequence_nhdsNE_zero eps heps heps0)
  have hprime :=
    tendsto_criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget
      K eps heps heps0
  have hdiff := hfull.sub hprime
  convert hdiff using 1
  · funext n
    simp only [Function.comp_apply]
    rw [criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget_eq_channels]
    ring
  · rw [criticalFeaturePoleGammaVMLatticeBudget_eq_channels]
    ring

/-- Pole--Gamma finite-shift lattice budget after the source-only line contour is removed. -/
def criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
    (K : Finset ℤ) (eps A B delta : ℝ) : ℝ :=
  criticalFeatureXiWardCubicFiniteShiftPoleGammaLatticeBudget K eps -
    criticalFeatureThinStripLineContourLattice K A B delta

/-- The source line contour is shift-independent, so the finite-shift pole--Gamma contour channel
lands on the exact HCF archimedean-contour budget. -/
theorem tendsto_criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
    (K : Finset ℤ) (eps : ℕ → ℝ) (A B delta : ℝ)
    (heps : ∀ n, 0 < eps n) (heps0 : Tendsto eps atTop (nhds 0)) :
    Tendsto
      (fun n => criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
        K (eps n) A B delta)
      atTop (nhds (criticalFeaturePoleGammaContourLatticeBudget K A B delta)) := by
  have harch := tendsto_criticalFeatureXiWardCubicFiniteShiftPoleGammaLatticeBudget
    K eps heps heps0
  have hcontour : Tendsto
      (fun _ : ℕ => criticalFeatureThinStripLineContourLattice K A B delta)
      atTop (nhds (criticalFeatureThinStripLineContourLattice K A B delta)) :=
    tendsto_const_nhds
  simpa only [criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget,
    criticalFeaturePoleGammaContourLatticeBudget] using harch.sub hcontour

/-- Any eventual upper bound for the explicit positive-shift pole--Gamma contour remainder passes
to the exact remainder. -/
theorem criticalFeaturePoleGammaContourLatticeBudget_le_of_eventually_finiteShift
    (K : Finset ℤ) (eps : ℕ → ℝ) (A B delta C : ℝ)
    (heps : ∀ n, 0 < eps n) (heps0 : Tendsto eps atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop,
      criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
        K (eps n) A B delta ≤ C) :
    criticalFeaturePoleGammaContourLatticeBudget K A B delta ≤ C :=
  le_of_tendsto
    (tendsto_criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
      K eps A B delta heps heps0)
    hbound

/-- Receiver-facing finite-shift pole--Gamma gate.  The only loss is the explicit `O(card K)`
prime constant, already negligible on canonical HCF windows. -/
theorem criticalFeatureThinStripPoleGammaVMLatticeBudget_le_of_eventually_finiteShiftPoleGamma
    (K : Finset ℤ) (eps : ℕ → ℝ) (A B delta C : ℝ)
    (heps : ∀ n, 0 < eps n) (heps0 : Tendsto eps atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop,
      criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
        K (eps n) A B delta ≤ C) :
    criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta ≤
      C + (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) := by
  have harch : criticalFeaturePoleGammaContourLatticeBudget K A B delta ≤ C :=
    criticalFeaturePoleGammaContourLatticeBudget_le_of_eventually_finiteShift
      K eps A B delta C heps heps0 hbound
  have hprime := abs_criticalFeatureVonMangoldtLatticeBudget_le K
  have hprimeUpper : criticalFeatureVonMangoldtLatticeBudget K ≤
      (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) :=
    (le_abs_self _).trans hprime
  rw [criticalFeatureThinStripPoleGammaVMLatticeBudget_eq_prime_add_archContour]
  linarith

/-- If the standard thin-strip source majorant is available, the finite-shift pole--Gamma bound
controls the actual off-line HCF lattice budget with the same lower-order prime correction. -/
theorem criticalFeaturePrimeGammaOffLineLatticeBudget_le_of_eventually_finiteShiftPoleGamma
    (K : Finset ℤ) (eps : ℕ → ℝ) (A B delta C : ℝ)
    (hmajor : criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      criticalFeatureThinStripPoleGammaVMLatticeBudget K A B delta)
    (heps : ∀ n, 0 < eps n) (heps0 : Tendsto eps atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop,
      criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
        K (eps n) A B delta ≤ C) :
    criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      C + (K.card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) :=
  hmajor.trans
    (criticalFeatureThinStripPoleGammaVMLatticeBudget_le_of_eventually_finiteShiftPoleGamma
      K eps A B delta C heps heps0 hbound)

/-- Exact corrected finite-shift split.  The prime term is uniformly lower-order; every possible
leading contribution is confined to the pole--Gamma divided difference minus line contour. -/
theorem criticalFeatureXiWardCubicFiniteShiftThinStripBudget_eq_channels
    (K : Finset ℤ) (eps A B delta : ℝ) :
    criticalFeatureXiWardCubicFiniteShiftThinStripBudget
        K (eps : ℂ) A B delta =
      criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget K eps +
        criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
          K eps A B delta := by
  rw [criticalFeatureXiWardCubicFiniteShiftThinStripBudget,
    Finset.sum_sub_distrib]
  change criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget K (eps : ℂ) -
      (∑ k ∈ K,
        (criticalFeatureThinStripSourceContour (k : ℝ) A B delta).re) = _
  rw [criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget_eq_channels,
    criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget,
    criticalFeatureThinStripLineContourLattice]
  ring

/-- Uniform submicroscopic prime elimination: for any positive shift schedule, a sublinear lattice
makes the normalized finite-shift corrected budget and its pole--Gamma contour channel agree up to
`o(N)`. -/
theorem tendsto_criticalFeatureXiWardCubicFiniteShiftThinStrip_sub_poleGammaContour_div
    (K : ℕ → Finset ℤ) (eps N A B delta : ℕ → ℝ)
    (heps : ∀ n, 0 < eps n)
    (hN : ∀ᶠ n in atTop, 0 < N n)
    (hcard : Tendsto (fun n => ((K n).card : ℝ) / N n) atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (criticalFeatureXiWardCubicFiniteShiftThinStripBudget
            (K n) (eps n : ℂ) (A n) (B n) (delta n) -
          criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
            (K n) (eps n) (A n) (B n) (delta n)) / N n)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmajor : Tendsto
      (fun n => ((K n).card : ℝ) / N n *
        (2 * criticalFeatureVonMangoldtUniformConstant)) atTop (nhds 0) := by
    simpa using hcard.mul_const (2 * criticalFeatureVonMangoldtUniformConstant)
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hmajor
  filter_upwards [hN] with n hn
  rw [criticalFeatureXiWardCubicFiniteShiftThinStripBudget_eq_channels]
  rw [show
    criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget (K n) (eps n) +
          criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
            (K n) (eps n) (A n) (B n) (delta n) -
        criticalFeatureXiWardCubicFiniteShiftPoleGammaContourLatticeBudget
            (K n) (eps n) (A n) (B n) (delta n) =
      criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget (K n) (eps n) by ring]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
  calc
    |criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget (K n) (eps n)| /
          N n ≤
        ((K n).card : ℝ) * (2 * criticalFeatureVonMangoldtUniformConstant) / N n :=
      (div_le_div_iff_of_pos_right hn).2
        (abs_criticalFeatureXiWardCubicFiniteShiftVonMangoldtLatticeBudget_le
          (K n) (eps n) (heps n))
    _ = ((K n).card : ℝ) / N n *
        (2 * criticalFeatureVonMangoldtUniformConstant) := by ring

end

end RHTower
