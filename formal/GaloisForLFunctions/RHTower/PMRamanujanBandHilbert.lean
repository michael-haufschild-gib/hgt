import GaloisForLFunctions.RHTower.PMRamanujanBandMellin
import GaloisForLFunctions.RHTower.StepFunctionCarrier
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel
import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge

/-!
# Complete Ramanujan-band Hilbert and Mellin energy

The literal logarithmic source lies in L1 and L2. Its squared Hilbert norm
is exactly the original reciprocal-weight energy of the complete band.
The complete critical Mellin trace is its rescaled Fourier transform.
Every L2 frequency test is a bounded literal integral pairing against this
trace, with no unknown energy estimate among the hypotheses.

Uniform control as the natural cutoff grows remains open.
-/

open MeasureTheory Set Complex Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

private def pmbh_bound (ε : ℝ) (X Y : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc X Y, ‖pmPowerDampedRamanujanWeight ε q‖ * pmRamanujanPrimitiveBound q

private theorem pmbh_band_norm (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) (N : ℕ) :
    ‖pmRamanujanDenominatorBand ε X Y N‖ ≤ pmbh_bound ε X Y := by
  unfold pmRamanujanDenominatorBand pmbh_bound
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_pmRamanujanPrimitive_le (lt_of_le_of_lt hX (Finset.mem_Ioc.mp hq).1) N)
    (norm_nonneg _)

/-- The actual complete band in the critical logarithmic spatial coordinate. -/
def pmRamanujanBandLogSource (ε : ℝ) (X Y : ℕ) (u : ℝ) : ℂ :=
  Real.exp (-(1/2 : ℝ)*u) • pmRamanujanDenominatorBand ε X Y ⌊Real.exp u⌋₊

theorem pmRamanujanBandLogSource_eq_logMellinLineSource (ε : ℝ) (X Y : ℕ) :
    pmRamanujanBandLogSource ε X Y =
      logMellinLineSource (pmRamanujanDenominatorBandSource ε X Y) (1/2) := by
  funext u
  simp only [pmRamanujanBandLogSource, logMellinLineSource,
    pmRamanujanDenominatorBandSource, Real.exp_neg, one_div, inv_inv]

theorem measurable_pmRamanujanBandLogSource (ε : ℝ) (X Y : ℕ) :
    Measurable (pmRamanujanBandLogSource ε X Y) := by
  have hf : Measurable (fun u : ℝ => Real.exp (-(1/2 : ℝ)*u)) := by fun_prop
  have hg : Measurable (fun u : ℝ => pmRamanujanDenominatorBand ε X Y ⌊Real.exp u⌋₊) :=
    (measurable_of_countable (pmRamanujanDenominatorBand ε X Y)).comp
      Real.measurable_exp.nat_floor
  exact hf.smul hg

theorem pmRamanujanBandLogSource_zero_of_neg (ε : ℝ) (X Y : ℕ) {u : ℝ}
    (hu : u < 0) : pmRamanujanBandLogSource ε X Y u = 0 := by
  simp [pmRamanujanBandLogSource, Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hu),
    pmRamanujanDenominatorBand, pmRamanujanPrimitive]

private theorem pmbh_log_norm (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) (u : ℝ) :
    ‖pmRamanujanBandLogSource ε X Y u‖ ≤
      pmbh_bound ε X Y * Real.exp (-(1/2 : ℝ)*u) := by
  rw [pmRamanujanBandLogSource, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (pmbh_band_norm ε hX _) (Real.exp_pos _).le).trans_eq
    (mul_comm _ _)

theorem integrable_pmRamanujanBandLogSource (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) :
    Integrable (pmRamanujanBandLogSource ε X Y) := by
  have hm := measurable_pmRamanujanBandLogSource ε X Y
  have he : IntegrableOn (fun u : ℝ => Real.exp (-(1/2 : ℝ)*u)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by norm_num) 0
  have hi : IntegrableOn (pmRamanujanBandLogSource ε X Y) (Ici 0) := by
    refine (he.const_mul (pmbh_bound ε X Y)).mono' hm.aestronglyMeasurable.restrict ?_
    exact Filter.Eventually.of_forall (pmbh_log_norm ε hX)
  have hh := (integrable_indicator_iff measurableSet_Ici).mpr hi
  have hfun : (Ici (0 : ℝ)).indicator (pmRamanujanBandLogSource ε X Y) =
      pmRamanujanBandLogSource ε X Y := by
    funext u
    by_cases hu : u ∈ Ici (0 : ℝ)
    · exact Set.indicator_of_mem hu _
    · rw [Set.indicator_of_notMem hu, pmRamanujanBandLogSource_zero_of_neg ε X Y
        (lt_of_not_ge hu)]
  rwa [hfun] at hh

theorem memLp_pmRamanujanBandLogSource (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) :
    MemLp (pmRamanujanBandLogSource ε X Y) 2 volume := by
  have hm := measurable_pmRamanujanBandLogSource ε X Y
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have he : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [neg_one_mul] using (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0)
  have hi : IntegrableOn (fun u => ‖pmRamanujanBandLogSource ε X Y u‖^2) (Ici 0) := by
    refine (he.const_mul ((pmbh_bound ε X Y)^2)).mono' (by fun_prop) ?_
    refine Filter.Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp : Real.exp (-(1/2 : ℝ)*u)^2 = Real.exp (-u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ (pmbh_bound ε X Y * Real.exp (-(1/2 : ℝ)*u))^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (pmbh_log_norm ε hX u) 2
      _ = _ := by rw [mul_pow, hp]
  have hh := (integrable_indicator_iff measurableSet_Ici).mpr hi
  have hfun : (Ici (0 : ℝ)).indicator
      (fun u => ‖pmRamanujanBandLogSource ε X Y u‖^2) =
      (fun u => ‖pmRamanujanBandLogSource ε X Y u‖^2) := by
    funext u
    by_cases hu : u ∈ Ici (0 : ℝ)
    · exact Set.indicator_of_mem hu _
    · simp only [Set.indicator_of_notMem hu,
        pmRamanujanBandLogSource_zero_of_neg ε X Y (lt_of_not_ge hu), norm_zero, zero_pow
          (by norm_num : (2 : ℕ) ≠ 0)]
  rwa [hfun] at hh

/-- The complete critical-line Mellin trace; all natural denominators remain present. -/
def pmRamanujanBandMellinTrace (ε : ℝ) (X Y : ℕ) (τ : ℝ) : ℂ :=
  let s : ℂ := (1/2 : ℂ)+(τ : ℂ)*I
  riemannZeta s/s * ∑ q ∈ Finset.Ioc X Y,
    pmPowerDampedRamanujanWeight ε q * pmRamanujanMellinSymbol q s

theorem pmRamanujanBandMellinTrace_eq_mellin (ε : ℝ) {X Y : ℕ}
    (hX : 1 ≤ X) (τ : ℝ) :
    pmRamanujanBandMellinTrace ε X Y τ =
      mellin (pmRamanujanDenominatorBandSource ε X Y) ((1/2 : ℂ)+(τ : ℂ)*I) := by
  exact (hasMellin_pmRamanujanDenominatorBandSource ε hX
    (by norm_num) (by norm_num)).2.symm

theorem pmRamanujanBandMellinTrace_eq_fourier (ε : ℝ) {X Y : ℕ}
    (hX : 1 ≤ X) (τ : ℝ) :
    pmRamanujanBandMellinTrace ε X Y τ =
      FourierTransform.fourier (pmRamanujanBandLogSource ε X Y) (τ/(2*Real.pi)) := by
  rw [pmRamanujanBandMellinTrace_eq_mellin ε hX,
    pmRamanujanBandLogSource_eq_logMellinLineSource]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    (mellin_line_eq_fourier_logMellinLineSource
      (pmRamanujanDenominatorBandSource ε X Y) (1/2) τ)

theorem integral_norm_sq_pmRamanujanBandMellinTrace (ε : ℝ) {X Y : ℕ}
    (hX : 1 ≤ X) :
    (∫ τ : ℝ, ‖pmRamanujanBandMellinTrace ε X Y τ‖^2) =
      2*Real.pi * ∫ u : ℝ, ‖pmRamanujanBandLogSource ε X Y u‖^2 := by
  have h1 := integrable_pmRamanujanBandLogSource ε hX (Y := Y)
  have h2 := memLp_pmRamanujanBandLogSource ε hX (Y := Y)
  rw [pmRamanujanBandLogSource_eq_logMellinLineSource] at h1 h2 ⊢
  have ht := integral_norm_sq_mellin_line_eq_logMellinLineSource h1 h2
  simpa only [pmRamanujanBandMellinTrace_eq_mellin ε hX, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using ht

private theorem pmbh_integral_log_energy (ε : ℝ) (X Y : ℕ) :
    (∫ u : ℝ, ‖pmRamanujanBandLogSource ε X Y u‖^2) =
      ∫ x in Ioi (0 : ℝ), ‖pmRamanujanDenominatorBand ε X Y ⌊x⌋₊‖^2 * (x⁻¹)^2 := by
  symm
  rw [← Real.range_exp, ← Set.image_univ]
  rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with u
  have he : Real.exp (-(1/2 : ℝ)*u)^2 = (Real.exp u)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    ring
  simp only [smul_eq_mul, pmRamanujanBandLogSource,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, he]
  have hu := (Real.exp_pos u).ne'
  field_simp

private theorem pmbh_integral_energy_tail (ε : ℝ) (X Y : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖pmRamanujanDenominatorBand ε X Y ⌊x⌋₊‖^2 * (x⁻¹)^2) =
      ∫ x in Ioi (1 : ℝ), ‖pmRamanujanDenominatorBand ε X Y ⌊x⌋₊‖^2 * (x⁻¹)^2 := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 1 := by
    rw [Filter.eventually_iff, mem_ae_iff]
    simp
  filter_upwards [hne] with x hx
  by_cases hx1 : 1 < x
  · simp [hx1, show (0 : ℝ) < x by linarith]
  · have hxlt : x < 1 := lt_of_le_of_ne (le_of_not_gt hx1) hx
    have hzero : pmRamanujanDenominatorBand ε X Y ⌊x⌋₊ = 0 := by
      simp [Nat.floor_eq_zero.mpr hxlt, pmRamanujanDenominatorBand, pmRamanujanPrimitive]
    by_cases hx0 : 0 < x <;> simp [hx0, hx1, hzero]

/-- Exact complete-band energy in the logarithmic Hilbert coordinate. -/
theorem hasSum_pmRamanujanBandLogSource_energy (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) :
    HasSum (fun n : ℕ => ‖pmRamanujanDenominatorBand ε X Y (n+1)‖^2 /
      (((n : ℝ)+1)*((n : ℝ)+2)))
      (∫ u : ℝ, ‖pmRamanujanBandLogSource ε X Y u‖^2) := by
  let S := pmRamanujanDenominatorBand ε X Y
  have hr (n : ℕ) : |(S n).re| ≤ pmbh_bound ε X Y :=
    (Complex.abs_re_le_norm _).trans (pmbh_band_norm ε hX n)
  have hi (n : ℕ) : |(S n).im| ≤ pmbh_bound ε X Y :=
    (Complex.abs_im_le_norm _).trans (pmbh_band_norm ε hX n)
  have hsum := (hasSum_stepGram hr hr).add (hasSum_stepGram hi hi)
  have hp (x : ℝ) : ‖S ⌊x⌋₊‖^2*(x⁻¹)^2 =
      (S ⌊x⌋₊).re*(S ⌊x⌋₊).re*(x⁻¹)^2 +
      (S ⌊x⌋₊).im*(S ⌊x⌋₊).im*(x⁻¹)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have he : (∫ u : ℝ, ‖pmRamanujanBandLogSource ε X Y u‖^2) =
      stepGram (fun n => (S n).re) (fun n => (S n).re) +
      stepGram (fun n => (S n).im) (fun n => (S n).im) := by
    rw [pmbh_integral_log_energy, pmbh_integral_energy_tail]
    change (∫ x in Ioi (1 : ℝ), ‖S ⌊x⌋₊‖^2*(x⁻¹)^2) = _
    simp_rw [hp]
    exact integral_add (integrableOn_stepGramIntegrand hr hr)
      (integrableOn_stepGramIntegrand hi hi)
  rw [he]
  convert hsum using 1
  funext n
  rw [Complex.sq_norm, Complex.normSq_apply]
  dsimp [S]
  ring

theorem integral_norm_sq_pmRamanujanBandLogSource_eq_tsum (ε : ℝ) {X Y : ℕ}
    (hX : 1 ≤ X) :
    (∫ u : ℝ, ‖pmRamanujanBandLogSource ε X Y u‖^2) =
      ∑' n : ℕ, ‖pmRamanujanDenominatorBand ε X Y (n+1)‖^2 /
        (((n : ℝ)+1)*((n : ℝ)+2)) :=
  (hasSum_pmRamanujanBandLogSource_energy ε hX).tsum_eq.symm

theorem continuous_pmRamanujanBandMellinTrace (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) :
    Continuous (pmRamanujanBandMellinTrace ε X Y) := by
  have hc : Continuous (FourierTransform.fourier (pmRamanujanBandLogSource ε X Y)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_pmRamanujanBandLogSource ε hX)
  change Continuous (fun τ : ℝ => pmRamanujanBandMellinTrace ε X Y τ)
  simp_rw [pmRamanujanBandMellinTrace_eq_fourier ε hX]
  exact hc.comp (by fun_prop)

theorem memLp_pmRamanujanBandMellinTrace (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) :
    MemLp (pmRamanujanBandMellinTrace ε X Y) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (continuous_pmRamanujanBandMellinTrace ε hX).aestronglyMeasurable).mpr
  have h1 := integrable_pmRamanujanBandLogSource ε hX (Y := Y)
  have h2 := memLp_pmRamanujanBandLogSource ε hX (Y := Y)
  rw [pmRamanujanBandLogSource_eq_logMellinLineSource] at h1 h2
  have ht := integrable_norm_sq_mellin_line_of_logMellinLineSource h1 h2
  simpa only [pmRamanujanBandMellinTrace_eq_mellin ε hX, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using ht

/-- The literal logarithmic band as a Hilbert vector. -/
def pmRamanujanBandLogVector (ε : ℝ) (X Y : ℕ) (hX : 1 ≤ X) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_pmRamanujanBandLogSource ε hX).toLp (pmRamanujanBandLogSource ε X Y)

/-- The complete critical Mellin trace as a Hilbert vector. -/
def pmRamanujanBandMellinVector (ε : ℝ) (X Y : ℕ) (hX : 1 ≤ X) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_pmRamanujanBandMellinTrace ε hX).toLp (pmRamanujanBandMellinTrace ε X Y)

theorem norm_sq_pmRamanujanBandLogVector (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) :
    ‖pmRamanujanBandLogVector ε X Y hX‖^2 =
      ∫ u : ℝ, ‖pmRamanujanBandLogSource ε X Y u‖^2 := by
  rw [GaloisForLFunctions.HTGeometry.Lp_two_norm_sq_eq_integral]
  exact integral_congr_ae ((memLp_pmRamanujanBandLogSource ε hX).coeFn_toLp.fun_comp
    (fun z : ℂ => ‖z‖^2))

theorem norm_sq_pmRamanujanBandLogVector_eq_energy (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) :
    ‖pmRamanujanBandLogVector ε X Y hX‖^2 =
      ∑' n : ℕ, ‖pmRamanujanDenominatorBand ε X Y (n+1)‖^2 /
        (((n : ℝ)+1)*((n : ℝ)+2)) := by
  rw [norm_sq_pmRamanujanBandLogVector, integral_norm_sq_pmRamanujanBandLogSource_eq_tsum ε hX]

theorem norm_sq_pmRamanujanBandMellinVector (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X) :
    ‖pmRamanujanBandMellinVector ε X Y hX‖^2 =
      2*Real.pi*‖pmRamanujanBandLogVector ε X Y hX‖^2 := by
  rw [GaloisForLFunctions.HTGeometry.Lp_two_norm_sq_eq_integral,
    norm_sq_pmRamanujanBandLogVector]
  calc
    _ = ∫ τ : ℝ, ‖pmRamanujanBandMellinTrace ε X Y τ‖^2 :=
      integral_congr_ae ((memLp_pmRamanujanBandMellinTrace ε hX).coeFn_toLp.fun_comp
        (fun z : ℂ => ‖z‖^2))
    _ = _ := integral_norm_sq_pmRamanujanBandMellinTrace ε hX

theorem integrable_pmRamanujanBandMellinTrace_pair (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X)
    (h : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (fun τ : ℝ => (starRingEnd ℂ) (h τ) * pmRamanujanBandMellinTrace ε X Y τ) := by
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) h (pmRamanujanBandMellinVector ε X Y hX)
  apply hi.congr
  filter_upwards [(memLp_pmRamanujanBandMellinTrace ε hX).coeFn_toLp] with τ hτ
  change (pmRamanujanBandMellinVector ε X Y hX : ℝ → ℂ) τ = _ at hτ
  rw [hτ]
  simp [RCLike.inner_apply, mul_comm]

theorem inner_pmRamanujanBandMellinVector (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X)
    (h : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ h (pmRamanujanBandMellinVector ε X Y hX) =
      ∫ τ : ℝ, (starRingEnd ℂ) (h τ) * pmRamanujanBandMellinTrace ε X Y τ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_pmRamanujanBandMellinTrace ε hX).coeFn_toLp] with τ hτ
  change (pmRamanujanBandMellinVector ε X Y hX : ℝ → ℂ) τ = _ at hτ
  rw [hτ]
  simp [RCLike.inner_apply, mul_comm]

/-- Every L2 frequency test is bounded by the original complete signed band energy. -/
theorem norm_sq_pmRamanujanBandMellinTrace_pair_le (ε : ℝ) {X Y : ℕ} (hX : 1 ≤ X)
    (h : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖∫ τ : ℝ, (starRingEnd ℂ) (h τ) * pmRamanujanBandMellinTrace ε X Y τ‖^2 ≤
      2*Real.pi*‖h‖^2 *
        ∑' n : ℕ, ‖pmRamanujanDenominatorBand ε X Y (n+1)‖^2 /
          (((n : ℝ)+1)*((n : ℝ)+2)) := by
  rw [← inner_pmRamanujanBandMellinVector ε hX h]
  calc
    _ ≤ (‖h‖*‖pmRamanujanBandMellinVector ε X Y hX‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    _ = _ := by
      rw [mul_pow, norm_sq_pmRamanujanBandMellinVector,
        norm_sq_pmRamanujanBandLogVector_eq_energy ε hX]
      ring

end RHTower
