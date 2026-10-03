import GaloisForLFunctions.RHTower.PMRamanujanBandEulerCorrection
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A positive compact test of the complete band residue

Beside every actual critical zeta zero, the complete cleared numerator is
continuous and nonzero on a short interval. Its literal compact restriction
is an L2 test with a positive frequency gap and strictly positive integrable
pairing against that full numerator. No zero-simplicity assumption is used.
This does not continue the actual moving-band transform or bound its energy.
-/

open MeasureTheory Set Complex Filter Topology
noncomputable section
namespace RHTower

/-- The literal cleared numerator at a critical zero, retaining every arithmetic factor. -/
def pmRamanujanBandResidueNumerator (ε : ℝ) (ρ : ℂ) (τ : ℝ) : ℂ :=
  let s : ℂ := (1/2 : ℂ)+(τ : ℂ)*I
  let r := (ε : ℂ)+s-ρ
  pmPowerDampedDivisorDensity ε * (riemannZeta s/s) *
    ((1-(2 : ℂ)^(-r))/r) * riemannZeta (1+ρ-s) * pmRamanujanBandEulerCorrection ε ρ s

private theorem pmbr_bandFactor_ne_zero {r : ℂ} (hr : 0 < r.re) :
    (1-(2 : ℂ)^(-r))/r ≠ 0 := by
  have hr0 : r ≠ 0 := by
    intro he
    simp [he] at hr
  apply div_ne_zero _ hr0
  intro he
  have hp : (2 : ℂ)^(-r) = 1 := (sub_eq_zero.mp he).symm
  have hn : ‖(2 : ℂ)^(-r)‖ < 1 := by
    change ‖((2 : ℝ) : ℂ)^(-r)‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hr)
  simp [hp] at hn

theorem pmRamanujanBandResidueNumerator_ne_zero {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hρ : ρ.re = 1/2) (τ : ℝ)
    (hζ : riemannZeta ((1/2 : ℂ)+(τ : ℂ)*I) ≠ 0)
    (hH : pmRamanujanBandEulerCorrection ε ρ ((1/2 : ℂ)+(τ : ℂ)*I) ≠ 0) :
    pmRamanujanBandResidueNumerator ε ρ τ ≠ 0 := by
  have hα : pmPowerDampedDivisorDensity ε ≠ 0 := by
    intro he
    have hp := pmPowerDampedDivisorDensity_re_pos hε
    simp [he] at hp
  have hs0 : (1/2 : ℂ)+(τ : ℂ)*I ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    norm_num at this
  have hr : 0 < ((ε : ℂ)+((1/2 : ℂ)+(τ : ℂ)*I)-ρ).re := by
    simpa [hρ] using hε
  have hζ1 : riemannZeta (1+ρ-((1/2 : ℂ)+(τ : ℂ)*I)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [hρ])
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hα (div_ne_zero hζ hs0))
    (pmbr_bandFactor_ne_zero hr)) hζ1) hH

/-- A full punctured interval beside every actual critical zero retains a nonzero numerator. -/
theorem exists_pmRamanujanBandResidueNumerator_ne_zero_interval {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hρ : ρ.re = 1/2) (hzero : riemannZeta ρ = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ τ ∈ Ioo ρ.im (ρ.im+R),
      pmRamanujanBandResidueNumerator ε ρ τ ≠ 0 := by
  let s : ℝ → ℂ := fun τ => (1/2 : ℂ)+(τ : ℂ)*I
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hsρ : s ρ.im = ρ := by apply Complex.ext <;> simp [s, hρ]
  obtain ⟨U,hU,hUeq⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    isDiscrete_riemannZetaZeros ρ hzero
  have hρU : ρ ∈ U := by
    have hm : ρ ∈ U ∩ riemannZetaZeros := by rw [hUeq]; simp
    exact hm.1
  have ht : Tendsto s (𝓝 ρ.im) (𝓝 ρ) := by simpa [hsρ] using hs.tendsto ρ.im
  have hu : ∀ᶠ τ in 𝓝 ρ.im, s τ ∈ U := ht.eventually (hU.mem_nhds hρU)
  have htp : Tendsto (fun τ => (ρ,s τ)) (𝓝 ρ.im) (𝓝 (ρ,ρ)) :=
    tendsto_const_nhds.prodMk_nhds ht
  have hh := htp.eventually (eventually_ne_zero_pmRamanujanBandEulerCorrection hε.le hρ)
  obtain ⟨R,hR,hnear⟩ := Metric.eventually_nhds_iff.mp (hu.and hh)
  refine ⟨R,hR,?_⟩
  intro τ hτ
  have hdist : dist τ ρ.im < R := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hτ.1)]
    linarith [hτ.2]
  obtain ⟨hτU,hτH⟩ := hnear hdist
  apply pmRamanujanBandResidueNumerator_ne_zero hε hρ τ _ hτH
  intro hz
  have hm : s τ ∈ U ∩ riemannZetaZeros := ⟨hτU,hz⟩
  rw [hUeq, Set.mem_singleton_iff] at hm
  have him := congrArg Complex.im hm
  have htγ : τ = ρ.im := by simpa [s] using him
  exact (ne_of_gt hτ.1) htγ

theorem continuousAt_pmRamanujanBandResidueNumerator {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hρ : ρ.re = 1/2) {τ : ℝ} (hτ : τ ≠ ρ.im) :
    ContinuousAt (pmRamanujanBandResidueNumerator ε ρ) τ := by
  let s : ℝ → ℂ := fun t => (1/2 : ℂ)+(t : ℂ)*I
  let r : ℝ → ℂ := fun t => (ε : ℂ)+s t-ρ
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hs0 : s τ ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num [s] at hh
  have hs1 : s τ ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num [s] at hh
  have hr0 : r τ ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    have he0 : ε = 0 := by simpa [r,s,hρ] using hh
    exact hε.ne' he0
  have hz1 : 1+ρ-s τ ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp [s] at hh
    apply hτ
    linarith
  have hζs : ContinuousAt (fun t => riemannZeta (s t)) τ :=
    (differentiableAt_riemannZeta hs1).continuousAt.comp hs.continuousAt
  have hζ1 : ContinuousAt (fun t => riemannZeta (1+ρ-s t)) τ :=
    (differentiableAt_riemannZeta hz1).continuousAt.comp (f := fun t : ℝ => 1+ρ-s t)
      (by fun_prop : ContinuousAt (fun t => 1+ρ-s t) τ)
  have hn : Continuous (fun t => 1-(2 : ℂ)^(-r t)) := by fun_prop
  have hmem : (ρ,s τ) ∈ pmRamanujanBandEulerDomain := by
    dsimp [pmRamanujanBandEulerDomain,s]
    rw [hρ]
    norm_num
  have hcH := (continuousOn_pmRamanujanBandEulerCorrection hε.le).continuousAt
    (isOpen_pmRamanujanBandEulerDomain.mem_nhds hmem)
  have hH : ContinuousAt (fun t => pmRamanujanBandEulerCorrection ε ρ (s t)) τ :=
    hcH.comp (f := fun t : ℝ => (ρ,s t)) (continuousAt_const.prodMk hs.continuousAt)
  change ContinuousAt (fun t => pmPowerDampedDivisorDensity ε * (riemannZeta (s t)/s t) *
    ((1-(2 : ℂ)^(-r t))/r t) * riemannZeta (1+ρ-s t) *
      pmRamanujanBandEulerCorrection ε ρ (s t)) τ
  exact (((continuousAt_const.mul (hζs.div hs.continuousAt hs0)).mul
    (hn.continuousAt.div hr.continuousAt hr0)).mul hζ1).mul hH

/-- The literal compact frequency test, retaining the full complex numerator. -/
def pmRamanujanBandResidueTest (ε : ℝ) (ρ : ℂ) (a b : ℝ) : ℝ → ℂ :=
  (Icc a b).indicator (pmRamanujanBandResidueNumerator ε ρ)

private theorem pmbr_continuousOn {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hρ : ρ.re = 1/2) {a b : ℝ} (ha : ρ.im < a) :
    ContinuousOn (pmRamanujanBandResidueNumerator ε ρ) (Icc a b) := by
  intro τ hτ
  exact (continuousAt_pmRamanujanBandResidueNumerator hε hρ
    (ne_of_gt (ha.trans_le hτ.1))).continuousWithinAt

theorem memLp_pmRamanujanBandResidueTest {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hρ : ρ.re = 1/2) {a b : ℝ} (ha : ρ.im < a) :
    MemLp (pmRamanujanBandResidueTest ε ρ a b) 2 volume := by
  rw [pmRamanujanBandResidueTest, memLp_indicator_iff_restrict measurableSet_Icc]
  have hc := pmbr_continuousOn hε hρ (b := b) ha
  apply (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable measurableSet_Icc)).mpr
  exact (hc.norm.pow 2).integrableOn_Icc

private theorem pmbr_pair_eq_indicator (ε : ℝ) (ρ : ℂ) (a b τ : ℝ) :
    (starRingEnd ℂ) (pmRamanujanBandResidueTest ε ρ a b τ) *
      pmRamanujanBandResidueNumerator ε ρ τ =
      (Icc a b).indicator
        (fun t => ((‖pmRamanujanBandResidueNumerator ε ρ t‖^2 : ℝ) : ℂ)) τ := by
  by_cases hτ : τ ∈ Icc a b
  · simp only [pmRamanujanBandResidueTest, Set.indicator_of_mem hτ,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  · simp [pmRamanujanBandResidueTest, Set.indicator_of_notMem hτ]

theorem integrable_pmRamanujanBandResidueTest_pair {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hρ : ρ.re = 1/2) {a b : ℝ} (ha : ρ.im < a) :
    Integrable (fun τ : ℝ => (starRingEnd ℂ) (pmRamanujanBandResidueTest ε ρ a b τ) *
      pmRamanujanBandResidueNumerator ε ρ τ) := by
  have hc := pmbr_continuousOn hε hρ (b := b) ha
  have hi : IntegrableOn (fun τ : ℝ =>
      ((‖pmRamanujanBandResidueNumerator ε ρ τ‖^2 : ℝ) : ℂ)) (Icc a b) :=
    ((hc.norm.pow 2).integrableOn_Icc (μ := volume)).ofReal
  have hg := (integrable_indicator_iff measurableSet_Icc).mpr hi
  exact hg.congr (.of_forall fun τ => (pmbr_pair_eq_indicator ε ρ a b τ).symm)

theorem integral_pmRamanujanBandResidueTest_pair (ε : ℝ) (ρ : ℂ) (a b : ℝ) :
    (∫ τ : ℝ, (starRingEnd ℂ) (pmRamanujanBandResidueTest ε ρ a b τ) *
      pmRamanujanBandResidueNumerator ε ρ τ) =
      ((∫ τ in Icc a b, ‖pmRamanujanBandResidueNumerator ε ρ τ‖^2 : ℝ) : ℂ) := by
  simp_rw [pmbr_pair_eq_indicator]
  rw [integral_indicator measurableSet_Icc]
  exact integral_ofReal

/-- An actual bounded L2 test sees a strictly positive complete critical numerator. -/
theorem exists_pmRamanujanBandResidue_positive_L2_test {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hρ : ρ.re = 1/2) (hzero : riemannZeta ρ = 0) :
    ∃ a b : ℝ, ρ.im < a ∧ a < b ∧ ∃ h : Lp ℂ 2 (volume : Measure ℝ),
      (h : ℝ → ℂ) =ᵐ[volume] pmRamanujanBandResidueTest ε ρ a b ∧
      (∀ᵐ τ : ℝ, h τ ≠ 0 → a-ρ.im ≤ |ρ.im-τ|) ∧
      Integrable (fun τ : ℝ => (starRingEnd ℂ) (h τ) *
        pmRamanujanBandResidueNumerator ε ρ τ) ∧
      0 < (∫ τ : ℝ, (starRingEnd ℂ) (h τ) *
        pmRamanujanBandResidueNumerator ε ρ τ).re := by
  obtain ⟨R,hR,hnear⟩ := exists_pmRamanujanBandResidueNumerator_ne_zero_interval hε hρ hzero
  let a := ρ.im+R/4
  let b := ρ.im+R/2
  have ha : ρ.im < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a,b]; linarith
  have hn : ∀ τ ∈ Icc a b, pmRamanujanBandResidueNumerator ε ρ τ ≠ 0 := by
    intro τ hτ
    apply hnear τ
    dsimp [a,b] at hτ
    constructor <;> linarith [hτ.1,hτ.2]
  have hc := pmbr_continuousOn hε hρ (b := b) ha
  have hi := (hc.norm.pow 2).integrableOn_Icc (μ := volume)
  have hsupport : Function.support (fun τ => ‖pmRamanujanBandResidueNumerator ε ρ τ‖^2) ∩
      Icc a b = Icc a b := by
    apply Set.inter_eq_right.mpr
    intro τ hτ
    change ‖pmRamanujanBandResidueNumerator ε ρ τ‖^2 ≠ 0
    exact ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (hn τ hτ)))
  have hp : 0 < ∫ τ in Icc a b, ‖pmRamanujanBandResidueNumerator ε ρ τ‖^2 := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (.of_forall fun τ => sq_nonneg _) hi).mpr
    rw [hsupport, Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  let hm := memLp_pmRamanujanBandResidueTest hε hρ (b := b) ha
  let h := hm.toLp (pmRamanujanBandResidueTest ε ρ a b)
  have hcoe : (h : ℝ → ℂ) =ᵐ[volume] pmRamanujanBandResidueTest ε ρ a b := hm.coeFn_toLp
  have hpair : (fun τ : ℝ => (starRingEnd ℂ) (h τ) * pmRamanujanBandResidueNumerator ε ρ τ)
      =ᵐ[volume] (fun τ => (starRingEnd ℂ) (pmRamanujanBandResidueTest ε ρ a b τ) *
        pmRamanujanBandResidueNumerator ε ρ τ) := by
    filter_upwards [hcoe] with τ hτ
    rw [hτ]
  refine ⟨a,b,ha,hab,h,hcoe,?_,?_,?_⟩
  · filter_upwards [hcoe] with τ hτ
    rw [hτ]
    intro hne
    have ht : τ ∈ Icc a b := by
      by_contra ht
      exact hne (by simp [pmRamanujanBandResidueTest, Set.indicator_of_notMem ht])
    rw [abs_of_nonpos (by linarith [ht.1] : ρ.im-τ ≤ 0)]
    linarith [ht.1]
  · exact (integrable_pmRamanujanBandResidueTest_pair hε hρ (b := b) ha).congr hpair.symm
  · rw [integral_congr_ae hpair, integral_pmRamanujanBandResidueTest_pair, Complex.ofReal_re]
    exact hp

end RHTower
