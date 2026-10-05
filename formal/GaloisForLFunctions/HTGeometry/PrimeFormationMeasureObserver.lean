import GaloisForLFunctions.HTGeometry.BaseNormFormationMeasure
import GaloisForLFunctions.HTGeometry.ArityCofinalFormationFracture
import GaloisForLFunctions.HTGeometry.GradeThreeCausalGreenFormation

/-!
# The complete prime formation measure and its Hilbert observer

For a finite nonempty set `I` of primes, `μ_I` is the law of the sum of the `2^{|I|} - 1`
independent exponential phases indexed by the nonempty subsets of `I`, the rate of a subset being
the sum of its prime logarithms.  These laws carry the base-norm formation isometry
`ℓ¹(𝕀) → M(Ω; ℓ¹(𝕀))` of `BaseNormFormationMeasure`.

Each `μ_I` lives on `[0, ∞)` and has the continuous density `h_I = H_I'`, positive on `(0, ∞)`
`(BNF.9)`: the derivative of a distribution function that is monotone on `[0, ∞)` is nonnegative,
and `H_{ρ::ρs} = ∫₀ᵗ ρ e^{-ρ(t-s)} H_{ρs}(s) ds ≤ H_{ρs}(t)(1 - e^{-ρt}) < H_{ρs}(t)`.  The density
field `𝔇 d(t) = (d_I h_I(t))_I` lies in `L¹((0,∞); ℓ¹)` with norm `‖d‖₁` `(BNF.11)`, by Tonelli.

The finite-horizon CDF observer `𝖢_T 𝔐 d (t) = (𝔐 d)([0,t])`, read in `L²((0,T]; ℓ²)` with `ℓ²(𝕀)`
realized on the orthonormal endpoint vectors `e_{Π_{p ∈ I} p}`, is the full formation tower composed
with `ℓ¹ ⊂ ℓ²`: bounded by `√T` but not bounded below, since on the first-prime channels
`‖𝖢_T 𝔐 e_{I_r}‖ → 0` while `‖𝔐 e_{I_r}‖_TV = 1` (Theorem 5.1).

Two corrections are made precise: distinct channels stay at total-variation distance two while
high-prime phases concentrate at `0` and first-prime phases escape every horizon; and forgetting
channel labels permits cancellation, `‖μ_I - μ_J‖_TV < 2` for `I ≠ J`, because both densities are
positive on `(0, ∞)`.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory Set Filter Topology HTGeometry RHTower

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

open Permutohedral

/-! ### Hypoexponential densities -/

theorem hypoCDFList_cons_zero (ρ : ℝ) (ρs : List ℝ) : hypoCDFList (ρ :: ρs) 0 = 0 :=
  expKernelConv_zero ρ _

theorem hypoCDFDeriv_nonneg {ρs : List ℝ} (h : ∀ ρ ∈ ρs, 0 < ρ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ hypoCDFDeriv ρs t := by
  have hd := ((hasDerivAt_hypoCDFList ρs t).hasDerivWithinAt (s := Ici 0)).derivWithin
    (uniqueDiffOn_Ici 0 t ht)
  rw [← hd]
  exact (monotoneOn_hypoCDFList h).derivWithin_nonneg

/-- `∫₀ᵗ ρ e^{-ρ(t-s)} ds = 1 - e^{-ρt}`. -/
theorem expKernelConv_one (ρ t : ℝ) :
    expKernelConv ρ (fun _ => 1) t = 1 - Real.exp (-(ρ * t)) := by
  have h := hypoCDFList_replicate 1 ρ t
  simpa [hypoCDFList, erlangCDF] using h

theorem expKernelConv_le {ρ : ℝ} (hρ : 0 ≤ ρ) {F : ℝ → ℝ} (hF : Continuous F) {t : ℝ}
    (ht : 0 ≤ t) {c : ℝ} (hc : ∀ s ∈ Icc 0 t, F s ≤ c) :
    expKernelConv ρ F t ≤ c * (1 - Real.exp (-(ρ * t))) := by
  rw [← expKernelConv_one, expKernelConv, expKernelConv, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on ht
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
  have h1 := hc s hs
  have hk : 0 ≤ ρ * Real.exp (-(ρ * (t - s))) := mul_nonneg hρ (Real.exp_pos _).le
  nlinarith

/-- Hypoexponential distribution functions with rates `≥ l > 0` are positive on `(0, ∞)`. -/
theorem hypoCDFList_pos {ρs : List ℝ} {l : ℝ} (hl : 0 < l) (h : ∀ ρ ∈ ρs, l ≤ ρ) {t : ℝ}
    (ht : 0 < t) : 0 < hypoCDFList ρs t := by
  have h1 := hypoCDFList_mono (forall₂_replicate_le h)
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hl) ht.le
  rw [hypoCDFList_replicate] at h1
  exact (erlangCDF_pos _ hl ht).trans_le h1

/-- Hypoexponential densities with rates `≥ l > 0` are positive on `(0, ∞)`. -/
theorem hypoCDFDeriv_pos {ρ : ℝ} {ρs : List ℝ} {l : ℝ} (hl : 0 < l) (h : ∀ x ∈ ρ :: ρs, l ≤ x)
    {t : ℝ} (ht : 0 < t) : 0 < hypoCDFDeriv (ρ :: ρs) t := by
  have hρ : 0 < ρ := hl.trans_le (h ρ List.mem_cons_self)
  have hs : ∀ x ∈ ρs, l ≤ x := fun x hx => h x (List.mem_cons_of_mem ρ hx)
  have hspos : ∀ x ∈ ρs, 0 < x := fun x hx => hl.trans_le (hs x hx)
  have hH := hypoCDFList_pos hl hs ht
  have hle := expKernelConv_le hρ.le (continuous_hypoCDFList ρs) ht.le
    (c := hypoCDFList ρs t) fun s hs' => monotoneOn_hypoCDFList hspos hs'.1 ht.le hs'.2
  show 0 < ρ * (hypoCDFList ρs t - expKernelConv ρ (hypoCDFList ρs) t)
  have he := Real.exp_pos (-(ρ * t))
  nlinarith [mul_pos (mul_pos hρ hH) he]

/-! ### The prime formation laws -/

/-- The formation law `μ_I` of a prime set `(BNF.1)`. -/
def primeLaw (I : PrimeSet) : Measure ℝ := subsetLaw I.grades

instance (I : PrimeSet) : IsProbabilityMeasure (primeLaw I) :=
  isProbabilityMeasure_subsetLaw I.grades_pos

theorem primeLaw_Iic (I : PrimeSet) {t : ℝ} (ht : 0 ≤ t) :
    primeLaw I (Iic t) = ENNReal.ofReal (subsetCDF I.grades t) :=
  (hasHalfLineCDF_subsetLaw I.grades_pos).Iic_eq t ht

theorem subsetRates_ne_nil (I : PrimeSet) : subsetRates I.grades ≠ [] := by
  intro h
  have hl := length_subsetRates I.grades
  rw [h, List.length_nil] at hl
  have : 1 < 2 ^ I.1.card := Nat.one_lt_two_pow (Finset.card_pos.2 I.2.1).ne'
  omega

theorem subsetCDF_zero (I : PrimeSet) : subsetCDF I.grades 0 = 0 := by
  obtain ⟨ρ, ρs, h⟩ := List.exists_cons_of_ne_nil (subsetRates_ne_nil I)
  rw [subsetCDF, h]
  exact hypoCDFList_cons_zero ρ ρs

/-- `μ_I` lives on `Ω = [0, ∞)`. -/
theorem primeLaw_Iio_zero (I : PrimeSet) : primeLaw I (Iio 0) = 0 :=
  measure_mono_null Iio_subset_Iic_self (by
    rw [primeLaw_Iic I le_rfl, subsetCDF_zero, ENNReal.ofReal_zero])

theorem primeLaw_Icc (I : PrimeSet) (t : ℝ) : primeLaw I (Icc 0 t) = primeLaw I (Iic t) := by
  rw [← measure_sdiff_null (s := Iic t) (primeLaw_Iio_zero I)]
  congr 1
  ext x
  simp only [mem_Icc, Set.mem_sdiff, mem_Iic, mem_Iio, not_lt]
  tauto

/-- The phase-type density `h_I = H_I'`. -/
def primeDensity (I : PrimeSet) : ℝ → ℝ := hypoCDFDeriv (subsetRates I.grades)

theorem continuous_primeDensity (I : PrimeSet) : Continuous (primeDensity I) :=
  continuous_hypoCDFDeriv _

theorem primeDensity_nonneg (I : PrimeSet) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ primeDensity I t :=
  hypoCDFDeriv_nonneg (subsetRates_pos I.grades_pos) ht

theorem primeDensity_pos (I : PrimeSet) {t : ℝ} (ht : 0 < t) : 0 < primeDensity I t := by
  obtain ⟨ρ, ρs, h⟩ := List.exists_cons_of_ne_nil (subsetRates_ne_nil I)
  rw [primeDensity, h]
  refine hypoCDFDeriv_pos (Real.log_pos one_lt_two) (fun x hx => ?_) ht
  rw [← h] at hx
  exact le_of_mem_subsetRates I.grades_pos I.log_two_le_grades x hx

theorem integral_primeDensity (I : PrimeSet) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, primeDensity I s = subsetCDF I.grades t := by
  unfold primeDensity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_hypoCDFList _ s)
    ((continuous_primeDensity I).intervalIntegrable _ _)]
  show subsetCDF I.grades t - subsetCDF I.grades 0 = _
  rw [subsetCDF_zero, sub_zero]

/-- **`(BNF.9)`**: `μ_I` has the density `h_I` on `(0, ∞)`. -/
theorem primeLaw_eq_withDensity (I : PrimeSet) :
    primeLaw I = (volume.restrict (Ioi 0)).withDensity
      fun t => ENNReal.ofReal (primeDensity I t) := by
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  rcases lt_or_ge a 0 with ha | ha
  · rw [show Iic a ∩ Ioi (0 : ℝ) = ∅ by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      linarith, Measure.restrict_empty, lintegral_zero_measure]
    exact (hasHalfLineCDF_subsetLaw I.grades_pos).Iic_neg a ha
  · rw [show Iic a ∩ Ioi (0 : ℝ) = Ioc 0 a by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]
      tauto, primeLaw_Iic I ha, ← ofReal_integral_eq_lintegral_ofReal,
      ← intervalIntegral.integral_of_le ha, integral_primeDensity]
    · exact (continuous_primeDensity I).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact primeDensity_nonneg I ht.1.le

theorem primeLaw_apply (I : PrimeSet) {E : Set ℝ} (hE : MeasurableSet E) :
    primeLaw I E = ∫⁻ t in E ∩ Ioi 0, ENNReal.ofReal (primeDensity I t) := by
  rw [primeLaw_eq_withDensity, withDensity_apply _ hE, Measure.restrict_restrict hE]

/-- **`(BNF.9)`**: `∫₀^∞ h_I = 1`. -/
theorem lintegral_primeDensity (I : PrimeSet) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (primeDensity I t) = 1 := by
  have h := measure_univ (μ := primeLaw I)
  rwa [primeLaw_apply I MeasurableSet.univ, univ_inter] at h

theorem integrableOn_primeDensity (I : PrimeSet) : IntegrableOn (primeDensity I) (Ioi 0) := by
  refine ⟨(continuous_primeDensity I).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact primeDensity_nonneg I (le_of_lt ht)), lintegral_primeDensity]
  exact ENNReal.one_lt_top

theorem integral_primeDensity_Ioi (I : PrimeSet) : ∫ t in Ioi 0, primeDensity I t = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact primeDensity_nonneg I (le_of_lt ht))
    (continuous_primeDensity I).aestronglyMeasurable, lintegral_primeDensity, ENNReal.toReal_one]

/-! ### The density realization `(BNF.10)`–`(BNF.11)` -/

open Classical in
/-- The all-grade density field `(𝔇 d)(t) = (d_I h_I(t))_I` `(BNF.10)` (set to `0` off the full
measure set where it is summable). -/
def densityVec (d : BaseCoeff PrimeSet) (t : ℝ) : BaseCoeff PrimeSet :=
  if h : Memℓp (fun I => d I * (primeDensity I t : ℂ)) 1 then ⟨_, h⟩ else 0

theorem measurable_mass_density (d : BaseCoeff PrimeSet) (I : PrimeSet) :
    Measurable fun t => ‖d I‖ₑ * ENNReal.ofReal (primeDensity I t) :=
  ((continuous_primeDensity I).measurable.ennreal_ofReal).const_mul _

theorem lintegral_mass_density (d : BaseCoeff PrimeSet) :
    ∫⁻ t in Ioi 0, ∑' I, ‖d I‖ₑ * ENNReal.ofReal (primeDensity I t) = ‖d‖ₑ := by
  rw [lintegral_tsum fun I => (measurable_mass_density d I).aemeasurable]
  simp_rw [lintegral_const_mul _ (continuous_primeDensity _).measurable.ennreal_ofReal,
    lintegral_primeDensity, mul_one]
  exact (enorm_baseCoeff d).symm

theorem ae_densityVec (d : BaseCoeff PrimeSet) :
    ∀ᵐ t ∂(volume.restrict (Ioi 0)), Memℓp (fun I => d I * (primeDensity I t : ℂ)) 1 ∧
      ‖densityVec d t‖ₑ = ∑' I, ‖d I‖ₑ * ENNReal.ofReal (primeDensity I t) := by
  have hfin : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      ∑' I, ‖d I‖ₑ * ENNReal.ofReal (primeDensity I t) < ∞ :=
    ae_lt_top' (Measurable.tsum (measurable_mass_density d)).aemeasurable
      (by rw [lintegral_mass_density]; exact enorm_ne_top)
  filter_upwards [hfin, ae_restrict_mem measurableSet_Ioi] with t ht ht0
  have hh : ∀ I, 0 ≤ primeDensity I t := fun I => primeDensity_nonneg I (le_of_lt ht0)
  have hn : ∀ I, ‖d I * (primeDensity I t : ℂ)‖ = ‖d I‖ * primeDensity I t := fun I => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hh I)]
  have hmem : Memℓp (fun I => d I * (primeDensity I t : ℂ)) 1 := by
    refine (memℓp_gen_iff (p := 1) (by norm_num)).2 ?_
    simp only [ENNReal.toReal_one, Real.rpow_one, hn]
    refine (ENNReal.summable_toReal ht.ne).congr fun I => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (hh I))]
  refine ⟨hmem, ?_⟩
  rw [densityVec, dif_pos hmem, enorm_baseCoeff]
  refine tsum_congr fun I => ?_
  show ‖d I * (primeDensity I t : ℂ)‖ₑ = _
  rw [← ofReal_norm, hn, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]

theorem continuous_lpSingle {ι : Type*} [DecidableEq ι] (i : ι) :
    Continuous (lp.single (E := fun _ : ι => ℂ) 1 i) :=
  (Isometry.of_dist_eq fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← lp.single_sub, lp.norm_single (by norm_num)]).continuous

theorem aestronglyMeasurable_densityVec (d : BaseCoeff PrimeSet) :
    AEStronglyMeasurable (densityVec d) (volume.restrict (Ioi 0)) := by
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset PrimeSet))
    (f := fun s t => ∑ I ∈ s, lp.single 1 I (d I * (primeDensity I t : ℂ))) (fun s => ?_) ?_
  · exact (continuous_finsetSum _ fun I _ => (continuous_lpSingle I).comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_primeDensity I))))
      |>.aestronglyMeasurable
  · filter_upwards [ae_densityVec d] with t ht
    have e : densityVec d t = ⟨_, ht.1⟩ := dif_pos ht.1
    rw [e]
    exact lp.hasSum_single (p := 1) (by norm_num) (⟨_, ht.1⟩ : BaseCoeff PrimeSet)

/-- **Corollary 4.1, `(BNF.11)`**: `𝔇 d ∈ L¹((0,∞); ℓ¹)` with `‖𝔇 d‖_{L¹} = ‖d‖₁`. -/
theorem densityVec_isometry (d : BaseCoeff PrimeSet) :
    MemLp (densityVec d) 1 (volume.restrict (Ioi 0)) ∧
      eLpNorm (densityVec d) 1 (volume.restrict (Ioi 0)) = ‖d‖ₑ := by
  have hn : eLpNorm (densityVec d) 1 (volume.restrict (Ioi 0)) = ‖d‖ₑ := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_mass_density d]
    exact lintegral_congr_ae ((ae_densityVec d).mono fun t ht => ht.2)
  exact ⟨⟨aestronglyMeasurable_densityVec d, by rw [hn]; exact enorm_lt_top⟩, hn⟩

/-! ### The Hilbert CDF observer `(BNF.12)`–`(BNF.15)` -/

section Inclusion

variable {ι : Type*}

theorem one_le_two_ennreal : (1 : ℝ≥0∞) ≤ 2 := by norm_num

theorem norm_linearMapOfLE_le (f : BaseCoeff ι) :
    ‖lp.linearMapOfLE ℂ (fun _ : ι => ℂ) one_le_two_ennreal f‖ ≤ ‖f‖ := by
  set g := lp.linearMapOfLE ℂ (fun _ : ι => ℂ) one_le_two_ennreal f
  have hg : ∀ i, g i = f i := fun i => by rw [lp.coe_linearMapOfLE_apply]
  have h2 : ‖g‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [HistoryFamily.lp_norm_sq g, sq ‖f‖]
    nth_rewrite 2 [norm_baseCoeff f]
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_) (HistoryFamily.summable_norm_sq g)
      ((summable_norm_baseCoeff f).mul_left _)
    rw [hg, sq, mul_comm]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm one_ne_zero f i) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- The inclusion `ℓ¹ ⊂ ℓ²`, of norm at most one. -/
def baseInclusion : BaseCoeff ι →L[ℂ] HistoryFamily.Controls ι :=
  LinearMap.mkContinuous (lp.linearMapOfLE ℂ (fun _ : ι => ℂ) one_le_two_ennreal) 1 fun f => by
    rw [one_mul]
    exact norm_linearMapOfLE_le f

@[simp] theorem baseInclusion_apply (f : BaseCoeff ι) (i : ι) : baseInclusion f i = f i :=
  congrFun (lp.coe_linearMapOfLE_apply one_le_two_ennreal f) i

theorem norm_baseInclusion_le (f : BaseCoeff ι) : ‖baseInclusion f‖ ≤ ‖f‖ :=
  norm_linearMapOfLE_le f

end Inclusion

/-- The finite-horizon CDF observer `𝖢_T 𝔐 : ℓ¹(𝕀) → L²((0,T]; ℓ²)` `(BNF.13)`, with `ℓ²(𝕀)`
realized isometrically on the orthonormal endpoint vectors `e_{Π_{p ∈ I} p}`. -/
def cdfObserver (T : ℝ) : BaseCoeff PrimeSet →L[ℂ] ResponseSpace T :=
  (towerFamily.response T).comp baseInclusion

theorem towerFamily_weight_eq (I : PrimeSet) {t : ℝ} (ht : 0 ≤ t) :
    towerFamily.weight I t = (primeLaw I (Iic t)).toReal := by
  show subsetCDF I.grades (max t 0) = _
  rw [max_eq_left ht, primeLaw_Iic I ht, ENNReal.toReal_ofReal (show 0 ≤ subsetCDF I.grades t from
    hypoCDFList_nonneg (subsetRates_pos I.grades_pos) ht)]

/-- **`(BNF.12)`**: the observed history at time `t ≥ 0` is the distribution function of the
formed measure, `(𝖢_T 𝔐 d)(t) = (𝔐 d)([0,t]) = (d_I μ_I([0,t]))_I`. -/
theorem profile_cdfObserver (d : BaseCoeff PrimeSet) {t : ℝ} (ht : 0 ≤ t) :
    towerFamily.profile (baseInclusion d) t =
      towerFamily.embed (baseInclusion (formationMeasure primeLaw d (Icc 0 t))) := by
  rw [HistoryFamily.profile, formationMeasure_apply primeLaw d measurableSet_Icc]
  congr 1
  refine lp.ext (funext fun I => ?_)
  simp only [HistoryFamily.weightDiag, ellTwoDiagonal_apply, baseInclusion_apply, massVec_apply,
    towerFamily_weight_eq I ht, primeLaw_Icc]
  ring

theorem cdfObserver_ae (T : ℝ) (d : BaseCoeff PrimeSet) :
    (cdfObserver T d : ℝ → ArithSpace) =ᵐ[timeMeasure T] towerFamily.profile (baseInclusion d) :=
  towerFamily.coeFn_response T _

theorem baseInclusion_single (I : PrimeSet) (a : ℂ) :
    baseInclusion (lp.single 1 I a) = lp.single 2 I a :=
  lp.ext (funext fun J => by simp [lp.single_apply])

theorem enorm_single_one (I : PrimeSet) : ‖(lp.single 1 I (1 : ℂ) : BaseCoeff PrimeSet)‖ₑ = 1 := by
  rw [← ofReal_norm, lp.norm_single (by norm_num), norm_one, ENNReal.ofReal_one]

/-- **Theorem 5.1, `(BNF.13)`–`(BNF.15)`**: the observer is bounded by `√T`; on the first-prime
channels its output tends to zero while the formed measures keep unit total variation; hence it is
not bounded below. -/
theorem cdfObserver_spec {T : ℝ} (hT : 0 < T) :
    (∀ d, ‖cdfObserver T d‖ ≤ Real.sqrt T * ‖d‖) ∧
      Tendsto (fun r : ℕ => ‖cdfObserver T
        (lp.single 1 (PrimeSet.firstPrimes (r + 1) r.succ_pos) 1)‖) atTop (𝓝 0) ∧
      (∀ I, (formationMeasure primeLaw (lp.single 1 I 1)).variation univ = 1) ∧
      ¬ ∃ c > 0, ∀ d, c * ‖d‖ ≤ ‖cdfObserver T d‖ := by
  have hs : ∀ I, ‖cdfObserver T (lp.single 1 I 1)‖ = sigma T I := fun I => by
    rw [cdfObserver, ContinuousLinearMap.comp_apply, baseInclusion_single,
      norm_tower_single hT.le, norm_one, mul_one]
  have hlim : Tendsto (fun r : ℕ => ‖cdfObserver T
      (lp.single 1 (PrimeSet.firstPrimes (r + 1) r.succ_pos) 1)‖) atTop (𝓝 0) := by
    simp_rw [hs]
    exact tendsto_sigma_firstPrimes hT.le
  refine ⟨fun d => ?_, hlim, fun I => ?_, ?_⟩
  · exact ((tower_fracture hT).1 _).trans
      (mul_le_mul_of_nonneg_left (norm_baseInclusion_le d) (Real.sqrt_nonneg _))
  · rw [variation_formationMeasure_univ, enorm_single_one]
  · rintro ⟨c, hc, hb⟩
    obtain ⟨r, hr⟩ := (hlim.eventually (gt_mem_nhds hc)).exists
    have := hb (lp.single 1 (PrimeSet.firstPrimes (r + 1) r.succ_pos) 1)
    rw [lp.norm_single (by norm_num), norm_one, mul_one] at this
    linarith

/-! ### Corrections: distance two, concentration and escape -/

theorem enorm_single_sub_single {ι : Type*} [DecidableEq ι] {I J : ι} (h : I ≠ J) :
    ‖(lp.single 1 I (1 : ℂ) - lp.single 1 J 1 : BaseCoeff ι)‖ₑ = 2 := by
  rw [enorm_baseCoeff, tsum_eq_sum (s := {I, J}) fun K hK => ?_, Finset.sum_pair h]
  · simp [lp.single_apply, h, Ne.symm h]
    norm_num
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hK
    simp [lp.single_apply, hK.1, hK.2]

/-- **§8 (4)**: distinct channels stay at total-variation distance two. -/
theorem variation_formationMeasure_single_sub {I J : PrimeSet} (h : I ≠ J) :
    (formationMeasure primeLaw (lp.single 1 I 1) -
      formationMeasure primeLaw (lp.single 1 J 1)).variation univ = 2 := by
  rw [variation_formationMeasure_sub, enorm_single_sub_single h]

/-- **§8 (4)**: at a fixed grade, high-prime phases concentrate at `0`. -/
theorem tendsto_primeLaw_block_Iic (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => primeLaw (PrimeSet.block k r) (Iic ε)) atTop (𝓝 1) := by
  have hH : Tendsto (fun k => subsetCDF (PrimeSet.block k r).grades ε) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      ((tendsto_erlangCDF_atTop (2 ^ (r + 1) - 1) hε).comp tendsto_log_nth_prime)
      tendsto_const_nhds (fun k => ?_)
      fun k => hypoCDFList_le_one (subsetRates_pos (PrimeSet.grades_pos _)) hε.le
    have hl : 0 < Real.log (Nat.nth Nat.Prime k) :=
      Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime k).one_lt)
    have h := erlangCDF_le_subsetCDF hl (PrimeSet.grades_pos _)
      (PrimeSet.log_le_grades_block k r) hε.le
    have e : 2 ^ (PrimeSet.block k r).1.card - 1 = 2 ^ (r + 1) - 1 := by
      rw [PrimeSet.card_block]
    rw [e] at h
    exact h
  have h1 := (ENNReal.continuous_ofReal.tendsto 1).comp hH
  rw [ENNReal.ofReal_one] at h1
  exact h1.congr fun k => (primeLaw_Iic _ hε.le).symm

/-- **§8 (4)**: the first-prime phases escape every finite horizon. -/
theorem tendsto_primeLaw_firstPrimes_Iic {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun r : ℕ => primeLaw (PrimeSet.firstPrimes (r + 1) r.succ_pos) (Iic t)) atTop
      (𝓝 0) := by
  have hH : Tendsto (fun r : ℕ => subsetCDF (PrimeSet.firstPrimes (r + 1) r.succ_pos).grades t)
      atTop (𝓝 0) := by
    refine squeeze_zero (fun r => hypoCDFList_nonneg (subsetRates_pos (PrimeSet.grades_pos _)) ht)
      (fun r => ?_) ((tendsto_firstPrimes_bound ht).comp (tendsto_add_atTop_nat 1))
    set I := PrimeSet.firstPrimes (r + 1) r.succ_pos
    have h1 := subsetCDF_le_pow I.grades_pos ht
    have e : 2 ^ I.1.card - 1 = 2 ^ (r + 1) - 1 := by rw [PrimeSet.card_firstPrimes]
    rw [e] at h1
    refine h1.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀
      (mul_nonneg (Finset.sum_nonneg fun i _ => (I.grades_pos i).le) ht) ?_ _) (by positivity))
    have hA := PrimeSet.sum_grades_firstPrimes_le (r + 1) r.succ_pos
    exact mul_le_mul_of_nonneg_right hA ht
  have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp hH
  rw [ENNReal.ofReal_zero] at h1
  exact h1.congr fun k => (primeLaw_Iic _ ht).symm

/-! ### Forgetting channel labels -/

section Forget

variable {ι α : Type*} [MeasurableSpace α]

/-- Summing over channels, `ℓ¹(ι) → ℂ`. -/
def labelSum : BaseCoeff ι →+ ℂ where
  toFun v := ∑' i, v i
  map_zero' := by simp
  map_add' v w := by
    simp only [lp.coeFn_add, Pi.add_apply]
    exact (Summable.of_norm (summable_norm_baseCoeff v)).tsum_add
      (Summable.of_norm (summable_norm_baseCoeff w))

theorem labelSum_apply (v : BaseCoeff ι) : labelSum v = ∑' i, v i := rfl

theorem norm_labelSum_le (v : BaseCoeff ι) : ‖labelSum v‖ ≤ ‖v‖ := by
  rw [norm_baseCoeff]
  exact norm_tsum_le_tsum_norm (summable_norm_baseCoeff v)

theorem continuous_labelSum : Continuous (labelSum (ι := ι)) :=
  AddMonoidHomClass.continuous_of_bound labelSum 1 fun v => by
    rw [one_mul]
    exact norm_labelSum_le v

/-- The scalar measure obtained by forgetting channel labels. -/
def forgetLabels (ν : VectorMeasure α (BaseCoeff ι)) : VectorMeasure α ℂ :=
  ν.mapRange labelSum continuous_labelSum

/-- Forgetting labels never increases total variation. -/
theorem variation_forgetLabels_le (ν : VectorMeasure α (BaseCoeff ι)) :
    (forgetLabels ν).variation ≤ ν.variation :=
  VectorMeasure.variation_le_of_forall_enorm_le fun E _ => by
    rw [forgetLabels, VectorMeasure.mapRange_apply]
    exact (enorm_le_iff_norm_le.2 (norm_labelSum_le _)).trans
      (VectorMeasure.enorm_measure_le_variation ν E)

end Forget

theorem forgetLabels_single_sub_apply {I J : PrimeSet} (h : I ≠ J) {E : Set ℝ}
    (hE : MeasurableSet E) :
    forgetLabels (formationMeasure primeLaw (lp.single 1 I 1 - lp.single 1 J 1)) E =
      (((primeLaw I E).toReal - (primeLaw J E).toReal : ℝ) : ℂ) := by
  rw [forgetLabels, VectorMeasure.mapRange_apply, formationMeasure_apply _ _ hE, labelSum_apply,
    tsum_eq_sum (s := {I, J}) fun K hK => ?_, Finset.sum_pair h]
  · simp [lp.single_apply, h, Ne.symm h, sub_eq_add_neg]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hK
    simp [lp.single_apply, hK.1, hK.2]

theorem toReal_primeLaw (I : PrimeSet) {E : Set ℝ} (hE : MeasurableSet E) :
    (primeLaw I E).toReal = ∫ t in E ∩ Ioi 0, primeDensity I t := by
  rw [primeLaw_apply I hE, ← ofReal_integral_eq_lintegral_ofReal
    ((integrableOn_primeDensity I).mono_set inter_subset_right) (by
      filter_upwards [ae_restrict_mem (hE.inter measurableSet_Ioi)] with t ht
      exact primeDensity_nonneg I (le_of_lt ht.2)),
    ENNReal.toReal_ofReal (setIntegral_nonneg (hE.inter measurableSet_Ioi)
      fun t ht => primeDensity_nonneg I (le_of_lt ht.2))]

/-- **§8 (2)**: forgetting channel labels destroys the isometry: for distinct prime sets
`‖μ_I - μ_J‖_TV < 2 = ‖e_I - e_J‖₁`. -/
theorem variation_forgetLabels_lt {I J : PrimeSet} (h : I ≠ J) :
    (forgetLabels (formationMeasure primeLaw (lp.single 1 I 1 - lp.single 1 J 1))).variation
      univ < ‖(lp.single 1 I (1 : ℂ) - lp.single 1 J 1 : BaseCoeff PrimeSet)‖ₑ := by
  rw [enorm_single_sub_single h]
  set g : ℝ → ℝ := fun t => |primeDensity I t - primeDensity J t|
  have hgc : Continuous g := ((continuous_primeDensity I).sub (continuous_primeDensity J)).abs
  have hgi : IntegrableOn g (Ioi 0) :=
    ((integrableOn_primeDensity I).sub (integrableOn_primeDensity J)).abs
  -- the variation is dominated by `∫ |h_I - h_J|`
  have hdom : (forgetLabels (formationMeasure primeLaw
      (lp.single 1 I 1 - lp.single 1 J 1))).variation ≤
      (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (g t) := by
    refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
    rw [forgetLabels_single_sub_apply h hE, withDensity_apply _ hE,
      Measure.restrict_restrict hE, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      toReal_primeLaw I hE, toReal_primeLaw J hE,
      ← integral_sub ((integrableOn_primeDensity I).mono_set inter_subset_right)
        ((integrableOn_primeDensity J).mono_set inter_subset_right),
      ← ofReal_integral_eq_lintegral_ofReal (hgi.mono_set inter_subset_right)
        (ae_of_all _ fun t => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_integral_le_integral_abs)
  -- `∫ |h_I - h_J| < ∫ h_I + ∫ h_J = 2`
  have hlt : ∫ t in Ioi 0, g t < 2 := by
    have hIJ : IntegrableOn (fun t => primeDensity I t + primeDensity J t) (Ioi 0) :=
      (integrableOn_primeDensity I).add (integrableOn_primeDensity J)
    have hpos : 0 < ∫ t in Ioi 0, (primeDensity I t + primeDensity J t - g t) := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        (f := fun t => primeDensity I t + primeDensity J t - g t) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have h1 := primeDensity_nonneg I (le_of_lt ht)
        have h2 := primeDensity_nonneg J (le_of_lt ht)
        have : |primeDensity I t - primeDensity J t| ≤ primeDensity I t + primeDensity J t :=
          abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
        show (0 : ℝ) ≤ primeDensity I t + primeDensity J t - g t
        linarith [this]) (hIJ.sub hgi)]
      rw [show Function.support (fun t => primeDensity I t + primeDensity J t - g t) ∩ Ioi 0 =
          Ioi 0 from inter_eq_right.2 fun t ht => by
        have h1 := primeDensity_pos I ht
        have h2 := primeDensity_pos J ht
        rw [Function.mem_support]
        show primeDensity I t + primeDensity J t - |primeDensity I t - primeDensity J t| ≠ 0
        rcases abs_cases (primeDensity I t - primeDensity J t) with ⟨h3, -⟩ | ⟨h3, -⟩ <;>
          rw [h3] <;> linarith, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    rw [integral_sub (f := fun t => primeDensity I t + primeDensity J t) hIJ hgi,
      integral_add (integrableOn_primeDensity I) (integrableOn_primeDensity J),
      integral_primeDensity_Ioi, integral_primeDensity_Ioi] at hpos
    linarith
  calc _ ≤ ((volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (g t)) univ := hdom _
    _ = ENNReal.ofReal (∫ t in Ioi 0, g t) := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ fun t => abs_nonneg _)]
    _ < 2 := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
        exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hlt

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
