import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarDualCertificate
import GaloisForLFunctions.BiScaleUncertainty.BroadSpectralCostRealization

/-!
# Physical partition certificates for actual source energy

Every admissible measurable collar partition gives a lower bound for the extended
archimedean energy of every compact continuous logarithmic-grid source. The bound
passes to the supremum over physical partitions, without an optimizer or a finite
source-energy assumption. Finite maxima across smaller grids give monotone certificates.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

namespace PhysicalCollarPartition
variable {n : ℕ}

/-- Allocate a nonnegative extended density using the actual physical shares. -/
def allocated (ρ : PhysicalCollarPartition n) (F : ℝ → ℝ≥0∞) (k : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (ρ.share k x) * F x

theorem measurable_allocated (ρ : PhysicalCollarPartition n) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (k : ℕ) : Measurable (ρ.allocated F k) :=
  (ρ.measurable_share k).ennreal_ofReal.mul hF

/-- Signed affine transport is exact for every physical partition, even at infinite mass. -/
theorem lintegral_signed_transport (ρ : PhysicalCollarPartition n) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) :
    (∑ k ∈ Finset.range (n + 1),
      ((∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.allocated F k (logarithmicCollarNode k - y)) +
       (∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.allocated F k (logarithmicCollarNode k + y)))) =
      ∫⁻ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), F x := by
  have hterm (k : ℕ) :
      ((∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.allocated F k (logarithmicCollarNode k - y)) +
       (∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.allocated F k (logarithmicCollarNode k + y))) =
        ∫⁻ x, ρ.allocated F k x := by
    rw [lintegral_collar_both, ← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext x
    by_cases hx : x ∈ Ioo (logarithmicCollarNode k - logarithmicCollarRadius)
        (logarithmicCollarNode k + logarithmicCollarRadius)
    · exact indicator_of_mem hx _
    · have he : x ∉ logarithmicPhysicalCollar n k := fun h => hx h.1
      simp [hx, allocated, ρ.supported k x he]
  simp_rw [hterm]
  rw [← lintegral_finsetSum (Finset.range (n + 1))
    (fun k _ => ρ.measurable_allocated F hF k), ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  simp only [allocated, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
    (fun k (_ : k ∈ Finset.range (n + 1)) => ρ.nonneg k x), ρ.partition]
  by_cases hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) <;> simp [hx]

/-- Pull back the source increment density, spending the origin interval once. -/
def sourceFibre (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) (y : ℝ) : ℝ≥0∞ :=
  continuousArchIncrementDensity (compactAutocorrKernel f) y +
    ∑ k ∈ Finset.range (n + 1),
      (ρ.allocated (continuousArchIncrementDensity (compactAutocorrKernel f)) k
        (logarithmicCollarNode k - y) +
       ρ.allocated (continuousArchIncrementDensity (compactAutocorrKernel f)) k
        (logarithmicCollarNode k + y))

/-- All overlap disappears under exact physical transport. -/
theorem lintegral_sourceFibre (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    (∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.sourceFibre f y) =
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f) x := by
  let F := continuousArchIncrementDensity (compactAutocorrKernel f)
  have hF : Measurable F := measurable_continuousArchIncrementDensity _
  have hl (k : ℕ) : Measurable (fun y => ρ.allocated F k (logarithmicCollarNode k - y)) :=
    (ρ.measurable_allocated F hF k).comp (measurable_const.sub measurable_id)
  have hr (k : ℕ) : Measurable (fun y => ρ.allocated F k (logarithmicCollarNode k + y)) :=
    (ρ.measurable_allocated F hF k).comp (measurable_const.add measurable_id)
  change (∫⁻ y in Ioo 0 logarithmicCollarRadius,
    F y + ∑ k ∈ Finset.range (n + 1),
      (ρ.allocated F k (logarithmicCollarNode k - y) +
       ρ.allocated F k (logarithmicCollarNode k + y))) = _
  rw [lintegral_add_left hF, lintegral_finsetSum (Finset.range (n + 1))
    (f := fun k y => ρ.allocated F k (logarithmicCollarNode k - y) +
      ρ.allocated F k (logarithmicCollarNode k + y)) (fun k _ => (hl k).add (hr k))]
  simp_rw [lintegral_add_left (hl _)]
  rw [ρ.lintegral_signed_transport F hF]
  have hd : Disjoint (Ioo 0 logarithmicCollarRadius)
      (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2.le) hy.1
  rw [← lintegral_union measurableSet_Ioo hd]
  apply setLIntegral_congr
  have he : logarithmicCollarRadius < logarithmicCollarEndpoint n := by
    have hb := logarithmicCollarNode_ge_log_two n
    change Real.log 2 ≤ logarithmicCollarEndpoint n at hb
    have hp := logarithmicCollarRadius_pos
    unfold logarithmicCollarRadius at hp ⊢
    linarith
  filter_upwards [volume.ae_ne logarithmicCollarRadius] with x hx
  apply propext
  change ((0 < x ∧ x < logarithmicCollarRadius) ∨
    (logarithmicCollarRadius < x ∧ x < logarithmicCollarEndpoint n)) ↔
    (0 < x ∧ x < logarithmicCollarEndpoint n)
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;> constructor <;>
      linarith [logarithmicCollarRadius_pos]
  · rintro ⟨ha, hb⟩
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exact Or.inl ⟨ha, hlt⟩
    · exact Or.inr ⟨hgt, hb⟩

/-- The shared-origin support function applies to arbitrary physical allocations. -/
theorem kernel_source_pointwise (ρ : PhysicalCollarPartition n) (f : LogarithmicGridSource n)
    (y : ℝ) :
    ρ.kernel y * autocorr f.1 0 ≤
      archLevySinhWeight y * (autocorr f.1 0 - autocorr f.1 y) +
      ∑ k ∈ Finset.range (n + 1),
        (ρ.weight false k y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode k - y)) +
         ρ.weight true k y * (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode k + y))) := by
  have h := shared_origin_leverage_bound (logarithmicSignedCosets n)
    (logarithmicSignedCosets_nonempty n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => ρ.weight j.2 k y)
    (fun j k => autocorr f.1 (logarithmicCollarNode k + collarSignedOffset j.2 y))
    (archLevySinhWeight y) (autocorr f.1 y) (autocorr f.1 0) (autocorr_zero_nonneg f.1)
    (fun j _ => autocorr_logarithmicCoset_sphere f.1 n j.1 f.2 j.2 y)
  rw [sum_logarithmicSignedCosets n (fun σ k => ρ.weight σ k y),
    sum_logarithmicSignedCosets n (fun σ k => ρ.weight σ k y *
      (autocorr f.1 0 - autocorr f.1 (logarithmicCollarNode k + collarSignedOffset σ y)))] at h
  simpa only [kernel, mass, blockNorm, collarSignedOffset, Bool.false_eq_true,
    ↓reduceIte, ← sub_eq_add_neg] using h

private theorem branch_density (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ))
    (σ : Bool) (k : ℕ) (y : ℝ) :
    ENNReal.ofReal (ρ.weight σ k y *
      (autocorr f 0 - autocorr f (logarithmicCollarNode k + collarSignedOffset σ y))) =
      ρ.allocated (continuousArchIncrementDensity (compactAutocorrKernel f)) k
        (logarithmicCollarNode k + collarSignedOffset σ y) := by
  unfold allocated continuousArchIncrementDensity compactAutocorrKernel
  rw [← ENNReal.ofReal_mul (ρ.nonneg k _)]
  congr 1
  unfold weight density archLevySinhWeight
  dsimp only [ContinuousMap.coe_mk]
  ring

theorem kernel_source_extended (ρ : PhysicalCollarPartition n) (f : LogarithmicGridSource n)
    {y : ℝ} (hy : 0 ≤ y) :
    ENNReal.ofReal (ρ.kernel y * autocorr f.1 0) ≤ ρ.sourceFibre f.1 y := by
  have hD (x : ℝ) : 0 ≤ autocorr f.1 0 - autocorr f.1 x :=
    autocorr_sub_nonneg f.1.hasCompactSupport f.1.continuous x
  have hn (σ : Bool) (k : ℕ) (x : ℝ) :
      0 ≤ ρ.weight σ k y * (autocorr f.1 0 - autocorr f.1 x) :=
    mul_nonneg (ρ.weight_nonneg σ k y) (hD x)
  refine (ENNReal.ofReal_le_ofReal (ρ.kernel_source_pointwise f y)).trans_eq ?_
  rw [ENNReal.ofReal_add (mul_nonneg (archLevySinhWeight_nonneg hy) (hD y))
    (Finset.sum_nonneg fun k _ => add_nonneg (hn false k _) (hn true k _)),
    ENNReal.ofReal_sum_of_nonneg (fun k _ => add_nonneg (hn false k _) (hn true k _))]
  unfold sourceFibre
  congr 1
  · change ENNReal.ofReal (_ * _) = ENNReal.ofReal (_ * _)
    congr 1
    change archLevySinhWeight y * (autocorr f.1 0 - autocorr f.1 y) =
      (autocorr f.1 0 - autocorr f.1 y) * archLevySinhWeight y
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro k _
    rw [ENNReal.ofReal_add (hn false k _) (hn true k _)]
    have hl := ρ.branch_density f.1 false k y
    have hr := ρ.branch_density f.1 true k y
    simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] at hl hr
    rw [hl, hr]

/-- Every physical partition bounds actual compact-continuous source energy.
No differentiability, finite-energy, or optimizer premise is required. -/
theorem coefficient_source_energy (ρ : PhysicalCollarPartition n) (f : LogarithmicGridSource n) :
    ENNReal.ofReal (ρ.coefficient * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  have hint := ρ.integrableOn_kernel.mul_const (autocorr f.1 0)
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 logarithmicCollarRadius)]
      (fun y => ρ.kernel y * autocorr f.1 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact mul_nonneg (ρ.kernel_bounds hy.1.le).1 (autocorr_zero_nonneg f.1)
  change ENNReal.ofReal ((∫ y in Ioo 0 logarithmicCollarRadius, ρ.kernel y) * _) ≤ _
  rw [← integral_mul_const, ofReal_integral_eq_lintegral_ofReal hint hn]
  calc
    _ ≤ ∫⁻ y in Ioo 0 logarithmicCollarRadius, ρ.sourceFibre f.1 y :=
      setLIntegral_mono' measurableSet_Ioo (fun y hy => ρ.kernel_source_extended f hy.1.le)
    _ = _ := ρ.lintegral_sourceFibre f.1

/-- The continuous allocation optimum is a genuine source-energy certificate;
an optimizing partition need not exist. -/
theorem optimalCoefficient_source_energy (f : LogarithmicGridSource n) :
    ENNReal.ofReal (optimalCoefficient n * autocorr f.1 0) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  let E := ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
    continuousArchIncrementDensity (compactAutocorrKernel f.1) x
  change ENNReal.ofReal (optimalCoefficient n * autocorr f.1 0) ≤ E
  by_cases hE : E = ∞
  · rw [hE]
    exact le_top
  by_cases hR : autocorr f.1 0 = 0
  · simp [hR]
  have hRp : 0 < autocorr f.1 0 := lt_of_le_of_ne (autocorr_zero_nonneg f.1) (Ne.symm hR)
  apply (ENNReal.ofReal_le_iff_le_toReal hE).2
  apply (le_div_iff₀ hRp).1
  apply csSup_le
  · exact ⟨(equalMultiplicity n).coefficient, equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    exact (le_div_iff₀ hRp).2
      ((ENNReal.ofReal_le_iff_le_toReal hE).1 (ρ.coefficient_source_energy f))

/-- The optimum also bounds the complete half-line energy. -/
theorem optimalCoefficient_source_energy_halfline (f : LogarithmicGridSource n) :
    ENNReal.ofReal (optimalCoefficient n * autocorr f.1 0) ≤
      ∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  exact (optimalCoefficient_source_energy f).trans (lintegral_mono_set fun _ hx => hx.1)

end PhysicalCollarPartition

/-- Restrict an actual source to a smaller logarithmic grid. -/
def LogarithmicGridSource.restrict {n k : ℕ} (f : LogarithmicGridSource n) (hk : k ≤ n) :
    LogarithmicGridSource k :=
  ⟨f.1, fun j hj => f.2 j (Finset.mem_range.mpr (by
    have h := Finset.mem_range.mp hj
    omega))⟩

/-- Best optimized physical-allocation certificate among all cutoffs up to `n+2`.
This finite maximum is not identified with the sharp autocorrelation constant. -/
def monotoneCollarCoefficient (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, by simp⟩ PhysicalCollarPartition.optimalCoefficient

theorem optimalCoefficient_le_monotoneCollarCoefficient (n : ℕ) :
    PhysicalCollarPartition.optimalCoefficient n ≤ monotoneCollarCoefficient n :=
  Finset.le_sup' _ (Finset.mem_range.mpr (by omega))

/-- Increasing the zero-grid cutoff cannot decrease this certificate. -/
theorem monotoneCollarCoefficient_monotone : Monotone monotoneCollarCoefficient := by
  intro n m hnm
  apply Finset.sup'_le
  intro k hk
  exact Finset.le_sup' _ (Finset.mem_range.mpr (by
    have h := Finset.mem_range.mp hk
    omega))

theorem monotoneCollarCoefficient_pos (n : ℕ) : 0 < monotoneCollarCoefficient n :=
  (PhysicalCollarPartition.optimalCoefficient_pos n).trans_le
    (optimalCoefficient_le_monotoneCollarCoefficient n)

/-- Every member of the finite envelope is tested against the same actual source. -/
theorem monotoneCollarCoefficient_source_energy (n : ℕ) (f : LogarithmicGridSource n) :
    ENNReal.ofReal (monotoneCollarCoefficient n * autocorr f.1 0) ≤
      ∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f.1) x := by
  have hm := Finset.exists_mem_eq_sup' (s := Finset.range (n + 1)) ⟨0, by simp⟩
    PhysicalCollarPartition.optimalCoefficient
  obtain ⟨k, hk, heq⟩ := hm
  have hkn : k ≤ n := by
    have h := Finset.mem_range.mp hk
    omega
  have hb := PhysicalCollarPartition.optimalCoefficient_source_energy_halfline (f.restrict hkn)
  change ENNReal.ofReal (PhysicalCollarPartition.optimalCoefficient k * autocorr f.1 0) ≤ _ at hb
  simpa only [monotoneCollarCoefficient, heq, LogarithmicGridSource.restrict] using hb

/-- Actual nonzero compact `C²` grid sources, with regularity and normalization only. -/
def SmoothLogarithmicGridSource (n : ℕ) :=
  {f : LogarithmicGridSource n // ContDiff ℝ 2 (f.1 : ℝ → ℝ) ∧ 0 < autocorr f.1 0}

/-- The certified monotone coefficient bounds the requested normalized energy. -/
theorem monotoneCollarCoefficient_le_normalized_energy (n : ℕ) (f : SmoothLogarithmicGridSource n) :
    monotoneCollarCoefficient n ≤ biScaleLevyEnergy f.1.1 / autocorr f.1.1 0 := by
  have hb := monotoneCollarCoefficient_source_energy n f.1
  have hi := integrableOn_biScaleLevyIntegrand f.2.1 f.1.1.hasCompactSupport
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun x => (autocorr f.1.1 0 - autocorr f.1.1 x) * archLevySinhWeight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (autocorr_sub_nonneg f.1.1.hasCompactSupport f.1.1.continuous x)
      (archLevySinhWeight_pos hx).le
  have he : ENNReal.ofReal (biScaleLevyEnergy f.1.1) =
      ∫⁻ x in Ioi 0, continuousArchIncrementDensity (compactAutocorrKernel f.1.1) x :=
    ofReal_integral_eq_lintegral_ofReal hi hn
  rw [← he] at hb
  exact (le_div_iff₀ f.2.2).2
    ((ENNReal.ofReal_le_ofReal_iff (biScaleLevyEnergy_nonneg
      f.1.1.hasCompactSupport f.1.1.continuous)).1 hb)

/-- Finite physical mass available outside the common origin collar. -/
def collarTailMass : ℝ := ∫ x in Ioi logarithmicCollarRadius, archLevySinhWeight x

theorem integrableOn_archWeight_collar_tail :
    IntegrableOn archLevySinhWeight (Ioi logarithmicCollarRadius) := by
  have hi := (integrableOn_mul_archLevySinhWeight.mono_set
    (show Ioi logarithmicCollarRadius ⊆ Ioi (0 : ℝ) from
      fun _ hx => logarithmicCollarRadius_pos.trans hx)).const_mul (1 / logarithmicCollarRadius)
  refine hi.mono' measurable_archLevySinhWeight.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hw := (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx)).le
  rw [Real.norm_eq_abs, abs_of_nonneg hw, one_div_mul_eq_div]
  apply (le_div_iff₀ logarithmicCollarRadius_pos).2
  change logarithmicCollarRadius < x at hx
  nlinarith [mul_le_mul_of_nonneg_right hx.le hw]

theorem optimalCoefficient_le_collarTailMass (n : ℕ) :
    PhysicalCollarPartition.optimalCoefficient n ≤ collarTailMass := by
  apply csSup_le
  · exact ⟨(PhysicalCollarPartition.equalMultiplicity n).coefficient,
      PhysicalCollarPartition.equalMultiplicity n, rfl⟩
  · rintro c ⟨ρ, rfl⟩
    refine ρ.coefficient_le_physical_mass.trans ?_
    apply setIntegral_mono_set integrableOn_archWeight_collar_tail
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx)).le
    · exact Filter.Eventually.of_forall fun _ hx => hx.1

/-- The monotone coefficients have an `N`-independent finite upper bound. -/
theorem monotoneCollarCoefficient_le_collarTailMass (n : ℕ) :
    monotoneCollarCoefficient n ≤ collarTailMass :=
  Finset.sup'_le _ _ (fun k _ => optimalCoefficient_le_collarTailMass k)

theorem monotoneCollarCoefficient_bddAbove : BddAbove (Set.range monotoneCollarCoefficient) :=
  ⟨collarTailMass, by rintro c ⟨n, rfl⟩; exact monotoneCollarCoefficient_le_collarTailMass n⟩

/-- Finite saturation value of the optimized certificate hierarchy. -/
def limitingCollarCoefficient : ℝ := ⨆ n, monotoneCollarCoefficient n

theorem limitingCollarCoefficient_bounds :
    0 < limitingCollarCoefficient ∧ limitingCollarCoefficient ≤ collarTailMass := by
  constructor
  · exact (monotoneCollarCoefficient_pos 0).trans_le
      (le_ciSup monotoneCollarCoefficient_bddAbove 0)
  · exact ciSup_le (fun n => monotoneCollarCoefficient_le_collarTailMass n)

/-- The certified bounds increase to a positive finite limit. -/
theorem monotoneCollarCoefficient_tendsto :
    Filter.Tendsto monotoneCollarCoefficient Filter.atTop (nhds limitingCollarCoefficient) :=
  tendsto_atTop_ciSup monotoneCollarCoefficient_monotone monotoneCollarCoefficient_bddAbove

end
end GaloisForLFunctions.BiScaleUncertainty
