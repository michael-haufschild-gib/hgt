import GaloisForLFunctions.RHTower.StationaryRecurrencePointSpectrumScalingLaw
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewDistribution
import GaloisForLFunctions.HTGeometry.InfiniteHilbertDispersion
import GaloisForLFunctions.HTGeometry.CarriedAtomic
import GaloisForLFunctions.HTGeometry.LeafCauchyTransform

/-!
# No-gap support and exact upper edge of stationary quantum recurrence

For a countably carried probability energy law, survival-fidelity loss is exactly a
summable screw series on the ordered energy-gap packet.  Its compact relation hull is
connected, so the completed loss law has interval support.  Reflecting back to fidelity
and applying the exact point-spectrum scaling law identifies the upper support edge of
every stationary survival law with the square of total point-spectrum mass.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory Topology Polynomial BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- A continuous image of a compact measure support is exactly the support of the pushforward. -/
theorem support_map_eq_image_support_of_continuous_of_compact
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HereditarilyLindelofSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
    (mu : Measure X) [IsFiniteMeasure mu] {f : X → Y}
    (hf : Continuous f) (hcompact : IsCompact mu.support) :
    (Measure.map f mu).support = f '' mu.support := by
  have hclosed : IsClosed (f '' mu.support) := (hcompact.image hf).isClosed
  apply Set.Subset.antisymm
  · refine Measure.support_subset_of_isClosed hclosed ?_
    rw [mem_ae_iff, Measure.map_apply hf.measurable hclosed.measurableSet.compl]
    apply measure_mono_null _ Measure.measure_compl_support
    intro x hx
    simp only [Set.mem_preimage, Set.mem_compl_iff] at hx ⊢
    intro hxs
    exact hx ⟨x, hxs, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hVopen, hfxV⟩ := mem_nhds_iff.mp hU
    have hpreOpen : IsOpen (f ⁻¹' V) := hVopen.preimage hf
    have hpreNhd : f ⁻¹' V ∈ 𝓝 x := hpreOpen.mem_nhds hfxV
    have hpos : 0 < mu (f ⁻¹' V) :=
      (Measure.mem_support_iff_forall x).mp hx _ hpreNhd
    have hmapPos : 0 < Measure.map f mu V := by
      rw [Measure.map_apply hf.measurable hVopen.measurableSet]
      exact hpos
    exact lt_of_lt_of_le hmapPos (measure_mono hVU)

section CountablePacket

variable {I : Type*} [Countable I]

/-- Ordered-pair Born weight of a countable pure-point packet. -/
def purePointGapWeight (w : I → ℝ) (q : I × I) : ℝ :=
  w q.1 * w q.2

/-- Ordered energy gap of a countable pure-point packet. -/
def purePointGapFrequency (energy : I → ℝ) (q : I × I) : ℝ :=
  energy q.1 - energy q.2

/-- Countable pure-point survival amplitude. -/
def countablePurePointSurvivalAmplitude
    (w energy : I → ℝ) (t : ℝ) : ℂ :=
  ∑' i, (w i : ℂ) * Complex.exp (((t * energy i : ℝ) : ℂ) * Complex.I)

omit [Countable I] in theorem summable_purePointGapWeight
    {w : I → ℝ} (hw : Summable w) (hwnn : ∀ i, 0 ≤ w i) :
    Summable (purePointGapWeight w) := by
  change Summable (fun q : I × I => w q.1 * w q.2)
  exact hw.mul_of_nonneg hw hwnn hwnn

omit [Countable I] in theorem tsum_purePointGapWeight
    {w : I → ℝ} (hw : Summable w) (hwnn : ∀ i, 0 ≤ w i) :
    ∑' q, purePointGapWeight w q = (∑' i, w i) ^ 2 := by
  have hpair := summable_purePointGapWeight hw hwnn
  rw [hpair.tsum_prod]
  simp_rw [purePointGapWeight, tsum_mul_left]
  rw [tsum_mul_right]
  ring

omit [Countable I] in private theorem phase_norm (energy : I → ℝ) (t : ℝ) (i : I) :
    ‖Complex.exp (((t * energy i : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

omit [Countable I] in private theorem summable_weightedPhase
    {w energy : I → ℝ} (hw : Summable w) (hwnn : ∀ i, 0 ≤ w i) (t : ℝ) :
    Summable (fun i => (w i : ℂ) *
      Complex.exp (((t * energy i : ℝ) : ℂ) * Complex.I)) := by
  apply Summable.of_norm
  refine hw.congr fun i => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hwnn i), phase_norm, mul_one]

omit [Countable I] in private theorem phase_chord_sq
    (energy : I → ℝ) (t : ℝ) (i j : I) :
    ‖Complex.exp (((t * energy i : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((t * energy j : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      2 * (1 - Real.cos ((energy i - energy j) * t)) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  have hni : Complex.normSq
      (Complex.exp (((t * energy i : ℝ) : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, phase_norm]
    norm_num
  have hnj : Complex.normSq
      (Complex.exp (((t * energy j : ℝ) : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, phase_norm]
    norm_num
  have hre :
      (Complex.exp (((t * energy i : ℝ) : ℂ) * Complex.I) *
        starRingEnd ℂ (Complex.exp (((t * energy j : ℝ) : ℂ) * Complex.I))).re =
        Real.cos ((energy i - energy j) * t) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_add]
    rw [show (((t * energy i : ℝ) : ℂ) * Complex.I +
        ((t * energy j : ℝ) : ℂ) * -Complex.I) =
          ((((energy i - energy j) * t : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
    exact Complex.exp_ofReal_mul_I_re _
  rw [hni, hnj, hre]
  ring

omit [Countable I] in private theorem summable_weightedPhase_normSq
    {w energy : I → ℝ} (hw : Summable w) (t : ℝ) :
    Summable (fun i => w i *
      ‖Complex.exp (((t * energy i : ℝ) : ℂ) * Complex.I)‖ ^ 2) := by
  refine hw.congr fun i => ?_
  rw [phase_norm]
  norm_num

omit [Countable I] in private theorem summable_pairwisePhaseDispersion
    {w energy : I → ℝ} (hw : Summable w) (hwnn : ∀ i, 0 ≤ w i) (t : ℝ) :
    Summable (fun q : I × I => w q.1 * w q.2 *
      ‖Complex.exp (((t * energy q.1 : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((t * energy q.2 : ℝ) : ℂ) * Complex.I)‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
  · intro q
    exact mul_nonneg (mul_nonneg (hwnn q.1) (hwnn q.2)) (sq_nonneg _)
  · intro q
    have hdist :
        ‖Complex.exp (((t * energy q.1 : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((t * energy q.2 : ℝ) : ℂ) * Complex.I)‖ ≤ 2 := by
      calc
        _ ≤ ‖Complex.exp (((t * energy q.1 : ℝ) : ℂ) * Complex.I)‖ +
            ‖Complex.exp (((t * energy q.2 : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
        _ = 2 := by rw [phase_norm, phase_norm]; norm_num
    have hsq :
        ‖Complex.exp (((t * energy q.1 : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((t * energy q.2 : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg
        (Complex.exp (((t * energy q.1 : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((t * energy q.2 : ℝ) : ℂ) * Complex.I))]
    exact mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (hwnn q.1) (hwnn q.2))
  · simpa [purePointGapWeight, mul_comm, mul_left_comm, mul_assoc] using
      (summable_purePointGapWeight hw hwnn).mul_left 4

omit [Countable I] in
/-- Exact ordered-gap screw representation of countable pure-point survival loss. -/
theorem one_sub_normSq_countablePurePointSurvivalAmplitude_eq_screwSeries
    (w energy : I → ℝ) (hwnn : ∀ i, 0 ≤ w i)
    (hw : Summable w) (htotal : ∑' i, w i = 1) (t : ℝ) :
    1 - Complex.normSq (countablePurePointSurvivalAmplitude w energy t) =
      screwSeries (purePointGapWeight w) (purePointGapFrequency energy) t := by
  let phase : I → ℂ :=
    fun i => Complex.exp (((t * energy i : ℝ) : ℂ) * Complex.I)
  have hM := summable_weightedPhase_normSq (energy := energy) hw t
  have hV : Summable (fun i => w i • phase i) := by
    apply Summable.of_norm
    refine hw.congr fun i => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hwnn i)]
    change w i = w i * ‖Complex.exp (((t * energy i : ℝ) : ℂ) * Complex.I)‖
    rw [phase_norm, mul_one]
  have hD := summable_pairwisePhaseDispersion (energy := energy) hw hwnn t
  have hdisp := tsum_pairwise_hilbert_dispersion w phase hw hM hV hD
  have hphaseNorm : ∑' i, w i * ‖phase i‖ ^ 2 = 1 := by
    convert htotal using 1
    apply tsum_congr
    intro i
    rw [phase_norm]
    norm_num
  have hphaseSum : (∑' i, w i • phase i) =
      countablePurePointSurvivalAmplitude w energy t := by
    apply tsum_congr
    intro i
    simp [phase]
  have hpair :
      (∑' q : I × I, w q.1 * w q.2 * ‖phase q.1 - phase q.2‖ ^ 2) =
        2 * screwSeries (purePointGapWeight w) (purePointGapFrequency energy) t := by
    rw [screwSeries, ← tsum_mul_left]
    apply tsum_congr
    rintro ⟨i, j⟩
    rw [purePointGapWeight, purePointGapFrequency]
    dsimp only [phase]
    rw [phase_chord_sq]
    ring
  rw [hpair, htotal, hphaseNorm, hphaseSum] at hdisp
  rw [Complex.normSq_eq_norm_sq]
  linarith

/-- Largest completed pure-point survival deficit allowed by the exact relation hull. -/
def purePointDefectMax (w energy : I → ℝ) : ℝ :=
  screwHullMax (purePointGapWeight w) (purePointGapFrequency energy)

theorem purePointDefectMax_nonneg
    (w energy : I → ℝ) (hwnn : ∀ i, 0 ≤ w i) (hw : Summable w) :
    0 ≤ purePointDefectMax w energy := by
  exact screwHullMax_nonneg
    (fun q => mul_nonneg (hwnn q.1) (hwnn q.2))
    (summable_purePointGapWeight hw hwnn)

/-- Physical fidelity bounds force the maximal relation-hull deficit to be at most one. -/
theorem purePointDefectMax_le_one
    (w energy : I → ℝ) (hwnn : ∀ i, 0 ≤ w i)
    (hw : Summable w) (htotal : ∑' i, w i = 1) :
    purePointDefectMax w energy ≤ 1 := by
  let a : I × I → ℝ := purePointGapWeight w
  let omega : I × I → ℝ := purePointGapFrequency energy
  have hapos : ∀ q, 0 ≤ a q := fun q => mul_nonneg (hwnn q.1) (hwnn q.2)
  have hasum : Summable a := summable_purePointGapWeight hw hwnn
  have htime : ∀ t : ℝ, screwSeries a omega t ≤ 1 := by
    intro t
    rw [← one_sub_normSq_countablePurePointSurvivalAmplitude_eq_screwSeries
      w energy hwnn hw htotal t]
    exact sub_le_self 1 (Complex.normSq_nonneg _)
  have himage : screwSeries a omega '' Set.Ici (0 : ℝ) ⊆ Set.Iic 1 := by
    rintro _ ⟨t, _ht, rfl⟩
    exact htime t
  have hclosure : closure (screwSeries a omega '' Set.Ici (0 : ℝ)) ⊆ Set.Iic 1 :=
    closure_minimal himage isClosed_Iic
  have hmaxmem : screwHullMax a omega ∈
      closure (screwSeries a omega '' Set.Ici (0 : ℝ)) := by
    rw [closure_screwSeries_image_Ici hapos hasum 0]
    exact ⟨screwHullMax_nonneg hapos hasum, le_refl _⟩
  exact hclosure hmaxmem

/-- Continuous reflection of a real deficit into the physical fidelity interval. -/
def reflectedUnitIntervalPoint (x : ℝ) : SpectralReturnFidelityInterval :=
  ⟨max 0 (min 1 (1 - x)), by
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)⟩

theorem reflectedUnitIntervalPoint_continuous :
    Continuous reflectedUnitIntervalPoint := by
  apply Continuous.subtype_mk
  fun_prop

theorem reflectedUnitIntervalPoint_eq_one_sub {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (reflectedUnitIntervalPoint x : ℝ) = 1 - x := by
  simp only [reflectedUnitIntervalPoint, Subtype.coe_mk]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- Fidelity one as a point of the exact compact carrier. -/
def oneSpectralReturnFidelity : SpectralReturnFidelityInterval :=
  ⟨1, by simp⟩

/-- Lower endpoint of the completed fidelity interval of a normalized pure-point packet. -/
def purePointFidelityFloor
    (w energy : I → ℝ) (hwnn : ∀ i, 0 ≤ w i)
    (hw : Summable w) (htotal : ∑' i, w i = 1) :
    SpectralReturnFidelityInterval :=
  ⟨1 - purePointDefectMax w energy, by
    constructor
    · linarith [purePointDefectMax_le_one w energy hwnn hw htotal]
    · linarith [purePointDefectMax_nonneg w energy hwnn hw]⟩

/-- Completed fidelity law generated by the exact countable gap-relation hull. -/
def countablePurePointStationaryFidelityLaw
    (w energy : I → ℝ) (hwnn : ∀ i, 0 ≤ w i) (hw : Summable w) :
    ProbabilityMeasure SpectralReturnFidelityInterval :=
  let a : I × I → ℝ := purePointGapWeight w
  let omega : I × I → ℝ := purePointGapFrequency energy
  let hapos : ∀ q, 0 ≤ a q := fun q => mul_nonneg (hwnn q.1) (hwnn q.2)
  let hasum : Summable a := summable_purePointGapWeight (I := I) hw hwnn
  ProbabilityMeasure.map (screwValueLaw hapos hasum omega)
    (f := reflectedUnitIntervalPoint) reflectedUnitIntervalPoint_continuous.aemeasurable

private theorem reflectedUnitIntervalPoint_image_defectInterval
    (w energy : I → ℝ) (hwnn : ∀ i, 0 ≤ w i)
    (hw : Summable w) (htotal : ∑' i, w i = 1) :
    reflectedUnitIntervalPoint ''
        Set.Icc 0 (purePointDefectMax w energy) =
      Set.Icc (purePointFidelityFloor w energy hwnn hw htotal)
        oneSpectralReturnFidelity := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx1 : x ≤ 1 := hx.2.trans
      (purePointDefectMax_le_one w energy hwnn hw htotal)
    have href := reflectedUnitIntervalPoint_eq_one_sub hx.1 hx1
    constructor
    · change 1 - purePointDefectMax w energy ≤
        (reflectedUnitIntervalPoint x : ℝ)
      rw [href]
      exact sub_le_sub_left hx.2 1
    · change (reflectedUnitIntervalPoint x : ℝ) ≤ 1
      rw [href]
      exact sub_le_self 1 hx.1
  · intro hy
    let x : ℝ := 1 - (y : ℝ)
    have hx0 : 0 ≤ x := by
      change 0 ≤ 1 - (y : ℝ)
      exact sub_nonneg.mpr y.2.2
    have hxM : x ≤ purePointDefectMax w energy := by
      change 1 - (y : ℝ) ≤ purePointDefectMax w energy
      have hlow := hy.1
      change 1 - purePointDefectMax w energy ≤ (y : ℝ) at hlow
      linarith
    refine ⟨x, ⟨hx0, hxM⟩, ?_⟩
    apply Subtype.ext
    rw [reflectedUnitIntervalPoint_eq_one_sub hx0
      (hxM.trans (purePointDefectMax_le_one w energy hwnn hw htotal))]
    dsimp only [x]
    linarith

/-- No-gap law for a normalized countable pure-point packet: completed fidelity support is one
closed interval ending at one, with arbitrary frequency relations allowed. -/
theorem countablePurePointStationaryFidelityLaw_support
    (w energy : I → ℝ) (hwnn : ∀ i, 0 ≤ w i)
    (hw : Summable w) (htotal : ∑' i, w i = 1) :
    (countablePurePointStationaryFidelityLaw w energy hwnn hw :
      Measure SpectralReturnFidelityInterval).support =
      Set.Icc (purePointFidelityFloor w energy hwnn hw htotal)
        oneSpectralReturnFidelity := by
  let a : I × I → ℝ := purePointGapWeight w
  let omega : I × I → ℝ := purePointGapFrequency energy
  have hapos : ∀ q, 0 ≤ a q := fun q => mul_nonneg (hwnn q.1) (hwnn q.2)
  have hasum : Summable a := summable_purePointGapWeight hw hwnn
  rw [countablePurePointStationaryFidelityLaw,
    ProbabilityMeasure.toMeasure_map]
  rw [support_map_eq_image_support_of_continuous_of_compact
    (screwValueLaw hapos hasum omega : Measure ℝ)
    reflectedUnitIntervalPoint_continuous]
  · rw [screwValueLaw_support hapos hasum]
    exact reflectedUnitIntervalPoint_image_defectInterval w energy hwnn hw htotal
  · rw [screwValueLaw_support hapos hasum]
    exact isCompact_Icc

end CountablePacket

section CountablyCarriedSpectrum

/-- Born weight of one point in a chosen countable spectral carrier. -/
def carriedAtomWeight (mu : Measure ℝ) (F : Set ℝ) (i : ↥F) : ℝ :=
  (mu {(i : ℝ)}).toReal

/-- Energy coordinate of one point in a chosen countable spectral carrier. -/
def carriedAtomEnergy (F : Set ℝ) (i : ↥F) : ℝ :=
  (i : ℝ)

theorem carriedAtomWeight_nonneg
    (mu : Measure ℝ) (F : Set ℝ) (i : ↥F) :
    0 ≤ carriedAtomWeight mu F i :=
  ENNReal.toReal_nonneg

private theorem measure_carrier_eq_one
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {F : Set ℝ}
    (hFm : MeasurableSet F) (hcar : mu Fᶜ = 0) :
    mu F = 1 := by
  have hsplit := measure_add_measure_compl (μ := mu) hFm
  rw [hcar, add_zero, measure_univ] at hsplit
  exact hsplit

theorem summable_carriedAtomWeight
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : mu Fᶜ = 0) :
    Summable (carriedAtomWeight mu F) := by
  have hsumENN : ∑' i : ↥F, mu {(i : ℝ)} = 1 := by
    rw [← HTGeometry.measure_eq_tsum_singleton mu hF]
    exact measure_carrier_eq_one mu hFm hcar
  apply ENNReal.summable_toReal
  rw [hsumENN]
  exact ENNReal.one_ne_top

theorem tsum_carriedAtomWeight
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : mu Fᶜ = 0) :
    ∑' i : ↥F, carriedAtomWeight mu F i = 1 := by
  have hsumENN : ∑' i : ↥F, mu {(i : ℝ)} = 1 := by
    rw [← HTGeometry.measure_eq_tsum_singleton mu hF]
    exact measure_carrier_eq_one mu hFm hcar
  change ∑' i : ↥F, (mu {(i : ℝ)}).toReal = 1
  rw [← ENNReal.tsum_toReal_eq (fun i : ↥F => measure_ne_top mu {(i : ℝ)}), hsumENN]
  norm_num

/-- A countably carried probability spectrum is exactly its absolutely convergent atomic survival
amplitude. -/
theorem charFun_eq_countablePurePointSurvivalAmplitude_of_carried
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : mu Fᶜ = 0) (t : ℝ) :
    charFun mu t = countablePurePointSurvivalAmplitude
      (carriedAtomWeight mu F) (carriedAtomEnergy F) t := by
  have hmeasure := HTGeometry.measure_eq_fiberMeasure_of_carried mu hF hFm hcar
  let f : ℝ → ℂ := fun x => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
  have hintMu : Integrable f mu := by
    apply Integrable.of_bound (by dsimp only [f]; fun_prop) 1
    filter_upwards with x
    dsimp only [f]
    rw [Complex.norm_exp]
    simp
  have hintFiber : Integrable f
      (HTGeometry.fiberMeasure (fun x => (mu {x}).toReal) F) := by
    rwa [← hmeasure]
  rw [charFun_apply_real]
  change (∫ x, f x ∂mu) = _
  rw [hmeasure, HTGeometry.integral_fiberMeasure_vector _ _ f hintFiber]
  unfold countablePurePointSurvivalAmplitude
  apply tsum_congr
  intro i
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  simp only [carriedAtomWeight, carriedAtomEnergy, real_smul]
  have hcoef :
      ((HTGeometry.fiberMeasure (fun x => (mu {x}).toReal) F) {(i : ℝ)}).toReal =
        (mu {(i : ℝ)}).toReal := by
    exact congrArg ENNReal.toReal
      (congrArg (fun nu : Measure ℝ => nu {(i : ℝ)}) hmeasure).symm
  have hfi : f (i : ℝ) =
      Complex.exp ((((t * (i : ℝ) : ℝ)) : ℂ) * Complex.I) := by
    dsimp only [f]
    congr 1
    push_cast
    rfl
  rw [hcoef, hfi]

/-- Exact screw representation of survival loss for every countably carried probability energy
law. -/
theorem one_sub_normSq_charFun_eq_screwSeries_of_carried
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : mu Fᶜ = 0) (t : ℝ) :
    1 - Complex.normSq (charFun mu t) =
      screwSeries
        (purePointGapWeight (carriedAtomWeight mu F))
        (purePointGapFrequency (carriedAtomEnergy F)) t := by
  letI : Countable ↥F := hF.to_subtype
  rw [charFun_eq_countablePurePointSurvivalAmplitude_of_carried mu hF hFm hcar]
  exact one_sub_normSq_countablePurePointSurvivalAmplitude_eq_screwSeries
    (carriedAtomWeight mu F) (carriedAtomEnergy F)
    (carriedAtomWeight_nonneg mu F)
    (summable_carriedAtomWeight mu hF hFm hcar)
    (tsum_carriedAtomWeight mu hF hFm hcar) t

/-- Centered finite-window fidelity law generated through the ordered-gap phase packet. -/
def countablePurePointSampledFidelityLaw
    {I : Type*} [Countable I]
    (w energy : I → ℝ) (hwnn : ∀ i, 0 ≤ w i) (hw : Summable w) (A : ℝ) :
    ProbabilityMeasure SpectralReturnFidelityInterval :=
  let a : I × I → ℝ := purePointGapWeight w
  let omega : I × I → ℝ := purePointGapFrequency energy
  let hapos : ∀ q, 0 ≤ a q := fun q => mul_nonneg (hwnn q.1) (hwnn q.2)
  let hasum : Summable a := summable_purePointGapWeight (I := I) hw hwnn
  ProbabilityMeasure.map
    (ProbabilityMeasure.map
      (infiniteTorusPhaseProbabilityMeasure omega A)
      (f := screwValue a)
      (screwValue_continuous hapos hasum).aemeasurable)
    (f := reflectedUnitIntervalPoint)
    reflectedUnitIntervalPoint_continuous.aemeasurable

/-- For a countably carried spectrum, direct centered-time sampling and ordered-gap phase sampling
give exactly the same finite-window fidelity law. -/
theorem centeredSpectralReturnProbabilityMeasure_eq_countablePurePointSampled
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : mu Fᶜ = 0) (A : ℝ) :
    letI : Countable ↥F := hF.to_subtype
    centeredSpectralReturnProbabilityMeasure mu A =
      countablePurePointSampledFidelityLaw
        (carriedAtomWeight mu F) (carriedAtomEnergy F)
        (carriedAtomWeight_nonneg mu F)
        (summable_carriedAtomWeight mu hF hFm hcar) A := by
  letI : Countable ↥F := hF.to_subtype
  let w : ↥F → ℝ := carriedAtomWeight mu F
  let energy : ↥F → ℝ := carriedAtomEnergy F
  let a : ↥F × ↥F → ℝ := purePointGapWeight w
  let omega : ↥F × ↥F → ℝ := purePointGapFrequency energy
  have hwnn : ∀ i, 0 ≤ w i := carriedAtomWeight_nonneg mu F
  have hw : Summable w := summable_carriedAtomWeight mu hF hFm hcar
  have htotal : ∑' i, w i = 1 := tsum_carriedAtomWeight mu hF hFm hcar
  have hapos : ∀ q, 0 ≤ a q := fun q => mul_nonneg (hwnn q.1) (hwnn q.2)
  have hasum : Summable a := summable_purePointGapWeight hw hwnn
  have hpoint : ∀ u : ℝ,
      spectralReturnFidelityPoint mu (A * (2 * u - 1)) =
        reflectedUnitIntervalPoint
          (screwValue a (infiniteTorusPhasePoint omega A u)) := by
    intro u
    let t : ℝ := A * (2 * u - 1)
    have hvalue : screwValue a (infiniteTorusPhasePoint omega A u) =
        screwSeries a omega t := by
      rw [screwSeries_eq_screwValue]
      congr 1
      funext q
      simp only [infiniteTorusPhasePoint, screwPhase]
      dsimp only [t]
      ring_nf
    have hD0 : 0 ≤ screwSeries a omega t := screwSeries_nonneg hapos t
    have hD1 : screwSeries a omega t ≤ 1 := by
      rw [← one_sub_normSq_charFun_eq_screwSeries_of_carried
        mu hF hFm hcar t]
      exact sub_le_self 1 (Complex.normSq_nonneg _)
    apply Subtype.ext
    rw [hvalue, reflectedUnitIntervalPoint_eq_one_sub hD0 hD1]
    change Complex.normSq (charFun mu t) = 1 - screwSeries a omega t
    rw [← one_sub_normSq_charFun_eq_screwSeries_of_carried
      mu hF hFm hcar t]
    ring
  apply ProbabilityMeasure.toMeasure_injective
  unfold centeredSpectralReturnProbabilityMeasure
    centeredUniformClockProbabilityMeasure
    countablePurePointSampledFidelityLaw
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
      reflectedUnitIntervalPoint_continuous.measurable
      (screwValue_continuous hapos hasum).measurable,
    infiniteTorusPhaseProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_map
      (reflectedUnitIntervalPoint_continuous.measurable.comp
        (screwValue_continuous hapos hasum).measurable)
      (infiniteTorusPhasePoint_continuous omega A).measurable,
    Measure.map_map
      (spectralReturnFidelityPoint_continuous mu).measurable
      (by fun_prop)]
  change Measure.map
      (fun u => spectralReturnFidelityPoint mu (A * (2 * u - 1)))
        (unitIntervalProbabilityMeasure : Measure ℝ) =
    Measure.map
      (fun u => reflectedUnitIntervalPoint
        (screwValue a (infiniteTorusPhasePoint omega A u)))
        (infiniteTorusUnitIntervalProbabilityMeasure : Measure ℝ)
  have hbase :
      (unitIntervalProbabilityMeasure : Measure ℝ) =
        (infiniteTorusUnitIntervalProbabilityMeasure : Measure ℝ) := rfl
  rw [hbase]
  congr 1
  funext u
  exact hpoint u

/-- Countably carried spectra converge to the explicit compact-relation-hull fidelity law. -/
theorem centeredSpectralReturnProbabilityMeasure_tendsto_countablePurePointLaw
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : mu Fᶜ = 0) :
    letI : Countable ↥F := hF.to_subtype
    Tendsto (centeredSpectralReturnProbabilityMeasure mu) atTop
      (𝓝 (countablePurePointStationaryFidelityLaw
        (carriedAtomWeight mu F) (carriedAtomEnergy F)
        (carriedAtomWeight_nonneg mu F)
        (summable_carriedAtomWeight mu hF hFm hcar))) := by
  letI : Countable ↥F := hF.to_subtype
  let w : ↥F → ℝ := carriedAtomWeight mu F
  let energy : ↥F → ℝ := carriedAtomEnergy F
  let a : ↥F × ↥F → ℝ := purePointGapWeight w
  let omega : ↥F × ↥F → ℝ := purePointGapFrequency energy
  have hwnn : ∀ i, 0 ≤ w i := carriedAtomWeight_nonneg mu F
  have hw : Summable w := summable_carriedAtomWeight mu hF hFm hcar
  have hapos : ∀ q, 0 ≤ a q := fun q => mul_nonneg (hwnn q.1) (hwnn q.2)
  have hasum : Summable a := summable_purePointGapWeight hw hwnn
  have hdefect := tendsto_screwValueLaw hapos hasum omega
  have hreflect := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ _ hdefect reflectedUnitIntervalPoint_continuous
  apply hreflect.congr'
  filter_upwards with A
  exact centeredSpectralReturnProbabilityMeasure_eq_countablePurePointSampled
    mu hF hFm hcar A |>.symm

/-- The canonical stationary law of a countably carried spectrum is its explicit relation-hull
law. -/
theorem stationarySpectralReturnProbabilityMeasure_eq_countablePurePointLaw
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : mu Fᶜ = 0) :
    letI : Countable ↥F := hF.to_subtype
    stationarySpectralReturnProbabilityMeasure mu =
      countablePurePointStationaryFidelityLaw
        (carriedAtomWeight mu F) (carriedAtomEnergy F)
        (carriedAtomWeight_nonneg mu F)
        (summable_carriedAtomWeight mu hF hFm hcar) := by
  exact tendsto_nhds_unique
    (centeredSpectralReturnProbabilityMeasure_tendsto_stationary mu)
    (centeredSpectralReturnProbabilityMeasure_tendsto_countablePurePointLaw
      mu hF hFm hcar)

/-- No-gap stationary support law for every countably carried probability energy spectrum. -/
theorem stationarySpectralReturnProbabilityMeasure_support_of_countablyCarried
    (mu : Measure ℝ) [IsProbabilityMeasure mu] {F : Set ℝ}
    (hF : F.Countable) (hFm : MeasurableSet F) (hcar : mu Fᶜ = 0) :
    letI : Countable ↥F := hF.to_subtype
    (stationarySpectralReturnProbabilityMeasure mu :
      Measure SpectralReturnFidelityInterval).support =
      Set.Icc
        (purePointFidelityFloor
          (carriedAtomWeight mu F) (carriedAtomEnergy F)
          (carriedAtomWeight_nonneg mu F)
          (summable_carriedAtomWeight mu hF hFm hcar)
          (tsum_carriedAtomWeight mu hF hFm hcar))
        oneSpectralReturnFidelity := by
  letI : Countable ↥F := hF.to_subtype
  rw [stationarySpectralReturnProbabilityMeasure_eq_countablePurePointLaw
    mu hF hFm hcar]
  exact countablePurePointStationaryFidelityLaw_support
    (carriedAtomWeight mu F) (carriedAtomEnergy F)
    (carriedAtomWeight_nonneg mu F)
    (summable_carriedAtomWeight mu hF hFm hcar)
    (tsum_carriedAtomWeight mu hF hFm hcar)

end CountablyCarriedSpectrum

section ArbitrarySpectrum

theorem pointSpectrumMass_eq_measure_pointSpectrumSet
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    pointSpectrumMass mu = mu (pointSpectrumSet mu) := by
  simp [pointSpectrumMass, pointSpectrumFiniteMeasure]

/-- When atomic mass is nonzero, its normalization is carried by the original point spectrum. -/
theorem normalizedPointSpectrumLaw_carried_of_mass_ne_zero
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hp : pointSpectrumMass mu ≠ 0) :
    (normalizedPointSpectrumLaw mu : Measure ℝ) (pointSpectrumSet mu)ᶜ = 0 := by
  have hfinite : pointSpectrumFiniteMeasure mu ≠ 0 := by
    intro hzero
    apply hp
    rw [pointSpectrumMass]
    exact congrArg (fun nu : Measure ℝ => nu Set.univ)
      (congrArg FiniteMeasure.toMeasure hzero)
  change ((pointSpectrumFiniteMeasure mu).normalize : Measure ℝ)
      (pointSpectrumSet mu)ᶜ = 0
  rw [(pointSpectrumFiniteMeasure mu).toMeasure_normalize_eq_of_nonzero hfinite]
  rw [Measure.smul_apply]
  simp [pointSpectrumFiniteMeasure,
    Measure.restrict_apply (pointSpectrumSet_measurable mu).compl]

/-- Nonnegative fidelity scaling sends a closed fidelity interval onto the interval between
the scaled endpoints, including the zero-scale branch. -/
private theorem pointSpectrumFidelityScale_image_Icc
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (a : SpectralReturnFidelityInterval) (ha : a ≤ oneSpectralReturnFidelity) :
    pointSpectrumFidelityScale mu '' Set.Icc a oneSpectralReturnFidelity =
      Set.Icc (pointSpectrumFidelityScale mu a)
        (pointSpectrumFidelityScale mu oneSpectralReturnFidelity) := by
  let c : ℝ := pointSpectrumMassReal mu ^ 2
  have hc : 0 ≤ c := sq_nonneg _
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · change c * (a : ℝ) ≤ c * (x : ℝ)
      exact mul_le_mul_of_nonneg_left hx.1 hc
    · change c * (x : ℝ) ≤ c * (oneSpectralReturnFidelity : ℝ)
      exact mul_le_mul_of_nonneg_left hx.2 hc
  · intro hy
    by_cases hc0 : c = 0
    · refine ⟨a, ⟨le_rfl, ha⟩, ?_⟩
      apply Subtype.ext
      change c * (a : ℝ) = (y : ℝ)
      have hylow := hy.1
      have hyhigh := hy.2
      change c * (a : ℝ) ≤ (y : ℝ) at hylow
      change (y : ℝ) ≤ c * (oneSpectralReturnFidelity : ℝ) at hyhigh
      rw [hc0, zero_mul] at hylow hyhigh ⊢
      linarith
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      let x : SpectralReturnFidelityInterval :=
        ⟨(y : ℝ) / c, by
          constructor
          · exact div_nonneg y.2.1 hc
          · have hyhigh := hy.2
            change (y : ℝ) ≤ c * (oneSpectralReturnFidelity : ℝ) at hyhigh
            change (y : ℝ) / c ≤ 1
            rw [div_le_iff₀ hcpos]
            simpa [oneSpectralReturnFidelity] using hyhigh⟩
      refine ⟨x, ?_, ?_⟩
      · constructor
        · have hylow := hy.1
          change c * (a : ℝ) ≤ (y : ℝ) at hylow
          change (a : ℝ) ≤ (y : ℝ) / c
          rw [le_div_iff₀ hcpos]
          simpa [mul_comm] using hylow
        · exact x.2.2
      · apply Subtype.ext
        change c * ((y : ℝ) / c) = (y : ℝ)
        field_simp

private theorem zeroSpectralReturnProbabilityMeasure_support :
    (zeroSpectralReturnProbabilityMeasure :
      Measure SpectralReturnFidelityInterval).support =
      {zeroSpectralReturnFidelity} := by
  ext x
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro hx
    by_contra hne
    have hU : {zeroSpectralReturnFidelity}ᶜ ∈ 𝓝 x :=
      isOpen_compl_singleton.mem_nhds hne
    have hpos := hx _ hU
    simp [zeroSpectralReturnProbabilityMeasure] at hpos
  · intro hx U hU
    rw [Set.mem_singleton_iff] at hx
    subst x
    have hmem : zeroSpectralReturnFidelity ∈ U := mem_of_mem_nhds hU
    simp [zeroSpectralReturnProbabilityMeasure, hmem]

/-- **Universal no-gap stationary-support law.** For every probability energy spectrum there is
a lower fidelity endpoint such that the complete stationary survival-fidelity support is exactly
one closed interval.  Its upper endpoint is the square-mass scaling of perfect pure-point return. -/
theorem exists_stationarySpectralReturnProbabilityMeasure_support_Icc
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ∃ rho : SpectralReturnFidelityInterval,
      (stationarySpectralReturnProbabilityMeasure mu :
        Measure SpectralReturnFidelityInterval).support =
        Set.Icc rho
          (pointSpectrumFidelityScale mu oneSpectralReturnFidelity) := by
  by_cases hp : pointSpectrumMass mu = 0
  · have hcarrierZero : mu (pointSpectrumSet mu) = 0 := by
      rw [← pointSpectrumMass_eq_measure_pointSpectrumSet mu, hp]
    letI : NullSingletonClass mu :=
      ⟨fun x => by
        by_contra hx
        have hsubset : {x} ⊆ pointSpectrumSet mu := by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          exact hx
        exact hx (measure_mono_null hsubset hcarrierZero)⟩
    refine ⟨zeroSpectralReturnFidelity, ?_⟩
    rw [stationarySpectralReturnProbabilityMeasure_eq_zero_of_noAtoms,
      zeroSpectralReturnProbabilityMeasure_support]
    have hscale :
        pointSpectrumFidelityScale mu oneSpectralReturnFidelity =
          zeroSpectralReturnFidelity := by
      apply Subtype.ext
      simp [pointSpectrumFidelityScale, pointSpectrumMassReal, hp,
        oneSpectralReturnFidelity, zeroSpectralReturnFidelity]
    rw [hscale]
    ext x
    simp [le_antisymm_iff]
  · let F : Set ℝ := pointSpectrumSet mu
    have hF : F.Countable := pointSpectrumSet_countable mu
    have hFm : MeasurableSet F := pointSpectrumSet_measurable mu
    have hcar :
        (normalizedPointSpectrumLaw mu : Measure ℝ) Fᶜ = 0 :=
      normalizedPointSpectrumLaw_carried_of_mass_ne_zero mu hp
    letI : Countable ↥F := hF.to_subtype
    let w : ↥F → ℝ :=
      carriedAtomWeight (normalizedPointSpectrumLaw mu : Measure ℝ) F
    let energy : ↥F → ℝ := carriedAtomEnergy F
    have hwnn : ∀ i, 0 ≤ w i :=
      carriedAtomWeight_nonneg (normalizedPointSpectrumLaw mu : Measure ℝ) F
    have hw : Summable w :=
      summable_carriedAtomWeight
        (normalizedPointSpectrumLaw mu : Measure ℝ) hF hFm hcar
    have htotal : ∑' i, w i = 1 :=
      tsum_carriedAtomWeight
        (normalizedPointSpectrumLaw mu : Measure ℝ) hF hFm hcar
    let rho0 : SpectralReturnFidelityInterval :=
      purePointFidelityFloor w energy hwnn hw htotal
    refine ⟨pointSpectrumFidelityScale mu rho0, ?_⟩
    rw [stationarySpectralReturnProbabilityMeasure_eq_scaledPointSpectrum,
      scaledPointSpectrumStationaryReturnLaw,
      ProbabilityMeasure.toMeasure_map]
    rw [support_map_eq_image_support_of_continuous_of_compact
      (stationarySpectralReturnProbabilityMeasure
        (normalizedPointSpectrumLaw mu : Measure ℝ) :
          Measure SpectralReturnFidelityInterval)
      (pointSpectrumFidelityScale_continuous mu)]
    · have hsupp :=
        stationarySpectralReturnProbabilityMeasure_support_of_countablyCarried
          (normalizedPointSpectrumLaw mu : Measure ℝ) hF hFm hcar
      change pointSpectrumFidelityScale mu ''
          (stationarySpectralReturnProbabilityMeasure
            (normalizedPointSpectrumLaw mu : Measure ℝ) :
              Measure SpectralReturnFidelityInterval).support = _
      rw [hsupp]
      exact pointSpectrumFidelityScale_image_Icc mu rho0 rho0.2.2
    · exact Measure.isClosed_support.isCompact

/-- The universal support endpoint is exactly squared total bound-state mass. -/
theorem coe_pointSpectrumFidelityScale_one
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ((pointSpectrumFidelityScale mu oneSpectralReturnFidelity :
      SpectralReturnFidelityInterval) : ℝ) =
      pointSpectrumMassReal mu ^ 2 := by
  simp [pointSpectrumFidelityScale, oneSpectralReturnFidelity]

/-- Total point-spectrum mass is recovered exactly from the stationary support edge. -/
theorem pointSpectrumMassReal_eq_sqrt_stationarySupportEdge
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    pointSpectrumMassReal mu =
      Real.sqrt
        ((pointSpectrumFidelityScale mu oneSpectralReturnFidelity :
          SpectralReturnFidelityInterval) : ℝ) := by
  rw [coe_pointSpectrumFidelityScale_one]
  rw [Real.sqrt_sq_eq_abs,
    abs_of_nonneg (pointSpectrumMassReal_mem_unitInterval mu).1]

/-- Exact upper-edge characterization: the scaled perfect-return point belongs to stationary
support and dominates every other support point. -/
theorem pointSpectrumFidelityScale_one_is_stationarySupportMaximum
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    pointSpectrumFidelityScale mu oneSpectralReturnFidelity ∈
        (stationarySpectralReturnProbabilityMeasure mu :
          Measure SpectralReturnFidelityInterval).support ∧
      ∀ x ∈ (stationarySpectralReturnProbabilityMeasure mu :
          Measure SpectralReturnFidelityInterval).support,
        x ≤ pointSpectrumFidelityScale mu oneSpectralReturnFidelity := by
  obtain ⟨rho, hsupp⟩ :=
    exists_stationarySpectralReturnProbabilityMeasure_support_Icc mu
  rw [hsupp]
  constructor
  · exact ⟨by
      have hrho : rho ≤ pointSpectrumFidelityScale mu oneSpectralReturnFidelity := by
        have hnonempty :
            (stationarySpectralReturnProbabilityMeasure mu :
              Measure SpectralReturnFidelityInterval).support.Nonempty :=
          Measure.nonempty_support (by
            intro hzero
            have hmass := congrArg
              (fun nu : Measure SpectralReturnFidelityInterval => nu Set.univ) hzero
            simp at hmass)
        rw [hsupp, Set.nonempty_Icc] at hnonempty
        exact hnonempty
      exact hrho, le_rfl⟩
  · intro x hx
    exact hx.2

/-- **Closed capstone: no-gap recurrence and exact bound-state-mass inversion.** For every
probability energy law, stationary survival fidelity fills one closed interval; its maximum is the
square of total point-spectrum mass, and that mass is recovered by taking the square root. -/
theorem universalStationaryRecurrenceNoGapBoundStateMassLaw :
    ∀ mu : ProbabilityMeasure ℝ,
      ∃ rho : SpectralReturnFidelityInterval,
        (stationarySpectralReturnProbabilityMeasure (mu : Measure ℝ) :
            Measure SpectralReturnFidelityInterval).support =
            Set.Icc rho
              (pointSpectrumFidelityScale (mu : Measure ℝ)
                oneSpectralReturnFidelity) ∧
        pointSpectrumFidelityScale (mu : Measure ℝ) oneSpectralReturnFidelity ∈
          (stationarySpectralReturnProbabilityMeasure (mu : Measure ℝ) :
            Measure SpectralReturnFidelityInterval).support ∧
        (∀ x ∈ (stationarySpectralReturnProbabilityMeasure (mu : Measure ℝ) :
            Measure SpectralReturnFidelityInterval).support,
          x ≤ pointSpectrumFidelityScale (mu : Measure ℝ)
            oneSpectralReturnFidelity) ∧
        pointSpectrumMassReal (mu : Measure ℝ) =
          Real.sqrt
            ((pointSpectrumFidelityScale (mu : Measure ℝ)
              oneSpectralReturnFidelity : SpectralReturnFidelityInterval) : ℝ) := by
  intro mu
  obtain ⟨rho, hsupp⟩ :=
    exists_stationarySpectralReturnProbabilityMeasure_support_Icc
      (mu : Measure ℝ)
  have hmax :=
    pointSpectrumFidelityScale_one_is_stationarySupportMaximum
      (mu : Measure ℝ)
  exact ⟨rho, hsupp, hmax.1, hmax.2,
    pointSpectrumMassReal_eq_sqrt_stationarySupportEdge (mu : Measure ℝ)⟩

end ArbitrarySpectrum

end RHTower
