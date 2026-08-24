import GaloisForLFunctions.HTGeometry.EvenWeightedSignCarrier
import GaloisForLFunctions.HTGeometry.InfiniteSupportPositiveAperture
import GaloisForLFunctions.HTGeometry.GlobalPowerTailSquareIntegrable
import GaloisForLFunctions.HTGeometry.PositiveReweightingSupport

open MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A nonzero atomless measure on the real line has infinite topological support. -/
theorem support_infinite_of_ne_zero_of_nullSingleton {μ : Measure ℝ}
    [NullSingletonClass μ] (hμ : μ ≠ 0) : μ.support.Infinite := by
  intro hfin
  have hsupp : μ μ.support = 0 := hfin.measure_zero μ
  have hcompl : μ μ.supportᶜ = 0 := mem_ae_iff.mp Measure.support_mem_ae
  have huniv : μ Set.univ = 0 := by
    apply le_zero_iff.mp
    rw [← Set.union_compl_self μ.support]
    exact (measure_union_le _ _).trans_eq (by simp [hsupp, hcompl])
  exact hμ (Measure.measure_univ_eq_zero.mp huniv)

/-- Positive even damping which makes every measurable signed-weight carrier finite without
changing its null sets. -/
def signedWeightFiniteDamping (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 + |t|) ^ (-2 : ℝ) / (1 + |w t|)

theorem signedWeightFiniteDamping_pos (w : ℝ → ℝ) (t : ℝ) :
    0 < signedWeightFiniteDamping w t := by
  unfold signedWeightFiniteDamping
  positivity

theorem measurable_signedWeightFiniteDamping {w : ℝ → ℝ} (hw : Measurable w) :
    Measurable (signedWeightFiniteDamping w) := by
  unfold signedWeightFiniteDamping
  fun_prop

theorem signedWeightFiniteDamping_even {w : ℝ → ℝ} (heven : ∀ t, w (-t) = w t) (t : ℝ) :
    signedWeightFiniteDamping w (-t) = signedWeightFiniteDamping w t := by
  simp [signedWeightFiniteDamping, heven]

abbrev finiteSignedWeightMeasure (w : ℝ → ℝ) : Measure ℝ :=
  (signedWeightMeasure w).withDensity (realDensity (signedWeightFiniteDamping w))

instance finiteSignedWeightMeasure_nullSingleton (w : ℝ → ℝ) :
    NullSingletonClass (finiteSignedWeightMeasure w) := by
  rw [finiteSignedWeightMeasure, signedWeightMeasure]
  infer_instance

theorem finiteSignedWeightMeasure_apply_eq_zero_iff {w : ℝ → ℝ} (hw : Measurable w)
    (s : Set ℝ) :
    finiteSignedWeightMeasure w s = 0 ↔ signedWeightMeasure w s = 0 := by
  exact measure_withDensity_eq_zero_iff (signedWeightMeasure w)
    (measurable_realDensity (measurable_signedWeightFiniteDamping hw))
    (Filter.Eventually.of_forall fun t => by
      simpa [realDensity] using signedWeightFiniteDamping_pos w t) s

theorem finiteSignedWeightMeasure_ne_zero_iff {w : ℝ → ℝ} (hw : Measurable w) :
    finiteSignedWeightMeasure w ≠ 0 ↔ signedWeightMeasure w ≠ 0 := by
  constructor
  · intro hfinite hsigned
    apply hfinite
    apply Measure.measure_univ_eq_zero.mp
    rw [finiteSignedWeightMeasure_apply_eq_zero_iff hw]
    exact Measure.measure_univ_eq_zero.mpr hsigned
  · intro hsigned hfinite
    apply hsigned
    apply Measure.measure_univ_eq_zero.mp
    rw [← finiteSignedWeightMeasure_apply_eq_zero_iff hw]
    exact Measure.measure_univ_eq_zero.mpr hfinite

theorem finiteSignedWeightMeasure_lt_top {w : ℝ → ℝ} (hw : Measurable w) :
    finiteSignedWeightMeasure w Set.univ < ∞ := by
  rw [finiteSignedWeightMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [signedWeightMeasure,
    lintegral_withDensity_eq_lintegral_mul₀
      (measurable_realDensity hw.abs).aemeasurable
      (measurable_realDensity (measurable_signedWeightFiniteDamping hw)).aemeasurable]
  apply lt_of_le_of_lt (lintegral_mono fun t => ?_)
    (lt_top_iff_ne_top.mpr (lintegral_oneAddAbsWeight_ne_top (by norm_num : (1 : ℝ) < 2)))
  rw [Pi.mul_apply, realDensity, realDensity, oneAddAbsWeight]
  have hnum : 0 ≤ |w t| := abs_nonneg _
  rw [← ENNReal.ofReal_mul hnum]
  apply ENNReal.ofReal_le_ofReal
  rw [signedWeightFiniteDamping]
  have hratio : |w t| / (1 + |w t|) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [abs_nonneg (w t)]
  calc
    |w t| * ((1 + |t|) ^ (-2 : ℝ) / (1 + |w t|)) =
        (1 + |t|) ^ (-2 : ℝ) * (|w t| / (1 + |w t|)) := by ring
    _ ≤ (1 + |t|) ^ (-2 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg (by positivity) _)
    _ = (1 + |t|) ^ (-2 : ℝ) := mul_one _

theorem finiteSignedWeightMeasure_isFinite {w : ℝ → ℝ} (hw : Measurable w) :
    IsFiniteMeasure (finiteSignedWeightMeasure w) := by
  rw [isFiniteMeasure_iff]
  exact finiteSignedWeightMeasure_lt_top hw

theorem map_neg_finiteSignedWeightMeasure {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    Measure.map (fun t : ℝ => -t) (finiteSignedWeightMeasure w) =
      finiteSignedWeightMeasure w := by
  rw [finiteSignedWeightMeasure,
    map_withDensity_of_involution measurable_neg (fun t => neg_neg t)
      (measurePreserving_neg_signedWeightMeasure hw heven).map_eq
      (measurable_realDensity (measurable_signedWeightFiniteDamping hw))]
  congr 1
  funext t
  simp [realDensity, signedWeightFiniteDamping_even heven]

theorem measurePreserving_neg_finiteSignedWeightMeasure {w : ℝ → ℝ} (hw : Measurable w)
    (heven : ∀ t, w (-t) = w t) :
    MeasurePreserving (fun t : ℝ => -t) (finiteSignedWeightMeasure w)
      (finiteSignedWeightMeasure w) :=
  ⟨measurable_neg, map_neg_finiteSignedWeightMeasure hw heven⟩

def weightStrictPositiveSet (w : ℝ → ℝ) : Set ℝ := {t | 0 < w t}

def weightStrictNegativeSet (w : ℝ → ℝ) : Set ℝ := {t | w t < 0}

theorem measurableSet_weightStrictPositiveSet {w : ℝ → ℝ} (hw : Measurable w) :
    MeasurableSet (weightStrictPositiveSet w) :=
  measurableSet_lt measurable_const hw

theorem measurableSet_weightStrictNegativeSet {w : ℝ → ℝ} (hw : Measurable w) :
    MeasurableSet (weightStrictNegativeSet w) :=
  measurableSet_lt hw measurable_const

theorem weightStrictPositiveSet_neg_mem_iff {w : ℝ → ℝ}
    (heven : ∀ t, w (-t) = w t) (t : ℝ) :
    -t ∈ weightStrictPositiveSet w ↔ t ∈ weightStrictPositiveSet w := by
  simp [weightStrictPositiveSet, heven]

theorem weightStrictNegativeSet_neg_mem_iff {w : ℝ → ℝ}
    (heven : ∀ t, w (-t) = w t) (t : ℝ) :
    -t ∈ weightStrictNegativeSet w ↔ t ∈ weightStrictNegativeSet w := by
  simp [weightStrictNegativeSet, heven]

theorem signedWeightMeasure_weightStrictPositiveSet_ne_zero {w : ℝ → ℝ}
    (hw : Measurable w) (hpos : 0 < volume (weightStrictPositiveSet w)) :
    signedWeightMeasure w (weightStrictPositiveSet w) ≠ 0 := by
  rw [signedWeightMeasure, ne_eq,
    withDensity_apply_eq_zero (measurable_signedWeightDensity hw)]
  intro hzero
  have hsub : weightStrictPositiveSet w ⊆
      {t | realDensity (fun u => |w u|) t ≠ 0} ∩ weightStrictPositiveSet w := by
    intro t ht
    exact ⟨by simpa [realDensity, weightStrictPositiveSet] using ht.ne', ht⟩
  exact hpos.ne' (measure_mono_null hsub hzero)

theorem signedWeightMeasure_weightStrictNegativeSet_ne_zero {w : ℝ → ℝ}
    (hw : Measurable w) (hneg : 0 < volume (weightStrictNegativeSet w)) :
    signedWeightMeasure w (weightStrictNegativeSet w) ≠ 0 := by
  rw [signedWeightMeasure, ne_eq,
    withDensity_apply_eq_zero (measurable_signedWeightDensity hw)]
  intro hzero
  have hsub : weightStrictNegativeSet w ⊆
      {t | realDensity (fun u => |w u|) t ≠ 0} ∩ weightStrictNegativeSet w := by
    intro t ht
    exact ⟨by simpa [realDensity, weightStrictNegativeSet] using ht.ne, ht⟩
  exact hneg.ne' (measure_mono_null hsub hzero)

theorem finiteSignedWeightMeasure_weightStrictPositiveSet_ne_zero {w : ℝ → ℝ}
    (hw : Measurable w) (hpos : 0 < volume (weightStrictPositiveSet w)) :
    finiteSignedWeightMeasure w (weightStrictPositiveSet w) ≠ 0 := by
  intro hzero
  exact signedWeightMeasure_weightStrictPositiveSet_ne_zero hw hpos
    ((finiteSignedWeightMeasure_apply_eq_zero_iff hw _).mp hzero)

theorem finiteSignedWeightMeasure_weightStrictNegativeSet_ne_zero {w : ℝ → ℝ}
    (hw : Measurable w) (hneg : 0 < volume (weightStrictNegativeSet w)) :
    finiteSignedWeightMeasure w (weightStrictNegativeSet w) ≠ 0 := by
  intro hzero
  exact signedWeightMeasure_weightStrictNegativeSet_ne_zero hw hneg
    ((finiteSignedWeightMeasure_apply_eq_zero_iff hw _).mp hzero)

/-- A nonnull measurable set invariant under reflection has nonnull positive half for every
reflection-invariant atomless measure. -/
theorem measure_inter_Ioi_zero_ne_zero_of_neg_invariant
    {μ : Measure ℝ} [NullSingletonClass μ] {s : Set ℝ}
    (hpres : MeasurePreserving (fun t : ℝ => -t) μ μ)
    (heven : ∀ t, -t ∈ s ↔ t ∈ s) (hs : μ s ≠ 0) :
    μ (s ∩ Set.Ioi 0) ≠ 0 := by
  intro hhalf
  have hreflected : μ ((fun t : ℝ => -t) ⁻¹' (s ∩ Set.Ioi 0)) = 0 :=
    hpres.preimage_null hhalf
  have hcover : s ⊆ (s ∩ Set.Ioi 0) ∪
      ((fun t : ℝ => -t) ⁻¹' (s ∩ Set.Ioi 0)) ∪ {0} := by
    intro t ht
    rcases lt_trichotomy t 0 with htneg | rfl | htpos
    · left; right
      exact ⟨(heven t).mpr ht, by simpa using htneg⟩
    · exact Or.inr rfl
    · left; left
      exact ⟨ht, htpos⟩
  apply hs
  exact measure_mono_null hcover
    (measure_union_null (measure_union_null hhalf hreflected) (measure_singleton 0))

theorem finiteSignedWeightMeasure_positiveHalf_ne_zero {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (hpos : 0 < volume (weightStrictPositiveSet w)) :
    finiteSignedWeightMeasure w (weightStrictPositiveSet w ∩ Set.Ioi 0) ≠ 0 := by
  exact measure_inter_Ioi_zero_ne_zero_of_neg_invariant
    (measurePreserving_neg_finiteSignedWeightMeasure hw heven)
    (weightStrictPositiveSet_neg_mem_iff heven)
    (finiteSignedWeightMeasure_weightStrictPositiveSet_ne_zero hw hpos)

theorem finiteSignedWeightMeasure_negativeHalf_ne_zero {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (hneg : 0 < volume (weightStrictNegativeSet w)) :
    finiteSignedWeightMeasure w (weightStrictNegativeSet w ∩ Set.Ioi 0) ≠ 0 := by
  exact measure_inter_Ioi_zero_ne_zero_of_neg_invariant
    (measurePreserving_neg_finiteSignedWeightMeasure hw heven)
    (weightStrictNegativeSet_neg_mem_iff heven)
    (finiteSignedWeightMeasure_weightStrictNegativeSet_ne_zero hw hneg)

def finiteSignedWeightHalfMeasure (w : ℝ → ℝ) (s : Set ℝ) : Measure ℝ :=
  (finiteSignedWeightMeasure w).restrict (s ∩ Set.Ioi 0)

instance finiteSignedWeightHalfMeasure_nullSingleton (w : ℝ → ℝ) (s : Set ℝ) :
    NullSingletonClass (finiteSignedWeightHalfMeasure w s) := by
  rw [finiteSignedWeightHalfMeasure]
  infer_instance

theorem finiteSignedWeightHalfMeasure_isFinite {w : ℝ → ℝ} (hw : Measurable w)
    (s : Set ℝ) : IsFiniteMeasure (finiteSignedWeightHalfMeasure w s) := by
  letI : IsFiniteMeasure (finiteSignedWeightMeasure w) :=
    finiteSignedWeightMeasure_isFinite hw
  rw [finiteSignedWeightHalfMeasure]
  infer_instance

theorem finiteSignedWeightHalfMeasure_ne_zero {w : ℝ → ℝ} {s : Set ℝ}
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) :
    finiteSignedWeightHalfMeasure w s ≠ 0 := by
  rw [finiteSignedWeightHalfMeasure, ne_eq, Measure.restrict_eq_zero]
  exact hs

theorem finiteSignedWeightHalfMeasure_support_infinite {w : ℝ → ℝ} {s : Set ℝ}
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) :
    (finiteSignedWeightHalfMeasure w s).support.Infinite :=
  support_infinite_of_ne_zero_of_nullSingleton
    (finiteSignedWeightHalfMeasure_ne_zero hs)

noncomputable def finiteSignedWeightHalfPiece (w : ℝ → ℝ) (s : Set ℝ)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) : Set ℝ :=
  infiniteSupportPositivePieces (finiteSignedWeightHalfMeasure w s)
      (finiteSignedWeightHalfMeasure_support_infinite hs) n ∩
    (s ∩ Set.Ioi 0)

theorem measurableSet_finiteSignedWeightHalfPiece {w : ℝ → ℝ} {s : Set ℝ}
    (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    MeasurableSet (finiteSignedWeightHalfPiece w s hs n) :=
  (measurableSet_infiniteSupportPositivePieces _ _ _).inter
    (hsmeas.inter measurableSet_Ioi)

theorem finiteSignedWeightHalfPiece_subset {w : ℝ → ℝ} {s : Set ℝ}
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    finiteSignedWeightHalfPiece w s hs n ⊆ s ∩ Set.Ioi 0 :=
  inter_subset_right

theorem finiteSignedWeightHalfPiece_pairwiseDisjoint {w : ℝ → ℝ} {s : Set ℝ}
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) :
    Set.PairwiseDisjoint Set.univ (finiteSignedWeightHalfPiece w s hs) := by
  intro n _ m _ hnm
  exact (infiniteSupportPositivePieces_pairwiseDisjoint
    (finiteSignedWeightHalfMeasure w s)
    (finiteSignedWeightHalfMeasure_support_infinite hs) hnm).mono inter_subset_left inter_subset_left

theorem finiteSignedWeightHalfPiece_halfMeasure_pos {w : ℝ → ℝ} {s : Set ℝ}
    (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    0 < finiteSignedWeightHalfMeasure w s (finiteSignedWeightHalfPiece w s hs n) := by
  rw [finiteSignedWeightHalfPiece,
    measure_inter_conull (mem_ae_iff.mp
      (show s ∩ Set.Ioi 0 ∈ ae (finiteSignedWeightHalfMeasure w s) by
        exact self_mem_ae_restrict (hsmeas.inter measurableSet_Ioi)))]
  exact measure_infiniteSupportPositivePieces_pos
    (finiteSignedWeightHalfMeasure w s)
    (finiteSignedWeightHalfMeasure_support_infinite hs)
    Measure.support_mem_ae n

theorem finiteSignedWeightHalfPiece_measure_pos {w : ℝ → ℝ} {s : Set ℝ}
    (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    0 < finiteSignedWeightMeasure w (finiteSignedWeightHalfPiece w s hs n) := by
  have h := finiteSignedWeightHalfPiece_halfMeasure_pos hsmeas hs n
  rw [finiteSignedWeightHalfMeasure,
    Measure.restrict_apply (measurableSet_finiteSignedWeightHalfPiece hsmeas hs n)] at h
  rw [inter_eq_left.mpr (finiteSignedWeightHalfPiece_subset hs n)] at h
  exact h

def evenizeRealSet (s : Set ℝ) : Set ℝ :=
  s ∪ (fun t : ℝ => -t) ⁻¹' s

theorem measurableSet_evenizeRealSet {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet (evenizeRealSet s) :=
  hs.union (hs.preimage measurable_neg)

theorem evenizeRealSet_neg_mem_iff (s : Set ℝ) (t : ℝ) :
    -t ∈ evenizeRealSet s ↔ t ∈ evenizeRealSet s := by
  simp only [evenizeRealSet, mem_union, mem_preimage, neg_neg]
  tauto

noncomputable def finiteSignedWeightEvenPiece (w : ℝ → ℝ) (s : Set ℝ)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) : Set ℝ :=
  evenizeRealSet (finiteSignedWeightHalfPiece w s hs n)

theorem measurableSet_finiteSignedWeightEvenPiece {w : ℝ → ℝ} {s : Set ℝ}
    (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    MeasurableSet (finiteSignedWeightEvenPiece w s hs n) :=
  measurableSet_evenizeRealSet (measurableSet_finiteSignedWeightHalfPiece hsmeas hs n)

theorem finiteSignedWeightEvenPiece_neg_mem_iff {w : ℝ → ℝ} {s : Set ℝ}
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) (t : ℝ) :
    -t ∈ finiteSignedWeightEvenPiece w s hs n ↔
      t ∈ finiteSignedWeightEvenPiece w s hs n :=
  evenizeRealSet_neg_mem_iff _ _

theorem finiteSignedWeightEvenPiece_pairwiseDisjoint {w : ℝ → ℝ} {s : Set ℝ}
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) :
    Set.PairwiseDisjoint Set.univ (finiteSignedWeightEvenPiece w s hs) := by
  intro n _ m _ hnm
  change Disjoint (finiteSignedWeightEvenPiece w s hs n)
    (finiteSignedWeightEvenPiece w s hs m)
  rw [Set.disjoint_left]
  intro t hn hm
  rcases hn with hn | hn <;> rcases hm with hm | hm
  · exact (Set.disjoint_left.mp
      (finiteSignedWeightHalfPiece_pairwiseDisjoint hs (Set.mem_univ n)
        (Set.mem_univ m) hnm)) hn hm
  · have htnpos := (finiteSignedWeightHalfPiece_subset hs n hn).2
    have htpos : 0 < t := htnpos
    have htneg : t < 0 := by
      have := (finiteSignedWeightHalfPiece_subset hs m hm).2
      simpa using this
    linarith
  · have htpos := (finiteSignedWeightHalfPiece_subset hs m hm).2
    have htpos' : 0 < t := htpos
    have htneg : t < 0 := by
      have := (finiteSignedWeightHalfPiece_subset hs n hn).2
      simpa using this
    linarith
  · exact (Set.disjoint_left.mp
      (finiteSignedWeightHalfPiece_pairwiseDisjoint hs (Set.mem_univ n)
        (Set.mem_univ m) hnm)) hn hm

theorem finiteSignedWeightEvenPiece_measure_pos {w : ℝ → ℝ} {s : Set ℝ}
    (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    0 < finiteSignedWeightMeasure w (finiteSignedWeightEvenPiece w s hs n) := by
  exact lt_of_lt_of_le (finiteSignedWeightHalfPiece_measure_pos hsmeas hs n)
    (measure_mono (show finiteSignedWeightHalfPiece w s hs n ⊆
      finiteSignedWeightEvenPiece w s hs n from subset_union_left))

theorem finiteSignedWeightEvenPiece_measure_ne_top {w : ℝ → ℝ} (hw : Measurable w)
    {s : Set ℝ} (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    finiteSignedWeightMeasure w (finiteSignedWeightEvenPiece w s hs n) ≠ ∞ := by
  letI : IsFiniteMeasure (finiteSignedWeightMeasure w) :=
    finiteSignedWeightMeasure_isFinite hw
  exact measure_ne_top _ _

noncomputable def finiteSignedWeightEvenVector (w : ℝ → ℝ) (hw : Measurable w) (s : Set ℝ)
    (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    Lp ℂ 2 (finiteSignedWeightMeasure w) :=
  normalizedIndicatorMeasure (finiteSignedWeightMeasure w)
    (finiteSignedWeightEvenPiece w s hs n)
    (measurableSet_finiteSignedWeightEvenPiece hsmeas hs n)
    (finiteSignedWeightEvenPiece_measure_ne_top hw hs n)

theorem finiteSignedWeightEvenVector_ae {w : ℝ → ℝ} (hw : Measurable w) {s : Set ℝ}
    (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    finiteSignedWeightEvenVector w hw s hsmeas hs n =ᵐ[finiteSignedWeightMeasure w]
      fun t => ((Real.sqrt ((finiteSignedWeightMeasure w).real
          (finiteSignedWeightEvenPiece w s hs n)))⁻¹ : ℂ) *
        (finiteSignedWeightEvenPiece w s hs n).indicator (fun _ => (1 : ℂ)) t :=
  normalizedIndicatorMeasure_ae _ _ _ _

theorem finiteSignedWeightEvenVector_orthonormal {w : ℝ → ℝ} (hw : Measurable w)
    {s : Set ℝ} (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) :
    Orthonormal ℂ (finiteSignedWeightEvenVector w hw s hsmeas hs) := by
  apply orthonormal_normalizedIndicatorMeasure (finiteSignedWeightMeasure w)
    (fun n => measurableSet_finiteSignedWeightEvenPiece hsmeas hs n)
    (finiteSignedWeightEvenPiece_measure_ne_top hw hs)
    (fun n => ?_)
    (finiteSignedWeightEvenPiece_pairwiseDisjoint hs)
  have hfin := finiteSignedWeightEvenPiece_measure_ne_top hw hs n
  have hne := (finiteSignedWeightEvenPiece_measure_pos hsmeas hs n).ne'
  exact lt_of_le_of_ne measureReal_nonneg ((measureReal_ne_zero_iff hfin).mpr hne).symm

noncomputable def measurableEvenSignedWeightVector {w : ℝ → ℝ} (hw : Measurable w)
    (s : Set ℝ) (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    SignedWeightL2 w :=
  densityMul (μ := signedWeightMeasure w) (signedWeightFiniteDamping w)
    (measurable_signedWeightFiniteDamping hw)
    (signedWeightFiniteDamping_pos w)
    (finiteSignedWeightEvenVector w hw s hsmeas hs n)

theorem measurableEvenSignedWeightVector_ae {w : ℝ → ℝ} (hw : Measurable w)
    {s : Set ℝ} (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    measurableEvenSignedWeightVector hw s hsmeas hs n =ᵐ[signedWeightMeasure w]
      fun t => sqrtWeight (signedWeightFiniteDamping w) t *
        (((Real.sqrt ((finiteSignedWeightMeasure w).real
          (finiteSignedWeightEvenPiece w s hs n)))⁻¹ : ℂ) *
        (finiteSignedWeightEvenPiece w s hs n).indicator (fun _ => (1 : ℂ)) t) := by
  have hv : (finiteSignedWeightEvenVector w hw s hsmeas hs n : ℝ → ℂ) =ᵐ[signedWeightMeasure w]
      fun t => ((Real.sqrt ((finiteSignedWeightMeasure w).real
          (finiteSignedWeightEvenPiece w s hs n)))⁻¹ : ℂ) *
        (finiteSignedWeightEvenPiece w s hs n).indicator (fun _ => (1 : ℂ)) t :=
    (withDensity_realDensity_ae_eq (measurable_signedWeightFiniteDamping hw)
      (signedWeightFiniteDamping_pos w)).mp
      (finiteSignedWeightEvenVector_ae hw hsmeas hs n)
  filter_upwards [densityMul_ae (μ := signedWeightMeasure w)
      (signedWeightFiniteDamping w) (measurable_signedWeightFiniteDamping hw)
      (signedWeightFiniteDamping_pos w) (finiteSignedWeightEvenVector w hw s hsmeas hs n), hv]
    with t hmul hvec
  change (densityMul (μ := signedWeightMeasure w) (signedWeightFiniteDamping w)
      (measurable_signedWeightFiniteDamping hw) (signedWeightFiniteDamping_pos w)
      (finiteSignedWeightEvenVector w hw s hsmeas hs n) : ℝ → ℂ) t = _
  rw [hmul, hvec]

theorem measurableEvenSignedWeightVector_orthonormal {w : ℝ → ℝ} (hw : Measurable w)
    {s : Set ℝ} (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) :
    Orthonormal ℂ (measurableEvenSignedWeightVector hw s hsmeas hs) := by
  have hv := finiteSignedWeightEvenVector_orthonormal hw hsmeas hs
  constructor
  · intro n
    exact (norm_densityMul (μ := signedWeightMeasure w)
      (signedWeightFiniteDamping w) (measurable_signedWeightFiniteDamping hw)
      (signedWeightFiniteDamping_pos w) (finiteSignedWeightEvenVector w hw s hsmeas hs n)).trans
        (hv.1 n)
  · intro n m hnm
    have hinner := (weightedDensityUnitary (μ := signedWeightMeasure w)
      (signedWeightFiniteDamping w) (measurable_signedWeightFiniteDamping hw)
      (signedWeightFiniteDamping_pos w)).inner_map_map
        (finiteSignedWeightEvenVector w hw s hsmeas hs n)
        (finiteSignedWeightEvenVector w hw s hsmeas hs m)
    rw [show measurableEvenSignedWeightVector hw s hsmeas hs n =
        weightedDensityUnitary (μ := signedWeightMeasure w)
          (signedWeightFiniteDamping w) (measurable_signedWeightFiniteDamping hw)
          (signedWeightFiniteDamping_pos w) (finiteSignedWeightEvenVector w hw s hsmeas hs n) from rfl,
      show measurableEvenSignedWeightVector hw s hsmeas hs m =
        weightedDensityUnitary (μ := signedWeightMeasure w)
          (signedWeightFiniteDamping w) (measurable_signedWeightFiniteDamping hw)
          (signedWeightFiniteDamping_pos w) (finiteSignedWeightEvenVector w hw s hsmeas hs m) from rfl,
      hinner]
    exact hv.2 hnm

theorem signedWeightReflection_measurableEvenSignedWeightVector {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    {s : Set ℝ} (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    signedWeightReflection hw heven (measurableEvenSignedWeightVector hw s hsmeas hs n) =
      measurableEvenSignedWeightVector hw s hsmeas hs n := by
  apply Lp.ext
  have hvec := measurableEvenSignedWeightVector_ae hw hsmeas hs n
  have hneg := hvec.comp_tendsto
    (measurePreserving_neg_signedWeightMeasure hw heven).quasiMeasurePreserving.tendsto_ae
  filter_upwards [signedWeightReflection_ae hw heven
      (measurableEvenSignedWeightVector hw s hsmeas hs n), hneg, hvec]
    with t href hneg hright
  rw [href]
  have hneg' :
      (measurableEvenSignedWeightVector hw s hsmeas hs n : ℝ → ℂ) (-t) =
        sqrtWeight (signedWeightFiniteDamping w) (-t) *
          (((Real.sqrt ((finiteSignedWeightMeasure w).real
            (finiteSignedWeightEvenPiece w s hs n)))⁻¹ : ℂ) *
          (finiteSignedWeightEvenPiece w s hs n).indicator (fun _ => (1 : ℂ)) (-t)) := by
    simpa [Function.comp_apply] using hneg
  rw [hneg', hright]
  have hind :
      (finiteSignedWeightEvenPiece w s hs n).indicator (fun _ => (1 : ℂ)) (-t) =
        (finiteSignedWeightEvenPiece w s hs n).indicator (fun _ => (1 : ℂ)) t := by
    by_cases ht : t ∈ finiteSignedWeightEvenPiece w s hs n
    · rw [Set.indicator_of_mem ht,
        Set.indicator_of_mem ((finiteSignedWeightEvenPiece_neg_mem_iff hs n t).mpr ht)]
    · rw [Set.indicator_of_notMem ht,
        Set.indicator_of_notMem (mt (finiteSignedWeightEvenPiece_neg_mem_iff hs n t).mp ht)]
  rw [hind]
  congr 1
  simp [sqrtWeight, signedWeightFiniteDamping_even heven]

noncomputable def measurableEvenSignedWeightVectorEven {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (s : Set ℝ) (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) (n : ℕ) :
    signedWeightEvenSubspace hw heven :=
  ⟨measurableEvenSignedWeightVector hw s hsmeas hs n,
    (mem_signedWeightEvenSubspace_iff hw heven _).mpr
      (signedWeightReflection_measurableEvenSignedWeightVector hw heven hsmeas hs n)⟩

theorem measurableEvenSignedWeightVectorEven_orthonormal {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    {s : Set ℝ} (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0) :
    Orthonormal ℂ (measurableEvenSignedWeightVectorEven hw heven s hsmeas hs) :=
  (measurableEvenSignedWeightVector_orthonormal hw hsmeas hs).codRestrict
    (signedWeightEvenSubspace hw heven)
    (fun n => (measurableEvenSignedWeightVectorEven hw heven s hsmeas hs n).property)

theorem finiteSignedWeightEvenPiece_subset_of_neg_invariant {w : ℝ → ℝ} {s : Set ℝ}
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0)
    (heven : ∀ t, -t ∈ s ↔ t ∈ s) (n : ℕ) :
    finiteSignedWeightEvenPiece w s hs n ⊆ s := by
  intro t ht
  rcases ht with ht | ht
  · exact (finiteSignedWeightHalfPiece_subset hs n ht).1
  · exact (heven t).mp (finiteSignedWeightHalfPiece_subset hs n ht).1

theorem measurableEvenSignedWeightVectorEven_mem_positiveSector {w : ℝ → ℝ}
    (hw : Measurable w) (hweven : ∀ t, w (-t) = w t)
    {s : Set ℝ} (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0)
    (hseven : ∀ t, -t ∈ s ↔ t ∈ s) (hpos : ∀ t ∈ s, 0 < w t) (n : ℕ) :
    measurableEvenSignedWeightVectorEven hw hweven s hsmeas hs n ∈
      weightPositiveSector hw hweven := by
  let v := measurableEvenSignedWeightVectorEven hw hweven s hsmeas hs n
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change (((weightPositiveProjection hw hweven v :
      signedWeightEvenSubspace hw hweven) : SignedWeightL2 w)) =
    ((v : signedWeightEvenSubspace hw hweven) : SignedWeightL2 w)
  apply Lp.ext
  filter_upwards [weightPositiveProjection_coeFn hw hweven v,
    measurableEvenSignedWeightVector_ae hw hsmeas hs n] with t hp hv
  rw [hp]
  change weightPositiveSymbol w t *
      (measurableEvenSignedWeightVector hw s hsmeas hs n : ℝ → ℂ) t =
    (measurableEvenSignedWeightVector hw s hsmeas hs n : ℝ → ℂ) t
  rw [hv]
  by_cases ht : t ∈ finiteSignedWeightEvenPiece w s hs n
  · have hwt : 0 < w t := hpos t
      (finiteSignedWeightEvenPiece_subset_of_neg_invariant hs hseven n ht)
    simp [weightPositiveSymbol, hwt, ht]
  · simp [weightPositiveSymbol, ht]

theorem measurableEvenSignedWeightVectorEven_mem_negativeSector {w : ℝ → ℝ}
    (hw : Measurable w) (hweven : ∀ t, w (-t) = w t)
    {s : Set ℝ} (hsmeas : MeasurableSet s)
    (hs : finiteSignedWeightMeasure w (s ∩ Set.Ioi 0) ≠ 0)
    (hseven : ∀ t, -t ∈ s ↔ t ∈ s) (hneg : ∀ t ∈ s, w t < 0) (n : ℕ) :
    measurableEvenSignedWeightVectorEven hw hweven s hsmeas hs n ∈
      weightNegativeSector hw hweven := by
  let v := measurableEvenSignedWeightVectorEven hw hweven s hsmeas hs n
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change (((weightNegativeProjection hw hweven v :
      signedWeightEvenSubspace hw hweven) : SignedWeightL2 w)) =
    ((v : signedWeightEvenSubspace hw hweven) : SignedWeightL2 w)
  apply Lp.ext
  filter_upwards [weightNegativeProjection_coeFn hw hweven v,
    measurableEvenSignedWeightVector_ae hw hsmeas hs n] with t hp hv
  rw [hp]
  change weightNegativeSymbol w t *
      (measurableEvenSignedWeightVector hw s hsmeas hs n : ℝ → ℂ) t =
    (measurableEvenSignedWeightVector hw s hsmeas hs n : ℝ → ℂ) t
  rw [hv]
  by_cases ht : t ∈ finiteSignedWeightEvenPiece w s hs n
  · have hwt : w t < 0 := hneg t
      (finiteSignedWeightEvenPiece_subset_of_neg_invariant hs hseven n ht)
    simp [weightNegativeSymbol, hwt, ht]
  · simp [weightNegativeSymbol, ht]

noncomputable def measurableWeightPositiveSectorVector {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (hpos : 0 < volume (weightStrictPositiveSet w)) (n : ℕ) :
    weightPositiveSector hw heven :=
  let hs := finiteSignedWeightMeasure_positiveHalf_ne_zero hw heven hpos
  ⟨measurableEvenSignedWeightVectorEven hw heven (weightStrictPositiveSet w)
      (measurableSet_weightStrictPositiveSet hw) hs n,
    measurableEvenSignedWeightVectorEven_mem_positiveSector hw heven
      (measurableSet_weightStrictPositiveSet hw) hs
      (weightStrictPositiveSet_neg_mem_iff heven)
      (fun _ ht => ht) n⟩

theorem measurableWeightPositiveSectorVector_orthonormal {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (hpos : 0 < volume (weightStrictPositiveSet w)) :
    Orthonormal ℂ (measurableWeightPositiveSectorVector hw heven hpos) := by
  let hs := finiteSignedWeightMeasure_positiveHalf_ne_zero hw heven hpos
  exact (measurableEvenSignedWeightVectorEven_orthonormal hw heven
    (measurableSet_weightStrictPositiveSet hw) hs).codRestrict
      (weightPositiveSector hw heven)
      (measurableEvenSignedWeightVectorEven_mem_positiveSector hw heven
        (measurableSet_weightStrictPositiveSet hw) hs
        (weightStrictPositiveSet_neg_mem_iff heven) (fun t ht => ht))

noncomputable def measurableWeightNegativeSectorVector {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (hneg : 0 < volume (weightStrictNegativeSet w)) (n : ℕ) :
    weightNegativeSector hw heven :=
  let hs := finiteSignedWeightMeasure_negativeHalf_ne_zero hw heven hneg
  ⟨measurableEvenSignedWeightVectorEven hw heven (weightStrictNegativeSet w)
      (measurableSet_weightStrictNegativeSet hw) hs n,
    measurableEvenSignedWeightVectorEven_mem_negativeSector hw heven
      (measurableSet_weightStrictNegativeSet hw) hs
      (weightStrictNegativeSet_neg_mem_iff heven)
      (fun _ ht => ht) n⟩

theorem measurableWeightNegativeSectorVector_orthonormal {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (hneg : 0 < volume (weightStrictNegativeSet w)) :
    Orthonormal ℂ (measurableWeightNegativeSectorVector hw heven hneg) := by
  let hs := finiteSignedWeightMeasure_negativeHalf_ne_zero hw heven hneg
  exact (measurableEvenSignedWeightVectorEven_orthonormal hw heven
    (measurableSet_weightStrictNegativeSet hw) hs).codRestrict
      (weightNegativeSector hw heven)
      (measurableEvenSignedWeightVectorEven_mem_negativeSector hw heven
        (measurableSet_weightStrictNegativeSet hw) hs
        (weightStrictNegativeSet_neg_mem_iff heven) (fun t ht => ht))

/-- Positive measure of the strict positive set forces an infinite-dimensional positive sector in
the literal even weighted carrier. -/
theorem weightPositiveSector_not_finiteDimensional_of_measure_pos {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (hpos : 0 < volume (weightStrictPositiveSet w)) :
    ¬ FiniteDimensional ℂ (weightPositiveSector hw heven) := by
  have hv := measurableWeightPositiveSectorVector_orthonormal hw heven hpos
  intro hfd
  letI : FiniteDimensional ℂ (weightPositiveSector hw heven) := hfd
  exact Module.Finite.not_linearIndependent_of_infinite
    (measurableWeightPositiveSectorVector hw heven hpos) hv.linearIndependent

/-- Positive measure of the strict negative set forces an infinite-dimensional negative sector in
the literal even weighted carrier. -/
theorem weightNegativeSector_not_finiteDimensional_of_measure_pos {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (hneg : 0 < volume (weightStrictNegativeSet w)) :
    ¬ FiniteDimensional ℂ (weightNegativeSector hw heven) := by
  have hv := measurableWeightNegativeSectorVector_orthonormal hw heven hneg
  intro hfd
  letI : FiniteDimensional ℂ (weightNegativeSector hw heven) := hfd
  exact Module.Finite.not_linearIndependent_of_infinite
    (measurableWeightNegativeSectorVector hw heven hneg) hv.linearIndependent

/-- Exact measurable version of bilateral infinite Krein index: no continuity or sign interval is
needed, only the two positive-measure sign sets supplied by the universal gauge theorem. -/
theorem evenWeightedCarrier_bilateral_infiniteKreinIndex_of_measure_pos {w : ℝ → ℝ}
    (hw : Measurable w) (heven : ∀ t, w (-t) = w t)
    (hpos : 0 < volume (weightStrictPositiveSet w))
    (hneg : 0 < volume (weightStrictNegativeSet w)) :
    (¬ FiniteDimensional ℂ (weightPositiveSector hw heven)) ∧
      (¬ FiniteDimensional ℂ (weightNegativeSector hw heven)) :=
  ⟨weightPositiveSector_not_finiteDimensional_of_measure_pos hw heven hpos,
    weightNegativeSector_not_finiteDimensional_of_measure_pos hw heven hneg⟩

end GaloisForLFunctions.HTGeometry
