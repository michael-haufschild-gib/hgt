import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffExponential
import Mathlib.MeasureTheory.Group.Measure

/-!
# Exact complex-time cutoff symbols at every derivative order

The real reciprocal frequency has both signs. Their two essential boundary
traces give the exact complex-time amplification exp(K * |Im t|), including
the sharp additional factor K^n for every time derivative.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The actual retained reciprocal frequency is odd under spectral reflection. -/
theorem cutoffPhaseFrequency_neg (a z : ℝ) :
    cutoffPhaseFrequency a (-z) = -cutoffPhaseFrequency a z := by
  by_cases hz : z ∈ cutoffPhaseSet a
  · have hn : -z ∈ cutoffPhaseSet a := by simpa only [cutoffPhaseSet,mem_setOf_eq,abs_neg] using hz
    rw [cutoffPhaseFrequency,indicator_of_mem hn,cutoffPhaseFrequency,indicator_of_mem hz]
    simp
  · have hn : -z ∉ cutoffPhaseSet a := by simpa only [cutoffPhaseSet,mem_setOf_eq,abs_neg] using hz
    rw [cutoffPhaseFrequency,indicator_of_notMem hn,cutoffPhaseFrequency,indicator_of_notMem hz,neg_zero]

/-- The literal complex-time phase and its n-th formal derivative symbol. -/
def cutoffComplexSymbol (a : ℝ) (n : ℕ) (τ : ℂ) (z : ℝ) : ℂ :=
  (-(cutoffPhaseFrequency a z : ℂ) * I)^n * Complex.exp (-τ * (cutoffPhaseFrequency a z : ℂ) * I)

/-- Exact pointwise modulus, before taking the essential supremum. -/
theorem norm_cutoffComplexSymbol (a z : ℝ) (τ : ℂ) (n : ℕ) :
    ‖cutoffComplexSymbol a n τ z‖ =
      |cutoffPhaseFrequency a z|^n * Real.exp (τ.im * cutoffPhaseFrequency a z) := by
  simp [cutoffComplexSymbol,norm_pow,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

/-- The complex-time derivative symbol is measurable in the actual spectral variable. -/
theorem measurable_cutoffComplexSymbol (a : ℝ) (n : ℕ) (τ : ℂ) :
    Measurable (cutoffComplexSymbol a n τ) := by
  have hm := measurable_cutoffPhaseFrequency a
  unfold cutoffComplexSymbol
  fun_prop

/-- Every derivative symbol has the sharp common complex-time upper bound. -/
theorem cutoffComplexSymbol_bound (a z : ℝ) (τ : ℂ) (n : ℕ) :
    ‖cutoffComplexSymbol a n τ z‖ ≤
      cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a) := by
  rw [norm_cutoffComplexSymbol]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (abs_cutoffPhaseFrequency_le a z) n)
    (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (pow_nonneg (cutoffPhaseBudget_pos a).le n)
  calc
    _ ≤ |τ.im * cutoffPhaseFrequency a z| := le_abs_self _
    _ = |τ.im| * |cutoffPhaseFrequency a z| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_cutoffPhaseFrequency_le a z) (abs_nonneg _)

/-- The actual complex-time derivative symbol as an ordinary L-infinity class. -/
def cutoffComplexLinfty (a : ℝ) (n : ℕ) (τ : ℂ) : Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound (measurable_cutoffComplexSymbol a n τ).aestronglyMeasurable
    (cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a))
    (.of_forall fun z => cutoffComplexSymbol_bound a z τ n)).toLp (cutoffComplexSymbol a n τ)

/-- The L-infinity representative is the literal derivative symbol almost everywhere. -/
theorem cutoffComplexLinfty_ae (a : ℝ) (n : ℕ) (τ : ℂ) :
    (cutoffComplexLinfty a n τ : ℝ → ℂ) =ᵐ[volume] cutoffComplexSymbol a n τ :=
  (memLp_top_of_bound (measurable_cutoffComplexSymbol a n τ).aestronglyMeasurable
    (cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a))
    (.of_forall fun z => cutoffComplexSymbol_bound a z τ n)).coeFn_toLp

/-- Both signed cutoff endpoints force the exact essential norm at every complex time and order. -/
theorem norm_cutoffComplexLinfty (a : ℝ) (n : ℕ) (τ : ℂ) :
    ‖cutoffComplexLinfty a n τ‖ =
      cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a) := by
  apply le_antisymm
  · rw [Lp.norm_def,eLpNorm_exponent_top]
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (pow_nonneg (cutoffPhaseBudget_pos a).le n) (Real.exp_pos _).le)
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [cutoffComplexLinfty_ae a n τ] with z hz
    rw [hz]
    exact cutoffComplexSymbol_bound a z τ n
  · let f : ℝ → ℝ := fun z => if 0 ≤ τ.im then ‖cutoffComplexSymbol a n τ z‖ else ‖cutoffComplexSymbol a n τ (-z)‖
    have hb : ∀ᵐ z ∂volume, ‖cutoffComplexSymbol a n τ z‖ ≤ ‖cutoffComplexLinfty a n τ‖ := by
      have h := ae_le_lpNorm_exponent_top (Lp.memLp (cutoffComplexLinfty a n τ))
      rw [← toReal_eLpNorm (Lp.memLp (cutoffComplexLinfty a n τ)).1,← Lp.norm_def] at h
      filter_upwards [h,cutoffComplexLinfty_ae a n τ] with z hz he
      rwa [he] at hz
    have hbf : ∀ᵐ z ∂volume, f z ≤ ‖cutoffComplexLinfty a n τ‖ := by
      by_cases ht : 0 ≤ τ.im
      · simpa only [f,if_pos ht] using hb
      · simpa only [f,if_neg ht] using (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hb
    have hc : ContinuousAt (fun z : ℝ => ((2*z)⁻¹)^n * Real.exp (|τ.im| * ((2*z)⁻¹))) (Real.exp a) := by
      fun_prop (disch := positivity)
    have ht : Tendsto f (𝓝[>] Real.exp a)
        (𝓝 (cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a))) := by
      apply hc.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hzpos : 0 < z := (Real.exp_pos a).trans hz
      have hm : z ∈ cutoffPhaseSet a := by
        change Real.exp a ≤ |z|
        rw [abs_of_pos hzpos]
        exact hz.le
      have he : cutoffPhaseFrequency a z = (2*z)⁻¹ := by
        rw [cutoffPhaseFrequency,indicator_of_mem hm]
      dsimp only [f]
      rw [norm_cutoffComplexSymbol,norm_cutoffComplexSymbol,cutoffPhaseFrequency_neg,abs_neg,he,
        abs_of_pos (by positivity : 0 < (2*z)⁻¹)]
      split_ifs with hb
      · rw [abs_of_nonneg hb]
      · rw [abs_of_neg (lt_of_not_ge hb)]
        congr 2
        ring
    by_contra hn
    have hlt : ‖cutoffComplexLinfty a n τ‖ <
        cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a) := lt_of_not_ge hn
    obtain ⟨d,hd,hI⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (ht.eventually_const_lt hlt)
    have hzero : volume {z : ℝ | ‖cutoffComplexLinfty a n τ‖ < f z} = 0 := by
      have h := hbf.mono fun z hz => not_lt.mpr hz
      simpa only [ae_iff,not_not] using h
    have hi := measure_mono_null hI hzero
    have hp : 0 < volume (Ioo (Real.exp a) d) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hd)
    exact hp.ne' hi

/-- The original real-time phase is exactly the zeroth complex-time symbol. -/
theorem cutoffComplexSymbol_zero_ofReal (a t z : ℝ) :
    cutoffComplexSymbol a 0 (t : ℂ) z = cutoffPhase a t z := by
  simp [cutoffComplexSymbol,cutoffPhase]

/-- The original real-time phase class is preserved literally. -/
theorem cutoffComplexLinfty_zero_ofReal (a t : ℝ) :
    cutoffComplexLinfty a 0 (t : ℂ) = cutoffPhaseLinfty a t := by
  apply Lp.ext
  filter_upwards [cutoffComplexLinfty_ae a 0 (t : ℂ),cutoffPhaseLinfty_ae a t] with z hz he
  rw [hz,he,cutoffComplexSymbol_zero_ofReal]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
