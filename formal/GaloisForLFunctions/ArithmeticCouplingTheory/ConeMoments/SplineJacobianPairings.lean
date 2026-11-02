import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineNumeratorIdentities
import GaloisForLFunctions.RHTower.Sieve.PhaseIntegral

/-!
# Near-biorthogonality of spline moment derivatives

Pairing a shifted spline derivative with the bounded reciprocal primitive
recovers the ordinary Fourier Gram up to endpoint terms. Pairing with the
conjugate primitive instead gives the positive-frequency Blaschke integral.
Consequently only unshifted frequency differences need quantitative separation.
All estimates hold uniformly over translated intervals.
-/

open Finset Complex
open scoped Interval
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments


lemma hasDerivAt_conj_splineDual {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (x : ℝ) :
    HasDerivAt (fun y => (starRingEnd ℂ) (splineDual δ s y))
      ((starRingEnd ℂ) (-phase (-s) x/Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I)^8)) x := by
  exact Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_splineDual_exact hδ hs x)

lemma hasDerivAt_spline_pair {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (t x : ℝ) :
    HasDerivAt (fun y => shiftedSplineNumerator δ t y*splineDual δ s y)
      (shiftedSplineSlope δ t x*splineDual δ s x-phase (t-s) x) x := by
  have h := (hasDerivAt_shiftedSplineNumerator δ t x).mul
    (hasDerivAt_splineDual_exact hδ hs x)
  have he : shiftedSplineNumerator δ t x*
      (-phase (-s) x/Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I)^8)=-phase (t-s) x := by
    rw [shiftedSplineNumerator_eq]
    have hbase := spline_sinh_ne_zero hδ x
    have hp : phase (t-s) x=phase t x*phase (-s) x := by
      rw [sub_eq_add_neg, phase_freq_add]
    rw [hp]
    field_simp [hbase]
  rw [he] at h
  exact h

lemma hasDerivAt_spline_conj_pair {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (t x : ℝ) :
    HasDerivAt (fun y => shiftedSplineNumerator δ t y*(starRingEnd ℂ) (splineDual δ s y))
      (shiftedSplineSlope δ t x*(starRingEnd ℂ) (splineDual δ s x)-
        phase (t+s) x*splineBlaschke δ x) x := by
  have h := (hasDerivAt_shiftedSplineNumerator δ t x).mul
    (hasDerivAt_conj_splineDual hδ hs x)
  have he : shiftedSplineNumerator δ t x*
      ((starRingEnd ℂ) (-phase (-s) x/Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I)^8))=
      -(phase (t+s) x*splineBlaschke δ x) := by
    have hp : (starRingEnd ℂ) (phase (-s) x)=phase s x := by
      change star (phase (-s) x)=phase s x
      simpa only [neg_neg] using (phase_neg (-s) x).symm
    rw [shiftedSplineNumerator_eq, map_div₀, map_neg, hp,
      splineBlaschke_eq_sinh_ratio hδ, phase_freq_add]
    ring
  rw [he] at h
  exact h

def splineNumeratorBound (δ : ℝ) : ℝ := ∑ j : Fin 9, |splineCoefficient δ j|

def splinePairBoundaryBound (δ s : ℝ) : ℝ :=
  splineNumeratorBound δ*((splineInvScale δ/(s+8))*(1/(1-splineRatio δ)^8))

lemma splineNumeratorBound_nonneg (δ : ℝ) : 0 ≤ splineNumeratorBound δ :=
  sum_nonneg fun _ _ => abs_nonneg _

lemma norm_shiftedSplineNumerator_le (δ t x : ℝ) :
    ‖shiftedSplineNumerator δ t x‖ ≤ splineNumeratorBound δ := by
  refine (norm_sum_le _ _).trans ?_
  apply sum_le_sum
  intro j _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, phase_norm, mul_one]

lemma norm_spline_pair_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (t x : ℝ) :
    ‖shiftedSplineNumerator δ t x*splineDual δ s x‖ ≤ splinePairBoundaryBound δ s := by
  rw [norm_mul]
  exact mul_le_mul (norm_shiftedSplineNumerator_le δ t x)
    (norm_splineDual_le hδ (by linarith only [hs]) x) (norm_nonneg _) (splineNumeratorBound_nonneg δ)

lemma norm_spline_conj_pair_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (t x : ℝ) :
    ‖shiftedSplineNumerator δ t x*(starRingEnd ℂ) (splineDual δ s x)‖ ≤
      splinePairBoundaryBound δ s := by
  rw [norm_mul, Complex.norm_conj, ← norm_mul]
  exact norm_spline_pair_le hδ hs t x

lemma continuous_shiftedSplineSlope (δ t : ℝ) : Continuous (shiftedSplineSlope δ t) := by
  unfold shiftedSplineSlope
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_phase (t+splineShift j))

lemma continuous_splineDual {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    Continuous (splineDual δ s) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_splineDual_exact hδ hs x).continuousAt

lemma continuous_conj_splineDual {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    Continuous (fun x => (starRingEnd ℂ) (splineDual δ s x)) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_conj_splineDual hδ hs x).continuousAt

/-- The ordinary pairing differs from the unshifted Fourier Gram by endpoint terms. -/
theorem norm_integral_spline_pair_sub_phase_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (t a b : ℝ) :
    ‖(∫ x in a..b, shiftedSplineSlope δ t x*splineDual δ s x)-
      (∫ x in a..b, phase (t-s) x)‖ ≤ 2*splinePairBoundaryBound δ s := by
  have hi : IntervalIntegrable (fun x => shiftedSplineSlope δ t x*splineDual δ s x)
      MeasureTheory.volume a b :=
    ((continuous_shiftedSplineSlope δ t).mul (continuous_splineDual hδ hs)).intervalIntegrable a b
  have hp : IntervalIntegrable (phase (t-s)) MeasureTheory.volume a b :=
    (continuous_phase (t-s)).intervalIntegrable a b
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_spline_pair hδ hs t x) (hi.sub hp)
  rw [intervalIntegral.integral_sub hi hp] at he
  rw [he]
  exact (norm_sub_le _ _).trans (by
    have ha := norm_spline_pair_le hδ hs t a
    have hb := norm_spline_pair_le hδ hs t b
    linarith only [ha,hb])

/-- Conjugate pairings need only the positive sum frequency, never shifted differences. -/
theorem norm_integral_spline_conj_pair_le {δ s t : ℝ} (hδ : 0 < δ)
    (hs : 0 < s) (ht : 0 < t) (a b : ℝ) :
    ‖∫ x in a..b, shiftedSplineSlope δ t x*(starRingEnd ℂ) (splineDual δ s x)‖ ≤
      2*splinePairBoundaryBound δ s+
      2*((1+splineRatio δ)^8/(t+s)*(1/(1-splineRatio δ)^8)) := by
  have hi : IntervalIntegrable (fun x => shiftedSplineSlope δ t x*
      (starRingEnd ℂ) (splineDual δ s x)) MeasureTheory.volume a b :=
    ((continuous_shiftedSplineSlope δ t).mul (continuous_conj_splineDual hδ hs)).intervalIntegrable a b
  have hp : IntervalIntegrable (fun x => phase (t+s) x*splineBlaschke δ x)
      MeasureTheory.volume a b :=
    ((continuous_phase (t+s)).mul (continuous_splineBlaschke hδ)).intervalIntegrable a b
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_spline_conj_pair hδ hs t x) (hi.sub hp)
  rw [intervalIntegral.integral_sub hi hp] at he
  rw [sub_eq_iff_eq_add.mp he]
  refine (norm_add_le _ _).trans (add_le_add ?_
    (norm_integral_phase_splineBlaschke_le hδ (add_pos ht hs) a b))
  exact (norm_sub_le _ _).trans (by
    have ha := norm_spline_conj_pair_le hδ hs t a
    have hb := norm_spline_conj_pair_le hδ hs t b
    linarith only [ha,hb])

lemma norm_integral_phase_le {u : ℝ} (hu : u ≠ 0) (a b : ℝ) :
    ‖∫ x in a..b, phase u x‖ ≤ 2/|u| := by
  have ht := intervalIntegral.integral_comp_add_right (phase u) a (a := 0) (b := b-a)
  simp only [zero_add, sub_add_cancel] at ht
  rw [← ht]
  have he : (fun x => phase u (x+a))=(fun x => phase u x*phase u a) := by
    funext x
    exact phase_add u x a
  rw [he, intervalIntegral.integral_mul_const, norm_mul, phase_norm, mul_one]
  simpa only [phase, mul_comm] using RHTower.Sieve.norm_integral_exp_phase_le u hu (b-a)

lemma norm_integral_spline_pair_self_sub_length_le {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (a b : ℝ) :
    ‖(∫ x in a..b, shiftedSplineSlope δ s x*splineDual δ s x)-((b-a : ℝ) : ℂ)‖ ≤
      2*splinePairBoundaryBound δ s := by
  simpa only [sub_self, phase_zero, intervalIntegral.integral_const,
    Complex.real_smul, mul_one] using norm_integral_spline_pair_sub_phase_le hδ hs s a b

lemma norm_integral_spline_pair_le_of_ne {δ s t : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hts : t ≠ s) (a b : ℝ) :
    ‖∫ x in a..b, shiftedSplineSlope δ t x*splineDual δ s x‖ ≤
      2*splinePairBoundaryBound δ s+2/|t-s| := by
  have h1 := norm_integral_spline_pair_sub_phase_le hδ hs t a b
  have h2 := norm_integral_phase_le (sub_ne_zero.mpr hts) a b
  have h := norm_add_le
    ((∫ x in a..b, shiftedSplineSlope δ t x*splineDual δ s x)-
      (∫ x in a..b, phase (t-s) x)) (∫ x in a..b, phase (t-s) x)
  rw [sub_add_cancel] at h
  exact h.trans (add_le_add h1 h2)

#print axioms norm_integral_spline_pair_sub_phase_le
#print axioms norm_integral_spline_conj_pair_le
#print axioms norm_integral_spline_pair_self_sub_length_le
#print axioms norm_integral_spline_pair_le_of_ne
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
