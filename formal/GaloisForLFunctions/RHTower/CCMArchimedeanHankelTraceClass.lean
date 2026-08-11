import GaloisForLFunctions.RHTower.CCMArchimedeanQuantizedCalculus
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.HTGeometry.SchwartzTranslation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Half-line Hankel factorization for the CCM quantized differential

Connes--Consani reduce their Lemma `quantsmooth` to the two off-diagonal half-line Hankel
blocks with kernel `g(x+y)`, for a Schwartz function `g`.  This file constructs the exact
Hilbert--Schmidt factorization used to prove those blocks trace class.

The intermediate variable carries Lebesgue measure on `[0,∞)`.  Its first factor is the weighted
Volterra observer

`Bf(t) = (1+t²)⁻¹ ∫₀ᵗ f(y) dy`.

The intrinsic interval-vector field is proved Bochner `L²`; no boundedness, measurability, or
integrability premise is exposed to the eventual source theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real symmDiff

namespace RHTower

/-- Lebesgue measure restricted to the positive half-line, used as the factorization carrier. -/
def ccmPositiveMeasure : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ici 0)

/-- Positive-half-line `L²` carrier in the Hankel factorization. -/
abbrev CCMPositiveL2 := Lp ℂ 2 ccmPositiveMeasure

/-- Interval vector `1_[0,max(t,0)]` in full real-line `L²`. -/
def ccmHalfIntervalVec (t : ℝ) : SoninL2 :=
  indicatorConstLp 2 (measurableSet_Icc : MeasurableSet (Icc 0 (max t 0)))
    (by simp [Real.volume_Icc] : volume (Icc 0 (max t 0)) ≠ ∞) (1 : ℂ)

/-- Exact symmetric-difference measure of two anchored half-intervals. -/
theorem volume_ccmHalfInterval_symmDiff (s t : ℝ) :
    volume (Icc 0 (max s 0) ∆ Icc 0 (max t 0)) =
      ENNReal.ofReal |max s 0 - max t 0| := by
  rcases le_total (max s 0) (max t 0) with h | h
  · have hset : Icc 0 (max s 0) ∆ Icc 0 (max t 0) = Ioc (max s 0) (max t 0) := by
      ext x
      simp only [mem_symmDiff, mem_Icc, mem_Ioc]
      constructor
      · rintro (⟨⟨hx0, hxs⟩, hnot⟩ | ⟨⟨hx0, hxt⟩, hnot⟩)
        · exact False.elim (hnot ⟨hx0, hxs.trans h⟩)
        · exact ⟨lt_of_not_ge (fun hle => hnot ⟨hx0, hle⟩), hxt⟩
      · rintro ⟨hxs, hxt⟩
        exact Or.inr ⟨⟨(le_max_right s 0).trans hxs.le, hxt⟩,
          fun hx => (not_le_of_gt hxs) hx.2⟩
    rw [hset, Real.volume_Ioc, abs_of_nonpos (sub_nonpos.mpr h)]
    congr 1
    ring
  · have hset : Icc 0 (max s 0) ∆ Icc 0 (max t 0) = Ioc (max t 0) (max s 0) := by
      ext x
      simp only [mem_symmDiff, mem_Icc, mem_Ioc]
      constructor
      · rintro (⟨⟨hx0, hxs⟩, hnot⟩ | ⟨⟨hx0, hxt⟩, hnot⟩)
        · exact ⟨lt_of_not_ge (fun hle => hnot ⟨hx0, hle⟩), hxs⟩
        · exact False.elim (hnot ⟨hx0, hxt.trans h⟩)
      · rintro ⟨hxt, hxs⟩
        exact Or.inl ⟨⟨(le_max_right t 0).trans hxt.le, hxs⟩,
          fun hx => (not_le_of_gt hxt) hx.2⟩
    rw [hset, Real.volume_Ioc, abs_of_nonneg (sub_nonneg.mpr h)]

/-- The anchored interval vector is strongly continuous in its endpoint. -/
theorem continuous_ccmHalfIntervalVec : Continuous ccmHalfIntervalVec := by
  apply continuous_indicatorConstLp_set (p := (2 : ENNReal)) (c := (1 : ℂ)) (by norm_num)
  intro x
  rw [show (fun y : ℝ => volume (Icc 0 (max y 0) ∆ Icc 0 (max x 0))) =
      fun y => ENNReal.ofReal |max y 0 - max x 0| by
    funext y
    exact volume_ccmHalfInterval_symmDiff y x]
  have hc : Continuous (fun y : ℝ => ENNReal.ofReal |max y 0 - max x 0|) :=
    ENNReal.continuous_ofReal.comp
      (continuous_abs.comp ((continuous_id.max continuous_const).sub continuous_const))
  simpa using hc.tendsto x

/-- Weighted Volterra observer vector `(1+t²)⁻¹ 1_[0,max(t,0)]`. -/
def ccmVolterraObserverVec (t : ℝ) : SoninL2 :=
  (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) • ccmHalfIntervalVec t

theorem continuous_ccmVolterraObserverVec : Continuous ccmVolterraObserverVec := by
  exact (Complex.continuous_ofReal.comp
    ((continuous_const.add (continuous_id.pow 2)).inv₀ (by
      intro t h
      change 1 + t ^ 2 = 0 at h
      nlinarith [sq_nonneg t])))
      |>.smul continuous_ccmHalfIntervalVec

/-- Pointwise `L²` energy bound furnishing the first Hilbert--Schmidt factor. -/
theorem norm_ccmVolterraObserverVec_sq_le {t : ℝ} (ht : 0 ≤ t) :
    ‖ccmVolterraObserverVec t‖ ^ 2 ≤ (1 + t ^ 2)⁻¹ := by
  rw [ccmVolterraObserverVec, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity)), ccmHalfIntervalVec,
    norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul,
    measureReal_def, Real.volume_Icc, max_eq_left ht, sub_zero,
    ENNReal.toReal_ofReal ht, show (2 : ENNReal).toReal = 2 by norm_num,
    one_div, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, mul_pow,
    Real.sq_sqrt ht]
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [inv_pow]
  field_simp
  nlinarith [sq_nonneg t]

theorem ccmVolterraObserverVec_memLp :
    MemLp ccmVolterraObserverVec 2 ccmPositiveMeasure := by
  refine (memLp_two_iff_integrable_sq_norm
    continuous_ccmVolterraObserverVec.aestronglyMeasurable).mpr ?_
  refine Integrable.mono' integrable_inv_one_add_sq.integrableOn
    (continuous_ccmVolterraObserverVec.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ccmVolterraObserverVec t‖)]
  exact norm_ccmVolterraObserverVec_sq_le ht

/-- Bochner `L²` field for the weighted Volterra observer. -/
def ccmVolterraObserverField : Lp SoninL2 2 ccmPositiveMeasure :=
  ccmVolterraObserverVec_memLp.toLp ccmVolterraObserverVec

/-- First factor in the Hankel trace-class decomposition. -/
def ccmVolterraObserver : SoninL2 →L[ℂ] CCMPositiveL2 :=
  l2ObserverAnalysis ccmPositiveMeasure ccmVolterraObserverField

/-- The first Hankel factor is genuinely Hilbert--Schmidt. -/
theorem ccmVolterraObserver_isHilbertSchmidt :
    ccmVolterraObserver.IsHilbertSchmidt :=
  l2ObserverAnalysis_isHilbertSchmidt ccmPositiveMeasure ccmVolterraObserverField

end RHTower
