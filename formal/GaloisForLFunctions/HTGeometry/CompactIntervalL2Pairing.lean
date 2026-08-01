import GaloisForLFunctions.HTGeometry.ConvolutionKernelSquareBound
import Mathlib.MeasureTheory.Function.L2Space
import GaloisForLFunctions.HTGeometry.CompactFourierSineKernel
import GaloisForLFunctions.HTGeometry.SignedCharFunCentralJet

/-!
# Pairings in `L²` of a compact interval

A continuous weight on a compact interval defines an element of `L²` there, and the inner product
against it is the integral of the conjugated weight against the function.  This is what turns a
"bounded `L²` functional" from an abstract vector into an explicit integral: a pairing vector
obtained this way carries the provenance of its weight.

The measure is `volume` restricted to `[-a, a]`, which is finite, so a continuous function is
bounded on the interval and lies in every `L^p`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-- `L²` of a compact symmetric interval. -/
abbrev IntervalL2 (a : ℝ) := Lp ℂ 2 (volume.restrict (Set.Icc (-a) a))

/-- A continuous function lies in `L²` of a compact interval: it is bounded there and the measure
is finite. -/
theorem memLp_two_of_continuous (a : ℝ) {w : ℝ → ℂ} (hw : Continuous w) :
    MemLp w 2 (volume.restrict (Set.Icc (-a) a)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := w) hw.continuousOn
  refine MemLp.of_bound hw.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using hC x hx

/-- A continuous weight as an element of `L²` of the interval. -/
def toIntervalL2 (a : ℝ) {w : ℝ → ℂ} (hw : Continuous w) : IntervalL2 a :=
  (memLp_two_of_continuous a hw).toLp w

/-- **The pairing against a continuous weight is an explicit integral.**  This is the concrete form
of "a bounded `L²` functional": the vector is the weight, and the pairing is the integral of the
conjugated weight against the function. -/
theorem inner_toIntervalL2 (a : ℝ) {w : ℝ → ℂ} (hw : Continuous w) (f : IntervalL2 a) :
    inner ℂ (toIntervalL2 a hw) f
      = ∫ x in Set.Icc (-a) a, (starRingEnd ℂ) (w x) * f x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_two_of_continuous a hw).coeFn_toLp] with x hx
  simp only [toIntervalL2]
  rw [hx, RCLike.inner_apply, mul_comm]

/-- The pairing of a continuous weight against a continuous function, both as `L²` elements. -/
theorem inner_toIntervalL2_toIntervalL2 (a : ℝ) {w f : ℝ → ℂ}
    (hw : Continuous w) (hf : Continuous f) :
    inner ℂ (toIntervalL2 a hw) (toIntervalL2 a hf)
      = ∫ x in Set.Icc (-a) a, (starRingEnd ℂ) (w x) * f x := by
  rw [inner_toIntervalL2 a hw]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_two_of_continuous a hf).coeFn_toLp] with x hx
  simp only [toIntervalL2]
  rw [hx]

/-- The constant function `1` as an element of `L²` of the interval. -/
def oneIntervalL2 (a : ℝ) : IntervalL2 a :=
  toIntervalL2 a (continuous_const : Continuous (fun _ : ℝ => (1 : ℂ)))

/-- **Pairing a weight against the constant function is the interval integral of its conjugate.**
This is the bridge that turns an interval-integral identity into a value of an `L²` pairing. -/
theorem inner_toIntervalL2_one (a : ℝ) (ha : 0 ≤ a) {w : ℝ → ℂ} (hw : Continuous w) :
    inner ℂ (toIntervalL2 a hw) (oneIntervalL2 a)
      = ∫ x in (-a : ℝ)..a, (starRingEnd ℂ) (w x) := by
  rw [oneIntervalL2, inner_toIntervalL2_toIntervalL2 a hw]
  simp only [mul_one]
  rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

/-! ## A pairing vector with provenance

The caution about free pairing vectors is answered by exhibiting one whose value is *proved*.  The
edge denominator weight is an explicit continuous function, and its pairing against the constant
function is the central jet `4 a cosh a` — the value the normalized edge quotient needs, obtained
from `integral_edgeDenominatorSum` rather than chosen. -/

/-- The explicit weight whose pairing against the constant function is the edge denominator. -/
def edgeDenominatorWeight : ℝ → ℂ := fun y =>
  (((Real.exp y + Real.exp (-y)) + y * (Real.exp y - Real.exp (-y)) : ℝ) : ℂ)

theorem continuous_edgeDenominatorWeight : Continuous edgeDenominatorWeight := by
  unfold edgeDenominatorWeight
  fun_prop

/-- The interval integral of the edge denominator weight is the central jet. -/
theorem integral_edgeDenominatorWeight (a : ℝ) :
    (∫ y in (-a : ℝ)..a,
        ((Real.exp y + Real.exp (-y)) + y * (Real.exp y - Real.exp (-y))))
      = 4 * a * Real.cosh a := by
  rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  exact integral_edgeDenominatorSum a

theorem conj_edgeDenominatorWeight (y : ℝ) :
    (starRingEnd ℂ) (edgeDenominatorWeight y) = edgeDenominatorWeight y :=
  Complex.conj_ofReal _

/-- **A pairing vector whose value is proved, not chosen.**  The pairing of the edge denominator
weight against the constant function is the central jet `4 a cosh a`. -/
theorem inner_edgeDenominatorWeight_one (a : ℝ) (ha : 0 ≤ a) :
    inner ℂ (toIntervalL2 a continuous_edgeDenominatorWeight) (oneIntervalL2 a)
      = ((4 * a * Real.cosh a : ℝ) : ℂ) := by
  rw [inner_toIntervalL2_one a ha,
    intervalIntegral.integral_congr (fun y _ => conj_edgeDenominatorWeight y)]
  simp only [edgeDenominatorWeight]
  rw [intervalIntegral.integral_ofReal, integral_edgeDenominatorWeight a]

/-! ### The numerator weight

The same construction for the numerator: the weight is read off from the exponential source
combination, and its integral is the endpoint-atom value `2 cosh a * H (2a)`. -/

/-- The explicit weight whose pairing against the constant function is the edge numerator. -/
def edgeNumeratorWeight (a : ℝ) (H H' : ℝ → ℝ) : ℝ → ℝ := fun x =>
  (Real.exp x + Real.exp (-x)) * H' (a - x) + (Real.exp (-x) - Real.exp x) * H (a - x)

/-- The reflected primitive is differentiable with the reflected derivative. -/
theorem hasDerivAt_reflect {H H' : ℝ → ℝ} (hH : ∀ x, HasDerivAt H (H' x) x) (a x : ℝ) :
    HasDerivAt (fun y => H (a - y)) (-(H' (a - x))) x := by
  have hin : HasDerivAt (fun y : ℝ => a - y) (-1) x := by
    have := (hasDerivAt_const x a).sub (hasDerivAt_id x)
    have hval : (0 : ℝ) - 1 = -1 := by ring
    rw [hval] at this
    exact this
  have hd := (hH (a - x)).comp x hin
  have hval : H' (a - x) * -1 = -(H' (a - x)) := by ring
  rw [hval] at hd
  exact hd

/-- **The integral of the numerator weight is the endpoint-atom value.** -/
theorem integral_edgeNumeratorWeight (a : ℝ) {H H' : ℝ → ℝ}
    (hH : ∀ x, HasDerivAt H (H' x) x) (hH'c : Continuous H') (hH0 : H 0 = 0) :
    (∫ x in (-a : ℝ)..a, edgeNumeratorWeight a H H' x) = 2 * Real.cosh a * H (2 * a) := by
  have hHc : Continuous H := by
    exact continuous_iff_continuousAt.mpr fun x => (hH x).continuousAt
  have hint : IntervalIntegrable (fun x => -(H' (a - x))) volume (-a) a :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hkey := exponentialSourceCombination_primitive_pairing a
    (H := H) (H' := H') (fun x _ => hasDerivAt_reflect hH a x) hint hH0
  rw [← hkey]
  have hsplit : ∀ x : ℝ, edgeNumeratorWeight a H H' x
      = (Real.exp x * -(H' (a - x))) * (-1) + (Real.exp x * H (a - x)) * (-1)
        + ((Real.exp (-x) * -(H' (a - x))) * (-1) + Real.exp (-x) * H (a - x)) := by
    intro x
    unfold edgeNumeratorWeight
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hsplit x)]
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [intervalIntegral.integral_mul_const]
  ring

/-- The numerator weight as a complex-valued function. -/
def edgeNumeratorWeightC (a : ℝ) (H H' : ℝ → ℝ) : ℝ → ℂ := fun x =>
  ((edgeNumeratorWeight a H H' x : ℝ) : ℂ)

theorem continuous_edgeNumeratorWeightC {H H' : ℝ → ℝ} (hH : ∀ x, HasDerivAt H (H' x) x)
    (hH'c : Continuous H') (a : ℝ) : Continuous (edgeNumeratorWeightC a H H') := by
  have hHc : Continuous H := continuous_iff_continuousAt.mpr fun x => (hH x).continuousAt
  unfold edgeNumeratorWeightC edgeNumeratorWeight
  fun_prop

theorem conj_edgeNumeratorWeightC (a : ℝ) (H H' : ℝ → ℝ) (y : ℝ) :
    (starRingEnd ℂ) (edgeNumeratorWeightC a H H' y) = edgeNumeratorWeightC a H H' y :=
  Complex.conj_ofReal _

/-- **The numerator pairing vector, with its value proved.**  The pairing of the numerator weight
against the constant function is the endpoint-atom value `2 cosh a * H (2a)`. -/
theorem inner_edgeNumeratorWeight_one (a : ℝ) (ha : 0 ≤ a) {H H' : ℝ → ℝ}
    (hH : ∀ x, HasDerivAt H (H' x) x) (hH'c : Continuous H') (hH0 : H 0 = 0) :
    inner ℂ (toIntervalL2 a (continuous_edgeNumeratorWeightC hH hH'c a)) (oneIntervalL2 a)
      = ((2 * Real.cosh a * H (2 * a) : ℝ) : ℂ) := by
  rw [inner_toIntervalL2_one a ha,
    intervalIntegral.integral_congr (fun y _ => conj_edgeNumeratorWeightC a H H' y)]
  simp only [edgeNumeratorWeightC]
  rw [intervalIntegral.integral_ofReal, integral_edgeNumeratorWeight a hH hH'c hH0]

end GaloisForLFunctions.HTGeometry
