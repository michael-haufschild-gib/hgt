import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Suzuki's oriented-interval Gram factorization

The free screw kernel in Suzuki (2022), Section 4, is not merely pointwise positive.  It is the
Gram kernel of signed intervals directed from `0` to `t`.  This file formalizes that exact
factorization and the corresponding Fourier feature

`∫ e_t(x) exp(i z x) dx = (exp(i z t) - 1) / (i z)`.

This is the structural input needed to repair the invalid pointwise-kernel-to-quadratic-form
inference in the printed proofs of Theorems 4.2--4.3.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- Signed indicator of the interval directed from `0` to `t`.  The half-open convention fixes a
literal representative; endpoint choices do not affect any Lebesgue integral below. -/
def suzukiOrientedSegment (t x : ℝ) : ℂ :=
  if 0 ≤ t then (Ioc 0 t).indicator (fun _ => (1 : ℂ)) x
  else -((Ioc t 0).indicator (fun _ => (1 : ℂ)) x)

theorem stronglyMeasurable_suzukiOrientedSegment (t : ℝ) :
    StronglyMeasurable (suzukiOrientedSegment t) := by
  change StronglyMeasurable (fun x => suzukiOrientedSegment t x)
  by_cases ht : 0 ≤ t
  · convert (stronglyMeasurable_const.indicator measurableSet_Ioc :
      StronglyMeasurable ((Ioc 0 t).indicator (fun _ => (1 : ℂ)))) using 1
    funext x
    simp [suzukiOrientedSegment, ht]
  · convert (stronglyMeasurable_const.indicator measurableSet_Ioc :
      StronglyMeasurable ((Ioc t 0).indicator (fun _ => (1 : ℂ)))).neg using 1
    funext x
    simp [suzukiOrientedSegment, ht]

theorem suzukiOrientedSegment_eq_zero_of_not_mem_Icc {a t x : ℝ}
    (_ha : 0 ≤ a) (ht : t ∈ Icc (-a) a) (hx : x ∉ Icc (-a) a) :
    suzukiOrientedSegment t x = 0 := by
  by_cases ht0 : 0 ≤ t
  · by_cases hm : x ∈ Ioc 0 t
    · exfalso
      apply hx
      exact ⟨by linarith [hm.1], hm.2.trans ht.2⟩
    · simp [suzukiOrientedSegment, ht0, Set.indicator, hm]
  · by_cases hm : x ∈ Ioc t 0
    · exfalso
      apply hx
      exact ⟨ht.1.trans hm.1.le, by linarith [hm.2]⟩
    · simp [suzukiOrientedSegment, ht0, Set.indicator, hm]

/-- Integrating against a directed segment is exactly an oriented interval integral. -/
theorem integral_suzukiOrientedSegment_mul (t : ℝ) (f : ℝ → ℂ) :
    (∫ x, suzukiOrientedSegment t x * f x) = ∫ x in 0..t, f x := by
  by_cases ht : 0 ≤ t
  · rw [intervalIntegral.integral_of_le ht,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp [suzukiOrientedSegment, ht, Set.indicator]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [intervalIntegral.integral_of_ge ht',
      ← MeasureTheory.integral_indicator measurableSet_Ioc,
      ← MeasureTheory.integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp [suzukiOrientedSegment, ht, Set.indicator]

/-- **Exact Suzuki Fourier feature.**  The divided exponential in Suzuki's `Phi_1` is the Fourier
transform of a directed interval. -/
theorem integral_suzukiOrientedSegment_mul_cexp (t z : ℝ) (hz : z ≠ 0) :
    (∫ x, suzukiOrientedSegment t x *
        Complex.exp (Complex.I * (z : ℂ) * (x : ℂ))) =
      (Complex.exp (Complex.I * (z : ℂ) * (t : ℂ)) - 1) /
        (Complex.I * (z : ℂ)) := by
  rw [integral_suzukiOrientedSegment_mul]
  have hc : Complex.I * (z : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hz)
  simpa [mul_assoc] using
    (integral_exp_mul_complex (a := 0) (b := t) hc)

/-- The literal free screw kernel used in Suzuki (2022), Eq. (4.3). -/
def suzukiFreeScrewKernel (t u : ℝ) : ℝ :=
  (|t| + |u| - |t - u|) / 2

/-- Overlap supporting the product of two directed segments. -/
def suzukiSegmentOverlap (t u : ℝ) : Set ℝ :=
  if 0 ≤ t then
    if 0 ≤ u then Ioc 0 (min t u) else ∅
  else if 0 ≤ u then ∅ else Ioc (max t u) 0

theorem measurableSet_suzukiSegmentOverlap (t u : ℝ) :
    MeasurableSet (suzukiSegmentOverlap t u) := by
  simp only [suzukiSegmentOverlap]
  split_ifs <;> measurability

theorem volume_suzukiSegmentOverlap_ne_top (t u : ℝ) :
    volume (suzukiSegmentOverlap t u) ≠ ⊤ := by
  simp only [suzukiSegmentOverlap]
  split_ifs <;> simp [Real.volume_Ioc]

/-- Products of directed segments are literal overlap indicators. -/
theorem star_suzukiOrientedSegment_mul_eq_indicator (t u x : ℝ) :
    star (suzukiOrientedSegment t x) * suzukiOrientedSegment u x =
      (suzukiSegmentOverlap t u).indicator (fun _ => (1 : ℂ)) x := by
  by_cases ht : 0 ≤ t
  · by_cases hu : 0 ≤ u
    · have hmem : x ∈ Ioc 0 (min t u) ↔ x ∈ Ioc 0 t ∧ x ∈ Ioc 0 u := by
        simp only [Set.mem_Ioc, le_min_iff]
        tauto
      simp [suzukiOrientedSegment, suzukiSegmentOverlap, ht, hu, Set.indicator, hmem]
      <;> split_ifs <;> simp_all
    · by_cases hp : x ∈ Ioc 0 t
      · by_cases hn : x ∈ Ioc u 0
        · exact False.elim ((not_lt_of_ge hn.2) hp.1)
        · simp [suzukiOrientedSegment, suzukiSegmentOverlap, ht, hu, Set.indicator, hp, hn]
      · simp [suzukiOrientedSegment, suzukiSegmentOverlap, ht, hu, Set.indicator, hp]
  · by_cases hu : 0 ≤ u
    · by_cases hn : x ∈ Ioc t 0
      · by_cases hp : x ∈ Ioc 0 u
        · exact False.elim ((not_lt_of_ge hn.2) hp.1)
        · simp [suzukiOrientedSegment, suzukiSegmentOverlap, ht, hu, Set.indicator, hn, hp]
      · simp [suzukiOrientedSegment, suzukiSegmentOverlap, ht, hu, Set.indicator, hn]
    · have hmem : x ∈ Ioc (max t u) 0 ↔ x ∈ Ioc t 0 ∧ x ∈ Ioc u 0 := by
        simp only [Set.mem_Ioc, max_lt_iff]
        tauto
      simp [suzukiOrientedSegment, suzukiSegmentOverlap, ht, hu, Set.indicator, hmem]
      <;> split_ifs <;> simp_all

theorem integrable_star_suzukiOrientedSegment_mul (t u : ℝ) :
    Integrable (fun x => star (suzukiOrientedSegment t x) * suzukiOrientedSegment u x) := by
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (suzukiSegmentOverlap t u) :=
    MeasureTheory.integrableOn_const (volume_suzukiSegmentOverlap_ne_top t u) (by simp)
  have hi := hone.integrable_indicator (measurableSet_suzukiSegmentOverlap t u)
  exact hi.congr (Filter.Eventually.of_forall fun x =>
    (star_suzukiOrientedSegment_mul_eq_indicator t u x).symm)

/-- **Exact free-kernel Gram factorization (Suzuki Eq. (4.3)).** -/
theorem integral_star_suzukiOrientedSegment_mul (t u : ℝ) :
    (∫ x, star (suzukiOrientedSegment t x) * suzukiOrientedSegment u x) =
      (suzukiFreeScrewKernel t u : ℂ) := by
  rw [show (fun x => star (suzukiOrientedSegment t x) * suzukiOrientedSegment u x) =
      (suzukiSegmentOverlap t u).indicator (fun _ => (1 : ℂ)) by
    funext x
    exact star_suzukiOrientedSegment_mul_eq_indicator t u x]
  rw [MeasureTheory.integral_indicator_const (1 : ℂ)
    (measurableSet_suzukiSegmentOverlap t u)]
  by_cases ht : 0 ≤ t
  · by_cases hu : 0 ≤ u
    · rw [show suzukiSegmentOverlap t u = Ioc 0 (min t u) by
        simp [suzukiSegmentOverlap, ht, hu]]
      rw [Real.volume_real_Ioc_of_le (by positivity : 0 ≤ min t u)]
      simp only [sub_zero, suzukiFreeScrewKernel]
      by_cases htu : t ≤ u
      · rw [min_eq_left htu]
        rw [abs_of_nonneg ht, abs_of_nonneg hu, abs_of_nonpos (sub_nonpos.mpr htu)]
        norm_num
        ring
      · have hut : u ≤ t := le_of_not_ge htu
        rw [min_eq_right hut]
        rw [abs_of_nonneg ht, abs_of_nonneg hu, abs_of_nonneg (sub_nonneg.mpr hut)]
        norm_num
    · have hu' : u ≤ 0 := le_of_not_ge hu
      rw [show suzukiSegmentOverlap t u = ∅ by simp [suzukiSegmentOverlap, ht, hu]]
      simp only [measureReal_def, measure_empty, ENNReal.toReal_zero, zero_smul,
        suzukiFreeScrewKernel]
      rw [abs_of_nonneg ht, abs_of_nonpos hu',
        abs_of_nonneg (sub_nonneg.mpr (hu'.trans ht))]
      push_cast
      ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    by_cases hu : 0 ≤ u
    · rw [show suzukiSegmentOverlap t u = ∅ by simp [suzukiSegmentOverlap, ht, hu]]
      simp only [measureReal_def, measure_empty, ENNReal.toReal_zero, zero_smul,
        suzukiFreeScrewKernel]
      rw [abs_of_nonpos ht', abs_of_nonneg hu,
        abs_of_nonpos (sub_nonpos.mpr (ht'.trans hu))]
      push_cast
      ring
    · have hu' : u ≤ 0 := le_of_not_ge hu
      rw [show suzukiSegmentOverlap t u = Ioc (max t u) 0 by
        simp [suzukiSegmentOverlap, ht, hu]]
      rw [Real.volume_real_Ioc_of_le (max_le ht' hu')]
      simp only [zero_sub, suzukiFreeScrewKernel]
      by_cases htu : t ≤ u
      · rw [max_eq_right htu]
        rw [abs_of_nonpos ht', abs_of_nonpos hu', abs_of_nonpos (sub_nonpos.mpr htu)]
        norm_num
        ring
      · have hut : u ≤ t := le_of_not_ge htu
        rw [max_eq_left hut]
        rw [abs_of_nonpos ht', abs_of_nonpos hu', abs_of_nonneg (sub_nonneg.mpr hut)]
        norm_num
        ring

/-! ## Exact finite quadratic-form factorization -/

/-- Finite superposition of Suzuki's directed interval features. -/
def suzukiFiniteOrientedPrimitive {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) (x : ℝ) : ℂ :=
  ∑ i ∈ s, c i * suzukiOrientedSegment (τ i) x

theorem stronglyMeasurable_suzukiFiniteOrientedPrimitive {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) :
    StronglyMeasurable (suzukiFiniteOrientedPrimitive s c τ) := by
  unfold suzukiFiniteOrientedPrimitive
  convert (Finset.stronglyMeasurable_sum s fun i hi =>
    (stronglyMeasurable_suzukiOrientedSegment (τ i)).const_mul (c i)) using 1
  funext x
  simp

theorem suzukiFiniteOrientedPrimitive_eq_zero_of_not_mem_Icc {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (τ : ι → ℝ) {a x : ℝ} (ha : 0 ≤ a)
    (hτ : ∀ i ∈ s, τ i ∈ Icc (-a) a) (hx : x ∉ Icc (-a) a) :
    suzukiFiniteOrientedPrimitive s c τ x = 0 := by
  unfold suzukiFiniteOrientedPrimitive
  apply Finset.sum_eq_zero
  intro i hi
  rw [suzukiOrientedSegment_eq_zero_of_not_mem_Icc ha (hτ i hi) hx]
  simp

/-- Quadratic form of the free screw kernel on a finite complex source. -/
def suzukiFreeKernelQuadraticForm {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s,
    star (c i) * (suzukiFreeScrewKernel (τ i) (τ j) : ℂ) * c j

/-- **Finite-source form identity.**  The free screw-kernel quadratic form is exactly squared
Gram energy of the directed-interval primitive.  Unlike entrywise kernel ordering, this identity
is valid for arbitrary complex coefficients. -/
theorem suzukiFreeKernelQuadraticForm_eq_integral {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) :
    suzukiFreeKernelQuadraticForm s c τ =
      ∫ x, star (suzukiFiniteOrientedPrimitive s c τ x) *
        suzukiFiniteOrientedPrimitive s c τ x := by
  unfold suzukiFreeKernelQuadraticForm suzukiFiniteOrientedPrimitive
  have hInt (i j : ι) : Integrable (fun x =>
      star (c i * suzukiOrientedSegment (τ i) x) *
        (c j * suzukiOrientedSegment (τ j) x)) := by
    convert ((integrable_star_suzukiOrientedSegment_mul (τ i) (τ j)).const_mul
      (star (c i))).mul_const (c j) using 1
    funext x
    rw [star_mul]
    ring
  calc
    (∑ i ∈ s, ∑ j ∈ s,
        star (c i) * (suzukiFreeScrewKernel (τ i) (τ j) : ℂ) * c j) =
      ∑ i ∈ s, ∑ j ∈ s,
        ∫ x, star (c i * suzukiOrientedSegment (τ i) x) *
          (c j * suzukiOrientedSegment (τ j) x) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (fun x => star (c i * suzukiOrientedSegment (τ i) x) *
            (c j * suzukiOrientedSegment (τ j) x)) = fun x =>
              star (c i) *
                (star (suzukiOrientedSegment (τ i) x) *
                  suzukiOrientedSegment (τ j) x) * c j by
          funext x
          rw [star_mul]
          ring]
        rw [integral_mul_const, integral_const_mul,
          integral_star_suzukiOrientedSegment_mul]
    _ = ∫ x, ∑ i ∈ s, ∑ j ∈ s,
        star (c i * suzukiOrientedSegment (τ i) x) *
          (c j * suzukiOrientedSegment (τ j) x) := by
        symm
        rw [MeasureTheory.integral_finsetSum s]
        · apply Finset.sum_congr rfl
          intro i hi
          rw [MeasureTheory.integral_finsetSum s (fun j hj => hInt i j)]
        · intro i hi
          exact MeasureTheory.integrable_finsetSum s (fun j hj => hInt i j)
    _ = ∫ x, star (∑ i ∈ s, c i * suzukiOrientedSegment (τ i) x) *
          (∑ j ∈ s, c j * suzukiOrientedSegment (τ j) x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change (∑ i ∈ s, ∑ j ∈ s,
              star (c i * suzukiOrientedSegment (τ i) x) *
                (c j * suzukiOrientedSegment (τ j) x)) =
            star (∑ i ∈ s, c i * suzukiOrientedSegment (τ i) x) *
              (∑ j ∈ s, c j * suzukiOrientedSegment (τ j) x)
          rw [star_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [star_mul, mul_assoc, Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

theorem integrable_suzukiFiniteOrientedPrimitive_energy {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) :
    Integrable (fun x => star (suzukiFiniteOrientedPrimitive s c τ x) *
      suzukiFiniteOrientedPrimitive s c τ x) := by
  have hInt (i j : ι) : Integrable (fun x =>
      star (c i * suzukiOrientedSegment (τ i) x) *
        (c j * suzukiOrientedSegment (τ j) x)) := by
    convert ((integrable_star_suzukiOrientedSegment_mul (τ i) (τ j)).const_mul
      (star (c i))).mul_const (c j) using 1
    funext x
    rw [star_mul]
    ring
  have hsum : Integrable (fun x => ∑ i ∈ s, ∑ j ∈ s,
      star (c i * suzukiOrientedSegment (τ i) x) *
        (c j * suzukiOrientedSegment (τ j) x)) :=
    MeasureTheory.integrable_finsetSum s fun i hi =>
      MeasureTheory.integrable_finsetSum s fun j hj => hInt i j
  apply hsum.congr
  exact Filter.Eventually.of_forall fun x => by
    unfold suzukiFiniteOrientedPrimitive
    change (∑ i ∈ s, ∑ j ∈ s,
        star (c i * suzukiOrientedSegment (τ i) x) *
          (c j * suzukiOrientedSegment (τ j) x)) =
      star (∑ i ∈ s, c i * suzukiOrientedSegment (τ i) x) *
        (∑ j ∈ s, c j * suzukiOrientedSegment (τ j) x)
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [star_mul, mul_assoc, Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem integrable_norm_sq_suzukiFiniteOrientedPrimitive {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) :
    Integrable (fun x => ‖suzukiFiniteOrientedPrimitive s c τ x‖ ^ 2) := by
  have h := (integrable_suzukiFiniteOrientedPrimitive_energy s c τ).norm
  simpa only [norm_mul, norm_star, pow_two] using h

/-- Real part of the finite free-kernel form is literally the squared `L²` norm of its oriented
primitive. -/
theorem suzukiFreeKernelQuadraticForm_re_eq_integral_norm_sq {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) :
    (suzukiFreeKernelQuadraticForm s c τ).re =
      ∫ x, ‖suzukiFiniteOrientedPrimitive s c τ x‖ ^ 2 := by
  rw [suzukiFreeKernelQuadraticForm_eq_integral]
  change RCLike.re (∫ x, star (suzukiFiniteOrientedPrimitive s c τ x) *
    suzukiFiniteOrientedPrimitive s c τ x) = _
  rw [← integral_re (integrable_suzukiFiniteOrientedPrimitive_energy s c τ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (star (suzukiFiniteOrientedPrimitive s c τ x) *
      suzukiFiniteOrientedPrimitive s c τ x).re = _
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_re _

/-- If every source point lies in `[-a,a]`, the free-kernel form energy is supported there. -/
theorem suzukiFreeKernelQuadraticForm_re_eq_integral_Icc_norm_sq {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (τ : ι → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hτ : ∀ i ∈ s, τ i ∈ Icc (-a) a) :
    (suzukiFreeKernelQuadraticForm s c τ).re =
      ∫ x in Icc (-a) a, ‖suzukiFiniteOrientedPrimitive s c τ x‖ ^ 2 := by
  rw [suzukiFreeKernelQuadraticForm_re_eq_integral_norm_sq]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [suzukiFiniteOrientedPrimitive_eq_zero_of_not_mem_Icc s c τ ha hτ hx, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)]).symm

/-- Closed positive-semidefiniteness of Suzuki's free screw kernel on every finite complex source. -/
theorem suzukiFreeKernelQuadraticForm_re_nonneg {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (τ : ι → ℝ) :
    0 ≤ (suzukiFreeKernelQuadraticForm s c τ).re := by
  rw [suzukiFreeKernelQuadraticForm_eq_integral]
  change 0 ≤ RCLike.re (∫ x,
    star (suzukiFiniteOrientedPrimitive s c τ x) * suzukiFiniteOrientedPrimitive s c τ x)
  rw [← integral_re (integrable_suzukiFiniteOrientedPrimitive_energy s c τ)]
  apply integral_nonneg
  intro x
  change 0 ≤ (star (suzukiFiniteOrientedPrimitive s c τ x) *
    suzukiFiniteOrientedPrimitive s c τ x).re
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  exact Complex.normSq_nonneg _

end RHTower

end
