import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The rank-two commutator of a truncated convolution

Let `k` be an even `C¹` kernel and let

`(A f)(x) = ∫_0^(1 : ℕ) k(x-y) f(y) dy`

be the associated truncated convolution on the unit interval.  In the exponential basis
`e_j(x) = e^{2πijx}` the matrix `Q_{ij} = ⟨e_i, A e_j⟩` obeys the exact divided-difference law

`(i - j) Q_{ij} = b_j - b_i`,   `b_j = -(2πi)^{-1} ∫_0^(1 : ℕ) (k(1-y) - k(y)) e_j(y) dy`,

with an odd source `b_{-j} = -b_j`.  The proof is two integrations by parts — one in the outer
variable against `e_{-i}`, one in the inner variable against `e_j` — whose interior terms are the
same double integral and cancel, leaving only the two boundary terms.  No Fubini and no
differentiation of the exponential basis in the outer variable are needed beyond this.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The exponential basis -/

/-- The exponential `e_j(x) = e^{2πijx}`. -/
def fourierChar (j : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (x : ℂ))

@[fun_prop]
theorem continuous_fourierChar (j : ℤ) : Continuous (fourierChar j) := by
  unfold fourierChar
  fun_prop

theorem hasDerivAt_fourierChar (j : ℤ) (x : ℝ) :
    HasDerivAt (fourierChar j)
      (2 * Real.pi * Complex.I * (j : ℂ) * fourierChar j x) x := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => 2 * Real.pi * Complex.I * (j : ℂ) * (s : ℂ))
      (2 * Real.pi * Complex.I * (j : ℂ)) x := by
    simpa using h1.const_mul (2 * Real.pi * Complex.I * (j : ℂ))
  have h3 := h2.cexp
  refine h3.congr_deriv ?_
  rw [fourierChar]
  ring

@[simp]
theorem fourierChar_zero (j : ℤ) : fourierChar j 0 = 1 := by
  simp [fourierChar]

@[simp]
theorem fourierChar_one (j : ℤ) : fourierChar j 1 = 1 := by
  have h : (2 : ℂ) * Real.pi * Complex.I * (j : ℂ) * ((1 : ℝ) : ℂ)
      = (j : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [fourierChar, h, Complex.exp_int_mul_two_pi_mul_I]

/-- Translating the argument by one and reflecting turns `e_{-j}` into `e_j`. -/
theorem fourierChar_neg_one_sub (j : ℤ) (u : ℝ) :
    fourierChar (-j) (1 - u) = fourierChar j u := by
  have h : (2 : ℂ) * Real.pi * Complex.I * ((-j : ℤ) : ℂ) * ((1 - u : ℝ) : ℂ)
      = (-j : ℤ) * (2 * Real.pi * Complex.I) + 2 * Real.pi * Complex.I * (j : ℂ) * (u : ℂ) := by
    push_cast
    ring
  rw [fourierChar, fourierChar, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-! ## The truncated convolution -/

/-- The truncated convolution `(A f)(x) = ∫_0^(1 : ℕ) k(x-y) f(y) dy`. -/
def truncConv (k : ℝ → ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in (0 : ℝ)..1, ((k (x - y) : ℝ) : ℂ) * f y

theorem continuous_truncConv {k : ℝ → ℝ} (hk : Continuous k) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (truncConv k f) := by
  have huncurry : Continuous (Function.uncurry fun x y : ℝ => ((k (x - y) : ℝ) : ℂ) * f y) := by
    have : Continuous fun p : ℝ × ℝ => ((k (p.1 - p.2) : ℝ) : ℂ) * f p.2 := by
      fun_prop
    exact this
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) huncurry 0 1

/-- **Differentiation falls on the kernel.** -/
theorem hasDerivAt_truncConv {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') {f : ℝ → ℂ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (truncConv k f) (truncConv k' f x) x := by
  have hkc : Continuous k := by
    refine continuous_iff_continuousAt.2 fun u => ?_
    exact (hk u).continuousAt
  set F : ℝ → ℝ → ℂ := fun z y => ((k (z - y) : ℝ) : ℂ) * f y with hF
  set F' : ℝ → ℝ → ℂ := fun z y => ((k' (z - y) : ℝ) : ℂ) * f y with hF'
  have hcontF : ∀ z : ℝ, Continuous (F z) := by
    intro z
    rw [hF]
    fun_prop
  have hcontF' : ∀ z : ℝ, Continuous (F' z) := by
    intro z
    rw [hF']
    fun_prop
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := x - 2) (b := x + 1)).exists_bound_of_continuousOn
    (hk'c.continuousOn (s := Set.Icc (x - 2) (x + 1)))
  obtain ⟨Cf, hCf⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hf.continuousOn (s := Set.Icc (0 : ℝ) 1))
  have hbound_int : IntervalIntegrable (fun _ : ℝ => M * Cf) volume 0 1 :=
    (continuous_const).intervalIntegrable _ _
  have hle : ∀ᵐ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ z ∈ Metric.ball x 1, ‖F' z t‖ ≤ M * Cf := by
    filter_upwards with t ht z hz
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht.1
    have ht1 : t ≤ 1 := ht.2
    have hzd : |z - x| < 1 := by
      have hd := Metric.mem_ball.1 hz
      rwa [Real.dist_eq] at hd
    have hmem : z - t ∈ Set.Icc (x - 2) (x + 1) := by
      obtain ⟨hz1, hz2⟩ := abs_lt.1 hzd
      exact ⟨by linarith, by linarith⟩
    have h1 : ‖((k' (z - t) : ℝ) : ℂ)‖ ≤ M := by
      simpa using hM _ hmem
    have h2 : ‖f t‖ ≤ Cf := hCf t ⟨ht0, ht1⟩
    rw [hF']
    simp only
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  have hdiff : ∀ᵐ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ z ∈ Metric.ball x 1, HasDerivAt (fun z : ℝ => F z t) (F' z t) z := by
    filter_upwards with t _ z _
    have hsub : HasDerivAt (fun z : ℝ => z - t) 1 z := (hasDerivAt_id z).sub_const t
    have hcomp : HasDerivAt (fun z : ℝ => k (z - t)) (k' (z - t)) z := by
      simpa [Function.comp_def] using (hk (z - t)).comp z hsub
    have hcplx : HasDerivAt (fun z : ℝ => ((k (z - t) : ℝ) : ℂ)) (((k' (z - t) : ℝ) : ℂ)) z :=
      hcomp.ofReal_comp
    rw [hF, hF']
    simp only
    exact hcplx.mul_const (f t)
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1) (F := F) (F' := F') (x₀ := x)
    (bound := fun _ : ℝ => M * Cf) (s := Metric.ball x 1)
    (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun z => (hcontF z).aestronglyMeasurable)
    ((hcontF x).intervalIntegrable _ _)
    ((hcontF' x).aestronglyMeasurable) hle hbound_int hdiff
  exact hmain.2

/-! ## The matrix and its source -/

/-- The matrix of the truncated convolution in the exponential basis. -/
def convMatrix (k : ℝ → ℝ) (i j : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, fourierChar (-i) x * truncConv k (fourierChar j) x

/-- The divided-difference source `b_j`. -/
def convSource (k : ℝ → ℝ) (j : ℤ) : ℂ :=
  (-1 / (2 * Real.pi * Complex.I)) *
    ∫ y in (0 : ℝ)..1, ((k (1 - y) - k y : ℝ) : ℂ) * fourierChar j y

/-- **The source is odd.** -/
theorem convSource_neg (k : ℝ → ℝ) (j : ℤ) : convSource k (-j) = -convSource k j := by
  have hsub : (∫ y in (0 : ℝ)..1, ((k (1 - y) - k y : ℝ) : ℂ) * fourierChar (-j) y)
      = -∫ y in (0 : ℝ)..1, ((k (1 - y) - k y : ℝ) : ℂ) * fourierChar j y := by
    have hcomp := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 : ℝ))
      (fun y : ℝ => ((k (1 - y) - k y : ℝ) : ℂ) * fourierChar (-j) y) (1 : ℝ)
    simp only [sub_zero, sub_self] at hcomp
    rw [← hcomp]
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have h1 : (1 : ℝ) - (1 - u) = u := by ring
    rw [h1, fourierChar_neg_one_sub]
    push_cast
    ring
  rw [convSource, convSource, hsub]
  ring

/-! ## The two integrations by parts -/

theorem hasDerivAt_kernel_sub {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u) (x y : ℝ) :
    HasDerivAt (fun s : ℝ => ((k (x - s) : ℝ) : ℂ)) (-((k' (x - y) : ℝ) : ℂ)) y := by
  have hsub : HasDerivAt (fun s : ℝ => x - s) (-1) y := by
    simpa using HasDerivAt.const_sub x (hasDerivAt_id y)
  have hcomp : HasDerivAt (fun s : ℝ => k (x - s)) (-(k' (x - y))) y := by
    simpa [Function.comp_def] using (hk (x - y)).comp y hsub
  simpa using hcomp.ofReal_comp

/-- **The inner integration by parts.**  Multiplying the exponential by its frequency is the
same as differentiating the kernel, up to the two endpoint values. -/
theorem truncConv_char_freq {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (j : ℤ) (x : ℝ) :
    2 * Real.pi * Complex.I * (j : ℂ) * truncConv k (fourierChar j) x
      = ((k (x - 1) - k x : ℝ) : ℂ) + truncConv k' (fourierChar j) x := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun u => (hk u).continuousAt
  have hu' : IntervalIntegrable (fun s : ℝ => -((k' (x - s) : ℝ) : ℂ)) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    fun_prop
  have hv' : IntervalIntegrable
      (fun s : ℝ => 2 * Real.pi * Complex.I * (j : ℂ) * fourierChar j s) volume 0 1 :=
    (continuous_const.mul (continuous_fourierChar j)).intervalIntegrable _ _
  have hby := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => ((k (x - s) : ℝ) : ℂ))
    (u' := fun s : ℝ => -((k' (x - s) : ℝ) : ℂ))
    (v := fourierChar j)
    (v' := fun s : ℝ => 2 * Real.pi * Complex.I * (j : ℂ) * fourierChar j s)
    (fun s _ => hasDerivAt_kernel_sub hk x s) (fun s _ => hasDerivAt_fourierChar j s) hu' hv'
  have hlhs : (∫ y in (0 : ℝ)..1, ((k (x - y) : ℝ) : ℂ) *
        (2 * Real.pi * Complex.I * (j : ℂ) * fourierChar j y))
      = 2 * Real.pi * Complex.I * (j : ℂ) * truncConv k (fourierChar j) x := by
    rw [truncConv, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  have hrhs : (∫ y in (0 : ℝ)..1, -((k' (x - y) : ℝ) : ℂ) * fourierChar j y)
      = -truncConv k' (fourierChar j) x := by
    rw [truncConv, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  rw [hlhs, hrhs] at hby
  rw [hby]
  simp only [fourierChar_one, fourierChar_zero, mul_one, sub_zero]
  push_cast
  ring

/-! ## The commutator law -/

/-- **The exact divided-difference law.**  For an even `C¹` kernel the matrix of the truncated
convolution in the exponential basis satisfies `(i-j)Q_{ij} = b_j - b_i`. -/
theorem convMatrix_commutator {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) (i j : ℤ) :
    ((i : ℂ) - (j : ℂ)) * convMatrix k i j = convSource k j - convSource k i := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun u => (hk u).continuousAt
  have hcne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  set G : ℝ → ℂ := truncConv k (fourierChar j) with hG
  set G' : ℝ → ℂ := truncConv k' (fourierChar j) with hG'
  have hGcont : Continuous G := continuous_truncConv hkc (continuous_fourierChar j)
  have hG'cont : Continuous G' := continuous_truncConv hk'c (continuous_fourierChar j)
  have hGderiv : ∀ x : ℝ, HasDerivAt G (G' x) x := fun x =>
    hasDerivAt_truncConv hk hk'c (continuous_fourierChar j) x
  have houter := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (u := fourierChar (-i))
    (u' := fun s : ℝ => 2 * (Real.pi : ℂ) * Complex.I * ((-i : ℤ) : ℂ) * fourierChar (-i) s)
    (v := G) (v' := G')
    (fun s _ => hasDerivAt_fourierChar (-i) s) (fun s _ => hGderiv s)
    ((continuous_const.mul (continuous_fourierChar (-i))).intervalIntegrable _ _)
    (hG'cont.intervalIntegrable _ _)
  have hIu : (∫ x in (0 : ℝ)..1,
        2 * (Real.pi : ℂ) * Complex.I * ((-i : ℤ) : ℂ) * fourierChar (-i) x * G x)
      = -(2 * (Real.pi : ℂ) * Complex.I * (i : ℂ)) * convMatrix k i j := by
    rw [convMatrix, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    push_cast
    ring
  rw [hIu, fourierChar_one, fourierChar_zero, one_mul, one_mul] at houter
  have hI : 2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * convMatrix k i j
      = (∫ x in (0 : ℝ)..1, fourierChar (-i) x * G' x) - (G 1 - G 0) := by
    rw [houter]
    ring
  have hII : 2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * convMatrix k i j
      = (∫ x in (0 : ℝ)..1, fourierChar (-i) x * ((k (x - 1) - k x : ℝ) : ℂ))
        + ∫ x in (0 : ℝ)..1, fourierChar (-i) x * G' x := by
    have hsplit : (∫ x in (0 : ℝ)..1, fourierChar (-i) x *
          (((k (x - 1) - k x : ℝ) : ℂ) + G' x))
        = (∫ x in (0 : ℝ)..1, fourierChar (-i) x * ((k (x - 1) - k x : ℝ) : ℂ))
          + ∫ x in (0 : ℝ)..1, fourierChar (-i) x * G' x := by
      rw [← intervalIntegral.integral_add]
      · refine intervalIntegral.integral_congr fun x _ => ?_
        ring
      · refine Continuous.intervalIntegrable ?_ _ _
        exact (continuous_fourierChar (-i)).mul (by fun_prop)
      · exact ((continuous_fourierChar (-i)).mul hG'cont).intervalIntegrable _ _
    rw [← hsplit, convMatrix, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [← truncConv_char_freq hk hk'c j x]
    ring
  have hcomb : 2 * (Real.pi : ℂ) * Complex.I * ((i : ℂ) - j) * convMatrix k i j
      = -(G 1 - G 0) - ∫ x in (0 : ℝ)..1, fourierChar (-i) x * ((k (x - 1) - k x : ℝ) : ℂ) := by
    linear_combination hI - hII
  have hbdry : G 1 - G 0 = -(2 * (Real.pi : ℂ) * Complex.I * convSource k j) := by
    have h1 : G 1 - G 0
        = ∫ y in (0 : ℝ)..1, ((k (1 - y) - k y : ℝ) : ℂ) * fourierChar j y := by
      rw [hG, truncConv, truncConv, ← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr fun y _ => ?_
        have hzero : ((k (0 - y) : ℝ) : ℂ) = ((k y : ℝ) : ℂ) := by
          rw [show (0 : ℝ) - y = -y by ring, heven y]
        rw [hzero]
        push_cast
        ring
      · refine Continuous.intervalIntegrable ?_ _ _
        fun_prop
      · refine Continuous.intervalIntegrable ?_ _ _
        fun_prop
    rw [h1, convSource]
    field_simp
  have hcross : (∫ x in (0 : ℝ)..1, fourierChar (-i) x * ((k (x - 1) - k x : ℝ) : ℂ))
      = -(2 * (Real.pi : ℂ) * Complex.I * convSource k (-i)) := by
    have h1 : (∫ x in (0 : ℝ)..1, fourierChar (-i) x * ((k (x - 1) - k x : ℝ) : ℂ))
        = ∫ x in (0 : ℝ)..1, ((k (1 - x) - k x : ℝ) : ℂ) * fourierChar (-i) x := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      have hflip : k (x - 1) = k (1 - x) := by
        rw [← heven (x - 1)]
        congr 1
        ring
      rw [hflip]
      ring
    rw [h1, convSource]
    field_simp
  rw [hbdry, hcross, convSource_neg] at hcomb
  have hfinal : 2 * (Real.pi : ℂ) * Complex.I * (((i : ℂ) - j) * convMatrix k i j)
      = 2 * (Real.pi : ℂ) * Complex.I * (convSource k j - convSource k i) := by
    rw [← mul_assoc, hcomb]
    ring
  exact mul_left_cancel₀ hcne hfinal

/-! ## Reflection invariance -/

/-- Reflecting the interval and the frequency leaves the truncated convolution unchanged. -/
theorem truncConv_reflect {k : ℝ → ℝ} (heven : ∀ u, k (-u) = k u)
    (j : ℤ) (x : ℝ) :
    truncConv k (fourierChar (-j)) (1 - x) = truncConv k (fourierChar j) x := by
  have hcomp := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 : ℝ))
    (fun y : ℝ => ((k (1 - x - y) : ℝ) : ℂ) * fourierChar (-j) y) (1 : ℝ)
  simp only [sub_zero, sub_self] at hcomp
  rw [truncConv, ← hcomp, truncConv]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have harg : (1 : ℝ) - x - (1 - u) = -(x - u) := by ring
  rw [harg, heven (x - u), fourierChar_neg_one_sub]

/-- **The matrix is reflection invariant.** -/
theorem convMatrix_reflect {k : ℝ → ℝ} (heven : ∀ u, k (-u) = k u)
    (i j : ℤ) : convMatrix k (-i) (-j) = convMatrix k i j := by
  have hcomp := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 : ℝ))
    (fun x : ℝ => fourierChar (-(-i)) x * truncConv k (fourierChar (-j)) x) (1 : ℝ)
  simp only [sub_zero, sub_self] at hcomp
  rw [convMatrix, ← hcomp, convMatrix]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [fourierChar_neg_one_sub (-i) t, truncConv_reflect heven]

/-! ## The real divided-difference law -/

/-- **The real form of the commutator law.** -/
theorem convMatrix_re_commutator {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) (i j : ℤ) :
    ((i : ℝ) - (j : ℝ)) * (convMatrix k i j).re
      = (convSource k j).re - (convSource k i).re := by
  have h := congrArg Complex.re (convMatrix_commutator hk hk'c heven i j)
  simpa [Complex.sub_re, Complex.mul_re, Complex.sub_im] using h

theorem convSource_re_neg (k : ℝ → ℝ) (j : ℤ) :
    (convSource k (-j)).re = -(convSource k j).re := by
  rw [convSource_neg]
  simp

/-! ## Orthonormality of the exponential basis on the unit interval -/

theorem fourierChar_conj (j : ℤ) (x : ℝ) :
    (starRingEnd ℂ) (fourierChar j x) = fourierChar (-j) x := by
  have hz : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (x : ℂ)
      = ((2 * Real.pi * j * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hz' : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((-j : ℤ) : ℂ) * (x : ℂ)
      = -(((2 * Real.pi * j * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [fourierChar, fourierChar, hz, hz', ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem fourierChar_add (i j : ℤ) (x : ℝ) :
    fourierChar i x * fourierChar j x = fourierChar (i + j) x := by
  rw [fourierChar, fourierChar, fourierChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_fourierChar (m : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierChar m x) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [fourierChar]
  · rw [if_neg hm]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hmc
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => fourierChar m s / (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)))
          (fourierChar m x) x := by
      intro x _
      have h := (hasDerivAt_fourierChar m x).div_const (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ))
      refine h.congr_deriv ?_
      field_simp
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((continuous_fourierChar m).intervalIntegrable _ _)
    rw [hint, fourierChar_one, fourierChar_zero, sub_self]

theorem integral_fourierChar_orthonormal (i j : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierChar (-i) x * fourierChar j x) = if i = j then 1 else 0 := by
  have hprod : ∀ x : ℝ, fourierChar (-i) x * fourierChar j x = fourierChar (j - i) x := by
    intro x
    rw [fourierChar_add]
    congr 1
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hprod x), integral_fourierChar]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij, if_neg (by omega : ¬ j - i = 0)]

/-! ## Conjugation -/

theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    (starRingEnd ℂ) (∫ x in a..b, f x) = ∫ x in a..b, (starRingEnd ℂ) (f x) := by
  simp only [intervalIntegral, map_sub, integral_conj]

theorem truncConv_conj (k : ℝ → ℝ) (j : ℤ) (x : ℝ) :
    (starRingEnd ℂ) (truncConv k (fourierChar j) x) = truncConv k (fourierChar (-j)) x := by
  rw [truncConv, intervalIntegral_conj, truncConv]
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [map_mul, Complex.conj_ofReal, fourierChar_conj]

/-- **The matrix is real.** -/
theorem convMatrix_conj {k : ℝ → ℝ} (i j : ℤ) :
    (starRingEnd ℂ) (convMatrix k i j) = convMatrix k (-i) (-j) := by
  rw [convMatrix, intervalIntegral_conj, convMatrix]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [map_mul, fourierChar_conj, truncConv_conj, neg_neg]

theorem convMatrix_im_eq_zero {k : ℝ → ℝ} (heven : ∀ u, k (-u) = k u) (i j : ℤ) :
    (convMatrix k i j).im = 0 := by
  have h : (starRingEnd ℂ) (convMatrix k i j) = convMatrix k i j := by
    rw [convMatrix_conj, convMatrix_reflect heven]
  have h2 := congrArg Complex.im h
  simp only [Complex.conj_im] at h2
  linarith

theorem convMatrix_ofReal_re {k : ℝ → ℝ} (heven : ∀ u, k (-u) = k u) (i j : ℤ) :
    (((convMatrix k i j).re : ℝ) : ℂ) = convMatrix k i j := by
  refine Complex.ext ?_ ?_
  · simp
  · simp [convMatrix_im_eq_zero heven]

/-- **The matrix is symmetric.**  Off the diagonal this is forced by the divided-difference law
alone. -/
theorem convMatrix_symm {k k' : ℝ → ℝ} (hk : ∀ u, HasDerivAt k (k' u) u)
    (hk'c : Continuous k') (heven : ∀ u, k (-u) = k u) (i j : ℤ) :
    convMatrix k i j = convMatrix k j i := by
  by_cases hij : i = j
  · rw [hij]
  · have h1 := convMatrix_commutator hk hk'c heven i j
    have h2 := convMatrix_commutator hk hk'c heven j i
    have hne : ((i : ℂ) - (j : ℂ)) ≠ 0 := by
      intro h
      exact hij (by exact_mod_cast sub_eq_zero.1 h)
    refine mul_left_cancel₀ hne ?_
    rw [h1]
    have h3 : ((i : ℂ) - (j : ℂ)) * convMatrix k j i
        = -(((j : ℂ) - (i : ℂ)) * convMatrix k j i) := by ring
    rw [h3, h2]
    ring

/-! ## The quadratic form of the truncated convolution on trigonometric polynomials -/

variable {ι : Type*} [Fintype ι]

/-- The trigonometric polynomial attached to a finite family of frequencies. -/
def indexTrigPoly (m : ι → ℤ) (v : ι → ℂ) (x : ℝ) : ℂ := ∑ i, v i * fourierChar (m i) x

theorem continuous_indexTrigPoly (m : ι → ℤ) (v : ι → ℂ) : Continuous (indexTrigPoly m v) := by
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul (continuous_fourierChar (m j))

theorem indexTrigPoly_conj (m : ι → ℤ) (v : ι → ℂ) (x : ℝ) :
    (starRingEnd ℂ) (indexTrigPoly m v x)
      = ∑ i, (starRingEnd ℂ) (v i) * fourierChar (-m i) x := by
  rw [indexTrigPoly, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, fourierChar_conj]

theorem truncConv_indexTrigPoly {k : ℝ → ℝ} (hkc : Continuous k) (m : ι → ℤ) (v : ι → ℂ)
    (x : ℝ) :
    truncConv k (indexTrigPoly m v) x = ∑ j, v j * truncConv k (fourierChar (m j)) x := by
  rw [truncConv]
  have hsplit : ∀ y : ℝ, ((k (x - y) : ℝ) : ℂ) * indexTrigPoly m v y
      = ∑ j, v j * (((k (x - y) : ℝ) : ℂ) * fourierChar (m j) y) := by
    intro y
    rw [indexTrigPoly, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (fun y _ => hsplit y), intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => by
      rw [intervalIntegral.integral_const_mul, truncConv]
  · intro j _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul
      ((Complex.continuous_ofReal.comp (hkc.comp (continuous_const.sub continuous_id))).mul
        (continuous_fourierChar (m j)))

/-- **The `L²` norm of a trigonometric polynomial is the `ℓ²` norm of its coefficients.** -/
theorem integral_indexTrigPoly_normSq {m : ι → ℤ} (hm : Function.Injective m) (v : ι → ℂ) :
    (∫ x in (0 : ℝ)..1, (starRingEnd ℂ) (indexTrigPoly m v x) * indexTrigPoly m v x)
      = ∑ i, (starRingEnd ℂ) (v i) * v i := by
  have hsplit : ∀ x : ℝ, (starRingEnd ℂ) (indexTrigPoly m v x) * indexTrigPoly m v x
      = ∑ i, ∑ j, ((starRingEnd ℂ) (v i) * v j) *
          (fourierChar (-m i) x * fourierChar (m j) x) := by
    intro x
    rw [indexTrigPoly_conj, indexTrigPoly, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (fun x _ => hsplit x), intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.sum_eq_single i]
      · rw [intervalIntegral.integral_const_mul, integral_fourierChar_orthonormal, if_pos rfl,
          mul_one]
      · intro j _ hji
        rw [intervalIntegral.integral_const_mul, integral_fourierChar_orthonormal,
          if_neg (fun h => hji (hm h.symm)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · intro j _
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul ((continuous_fourierChar _).mul (continuous_fourierChar _))
  · intro i _
    refine Continuous.intervalIntegrable ?_ _ _
    refine continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_fourierChar _).mul (continuous_fourierChar _))

/-- **The quadratic form is the matrix form.**  The truncated-convolution pairing of a
trigonometric polynomial with itself is the sesquilinear form of the matrix `Q` on its
coefficients. -/
theorem integral_indexTrigPoly_truncConv {k : ℝ → ℝ} (hkc : Continuous k) (m : ι → ℤ)
    (v : ι → ℂ) :
    (∫ x in (0 : ℝ)..1,
        (starRingEnd ℂ) (indexTrigPoly m v x) * truncConv k (indexTrigPoly m v) x)
      = ∑ i, ∑ j, (starRingEnd ℂ) (v i) * convMatrix k (m i) (m j) * v j := by
  have hsplit : ∀ x : ℝ,
      (starRingEnd ℂ) (indexTrigPoly m v x) * truncConv k (indexTrigPoly m v) x
      = ∑ i, ∑ j, ((starRingEnd ℂ) (v i) * v j) *
          (fourierChar (-m i) x * truncConv k (fourierChar (m j)) x) := by
    intro x
    rw [indexTrigPoly_conj, truncConv_indexTrigPoly hkc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (fun x _ => hsplit x), intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_const_mul, convMatrix]
      ring
    · intro j _
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul ((continuous_fourierChar _).mul
        (continuous_truncConv hkc (continuous_fourierChar (m j))))
  · intro i _
    refine Continuous.intervalIntegrable ?_ _ _
    refine continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_fourierChar _).mul
      (continuous_truncConv hkc (continuous_fourierChar (m j))))

end

end GaloisForLFunctions.HTGeometry
