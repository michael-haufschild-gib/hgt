import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The fractional part and the zeta function

Abel summation writes the zeta function on `Re s > 1` as `s` times the Mellin integral of the
integer part.  Replacing the integer part by `t - fract t` and evaluating the elementary half of
the integral gives the classical formula

`integral_1^infinity fract(t) t^(-s-1) dt = 1/(s-1) - zeta(s)/s`.

The left-hand side converges on the whole half-plane `Re s > 0`, which is what makes this the
standard analytic continuation of zeta past the abscissa of convergence.
-/

open Complex Real MeasureTheory Set Filter Topology Finset

noncomputable section

namespace RHTower

theorem measurable_fract_complex : Measurable fun t : ℝ => ((Int.fract t : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp measurable_fract

theorem norm_fract_le (t : ℝ) : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
  exact (Int.fract_lt_one t).le

theorem integrableOn_Ioi_one_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  refine integrableOn_Ioi_cpow_of_lt ?_ one_pos
  rw [Complex.neg_re, Complex.add_re, Complex.one_re]
  linarith

theorem integrableOn_Ioi_one_fract_cpow {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
  (integrableOn_Ioi_one_cpow hs).bdd_mul
    (measurable_fract_complex.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => norm_fract_le t)

/-- **Abel summation for zeta.**  On `Re s > 1` the zeta function is `s` times the Mellin integral
of the integer part. -/
theorem riemannZeta_eq_mul_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hfun : (fun n : ℕ => ∑ k ∈ Icc 1 n, ‖(1 : ℕ → ℂ) k‖) = fun n : ℕ => (n : ℝ) := by
    funext n
    simp [Nat.card_Icc]
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, ‖(1 : ℕ → ℂ) k‖) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    rw [hfun]
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun n => ?_)
    rw [Real.rpow_one, one_mul]
  have hmain := LSeries_eq_mul_integral' (1 : ℕ → ℂ) (r := 1) zero_le_one hs hO
  rw [LSeries_one_eq_riemannZeta hs] at hmain
  rw [hmain]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  congr 1
  simp [Nat.card_Icc]

/-- **The Mellin integral of the fractional part.**  The elementary half of the Abel-summation
formula, on `Re s > 1`. -/
theorem integral_Ioi_one_fract_cpow {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) =
      1 / (s - 1) - riemannZeta s / s := by
  have hs0 : (0 : ℝ) < s.re := by linarith
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs0
    simp at hs0
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have h1 : s = 1 := sub_eq_zero.mp h
    rw [h1, Complex.one_re] at hs
    exact lt_irrefl 1 hs
  -- the integer part splits
  have hsplit : ∀ t ∈ Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_trans one_pos (mem_Ioi.mp ht)
    have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htpos)
    have hfloor : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      have h : ((⌊t⌋₊ : ℕ) : ℤ) = ⌊t⌋ := Int.natCast_floor_eq_floor htpos.le
      have h2 : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
        have h3 : ((⌊t⌋₊ : ℕ) : ℝ) = ((⌊t⌋ : ℤ) : ℝ) := by
          exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h
        rw [h3, Int.self_sub_fract]
      rw [show ((⌊t⌋₊ : ℕ) : ℂ) = (((⌊t⌋₊ : ℕ) : ℝ) : ℂ) by push_cast; ring, h2]
      push_cast
      ring
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [show (-s : ℂ) = 1 + -(s + 1) by ring, Complex.cpow_add _ _ htne, Complex.cpow_one]
    rw [hfloor, hpow]
    ring
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ one_pos
    rw [Complex.neg_re]
    linarith
  have hint2 := integrableOn_Ioi_one_fract_cpow hs0
  have hzeta := riemannZeta_eq_mul_integral_floor hs
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hint1 hint2] at hzeta
  have hpow : (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (by rw [Complex.neg_re]; linarith) one_pos,
      Complex.ofReal_one, Complex.one_cpow, show (-s + 1 : ℂ) = -(s - 1) by ring]
    field_simp
  rw [hpow] at hzeta
  have hJ : riemannZeta s / s = 1 / (s - 1) -
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [hzeta, mul_comm, mul_div_assoc, div_self hsne, mul_one]
  linear_combination hJ



/-! ## Analytic continuation to the right half-plane -/

/-- The fractional part restricted to the tail of the positive ray. -/
def fractTailKernel : ℝ → ℂ := Set.indicator (Ioi 1) fun t : ℝ => ((Int.fract t : ℝ) : ℂ)

theorem measurable_fractTailKernel : Measurable fractTailKernel :=
  measurable_fract_complex.indicator measurableSet_Ioi

theorem norm_fractTailKernel_le (t : ℝ) : ‖fractTailKernel t‖ ≤ 1 := by
  by_cases h : t ∈ Ioi (1 : ℝ)
  · rw [fractTailKernel, Set.indicator_of_mem h]
    exact norm_fract_le t
  · rw [fractTailKernel, Set.indicator_of_notMem h, norm_zero]
    norm_num

theorem fractTailKernel_eq_zero_of_lt_one {t : ℝ} (ht : t ≤ 1) : fractTailKernel t = 0 :=
  Set.indicator_of_notMem (by simpa using ht) _

theorem mellin_fractTailKernel (s : ℂ) :
    mellin fractTailKernel (-s) =
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  have hpt : ∀ t : ℝ, (t : ℂ) ^ ((-s : ℂ) - 1) • fractTailKernel t =
      Set.indicator (Ioi 1) (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) t := by
    intro t
    by_cases h : t ∈ Ioi (1 : ℝ)
    · rw [fractTailKernel, Set.indicator_of_mem h, Set.indicator_of_mem h, smul_eq_mul,
        show ((-s : ℂ) - 1) = -(s + 1) by ring]
      ring
    · rw [fractTailKernel, Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_zero]
  have hsub : Set.Ioi (0 : ℝ) ∩ Set.Ioi 1 = Set.Ioi 1 := by
    rw [Set.inter_eq_right]
    exact fun t ht => lt_trans one_pos (mem_Ioi.mp ht)
  simp only [hpt]
  rw [setIntegral_indicator measurableSet_Ioi, hsub]

theorem differentiableAt_mellin_fractTailKernel {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin fractTailKernel) (-s) := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
  · refine (MeasureTheory.locallyIntegrable_iff.mpr ?_).locallyIntegrableOn _
    intro K hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      measurable_fractTailKernel.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => norm_fractTailKernel_le t)
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [one_mul, neg_zero, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht 0),
      Real.rpow_zero]
    exact norm_fractTailKernel_le t
  · rw [Complex.neg_re]
    linarith
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht ht1
    rw [fractTailKernel_eq_zero_of_lt_one (le_of_lt ht1), norm_zero, zero_mul]
  · rw [Complex.neg_re]
    linarith



/-! ## The punctured right half-plane -/

/-- The right half-plane with the pole of zeta removed. -/
def puncturedRightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re ∧ s ≠ 1}

theorem isOpen_puncturedRightHalfPlane : IsOpen puncturedRightHalfPlane := by
  have h1 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  exact h1.inter h2

/-- **The punctured right half-plane is connected.**  It is covered by four convex half-plane
intersections, chained through explicit common points. -/
theorem isPreconnected_puncturedRightHalfPlane : IsPreconnected puncturedRightHalfPlane := by
  set B1 : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1} with hB1
  set B2 : Set ℂ := {s : ℂ | 1 < s.re} with hB2
  set B3 : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im} with hB3
  set B4 : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0} with hB4
  have hc1 : IsPreconnected B1 :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hc2 : IsPreconnected B2 := (convex_halfSpace_re_gt 1).isPreconnected
  have hc3 : IsPreconnected B3 :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hc4 : IsPreconnected B4 :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hu13 : IsPreconnected (B1 ∪ B3) := by
    refine IsPreconnected.union (⟨1 / 2, 1⟩ : ℂ) ?_ ?_ hc1 hc3 <;>
      exact ⟨by norm_num, by norm_num⟩
  have hu134 : IsPreconnected (B1 ∪ B3 ∪ B4) := by
    refine IsPreconnected.union (⟨1 / 2, -1⟩ : ℂ) ?_ ?_ hu13 hc4
    · exact Or.inl ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
  have hall : IsPreconnected (B1 ∪ B3 ∪ B4 ∪ B2) := by
    refine IsPreconnected.union (⟨2, 1⟩ : ℂ) ?_ ?_ hu134 hc2
    · exact Or.inl (Or.inr ⟨by norm_num, by norm_num⟩)
    · show (1 : ℝ) < (2 : ℝ)
      norm_num
  have hset : puncturedRightHalfPlane = B1 ∪ B3 ∪ B4 ∪ B2 := by
    ext s
    constructor
    · rintro ⟨hre, hne⟩
      rcases lt_trichotomy s.re 1 with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hre, h⟩))
      · rcases lt_trichotomy s.im 0 with hi | hi | hi
        · exact Or.inl (Or.inr ⟨hre, hi⟩)
        · exact absurd (Complex.ext h hi) hne
        · exact Or.inl (Or.inl (Or.inr ⟨hre, hi⟩))
      · exact Or.inr h
    · rintro (((⟨hre, hlt⟩ | ⟨hre, him⟩) | ⟨hre, him⟩) | hgt)
      · exact ⟨hre, fun h => by rw [h] at hlt; norm_num [Complex.one_re] at hlt⟩
      · exact ⟨hre, fun h => by rw [h] at him; norm_num [Complex.one_im] at him⟩
      · exact ⟨hre, fun h => by rw [h] at him; norm_num [Complex.one_im] at him⟩
      · refine ⟨lt_trans one_pos hgt, fun h => ?_⟩
        rw [h] at hgt
        have hone : (1 : ℝ) < (1 : ℂ).re := hgt
        rw [Complex.one_re] at hone
        exact lt_irrefl 1 hone
  rw [hset]
  exact hall

/-- **The Mellin integral of the fractional part on the right half-plane.**  Analytic continuation
from the region of absolute convergence of the zeta series. -/
theorem integral_Ioi_one_fract_cpow_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) =
      1 / (s - 1) - riemannZeta s / s := by
  set F : ℂ → ℂ :=
    fun w => ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) with hFdef
  set G : ℂ → ℂ := fun w => 1 / (w - 1) - riemannZeta w / w with hGdef
  have hFeq : F = (mellin fractTailKernel) ∘ (fun w : ℂ => -w) := by
    funext w
    exact (mellin_fractTailKernel w).symm
  have hFdiff : DifferentiableOn ℂ F puncturedRightHalfPlane := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rw [hFeq]
    exact (differentiableAt_mellin_fractTailKernel hz.1).comp z (differentiable_neg z)
  have hGdiff : DifferentiableOn ℂ G puncturedRightHalfPlane := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hz0 : z ≠ 0 := by
      intro h
      have hzre := hz.1
      rw [h, Complex.zero_re] at hzre
      exact lt_irrefl 0 hzre
    have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 / (w - 1)) z :=
      (differentiableAt_const 1).div (differentiableAt_id.sub (differentiableAt_const 1))
        (sub_ne_zero.mpr hz.2)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => riemannZeta w / w) z :=
      (differentiableAt_riemannZeta hz.2).div differentiableAt_id hz0
    exact h1.sub h2
  have hFa := hFdiff.analyticOnNhd isOpen_puncturedRightHalfPlane
  have hGa := hGdiff.analyticOnNhd isOpen_puncturedRightHalfPlane
  have hmem2 : (2 : ℂ) ∈ puncturedRightHalfPlane := by
    constructor
    · norm_num
    · intro h
      have hre := congrArg Complex.re h
      rw [show ((2 : ℂ)).re = (2 : ℝ) by norm_num, Complex.one_re] at hre
      norm_num at hre
  have heq : F =ᶠ[nhds (2 : ℂ)] G := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds (by norm_num)) fun w hw => ?_
    exact integral_Ioi_one_fract_cpow hw
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa isPreconnected_puncturedRightHalfPlane
    hmem2 heq ⟨hs, hs1⟩



/-! ## The full Mellin transform of the fractional part -/

theorem integrableOn_Ioc_zero_one_fract_cpow {w : ℂ} (hw : w.re < 1) :
    IntegrableOn (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1)))
      (Set.Ioc 0 1) := by
  have hcpow : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-w)) (Set.Ioc 0 1) := by
    have h := intervalIntegral.intervalIntegrable_cpow' (a := (0 : ℝ)) (b := 1) (r := -w)
      (by rw [Complex.neg_re]; linarith)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h
  refine hcpow.congr_fun_ae ?_
  have hne1 : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), u ≠ 1 := by
    refine ae_restrict_of_ae ?_
    rw [Filter.eventually_iff, mem_ae_iff,
      show {u : ℝ | u ≠ 1}ᶜ = {(1 : ℝ)} by ext x; simp]
    exact MeasureTheory.measure_singleton 1
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hne1] with u hu0 hune
  have hu : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hu0.1, lt_of_le_of_ne hu0.2 hune⟩
  have hfr : Int.fract u = u := Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩
  have hune : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu.1)
  rw [hfr, show (-w : ℂ) = 1 + -(w + 1) by ring, Complex.cpow_add _ _ hune, Complex.cpow_one]

theorem integral_Ioc_zero_one_fract_cpow {w : ℂ} (hw : w.re < 1) :
    (∫ u in Set.Ioc (0 : ℝ) 1, ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1))) = 1 / (1 - w) := by
  have hne : (-w + 1 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hcongr : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1)) = (u : ℂ) ^ (-w) := by
    intro u hu
    have hfr : Int.fract u = u := Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩
    have hune : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu.1)
    rw [hfr, show (-w : ℂ) = 1 + -(w + 1) by ring, Complex.cpow_add _ _ hune, Complex.cpow_one]
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hcongr,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl (by rw [Complex.neg_re]; linarith)),
    Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hne, sub_zero,
    show (-w + 1 : ℂ) = 1 - w by ring]

/-- **The Mellin transform of the fractional part on the critical strip.**  On `0 < Re w < 1` the
whole half-line integral of the fractional part is `-zeta(w)/w`: the pole terms of the two halves
cancel exactly. -/
theorem integral_Ioi_zero_fract_cpow {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ u in Set.Ioi (0 : ℝ), ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1))) =
      -(riemannZeta w / w) := by
  have hwne1 : w ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw1
    exact lt_irrefl 1 hw1
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
    (integrableOn_Ioc_zero_one_fract_cpow hw1) (integrableOn_Ioi_one_fract_cpow hw0),
    integral_Ioc_zero_one_fract_cpow hw1, integral_Ioi_one_fract_cpow_of_re_pos hw0 hwne1]
  have h1 : (1 : ℂ) - w ≠ 0 := by
    intro h
    exact hwne1 (by linear_combination -h)
  have h2 : w - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hwne1
  field_simp
  ring



/-! ## Dilations of the fractional-part kernel -/

theorem integrableOn_Ioi_zero_fract_cpow {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1)))
      (Set.Ioi 0) := by
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hunion]
  exact (integrableOn_Ioc_zero_one_fract_cpow hw1).union (integrableOn_Ioi_one_fract_cpow hw0)

theorem fract_dilate_cpow_eq {w : ℂ} {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    ((Int.fract (c * t) : ℝ) : ℂ) * ((c * t : ℝ) : ℂ) ^ (-(w + 1)) =
      ((c : ℝ) : ℂ) ^ (-(w + 1)) * (((Int.fract (c * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le ht.le]
  ring

theorem integrableOn_Ioi_zero_fract_dilate_cpow {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => ((Int.fract (c * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)))
      (Set.Ioi 0) := by
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hcpowne : ((c : ℝ) : ℂ) ^ (-(w + 1)) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hcne)
  have hbase := integrableOn_Ioi_zero_fract_cpow hw0 hw1
  have hcomp : IntegrableOn
      (fun t : ℝ => ((Int.fract (c * t) : ℝ) : ℂ) * ((c * t : ℝ) : ℂ) ^ (-(w + 1)))
      (Set.Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1))) 0 hc).mpr
      (by rwa [mul_zero])
    exact h
  refine (hcomp.smul (((c : ℝ) : ℂ) ^ (-(w + 1)))⁻¹).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Pi.smul_apply, smul_eq_mul, fract_dilate_cpow_eq hc (mem_Ioi.mp ht), ← mul_assoc,
    inv_mul_cancel₀ hcpowne, one_mul]

/-- **The dilated fractional-part kernel.**  Dilating the argument by `c` multiplies the Mellin
integral by `c^w`. -/
theorem integral_Ioi_zero_fract_dilate_cpow {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {c : ℝ} (hc : 0 < c) :
    (∫ t in Set.Ioi (0 : ℝ), ((Int.fract (c * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))) =
      ((c : ℝ) : ℂ) ^ w * (-(riemannZeta w / w)) := by
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hcpowne : ((c : ℝ) : ℂ) ^ (-(w + 1)) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hcne)
  have hkey := integral_comp_mul_left_Ioi
    (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(w + 1))) 0 hc
  rw [mul_zero] at hkey
  have hpt : (∫ t in Set.Ioi (0 : ℝ),
      ((Int.fract (c * t) : ℝ) : ℂ) * ((c * t : ℝ) : ℂ) ^ (-(w + 1))) =
      ((c : ℝ) : ℂ) ^ (-(w + 1)) *
        ∫ t in Set.Ioi (0 : ℝ), ((Int.fract (c * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact fract_dilate_cpow_eq hc (mem_Ioi.mp ht)
  rw [hpt, integral_Ioi_zero_fract_cpow hw0 hw1] at hkey
  have hfin : ((c : ℝ) : ℂ) ^ (-(w + 1)) *
      (∫ t in Set.Ioi (0 : ℝ), ((Int.fract (c * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))) =
      ((c : ℝ) : ℂ)⁻¹ * (-(riemannZeta w / w)) := by
    rw [hkey, Complex.real_smul, Complex.ofReal_inv]
  have hAinv : (((c : ℝ) : ℂ) ^ (-(w + 1)))⁻¹ = ((c : ℝ) : ℂ) ^ (w + 1) := by
    rw [← Complex.cpow_neg, neg_neg]
  have hX : (∫ t in Set.Ioi (0 : ℝ), ((Int.fract (c * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))) =
      (((c : ℝ) : ℂ) ^ (-(w + 1)))⁻¹ * (((c : ℝ) : ℂ) ^ (-(w + 1)) *
        ∫ t in Set.Ioi (0 : ℝ), ((Int.fract (c * t) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))) := by
    rw [← mul_assoc, inv_mul_cancel₀ hcpowne, one_mul]
  rw [hX, hfin, hAinv, Complex.cpow_add _ _ hcne, Complex.cpow_one, mul_assoc,
    ← mul_assoc ((c : ℝ) : ℂ) (((c : ℝ) : ℂ))⁻¹, mul_inv_cancel₀ hcne, one_mul]

theorem ofReal_fract_rpow {σ : ℝ} {u : ℝ} (hu : 0 < u) :
    ((Int.fract u * u ^ (-(σ + 1)) : ℝ) : ℂ)
      = ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(((σ : ℝ) : ℂ) + 1)) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hu.le]
  push_cast
  ring

/-- **Zeta has no zero on the real segment `(0,1)`.**  The fractional-part representation
`zeta(s)/s = - integral_0^infinity fract(u) u^(-s-1) du` has a strictly positive integrand for a
real exponent, so the integral cannot vanish. -/
theorem riemannZeta_ne_zero_of_ofReal_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta ((σ : ℝ) : ℂ) ≠ 0 := by
  intro hz
  have hre : (((σ : ℝ) : ℂ)).re = σ := Complex.ofReal_re σ
  have hw0 : 0 < (((σ : ℝ) : ℂ)).re := by rw [hre]; exact h0
  have hw1 : (((σ : ℝ) : ℂ)).re < 1 := by rw [hre]; exact h1
  set f : ℝ → ℝ := fun u => Int.fract u * u ^ (-(σ + 1)) with hf
  have hcongr : EqOn (fun u : ℝ => ((f u : ℝ) : ℂ))
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(((σ : ℝ) : ℂ) + 1))) (Ioi 0) := by
    intro u hu
    exact ofReal_fract_rpow (mem_Ioi.mp hu)
  -- integrability
  have hIC : IntegrableOn
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(((σ : ℝ) : ℂ) + 1))) (Ioi 0) :=
    integrableOn_Ioi_zero_fract_cpow hw0 hw1
  have hICf : IntegrableOn (fun u : ℝ => ((f u : ℝ) : ℂ)) (Ioi 0) :=
    hIC.congr_fun (fun u hu => (hcongr hu).symm) measurableSet_Ioi
  have hIf : IntegrableOn f (Ioi 0) := by
    exact hICf.re
  -- the integral vanishes
  have hint := integral_Ioi_zero_fract_cpow hw0 hw1
  rw [hz] at hint
  have hzeroC : (∫ u in Ioi (0:ℝ), ((f u : ℝ) : ℂ)) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hint]
    simp
  have hzeroR : (∫ u in Ioi (0:ℝ), f u) = 0 := by
    have : ((∫ u in Ioi (0:ℝ), f u : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]; exact hzeroC
    exact_mod_cast this
  -- nonnegativity forces the integrand to vanish a.e.
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] f := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards with u hu
    exact mul_nonneg (Int.fract_nonneg u) (Real.rpow_nonneg (le_of_lt (mem_Ioi.mp hu)) _)
  have hae : f =ᵐ[volume.restrict (Ioi (0:ℝ))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hIf).mp hzeroR
  have hae' : ∀ᵐ u ∂volume, u ∈ Ioi (0:ℝ) → f u = 0 :=
    (ae_restrict_iff' measurableSet_Ioi).mp hae
  -- but the integrand is strictly positive on `(1,2)`
  have hnull : volume (Ioo (1:ℝ) 2) = 0 := by
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hae'] with u hu hmem
    have hu1 : (1:ℝ) < u := hmem.1
    have hu2 : u < 2 := hmem.2
    have hupos : 0 < u := by linarith
    have hfl : ⌊u⌋ = 1 := by
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast; linarith
    have hfract : Int.fract u = u - 1 := by
      have : Int.fract u = u - (⌊u⌋ : ℝ) := rfl
      rw [this, hfl]; norm_num
    have hpos : 0 < f u := by
      rw [hf]
      refine mul_pos ?_ (Real.rpow_pos_of_pos hupos _)
      rw [hfract]; linarith
    exact absurd (hu (mem_Ioi.mpr hupos)) (ne_of_gt hpos)
  rw [Real.volume_Ioo] at hnull
  norm_num at hnull

end RHTower
