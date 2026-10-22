import GaloisForLFunctions.RHTower.Deninger.DeningerCapVanishing
import GaloisForLFunctions.RHTower.Deninger.DeningerZetaLeftLine
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonZeroDivisor

/-!
# The reverse Mellin estimate on a line to the left of the critical strip

Second-order vanishing at the origin pushes the Mellin transform of a member of Meyer's space to
the half plane `Re s > −2`, where it is holomorphic.  The factorization `M(Zf) = ζ·M(f)`, proved
for `Re s > 1`, therefore propagates by the identity theorem to the whole of that half plane minus
the pole, in particular to the line `Re s = −1` away from the real axis.

There the archimedean lower bound for `ζ` inverts the factorization: `‖M(f)‖ ≤ 8π²‖M(Zf)‖`.  Two
vertical lines, one on each side of the critical strip, are now available, and on neither of them
does anything about the zeros of `ζ` enter.

* `mellinConvergent_cap`, `differentiableAt_mellin_cap` : the Mellin transform on `Re s > −2`.
* `mellin_deningerPoissonValue_eq_zeta_mul_left` : the factorization on the left half plane.
* `norm_mellin_le_left_line` : **`‖M(f)(−1+it)‖ ≤ 8π²‖M(Zf)(−1+it)‖` for `t ≠ 0`.**
-/

open scoped Real SchwartzMap Topology
open Complex MeasureTheory Set Filter Asymptotics GaloisForLFunctions
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## The Mellin transform of a member of Meyer's space -/

theorem isBigO_cap_zero {f : 𝓢(ℝ, ℂ)} (he : ∀ x : ℝ, f (-x) = f x) (h0 : f 0 = 0) :
    (f : ℝ → ℂ) =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-(-2 : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr
    ⟨SchwartzMap.seminorm ℂ 0 0 (derivSCLM (derivSCLM f)), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hbound := norm_le_seminorm_mul_sq he h0 x
  have hnorm : ‖x ^ (-(-2 : ℝ))‖ = x ^ (2 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    norm_num
  rw [hnorm]
  have hpow : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    rw [Real.rpow_two]
  rw [hpow]
  exact hbound

theorem mellinConvergent_cap {f : 𝓢(ℝ, ℂ)} (he : ∀ x : ℝ, f (-x) = f x) (h0 : f 0 = 0)
    {s : ℂ} (hs : -2 < s.re) : MellinConvergent (f : ℝ → ℂ) s :=
  mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := -2)
    ((f.continuous.locallyIntegrable).locallyIntegrableOn _)
    (schwartz_isBigO_atTop f (s.re + 1)) (by linarith) (isBigO_cap_zero he h0) hs

theorem differentiableAt_mellin_cap {f : 𝓢(ℝ, ℂ)} (he : ∀ x : ℝ, f (-x) = f x) (h0 : f 0 = 0)
    {s : ℂ} (hs : -2 < s.re) : DifferentiableAt ℂ (mellin (f : ℝ → ℂ)) s :=
  mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := -2)
    ((f.continuous.locallyIntegrable).locallyIntegrableOn _)
    (schwartz_isBigO_atTop f (s.re + 1)) (by linarith) (isBigO_cap_zero he h0) hs

/-! ## The region to the left -/

/-- The half plane `Re s > −2` on one side of the real axis, joined to the region of absolute
convergence, with the pole of zeta excluded. -/
def deningerZetaRegionLeft (upper : Bool) : Set ℂ :=
  {s : ℂ | -2 < s.re ∧ (if upper then 0 < s.im else s.im < 0)} ∪ {s : ℂ | 1 < s.re}

theorem isOpen_deningerZetaRegionLeft (upper : Bool) : IsOpen (deningerZetaRegionLeft upper) := by
  refine IsOpen.union ?_ ?_
  · by_cases h : upper
    · have hset : {s : ℂ | -2 < s.re ∧ (if upper then 0 < s.im else s.im < 0)}
          = {s : ℂ | -2 < s.re} ∩ {s : ℂ | 0 < s.im} := by
        ext s
        simp [h]
      rw [hset]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    · have hset : {s : ℂ | -2 < s.re ∧ (if upper then 0 < s.im else s.im < 0)}
          = {s : ℂ | -2 < s.re} ∩ {s : ℂ | s.im < 0} := by
        ext s
        simp [h]
      rw [hset]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_im continuous_const)
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem convex_deningerZetaRegionLeft_left (upper : Bool) :
    Convex ℝ {s : ℂ | -2 < s.re ∧ (if upper then 0 < s.im else s.im < 0)} := by
  by_cases h : upper
  · have hset : {s : ℂ | -2 < s.re ∧ (if upper then 0 < s.im else s.im < 0)}
        = {s : ℂ | -2 < s.re} ∩ {s : ℂ | 0 < s.im} := by
      ext s
      simp [h]
    rw [hset]
    exact (convex_halfSpace_re_gt (-2)).inter (convex_halfSpace_im_gt 0)
  · have hset : {s : ℂ | -2 < s.re ∧ (if upper then 0 < s.im else s.im < 0)}
        = {s : ℂ | -2 < s.re} ∩ {s : ℂ | s.im < 0} := by
      ext s
      simp [h]
    rw [hset]
    exact (convex_halfSpace_re_gt (-2)).inter (convex_halfSpace_im_lt 0)

theorem isPreconnected_deningerZetaRegionLeft (upper : Bool) :
    IsPreconnected (deningerZetaRegionLeft upper) := by
  refine IsPreconnected.union (if upper then (2 : ℂ) + Complex.I else (2 : ℂ) - Complex.I)
    ?_ ?_ ?_ ?_
  · by_cases h : upper <;>
      simp [h, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  · by_cases h : upper <;> simp [h, Complex.add_re, Complex.sub_re]
  · exact (convex_deningerZetaRegionLeft_left upper).isPreconnected
  · exact (convex_halfSpace_re_gt 1).isPreconnected

theorem two_mem_deningerZetaRegionLeft (upper : Bool) :
    (2 : ℂ) ∈ deningerZetaRegionLeft upper := by
  right
  show (1 : ℝ) < (2 : ℂ).re
  norm_num

theorem ne_one_of_mem_deningerZetaRegionLeft {upper : Bool} {s : ℂ}
    (hs : s ∈ deningerZetaRegionLeft upper) : s ≠ 1 := by
  rcases hs with hs | hs
  · intro hone
    subst hone
    by_cases h : upper
    · have him : (0 : ℝ) < (1 : ℂ).im := by simpa [h] using hs.2
      norm_num at him
    · have him : (1 : ℂ).im < 0 := by simpa [h] using hs.2
      norm_num at him
  · intro hone
    subst hone
    have hre : (1 : ℝ) < (1 : ℂ).re := hs
    norm_num at hre

theorem re_gt_of_mem_deningerZetaRegionLeft {upper : Bool} {s : ℂ}
    (hs : s ∈ deningerZetaRegionLeft upper) : -2 < s.re := by
  rcases hs with hs | hs
  · exact hs.1
  · have hre : (1 : ℝ) < s.re := hs
    linarith

/-! ## The factorization to the left -/

/-- **The Mellin factorization on the left half plane.** -/
theorem mellin_deningerPoissonValue_eq_zeta_mul_left {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap)
    (upper : Bool) {s : ℂ} (hs : s ∈ deningerZetaRegionLeft upper) :
    mellin (deningerPoissonValue f) s = riemannZeta s * mellin (f : ℝ → ℂ) s := by
  obtain ⟨he, h0, _⟩ := (deningerMeyerCap_mem_iff f).mp hf
  set H : ℂ → ℂ := fun z => mellin (deningerPoissonValue f) z
    - riemannZeta z * mellin (f : ℝ → ℂ) z with hH
  have hdiff : DifferentiableOn ℂ H (deningerZetaRegionLeft upper) := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_mellin_deningerPoissonValue hf z).sub ?_
    exact (differentiableAt_riemannZeta (ne_one_of_mem_deningerZetaRegionLeft hz)).mul
      (differentiableAt_mellin_cap he h0 (re_gt_of_mem_deningerZetaRegionLeft hz))
  have hanal : AnalyticOnNhd ℂ H (deningerZetaRegionLeft upper) :=
    hdiff.analyticOnNhd (isOpen_deningerZetaRegionLeft upper)
  have hzero : H =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) ?_
      show (1 : ℝ) < (2 : ℂ).re
      norm_num
    filter_upwards [hmem] with z hz
    have hz' : 1 < z.re := hz
    show mellin (deningerPoissonValue f) z - riemannZeta z * mellin (f : ℝ → ℂ) z = 0
    rw [mellin_deningerPoissonValue f hz', sub_self]
  have heq := hanal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isPreconnected_deningerZetaRegionLeft upper) (two_mem_deningerZetaRegionLeft upper) hzero
  have hval : H s = 0 := heq hs
  rw [hH] at hval
  have hval' : mellin (deningerPoissonValue f) s - riemannZeta s * mellin (f : ℝ → ℂ) s = 0 :=
    hval
  linear_combination hval'

/-! ## The reverse estimate on the line -/

/-- **The reverse Mellin estimate on the line `Re s = −1`**, off the real axis. -/
theorem norm_mellin_le_left_line {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) {t : ℝ}
    (ht : t ≠ 0) :
    ‖mellin (f : ℝ → ℂ) (-1 + (t : ℂ) * I)‖
      ≤ 8 * π ^ 2 * ‖mellin (deningerPoissonValue f) (-1 + (t : ℂ) * I)‖ := by
  have hre : ((-1 : ℂ) + (t : ℂ) * I).re = -1 := by simp
  have him : ((-1 : ℂ) + (t : ℂ) * I).im = t := by simp
  have hmem : ∀ upper : Bool, (if upper then 0 < t else t < 0) →
      ((-1 : ℂ) + (t : ℂ) * I) ∈ deningerZetaRegionLeft upper := by
    intro upper hcond
    left
    refine ⟨by rw [hre]; norm_num, ?_⟩
    by_cases h : upper
    · simp only [h, if_pos] at hcond ⊢
      rw [him]
      exact hcond
    · simp only [h] at hcond ⊢
      rw [him]
      exact hcond
  have hfac : mellin (deningerPoissonValue f) ((-1 : ℂ) + (t : ℂ) * I)
      = riemannZeta ((-1 : ℂ) + (t : ℂ) * I) * mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I) := by
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · exact mellin_deningerPoissonValue_eq_zeta_mul_left hf false (hmem false (by simpa using hneg))
    · exact mellin_deningerPoissonValue_eq_zeta_mul_left hf true (hmem true (by simpa using hpos))
  have hzeta := norm_riemannZeta_left_line_ge_const t
  have hpi : (0 : ℝ) < 8 * π ^ 2 := by
    have := Real.pi_pos
    positivity
  have hnorm : ‖mellin (deningerPoissonValue f) ((-1 : ℂ) + (t : ℂ) * I)‖
      = ‖riemannZeta ((-1 : ℂ) + (t : ℂ) * I)‖
        * ‖mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I)‖ := by
    rw [hfac, norm_mul]
  rw [hnorm]
  have hmnn : 0 ≤ ‖mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I)‖ := norm_nonneg _
  have hstep : (1 / (8 * π ^ 2)) * ‖mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I)‖
      ≤ ‖riemannZeta ((-1 : ℂ) + (t : ℂ) * I)‖
        * ‖mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I)‖ :=
    mul_le_mul_of_nonneg_right hzeta hmnn
  have hmul : (8 * π ^ 2)
      * ((1 / (8 * π ^ 2)) * ‖mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I)‖)
      = ‖mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I)‖ := by
    field_simp
  calc ‖mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I)‖
      = (8 * π ^ 2)
        * ((1 / (8 * π ^ 2)) * ‖mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I)‖) := hmul.symm
    _ ≤ (8 * π ^ 2) * (‖riemannZeta ((-1 : ℂ) + (t : ℂ) * I)‖
        * ‖mellin (f : ℝ → ℂ) ((-1 : ℂ) + (t : ℂ) * I)‖) :=
        mul_le_mul_of_nonneg_left hstep hpi.le

end RHTower

end
