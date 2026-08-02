import GaloisForLFunctions.RHTower.DeningerPoissonMellin
import GaloisForLFunctions.RHTower.DeningerPoissonDerivative
import GaloisForLFunctions.RHTower.DeningerPoissonSchwartz

/-!
# The image of the Poisson operator vanishes on the zeros of zeta

A Poisson sum of a member of Meyer's space decays faster than every power at both multiplicative
ends, so its Mellin transform is differentiable everywhere; the Mellin transform of a Schwartz
function is differentiable on the right half plane.  The factorization `M(Zf) = ζ·M(f)` holds for
`Re s > 1`, and both sides are analytic on the half plane with the pole of `ζ` removed, so the
identity theorem propagates it to every point there.

Consequently `M(Zf)` vanishes at every non-real zero of `ζ` in the right half plane: the range of
the Poisson operator lies in the subspace cut out by the zero divisor of `ζ`.  That is the
mechanism by which the cokernel `M_ζ` sees the zeros.

* `isBigO_deningerPoissonValue_atTop`, `_zero` : the two-ended decay in `O`-form.
* `differentiableAt_mellin_deningerPoissonValue` : **`M(Zf)` is entire.**
* `mellin_deningerPoissonValue_eq_zeta_mul` : the factorization on the right half plane.
* `mellin_deningerPoissonValue_eq_zero_of_zeta_eq_zero` : **`M(Zf)` vanishes on the zeros.**
-/

open scoped Real SchwartzMap FourierTransform Topology
open Complex MeasureTheory Set Filter Asymptotics GaloisForLFunctions
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-! ## Continuity of the Poisson sum on the half line -/

theorem continuousOn_deningerPoissonValue (f : 𝓢(ℝ, ℂ)) :
    ContinuousOn (deningerPoissonValue f) (Ioi 0) := by
  have hlogc : ContinuousOn Real.log (Ioi (0 : ℝ)) := by
    refine Real.continuousOn_log.mono fun x hx => ?_
    have hx' : (0 : ℝ) < x := hx
    exact hx'.ne'
  have hlog : ContinuousOn (fun x : ℝ => deningerPoissonLog f (Real.log x)) (Ioi 0) :=
    (differentiable_deningerPoissonLog f).continuous.comp_continuousOn hlogc
  refine hlog.congr fun x hx => ?_
  have hx' : (0 : ℝ) < x := hx
  show deningerPoissonValue f x = deningerPoissonLog f (Real.log x)
  rw [deningerPoissonLog_eq, Real.exp_log hx']

theorem locallyIntegrableOn_deningerPoissonValue (f : 𝓢(ℝ, ℂ)) :
    LocallyIntegrableOn (deningerPoissonValue f) (Ioi 0) :=
  (continuousOn_deningerPoissonValue f).locallyIntegrableOn measurableSet_Ioi

/-! ## The two-ended decay in `O`-form -/

theorem isBigO_deningerPoissonValue_atTop {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) (a : ℝ) :
    (deningerPoissonValue f) =O[atTop] fun x : ℝ => x ^ (-a) := by
  set N : ℕ := ⌈a⌉₊ with hN
  have hexp : a ≤ (ccmRationalArchimedeanDecayExponent N : ℝ) := by
    have hceil : a ≤ (N : ℝ) := Nat.le_ceil a
    have hval : (ccmRationalArchimedeanDecayExponent N : ℝ) = 2 * ((N : ℝ) + 1) := by
      rw [ccmRationalArchimedeanDecayExponent]
      push_cast
      ring
    rw [hval]
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  refine Asymptotics.isBigO_iff.mpr
    ⟨ccmRationalArchimedeanDecayConstant f N / 2, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hbound := norm_deningerPoissonValue_le_large (deningerMeyerCap_even hf)
    (deningerMeyerCap_zero hf) N hx0
  have hpow : x ^ (ccmRationalArchimedeanDecayExponent N)
      = x ^ ((ccmRationalArchimedeanDecayExponent N : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  have hle : x ^ (-(ccmRationalArchimedeanDecayExponent N : ℝ)) ≤ x ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hnorm : ‖x ^ (-a)‖ = x ^ (-a) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  rw [hnorm]
  refine hbound.trans ?_
  have hrw : ccmRationalArchimedeanDecayConstant f N
      / x ^ (ccmRationalArchimedeanDecayExponent N) / 2
      = ccmRationalArchimedeanDecayConstant f N / 2
        * x ^ (-(ccmRationalArchimedeanDecayExponent N : ℝ)) := by
    rw [hpow, Real.rpow_neg hx0.le]
    field_simp
  rw [hrw]
  refine mul_le_mul_of_nonneg_left hle ?_
  have := ccmRationalArchimedeanDecayConstant_nonneg f N
  linarith

theorem isBigO_deningerPoissonValue_zero {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap) (N : ℕ) :
    (deningerPoissonValue f) =O[𝓝[>] (0 : ℝ)]
      fun x : ℝ => x ^ (-(1 - (ccmRationalArchimedeanDecayExponent N : ℝ))) := by
  refine Asymptotics.isBigO_iff.mpr
    ⟨ccmRationalArchimedeanDecayConstant (𝓕 f) N / 2, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hbound := norm_deningerPoissonValue_le_small (deningerMeyerCap_even hf)
    (deningerMeyerCap_zero hf) (deningerMeyerCap_fourier_zero hf) N hx0
  have hnorm : ‖x ^ (-(1 - (ccmRationalArchimedeanDecayExponent N : ℝ)))‖
      = x ^ ((ccmRationalArchimedeanDecayExponent N : ℝ) - 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    congr 1
    ring
  rw [hnorm]
  refine hbound.trans (le_of_eq ?_)
  have hple : 1 ≤ ccmRationalArchimedeanDecayExponent N :=
    (ccmRationalArchimedeanDecayExponent_gt_one N).le
  have hpow : x ^ (ccmRationalArchimedeanDecayExponent N - 1)
      = x ^ ((ccmRationalArchimedeanDecayExponent N : ℝ) - 1) := by
    rw [← Real.rpow_natCast x (ccmRationalArchimedeanDecayExponent N - 1)]
    congr 1
    push_cast [Nat.cast_sub hple]
    ring
  rw [hpow]
  ring

/-! ## Differentiability of the two Mellin transforms -/

theorem differentiableAt_mellin_deningerPoissonValue {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap)
    (s : ℂ) : DifferentiableAt ℂ (mellin (deningerPoissonValue f)) s := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 - (ccmRationalArchimedeanDecayExponent N : ℝ) < s.re := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 - s.re)
    refine ⟨N, ?_⟩
    have hval : (ccmRationalArchimedeanDecayExponent N : ℝ) = 2 * ((N : ℝ) + 1) := by
      rw [ccmRationalArchimedeanDecayExponent]
      push_cast
      ring
    rw [hval]
    linarith
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1)
    (b := 1 - (ccmRationalArchimedeanDecayExponent N : ℝ))
    (locallyIntegrableOn_deningerPoissonValue f)
    (isBigO_deningerPoissonValue_atTop hf (s.re + 1)) (by linarith)
    (isBigO_deningerPoissonValue_zero hf N) hN

theorem differentiableAt_mellin_schwartz (f : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (f : ℝ → ℂ)) s :=
  mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    ((f.continuous.locallyIntegrable).locallyIntegrableOn _)
    (schwartz_isBigO_atTop f (s.re + 1)) (by linarith) (schwartz_isBigO_zero f) hs

/-! ## The factorization on the right half plane -/

/-- The open half plane with the pole of zeta removed, on the side of a given nonzero
imaginary part. -/
def deningerZetaRegion (upper : Bool) : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ (if upper then 0 < s.im else s.im < 0)} ∪ {s : ℂ | 1 < s.re}

theorem isOpen_deningerZetaRegion (upper : Bool) : IsOpen (deningerZetaRegion upper) := by
  refine IsOpen.union ?_ ?_
  · by_cases h : upper
    · have hset : {s : ℂ | 0 < s.re ∧ (if upper then 0 < s.im else s.im < 0)}
          = {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im} := by
        ext s
        simp [h]
      rw [hset]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    · have hset : {s : ℂ | 0 < s.re ∧ (if upper then 0 < s.im else s.im < 0)}
          = {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0} := by
        ext s
        simp [h]
      rw [hset]
      exact (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_im continuous_const)
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem convex_deningerZetaRegion_left (upper : Bool) :
    Convex ℝ {s : ℂ | 0 < s.re ∧ (if upper then 0 < s.im else s.im < 0)} := by
  by_cases h : upper
  · have hset : {s : ℂ | 0 < s.re ∧ (if upper then 0 < s.im else s.im < 0)}
        = {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im} := by
      ext s
      simp [h]
    rw [hset]
    exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  · have hset : {s : ℂ | 0 < s.re ∧ (if upper then 0 < s.im else s.im < 0)}
        = {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0} := by
      ext s
      simp [h]
    rw [hset]
    exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)

theorem isPreconnected_deningerZetaRegion (upper : Bool) :
    IsPreconnected (deningerZetaRegion upper) := by
  refine IsPreconnected.union (if upper then (2 : ℂ) + Complex.I else (2 : ℂ) - Complex.I)
    ?_ ?_ ?_ ?_
  · by_cases h : upper <;>
      simp [h, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  · by_cases h : upper <;> simp [h, Complex.add_re, Complex.sub_re]
  · exact (convex_deningerZetaRegion_left upper).isPreconnected
  · exact (convex_halfSpace_re_gt 1).isPreconnected

theorem two_mem_deningerZetaRegion (upper : Bool) : (2 : ℂ) ∈ deningerZetaRegion upper := by
  right
  show (1 : ℝ) < (2 : ℂ).re
  norm_num

theorem ne_one_of_mem_deningerZetaRegion {upper : Bool} {s : ℂ}
    (hs : s ∈ deningerZetaRegion upper) : s ≠ 1 := by
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

theorem re_pos_of_mem_deningerZetaRegion {upper : Bool} {s : ℂ}
    (hs : s ∈ deningerZetaRegion upper) : 0 < s.re := by
  rcases hs with hs | hs
  · exact hs.1
  · have hre : (1 : ℝ) < s.re := hs
    linarith

/-- **The Mellin factorization propagates to the whole half plane.** -/
theorem mellin_deningerPoissonValue_eq_zeta_mul {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap)
    (upper : Bool) {s : ℂ} (hs : s ∈ deningerZetaRegion upper) :
    mellin (deningerPoissonValue f) s = riemannZeta s * mellin (f : ℝ → ℂ) s := by
  set H : ℂ → ℂ := fun z => mellin (deningerPoissonValue f) z
    - riemannZeta z * mellin (f : ℝ → ℂ) z with hH
  have hdiff : DifferentiableOn ℂ H (deningerZetaRegion upper) := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_mellin_deningerPoissonValue hf z).sub ?_
    exact (differentiableAt_riemannZeta (ne_one_of_mem_deningerZetaRegion hz)).mul
      (differentiableAt_mellin_schwartz f (re_pos_of_mem_deningerZetaRegion hz))
  have hanal : AnalyticOnNhd ℂ H (deningerZetaRegion upper) :=
    hdiff.analyticOnNhd (isOpen_deningerZetaRegion upper)
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
    (isPreconnected_deningerZetaRegion upper) (two_mem_deningerZetaRegion upper) hzero
  have hval : H s = 0 := heq hs
  rw [hH] at hval
  have hval' : mellin (deningerPoissonValue f) s - riemannZeta s * mellin (f : ℝ → ℂ) s = 0 := hval
  linear_combination hval'

/-- **The Mellin transform of a Poisson sum vanishes at every non-real zero of zeta in the right
half plane.**  The range of the Poisson operator lies in the subspace cut out by the zero divisor
of the zeta function. -/
theorem mellin_deningerPoissonValue_eq_zero_of_zeta_eq_zero {f : 𝓢(ℝ, ℂ)}
    (hf : f ∈ DeningerMeyerCap) {ρ : ℂ} (hre : 0 < ρ.re) (him : ρ.im ≠ 0)
    (hζ : riemannZeta ρ = 0) : mellin (deningerPoissonValue f) ρ = 0 := by
  rcases lt_or_gt_of_ne him with hlt | hgt
  · have hmem : ρ ∈ deningerZetaRegion false := by
      left
      exact ⟨hre, by simpa using hlt⟩
    rw [mellin_deningerPoissonValue_eq_zeta_mul hf false hmem, hζ, zero_mul]
  · have hmem : ρ ∈ deningerZetaRegion true := by
      left
      exact ⟨hre, by simpa using hgt⟩
    rw [mellin_deningerPoissonValue_eq_zeta_mul hf true hmem, hζ, zero_mul]

end RHTower

end
