import GaloisForLFunctions.RHTower.EvenOrderOnePartialFractionZeroCount
import GaloisForLFunctions.RHTower.XiCosineShiftDefectDisks

/-!
# Exceptional points of the cosine producer are confined to defect traces

Let `f` be entire, even, real, of order one, with `f(0) ≠ 0`, and let
`A_h(z) = (f(z + ih) + f(z − ih))/2`. On the real line `A_h(x) = Re f(x + ih)`. Its phase
`arg f(x + ih)` has derivative `Im (f'/f)(x + ih)`. The genus-one partial fraction, paired over
conjugate zeros `a = u + iv`, gives

  `Im(1/(z − a)) + Im(1/(z − ā)) = −2h((x − u)² + h² − v²) / (|z − a|²|z − ā|²)`,   `z = x + ih`

(`im_inv_sub_add_im_inv_sub_conj`). So if every zero satisfies `(x − u)² + h² > v²`, that is, if `x`
avoids the real traces `|x − u| ≤ √(v² − h²)` of all defect disks, then
`Im (f'/f)(x + ih) < 0` (`im_logDeriv_neg_of_local`). The phase is strictly monotone at `x`, and a
real zero of `A_h` at `x` is simple (`deriv_cosineShift_ne_zero_of_local`).

For `cos(hD)Ξ` (`deriv_cosineShiftXi_ne_zero_of_local`): a multiple real zero, which is an
exceptional point of the lossless producer, can occur at `x` only if `ξ` has a zero `ρ` with
`(x − Im ρ)² + h² ≤ (Re ρ − ½)²`. In particular `|Re ρ − ½| ≥ h` and `|x − Im ρ| < ½`. Under RH,
every real zero of `cos(hD)Ξ` is simple for every `h > 0`
(`deriv_cosineShiftXi_ne_zero_of_rh`).
-/

open Complex Filter Topology Set
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower

noncomputable section

variable {f : ℂ → ℂ}

/-- The conjugate-pair imaginary part identity at `z = x + ih`. -/
theorem im_inv_sub_add_im_inv_sub_conj (x h : ℝ) (a : ℂ)
    (h1 : 0 < (x - a.re) ^ 2 + (h - a.im) ^ 2) (h2 : 0 < (x - a.re) ^ 2 + (h + a.im) ^ 2) :
    (((x : ℂ) + h * I - a)⁻¹).im + (((x : ℂ) + h * I - (starRingEnd ℂ) a)⁻¹).im =
      -(2 * h * ((x - a.re) ^ 2 + h ^ 2 - a.im ^ 2)) /
        (((x - a.re) ^ 2 + (h - a.im) ^ 2) * ((x - a.re) ^ 2 + (h + a.im) ^ 2)) := by
  rw [Complex.inv_im, Complex.inv_im]
  have n1 : Complex.normSq ((x : ℂ) + h * I - a) = (x - a.re) ^ 2 + (h - a.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have n2 : Complex.normSq ((x : ℂ) + h * I - (starRingEnd ℂ) a) =
      (x - a.re) ^ 2 + (h + a.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have i1 : ((x : ℂ) + h * I - a).im = h - a.im := by simp
  have i2 : ((x : ℂ) + h * I - (starRingEnd ℂ) a).im = h + a.im := by simp
  rw [n1, n2, i1, i2]
  field_simp
  ring

/-- **Monotone phase off the defect traces.** -/
theorem im_logDeriv_neg_of_local {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {x h : ℝ} (hh : 0 < h) (hloc : ∀ w, f w = 0 → w.im ^ 2 < (x - w.re) ^ 2 + h ^ 2)
    (hne : Nonempty (ZeroCopy f)) :
    (logDeriv f ((x : ℂ) + h * I)).im < 0 := by
  set z : ℂ := (x : ℂ) + h * I with hz
  set a := zeroCopyPoint f with hadef
  have hzre : z.re = x := by simp [hz]
  have hzim : z.im = h := by simp [hz]
  have hfz : f z ≠ 0 := by
    intro h0
    have := hloc z h0
    rw [hzre, hzim, sub_self] at this
    nlinarith
  have hane : ∀ q, a q ≠ 0 := zeroCopyPoint_ne_zero hf hf0
  have hza : ∀ q, z ≠ a q := fun q h' => hfz (h' ▸ DeBruijn.apply_zeroCopyPoint hf q)
  set σ := DeBruijn.zeroCopyConj hf hconj with hσdef
  have hσa : ∀ q, a (σ q) = (starRingEnd ℂ) (a q) := DeBruijn.zeroCopyPoint_conj hf hconj
  set φ : ZeroCopy f → ℂ := fun q => -z / (a q * (a q - z)) with hφ
  have hsum : Summable φ := summable_neg_div_zeroCopyPoint hC hf hf0 hbound z
  have hlog : logDeriv f z = ∑' q, φ q := logDeriv_eq_tsum_of_even hC hf hf0 heven hbound hfz
  have hφeq : ∀ q, φ q = (z - a q)⁻¹ + (a q)⁻¹ := by
    intro q
    have h1 : a q - z ≠ 0 := sub_ne_zero.mpr (Ne.symm (hza q))
    have h2 : z - a q ≠ 0 := sub_ne_zero.mpr (hza q)
    simp only [hφ]
    field_simp [hane q]
    ring
  have hsumim : Summable (fun q => -(φ q).im) := (Complex.imCLM.summable hsum).neg
  have hpair : ∀ q, 0 < -(φ q).im + -(φ (σ q)).im := by
    intro q
    rw [hφeq, hφeq, hσa]
    have hconjinv : ((starRingEnd ℂ) (a q))⁻¹ = (starRingEnd ℂ) ((a q)⁻¹) := by
      rw [map_inv₀]
    rw [hconjinv, Complex.add_im, Complex.add_im, Complex.conj_im]
    have hl := hloc (a q) (DeBruijn.apply_zeroCopyPoint hf q)
    have hD1 : 0 < (x - (a q).re) ^ 2 + (h - (a q).im) ^ 2 := by
      by_contra hle
      have h1 : (x - (a q).re) ^ 2 = 0 := by nlinarith [sq_nonneg (x - (a q).re), sq_nonneg (h - (a q).im)]
      have h2 : (h - (a q).im) ^ 2 = 0 := by nlinarith [sq_nonneg (x - (a q).re), sq_nonneg (h - (a q).im)]
      apply hza q
      apply Complex.ext
      · rw [hzre]; nlinarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h1]
      · rw [hzim]; nlinarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h2]
    have hD2 : 0 < (x - (a q).re) ^ 2 + (h + (a q).im) ^ 2 := by
      have : (x - (a q).re) ^ 2 + (h - (a q).im) ^ 2 ≤
          (x - (a q).re) ^ 2 + (h + (a q).im) ^ 2 + 4 * h * |(a q).im| := by
        nlinarith [abs_nonneg (a q).im, sq_abs (a q).im, le_abs_self (a q).im,
          neg_abs_le (a q).im]
      by_contra hle
      have h0 : (x - (a q).re) ^ 2 + (h + (a q).im) ^ 2 = 0 :=
        le_antisymm (not_lt.mp hle) (by positivity)
      have hv : (a q).im = -h := by nlinarith [sq_nonneg (x - (a q).re), sq_nonneg (h + (a q).im)]
      rw [hv] at hl
      nlinarith [sq_nonneg (x - (a q).re)]
    have hid := im_inv_sub_add_im_inv_sub_conj x h (a q) hD1 hD2
    rw [← hz] at hid
    have hnum : 0 < 2 * h * ((x - (a q).re) ^ 2 + h ^ 2 - (a q).im ^ 2) := by
      have : 0 < (x - (a q).re) ^ 2 + h ^ 2 - (a q).im ^ 2 := by linarith
      positivity
    have hfrac : 0 < 2 * h * ((x - (a q).re) ^ 2 + h ^ 2 - (a q).im ^ 2) /
        (((x - (a q).re) ^ 2 + (h - (a q).im) ^ 2) * ((x - (a q).re) ^ 2 + (h + (a q).im) ^ 2)) :=
      div_pos hnum (mul_pos hD1 hD2)
    have : ((z - a q)⁻¹).im + ((z - (starRingEnd ℂ) (a q))⁻¹).im < 0 := by
      rw [hid, neg_div]; linarith
    linarith
  have hpos := DeBruijn.tsum_pos_of_involution hsumim σ hpair
  rw [hlog, Complex.im_tsum hsum]
  rw [tsum_neg] at hpos
  linarith

/-- **Simple real zeros off the defect traces.** -/
theorem deriv_cosineShift_ne_zero_of_local {C : ℝ} (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f univ)
    (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {x h : ℝ} (hh : 0 < h) (hloc : ∀ w, f w = 0 → w.im ^ 2 < (x - w.re) ^ 2 + h ^ 2)
    (hzero : (f ((x : ℂ) + h * I) + f ((x : ℂ) - h * I)) / 2 = 0) :
    deriv (fun z => (f (z + h * I) + f (z - h * I)) / 2) x ≠ 0 := by
  have hfd : Differentiable ℂ f := fun z => (hf z (mem_univ z)).differentiableAt
  set zp : ℂ := (x : ℂ) + h * I with hzp
  have hzm : (x : ℂ) - h * I = (starRingEnd ℂ) zp := by
    rw [hzp]; simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have hfzm : f ((x : ℂ) - h * I) = (starRingEnd ℂ) (f zp) := by rw [hzm, hconj]
  -- the derivative of `f` is real as well
  have hderiv_conj : deriv f ((starRingEnd ℂ) zp) = (starRingEnd ℂ) (deriv f zp) := by
    have h1 := (hfd zp).hasDerivAt.conj_conj
    have hfun : (⇑(starRingEnd ℂ) ∘ f ∘ ⇑(starRingEnd ℂ)) = f := by
      funext w; simp [Function.comp, hconj]
    rw [hfun] at h1
    exact h1.deriv
  have hA : HasDerivAt (fun z => (f (z + h * I) + f (z - h * I)) / 2)
      ((deriv f zp + deriv f ((x : ℂ) - h * I)) / 2) x := by
    have d1 := (hfd zp).hasDerivAt.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const (h * I))
    have d2 := (hfd ((x : ℂ) - h * I)).hasDerivAt.comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).sub_const (h * I))
    have := (d1.add d2).div_const 2
    simpa [Function.comp_def, hzp] using this
  rw [hA.deriv, hzm, hderiv_conj]
  -- `f(zp)` is purely imaginary and nonzero
  have hfz : f zp ≠ 0 := by
    intro h0
    have := hloc zp h0
    simp [hzp] at this
  rw [hfzm] at hzero
  have hre : (f zp).re = 0 := by
    have := congrArg Complex.re hzero
    simp [Complex.add_re, Complex.conj_re] at this
    linarith
  rcases isEmpty_or_nonempty (ZeroCopy f) with hempty | hne
  · -- no zeros: `f` is constant, so `A_h(x) = f 0 ≠ 0`
    have hford := DeBruijn.analyticOrderAt_ne_top_of_ne_zero hf hf0
    have hfac := OrderOneHadamard.eq_const_mul_hadamardProduct_of_even hC hf hf0 hford heven hbound
    have hconst : ∀ w, f w = f 0 := by
      intro w
      rw [hfac w]
      change f 0 * ∏' q : ZeroCopy f, weierstrassE1 (w / zeroCopyPoint f q) = f 0
      rw [tprod_empty, mul_one]
    exfalso
    have h1 := hconst zp
    have h2 : (f 0).re = 0 := by rw [← h1]; exact hre
    have h3 : (f 0).im = 0 := by
      have := hconj 0
      simp only [map_zero] at this
      have := congrArg Complex.im this
      simp at this
      linarith
    exact hf0 (Complex.ext h2 h3)
  · have hL := im_logDeriv_neg_of_local hC hf hf0 heven hconj hbound hh hloc hne
    rw [← hzp] at hL
    have hd : deriv f zp = logDeriv f zp * f zp := by
      rw [logDeriv_apply, div_mul_cancel₀ _ hfz]
    have hβ : (f zp).im ≠ 0 := by
      intro him
      exact hfz (Complex.ext hre him)
    intro h0
    have h1 := congrArg Complex.re h0
    rw [hd] at h1
    simp only [Complex.div_re, Complex.add_re, Complex.conj_re, Complex.mul_re, hre] at h1
    norm_num at h1
    rcases h1 with h1 | h1
    · have : (logDeriv f zp).im * (f zp).im = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h2 | h2
      · linarith
      · exact hβ h2
    · exact hβ h1

/-! ## The cosine producer of `Ξ` -/

/-- **Exceptional points are confined to defect traces.** If no zero `w` of `Ξ` satisfies
`(Im w)² ≥ (x − Re w)² + h²`, a real zero of `cos(hD)Ξ` at `x` is simple. -/
theorem deriv_cosineShiftXi_ne_zero_of_local {x h : ℝ} (hh : 0 < h)
    (hloc : ∀ w, XiC w = 0 → w.im ^ 2 < (x - w.re) ^ 2 + h ^ 2)
    (hzero : (XiC ((x : ℂ) + h * I) + XiC ((x : ℂ) - h * I)) / 2 = 0) :
    deriv (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) x ≠ 0 := by
  have hg := DeBruijn.riemannKernel_superExp
  obtain ⟨C, hC0, hC⟩ := hg.exists_envelope
  rw [DeBruijn.cosTransform_riemannKernel_eq_XiC] at hC
  have han : AnalyticOnNhd ℂ XiC univ := by
    rw [← DeBruijn.cosTransform_riemannKernel_eq_XiC]
    exact hg.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hX0 : XiC 0 ≠ 0 := by
    rw [← DeBruijn.cosTransform_riemannKernel_eq_XiC]; exact hg.cosTransform_zero_ne
  exact deriv_cosineShift_ne_zero_of_local hC0 han hX0 DeBruijn.XiC_neg' DeBruijn.XiC_conj' hC hh
    hloc hzero

/-- **Under RH the producer has no exceptional points.** -/
theorem deriv_cosineShiftXi_ne_zero_of_rh (hRH : RiemannHypothesis) {x h : ℝ} (hh : 0 < h)
    (hzero : (XiC ((x : ℂ) + h * I) + XiC ((x : ℂ) - h * I)) / 2 = 0) :
    deriv (fun z => (XiC (z + h * I) + XiC (z - h * I)) / 2) x ≠ 0 := by
  refine deriv_cosineShiftXi_ne_zero_of_local hh (fun w hw => ?_) hzero
  have hw0 : DeBruijn.riemannHeat 0 w = 0 := by
    rw [DeBruijn.riemannHeat_zero, mul_comm]; exact hw
  have him : w.im = 0 := DeBruijn.riemannHypothesis_iff_riemannHeat_zero_real.mp hRH w hw0
  rw [him]
  have : 0 < h ^ 2 := by positivity
  nlinarith [sq_nonneg (x - w.re)]

end

end RHTower
