import Mathlib.Analysis.Analytic.IsolatedZeros
import GaloisForLFunctions.RHTower.SlepianExteriorTransfer

/-!
# The entire sinc kernel and the full Slepian transfer on the band

The time–band kernel profile has a removable singularity at the origin.  Its entire extension
is obtained with no power-series bookkeeping as a difference slope: `sincSmooth c` is
`dslope (u ↦ sin(cu)/π) 0`, which equals `sin(cu)/(πu)` off the origin and `c/π` at it, and is
analytic on all of `ℝ` because `dslope` preserves analyticity (the isolated-zeros power-series
shift).  Consequently the smooth kernel `K̃_c(x,y) = sincSmooth c (x−y)` is `C^∞` in each
variable everywhere, satisfies the same off-diagonal Slepian commutation
`P_x K̃ = P_y K̃` as the raw kernel, and — this is the gain over the raw kernel — its slices are
globally twice continuously differentiable.

This closes the interior case left open by the exterior transfer: for **every** evaluation
point `x` (inside or outside the band),

`∫_{−1}^{1} K̃_c(x,y)·(P_c f)(y) dy = ∫_{−1}^{1} (P_c K̃_c(·,y))(x)·f(y) dy`

(`slepian_transfer`): band self-adjointness moves the prolate action onto the smooth slice,
and the off-diagonal commutation swaps it to the outer variable almost everywhere — the single
diagonal point is volume-null.  This is the integrated Slepian commutation on the whole band.
-/

open Filter MeasureTheory

namespace RHTower

/-- The entire sinc profile: `dslope` of `u ↦ sin(cu)/π` at the origin.  It equals
`sin(cu)/(πu)` off the origin and `c/π` at it. -/
noncomputable def sincSmooth (c : ℝ) : ℝ → ℝ :=
  dslope (fun u => Real.sin (c * u) / Real.pi) 0

theorem sincSmooth_eq_off {c u : ℝ} (h : u ≠ 0) : sincSmooth c u = sincScalar c u := by
  unfold sincSmooth sincScalar
  rw [dslope_of_ne _ h, slope_def_field]
  simp [mul_zero, Real.sin_zero, zero_div, sub_zero, div_div]

theorem analyticAt_sincSmooth (c u : ℝ) : AnalyticAt ℝ (sincSmooth c) u := by
  by_cases h : u = 0
  · subst h
    have hF : AnalyticAt ℝ (fun v : ℝ => Real.sin (c * v) / Real.pi) 0 := by
      have hlin : AnalyticAt ℝ (fun v : ℝ => c * v) 0 := analyticAt_const.mul analyticAt_id
      have hs : AnalyticAt ℝ (fun v : ℝ => Real.sin (c * v)) 0 :=
        Real.analyticAt_sin.comp hlin
      exact hs.div analyticAt_const Real.pi_ne_zero
    obtain ⟨p, hp⟩ := hF
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hloc : sincScalar c =ᶠ[nhds u] sincSmooth c := by
      filter_upwards [isOpen_compl_singleton.mem_nhds
        (by simpa using h : u ∈ ({0}ᶜ : Set ℝ))] with v hv
      exact (sincSmooth_eq_off (by simpa using hv)).symm
    have hnum : AnalyticAt ℝ (fun v : ℝ => Real.sin (c * v)) u :=
      Real.analyticAt_sin.comp (analyticAt_const.mul analyticAt_id)
    have hden : AnalyticAt ℝ (fun v : ℝ => Real.pi * v) u := analyticAt_const.mul analyticAt_id
    have hs : AnalyticAt ℝ (sincScalar c) u :=
      hnum.div hden (mul_ne_zero Real.pi_ne_zero h)
    exact hs.congr hloc

theorem contDiff_sincSmooth (c : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sincSmooth c) :=
  contDiff_iff_contDiffAt.mpr fun u => (analyticAt_sincSmooth c u).contDiffAt

theorem eventuallyEq_sincSmooth {c u : ℝ} (h : u ≠ 0) :
    sincSmooth c =ᶠ[nhds u] sincScalar c := by
  filter_upwards [isOpen_compl_singleton.mem_nhds
    (by simpa using h : u ∈ ({0}ᶜ : Set ℝ))] with v hv
  exact sincSmooth_eq_off (by simpa using hv)

theorem deriv_sincSmooth_off {c u : ℝ} (h : u ≠ 0) :
    deriv (sincSmooth c) u = deriv (sincScalar c) u :=
  (eventuallyEq_sincSmooth h).deriv_eq

theorem deriv2_sincSmooth_off {c u : ℝ} (h : u ≠ 0) :
    deriv (deriv (sincSmooth c)) u = deriv (deriv (sincScalar c)) u :=
  ((eventuallyEq_sincSmooth h).deriv).deriv_eq

/-- The radial (spherical Bessel) identity transfers to the entire sinc profile off the
origin. -/
theorem sincSmooth_bessel {c u : ℝ} (h : u ≠ 0) :
    u * deriv (deriv (sincSmooth c)) u + 2 * deriv (sincSmooth c) u
      + c ^ 2 * u * sincSmooth c u = 0 := by
  rw [deriv2_sincSmooth_off h, deriv_sincSmooth_off h, sincSmooth_eq_off h]
  exact sincScalar_bessel h

/-- The entire time–band kernel `K̃_c(x,y) = sincSmooth c (x−y)`. -/
noncomputable def sincKernelSmooth (c x y : ℝ) : ℝ := sincSmooth c (x - y)

theorem sincKernelSmooth_eq_off {c x y : ℝ} (h : x ≠ y) :
    sincKernelSmooth c x y = sincKernel c x y :=
  sincSmooth_eq_off (sub_ne_zero.mpr h)

/-- Off-diagonal Slepian commutation for the entire kernel: `P_x K̃ = P_y K̃`. -/
theorem prolateSLAction_sincKernelSmooth {c x y : ℝ} (h : x ≠ y) :
    prolateSLAction c (fun t => sincKernelSmooth c t y) x
      = prolateSLAction c (fun s => sincKernelSmooth c x s) y := by
  have hu : x - y ≠ 0 := sub_ne_zero.mpr h
  have hx1 : deriv (fun t => sincKernelSmooth c t y) x = deriv (sincSmooth c) (x - y) :=
    deriv_comp_sub_const (sincSmooth c) y x
  have hx2 : deriv (deriv (fun t => sincKernelSmooth c t y)) x
      = deriv (deriv (sincSmooth c)) (x - y) := by
    have hfun : deriv (fun t => sincKernelSmooth c t y)
        = fun t => deriv (sincSmooth c) (t - y) :=
      funext fun t => deriv_comp_sub_const (sincSmooth c) y t
    rw [hfun]
    exact deriv_comp_sub_const (deriv (sincSmooth c)) y x
  have hy1 : deriv (fun s => sincKernelSmooth c x s) y = -deriv (sincSmooth c) (x - y) :=
    deriv_comp_const_sub (sincSmooth c) x y
  have hy2 : deriv (deriv (fun s => sincKernelSmooth c x s)) y
      = deriv (deriv (sincSmooth c)) (x - y) := by
    have hfun : deriv (fun s => sincKernelSmooth c x s)
        = fun s => -deriv (sincSmooth c) (x - s) :=
      funext fun s => deriv_comp_const_sub (sincSmooth c) x s
    rw [hfun]
    have hneg : deriv (fun s : ℝ => -deriv (sincSmooth c) (x - s)) y
        = -deriv (fun s : ℝ => deriv (sincSmooth c) (x - s)) y := deriv.neg
    rw [hneg, deriv_comp_const_sub (deriv (sincSmooth c)) x y, neg_neg]
  have hb := sincSmooth_bessel (c := c) hu
  unfold prolateSLAction
  rw [hx1, hx2, hy1, hy2]
  simp only [sincKernelSmooth]
  linear_combination (-(x + y)) * hb

/-- **Full Slepian transfer on the band.**  For every evaluation point `x` — interior or
exterior — the prolate action moves through the time–band integral built on the entire
kernel: `∫ K̃(x,y)·(P_c f)(y) dy = ∫ (P_c K̃(·,y))(x)·f(y) dy`.  Band self-adjointness applies
to the globally smooth slice `K̃(x,·)`, and the off-diagonal commutation swaps the action to
the outer variable almost everywhere; the diagonal point is volume-null. -/
theorem slepian_transfer (c x : ℝ) {f : ℝ → ℝ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hf2c : Continuous (deriv (deriv f))) :
    ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * prolateSLAction c f y
      = ∫ y in (-1 : ℝ)..1, prolateSLAction c (fun t => sincKernelSmooth c t y) x * f y := by
  have haff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => x - s) :=
    contDiff_const.sub contDiff_id
  have hslice : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => sincKernelSmooth c x s) :=
    (contDiff_sincSmooth c).comp haff
  have h1 : Differentiable ℝ (fun s => sincKernelSmooth c x s) :=
    (contDiff_infty_iff_deriv.mp hslice).1
  have h2' := (contDiff_infty_iff_deriv.mp hslice).2
  have h2 : Differentiable ℝ (deriv (fun s => sincKernelSmooth c x s)) :=
    (contDiff_infty_iff_deriv.mp h2').1
  have h3 : Continuous (deriv (deriv (fun s => sincKernelSmooth c x s))) :=
    ((contDiff_infty_iff_deriv.mp h2').2).continuous
  have hsym := prolateSLAction_band_symmetric hf1 hf2 hf2c h1 h2 h3 c
  calc ∫ y in (-1 : ℝ)..1, sincKernelSmooth c x y * prolateSLAction c f y
      = ∫ y in (-1 : ℝ)..1, f y * prolateSLAction c (fun s => sincKernelSmooth c x s) y := hsym
    _ = ∫ y in (-1 : ℝ)..1, prolateSLAction c (fun t => sincKernelSmooth c t y) x * f y := by
        apply intervalIntegral.integral_congr_ae
        have hae : ∀ᵐ y : ℝ ∂volume, y ≠ x := by
          rw [MeasureTheory.ae_iff]
          have hset : {a : ℝ | ¬a ≠ x} = {x} := by ext a; simp
          rw [hset]
          exact Real.volume_singleton
        filter_upwards [hae] with y hy _
        rw [prolateSLAction_sincKernelSmooth (Ne.symm hy)]
        ring

end RHTower
