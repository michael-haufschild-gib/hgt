import GaloisForLFunctions.HTGeometry.AnalyticBallFinsetFactorization
import GaloisForLFunctions.HTGeometry.BoundaryCauchyKernel
import GaloisForLFunctions.RHTower.Reflection

/-!
# The real-boundary divisor limit of a Schwarz-real entire function

Let `F` be entire with `F(conj z) = conj (F z)`.  Its zero set is locally finite and stable under
conjugation, and near a zero `ρ` of multiplicity `m` one has `F'/F = m/(z - ρ) + (holomorphic)`.
Pairing the boundary density

```text
-(1/π) Im (F'/F)(t + iε)
```

against a test function supported in a real interval and letting `ε ↓ 0` therefore produces:

* from each **real** zero `γ`, the Poisson/Cauchy approximate identity `m_γ · δ_γ`;
* from each **nonreal conjugate pair** `ρ, conj ρ`, a kernel whose boundary value is real, hence
  no atom at all;
* from the zero-free remainder `g`, nothing: `g` is Schwarz-real, so `Im (g'/g)` vanishes on the
  real axis off the (finite) zero set.

The main theorem `tendsto_boundaryDensity_setIntegral` assembles these three facts into the local
distributional convergence of the boundary density to the *positive* atomic measure carried by the
real zeros, each weighted by its analytic multiplicity.  This is the general form of the canonical
positive real-boundary divisor measure; the completed-Xi specialisation is immediate from
`RHTower.XiC_conj`.

The three ingredients are:

* `boundaryDensity_decomp` — the pointwise splitting at an admissible height;
* `tendsto_integral_cauchyPDFReal_mul` and `tendsto_integral_conjPairKernel`
  (from `HTGeometry.BoundaryCauchyKernel`) — the atom and the pair cancellation;
* `tendsto_integral_logDeriv_remainder` — the zero-free remainder carries no mass.
-/

noncomputable section

open Complex Filter Topology Metric Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.RealBoundaryDivisor

/-! ## Schwarz reality of the logarithmic derivative -/

/-- The derivative of a Schwarz-real function is Schwarz-real.  No differentiability is needed:
`deriv` is junk-valued exactly where the reflection is too. -/
theorem deriv_schwarz {g : ℂ → ℂ}
    (hg : ∀ z : ℂ, g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (g z)) (z : ℂ) :
    deriv g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (deriv g z) := by
  have hcomp : (starRingEnd ℂ) ∘ g ∘ (starRingEnd ℂ) = g := by
    funext u
    simp only [Function.comp_apply, hg u, Complex.conj_conj]
  have h := deriv_conj_conj (f := g)
  rw [hcomp] at h
  have hw := congrFun h z
  simp only [Function.comp_apply] at hw
  rw [hw, Complex.conj_conj]

/-- **A Schwarz-real function has real logarithmic derivative on the real axis.** -/
theorem im_logDeriv_eq_zero_of_schwarz {g : ℂ → ℂ}
    (hg : ∀ z : ℂ, g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (g z)) (t : ℝ) :
    (logDeriv g (t : ℂ)).im = 0 := by
  have hreal : ∀ h : ℂ → ℂ, (∀ z : ℂ, h ((starRingEnd ℂ) z) = (starRingEnd ℂ) (h z)) →
      (starRingEnd ℂ) (h (t : ℂ)) = h (t : ℂ) := by
    intro h hh
    have hc : (starRingEnd ℂ) ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) := Complex.conj_ofReal t
    have := hh ((t : ℝ) : ℂ)
    rw [hc] at this
    exact this.symm
  have h1 : (starRingEnd ℂ) (g (t : ℂ)) = g (t : ℂ) := hreal g hg
  have h2 : (starRingEnd ℂ) (deriv g (t : ℂ)) = deriv g (t : ℂ) := hreal (deriv g) (deriv_schwarz hg)
  rw [logDeriv_apply]
  have hquot : (starRingEnd ℂ) (deriv g (t : ℂ) / g (t : ℂ)) = deriv g (t : ℂ) / g (t : ℂ) := by
    rw [map_div₀, h1, h2]
  exact Complex.conj_eq_iff_im.mp hquot

/-! ## The local splitting of the logarithmic derivative -/

/-- **The factorization splits the logarithmic derivative**, in the local (germ) form. -/
theorem logDeriv_split_eventually {F g : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hfac : ∀ᶠ w in 𝓝 z, F w = (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * g w)
    (hgdiff : DifferentiableAt ℂ g z) (hgz : g z ≠ 0) (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    logDeriv F z = (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) + logDeriv g z := by
  have hfe : F =ᶠ[𝓝 z] (fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * g w) := hfac
  have hlog : logDeriv F z = logDeriv (fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * g w) z := by
    rw [logDeriv_apply, logDeriv_apply, hfe.deriv_eq, hfe.self_of_nhds]
  have hPne : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ))
  have hPdiff : DifferentiableAt ℂ (fun w : ℂ => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z := by fun_prop
  rw [hlog, logDeriv_mul z hPne hgz hPdiff hgdiff, HTGeometry.logDeriv_finset_prod_pow hz]

/-- **The exponent in the factorization is the analytic order.** -/
theorem analyticOrderAt_eq_mult {F g : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {ρ : ℂ}
    (hρ : ρ ∈ Z) (hFan : AnalyticAt ℂ F ρ) (hgan : AnalyticAt ℂ g ρ) (hgne : g ρ ≠ 0)
    (hfac : ∀ᶠ w in 𝓝 ρ, F w = (∏ σ ∈ Z, (w - σ) ^ m σ) * g w) :
    analyticOrderAt F ρ = (m ρ : ℕ∞) := by
  classical
  rw [hFan.analyticOrderAt_eq_natCast]
  refine ⟨fun w => (∏ σ ∈ Z.erase ρ, (w - σ) ^ m σ) * g w, ?_, ?_, ?_⟩
  · exact (Finset.analyticAt_fun_prod _
      (fun σ _ => ((analyticAt_id.sub analyticAt_const).pow (m σ)))).mul hgan
  · refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun σ hσ => ?_) hgne
    have hne : ρ - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hσ))
    exact pow_ne_zero _ hne
  · filter_upwards [hfac] with w hw
    rw [hw, smul_eq_mul, ← mul_assoc,
      ← Finset.mul_prod_erase Z (fun σ => (w - σ) ^ m σ) hρ]



/-! ## The pointwise boundary decomposition -/

/-- The boundary density of `F` at height `ε`: `-(1/π)·Im (F'/F)(t + iε)`. -/
def boundaryDensity (F : ℂ → ℂ) (ε t : ℝ) : ℝ :=
  -(Real.pi)⁻¹ * (logDeriv F ((t : ℂ) + (ε : ℂ) * I)).im

/-- The conjugation involution as an equivalence of `ℂ`. -/
def conjEquiv : ℂ ≃ ℂ :=
  ⟨starRingEnd ℂ, starRingEnd ℂ, fun z => Complex.conj_conj z, fun z => Complex.conj_conj z⟩

theorem conjEquiv_apply (z : ℂ) : conjEquiv z = (starRingEnd ℂ) z := rfl

/-- **The boundary decomposition.**  At a height that avoids every zero, the boundary density
splits into the Cauchy atoms of the real zeros, the conjugate-pair kernels of the nonreal zeros,
and the zero-free remainder. -/
theorem boundaryDensity_decomp {F g : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {ε t : ℝ} (hε : 0 < ε)
    (hfac : ∀ᶠ w in 𝓝 ((t : ℂ) + (ε : ℂ) * I), F w = (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * g w)
    (hgdiff : DifferentiableAt ℂ g ((t : ℂ) + (ε : ℂ) * I))
    (hgz : g ((t : ℂ) + (ε : ℂ) * I) ≠ 0)
    (hz : ∀ ρ ∈ Z, ((t : ℂ) + (ε : ℂ) * I) ≠ ρ)
    (hconjZ : ∀ ρ ∈ Z, (starRingEnd ℂ) ρ ∈ Z)
    (hconjm : ∀ ρ ∈ Z, m ((starRingEnd ℂ) ρ) = m ρ) :
    boundaryDensity F ε t
      = (∑ ρ ∈ Z.filter (fun ρ => ρ.im = 0), (m ρ : ℝ) * cauchyPDFReal ρ.re (Real.toNNReal ε) t)
        + (-(2 * Real.pi)⁻¹)
            * (∑ ρ ∈ Z.filter (fun ρ => ρ.im ≠ 0), (m ρ : ℝ) * conjPairKernel ρ ε t)
        + (-(Real.pi)⁻¹) * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im := by
  classical
  set z : ℂ := (t : ℂ) + (ε : ℂ) * I with hzdef
  have hsplit := logDeriv_split_eventually hfac hgdiff hgz hz
  have hs : ((Real.toNNReal ε : NNReal) : ℝ) = ε := Real.coe_toNNReal ε hε.le
  -- the imaginary part of the pole sum
  have him : (logDeriv F z).im
      = (∑ ρ ∈ Z, ((m ρ : ℝ) * ((z - ρ)⁻¹).im)) + (logDeriv g z).im := by
    rw [hsplit, Complex.add_im, Complex.im_sum]
    congr 1
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [div_eq_mul_inv]
    simp [Complex.mul_im]
  -- split the pole sum into real and nonreal parts
  have hpart : (∑ ρ ∈ Z, ((m ρ : ℝ) * ((z - ρ)⁻¹).im))
      = (∑ ρ ∈ Z.filter (fun ρ => ρ.im = 0), (m ρ : ℝ) * ((z - ρ)⁻¹).im)
        + (∑ ρ ∈ Z.filter (fun ρ => ρ.im ≠ 0), (m ρ : ℝ) * ((z - ρ)⁻¹).im) := by
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun ρ => ρ.im = 0)]
  -- the nonreal part is half the conjugate-pair sum
  have hZc : ∀ ρ, ρ ∈ Z.filter (fun ρ => ρ.im ≠ 0) ↔
      (starRingEnd ℂ) ρ ∈ Z.filter (fun ρ => ρ.im ≠ 0) := by
    intro ρ
    constructor
    · intro h
      rw [Finset.mem_filter] at h ⊢
      exact ⟨hconjZ ρ h.1, by simpa using h.2⟩
    · intro h
      rw [Finset.mem_filter] at h ⊢
      have h1 := hconjZ _ h.1
      rw [Complex.conj_conj] at h1
      exact ⟨h1, by simpa using h.2⟩
  have hreidx : (∑ ρ ∈ Z.filter (fun ρ => ρ.im ≠ 0),
        (m ((starRingEnd ℂ) ρ) : ℝ) * ((z - (starRingEnd ℂ) ρ)⁻¹).im)
      = ∑ ρ ∈ Z.filter (fun ρ => ρ.im ≠ 0), (m ρ : ℝ) * ((z - ρ)⁻¹).im :=
    Finset.sum_equiv conjEquiv (fun i => hZc i) (fun _ _ => rfl)
  have hnonreal : (∑ ρ ∈ Z.filter (fun ρ => ρ.im ≠ 0), (m ρ : ℝ) * ((z - ρ)⁻¹).im)
      = (2 : ℝ)⁻¹ * ∑ ρ ∈ Z.filter (fun ρ => ρ.im ≠ 0), (m ρ : ℝ) * conjPairKernel ρ ε t := by
    have hpair : ∀ ρ ∈ Z.filter (fun ρ => ρ.im ≠ 0),
        (m ρ : ℝ) * conjPairKernel ρ ε t
          = (m ρ : ℝ) * ((z - ρ)⁻¹).im
            + (m ((starRingEnd ℂ) ρ) : ℝ) * ((z - (starRingEnd ℂ) ρ)⁻¹).im := by
      intro ρ hρ
      have hm := hconjm ρ (Finset.mem_filter.mp hρ).1
      rw [hm, conjPairKernel, Complex.add_im]
      ring
    rw [Finset.sum_congr rfl hpair, Finset.sum_add_distrib, hreidx]
    ring
  rw [boundaryDensity, ← hzdef, him, hpart, hnonreal]
  have hreal : (∑ ρ ∈ Z.filter (fun ρ => ρ.im = 0), (m ρ : ℝ) * ((z - ρ)⁻¹).im)
      = -Real.pi * ∑ ρ ∈ Z.filter (fun ρ => ρ.im = 0),
          (m ρ : ℝ) * cauchyPDFReal ρ.re (Real.toNNReal ε) t := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    have him0 : ρ.im = 0 := (Finset.mem_filter.mp hρ).2
    have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him0]
    have hshape : z - ρ = (t : ℂ) - ((ρ.re : ℝ) : ℂ) + (ε : ℂ) * I := by
      rw [hzdef, show ((ρ.re : ℝ) : ℂ) = ρ from hρre.symm]; ring
    have hk := neg_im_inv_eq_cauchyPDFReal hs hε ρ.re t
    rw [hshape]
    have : ((((t : ℂ) - ((ρ.re : ℝ) : ℂ) + (ε : ℂ) * I))⁻¹).im
        = -(Real.pi * cauchyPDFReal ρ.re (Real.toNNReal ε) t) := by
      linarith [hk]
    rw [this]
    ring
  rw [hreal]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring



/-! ## The zero-free remainder contributes nothing -/

/-- A horizontal segment at small height stays inside the ball. -/
theorem mem_ball_horizontal {c r R ε t : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (ht : t ∈ Icc (c - r) (c + r)) (hε0 : 0 ≤ ε) (hε1 : ε ≤ (R - r) / 2) :
    (t : ℂ) + (ε : ℂ) * I ∈ ball (c : ℂ) R := by
  rw [mem_ball, Complex.dist_eq]
  have hshape : (t : ℂ) + (ε : ℂ) * I - (c : ℂ) = ((t - c : ℝ) : ℂ) + ((ε : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hshape, Complex.norm_add_mul_I]
  have hRpos : (0 : ℝ) < R := lt_of_le_of_lt hr hrR
  rw [show R = Real.sqrt (R ^ 2) by rw [Real.sqrt_sq hRpos.le]]
  refine Real.sqrt_lt_sqrt (by positivity) ?_
  obtain ⟨h1, h2⟩ := ht
  have hbc : (t - c) ^ 2 ≤ r ^ 2 := by nlinarith
  have hbe : ε ^ 2 ≤ ((R - r) / 2) ^ 2 := by nlinarith
  nlinarith

/-- The set swept by the horizontal segments at heights in `[0, ε₁]`. -/
def sweep (c r ε₁ : ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) '' (Icc (c - r) (c + r) ×ˢ Icc 0 ε₁)

theorem isCompact_sweep (c r ε₁ : ℝ) : IsCompact (sweep c r ε₁) := by
  refine IsCompact.image (isCompact_Icc.prod isCompact_Icc) ?_
  fun_prop

theorem sweep_subset_ball {c r R ε₁ : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hε₁ : ε₁ ≤ (R - r) / 2) : sweep c r ε₁ ⊆ ball (c : ℂ) R := by
  rintro z ⟨⟨t, ε⟩, ⟨ht, hε⟩, rfl⟩
  exact mem_ball_horizontal hr hrR ht hε.1 (le_trans hε.2 hε₁)

/-- **The zero-free factor contributes no boundary mass.** -/
theorem tendsto_integral_logDeriv_remainder {g : ℂ → ℂ} {c r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hgan : AnalyticOnNhd ℂ g (ball (c : ℂ) R)) (hgne : ∀ z ∈ ball (c : ℂ) R, g z ≠ 0)
    (hgim : ∀ᵐ t ∂(volume.restrict (Icc (c - r) (c + r))), (logDeriv g ((t : ℝ) : ℂ)).im = 0)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Tendsto (fun ε : ℝ => ∫ t in Icc (c - r) (c + r),
        φ t * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im) (𝓝[>] 0) (𝓝 0) := by
  classical
  set K : Set ℝ := Icc (c - r) (c + r) with hK
  set ε₁ : ℝ := (R - r) / 2 with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; linarith
  set L : ℂ → ℂ := fun z => logDeriv g z with hLdef
  have hLcont : ContinuousOn L (ball (c : ℂ) R) := by
    have hd : ContinuousOn (fun z => deriv g z) (ball (c : ℂ) R) :=
      (hgan.deriv).continuousOn
    have hg : ContinuousOn g (ball (c : ℂ) R) := hgan.continuousOn
    exact hd.div hg hgne
  have hSsub : sweep c r ε₁ ⊆ ball (c : ℂ) R := sweep_subset_ball hr hrR le_rfl
  obtain ⟨C, hC⟩ := (isCompact_sweep c r ε₁).exists_bound_of_continuousOn
    (hLcont.mono hSsub)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := c - r) (b := c + r)).exists_bound_of_continuousOn
    hφ.continuousOn
  have hmemsweep : ∀ {ε t : ℝ}, t ∈ K → 0 ≤ ε → ε ≤ ε₁ →
      ((t : ℂ) + (ε : ℂ) * I) ∈ sweep c r ε₁ := by
    intro ε t ht hε0 hε1
    exact ⟨(t, ε), ⟨ht, ⟨hε0, hε1⟩⟩, rfl⟩
  -- the domination
  have hcontOn : ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε₁ →
      ContinuousOn (fun t : ℝ => φ t * (L ((t : ℂ) + (ε : ℂ) * I)).im) K := by
    intro ε hε0 hε1
    refine hφ.continuousOn.mul ?_
    refine Complex.continuous_im.comp_continuousOn ?_
    refine hLcont.comp ?_ ?_
    · fun_prop
    · intro t ht
      exact hSsub (hmemsweep ht hε0 hε1)
  have key : Tendsto (fun ε : ℝ => ∫ t in K, φ t * (L ((t : ℂ) + (ε : ℂ) * I)).im) (𝓝[>] 0)
      (𝓝 (∫ _t in K, (0 : ℝ))) := by
   refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => M * C) ?_ ?_ ?_ ?_
   · filter_upwards [Ioo_mem_nhdsGT hε₁pos] with ε hε
     exact ((hcontOn hε.1.le hε.2.le).aestronglyMeasurable measurableSet_Icc)
   · filter_upwards [Ioo_mem_nhdsGT hε₁pos] with ε hε
     filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
     have h1 : |φ t| ≤ M := hM t ht
     have h2 : ‖L ((t : ℂ) + (ε : ℂ) * I)‖ ≤ C := hC _ (hmemsweep ht hε.1.le hε.2.le)
     have h3 : |(L ((t : ℂ) + (ε : ℂ) * I)).im| ≤ C :=
       le_trans (Complex.abs_im_le_norm _) h2
     have : ‖φ t * (L ((t : ℂ) + (ε : ℂ) * I)).im‖ = |φ t| * |(L ((t : ℂ) + (ε : ℂ) * I)).im| := by
       rw [Real.norm_eq_abs, abs_mul]
     rw [this]
     have hMnn : 0 ≤ M := le_trans (abs_nonneg _) h1
     have hCnn : 0 ≤ C := le_trans (abs_nonneg _) h3
     exact mul_le_mul h1 h3 (abs_nonneg _) hMnn
   · exact integrableOn_const (by rw [hK]; exact measure_Icc_lt_top.ne)
   · filter_upwards [hgim, ae_restrict_mem measurableSet_Icc] with t htim ht
     have hball : ((t : ℝ) : ℂ) ∈ ball (c : ℂ) R := by
       have := hmemsweep (ε := 0) ht le_rfl hε₁pos.le
       simpa using hSsub this
     have hLat : ContinuousAt L ((t : ℝ) : ℂ) :=
       hLcont.continuousAt (isOpen_ball.mem_nhds hball)
     have hpath : Tendsto (fun ε : ℝ => (t : ℂ) + (ε : ℂ) * I) (𝓝[>] 0) (𝓝 ((t : ℝ) : ℂ)) := by
       have hcont : Continuous (fun ε : ℝ => (t : ℂ) + (ε : ℂ) * I) := by fun_prop
       have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (a := (0 : ℝ)))
       simpa using this
     have hlim := (hLat.tendsto.comp hpath)
     have hlim2 : Tendsto (fun ε : ℝ => φ t * (L ((t : ℂ) + (ε : ℂ) * I)).im) (𝓝[>] 0)
         (𝓝 (φ t * (L ((t : ℝ) : ℂ)).im)) :=
       (tendsto_const_nhds.mul ((Complex.continuous_im.tendsto _).comp hlim))
     have hzero : φ t * (L ((t : ℝ) : ℂ)).im = 0 := by
       rw [hLdef]
       simp only
       rw [htim, mul_zero]
     rw [hzero] at hlim2
     exact hlim2
  simpa using key




/-! ## Auxiliary continuity and reindexing -/

theorem continuous_cauchyPDFReal {γ : ℝ} {s : NNReal} (hs : s ≠ 0) :
    Continuous (cauchyPDFReal γ s) := by
  have hspos : (0 : ℝ) < (s : ℝ) := by
    rcases (NNReal.coe_pos (r := s)).mpr (pos_iff_ne_zero.mpr hs) with h
    exact h
  have hden : ∀ x : ℝ, ((x - γ) ^ 2 + (s : ℝ) ^ 2) ≠ 0 := by
    intro x
    positivity
  have heq : cauchyPDFReal γ s
      = fun x : ℝ => Real.pi⁻¹ * (s : ℝ) * ((x - γ) ^ 2 + (s : ℝ) ^ 2)⁻¹ := by
    funext x
    rw [cauchyPDFReal_def]
  rw [heq]
  exact continuous_const.mul (Continuous.inv₀ (by fun_prop) hden)

/-- A conjugation-stable zero polynomial is Schwarz-real. -/
theorem zeroPoly_conj {Z : Finset ℂ} {m : ℂ → ℕ}
    (hconjZ : ∀ ρ, ρ ∈ Z ↔ (starRingEnd ℂ) ρ ∈ Z)
    (hconjm : ∀ ρ ∈ Z, m ((starRingEnd ℂ) ρ) = m ρ) (w : ℂ) :
    (∏ ρ ∈ Z, ((starRingEnd ℂ) w - ρ) ^ m ρ)
      = (starRingEnd ℂ) (∏ ρ ∈ Z, (w - ρ) ^ m ρ) := by
  rw [map_prod]
  refine (Finset.prod_equiv conjEquiv (fun i => hconjZ i) ?_).symm
  intro ρ hρ
  rw [conjEquiv_apply, map_pow, map_sub, hconjm ρ hρ]



/-- The boundary remainder integrand is continuous on the base interval. -/
theorem continuousOn_logDeriv_im {g : ℂ → ℂ} {c r R ε : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hgan : AnalyticOnNhd ℂ g (ball (c : ℂ) R)) (hgne : ∀ z ∈ ball (c : ℂ) R, g z ≠ 0)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ (R - r) / 2) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ContinuousOn (fun t : ℝ => φ t * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im)
      (Icc (c - r) (c + r)) := by
  have hLcont : ContinuousOn (fun z => logDeriv g z) (ball (c : ℂ) R) :=
    (hgan.deriv).continuousOn.div hgan.continuousOn hgne
  refine hφ.continuousOn.mul ?_
  refine Complex.continuous_im.comp_continuousOn ?_
  refine hLcont.comp (by fun_prop) ?_
  intro t ht
  exact mem_ball_horizontal hr hrR ht hε0 hε1

/-! ## The general real-boundary divisor limit -/

set_option maxHeartbeats 2000000 in
/-- **The general boundary identity.**  For a Schwarz-real entire function `F`, the boundary
density `-(1/π)·Im (F'/F)(t + iε)` converges, as `ε ↓ 0`, weakly against every test function
supported in `(c - r, c + r)` to the positive atomic measure carried by the *real* zeros of `F`,
each weighted by its analytic multiplicity.  Nonreal conjugate zero pairs contribute nothing. -/
theorem tendsto_boundaryDensity_setIntegral
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hFconj : ∀ z : ℂ, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z))
    {c r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (c : ℂ) R) (hFz₀ : F z₀ ≠ 0)
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ t : ℝ, t ∉ Ioo (c - r) (c + r) → φ t = 0) :
    ∃ Γ : Finset ℝ,
      (∀ γ : ℝ, γ ∈ Γ ↔ ((γ : ℂ) ∈ ball (c : ℂ) R ∧ F (γ : ℂ) = 0)) ∧
      Tendsto (fun ε : ℝ => ∫ t in Icc (c - r) (c + r), φ t * boundaryDensity F ε t)
        (𝓝[>] 0) (𝓝 (∑ γ ∈ Γ, ((analyticOrderAt F (γ : ℂ)).toNat : ℝ) * φ γ)) := by
  classical
  set K : Set ℝ := Icc (c - r) (c + r) with hKdef
  have hRpos : (0 : ℝ) < R := lt_of_le_of_lt hr hrR
  have hFa : ∀ z : ℂ, AnalyticAt ℂ F z := fun z =>
    (hF.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hFan : AnalyticOnNhd ℂ F (closedBall (c : ℂ) R) := fun z _ => hFa z
  obtain ⟨Z, m, g, hZball, hm1, hZzero, hgan, hgne, hEq⟩ :=
    HTGeometry.exists_finset_zeroFree_factorization hFan hz₀ hFz₀
  -- conjugation stability of the ball and of the zero set
  have hballconj : ∀ z : ℂ, z ∈ ball (c : ℂ) R → (starRingEnd ℂ) z ∈ ball (c : ℂ) R := by
    intro z hz
    rw [mem_ball, Complex.dist_eq] at hz ⊢
    have hrw : (starRingEnd ℂ) z - (c : ℂ) = (starRingEnd ℂ) (z - (c : ℂ)) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [hrw, RCLike.norm_conj]
    exact hz
  have hconjZ : ∀ ρ, ρ ∈ Z ↔ (starRingEnd ℂ) ρ ∈ Z := by
    intro ρ
    constructor
    · intro h
      have hb := hZball ρ h
      have hz : F ρ = 0 := (hZzero ρ hb).mpr h
      have hz2 : F ((starRingEnd ℂ) ρ) = 0 := by rw [hFconj, hz, map_zero]
      exact (hZzero _ (hballconj ρ hb)).mp hz2
    · intro h
      have hb := hZball _ h
      have hz : F ((starRingEnd ℂ) ρ) = 0 := (hZzero _ hb).mpr h
      have hb' : ρ ∈ ball (c : ℂ) R := by
        have hx := hballconj _ hb
        rwa [Complex.conj_conj] at hx
      have hz2 : F ρ = 0 := by
        have h2 : (starRingEnd ℂ) (F ρ) = 0 := by rw [← hFconj ρ, hz]
        simpa using h2
      exact (hZzero ρ hb').mp hz2
  have hfacEv : ∀ w ∈ ball (c : ℂ) R,
      ∀ᶠ u in 𝓝 w, F u = (∏ ρ ∈ Z, (u - ρ) ^ m ρ) * g u := by
    intro w hw
    exact Filter.eventually_iff_exists_mem.mpr
      ⟨ball (c : ℂ) R, isOpen_ball.mem_nhds hw, fun u hu => hEq hu⟩
  have hmord : ∀ ρ ∈ Z, analyticOrderAt F ρ = (m ρ : ℕ∞) := by
    intro ρ hρ
    have hb := hZball ρ hρ
    exact analyticOrderAt_eq_mult hρ (hFa ρ) (hgan ρ hb) (hgne ρ hb) (hfacEv ρ hb)
  have hconjm : ∀ ρ ∈ Z, m ((starRingEnd ℂ) ρ) = m ρ := by
    intro ρ hρ
    have h1 := hmord _ ((hconjZ ρ).mp hρ)
    have h2 := hmord ρ hρ
    have h3 : analyticOrderAt F ((starRingEnd ℂ) ρ) = analyticOrderAt F ρ :=
      RHTower.analyticOrderAt_conj_of_conjEquivariant hFconj (hFa ρ) (hFa _)
    rw [h1, h2] at h3
    exact_mod_cast h3
  set Zr : Finset ℂ := Z.filter (fun ρ => ρ.im = 0) with hZrdef
  set Zc : Finset ℂ := Z.filter (fun ρ => ρ.im ≠ 0) with hZcdef
  set Γ : Finset ℝ := Zr.image Complex.re with hΓdef
  have hΓZ : ∀ γ : ℝ, γ ∈ Γ ↔ ((γ : ℂ) ∈ Z) := by
    intro γ
    rw [hΓdef, Finset.mem_image]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      rw [hZrdef, Finset.mem_filter] at hρ
      have : ((ρ.re : ℝ) : ℂ) = ρ := by
        apply Complex.ext <;> simp [hρ.2]
      rw [this]
      exact hρ.1
    · intro h
      exact ⟨(γ : ℂ), by rw [hZrdef, Finset.mem_filter]; exact ⟨h, by simp⟩, by simp⟩
  have hΓchar : ∀ γ : ℝ, γ ∈ Γ ↔ ((γ : ℂ) ∈ ball (c : ℂ) R ∧ F (γ : ℂ) = 0) := by
    intro γ
    rw [hΓZ γ]
    constructor
    · intro h
      exact ⟨hZball _ h, (hZzero _ (hZball _ h)).mpr h⟩
    · rintro ⟨h1, h2⟩
      exact (hZzero _ h1).mp h2
  have hsumΓ : (∑ γ ∈ Γ, ((analyticOrderAt F (γ : ℂ)).toNat : ℝ) * φ γ)
      = ∑ ρ ∈ Zr, (m ρ : ℝ) * φ ρ.re := by
    rw [hΓdef, Finset.sum_image ?inj]
    · refine Finset.sum_congr rfl (fun ρ hρ => ?_)
      rw [hZrdef, Finset.mem_filter] at hρ
      have hre : ((ρ.re : ℝ) : ℂ) = ρ := by apply Complex.ext <;> simp [hρ.2]
      rw [hre, hmord ρ hρ.1]
      simp
    case inj =>
      intro x hx y hy hxy
      have hx' : x.im = 0 := by
        have := Finset.mem_coe.mp hx
        rw [hZrdef, Finset.mem_filter] at this
        exact this.2
      have hy' : y.im = 0 := by
        have := Finset.mem_coe.mp hy
        rw [hZrdef, Finset.mem_filter] at this
        exact this.2
      apply Complex.ext
      · exact hxy
      · rw [hx', hy']

  -- the zero-free factor is Schwarz-real away from the zeros
  have hPconj : ∀ w : ℂ, (∏ ρ ∈ Z, ((starRingEnd ℂ) w - ρ) ^ m ρ)
      = (starRingEnd ℂ) (∏ ρ ∈ Z, (w - ρ) ^ m ρ) := zeroPoly_conj hconjZ hconjm
  have hquotconj : ∀ z : ℂ,
      (fun u : ℂ => F u / (∏ ρ ∈ Z, (u - ρ) ^ m ρ)) ((starRingEnd ℂ) z)
        = (starRingEnd ℂ) ((fun u : ℂ => F u / (∏ ρ ∈ Z, (u - ρ) ^ m ρ)) z) := by
    intro z
    simp only
    rw [hFconj z, hPconj z, ← map_div₀]
  have hgae : ∀ᵐ t ∂(volume.restrict K), (logDeriv g ((t : ℝ) : ℂ)).im = 0 := by
    have hbad : ∀ᵐ t : ℝ, ((t : ℝ) : ℂ) ∉ Z := by
      have hfin : (Complex.re '' (Z : Set ℂ)).Finite := Z.finite_toSet.image _
      have h0 : (volume : Measure ℝ) (Complex.re '' (Z : Set ℂ)) = 0 := hfin.measure_zero volume
      have hae : ∀ᵐ t : ℝ, t ∉ Complex.re '' (Z : Set ℂ) := by
        rw [MeasureTheory.ae_iff]
        have hset : {a : ℝ | ¬ a ∉ Complex.re '' (Z : Set ℂ)} = Complex.re '' (Z : Set ℂ) := by
          ext a
          simp only [not_not, Set.mem_setOf_eq]
        rw [hset]
        exact h0
      filter_upwards [hae] with t ht hcon
      exact ht ⟨((t : ℝ) : ℂ), Finset.mem_coe.mpr hcon, by simp⟩
    filter_upwards [MeasureTheory.ae_restrict_of_ae hbad, ae_restrict_mem measurableSet_Icc]
      with t htnotZ ht
    have hball : ((t : ℝ) : ℂ) ∈ ball (c : ℂ) R := by
      have hx := mem_ball_horizontal (ε := 0) hr hrR ht le_rfl (by linarith)
      simpa using hx
    have hUopen : IsOpen (ball (c : ℂ) R \ (Z : Set ℂ)) :=
      isOpen_ball.sdiff (Z.finite_toSet.isClosed)
    have hgquot : g =ᶠ[𝓝 ((t : ℝ) : ℂ)] (fun u : ℂ => F u / (∏ ρ ∈ Z, (u - ρ) ^ m ρ)) := by
      refine Filter.eventually_iff_exists_mem.mpr
        ⟨_, hUopen.mem_nhds ⟨hball, htnotZ⟩, fun u hu => ?_⟩
      have hP : (∏ ρ ∈ Z, (u - ρ) ^ m ρ) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr ?_))
        intro hcon
        rw [hcon] at hu
        exact hu.2 (Finset.mem_coe.mpr hρ)
      show g u = F u / (∏ ρ ∈ Z, (u - ρ) ^ m ρ)
      rw [hEq hu.1]
      field_simp
    have hlogeq : logDeriv g ((t : ℝ) : ℂ)
        = logDeriv (fun u : ℂ => F u / (∏ ρ ∈ Z, (u - ρ) ^ m ρ)) ((t : ℝ) : ℂ) := by
      rw [logDeriv_apply, logDeriv_apply, hgquot.deriv_eq, hgquot.self_of_nhds]
    rw [hlogeq]
    exact im_logDeriv_eq_zero_of_schwarz hquotconj t
  -- admissible heights
  set ε₁ : ℝ := (R - r) / 2 with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; linarith
  set Bad : Set ℝ :=
    (((Z.image Complex.im : Finset ℝ) : Set ℝ)
      ∪ ((Z.image (fun ρ => -ρ.im) : Finset ℝ) : Set ℝ)) \ {0} with hBaddef
  have hBadfin : Bad.Finite :=
    (((Z.image Complex.im).finite_toSet.union
      (Z.image (fun ρ => -ρ.im)).finite_toSet)).sdiff
  have h0Bad : (0 : ℝ) ∉ Bad := by
    rw [hBaddef]
    intro h
    exact h.2 rfl
  have hgood : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ ε₁ ∧ ε ∉ Bad := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∉ Bad :=
      (Filter.eventually_of_mem (hBadfin.isClosed.isOpen_compl.mem_nhds h0Bad)
        (fun x hx => hx)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hε₁pos, h1] with ε h2 h3 h4
    exact ⟨h2, h3.2.le, h4⟩
  have hεZ : ∀ ε : ℝ, 0 < ε → ε ∉ Bad →
      (∀ ρ ∈ Z, ε ≠ ρ.im) ∧ (∀ ρ ∈ Z, ε ≠ -ρ.im) := by
    intro ε hε hεB
    rw [hBaddef] at hεB
    constructor
    · intro ρ hρ hcon
      refine hεB ⟨Or.inl ?_, fun hz => hε.ne' hz⟩
      refine Finset.mem_coe.mpr ?_
      rw [hcon]
      exact Finset.mem_image_of_mem _ hρ
    · intro ρ hρ hcon
      refine hεB ⟨Or.inr ?_, fun hz => hε.ne' hz⟩
      refine Finset.mem_coe.mpr ?_
      rw [hcon]
      exact Finset.mem_image_of_mem _ hρ
  -- the integral identity at an admissible height
  have hIdent : ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ε ∉ Bad →
      ∫ t in K, φ t * boundaryDensity F ε t
        = (∑ ρ ∈ Zr, (m ρ : ℝ) * ∫ t, cauchyPDFReal ρ.re (Real.toNNReal ε) t * φ t)
          + (-(2 * Real.pi)⁻¹) * (∑ ρ ∈ Zc, (m ρ : ℝ) * ∫ t, φ t * conjPairKernel ρ ε t)
          + (-(Real.pi)⁻¹) * ∫ t in K, φ t * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im := by
    intro ε hε hε1 hεB
    obtain ⟨hne1, hne2⟩ := hεZ ε hε hεB
    have hs : ((Real.toNNReal ε : NNReal) : ℝ) = ε := Real.coe_toNNReal ε hε.le
    have hsne : Real.toNNReal ε ≠ 0 := by
      intro hcon
      rw [hcon] at hs
      exact hε.ne' (by simpa using hs.symm)
    have hpt : Set.EqOn (fun t => φ t * boundaryDensity F ε t)
        (fun t => (∑ ρ ∈ Zr, φ t * ((m ρ : ℝ) * cauchyPDFReal ρ.re (Real.toNNReal ε) t))
          + (-(2 * Real.pi)⁻¹) * (∑ ρ ∈ Zc, φ t * ((m ρ : ℝ) * conjPairKernel ρ ε t))
          + (-(Real.pi)⁻¹) * (φ t * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im)) K := by
      intro t ht
      have hmem : (t : ℂ) + (ε : ℂ) * I ∈ ball (c : ℂ) R :=
        mem_ball_horizontal hr hrR ht hε.le hε1
      have hzne : ∀ ρ ∈ Z, ((t : ℂ) + (ε : ℂ) * I) ≠ ρ := by
        intro ρ hρ hcon
        have him : ((t : ℂ) + (ε : ℂ) * I).im = ρ.im := by rw [hcon]
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero] at him
        exact hne1 ρ hρ him
      simp only
      rw [boundaryDensity_decomp hε (hfacEv _ hmem) ((hgan _ hmem).differentiableAt)
        (hgne _ hmem) hzne (fun ρ hρ => (hconjZ ρ).mp hρ) hconjm]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    have hIcc : IsCompact K := isCompact_Icc
    have hint1 : ∀ ρ ∈ Zr, IntegrableOn
        (fun t => φ t * ((m ρ : ℝ) * cauchyPDFReal ρ.re (Real.toNNReal ε) t)) K :=
      fun ρ _ => (hφ.mul (continuous_const.mul
        (continuous_cauchyPDFReal hsne))).continuousOn.integrableOn_compact hIcc
    have hint2 : ∀ ρ ∈ Zc, IntegrableOn
        (fun t => φ t * ((m ρ : ℝ) * conjPairKernel ρ ε t)) K := by
      intro ρ hρ
      rw [hZcdef, Finset.mem_filter] at hρ
      have h1 : ε - ρ.im ≠ 0 := sub_ne_zero.mpr (hne1 ρ hρ.1)
      have h2 : ε + ρ.im ≠ 0 := by
        intro hcon
        exact hne2 ρ hρ.1 (by linarith)
      exact (hφ.mul (continuous_const.mul
        (continuous_conjPairKernel_of_ne h1 h2))).continuousOn.integrableOn_compact hIcc
    have hint3 : IntegrableOn
        (fun t => φ t * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im) K :=
      (continuousOn_logDeriv_im hr hrR hgan hgne hε.le hε1 hφ).integrableOn_compact hIcc
    have hintS1 : IntegrableOn
        (fun t => ∑ ρ ∈ Zr, φ t * ((m ρ : ℝ) * cauchyPDFReal ρ.re (Real.toNNReal ε) t)) K :=
      integrable_finsetSum _ hint1
    have hintS2 : IntegrableOn
        (fun t => (-(2 * Real.pi)⁻¹)
          * (∑ ρ ∈ Zc, φ t * ((m ρ : ℝ) * conjPairKernel ρ ε t))) K :=
      (integrable_finsetSum _ hint2).const_mul _
    have hintS3 : IntegrableOn
        (fun t => (-(Real.pi)⁻¹) * (φ t * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im)) K :=
      hint3.const_mul _
    have hintS12 : IntegrableOn
        (fun t => (∑ ρ ∈ Zr, φ t * ((m ρ : ℝ) * cauchyPDFReal ρ.re (Real.toNNReal ε) t))
          + (-(2 * Real.pi)⁻¹)
            * (∑ ρ ∈ Zc, φ t * ((m ρ : ℝ) * conjPairKernel ρ ε t))) K := hintS1.add hintS2
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt,
      MeasureTheory.integral_add hintS12 hintS3,
      MeasureTheory.integral_add hintS1 hintS2,
      MeasureTheory.integral_finsetSum _ hint1,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ hint2,
      MeasureTheory.integral_const_mul]
    congr 1
    congr 1
    · refine Finset.sum_congr rfl (fun ρ _ => ?_)
      have hzero : ∀ t : ℝ, t ∉ K →
          φ t * ((m ρ : ℝ) * cauchyPDFReal ρ.re (Real.toNNReal ε) t) = 0 := by
        intro t ht
        rw [hsupp t (fun hcon => ht (Ioo_subset_Icc_self hcon)), zero_mul]
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
        ← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
    · congr 1
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      have hzero : ∀ t : ℝ, t ∉ K → φ t * ((m ρ : ℝ) * conjPairKernel ρ ε t) = 0 := by
        intro t ht
        rw [hsupp t (fun hcon => ht (Ioo_subset_Icc_self hcon)), zero_mul]
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
        ← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun t => by ring))
  -- the three limits
  have hφint : Integrable φ := by
    have hcs : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc
      (fun t ht => hsupp t (fun hcon => ht (Ioo_subset_Icc_self hcon)))
    exact hφ.integrable_of_hasCompactSupport hcs
  have hlim1 : ∀ ρ ∈ Zr,
      Tendsto (fun ε : ℝ => ∫ t, cauchyPDFReal ρ.re (Real.toNNReal ε) t * φ t)
        (𝓝[>] 0) (𝓝 (φ ρ.re)) := by
    intro ρ _
    have h := tendsto_integral_cauchyPDFReal_mul hφint (γ := ρ.re) hφ.continuousAt
    have h2 := h.comp tendsto_inv_nhdsGT_zero
    refine h2.congr (fun ε => ?_)
    simp
  have hlim2 : ∀ ρ ∈ Zc,
      Tendsto (fun ε : ℝ => ∫ t, φ t * conjPairKernel ρ ε t) (𝓝[>] 0) (𝓝 0) := by
    intro ρ hρ
    rw [hZcdef, Finset.mem_filter] at hρ
    exact (tendsto_integral_conjPairKernel hρ.2 hφint).mono_left nhdsWithin_le_nhds
  have hlim3 : Tendsto (fun ε : ℝ =>
      ∫ t in K, φ t * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im) (𝓝[>] 0) (𝓝 0) :=
    tendsto_integral_logDeriv_remainder hr hrR hgan hgne hgae hφ
  refine ⟨Γ, hΓchar, ?_⟩
  rw [hsumΓ]
  have hmain : Tendsto (fun ε : ℝ =>
      (∑ ρ ∈ Zr, (m ρ : ℝ) * ∫ t, cauchyPDFReal ρ.re (Real.toNNReal ε) t * φ t)
        + (-(2 * Real.pi)⁻¹) * (∑ ρ ∈ Zc, (m ρ : ℝ) * ∫ t, φ t * conjPairKernel ρ ε t)
        + (-(Real.pi)⁻¹) * ∫ t in K, φ t * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im)
      (𝓝[>] 0) (𝓝 ((∑ ρ ∈ Zr, (m ρ : ℝ) * φ ρ.re) + (-(2 * Real.pi)⁻¹) * 0
        + (-(Real.pi)⁻¹) * 0)) := by
    refine Filter.Tendsto.add (Filter.Tendsto.add ?_ ?_) ?_
    · exact tendsto_finsetSum _ (fun ρ hρ => tendsto_const_nhds.mul (hlim1 ρ hρ))
    · have hz : Tendsto (fun ε : ℝ => ∑ ρ ∈ Zc, (m ρ : ℝ) * ∫ t, φ t * conjPairKernel ρ ε t)
          (𝓝[>] 0) (𝓝 (∑ ρ ∈ Zc, (m ρ : ℝ) * 0)) :=
        tendsto_finsetSum _ (fun ρ hρ => tendsto_const_nhds.mul (hlim2 ρ hρ))
      simp only [mul_zero, Finset.sum_const_zero] at hz
      exact tendsto_const_nhds.mul hz
    · exact tendsto_const_nhds.mul hlim3
  have hev : (fun ε : ℝ =>
      (∑ ρ ∈ Zr, (m ρ : ℝ) * ∫ t, cauchyPDFReal ρ.re (Real.toNNReal ε) t * φ t)
        + (-(2 * Real.pi)⁻¹) * (∑ ρ ∈ Zc, (m ρ : ℝ) * ∫ t, φ t * conjPairKernel ρ ε t)
        + (-(Real.pi)⁻¹) * ∫ t in K, φ t * (logDeriv g ((t : ℂ) + (ε : ℂ) * I)).im)
      =ᶠ[𝓝[>] 0] (fun ε : ℝ => ∫ t in K, φ t * boundaryDensity F ε t) := by
    filter_upwards [hgood] with ε hε
    exact (hIdent ε hε.1 hε.2.1 hε.2.2).symm
  have hfin := hmain.congr' hev
  simpa using hfin

end RHTower.RealBoundaryDivisor

namespace RHTower.RealBoundaryDivisor

/-! ## The exact limitation: nonreal pairs are invisible -/

/-- **The boundary measure is blind to nonreal zeros.**  If `F` has no real zero at all, the whole
boundary limit vanishes, however many nonreal zeros `F` carries. -/
theorem tendsto_boundaryDensity_setIntegral_zero_of_no_real_zero
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hFconj : ∀ z : ℂ, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z))
    {c r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball (c : ℂ) R) (hFz₀ : F z₀ ≠ 0)
    {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ t : ℝ, t ∉ Ioo (c - r) (c + r) → φ t = 0)
    (hnoreal : ∀ γ : ℝ, F (γ : ℂ) ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ t in Icc (c - r) (c + r), φ t * boundaryDensity F ε t)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Γ, hΓ, hlim⟩ :=
    tendsto_boundaryDensity_setIntegral hF hFconj hr hrR hz₀ hFz₀ hφ hsupp
  have hempty : Γ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun γ hγ => ?_)
    exact hnoreal γ ((hΓ γ).mp hγ).2
  rw [hempty] at hlim
  simpa using hlim

/-- `z ↦ z² + 1` has no real zero. -/
theorem sqAddOne_ofReal_ne_zero (γ : ℝ) : ((γ : ℂ) ^ 2 + 1) ≠ 0 := by
  intro h
  have hc : (((γ ^ 2 + 1 : ℝ)) : ℂ) = 0 := by push_cast; exact h
  have h2 : (γ ^ 2 + 1 : ℝ) = 0 := by exact_mod_cast hc
  nlinarith [sq_nonneg γ]

/-- **The exact limitation.**  A Schwarz-real entire function can carry a full conjugate pair of
zeros and still have an identically vanishing real-boundary divisor measure: the boundary
construction sees only the *real* part of the analytic divisor.  Hence the assertion that the
analytic divisor is exhausted by the boundary measure is a genuinely stronger statement, not a
formal consequence of the construction. -/
theorem exists_nonreal_pair_with_vanishing_boundary_measure :
    ∃ F : ℂ → ℂ, Differentiable ℂ F
      ∧ (∀ z : ℂ, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z))
      ∧ F I = 0 ∧ F (-I) = 0
      ∧ (∀ γ : ℝ, F (γ : ℂ) ≠ 0)
      ∧ ∀ (c r R : ℝ), 0 ≤ r → r < R → ∀ φ : ℝ → ℝ, Continuous φ →
          (∀ t : ℝ, t ∉ Ioo (c - r) (c + r) → φ t = 0) →
          Tendsto (fun ε : ℝ => ∫ t in Icc (c - r) (c + r), φ t * boundaryDensity F ε t)
            (𝓝[>] 0) (𝓝 0) := by
  refine ⟨fun z => z ^ 2 + 1, by fun_prop, ?_, ?_, ?_, sqAddOne_ofReal_ne_zero, ?_⟩
  · intro z
    simp only
    rw [map_add, map_pow, map_one]
  · simp [Complex.I_sq]
  · simp [Complex.I_sq]
  · intro c r R hr hrR φ hφ hsupp
    have hRpos : (0 : ℝ) < R := lt_of_le_of_lt hr hrR
    have hz₀ : ((c + R / 2 : ℝ) : ℂ) ∈ ball (c : ℂ) R := by
      rw [mem_ball, Complex.dist_eq]
      have hrw : ((c + R / 2 : ℝ) : ℂ) - (c : ℂ) = ((R / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hrw, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    exact tendsto_boundaryDensity_setIntegral_zero_of_no_real_zero (by fun_prop)
      (fun z => by
        show ((starRingEnd ℂ) z) ^ 2 + 1 = (starRingEnd ℂ) (z ^ 2 + 1)
        rw [map_add, map_pow, map_one]) hr hrR hz₀
      (sqAddOne_ofReal_ne_zero (c + R / 2)) hφ hsupp sqAddOne_ofReal_ne_zero

end RHTower.RealBoundaryDivisor
