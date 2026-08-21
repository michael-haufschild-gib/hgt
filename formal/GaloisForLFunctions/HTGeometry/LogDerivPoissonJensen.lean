import GaloisForLFunctions.HTGeometry.PoissonJensenFormula
import GaloisForLFunctions.HTGeometry.HerglotzTransformKernel

/-!
# The Poisson–Jensen formula for the logarithmic derivative

Differentiating the Poisson–Jensen formula at an interior point gives Nevanlinna's starting
identity

```text
f'(w)/f(w) = ∑_u m_u ( 1/(w−u) + conj(u−c)/(R² − conj(u−c)(w−c)) )
             + (1/2π) ∫ 2(z−c)/(z−w)² · log ‖f(z)‖ ,
```

where the sum runs over the zeros and poles of `f` in the open disc with their multiplicities.
The two halves are already available: `logDeriv_eq_circleAverage_of_ne_zero` for the zero-free
factor and `circleAverage_herglotzDerivKernel_log_norm_sub` for each divisor point.  What is added
here is the assembly over the finite divisor, together with the germ transport that turns the
codiscrete factorization `f = (∏ (·−u)^{m_u}) · g` into an identity of logarithmic derivatives at
an interior point off the divisor.
-/

namespace GaloisForLFunctions.HTGeometry.PoissonJensen

open Complex Metric Real MeromorphicOn

noncomputable section

/-! ## Germ transport across a codiscrete equality -/

theorem eventuallyEq_nhdsNE_of_codiscreteWithin {U : Set ℂ} {f F : ℂ → ℂ}
    (h : f =ᶠ[Filter.codiscreteWithin U] F) {w : ℂ} (hU : U ∈ nhds w) :
    f =ᶠ[nhdsWithin w {w}ᶜ] F := by
  have hw : w ∈ U := mem_of_mem_nhds hU
  have hmem := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h) w hw
  have hUne : U ∈ nhdsWithin w {w}ᶜ := nhdsWithin_le_nhds hU
  have := Filter.inter_mem hmem hUne
  refine Filter.mem_of_superset this ?_
  rintro z ⟨hz1, hz2⟩
  rcases hz1 with hz1 | hz1
  · exact hz1
  · exact absurd hz2 hz1

theorem eq_of_eventuallyEq_nhdsNE {f F : ℂ → ℂ} {w : ℂ}
    (h : f =ᶠ[nhdsWithin w {w}ᶜ] F) (hf : ContinuousAt f w) (hF : ContinuousAt F w) :
    f w = F w := by
  have hne : (nhdsWithin w ({w}ᶜ : Set ℂ)).NeBot := Module.punctured_nhds_neBot ℂ ℂ w
  have h1 : Filter.Tendsto f (nhdsWithin w {w}ᶜ) (nhds (f w)) :=
    hf.continuousWithinAt.tendsto
  have h2 : Filter.Tendsto F (nhdsWithin w {w}ᶜ) (nhds (F w)) :=
    hF.continuousWithinAt.tendsto
  exact tendsto_nhds_unique (h1.congr' h) h2

theorem eventuallyEq_nhds_of_codiscreteWithin {U : Set ℂ} {f F : ℂ → ℂ}
    (h : f =ᶠ[Filter.codiscreteWithin U] F) {w : ℂ} (hU : U ∈ nhds w)
    (hf : ContinuousAt f w) (hF : ContinuousAt F w) :
    f =ᶠ[nhds w] F := by
  have hne := eventuallyEq_nhdsNE_of_codiscreteWithin h hU
  have hval := eq_of_eventuallyEq_nhdsNE hne hf hF
  rw [← nhdsNE_sup_pure w]
  exact Filter.mem_sup.mpr ⟨hne, hval⟩

/-! ## The logarithmic derivative of a divisor factor -/

theorem logDeriv_sub_zpow (u w : ℂ) (n : ℤ) (h : w - u ≠ 0) :
    logDeriv (fun z : ℂ => (z - u) ^ n) w = (n : ℂ) / (w - u) := by
  have h1 : HasDerivAt (fun z : ℂ => z - u) 1 w := (hasDerivAt_id w).sub_const u
  have h2 : HasDerivAt (fun z : ℂ => (z - u) ^ n) ((n : ℂ) * (w - u) ^ (n - 1) * 1) w := by
    have := (hasDerivAt_zpow n (w - u) (Or.inl h)).comp w h1
    exact this
  rw [logDeriv_apply, h2.deriv]
  rw [zpow_sub₀ h, zpow_one]
  field_simp

/-! ## Circle integrability against the differentiated kernel -/

open MeasureTheory in
theorem circleIntegrable_herglotzDeriv_mul {c : ℂ} {R : ℝ} {v : ℂ → ℝ} (hR : 0 < R)
    (hv : CircleIntegrable v c R) {w : ℂ} (hw : w ∈ ball c R) :
    CircleIntegrable (fun z => herglotzDerivKernel c w z * ((v z : ℝ) : ℂ)) c R := by
  have hwc : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  set ε : ℝ := (R - ‖w - c‖) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hne := circleMap_ne_of_mem_ball hR hwc hεdef w (mem_ball_self hεpos)
  have hVint : IntervalIntegrable (fun θ : ℝ => ((v (circleMap c R θ) : ℝ) : ℂ))
      volume 0 (2 * Real.pi) := by
    have hv' : IntervalIntegrable (fun θ : ℝ => v (circleMap c R θ)) volume 0 (2 * Real.pi) := hv
    rw [intervalIntegrable_iff] at hv' ⊢
    exact hv'.ofReal
  have hcont : Continuous (fun θ : ℝ => herglotzDerivKernel c w (circleMap c R θ)) := by
    simp only [herglotzDerivKernel]
    refine Continuous.div ?_ ?_ (fun θ => ?_)
    · exact continuous_const.mul ((continuous_circleMap c R).sub continuous_const)
    · exact ((continuous_circleMap c R).sub continuous_const).pow 2
    · exact pow_ne_zero 2 (sub_ne_zero.mpr (hne θ))
  exact hVint.continuousOn_mul hcont.continuousOn


/-! ## The circle average of the differentiated kernel against `log ‖f‖` -/

open MeasureTheory in
/-- **The differentiated Poisson–Jensen split.**  The circle average of the differentiated Herglotz
kernel against `log ‖f‖` is the sum of the Blaschke terms of the divisor plus the logarithmic
derivative of the zero-free factor. -/
theorem circleAverage_herglotzDeriv_log_split {c w : ℂ} {R : ℝ} {f g : ℂ → ℂ} {D : ℂ → ℤ}
    (hR : 0 < R) (hfin : (Function.support D).Finite)
    (hsupp : ∀ u ∈ hfin.toFinset, u ∈ ball c R)
    (hlog : (fun x => Real.log ‖f x‖) =ᶠ[Filter.codiscreteWithin (closedBall c |R|)]
      (∑ᶠ u : ℂ, fun x : ℂ => (D u : ℝ) * Real.log ‖x - u‖) + fun x => Real.log ‖g x‖)
    (hgan : AnalyticOnNhd ℂ g (closedBall c R)) (hgne : ∀ z ∈ closedBall c R, g z ≠ 0)
    (hw : w ∈ ball c R) :
    circleAverage (fun z => herglotzDerivKernel c w z * ((Real.log ‖f z‖ : ℝ) : ℂ)) c R
      = (∑ u ∈ hfin.toFinset, (D u : ℂ) *
          (-(starRingEnd ℂ) (u - c) / ((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - c) * (w - c))))
        + deriv g w / g w := by
  classical
  have habs : |R| = R := abs_of_pos hR
  set S : ℂ → ℝ := fun z => ∑ u ∈ hfin.toFinset, (D u : ℝ) * Real.log ‖z - u‖ with hS
  set L : ℂ → ℝ := fun z => Real.log ‖g z‖ with hL
  have hfinsum : (∑ᶠ u : ℂ, fun x : ℂ => (D u : ℝ) * Real.log ‖x - u‖) = S := by
    have hsub : (Function.support fun u : ℂ => fun x : ℂ => (D u : ℝ) * Real.log ‖x - u‖)
        ⊆ hfin.toFinset := by
      intro u hu
      simp only [Function.mem_support] at hu
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
      intro hzero
      exact hu (by funext x; rw [hzero]; simp)
    rw [finsum_eq_sum_of_support_subset _ hsub]
    funext z
    rw [Finset.sum_apply]
  rw [hfinsum] at hlog
  have hTermInt : ∀ u : ℂ, CircleIntegrable (fun x : ℂ => Real.log ‖x - u‖) c R := fun u =>
    MeromorphicOn.circleIntegrable_log_norm
      (f := fun z => z - u) (fun z _ => (analyticAt_id.sub analyticAt_const).meromorphicAt)
  have hLint : CircleIntegrable L c R := by
    have hmero : MeromorphicOn g (sphere c |R|) := by
      rw [habs]
      exact (hgan.mono sphere_subset_closedBall).meromorphicOn
    exact hmero.circleIntegrable_log_norm
  have hSint : CircleIntegrable S c R := by
    have heq : (fun θ : ℝ => S (circleMap c R θ))
        = ∑ u ∈ hfin.toFinset,
            (fun θ : ℝ => (D u : ℝ) * Real.log ‖circleMap c R θ - u‖) := by
      funext θ
      rw [Finset.sum_apply]
    show IntervalIntegrable (fun θ : ℝ => S (circleMap c R θ)) volume 0 (2 * Real.pi)
    rw [heq]
    exact IntervalIntegrable.sum _ fun u _ => ((hTermInt u).smul (D u : ℝ))
  have hcongr : (fun z => herglotzDerivKernel c w z * ((Real.log ‖f z‖ : ℝ) : ℂ))
      =ᶠ[Filter.codiscreteWithin (sphere c |R|)]
      (fun z => herglotzDerivKernel c w z * (((S z + L z : ℝ)) : ℂ)) := by
    have hmono := Filter.codiscreteWithin_mono
      (sphere_subset_closedBall (x := c) (ε := |R|)) hlog
    filter_upwards [hmono] with z hz
    have hval : Real.log ‖f z‖ = S z + L z := by simpa using hz
    rw [hval]
  rw [circleAverage_congr_codiscreteWithin hcongr hR.ne']
  have hsplitfun : (fun z => herglotzDerivKernel c w z * (((S z + L z : ℝ)) : ℂ))
      = (fun z => herglotzDerivKernel c w z * ((S z : ℝ) : ℂ))
        + (fun z => herglotzDerivKernel c w z * ((L z : ℝ) : ℂ)) := by
    funext z
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [hsplitfun, circleAverage_add (circleIntegrable_herglotzDeriv_mul hR hSint hw)
    (circleIntegrable_herglotzDeriv_mul hR hLint hw)]
  congr 1
  · have hexp : (fun z => herglotzDerivKernel c w z * ((S z : ℝ) : ℂ))
        = ∑ u ∈ hfin.toFinset, (D u : ℂ) •
            (fun z : ℂ => herglotzDerivKernel c w z * ((Real.log ‖z - u‖ : ℝ) : ℂ)) := by
      funext z
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, hS]
      rw [Complex.ofReal_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by push_cast; ring
    rw [hexp, circleAverage_sum (f := fun u : ℂ => (D u : ℂ) •
        (fun z : ℂ => herglotzDerivKernel c w z * ((Real.log ‖z - u‖ : ℝ) : ℂ)))
      (fun u _ => ((circleIntegrable_herglotzDeriv_mul hR (hTermInt u) hw).smul (D u : ℂ)))]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [circleAverage_smul, circleAverage_herglotzDerivKernel_log_norm_sub hR (hsupp u hu) hw]
    rfl
  · exact (logDeriv_eq_circleAverage_of_ne_zero hR hgan hgne hw).symm


/-! ## The logarithmic derivative of the extracted factorization -/

theorem finprod_shiftPow_apply {D : ℂ → ℤ} (hfin : (Function.support D).Finite) (z : ℂ) :
    ((∏ᶠ u : ℂ, (fun x : ℂ => x - u) ^ (D u)) z)
      = ∏ u ∈ hfin.toFinset, (z - u) ^ (D u) := by
  classical
  have hmul : (Function.mulSupport fun u : ℂ => (fun x : ℂ => x - u) ^ (D u))
      ⊆ hfin.toFinset := by
    intro u hu
    simp only [Function.mem_mulSupport] at hu
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro hzero
    exact hu (by rw [hzero, zpow_zero])
  rw [finprod_eq_prod_of_mulSupport_subset _ hmul, Finset.prod_apply]
  exact Finset.prod_congr rfl fun u _ => rfl

/-- **The logarithmic derivative of an extracted factorization.**  At an interior point off the
divisor, the logarithmic derivative of `f` is the sum of the simple divisor poles plus the
logarithmic derivative of the zero-free factor. -/
theorem logDeriv_eq_divisorSum_add {U : Set ℂ} {f g : ℂ → ℂ} {D : ℂ → ℤ} {w : ℂ}
    (hfin : (Function.support D).Finite)
    (hfac : f =ᶠ[Filter.codiscreteWithin U] (∏ᶠ u : ℂ, (fun x : ℂ => x - u) ^ (D u)) • g)
    (hU : U ∈ nhds w) (hf : ContinuousAt f w)
    (hgan : AnalyticAt ℂ g w) (hgne : g w ≠ 0)
    (hwsupp : ∀ u ∈ hfin.toFinset, w - u ≠ 0) :
    logDeriv f w = (∑ u ∈ hfin.toFinset, (D u : ℂ) / (w - u)) + logDeriv g w := by
  classical
  set F : ℂ → ℂ := fun z => (∏ u ∈ hfin.toFinset, (z - u) ^ (D u)) * g z with hF
  have hfacF : f =ᶠ[Filter.codiscreteWithin U] F := by
    refine hfac.trans (Filter.Eventually.of_forall fun z => ?_)
    show ((∏ᶠ u : ℂ, (fun x : ℂ => x - u) ^ (D u)) • g) z = F z
    rw [Pi.smul_apply', smul_eq_mul, finprod_shiftPow_apply hfin]
  have hprodAn : AnalyticAt ℂ (fun z : ℂ => ∏ u ∈ hfin.toFinset, (z - u) ^ (D u)) w := by
    refine Finset.analyticAt_fun_prod _ fun u hu => ?_
    exact AnalyticAt.fun_zpow (analyticAt_id.sub analyticAt_const) (hwsupp u hu)
  have hFcont : ContinuousAt F w := (hprodAn.mul hgan).continuousAt
  have hEq : f =ᶠ[nhds w] F := eventuallyEq_nhds_of_codiscreteWithin hfacF hU hf hFcont
  have hderiv : deriv f w = deriv F w := Filter.EventuallyEq.deriv_eq hEq
  have hval : f w = F w := hEq.eq_of_nhds
  rw [logDeriv_apply, hderiv, hval, ← logDeriv_apply]
  have hprodne : (∏ u ∈ hfin.toFinset, (w - u) ^ (D u)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun u hu => ?_
    exact zpow_ne_zero _ (hwsupp u hu)
  rw [hF, logDeriv_mul w hprodne hgne hprodAn.differentiableAt hgan.differentiableAt]
  congr 1
  rw [logDeriv_prod (f := fun u => fun z : ℂ => (z - u) ^ (D u))
    (fun u hu => zpow_ne_zero _ (hwsupp u hu))
    (fun u hu => (AnalyticAt.fun_zpow (analyticAt_id.sub analyticAt_const)
      (hwsupp u hu)).differentiableAt)]
  exact Finset.sum_congr rfl fun u hu => logDeriv_sub_zpow u w (D u) (hwsupp u hu)


/-! ## The Nevanlinna pointwise bound -/

open MeasureTheory in
theorem norm_circleAverage_le {c : ℂ} {R : ℝ} (F : ℂ → ℂ) :
    ‖circleAverage F c R‖ ≤ circleAverage (fun z => ‖F z‖) c R := by
  rw [circleAverage_def, circleAverage_def, norm_smul, smul_eq_mul]
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun θ : ℝ => F (circleMap c R θ)) (a := 0) (b := 2 * Real.pi) hpi
  have hn : ‖(2 * Real.pi)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hn]
  exact mul_le_mul_of_nonneg_left h (by positivity)

open MeasureTheory in
/-- **The boundary term of the differentiated Poisson–Jensen formula is bounded by the circle
average of `|log ‖f‖|`.**  This is the analytic half of Nevanlinna's estimate for the logarithmic
derivative. -/
theorem norm_circleAverage_herglotzDeriv_log_le {c w : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R)
    (hfs : MeromorphicOn f (sphere c |R|)) (hw : w ∈ ball c R) :
    ‖circleAverage (fun z => herglotzDerivKernel c w z * ((Real.log ‖f z‖ : ℝ) : ℂ)) c R‖
      ≤ 2 * R / (R - ‖w - c‖) ^ 2
        * circleAverage (fun z => |Real.log ‖f z‖|) c R := by
  have hwc : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hδ : 0 < R - ‖w - c‖ := by linarith
  have hlogint : CircleIntegrable (fun z => Real.log ‖f z‖) c R := hfs.circleIntegrable_log_norm
  have habsint : CircleIntegrable (fun z => |Real.log ‖f z‖|) c R := hlogint.abs
  have hprodint := circleIntegrable_herglotzDeriv_mul hR hlogint hw
  refine le_trans (norm_circleAverage_le _) ?_
  have hbound : ∀ z ∈ sphere c |R|,
      ‖herglotzDerivKernel c w z * ((Real.log ‖f z‖ : ℝ) : ℂ)‖
        ≤ (2 * R / (R - ‖w - c‖) ^ 2) * |Real.log ‖f z‖| := by
    intro z hz
    have hzn : ‖z - c‖ = R := by
      rw [mem_sphere_iff_norm, abs_of_pos hR] at hz
      exact hz
    have hlow : (R - ‖w - c‖) ≤ ‖z - w‖ := dist_sphere_ball hzn le_rfl
    have hk := norm_herglotzDerivKernel_le hR hzn hδ hlow
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  have hmono : circleAverage (fun z => ‖herglotzDerivKernel c w z * ((Real.log ‖f z‖ : ℝ) : ℂ)‖) c R
      ≤ circleAverage (fun z => (2 * R / (R - ‖w - c‖) ^ 2) * |Real.log ‖f z‖|) c R := by
    refine circleAverage_mono hprodint.norm ?_ hbound
    exact habsint.smul (2 * R / (R - ‖w - c‖) ^ 2)
  refine le_trans hmono (le_of_eq ?_)
  have : (fun z => (2 * R / (R - ‖w - c‖) ^ 2) * |Real.log ‖f z‖|)
      = (2 * R / (R - ‖w - c‖) ^ 2) • (fun z => |Real.log ‖f z‖|) := rfl
  rw [this, circleAverage_smul, smul_eq_mul]


/-! ## The Poisson–Jensen formula for the logarithmic derivative -/

open MeasureTheory in
/-- **Poisson–Jensen for the logarithmic derivative.**  At an interior point where `f` is analytic
and nonzero, the logarithmic derivative is the sum of the divisor terms — a simple pole at each
zero or pole together with its Blaschke reflection — plus the circle average of the differentiated
Herglotz kernel against `log ‖f‖`.  This is Nevanlinna's starting identity. -/
theorem logDeriv_poissonJensen {c w : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R)
    (h₁f : MeromorphicOn f (closedBall c |R|))
    (h₂f : ∀ u : (closedBall c |R| : Set ℂ), meromorphicOrderAt f u ≠ ⊤)
    (hbd : ∀ u ∈ sphere c |R|, divisor f (closedBall c |R|) u = 0)
    (hw : w ∈ ball c R) (hwf : AnalyticAt ℂ f w) (hfw : f w ≠ 0)
    (hwdiv : divisor f (closedBall c |R|) w = 0) :
    logDeriv f w
      = (∑ᶠ u : ℂ, (divisor f (closedBall c |R|) u : ℂ) *
          (1 / (w - u) + (starRingEnd ℂ) (u - c)
            / ((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - c) * (w - c))))
        + circleAverage (fun z => herglotzDerivKernel c w z * ((Real.log ‖f z‖ : ℝ) : ℂ)) c R := by
  classical
  have habs : |R| = R := abs_of_pos hR
  set CB := closedBall c |R| with hCB
  set D : ℂ → ℤ := fun u => divisor f CB u with hD
  have hfin : (Function.support D).Finite :=
    (divisor f CB).finiteSupport (isCompact_closedBall c |R|)
  obtain ⟨g, hgan, hgne, hfac⟩ := h₁f.extract_zeros_poles h₂f hfin
  have hlog := MeromorphicOn.extract_zeros_poles_log hgne hfac
  -- geometry of the support
  have hsupp : ∀ u ∈ hfin.toFinset, u ∈ ball c R := by
    intro u hu
    have hune : D u ≠ 0 := by
      simpa [Set.Finite.mem_toFinset, Function.mem_support] using hu
    have humem : u ∈ CB := (divisor f CB).supportWithinDomain (by simpa [hD] using hune)
    rw [hCB, habs] at humem
    rcases lt_or_eq_of_le (mem_closedBall_iff_norm.mp humem) with hlt | heq
    · exact mem_ball_iff_norm.mpr hlt
    · exfalso
      refine hune ?_
      have : u ∈ sphere c |R| := by
        rw [mem_sphere_iff_norm, habs]
        exact heq
      simpa [hD] using hbd u this
  have hwsupp : ∀ u ∈ hfin.toFinset, w - u ≠ 0 := by
    intro u hu hzero
    have huw : u = w := by linear_combination -hzero
    subst huw
    have hune : D u ≠ 0 := by
      simpa [Set.Finite.mem_toFinset, Function.mem_support] using hu
    exact hune (by simpa [hD] using hwdiv)
  -- the zero-free factor at `w`
  have hwCB : w ∈ CB := by
    rw [hCB, habs]
    exact ball_subset_closedBall hw
  have hganw : AnalyticAt ℂ g w := hgan w hwCB
  have hgnew : g w ≠ 0 := hgne ⟨w, hwCB⟩
  have hganR : AnalyticOnNhd ℂ g (closedBall c R) := by rw [← habs]; exact hgan
  have hgneR : ∀ z ∈ closedBall c R, g z ≠ 0 := by
    intro z hz
    rw [← habs] at hz
    exact hgne ⟨z, hz⟩
  -- Step A and Step B
  have hstepA := logDeriv_eq_divisorSum_add (U := CB) (f := f) (g := g) (D := D) hfin hfac
    (by rw [hCB, habs]; exact mem_nhds_iff.mpr ⟨ball c R, ball_subset_closedBall, isOpen_ball, hw⟩)
    hwf.continuousAt hganw hgnew hwsupp
  have hstepB := circleAverage_herglotzDeriv_log_split (c := c) (w := w) (R := R) (f := f)
    (g := g) (D := D) hR hfin hsupp (by rw [hCB] at hlog; exact hlog) hganR hgneR hw
  -- assemble
  have hfinsum : (∑ᶠ u : ℂ, (D u : ℂ) *
      (1 / (w - u) + (starRingEnd ℂ) (u - c)
        / ((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - c) * (w - c))))
      = ∑ u ∈ hfin.toFinset, (D u : ℂ) *
        (1 / (w - u) + (starRingEnd ℂ) (u - c)
          / ((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - c) * (w - c))) := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
    intro hzero
    exact hu (by rw [hzero]; simp)
  have hcancel : (∑ u ∈ hfin.toFinset, (D u : ℂ) *
        (1 / (w - u) + (starRingEnd ℂ) (u - c)
          / ((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - c) * (w - c))))
      + (∑ u ∈ hfin.toFinset, (D u : ℂ) *
        (-(starRingEnd ℂ) (u - c) / ((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - c) * (w - c))))
      = ∑ u ∈ hfin.toFinset, (D u : ℂ) / (w - u) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [hfinsum, hstepA, hstepB, logDeriv_apply]
  linear_combination -hcancel


open MeasureTheory in
/-- **The Nevanlinna pointwise bound for the logarithmic derivative.**  At an interior point where
`f` is analytic and nonzero, the logarithmic derivative is bounded by the divisor contribution plus
an explicit multiple of the circle average of `|log ‖f‖|`. -/
theorem norm_logDeriv_le {c w : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R)
    (h₁f : MeromorphicOn f (closedBall c |R|))
    (h₂f : ∀ u : (closedBall c |R| : Set ℂ), meromorphicOrderAt f u ≠ ⊤)
    (hbd : ∀ u ∈ sphere c |R|, divisor f (closedBall c |R|) u = 0)
    (hw : w ∈ ball c R) (hwf : AnalyticAt ℂ f w) (hfw : f w ≠ 0)
    (hwdiv : divisor f (closedBall c |R|) w = 0) :
    ‖logDeriv f w‖
      ≤ ‖∑ᶠ u : ℂ, (divisor f (closedBall c |R|) u : ℂ) *
          (1 / (w - u) + (starRingEnd ℂ) (u - c)
            / ((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - c) * (w - c)))‖
        + 2 * R / (R - ‖w - c‖) ^ 2 * circleAverage (fun z => |Real.log ‖f z‖|) c R := by
  have hfs : MeromorphicOn f (sphere c |R|) := fun z hz => h₁f z (sphere_subset_closedBall hz)
  rw [logDeriv_poissonJensen hR h₁f h₂f hbd hw hwf hfw hwdiv]
  refine le_trans (norm_add_le _ _) ?_
  gcongr
  exact norm_circleAverage_herglotzDeriv_log_le hR hfs hw



/-! ## From the circle average of `|log ‖f‖|` to the Nevanlinna proximities -/

theorem abs_log_eq_posLog_add_posLog_inv (x : ℝ) :
    |Real.log x| = Real.posLog x + Real.posLog x⁻¹ := by
  rw [Real.posLog_apply, Real.posLog_apply]
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · rw [Real.log_inv]
    rcases le_total 0 (Real.log x) with hl | hl
    · rw [abs_of_nonneg hl, max_eq_right hl, max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonpos hl, max_eq_left hl, max_eq_right (by linarith)]
      ring

open MeasureTheory in
/-- **The circle average of `|log ‖f‖|` is the sum of the two Nevanlinna proximity functions.**
This converts the boundary term of the differentiated Poisson–Jensen formula into value-
distribution data. -/
theorem circleAverage_abs_log_norm_eq {r : ℝ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f (sphere 0 |r|)) :
    circleAverage (fun z => |Real.log ‖f z‖|) 0 r
      = ValueDistribution.proximity f ⊤ r + ValueDistribution.proximity f 0 r := by
  have hlog : CircleIntegrable (fun z => Real.log ‖f z‖) 0 r := hf.circleIntegrable_log_norm
  have h1 : CircleIntegrable (fun z => Real.posLog ‖f z‖) 0 r := hf.circleIntegrable_posLog_norm
  have h2 : CircleIntegrable (fun z => Real.posLog ‖f z‖⁻¹) 0 r := by
    have hsub := hlog.abs.sub h1
    have heq : (fun θ : ℝ => Real.posLog ‖f (circleMap 0 r θ)‖⁻¹)
        = fun θ : ℝ => |Real.log ‖f (circleMap 0 r θ)‖|
            - Real.posLog ‖f (circleMap 0 r θ)‖ := by
      funext θ
      have hid := abs_log_eq_posLog_add_posLog_inv ‖f (circleMap 0 r θ)‖
      linarith
    show IntervalIntegrable (fun θ : ℝ => Real.posLog ‖f (circleMap 0 r θ)‖⁻¹)
      volume 0 (2 * Real.pi)
    rw [heq]
    exact hsub
  have hpt : (fun z => |Real.log ‖f z‖|)
      = (fun z => Real.posLog ‖f z‖) + (fun z => Real.posLog ‖f z‖⁻¹) := by
    funext z
    exact abs_log_eq_posLog_add_posLog_inv ‖f z‖
  have hA : ValueDistribution.proximity f ⊤ r
      = circleAverage (fun z => Real.posLog ‖f z‖) 0 r := by
    simp [ValueDistribution.proximity]
  have hB : ValueDistribution.proximity f 0 r
      = circleAverage (fun z => Real.posLog ‖f z‖⁻¹) 0 r := by
    simp only [ValueDistribution.proximity]
    rw [dif_neg (show (0 : WithTop ℂ) ≠ ⊤ by simp)]
    simp
  rw [hpt, circleAverage_add h1 h2, hA, hB]


open MeasureTheory in
/-- **The circle average of `|log ‖f‖|` is at most twice the characteristic.**  Both proximity
functions are bounded by their characteristics, and the first main theorem compares the
characteristic at `0` with the characteristic at `⊤`. -/
theorem circleAverage_abs_log_norm_le_characteristic {r : ℝ} (hr : 1 ≤ r) {f : ℂ → ℂ}
    (hfm : Meromorphic f) :
    circleAverage (fun z => |Real.log ‖f z‖|) 0 r
      ≤ 2 * ValueDistribution.characteristic f ⊤ r
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  have hf : MeromorphicOn f (sphere 0 |r|) := fun z _ => hfm z
  rw [circleAverage_abs_log_norm_eq hf]
  have hchar : ∀ a : WithTop ℂ, ValueDistribution.characteristic f a r
      = ValueDistribution.proximity f a r + ValueDistribution.logCounting f a r := fun a => rfl
  have h1 : ValueDistribution.proximity f ⊤ r ≤ ValueDistribution.characteristic f ⊤ r := by
    rw [hchar ⊤]
    linarith [ValueDistribution.logCounting_nonneg (f := f) (e := (⊤ : WithTop ℂ)) hr]
  have h2 : ValueDistribution.proximity f 0 r ≤ ValueDistribution.characteristic f 0 r := by
    rw [hchar 0]
    linarith [ValueDistribution.logCounting_nonneg (f := f) (e := (0 : WithTop ℂ)) hr]
  have h3 : ValueDistribution.characteristic f 0 = ValueDistribution.characteristic f⁻¹ ⊤ := by
    rw [ValueDistribution.characteristic, ValueDistribution.characteristic,
      ValueDistribution.proximity_inv, ValueDistribution.logCounting_inv]
  have h4 := ValueDistribution.characteristic_sub_characteristic_inv_le (f := f) (R := r) hfm
  have h5 : ValueDistribution.characteristic f⁻¹ ⊤ r - ValueDistribution.characteristic f ⊤ r
      ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    have := (abs_le.mp h4).1
    linarith
  have h6 : ValueDistribution.characteristic f 0 r = ValueDistribution.characteristic f⁻¹ ⊤ r := by
    rw [h3]
  linarith [h1, h2, h5, h6]


open MeasureTheory in
/-- **The Nevanlinna pointwise bound in value-distribution form.**  At an interior point of a disc
of radius `R ≥ 1` centred at the origin, where `f` is analytic and nonzero, the logarithmic
derivative is bounded by the divisor contribution plus an explicit multiple of the Nevanlinna
characteristic. -/
theorem norm_logDeriv_le_characteristic {w : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : 1 ≤ R)
    (hfm : Meromorphic f)
    (h₂f : ∀ u : (closedBall (0 : ℂ) |R| : Set ℂ), meromorphicOrderAt f u ≠ ⊤)
    (hbd : ∀ u ∈ sphere (0 : ℂ) |R|, divisor f (closedBall (0 : ℂ) |R|) u = 0)
    (hw : w ∈ ball (0 : ℂ) R) (hwf : AnalyticAt ℂ f w) (hfw : f w ≠ 0)
    (hwdiv : divisor f (closedBall (0 : ℂ) |R|) w = 0) :
    ‖logDeriv f w‖
      ≤ ‖∑ᶠ u : ℂ, (divisor f (closedBall (0 : ℂ) |R|) u : ℂ) *
          (1 / (w - u) + (starRingEnd ℂ) (u - 0)
            / ((R : ℂ) ^ 2 - (starRingEnd ℂ) (u - 0) * (w - 0)))‖
        + 2 * R / (R - ‖w - 0‖) ^ 2
          * (2 * ValueDistribution.characteristic f ⊤ R
            + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) := by
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have h₁f : MeromorphicOn f (closedBall (0 : ℂ) |R|) := fun z _ => hfm z
  have hbase := norm_logDeriv_le hRpos h₁f h₂f hbd hw hwf hfw hwdiv
  have havg := circleAverage_abs_log_norm_le_characteristic hR hfm
  have hcoef : 0 ≤ 2 * R / (R - ‖w - 0‖) ^ 2 := by
    have hwn : ‖w - 0‖ < R := by simpa using mem_ball_iff_norm.mp hw
    have : 0 < R - ‖w - 0‖ := by linarith
    positivity
  refine le_trans hbase ?_
  gcongr


end

end GaloisForLFunctions.HTGeometry.PoissonJensen
