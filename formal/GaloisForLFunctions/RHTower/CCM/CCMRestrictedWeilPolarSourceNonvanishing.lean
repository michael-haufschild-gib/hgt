import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarGroundSourceMoment

/-!
# Nonvanishing of the actual constrained Weil pole source

The boundary–arithmetic source diverges at the aperture endpoint and has no
essential upper bound there. Its actual L² defect therefore lies outside the
entire two-pole span. The complete constrained source functional is nonzero
and realizes every complex value, at every positive aperture. This excludes
automatic pole-space invariance, not a particular ground's forced equation.
The two boundary logarithms also split into a common reflection-symmetric
singular part and an explicit asymmetry of absolute size less than `log 2`.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology ENNReal
noncomputable section
namespace RHTower

/-- The actual two-tail Gamma boundary diverges at the right aperture endpoint. -/
theorem tendsto_ccmGammaPolarBoundary_right (a : SuzukiPositiveAperture) :
    Tendsto (fun x : ℝ => ccmGammaPolarBoundary (a.1-x) (a.1+x)) (𝓝[<] a.1) atTop := by
  have harg : Tendsto (fun x : ℝ => 1-Real.exp (-(2*(a.1-x)))) (𝓝[<] a.1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Continuous (fun x : ℝ => 1-Real.exp (-(2*(a.1-x)))) := by fun_prop
      simpa using (h.tendsto a.1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [show x<a.1 from hx]))
  have hlog := Real.tendsto_log_nhdsGT_zero.comp harg
  have hdiv : Tendsto (fun x : ℝ => -(1/2)*Real.log (1-Real.exp (-(2*(a.1-x)))))
      (𝓝[<] a.1) atTop :=
    Filter.Tendsto.neg_mul_atBot (by norm_num) tendsto_const_nhds hlog
  have hL : 1-Real.exp (-(a.1+a.1)) ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [a.property])))
  have hL2 : 1-Real.exp (-(2*(a.1+a.1))) ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [a.property])))
  have hc : ContinuousAt (fun x : ℝ => -Real.log (1-Real.exp (-(a.1+x)))+
      (1/2)*Real.log (1-Real.exp (-(2*(a.1+x))))) a.1 := by fun_prop
  have h := hdiv.atTop_add (hc.tendsto.mono_left nhdsWithin_le_nhds)
  convert h using 1
  funext x
  unfold ccmGammaPolarBoundary
  ring

/-- The combined boundary–arithmetic profile tends to positive infinity at the right endpoint. -/
theorem tendsto_ccmPolarBoundaryArithmeticProfile_re_right (a : SuzukiPositiveAperture) :
    Tendsto (fun x : ℝ => (ccmPolarBoundaryArithmeticProfile a x).re) (𝓝[<] a.1) atTop := by
  let C := Chebyshev.psi (Real.exp (2*a.1)) + (Real.log 4+5)
  have hbase : Tendsto (fun x : ℝ => ccmGammaPolarBoundary (a.1-x) (a.1+x)-C)
      (𝓝[<] a.1) atTop :=
    tendsto_atTop_add_const_right _ (-C) (tendsto_ccmGammaPolarBoundary_right a)
  have hbound : ∀ᶠ x in 𝓝[<] a.1,
      ccmGammaPolarBoundary (a.1-x) (a.1+x)-C ≤
        ccmGammaPolarBoundary (a.1-x) (a.1+x)-
          (Chebyshev.psi (Real.exp (a.1-x))-Real.exp (a.1-x))-ccmReciprocalMangoldtError (a.1+x) := by
    filter_upwards [Ioo_mem_nhdsLT (show -a.1<a.1 by linarith [a.property])] with x hx
    have hp := Chebyshev.psi_mono (Real.exp_le_exp.mpr (show a.1-x≤2*a.1 by linarith [hx.1]))
    have he := (abs_le.mp (abs_ccmReciprocalMangoldtError_le (show 0≤a.1+x by linarith [hx.1]))).2
    dsimp [C]
    linarith [Real.exp_pos (a.1-x)]
  have hbr := tendsto_atTop_mono' _ hbound hbase
  have he : Tendsto (fun x : ℝ => Real.exp (x/2)) (𝓝[<] a.1) (𝓝 (Real.exp (a.1/2))) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (x/2))).tendsto a.1 |>.mono_left nhdsWithin_le_nhds
  simpa only [ccmPolarBoundaryArithmeticProfile, Complex.ofReal_re] using
    Filter.Tendsto.pos_mul_atTop (Real.exp_pos _) he hbr

private theorem not_ae_bounded_of_tendsto_right {a l C : ℝ} (hl : l<a) (f : ℝ → ℝ)
    (ht : Tendsto f (𝓝[<] a) atTop)
    (hb : ∀ᵐ x : ℝ, x ∈ Ioo l a → f x ≤ C) : False := by
  have he : ∀ᶠ x in 𝓝[<] a, x ∈ Ioo l a ∧ C+1 ≤ f x := by
    filter_upwards [Ioo_mem_nhdsLT hl, ht.eventually_ge_atTop (C+1)] with x hx hy
    exact ⟨hx,hy⟩
  obtain ⟨b,hb',hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  have hm : volume (Ioo b a) ≠ 0 := isOpen_Ioo.measure_ne_zero volume (nonempty_Ioo.mpr hb')
  obtain ⟨x,hx,hbx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hb)
  have h := hsub hx
  have := hbx h.1
  linarith [h.2]

/-- The literal boundary–arithmetic source has no essential upper bound on its aperture. -/
theorem not_ae_bounded_ccmPolarBoundaryArithmeticProfile (a : SuzukiPositiveAperture) (C : ℝ) :
    ¬ ∀ᵐ x : ℝ, x ∈ Ioo (-a.1) a.1 → (ccmPolarBoundaryArithmeticProfile a x).re ≤ C :=
  not_ae_bounded_of_tendsto_right (by linarith [a.property]) _
    (tendsto_ccmPolarBoundaryArithmeticProfile_re_right a)

/-- Literal physical coefficients of a two-pole forcing vector. -/
theorem ccmPolarForcing_coeFn (a : SuzukiPositiveAperture) (c : ℂ × ℂ) :
    ((ccmPolarForcing a c : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x =>
        c.1 * ccmPolarProfile (1/2) x+c.2 * ccmPolarProfile (-1/2) x) := by
  change (((c.1 • ccmPolarL2Vector a (1/2)+c.2 • ccmPolarL2Vector a (-1/2) : SoninL2)) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add (c.1 • ccmPolarL2Vector a (1/2)) (c.2 • ccmPolarL2Vector a (-1/2)),
    Lp.coeFn_smul c.1 (ccmPolarL2Vector a (1/2)), Lp.coeFn_smul c.2 (ccmPolarL2Vector a (-1/2)),
    ccmPolarL2Vector_coeFn a (1/2), ccmPolarL2Vector_coeFn a (-1/2)] with x ha hp hm hxp hxm
  simp only [Pi.add_apply, Pi.smul_apply] at ha hp hm
  rw [ha,hp,hm,hxp,hxm]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx, smul_eq_mul]
  · simp [indicator_of_notMem hx]

/-- At every positive aperture, the actual boundary–arithmetic defect lies outside the entire pole span. -/
theorem ccmPolarWeilBoundaryDefect_ne_forcing (a : SuzukiPositiveAperture) (c : ℂ × ℂ) :
    ccmPolarWeilBoundaryDefect a ≠ ccmPolarForcing a c := by
  intro heq
  let q : ℝ → ℂ := fun x => c.1 * ccmPolarProfile (1/2) x+c.2 * ccmPolarProfile (-1/2) x
  have hq : Continuous q := by dsimp [q,ccmPolarProfile]; fun_prop
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq.continuousOn
  apply not_ae_bounded_ccmPolarBoundaryArithmeticProfile a C
  have hd := ccmPolarWeilBoundaryDefect_coeFn a
  rw [heq] at hd
  filter_upwards [hd,ccmPolarForcing_coeFn a c] with x hx hy
  intro hxin
  have hi : x ∈ centralInterval a.1 := Ioo_subset_Icc_self hxin
  rw [indicator_of_mem hi] at hx hy
  have he : ccmPolarBoundaryArithmeticProfile a x=q x := hx.symm.trans hy
  rw [he]
  exact (Complex.re_le_norm _).trans (hC x hi)

/-- The full source coupling cannot vanish on the complete constrained sector at any aperture. -/
theorem exists_polarConstrained_boundarySource_ne_zero (a : SuzukiPositiveAperture) :
    ∃ u : CCMArchimedeanFormDomain a, IsPolarConstrained a u ∧
      ccmPolarBoundarySourceFunctional a u ≠ 0 := by
  by_contra h
  have hzero : ∀ u, IsPolarConstrained a u → ccmPolarBoundarySourceFunctional a u=0 := by
    simpa only [not_exists, not_and, not_not] using h
  obtain ⟨c,hc,_⟩ := existsUnique_ccmPolarForcing_representative a (ccmPolarBoundarySourceFunctional a) hzero
  apply ccmPolarWeilBoundaryDefect_ne_forcing a c
  exact (denseRange_ccmArchimedeanFormToAperture a).eq_of_inner_left ℂ hc

/-- Every complex source moment is realized by an actual completed two-moment constrained vector. -/
theorem polarConstrained_boundarySource_surjective (a : SuzukiPositiveAperture) :
    Function.Surjective (fun u : ccmPolarConstraintSubmodule a => ccmPolarBoundarySourceFunctional a u.1) := by
  obtain ⟨u,hu,hne⟩ := exists_polarConstrained_boundarySource_ne_zero a
  intro z
  let v : ccmPolarConstraintSubmodule a := ⟨u,hu⟩
  refine ⟨(z / ccmPolarBoundarySourceFunctional a u) • v, ?_⟩
  change ccmPolarBoundarySourceFunctional a ((z / ccmPolarBoundarySourceFunctional a u) • u)=z
  rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hne]

/-- The actual Weil image of the positive pole is outside the entire two-pole forcing space. -/
theorem ccmRestrictedWeilOperator_polarPlus_ne_forcing (a : SuzukiPositiveAperture) (c : ℂ × ℂ) :
    ccmRestrictedWeilOperator a
      ⟨ccmPolarApertureVector a (1/2),ccmPolarApertureVector_mem_weilOperator_domain a (1/2)⟩ ≠
        ccmPolarForcing a c := by
  intro hc
  rw [ccmRestrictedWeilOperator_polar_apply] at hc
  let k : ℂ := ((-Real.eulerMascheroniConstant-Real.log (2*Real.pi):ℝ):ℂ)
  apply ccmPolarWeilBoundaryDefect_ne_forcing a (c.1-k,c.2+(Real.exp (-a.1):ℂ))
  rw [ccmPolarWeilBoundaryDefect,hc,ccmPolarForcing,ccmPolarForcing]
  change (c.1 • ccmPolarApertureVector a (1/2)+c.2 • ccmPolarApertureVector a (-1/2)) -
    k • ccmPolarApertureVector a (1/2)+(Real.exp (-a.1):ℂ) • ccmPolarApertureVector a (-1/2) =
      (c.1-k) • ccmPolarApertureVector a (1/2)+
        (c.2+(Real.exp (-a.1):ℂ)) • ccmPolarApertureVector a (-1/2)
  rw [sub_smul,add_smul]
  abel

/-- Both logarithmic singularities have one common reflection-symmetric part;
the remaining endpoint asymmetry is the bounded logarithm of `1+exp(-L)`. -/
theorem ccmGammaPolarBoundary_symmetric_decomposition {R L : ℝ} (hL : 0<L) :
    ccmGammaPolarBoundary R L =
      -(1/2)*Real.log (1-Real.exp (-(2*R))) -
        (1/2)*Real.log (1-Real.exp (-(2*L))) + Real.log (1+Real.exp (-L)) := by
  have hm : 0<1-Real.exp (-L) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hp : 0<1+Real.exp (-L) := by positivity
  have he : 1-Real.exp (-(2*L))=(1-Real.exp (-L))*(1+Real.exp (-L)) := by
    rw [show -(2*L)=(-L)+(-L) by ring,Real.exp_add]
    ring
  have hlog : Real.log (1-Real.exp (-(2*L))) =
      Real.log (1-Real.exp (-L))+Real.log (1+Real.exp (-L)) := by
    rw [he,Real.log_mul hm.ne' hp.ne']
  unfold ccmGammaPolarBoundary
  rw [hlog]
  ring

/-- Exact reflection-odd boundary remainder: every divergent endpoint logarithm cancels. -/
theorem ccmGammaPolarBoundary_sub_swap {R L : ℝ} (hR : 0<R) (hL : 0<L) :
    ccmGammaPolarBoundary R L-ccmGammaPolarBoundary L R =
      Real.log (1+Real.exp (-L))-Real.log (1+Real.exp (-R)) := by
  rw [ccmGammaPolarBoundary_symmetric_decomposition hL,
    ccmGammaPolarBoundary_symmetric_decomposition hR]
  ring

/-- The boundary's reflection asymmetry is uniformly smaller than `log 2` at every aperture. -/
theorem abs_ccmGammaPolarBoundary_sub_swap_lt {R L : ℝ} (hR : 0<R) (hL : 0<L) :
    |ccmGammaPolarBoundary R L-ccmGammaPolarBoundary L R| < Real.log 2 := by
  have hlog (t : ℝ) (ht : 0<t) : 0<Real.log (1+Real.exp (-t)) ∧
      Real.log (1+Real.exp (-t))<Real.log 2 := by
    constructor
    · apply Real.log_pos
      linarith [Real.exp_pos (-t)]
    · apply Real.log_lt_log (by positivity)
      have := Real.exp_lt_one_iff.mpr (show -t<0 by linarith)
      linarith
  rw [ccmGammaPolarBoundary_sub_swap hR hL,abs_lt]
  have h1 := hlog R hR
  have h2 := hlog L hL
  constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]

end RHTower
