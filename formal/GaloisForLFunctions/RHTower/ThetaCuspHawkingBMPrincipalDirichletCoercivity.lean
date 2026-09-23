import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadialDirichletGraph
import GaloisForLFunctions.HTGeometry.L2SpatialReflectionMultipliers
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import GaloisForLFunctions.HTGeometry.CoerciveOperatorInverse
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalData
/-! Exact hyperbolic factorization on the original radial Dirichlet graph. -/
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace RHTower.D4BMJointWave
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem tanh_continuous : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun x => (_root_.HTGeometry.hasDerivAt_tanh x).continuousAt)

private theorem tanh_norm_le (x : ℝ) : ‖(Real.tanh x:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_le]
  have h := _root_.HTGeometry.one_sub_tanh_sq x
  have hp : 0 ≤ 1 / Real.cosh x^(2 : ℕ) := by positivity
  constructor <;> nlinarith [sq_nonneg (Real.tanh x+1),sq_nonneg (Real.tanh x-1)]

private theorem sech_continuous : Continuous (fun x : ℝ => (((Real.cosh x)⁻¹:ℝ):ℂ)) :=
  Complex.continuous_ofReal.comp (Real.continuous_cosh.inv₀ (fun x => ne_of_gt (Real.cosh_pos x)))

private theorem sech_norm_le (x : ℝ) : ‖(((Real.cosh x)⁻¹:ℝ):ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (Real.cosh_pos x))]
  exact inv_le_one_of_one_le₀ (Real.one_le_cosh x)

/-- Multiplication by the original hyperbolic tangent in the radial measure. -/
def radialTanh : RadialSpace →L[ℂ] RadialSpace :=
  lpBoundedMulCLM (Complex.continuous_ofReal.comp tanh_continuous).measurable
    zero_le_one tanh_norm_le

/-- Multiplication by the original square root of the radial angular weight. -/
def radialSech : RadialSpace →L[ℂ] RadialSpace :=
  lpBoundedMulCLM sech_continuous.measurable zero_le_one sech_norm_le

private theorem tanh_ae (v : RadialSpace) : radialTanh v =ᵐ[radialMeasure]
    fun x => (Real.tanh x:ℂ)*v x := lpBoundedMulCLM_coeFn _ _ _ v

private theorem sech_ae (v : RadialSpace) : radialSech v =ᵐ[radialMeasure]
    fun x => (((Real.cosh x)⁻¹:ℝ):ℂ)*v x := lpBoundedMulCLM_coeFn _ _ _ v

private theorem hyperbolic_partition (x : ℝ) :
    (Real.tanh x:ℂ)^(2 : ℕ)+(((Real.cosh x)⁻¹:ℝ):ℂ)^(2 : ℕ)=1 := by
  have h := _root_.HTGeometry.one_sub_tanh_sq x
  have hr : Real.tanh x^(2 : ℕ)+((Real.cosh x)⁻¹)^(2 : ℕ)=1 := by
    rw [inv_pow,← one_div] 
    linarith
  exact_mod_cast hr

private theorem multiplier_partition (v : RadialSpace) :
    ‖radialTanh v‖^(2 : ℕ)+‖radialSech v‖^(2 : ℕ)=‖v‖^(2 : ℕ) := by
  have h : inner ℂ (radialTanh v) (radialTanh v)+inner ℂ (radialSech v) (radialSech v)=inner ℂ v v := by
    rw [L2.inner_def,L2.inner_def,L2.inner_def,
      ← integral_add (L2.integrable_inner (𝕜 := ℂ) (radialTanh v) (radialTanh v))
        (L2.integrable_inner (𝕜 := ℂ) (radialSech v) (radialSech v))]
    apply integral_congr_ae
    filter_upwards [tanh_ae v,sech_ae v] with x ht hs
    rw [ht,hs]
    simp only [RCLike.inner_apply,map_mul,Complex.conj_ofReal]
    linear_combination (conj (v x)*v x)*(hyperbolic_partition x)
  have hr := congrArg Complex.re h
  simpa only [Complex.add_re,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow,Complex.ofReal_re] using hr

private def boundaryForm (u : RadialDerivativeSpace) : RadialDerivativeSpace →L[ℂ] ℂ :=
  (innerSL ℂ (u 1)).comp (radialTanh.comp (PiLp.proj 2 (fun _ : Fin 2 => RadialSpace) 0))+
  (innerSL ℂ (radialTanh (u 0))).comp (PiLp.proj 2 (fun _ : Fin 2 => RadialSpace) 1)+
  (innerSL ℂ (radialSech (u 0))).comp (radialSech.comp (PiLp.proj 2 (fun _ : Fin 2 => RadialSpace) 0))

private theorem boundaryForm_apply (u v : RadialDerivativeSpace) :
    boundaryForm u v=inner ℂ (u 1) (radialTanh (v 0))+
      inner ℂ (radialTanh (u 0)) (v 1)+inner ℂ (radialSech (u 0)) (radialSech (v 0)) := rfl

private theorem boundaryForm_conj (u v : RadialDerivativeSpace) :
    conj (boundaryForm u v)=boundaryForm v u := by
  simp only [boundaryForm_apply,map_add,inner_conj_symm]
  ring

private theorem core_boundary_zero (f g : RadialCore) :
    boundaryForm (radialDirichletGraph f) (radialDirichletGraph g)=0 := by
  let T : ℝ → ℂ := fun x => (Real.tanh x:ℂ)
  let K : ℝ → ℂ := fun x => (((Real.cosh x)⁻¹:ℝ):ℂ)
  let P : ℝ → ℂ := fun x => T x*conj (f.field x)*g.field x
  let DP : ℝ → ℂ := fun x =>
    conj (deriv f.field x)*(T x*g.field x)+conj (T x*f.field x)*deriv g.field x+
      conj (K x*f.field x)*(K x*g.field x)
  have hfD (x : ℝ) : HasDerivAt f.field (deriv f.field x) x := (f.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hgD (x : ℝ) : HasDerivAt g.field (deriv g.field x) x := (g.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hTD (x : ℝ) : HasDerivAt T (K x^(2 : ℕ)) x := by
    have h := (_root_.HTGeometry.hasDerivAt_tanh x).ofReal_comp
    convert! h using 1
    simp only [K,Complex.ofReal_pow,Complex.ofReal_inv,inv_pow,one_div]
  have hd (x : ℝ) : HasDerivAt P (DP x) x := by
    have h := ((hTD x).mul (hfD x).star).mul (hgD x)
    convert! h using 1
    simp only [DP,T,K,Pi.mul_apply,Complex.star_def,map_mul,Complex.conj_ofReal]
    ring
  have hTc : Continuous T := Complex.continuous_ofReal.comp tanh_continuous
  have hKc : Continuous K := sech_continuous
  have hPc : Continuous P := (hTc.mul f.smooth.continuous.star).mul g.smooth.continuous
  have hDPc : Continuous DP := by
    dsimp only [DP]
    exact (((f.smooth.continuous_deriv (by simp)).star.mul (hTc.mul g.smooth.continuous)).add
      ((hTc.mul f.smooth.continuous).star.mul (g.smooth.continuous_deriv (by simp)))).add
      ((hKc.mul f.smooth.continuous).star.mul (hKc.mul g.smooth.continuous))
  have hPcpt : HasCompactSupport P := g.compact.mul_left
  have hDPcpt : HasCompactSupport DP := by
    have ht : HasCompactSupport (fun x => T x*g.field x) := g.compact.mul_left
    have hk : HasCompactSupport (fun x => K x*g.field x) := g.compact.mul_left
    have h1 : HasCompactSupport (fun x => conj (deriv f.field x)*(T x*g.field x)) := ht.mul_left
    have h2 : HasCompactSupport (fun x => conj (T x*f.field x)*deriv g.field x) := g.compact.deriv.mul_left
    have h3 : HasCompactSupport (fun x => conj (K x*f.field x)*(K x*g.field x)) := hk.mul_left
    exact (h1.add h2).add h3
  have hzero : (∫ x, DP x)=0 := integral_eq_zero_of_hasDerivAt_of_integrable hd
    (hDPc.integrable_of_hasCompactSupport hDPcpt) (hPc.integrable_of_hasCompactSupport hPcpt)
  have hrestrict : (∫ x, DP x ∂radialMeasure)=∫ x, DP x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hg : g.field x=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (g.support h))
    have hgd : deriv g.field x=0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (g.support (tsupport_deriv_subset h)))
    simp only [DP,hg,hgd,mul_zero,add_zero]
  rw [boundaryForm_apply]
  change inner ℂ (radialDerivative f) (radialTanh (radialValue g))+
    inner ℂ (radialTanh (radialValue f)) (radialDerivative g)+
    inner ℂ (radialSech (radialValue f)) (radialSech (radialValue g))=0
  rw [L2.inner_def,L2.inner_def,L2.inner_def,
    ← integral_add (L2.integrable_inner (𝕜 := ℂ) (radialDerivative f) (radialTanh (radialValue g)))
      (L2.integrable_inner (𝕜 := ℂ) (radialTanh (radialValue f)) (radialDerivative g)),
    ← integral_add (f := fun x : ℝ => inner ℂ (radialDerivative f x) (radialTanh (radialValue g) x)+
      inner ℂ (radialTanh (radialValue f) x) (radialDerivative g x)) ((L2.integrable_inner (𝕜 := ℂ) (radialDerivative f) (radialTanh (radialValue g))).add
      (L2.integrable_inner (𝕜 := ℂ) (radialTanh (radialValue f)) (radialDerivative g)))
      (L2.integrable_inner (𝕜 := ℂ) (radialSech (radialValue f)) (radialSech (radialValue g)))]
  have he : (fun x => inner ℂ (radialDerivative f x) (radialTanh (radialValue g) x)+
      inner ℂ (radialTanh (radialValue f) x) (radialDerivative g x)+
      inner ℂ (radialSech (radialValue f) x) (radialSech (radialValue g) x)) =ᵐ[radialMeasure] DP := by
    filter_upwards [tanh_ae (radialValue f),tanh_ae (radialValue g),
      sech_ae (radialValue f),sech_ae (radialValue g),
      (f.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := radialMeasure) f.compact).coeFn_toLp,
      (g.smooth.continuous.memLp_of_hasCompactSupport (p := 2) (μ := radialMeasure) g.compact).coeFn_toLp,
      ((f.smooth.continuous_deriv (by simp)).memLp_of_hasCompactSupport
        (p := 2) (μ := radialMeasure) f.compact.deriv).coeFn_toLp,
      ((g.smooth.continuous_deriv (by simp)).memLp_of_hasCompactSupport
        (p := 2) (μ := radialMeasure) g.compact.deriv).coeFn_toLp] with x htf htg hkf hkg hf hg hdf hdg
    change radialValue f x = f.field x at hf
    change radialValue g x = g.field x at hg
    change radialDerivative f x = deriv f.field x at hdf
    change radialDerivative g x = deriv g.field x at hdg
    rw [htf,htg,hkf,hkg,hf,hg,hdf,hdg]
    simp only [DP,T,K,RCLike.inner_apply]
    ring
  rw [integral_congr_ae he,hrestrict,hzero]

private theorem boundaryForm_zero (u v : radialDirichletDomain) : boundaryForm u v=0 := by
  have hcore (f : RadialCore) (v : radialDirichletDomain) :
      boundaryForm (radialDirichletGraph f) v=0 := by
    have hs : radialDirichletDomain ≤ (boundaryForm (radialDirichletGraph f)).ker := by
      apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro _ ⟨g,rfl⟩
        exact core_boundary_zero f g
      · exact (boundaryForm (radialDirichletGraph f)).isClosed_ker
    exact hs v.property
  have hs : radialDirichletDomain ≤ (boundaryForm (u : RadialDerivativeSpace)).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨f,rfl⟩
      change boundaryForm (u : RadialDerivativeSpace) (radialDirichletGraph f)=0
      rw [← boundaryForm_conj, hcore, map_zero]
    · exact (boundaryForm (u : RadialDerivativeSpace)).isClosed_ker
  exact hs v.property

/-- Exact square completion holds on the original completed Dirichlet graph, retaining its endpoint realization. -/
theorem radialDirichlet_hyperbolic_factorization (u : radialDirichletDomain) :
    ‖(u : RadialDerivativeSpace) 1+radialTanh ((u : RadialDerivativeSpace) 0)‖^(2 : ℕ)+
      2*‖radialSech ((u : RadialDerivativeSpace) 0)‖^(2 : ℕ) =
    ‖(u : RadialDerivativeSpace) 1‖^(2 : ℕ)+‖(u : RadialDerivativeSpace) 0‖^(2 : ℕ) := by
  have hb := congrArg Complex.re (boundaryForm_zero u u)
  simp only [boundaryForm_apply,Complex.add_re,Complex.zero_re,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow,Complex.ofReal_re] at hb
  have hp := multiplier_partition ((u : RadialDerivativeSpace) 0)
  have he := congrArg Complex.re (inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
    ((u : RadialDerivativeSpace) 1+radialTanh ((u : RadialDerivativeSpace) 0)))
  rw [inner_add_left,inner_add_right,inner_add_right] at he
  simp only [Complex.add_re,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow,Complex.ofReal_re] at he
  linarith

private theorem rotated_scalar_bound (a b c d eta N H D : ℝ)
    (hN : 0 ≤ N) (hH : 0 ≤ H) (hHN : H ≤ N)
    (hfac : 2*H ≤ D+N) (hc : c ≤ 2) (hd : d^(2 : ℕ) ≤ 9) :
    (a-3/2)*(D+(a^(2 : ℕ)+b^(2 : ℕ)+2)*N+(eta^(2 : ℕ)-c)*H) ≤
      a*D+a*(a^(2 : ℕ)+b^(2 : ℕ))*N+(a*(eta^(2 : ℕ)-c)-b*d*eta)*H := by
  have hcross : b*d*eta ≤ (3/2)*(b^(2 : ℕ)+eta^(2 : ℕ)) := by
    nlinarith [sq_nonneg (eta-b*d/3),mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg b)]
  have ha : 2*a ≤ (3/2)*(a^(2 : ℕ)+1) := by nlinarith [sq_nonneg (a-2/3)]
  have h1 := mul_le_mul_of_nonneg_right ha hN
  have h2 := mul_le_mul_of_nonneg_right hcross hH
  have h3 := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hHN)
  have h4 := mul_nonneg (sub_nonneg.mpr hc) hH
  nlinarith

/-- The value projection from the original completed radial Dirichlet graph. -/
def principalDirichletValue : radialDirichletDomain →L[ℂ] RadialSpace :=
  (PiLp.proj 2 (fun _ : Fin 2 => RadialSpace) 0).comp radialDirichletDomain.subtypeL

def principalDirichletSech : radialDirichletDomain →L[ℂ] RadialSpace :=
  radialSech.comp principalDirichletValue

private theorem domain_inner (u v : radialDirichletDomain) :
    inner ℂ u v = inner ℂ ((u : RadialDerivativeSpace) 0) ((v : RadialDerivativeSpace) 0)+
      inner ℂ ((u : RadialDerivativeSpace) 1) ((v : RadialDerivativeSpace) 1) := by
  change inner ℂ (u : RadialDerivativeSpace) (v : RadialDerivativeSpace)=_
  simp only [PiLp.inner_apply,Fin.sum_univ_two]

private theorem domain_norm (u : radialDirichletDomain) :
    ‖u‖^(2 : ℕ)=‖(u : RadialDerivativeSpace) 0‖^(2 : ℕ)+‖(u : RadialDerivativeSpace) 1‖^(2 : ℕ) := by
  have h := congrArg Complex.re (domain_inner u u)
  simpa only [Complex.add_re,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow,Complex.ofReal_re] using h

/-- The original radial form with the complex principal potential, before Laplace rotation. -/
def principalDirichletFormOperator (m w : ℂ) : radialDirichletDomain →L[ℂ] radialDirichletDomain :=
  ContinuousLinearMap.id ℂ radialDirichletDomain +
    (w^(2 : ℕ)-1) • principalDirichletValue.adjoint.comp principalDirichletValue -
    (m*(m-1)) • principalDirichletSech.adjoint.comp principalDirichletSech

/-- Rotation retains the principal parameter and the independent frequency. -/
def principalDirichletRotatedOperator (m w : ℂ) : radialDirichletDomain →L[ℂ] radialDirichletDomain :=
  conj w • principalDirichletFormOperator m w

/-- Exact original derivative and hyperbolic-potential terms on the Dirichlet realization. -/
theorem principalDirichletFormOperator_inner (m w : ℂ) (u v : radialDirichletDomain) :
    inner ℂ u (principalDirichletFormOperator m w v) =
      inner ℂ ((u : RadialDerivativeSpace) 1) ((v : RadialDerivativeSpace) 1)+
      w^(2 : ℕ)*inner ℂ (principalDirichletValue u) (principalDirichletValue v)-
      m*(m-1)*inner ℂ (principalDirichletSech u) (principalDirichletSech v) := by
  simp only [principalDirichletFormOperator,sub_apply,
    add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,inner_sub_right,inner_add_right,inner_smul_right,
    principalDirichletValue.adjoint_inner_right,principalDirichletSech.adjoint_inner_right,
    domain_inner]
  have hJ (z : radialDirichletDomain) : principalDirichletValue z=(z : RadialDerivativeSpace) 0 := rfl
  rw [hJ u,hJ v]
  ring

private theorem rotated_energy_exact (m w : ℂ) (u : radialDirichletDomain) :
    (inner ℂ (principalDirichletRotatedOperator m w u) u).re =
      w.re*‖(u : RadialDerivativeSpace) 1‖^(2 : ℕ)+
      w.re*(w.re^(2 : ℕ)+w.im^(2 : ℕ))*‖principalDirichletValue u‖^(2 : ℕ)+
      (w.re*(m.im^(2 : ℕ)-m.re*(m.re-1))-w.im*(2*m.re-1)*m.im)*‖principalDirichletSech u‖^(2 : ℕ) := by
  change (inner ℂ (conj w • principalDirichletFormOperator m w u) u).re = _
  rw [inner_smul_left]
  have he : inner ℂ (principalDirichletFormOperator m w u) u =
      conj (inner ℂ u (principalDirichletFormOperator m w u)) := (inner_conj_symm _ _).symm
  rw [he,principalDirichletFormOperator_inner]
  simp only [inner_self_eq_norm_sq_to_K,starRingEnd_self_apply]
  simp [pow_two,Complex.mul_re,Complex.mul_im]
  ring

private def principalDirichletEnergy (m w : ℂ) (u : radialDirichletDomain) : ℝ :=
  ‖(u : RadialDerivativeSpace) 1‖^(2 : ℕ)+(w.re^(2 : ℕ)+w.im^(2 : ℕ)+2)*‖principalDirichletValue u‖^(2 : ℕ)+
    (m.im^(2 : ℕ)-m.re*(m.re-1))*‖principalDirichletSech u‖^(2 : ℕ)

private theorem sech_square_le (u : radialDirichletDomain) :
    ‖principalDirichletSech u‖^(2 : ℕ) ≤ ‖principalDirichletValue u‖^(2 : ℕ) := by
  have h := multiplier_partition (principalDirichletValue u)
  change ‖radialSech (principalDirichletValue u)‖^(2 : ℕ) ≤ _
  nlinarith [sq_nonneg ‖radialTanh (principalDirichletValue u)‖]

private theorem principal_energy_lower (m w : ℂ) (hm0 : 0 ≤ m.re) (hm2 : m.re ≤ 2)
    (u : radialDirichletDomain) :
    ‖(u : RadialDerivativeSpace) 1‖^(2 : ℕ)+Complex.normSq w*‖principalDirichletValue u‖^(2 : ℕ) ≤
      principalDirichletEnergy m w u := by
  have hc : m.re*(m.re-1) ≤ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ m.re+1 by linarith) (sub_nonneg.mpr hm2)]
  have h1 := mul_nonneg (sq_nonneg m.im) (sq_nonneg ‖principalDirichletSech u‖)
  have h2 := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg ‖principalDirichletSech u‖)
  have h3 := sech_square_le u
  unfold principalDirichletEnergy
  rw [Complex.normSq_apply]
  nlinarith

private theorem principal_rotated_energy (m w : ℂ) (hm0 : 0 ≤ m.re) (hm2 : m.re ≤ 2)
    (u : radialDirichletDomain) :
    (w.re-3/2)*principalDirichletEnergy m w u ≤
      (inner ℂ (principalDirichletRotatedOperator m w u) u).re := by
  have hc : m.re*(m.re-1) ≤ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ m.re+1 by linarith) (sub_nonneg.mpr hm2)]
  have hd : (2*m.re-1)^(2 : ℕ) ≤ 9 := by nlinarith [hc]
  have hf := radialDirichlet_hyperbolic_factorization u
  have hfac : 2*‖principalDirichletSech u‖^(2 : ℕ) ≤
      ‖(u : RadialDerivativeSpace) 1‖^(2 : ℕ)+‖principalDirichletValue u‖^(2 : ℕ) := by
    change 2*‖radialSech ((u : RadialDerivativeSpace) 0)‖^(2 : ℕ) ≤ _
    change _ ≤ ‖(u : RadialDerivativeSpace) 1‖^(2 : ℕ)+‖(u : RadialDerivativeSpace) 0‖^(2 : ℕ)
    nlinarith [sq_nonneg ‖(u : RadialDerivativeSpace) 1+radialTanh ((u : RadialDerivativeSpace) 0)‖]
  rw [rotated_energy_exact]
  exact rotated_scalar_bound w.re w.im (m.re*(m.re-1)) (2*m.re-1) m.im
    _ _ _ (sq_nonneg _) (sq_nonneg _) (sech_square_le u) hfac hc hd

/-- Uniform principal coercivity throughout Re(w)>3/2; no restriction on Im(m). -/
theorem principalDirichletRotatedOperator_coercive (m w : ℂ)
    (hm0 : 0 ≤ m.re) (hm2 : m.re ≤ 2) (hw : 3/2 < w.re) (u : radialDirichletDomain) :
    (w.re-3/2)*‖u‖^(2 : ℕ) ≤ (inner ℂ (principalDirichletRotatedOperator m w u) u).re := by
  have hn : 1 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg w.im]
  have he := principal_energy_lower m w hm0 hm2 u
  have hdom : ‖u‖^(2 : ℕ) ≤ principalDirichletEnergy m w u := by
    rw [domain_norm]
    change ‖principalDirichletValue u‖^(2 : ℕ)+‖(u : RadialDerivativeSpace) 1‖^(2 : ℕ) ≤ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg ‖principalDirichletValue u‖)]
  exact (mul_le_mul_of_nonneg_left hdom (by linarith)).trans
    (principal_rotated_energy m w hm0 hm2 u)

/-- The inverse is constructed on the original completed Dirichlet domain in the common Green half-plane. -/
theorem principalDirichletRotatedOperator_inverse (m w : ℂ)
    (hm0 : 0 ≤ m.re) (hm2 : m.re ≤ 2) (hw : 3/2 < w.re) :
    ∃ S : radialDirichletDomain →L[ℂ] radialDirichletDomain,
      (∀ v, principalDirichletRotatedOperator m w (S v)=v) ∧
      (∀ u, S (principalDirichletRotatedOperator m w u)=u) ∧
      ∀ v, ‖S v‖ ≤ (w.re-3/2)⁻¹*‖v‖ :=
  exists_inverse_of_coercive (by linarith) (principalDirichletRotatedOperator_coercive m w hm0 hm2 hw)

/-- Actual forcing equation on the original radial Dirichlet graph. -/
def PrincipalDirichletFormSolution (m w : ℂ) (F : RadialSpace) (u : radialDirichletDomain) : Prop :=
  principalDirichletFormOperator m w u = principalDirichletValue.adjoint F

/-- Unique forced principal response on the entire common Green half-plane. -/
theorem exists_unique_principalDirichletFormSolution (m w : ℂ)
    (hm0 : 0 ≤ m.re) (hm2 : m.re ≤ 2) (hw : 3/2 < w.re) (F : RadialSpace) :
    ∃! u : radialDirichletDomain, PrincipalDirichletFormSolution m w F u := by
  obtain ⟨S,hS,hleft,_⟩ := principalDirichletRotatedOperator_inverse m w hm0 hm2 hw
  have hw0 : conj w ≠ 0 := by
    simpa using (show w ≠ 0 from fun h => by simp [h] at hw; linarith)
  let u := S (conj w • principalDirichletValue.adjoint F)
  have hu : PrincipalDirichletFormSolution m w F u := by
    apply smul_right_injective radialDirichletDomain hw0
    exact hS (conj w • principalDirichletValue.adjoint F)
  refine ⟨u,hu,?_⟩
  intro v hv
  have he : principalDirichletRotatedOperator m w v = principalDirichletRotatedOperator m w u := by
    change conj w • principalDirichletFormOperator m w v = conj w • principalDirichletFormOperator m w u
    rw [hv,hu]
  have hh := congrArg S he
  simpa only [hleft] using hh

/-- Frequency decay has a constant independent of the imaginary principal exponent. -/
theorem principalDirichletFormSolution_mass_bound (m w : ℂ)
    (hm0 : 0 ≤ m.re) (hm2 : m.re ≤ 2) (hw : 3/2 < w.re) (F : RadialSpace)
    {u : radialDirichletDomain} (hu : PrincipalDirichletFormSolution m w F u) :
    ‖principalDirichletValue u‖ ≤ ‖F‖/((w.re-3/2)*‖w‖) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw; linarith
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hc : 0 < w.re-3/2 := by linarith
  have he := principal_rotated_energy m w hm0 hm2 u
  have hlow := principal_energy_lower m w hm0 hm2 u
  have hr : principalDirichletRotatedOperator m w u = conj w • principalDirichletValue.adjoint F := by
    change conj w • principalDirichletFormOperator m w u = _
    rw [hu]
  rw [hr,inner_smul_left,principalDirichletValue.adjoint_inner_left,starRingEnd_self_apply] at he
  have hupper : (w*inner ℂ F (principalDirichletValue u)).re ≤
      ‖w‖*‖F‖*‖principalDirichletValue u‖ := by
    calc
      _ ≤ ‖w*inner ℂ F (principalDirichletValue u)‖ := Complex.re_le_norm _
      _ = ‖w‖*‖inner ℂ F (principalDirichletValue u)‖ := norm_mul _ _
      _ ≤ ‖w‖*(‖F‖*‖principalDirichletValue u‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) hwn.le
      _ = _ := by ring
  have hb : (w.re-3/2)*‖w‖^(2 : ℕ)*‖principalDirichletValue u‖^(2 : ℕ) ≤
      ‖w‖*‖F‖*‖principalDirichletValue u‖ := by
    rw [Complex.normSq_eq_norm_sq] at hlow
    have hh := mul_le_mul_of_nonneg_left hlow hc.le
    nlinarith [mul_nonneg hc.le (sq_nonneg ‖(u : RadialDerivativeSpace) 1‖)]
  rcases eq_or_lt_of_le (norm_nonneg (principalDirichletValue u)) with hz | hp
  · rw [← hz]
    positivity
  · rw [le_div_iff₀ (mul_pos hc hwn)]
    have hh : (‖principalDirichletValue u‖*((w.re-3/2)*‖w‖))*(‖w‖*‖principalDirichletValue u‖) ≤
        ‖F‖*(‖w‖*‖principalDirichletValue u‖) := by nlinarith [hb]
    exact le_of_mul_le_mul_right hh (mul_pos hwn hp)


private theorem actual_principal_strip (q : XiZeroCopy) (i : Fin 3) :
    0 ≤ (D4BMJointSource.principalExponent q i).re ∧
      (D4BMJointSource.principalExponent q i).re ≤ 2 := by
  have hx := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hx
  norm_num [xiSpectralPoint] at hx
  fin_cases i <;> norm_num [D4BMJointSource.principalExponent]
  all_goals constructor <;> linarith [hx.1,hx.2]

/-- All three actual Xi principal channels have their unique original Dirichlet response
and the uniform Green-chamber decay bound. -/
theorem actualPrincipalDirichlet_response (q : XiZeroCopy) (i : Fin 3)
    (w : ℂ) (hw : 7/4 ≤ w.re) (F : RadialSpace) :
    ∃ u : radialDirichletDomain,
      PrincipalDirichletFormSolution (D4BMJointSource.principalExponent q i) w F u ∧
      ‖principalDirichletValue u‖ ≤ 4*‖F‖/‖w‖ ∧
      ∀ v, PrincipalDirichletFormSolution (D4BMJointSource.principalExponent q i) w F v → v=u := by
  obtain ⟨hm0,hm2⟩ := actual_principal_strip q i
  have hw' : 3/2 < w.re := by linarith
  obtain ⟨u,hu,hunique⟩ := exists_unique_principalDirichletFormSolution
    (D4BMJointSource.principalExponent q i) w hm0 hm2 hw' F
  refine ⟨u,hu,?_,hunique⟩
  have hb := principalDirichletFormSolution_mass_bound
    (D4BMJointSource.principalExponent q i) w hm0 hm2 hw' F hu
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h => by simp [h] at hw; linarith)
  have hc : 0 < w.re-3/2 := by linarith
  rw [le_div_iff₀ (mul_pos hc hwn)] at hb
  rw [le_div_iff₀ hwn]
  have hh : (‖principalDirichletValue u‖*‖w‖)/4 ≤ ‖F‖ := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ w.re-3/2-1/4)
      (mul_nonneg (norm_nonneg (principalDirichletValue u)) hwn.le)]
  linarith

end
end RHTower.D4BMJointWave
