import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinContinuation
import GaloisForLFunctions.RHTower.EisensteinHeckeFactorizationAtI

/-! The actual completed Eisenstein Fourier model on the imaginary axis
is the independently continued rectangular Epstein field, with its exact
Gamma and height normalization. A gcd decomposition proves the identity
in the absolute chamber, and holomorphic continuation preserves it at
zeta zeros. Its absolutely convergent Cauchy transform is the genuine
Mayer scattering period. -/

open Complex Set Filter MeasureTheory
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerEpsteinQuadrants
open _root_.RHTower _root_.RHTower.HeckeFactorization
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEisensteinLift

/-- The positive imaginary axis in the upper half-plane. -/
def axisPoint (a : ℝ) (ha : 0 < a) : UpperHalfPlane :=
  ⟨(a : ℂ)*I,by simpa using ha⟩

private def axisCoordinate (a : ℝ) (ha : 0 < a) : D4BMUpperHalfPlaneCoordinate := ⟨0,a,ha⟩

private theorem axis_quadratic {a : ℝ} (ha : 0 < a) (p : ℤ × ℤ) :
    d4BMPoincareQuadratic (axisCoordinate a ha) p=rectForm a p.swap := by
  simp only [d4BMPoincareQuadratic,axisCoordinate,rectForm,Prod.fst_swap,Prod.snd_swap]
  ring

private def latticeTerm (a : ℝ) (ha : 0 < a) (s : ℂ)
    (p : {p : ℤ × ℤ // p ≠ (0,0)}) : ℂ :=
  (d4BMPoincareQuadratic (axisCoordinate a ha) p.1 : ℂ)^(-s)

private theorem lattice_summable {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 < s.re) :
    Summable (latticeTerm a ha s) := by
  refine Summable.of_norm_bounded (summable_d4BMPoincareQuadratic_cpow_norm
    (axisCoordinate a ha) ⟨s,hs⟩) fun p => ?_
  rw [latticeTerm,Complex.norm_cpow_eq_rpow_re_of_pos
    (d4BMPoincareQuadratic_pos _ p.1 p.2)]
  simp

private theorem quadratic_gcd {a : ℝ} (ha : 0 < a) (k : ℕ) (q : D4BMPrimitiveIntegerPair) :
    d4BMPoincareQuadratic (axisCoordinate a ha) (gcdEquiv (k,q)).1=
      (((k+1)^2 : ℕ) : ℝ)*d4BMPoincareQuadratic (axisCoordinate a ha) q.pair := by
  change (((((k : ℤ)+1)*q.pair.1 : ℤ) : ℝ)*a)^2+
    (((((k : ℤ)+1)*q.pair.1 : ℤ) : ℝ)*0+
    ((((k : ℤ)+1)*q.pair.2 : ℤ) : ℝ))^2=_
  simp only [d4BMPoincareQuadratic,axisCoordinate]
  push_cast
  ring

/-- Splitting each nonzero lattice vector by its positive gcd preserves all multiplicities. -/
private theorem lattice_sum_eq_zeta_primitive {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 < s.re) :
    (∑' p, latticeTerm a ha s p)=riemannZeta (2*s)*
      ∑' q : D4BMPrimitiveIntegerPair,
        (d4BMPoincareQuadratic (axisCoordinate a ha) q.pair : ℂ)^(-s) := by
  have hf := lattice_summable ha hs
  have hsum : Summable (latticeTerm a ha s ∘ gcdEquiv) := gcdEquiv.summable_iff.mpr hf
  have hterm (k : ℕ) (q : D4BMPrimitiveIntegerPair) :
      latticeTerm a ha s (gcdEquiv (k,q))=
        (1/((k : ℂ)+1)^(2*s))*(d4BMPoincareQuadratic (axisCoordinate a ha) q.pair : ℂ)^(-s) := by
    rw [latticeTerm,quadratic_gcd,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity)
        (d4BMPoincareQuadratic_pos _ q.pair q.pair_ne_zero).le]
    simp only [ofReal_natCast]
    rw [natCast_sq_cpow_neg]
  calc
    _ = ∑' x, (latticeTerm a ha s ∘ gcdEquiv) x := (gcdEquiv.tsum_eq _).symm
    _ = ∑' k, ∑' q, latticeTerm a ha s (gcdEquiv (k,q)) := hsum.tsum_prod
    _ = _ := by
      simp_rw [hterm,tsum_mul_left]
      rw [tsum_mul_right,← zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; linarith only [hs])]

private theorem epstein_eq_completed_lattice {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 < s.re) :
    epsteinLambda a ha s=Gammaℝ (2*s)*(∑' p, latticeTerm a ha s p) := by
  let F : ℤ × ℤ → ℂ := fun p => Gamma s*(if p=0 then 0 else 1)/
    ((Real.pi*d4BMPoincareQuadratic (axisCoordinate a ha) p : ℝ) : ℂ)^s
  have hswap := (Equiv.prodComm ℤ ℤ).hasSum_iff.mpr (hasSum_epsteinLambda ha hs)
  have hF : HasSum F (epsteinLambda a ha s) := by
    refine hswap.congr_fun (fun p => ?_)
    have hswap0 : p.swap=0 ↔ p=0 := by
      constructor
      · intro h
        have he := congrArg Prod.swap h
        simpa using he
      · intro h
        rw [h]
        rfl
    change F p=Gamma s*(if p.swap=0 then 0 else 1)/((Real.pi*rectForm a p.swap : ℝ) : ℂ)^s
    simp only [F,axis_quadratic ha,hswap0]
  have hsupp : Function.support F ⊆ {p : ℤ × ℤ | p ≠ (0,0)} := by
    intro p hp
    change p ≠ (0,0)
    intro he
    subst p
    simp [F] at hp
  have hsub : HasSum (fun p : {p : ℤ × ℤ // p ≠ (0,0)} => F p)
      (epsteinLambda a ha s) := by
    simpa only [Function.comp_def] using! (hasSum_subtype_iff_of_support_subset hsupp).mpr hF
  have hcompleted : HasSum
      (fun p : {p : ℤ × ℤ // p ≠ (0,0)} => Gammaℝ (2*s)*latticeTerm a ha s p)
      (epsteinLambda a ha s) := by
    refine hsub.congr_fun (fun p => ?_)
    dsimp only [Function.comp_apply,F]
    have hp0 : (p : ℤ × ℤ) ≠ 0 := p.2
    rw [if_neg hp0,mul_one,Gammaℝ_def,show -(2*s)/2= -s by ring,
      show 2*s/2=s by ring,latticeTerm,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (d4BMPoincareQuadratic_pos _ p.1 p.2).le]
    simp only [Complex.cpow_neg]
    ring
  rw [← hcompleted.tsum_eq,tsum_mul_left]

private theorem axis_seed {a : ℝ} (ha : 0 < a) (s : ℂ) (q : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed (axisCoordinate a ha) s q=
      (a : ℂ)^s*(d4BMPoincareQuadratic (axisCoordinate a ha) q.pair : ℂ)^(-s) := by
  have hq := d4BMPoincareQuadratic_pos (axisCoordinate a ha) q.pair q.pair_ne_zero
  rw [d4BMPoincareSeed]
  change ((a/d4BMPoincareQuadratic (axisCoordinate a ha) q.pair : ℝ) : ℂ)^s=_
  rw [div_eq_mul_inv,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_pos.mpr hq).le,Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hq.le]; exact Real.pi_ne_zero.symm),
    ← Complex.cpow_neg]

/-- The completed Poincaré model equals the rectangular Epstein series in the absolute chamber. -/
theorem eisenstein_eq_epstein_source {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 < s.re) :
    eisensteinLineModel (s-1/2) (axisPoint a ha)=
      (a : ℂ)^s/2*epsteinLambda a ha s := by
  have h := d4BM_actualCompletedPoincare_eq_canonicalCuspLeg (axisCoordinate a ha) ⟨s,hs⟩ 0
  change d4BMCompletedEisensteinHorizontalFunction (axisCoordinate a ha) ⟨s,hs⟩ 0=
    d4BMCompletedEisensteinCuspLeg .scalar (s-1/2) 0 a at h
  have he : eisensteinLineModel (s-1/2) (axisPoint a ha)=
      d4BMCompletedEisensteinCuspLeg .scalar (s-1/2) 0 a := by
    simp [eisensteinLineModel,axisPoint]
  rw [he,← h]
  change reflectedCompletedLambda (2*s)*d4BMRawEisensteinPoincareSeries (axisCoordinate a ha) ⟨s,hs⟩=_
  rw [d4BMRawEisensteinPoincareSeries]
  simp_rw [axis_seed ha s]
  rw [tsum_mul_left,epstein_eq_completed_lattice ha hs,lattice_sum_eq_zeta_primitive ha hs,
    reflectedCompletedLambda]
  ring

#print axioms eisenstein_eq_epstein_source


private theorem eisenstein_eq_epstein_line_parameter {a : ℝ} (ha : 0 < a)
    {u : ℂ} (hu : u ∈ eisensteinLineDomain) :
    eisensteinLineModel u (axisPoint a ha)=
      (a : ℂ)^(u+1/2)/2*epsteinLambda a ha (u+1/2) := by
  let F : ℂ → ℂ := fun v => eisensteinLineModel v (axisPoint a ha)
  let G : ℂ → ℂ := fun v => (a : ℂ)^(v+1/2)/2*epsteinLambda a ha (v+1/2)
  have hF : DifferentiableOn ℂ F eisensteinLineDomain := by
    refine (differentiableOn_cuspLeg 0 ha).congr (fun v _ => ?_)
    simp only [F,eisensteinLineModel,axisPoint]
    simp
  have hG : DifferentiableOn ℂ G eisensteinLineDomain := by
    intro v hv
    have h0 : v+1/2 ≠ 0 := by
      intro he
      have hi := congrArg Complex.im he
      simp at hi
      exact hv.2.ne' hi
    have h1 : v+1/2 ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp at hi
      exact hv.2.ne' hi
    have hp : DifferentiableAt ℂ (fun v : ℂ => (a : ℂ)^(v+1/2)) v :=
      (differentiableAt_id.add_const (1/2 : ℂ)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))
    have hE := (differentiableAt_epsteinLambda ha h0 h1).comp v
      (differentiableAt_id.add_const (1/2 : ℂ))
    exact ((hp.div_const 2).mul hE).differentiableWithinAt
  have heq : EqOn F G eisensteinLineDomain := by
    refine (hF.analyticOnNhd isOpen_eisensteinLineDomain).eqOn_of_preconnected_of_eventuallyEq
      (hG.analyticOnNhd isOpen_eisensteinLineDomain) isPreconnected_eisensteinLineDomain
      (z₀ := 1+I) ⟨by simp; norm_num,by simp⟩ ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1/2 : ℝ)<(1+I).re by simp; norm_num)] with v hv
    have hs : 1 < (v+1/2).re := by simp; linarith only [hv]
    have h := eisenstein_eq_epstein_source ha hs
    simpa only [add_sub_cancel_right,F,G] using h
  exact heq hu

/-- The independently continued Eisenstein Fourier model is the rectangular Epstein completion. -/
theorem eisenstein_eq_epstein {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw : 0 < w.re) (him : 0 < w.im) :
    eisensteinLineModel ((w-1)/2) (axisPoint a ha)=
      (a : ℂ)^(w/2)/2*epsteinLambda a ha (w/2) := by
  have hu : (w-1)/2 ∈ eisensteinLineDomain := by
    constructor <;> simp <;> linarith only [hw,him]
  have h := eisenstein_eq_epstein_line_parameter ha hu
  simpa only [show (w-1)/2+1/2=w/2 by ring] using h

/-- The height restriction of the actual completed Eisenstein field, with archimedean
and height normalizations removed; zero outside positive heights. -/
def eisensteinField (w : ℂ) (a : ℝ) : ℂ :=
  if ha : 0 < a then
    (a : ℂ)^(-w/2)/Gammaℝ w*eisensteinLineModel ((w-1)/2) (axisPoint a ha)
  else 0

/-- Equality with the independently Poisson-defined field holds even at zeta zeros. -/
theorem eisensteinField_eq_epsteinField {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im) :
    eisensteinField w=epsteinField w := by
  funext a
  by_cases ha : 0 < a
  · have hA : (a : ℂ)^(w/2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))
    have hP : (Real.pi : ℂ)^(w/2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hG : Gamma (w/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith only [hw])
    rw [eisensteinField,dif_pos ha,eisenstein_eq_epstein ha hw him,
      epsteinField,dif_pos ha,Gammaℝ_def,show -w/2= -(w/2) by ring]
    simp only [Complex.cpow_neg]
    field_simp
  · simp only [eisensteinField,epsteinField,dif_neg ha]

#print axioms eisenstein_eq_epstein
#print axioms eisensteinField_eq_epsteinField


/-- The actual Eisenstein height field has an absolutely convergent Cauchy transform. -/
theorem cauchyKernel_eisenstein_integrable {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => MayerQuadraticCone.cauchyKernel w t*eisensteinField w (a/t)/(t : ℂ))
      (Ioi 0) := by
  have hw2 : w ≠ 2 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact him.ne' hi
  rw [eisensteinField_eq_epsteinField hw him]
  exact MayerEpsteinContinuation.cauchyKernel_epstein_integrable hw hw2 ha

/-- The independently defined geometric Eisenstein field maps to the actual Mayer period. -/
theorem cauchyKernel_eisenstein_period {w : ℂ} (hw : 0 < w.re) (him : 0 < w.im)
    {a : ℝ} (ha : a ∈ MayerScatteringPeriod.periodSegment) :
    _root_.RHTower.positiveMellinConvolution (MayerQuadraticCone.cauchyKernel w) (eisensteinField w) a=
      MayerScatteringPeriod.periodValue w a := by
  have hw2 : w ≠ 2 := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact him.ne' hi
  rw [eisensteinField_eq_epsteinField hw him]
  exact MayerEpsteinContinuation.cauchyKernel_epstein_period hw hw2 ha

#print axioms cauchyKernel_eisenstein_integrable
#print axioms cauchyKernel_eisenstein_period

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEisensteinLift
