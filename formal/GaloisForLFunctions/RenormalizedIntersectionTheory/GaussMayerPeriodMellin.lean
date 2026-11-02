import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringPeriod
import GaloisForLFunctions.RHTower.Suzuki.SuzukiMellinConvolution
import GaloisForLFunctions.HTGeometry.BarnesSingleZetaContinuation

/-! The actual Mayer period's interior lattice cone has a separated Mellin
transform. Multiplicative convolution proves absolute convergence and
identifies both zeta factors before any meromorphic continuation. -/

open Complex Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPeriodMellin

/-- The interior positive-lattice part of the actual scattering period. -/
def conePeriod (w : ℂ) (a : ℝ) : ℂ := barnesDoubleZeta a 1 w (1+(a : ℂ))

private def ray (t : ℝ) : ℂ := barnesRayKernel 1 1 t

private theorem ray_convergent {u : ℂ} (hu : 1 < u.re) : MellinConvergent ray u := by
  rw [MellinConvergent,← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [ray,smul_eq_mul]
  exact (integrableOn_cpow_mul_barnesRayKernel_Ioc zero_lt_one hu).union
    (integrableOn_cpow_mul_barnesRayKernel_Ioi_one zero_lt_one zero_lt_one
      (zero_lt_one.trans hu))

private theorem ray_mellin {u : ℂ} (hu : 1 < u.re) :
    mellin ray u=Complex.Gamma u*riemannZeta u := by
  have hs : barnesSingleZeta 1 u (1 : ℂ)=riemannZeta u := by
    rw [barnesSingleZeta,zeta_eq_tsum_one_div_nat_add_one_cpow hu]
    apply tsum_congr
    intro n
    simp only [mul_one,Complex.ofReal_natCast,Complex.cpow_neg,one_div]
    congr 2
    ring
  change mellin (barnesRayKernel 1 1) u=_
  rw [← Gamma_mul_barnesSingleZeta_eq_mellin zero_lt_one zero_lt_one hu]
  simp only [Complex.ofReal_one,hs]

private def inverseRay (w : ℂ) (y : ℝ) : ℂ :=
  ((y⁻¹ : ℝ) : ℂ)^w*ray y⁻¹

private theorem inverseRay_convergent {w u : ℂ} (hu : 1 < (w-u).re) :
    MellinConvergent (inverseRay w) u := by
  have h : MellinConvergent (fun t : ℝ => (t : ℂ)^w • ray t) (-u) := by
    rw [MellinConvergent.cpow_smul,show -u+w=w-u by ring]
    exact ray_convergent hu
  have hi := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => (t : ℂ)^w • ray t) (s := u) (a := -1) (by norm_num)).mpr
    (by simpa only [Complex.ofReal_neg,Complex.ofReal_one,div_neg,div_one] using h)
  unfold inverseRay
  simpa only [Real.rpow_neg_one,smul_eq_mul] using! hi

private theorem inverseRay_mellin {w u : ℂ} (hu : 1 < (w-u).re) :
    mellin (inverseRay w) u=Complex.Gamma (w-u)*riemannZeta (w-u) := by
  have h := mellin_comp_inv (fun t : ℝ => (t : ℂ)^w • ray t) u
  rw [mellin_cpow_smul,show -u+w=w-u by ring,ray_mellin hu] at h
  exact h

private theorem ray_product (a t : ℝ) :
    ray t*ray (a*t)=barnesConeKernel a 1 (a+1) t := by
  have he : Real.exp (-((a+1)*t))=Real.exp (-t)*Real.exp (-(a*t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [ray,barnesRayKernel,barnesConeKernel,one_mul,neg_mul]
  rw [he,Complex.ofReal_mul]
  simp only [div_eq_mul_inv,mul_inv]
  ring

/-- The cone is a genuine multiplicative convolution of two ray kernels. -/
private theorem convolution_eq {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    _root_.RHTower.positiveMellinConvolution (inverseRay w) ray a=
      Complex.Gamma w*conePeriod w a := by
  let k : ℝ → ℂ := fun t => (t : ℂ)^w • (ray t*ray (a*t))
  calc
    _ = mellin (fun t => k t⁻¹) 0 := by
      unfold _root_.RHTower.positiveMellinConvolution mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      simp only [inverseRay,k,smul_eq_mul,zero_sub,Complex.cpow_neg_one,
        div_eq_mul_inv,Complex.ofReal_inv]
      ring
    _ = mellin k 0 := by rw [mellin_comp_inv,neg_zero]
    _ = mellin (fun t => ray t*ray (a*t)) w := by
      rw [mellin_cpow_smul,zero_add]
    _ = Complex.Gamma w*conePeriod w a := by
      simp_rw [ray_product]
      rw [← Gamma_mul_barnesDoubleZeta_eq_mellin ha zero_lt_one (by linarith only [ha]) hw]
      simp only [conePeriod,Complex.ofReal_add,Complex.ofReal_one,add_comm]

/-- The Mellin transform before division by the nonzero Gamma factor, with absolute convergence. -/
theorem hasMellin_gamma_cone {w u : ℂ} (hu : 1 < u.re) (hwu : 1 < (w-u).re) :
    HasMellin (fun a => Complex.Gamma w*conePeriod w a) u
      ((Complex.Gamma (w-u)*riemannZeta (w-u))*(Complex.Gamma u*riemannZeta u)) := by
  have hw : 2 < w.re := by
    simp only [Complex.sub_re] at hwu
    linarith only [hu,hwu]
  have hf : Measurable (inverseRay w) := by unfold inverseRay ray barnesRayKernel; fun_prop
  have hg : Measurable ray := by unfold ray barnesRayKernel; fun_prop
  have h := _root_.RHTower.hasMellin_positiveMellinConvolution hf hg
    (inverseRay_convergent hwu) (ray_convergent hu)
  rw [inverseRay_mellin hwu,ray_mellin hu] at h
  constructor
  · exact h.1.congr_fun (fun a ha => congrArg
      (fun z : ℂ => (a : ℂ)^(u-1) • z) (convolution_eq hw ha)) measurableSet_Ioi
  · rw [← h.2]
    exact setIntegral_congr_fun measurableSet_Ioi (fun a ha => congrArg
      (fun z : ℂ => (a : ℂ)^(u-1) • z) (convolution_eq hw ha).symm)

/-- The exact Mellin value of the actual interior cone. -/
theorem mellin_cone {w u : ℂ} (hu : 1 < u.re) (hwu : 1 < (w-u).re) :
    mellin (conePeriod w) u=
      Complex.Gamma u*Complex.Gamma (w-u)*riemannZeta u*riemannZeta (w-u)/Complex.Gamma w := by
  have hw : 0 < w.re := by
    simp only [Complex.sub_re] at hwu
    linarith only [hu,hwu]
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero (fun n hn => by
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re,Complex.natCast_re] at hr
    linarith only [hr,hw,Nat.cast_nonneg (α := ℝ) n])
  have h := (hasMellin_gamma_cone hu hwu).2
  change mellin (fun a => Complex.Gamma w • conePeriod w a) u=_ at h
  rw [mellin_const_smul,smul_eq_mul] at h
  apply (eq_div_iff hG).mpr
  linear_combination h

/-- The cone integral is absolutely convergent on the indicated two-variable chamber. -/
theorem mellinConvergent_cone {w u : ℂ} (hu : 1 < u.re) (hwu : 1 < (w-u).re) :
    MellinConvergent (conePeriod w) u := by
  have hw : 0 < w.re := by
    simp only [Complex.sub_re] at hwu
    linarith only [hu,hwu]
  have hG : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero (fun n hn => by
    have hr := congrArg Complex.re hn
    simp only [Complex.neg_re,Complex.natCast_re] at hr
    linarith only [hr,hw,Nat.cast_nonneg (α := ℝ) n])
  have h := (hasMellin_gamma_cone hu hwu).1.const_smul (Complex.Gamma w)⁻¹
  simpa only [smul_eq_mul,inv_mul_cancel_left₀ hG] using h

/-- On the actual disc segment, the cone is exactly the period with its two axes removed. -/
theorem period_axes_decomposition {w : ℂ} (hw : 2 < w.re) {a : ℝ}
    (ha : a ∈ MayerScatteringPeriod.periodSegment) :
    MayerScatteringPeriod.periodValue w a=
      riemannZeta w*(1+(a : ℂ)^(-w))+2*conePeriod w a := by
  rw [MayerScatteringPeriod.periodValue_barnes hw ha,
    MayerScatteringChamber.barnes_boundary_pair (by linarith only [ha.1]) hw]
  rfl

#print axioms convolution_eq
#print axioms hasMellin_gamma_cone
#print axioms mellin_cone
#print axioms mellinConvergent_cone
#print axioms period_axes_decomposition
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPeriodMellin
