import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEpsteinQuadrants
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Height inversion for the actual Poisson-defined Epstein field extends
from its lattice series by clearing its two source poles. The entire
reciprocal Gamma factor keeps the continuation independent of lattice sums. -/

open Complex Set Filter Topology
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerEpsteinQuadrants
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinReciprocity

private def normalizer (w : ℂ) : ℂ :=
  (Real.pi : ℂ)^(w/2)/2*(Complex.Gamma (w/2))⁻¹

private theorem differentiable_normalizer : Differentiable ℂ normalizer := by
  have hn : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp : Differentiable ℂ (fun w : ℂ => (Real.pi : ℂ)^(w/2)) := by
    simp only [Complex.cpow_def_of_ne_zero hn]
    fun_prop
  exact (hp.div_const 2).mul
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const 2))

private theorem field_eq {a : ℝ} (ha : 0 < a) (w : ℂ) :
    epsteinField w a=normalizer w*epsteinLambda a ha (w/2) := by
  rw [epsteinField,dif_pos ha,normalizer]
  simp only [div_eq_mul_inv,mul_inv]
  ring

private def clearedField (a : ℝ) (ha : 0 < a) (w : ℂ) : ℂ :=
  normalizer w*(w*(w-2)*(rectFEPair a ha).Λ₀ (w/2)-2*(w-2)+2*w/(a : ℂ))

private theorem differentiable_clearedField {a : ℝ} (ha : 0 < a) :
    Differentiable ℂ (clearedField a ha) := by
  have hL := (rectFEPair a ha).differentiable_Λ₀.comp
    (differentiable_id.div_const (2 : ℂ))
  unfold clearedField
  apply differentiable_normalizer.mul
  exact (((differentiable_id.mul (differentiable_id.sub_const 2)).mul hL).sub
    ((differentiable_const (2 : ℂ)).mul (differentiable_id.sub_const 2))).add
      (((differentiable_const (2 : ℂ)).mul differentiable_id).div_const (a : ℂ))

private theorem clearedField_eq {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw0 : w ≠ 0) (hw2 : w ≠ 2) :
    clearedField a ha w=w*(w-2)*epsteinField w a := by
  have hhalf : 1-w/2 ≠ 0 := by
    intro h
    apply hw2
    linear_combination -2*h
  have hL : epsteinLambda a ha (w/2)=
      (rectFEPair a ha).Λ₀ (w/2)-1/(w/2)-(1/(a : ℂ))/(1-w/2) := by
    rw [epsteinLambda,WeakFEPair.Λ]
    change _-(1/(w/2))*1-(((1/a : ℝ) : ℂ)/(1-w/2))*1=_
    simp only [mul_one,Complex.ofReal_div,Complex.ofReal_one]
  have hc : w*(w-2)*(rectFEPair a ha).Λ₀ (w/2)-2*(w-2)+2*w/(a : ℂ)=
      w*(w-2)*epsteinLambda a ha (w/2) := by
    rw [hL]
    field_simp [hw0,hhalf,Complex.ofReal_ne_zero.mpr ha.ne']
    ring
  rw [clearedField,hc,field_eq ha]
  ring

private theorem square_power {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ((a^2 : ℝ) : ℂ)^(-w/2)=(a : ℂ)^(-w) := by
  have h := Complex.cpow_mul_ofReal_nonneg ha.le (2 : ℝ) (-w/2)
  rw [show a^(2 : ℝ)=a^2 from Real.rpow_natCast a 2] at h
  have he : ((2 : ℝ) : ℂ)*(-w/2)= -w := by push_cast; ring
  simpa only [he] using h.symm

private theorem inverse_power {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ((1/a : ℝ) : ℂ)^(-w)=(a : ℂ)^w := by
  have h := Complex.cpow_mul_ofReal_nonneg ha.le (-1 : ℝ) (-w)
  rw [Real.rpow_neg_one] at h
  have he : ((-1 : ℝ) : ℂ)*(-w)=w := by push_cast; ring
  simpa only [he,one_div] using h.symm

private theorem cone_reciprocity {a : ℝ} (ha : 0 < a) (w : ℂ) :
    quadraticCone w a=(a : ℂ)^(-w)*quadraticCone w (1/a) := by
  have he (p : ℕ × ℕ) : quadraticWeight a p=a^2*quadraticWeight (1/a) (p.2,p.1) := by
    unfold quadraticWeight
    field_simp [ha.ne']
    ring
  have ht (p : ℕ × ℕ) : (quadraticWeight a p : ℂ)^(-w/2)=
      (a : ℂ)^(-w)*(quadraticWeight (1/a) (p.2,p.1) : ℂ)^(-w/2) := by
    rw [he,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (sq_nonneg a)
      (by unfold quadraticWeight; positivity),square_power ha]
  unfold quadraticCone
  calc
    _ = ∑' p : ℕ × ℕ, (a : ℂ)^(-w)*(quadraticWeight (1/a) (p.2,p.1) : ℂ)^(-w/2) :=
      tsum_congr ht
    _ = _ := by
      rw [tsum_mul_left]
      congr 1
      exact (Equiv.prodComm ℕ ℕ).tsum_eq
        (fun p : ℕ × ℕ => (quadraticWeight (1/a) p : ℂ)^(-w/2))

/-- Height reciprocity of the actual Epstein field in its absolute lattice chamber. -/
theorem reciprocity_absolute {w : ℂ} (hw : 2 < w.re) {a : ℝ} (ha : 0 < a) :
    epsteinField w a=(a : ℂ)^(-w)*epsteinField w (1/a) := by
  have hn : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hc : (a : ℂ)^(-w)*(a : ℂ)^w=1 := by
    rw [← Complex.cpow_add _ _ hn,neg_add_cancel,Complex.cpow_zero]
  rw [epsteinField_eq hw ha,epsteinField_eq hw (one_div_pos.mpr ha),
    cone_reciprocity ha,inverse_power ha]
  linear_combination -(riemannZeta w)*hc

private def reciprocalDefect (a : ℝ) (ha : 0 < a) (w : ℂ) : ℂ :=
  clearedField a ha w-(a : ℂ)^(-w)*clearedField (1/a) (one_div_pos.mpr ha) w

private theorem differentiable_reciprocalDefect {a : ℝ} (ha : 0 < a) :
    Differentiable ℂ (reciprocalDefect a ha) := by
  have hn : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hp : Differentiable ℂ (fun w : ℂ => (a : ℂ)^(-w)) := by
    simp only [Complex.cpow_def_of_ne_zero hn]
    fun_prop
  exact (differentiable_clearedField ha).sub
    (hp.mul (differentiable_clearedField (one_div_pos.mpr ha)))

private theorem reciprocalDefect_zero {a : ℝ} (ha : 0 < a) (w : ℂ) :
    reciprocalDefect a ha w=0 := by
  have he : reciprocalDefect a ha =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {v : ℂ | 2 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {v : ℂ | 2 < v.re} by norm_num)] with v hv
    change reciprocalDefect a ha v=0
    have hv0 : v ≠ 0 := by intro h; norm_num [h] at hv
    have hv2 : v ≠ 2 := by intro h; norm_num [h] at hv
    rw [reciprocalDefect,clearedField_eq ha hv0 hv2,
      clearedField_eq (one_div_pos.mpr ha) hv0 hv2,reciprocity_absolute hv ha]
    ring
  have hA : AnalyticOnNhd ℂ (reciprocalDefect a ha) univ :=
    (differentiable_reciprocalDefect ha).differentiableOn.analyticOnNhd isOpen_univ
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ 3) he (mem_univ w)

/-- The actual Epstein field is holomorphic on the source half-plane away from its pole. -/
theorem differentiableAt_epsteinField {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : 0 < a) : DifferentiableAt ℂ (fun v => epsteinField v a) w := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hs0 : w/2 ≠ 0 := div_ne_zero hw0 (by norm_num)
  have hs1 : w/2 ≠ 1 := by intro h; apply hw2; linear_combination 2*h
  have hL := (differentiableAt_epsteinLambda ha hs0 hs1).comp w
    (differentiableAt_id.div_const (2 : ℂ))
  simpa only [field_eq ha,Pi.mul_apply,Function.comp_apply,id_eq] using!
    (differentiable_normalizer w).mul hL

/-- Height inversion remains exact for the independently continued Epstein field. -/
theorem reciprocity {w : ℂ} (hw : 0 < w.re) (hw2 : w ≠ 2)
    {a : ℝ} (ha : 0 < a) :
    epsteinField w a=(a : ℂ)^(-w)*epsteinField w (1/a) := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have h := reciprocalDefect_zero ha w
  rw [reciprocalDefect,clearedField_eq ha hw0 hw2,
    clearedField_eq (one_div_pos.mpr ha) hw0 hw2] at h
  apply mul_left_cancel₀ (mul_ne_zero hw0 (sub_ne_zero.mpr hw2))
  linear_combination h

#print axioms differentiable_clearedField
#print axioms reciprocity_absolute
#print axioms reciprocalDefect_zero
#print axioms differentiableAt_epsteinField
#print axioms reciprocity
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinReciprocity
