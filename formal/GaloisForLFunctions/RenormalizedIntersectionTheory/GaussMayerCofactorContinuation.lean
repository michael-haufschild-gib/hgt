import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoprimeCofactor
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-! Clearing the two scalar poles continues the actual Mayer cofactor identity
through the whole source half-plane. No continuation of the Green vector is needed. -/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerParameter MayerCoprimeCofactor
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCofactorContinuation

/-- The actual determinant with its simple source pole removed. -/
def clearedDeterminant (w : ℂ) : ℂ :=
  (w-1)*MayerPole.regularPart w 1+_root_.RHTower.zetaResidueUnit w*MayerPole.polePart w 1

/-- The cofactor relation after removing both possible zeta poles. -/
def clearedIdentity (w : ℂ) : ℂ :=
  2*_root_.RHTower.zetaResidueUnit (w-1)*clearedDeterminant w+
    (w-2)*_root_.RHTower.zetaResidueUnit w*MayerPole.polePart w 1

private theorem residue_differentiable : Differentiable ℂ _root_.RHTower.zetaResidueUnit :=
  fun w => (_root_.RHTower.analyticAt_zetaResidueUnit w).differentiableAt

private theorem differentiableOn_clearedDeterminant :
    DifferentiableOn ℂ clearedDeterminant {w : ℂ | 0 < w.re} := by
  exact ((differentiableOn_id.sub_const 1).mul (MayerPole.differentiableOn_regularPart 1)).add
    (residue_differentiable.differentiableOn.mul (MayerPole.differentiableOn_polePart 1))

/-- Pole clearing is holomorphic even at source parameters one and two. -/
theorem analyticOn_clearedIdentity : AnalyticOnNhd ℂ clearedIdentity {w : ℂ | 0 < w.re} := by
  have hd : DifferentiableOn ℂ clearedIdentity {w : ℂ | 0 < w.re} :=
    (((residue_differentiable.comp (differentiable_id.sub_const 1)).differentiableOn.const_mul 2).mul
      differentiableOn_clearedDeterminant).add
      (((differentiableOn_id.sub_const 2).mul residue_differentiable.differentiableOn).mul
        (MayerPole.differentiableOn_polePart 1))
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

private theorem residue_of_ne {w : ℂ} (hw : w ≠ 1) :
    _root_.RHTower.zetaResidueUnit w=(w-1)*riemannZeta w := by
  rw [_root_.RHTower.zetaResidueUnit,Function.update_of_ne hw]

private theorem clearedDeterminant_eq {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    clearedDeterminant w=(w-1)*sourceDeterminant w 1 := by
  rw [clearedDeterminant,residue_of_ne hw1,MayerPole.sourceDeterminant_decomposition hw]
  ring

private theorem clearedIdentity_eq {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hw2 : w ≠ 2) :
    clearedIdentity w=(w-1)*(w-2)*
      (2*riemannZeta (w-1)*sourceDeterminant w 1+riemannZeta w*MayerPole.polePart w 1) := by
  have hs : w-1 ≠ 1 := by
    intro he
    apply hw2
    linear_combination he
  rw [clearedIdentity,clearedDeterminant_eq hw hw1,residue_of_ne hw1,residue_of_ne hs]
  ring

private theorem clearedIdentity_zero_absolute {w : ℂ} (hw : 2 < w.re) : clearedIdentity w=0 := by
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at hw
  have hw2 : w ≠ 2 := by intro he; norm_num [he] at hw
  rw [clearedIdentity_eq (by linarith only [hw]) hw1 hw2,zeta_cofactor_identity hw,mul_zero]

/-- The source half-plane is connected by real affine segments. -/
theorem rightHalfPlane_preconnected : IsPreconnected {w : ℂ | 0 < w.re} := by
  have hc : Convex ℝ {w : ℂ | 0 < w.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq,Complex.add_re,Complex.smul_re,smul_eq_mul]
    by_cases ha0 : a=0
    · subst a
      have hb1 : b=1 := by simpa only [zero_add] using hab
      rw [hb1,zero_mul,zero_add,one_mul]
      exact hy
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hap hx) (mul_nonneg hb hy.le)
  exact hc.isPreconnected

/-- The cleared actual cofactor relation vanishes throughout the right half-plane. -/
theorem clearedIdentity_zero {w : ℂ} (hw : 0 < w.re) : clearedIdentity w=0 := by
  have he : clearedIdentity =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : IsOpen {w : ℂ | 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (3 : ℂ) ∈ {w : ℂ | 2 < w.re} by norm_num)] with z hz
    exact clearedIdentity_zero_absolute hz
  exact analyticOn_clearedIdentity.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    rightHalfPlane_preconnected (by norm_num : (3 : ℂ) ∈ {w : ℂ | 0 < w.re}) he hw

/-- The meromorphic source/cofactor relation, at every non-pole source parameter. -/
theorem zeta_cofactor_identity {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hw2 : w ≠ 2) :
    2*riemannZeta (w-1)*sourceDeterminant w 1+riemannZeta w*MayerPole.polePart w 1=0 := by
  have h := clearedIdentity_zero hw
  rw [clearedIdentity_eq hw hw1 hw2] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (sub_ne_zero.mpr hw1) (sub_ne_zero.mpr hw2))

/-- The holomorphic remainder determinant has an additional exact shifted-zeta factor. -/
theorem regularPart_eq_shifted_zeta_factor {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (hw2 : w ≠ 2) :
    MayerPole.regularPart w 1=(1+2*riemannZeta (w-1))*sourceDeterminant w 1 := by
  have hd := MayerPole.sourceDeterminant_decomposition hw 1
  have hz := zeta_cofactor_identity hw hw1 hw2
  linear_combination -hd-hz

#print axioms analyticOn_clearedIdentity
#print axioms clearedIdentity_zero
#print axioms zeta_cofactor_identity
#print axioms regularPart_eq_shifted_zeta_factor

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCofactorContinuation
