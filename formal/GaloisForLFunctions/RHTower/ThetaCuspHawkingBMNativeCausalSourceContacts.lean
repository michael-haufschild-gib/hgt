import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCharacteristicContact

namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMCausalKernel
open Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private def edgeArgument (a b x y : ℝ) : ℝ :=
  1+2*Real.sinh a*Real.sinh (y-b)/(Real.cosh x*Real.cosh y)

private theorem edge_argument_derivative (a b x : ℝ) :
    HasDerivAt (edgeArgument a b x) (2*Real.sinh a/(Real.cosh x*Real.cosh b)) b := by
  have hn : Real.cosh x*Real.cosh b ≠ 0 := mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have h1 := (((Real.hasDerivAt_sinh (b-b)).comp b (h := fun y : ℝ => y-b) ((hasDerivAt_id b).sub_const b)).const_mul
    (2*Real.sinh a))
  have h2 := (Real.hasDerivAt_cosh b).const_mul (Real.cosh x)
  apply ((h1.div h2 hn).const_add 1).congr_deriv
  simp only [Function.comp_apply,sub_self,Real.sinh_zero,Real.cosh_zero,mul_one,mul_zero,zero_mul,sub_zero]
  field_simp

private theorem edge_contact (q : XiZeroCopy) (a b x X k : ℝ) (ha : 0 ≤ a) :
    HasDerivWithinAt (fun y => angularKernel q (edgeArgument a b x y) X k)
      (((Real.sinh a/(Real.cosh x*Real.cosh b):ℝ):ℂ)*
        scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]) (Ici b) b := by
  have he : edgeArgument a b x b=1 := by simp [edgeArgument]
  have hm : MapsTo (edgeArgument a b x) (Ici b) (Ici 1) := by
    intro y hy
    change 1 ≤ 1+2*Real.sinh a*Real.sinh (y-b)/(Real.cosh x*Real.cosh y)
    have hn : 0 ≤ 2*Real.sinh a*Real.sinh (y-b)/(Real.cosh x*Real.cosh y) :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr ha))
        (Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hy)))
        (mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).le
    linarith
  apply ((angularKernel_right_derivative q X k).scomp_of_eq b
    (edge_argument_derivative a b x).hasDerivWithinAt hm he.symm).congr_deriv
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

private theorem direct_argument (h x y : ℝ) :
    invariant (h-x+y) x y=edgeArgument (h/2) (x-h/2) x y := by
  have h1 : Real.cosh (h-x+y)=Real.cosh (x-y)+
      2*Real.sinh (h/2)*Real.sinh (y-(x-h/2)) := by
    have ha : h-x+y=h/2+(y-(x-h/2)) := by ring
    have hb : h/2-(y-(x-h/2))=x-y := by ring
    have hs := Real.cosh_sub (h/2) (y-(x-h/2))
    rw [hb] at hs
    rw [ha,Real.cosh_add]
    linear_combination -hs
  dsimp [invariant,edgeArgument]
  rw [h1,Real.cosh_sub]
  have hn : Real.cosh x*Real.cosh y ≠ 0 := mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  field_simp
  ring

private theorem image_argument (h x y : ℝ) :
    invariant (h-x+y) x (-y)=edgeArgument (h/2-x) (-h/2) x y := by
  have h1 : Real.cosh (h-x+y)=Real.cosh (x+y)+
      2*Real.sinh (h/2-x)*Real.sinh (y-(-h/2)) := by
    have ha : h-x+y=(h/2-x)+(y-(-h/2)) := by ring
    have hb : (h/2-x)-(y-(-h/2))=-(x+y) := by ring
    have hs := Real.cosh_sub (h/2-x) (y-(-h/2))
    rw [hb,Real.cosh_neg] at hs
    rw [ha,Real.cosh_add]
    linear_combination -hs
  dsimp [invariant,edgeArgument]
  rw [h1,Real.sinh_neg,Real.cosh_neg,Real.cosh_add]
  have hn : Real.cosh x*Real.cosh y ≠ 0 := mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  field_simp
  ring

/-- The source-normal contact on the original direct characteristic at fixed ingoing delay. -/
theorem nativeRiemannKernel_direct_source_contact (q : XiZeroCopy) (h : Ioi (0:ℝ))
    (x X k : ℝ) :
    HasDerivWithinAt (fun y => nativeRiemannKernel q (h.val-x+y) x y X k)
      (((Real.sinh (h.val/2)/(Real.cosh x*Real.cosh (x-h.val/2)):ℝ):ℂ)*
        scalarLaplacian (fullSquarePotential q) ![X,Real.exp k])
      (Ici (x-h.val/2)) (x-h.val/2) := by
  have he : (fun y => nativeRiemannKernel q (h.val-x+y) x y X k)=
      fun y => angularKernel q (edgeArgument (h.val/2) (x-h.val/2) x y) X k := by
    funext y
    rw [nativeRiemannKernel,direct_argument]
  rw [he]
  exact edge_contact q (h.val/2) (x-h.val/2) x X k (by have hp : 0 < h.val := h.property; linarith)

/-- The reflected causal kernel has its own source-normal contact at the original AdS image. -/
theorem nativeRiemannKernel_image_source_contact (q : XiZeroCopy) (h : Ioi (0:ℝ))
    (x : Iic (0:ℝ)) (X k : ℝ) :
    HasDerivWithinAt (fun y => nativeRiemannKernel q (h.val-x.val+y) x.val (-y) X k)
      (((Real.sinh (h.val/2-x.val)/(Real.cosh x.val*Real.cosh (h.val/2)):ℝ):ℂ)*
        scalarLaplacian (fullSquarePotential q) ![X,Real.exp k])
      (Ici (-h.val/2)) (-h.val/2) := by
  have he : (fun y => nativeRiemannKernel q (h.val-x.val+y) x.val (-y) X k)=
      fun y => angularKernel q (edgeArgument (h.val/2-x.val) (-h.val/2) x.val y) X k := by
    funext y
    rw [nativeRiemannKernel,image_argument]
  rw [he]
  simpa only [neg_div,Real.cosh_neg] using
    edge_contact q (h.val/2-x.val) (-h.val/2) x.val X k (by have hp : 0 < h.val := h.property; have hx : x.val ≤ 0 := x.property; linarith)

end
end RHTower.D4BMNativeCircle
