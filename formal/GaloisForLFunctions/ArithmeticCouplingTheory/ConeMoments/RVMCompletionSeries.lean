import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.RVMCompletionGeometry

/-!
# Exact Laplace series of the completed divisor

Absolute convergence permits the block bijection and finite sign sums.
The literal completed-divisor kernel is the original quartet kernel plus
the uniformly bounded critical-pair kernel.
-/

set_option autoImplicit false
noncomputable section
open Finset Complex
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma summable_bool_choice {ι : Type*} {f g : ι → ℂ}
    (hf : Summable f) (hg : Summable g) :
    Summable (fun a : ι × Bool => if a.2 then f a.1 else g a.1) := by
  have hfin : Summable (fun _ : Bool => (1:ℝ)) := Summable.of_finite
  have hm := summable_mul_of_summable_norm (hf.norm.add hg.norm).norm hfin.norm
  apply Summable.of_norm_bounded hm
  rintro ⟨i,b⟩
  cases b
  · simpa only [Bool.false_eq_true,if_false,mul_one] using
      le_add_of_nonneg_left (norm_nonneg (f i))
  · simpa only [if_true,mul_one] using le_add_of_nonneg_right (norm_nonneg (g i))

lemma tsum_bool_choice {ι : Type*} {f g : ι → ℂ}
    (hf : Summable f) (hg : Summable g) :
    (∑' a : ι × Bool,if a.2 then f a.1 else g a.1)=(∑' i,g i)+(∑' i,f i) := by
  rw [(summable_bool_choice hf hg).tsum_prod]
  simp only [tsum_bool,Bool.false_eq_true,if_false,if_true]
  exact hg.tsum_add hf

lemma spline_moment_neg (z : ℂ) (t : ℝ) :
    splineMomentCoefficient (-z)*Complex.exp ((t:ℂ)*(-z))=
      splineMomentCoefficient z*Complex.exp (((-t:ℝ):ℂ)*z) := by
  simp only [splineMomentCoefficient_neg,Complex.ofReal_neg,mul_neg,neg_mul]

lemma spline_moment_conj (z : ℂ) (t : ℝ) :
    splineMomentCoefficient ((starRingEnd ℂ) z)*Complex.exp ((t:ℂ)*(starRingEnd ℂ) z)=
      star (splineMomentCoefficient z*Complex.exp ((t:ℂ)*z)) := by
  change _=(starRingEnd ℂ) (_*_)
  rw [map_mul,← Complex.exp_conj,map_mul,Complex.conj_ofReal,splineMomentCoefficient_conj]

lemma rvmPositiveCoreAtom_moment {ι : Type*} (z : ι → ℂ) (t : ℝ) (a : ι × Bool) :
    splineMomentCoefficient (rvmPositiveCoreAtom z a)*Complex.exp ((t:ℂ)*rvmPositiveCoreAtom z a)=
      if a.2 then star (splineMomentCoefficient (z a.1)*Complex.exp (((-t:ℝ):ℂ)*z a.1))
      else splineMomentCoefficient (z a.1)*Complex.exp ((t:ℂ)*z a.1) := by
  rcases a with ⟨i,b⟩
  cases b
  · rfl
  · change splineMomentCoefficient (-(starRingEnd ℂ) (z i))*
      Complex.exp ((t:ℂ)*(-(starRingEnd ℂ) (z i)))=_
    rw [spline_moment_neg,spline_moment_conj]
    rfl

lemma summable_rvmPositiveCore_moment {ι : Type*} (z : ι → ℂ)
    (hall : ∀ t : ℝ,Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t:ℂ)*z i)))
    (t : ℝ) : Summable (fun a : ι × Bool =>
      splineMomentCoefficient (rvmPositiveCoreAtom z a)*Complex.exp ((t:ℂ)*rvmPositiveCoreAtom z a)) := by
  exact (summable_bool_choice (hall (-t)).star (hall t)).congr fun a =>
    (rvmPositiveCoreAtom_moment z t a).symm

lemma prescribedSplineLaplace_rvmPositiveCore {ι : Type*} (z : ι → ℂ)
    (hall : ∀ t : ℝ,Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t:ℂ)*z i)))
    (t : ℝ) : prescribedSplineLaplace (rvmPositiveCoreAtom z) t=
      prescribedSplineLaplace z t+star (prescribedSplineLaplace z (-t)) := by
  unfold prescribedSplineLaplace
  simp_rw [rvmPositiveCoreAtom_moment]
  rw [tsum_bool_choice (hall (-t)).star (hall t),tsum_star]

def rvmCompletionFlatAtom {ι : Type*} (z : ι → ℂ) :
    ((ι × Bool) ⊕ ((j : ℕ) × Fin (rvmCompletionCriticalCount z j))) → ℂ :=
  Sum.elim (rvmPositiveCoreAtom z)
    (rvmCriticalSlotAtom (rvmCompletionCriticalCount z) (rvmCompletionCriticalCount_le z))

lemma rvmCompletionPositiveAtom_eq_flat {ι : Type*} (z : ι → ℂ)
    (a : (j : ℕ) × RVMCompletionBlock z j) :
    rvmCompletionPositiveAtom z a=rvmCompletionFlatAtom z (rvmCompletionPositiveEquiv z a) := by
  rcases a with ⟨j,a|k⟩ <;> rfl

theorem summable_rvmCompletionPositive_moment {ι : Type*} (z : ι → ℂ)
    (hall : ∀ t : ℝ,Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t:ℂ)*z i)))
    (t : ℝ) : Summable (fun a : (j : ℕ) × RVMCompletionBlock z j =>
      splineMomentCoefficient (rvmCompletionPositiveAtom z a)*Complex.exp ((t:ℂ)*rvmCompletionPositiveAtom z a)) := by
  have hf : Summable (fun a => splineMomentCoefficient (rvmCompletionFlatAtom z a)*
      Complex.exp ((t:ℂ)*rvmCompletionFlatAtom z a)) :=
    Summable.sum _ (summable_rvmPositiveCore_moment z hall t)
      (summable_rvmCriticalSlot_moment _ (rvmCompletionCriticalCount_le z) t)
  have he := (rvmCompletionPositiveEquiv z).summable_iff.mpr hf
  simpa only [Function.comp_def,← rvmCompletionPositiveAtom_eq_flat] using he

theorem prescribedSplineLaplace_rvmCompletionPositive {ι : Type*} (z : ι → ℂ)
    (hall : ∀ t : ℝ,Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t:ℂ)*z i)))
    (t : ℝ) : prescribedSplineLaplace (rvmCompletionPositiveAtom z) t=
      prescribedSplineLaplace (rvmPositiveCoreAtom z) t+
      prescribedSplineLaplace (rvmCriticalSlotAtom (rvmCompletionCriticalCount z)
        (rvmCompletionCriticalCount_le z)) t := by
  have he := (rvmCompletionPositiveEquiv z).tsum_eq
    (fun a => splineMomentCoefficient (rvmCompletionFlatAtom z a)*Complex.exp ((t:ℂ)*rvmCompletionFlatAtom z a))
  change (∑' a,splineMomentCoefficient (rvmCompletionPositiveAtom z a)*
    Complex.exp ((t:ℂ)*rvmCompletionPositiveAtom z a))=_
  simp only [← rvmCompletionPositiveAtom_eq_flat] at he
  rw [he]
  exact Summable.tsum_sum
    (f := fun a => splineMomentCoefficient (rvmCompletionFlatAtom z a)*
      Complex.exp ((t:ℂ)*rvmCompletionFlatAtom z a))
    (summable_rvmPositiveCore_moment z hall t)
    (summable_rvmCriticalSlot_moment _ (rvmCompletionCriticalCount_le z) t)

lemma signedSplineAtom_moment {α : Type*} (w : α → ℂ) (t : ℝ) (a : α × Bool) :
    splineMomentCoefficient (signedSplineAtom w a)*Complex.exp ((t:ℂ)*signedSplineAtom w a)=
      if a.2 then splineMomentCoefficient (w a.1)*Complex.exp (((-t:ℝ):ℂ)*w a.1)
      else splineMomentCoefficient (w a.1)*Complex.exp ((t:ℂ)*w a.1) := by
  rcases a with ⟨a,b⟩
  cases b
  · rfl
  · exact spline_moment_neg (w a) t

theorem summable_signedSplineAtom_moment {α : Type*} (w : α → ℂ)
    (hall : ∀ t : ℝ,Summable (fun a => splineMomentCoefficient (w a)*Complex.exp ((t:ℂ)*w a)))
    (t : ℝ) : Summable (fun a : α × Bool =>
      splineMomentCoefficient (signedSplineAtom w a)*Complex.exp ((t:ℂ)*signedSplineAtom w a)) :=
  (summable_bool_choice (hall (-t)) (hall t)).congr fun a => (signedSplineAtom_moment w t a).symm

lemma prescribedSplineLaplace_signedSplineAtom {α : Type*} (w : α → ℂ)
    (hall : ∀ t : ℝ,Summable (fun a => splineMomentCoefficient (w a)*Complex.exp ((t:ℂ)*w a)))
    (t : ℝ) : prescribedSplineLaplace (signedSplineAtom w) t=prescribedSplinePairKernel w t := by
  unfold prescribedSplineLaplace prescribedSplinePairKernel
  simp_rw [signedSplineAtom_moment]
  exact tsum_bool_choice (hall (-t)) (hall t)

/-- The exact atom series splits into the old quartet series and the added critical pairs. -/
theorem rvmCompletion_kernel_decomposition {ι : Type*} (z : ι → ℂ)
    (hall : ∀ t : ℝ,Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t:ℂ)*z i)))
    (t : ℝ) : prescribedSplineLaplace (signedSplineAtom (rvmCompletionPositiveAtom z)) t=
      prescribedSplineQuartetKernel z t+
        prescribedSplinePairKernel (rvmCriticalSlotAtom (rvmCompletionCriticalCount z)
          (rvmCompletionCriticalCount_le z)) t := by
  rw [prescribedSplineLaplace_signedSplineAtom _ (summable_rvmCompletionPositive_moment z hall)]
  simp only [prescribedSplinePairKernel,prescribedSplineLaplace_rvmCompletionPositive z hall,
    prescribedSplineLaplace_rvmPositiveCore z hall,neg_neg,prescribedSplineQuartetKernel]
  ring

#print axioms summable_rvmCompletionPositive_moment
#print axioms summable_signedSplineAtom_moment
#print axioms rvmCompletion_kernel_decomposition
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
