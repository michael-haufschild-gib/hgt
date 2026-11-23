import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Prod

/-! # Exponential moments after revealing one independent phase -/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.PhaseFluctuations
noncomputable section

/-- A bounded observable whose oscillation is at most L satisfies
Hoeffding's lemma with parameter L²/4, independently of its mean. -/
theorem subgaussian_of_oscillation {X : Type*} [MeasurableSpace X] [Nonempty X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f)
    {b : ℝ} (hl : ∀ x, b ≤ f x) (L : NNReal) (h : ∀ x y, f x-f y ≤ L) :
    HasSubgaussianMGF (fun x => f x-∫ y, f y ∂μ) ((L/2)^2) μ := by
  let a := sInf (range f)
  have hb : BddBelow (range f) := ⟨b,fun _ ⟨x,hx⟩ => hx ▸ hl x⟩
  have hm (x) : a ≤ f x := csInf_le hb (mem_range_self x)
  have hM (x) : f x ≤ a+L := by
    have hlo : f x-L ≤ a := by
      apply le_csInf (range_nonempty f)
      rintro _ ⟨y,rfl⟩
      linarith only [h x y]
    linarith only [hlo]
  have hs := hasSubgaussianMGF_of_mem_Icc (μ:=μ) hf.aemeasurable
    (Filter.Eventually.of_forall fun x => (show f x∈Icc a (a+L) from ⟨hm x,hM x⟩))
  have hnorm : ‖(L:ℝ)‖₊=L := NNReal.eq (Real.norm_of_nonneg L.2)
  simpa only [add_sub_cancel_left,hnorm] using hs

/-- Integrating over the unrevealed phases adds their exponential-moment
parameter to the cost of revealing the first phase. -/
theorem subgaussian_product_step {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X × Y → ℝ) (hf : Measurable f) {a b : ℝ} (hb : ∀ p, f p∈Icc a b)
    (L c : NNReal) (hchange : ∀ x x' y, f (x,y)-f (x',y) ≤ L)
    (hrest : ∀ x, HasSubgaussianMGF (fun y => f (x,y)-∫ z, f (x,z) ∂ν) c ν) :
    HasSubgaussianMGF (fun p => f p-∫ q, f q ∂(μ.prod ν)) (c+(L/2)^2) (μ.prod ν) := by
  let m (x : X) := ∫ y, f (x,y) ∂ν
  let M := ∫ p, f p ∂(μ.prod ν)
  have hi := Integrable.of_mem_Icc (μ:=μ.prod ν) a b hf.aemeasurable (Filter.Eventually.of_forall hb)
  have his (x : X) : Integrable (fun y => f (x,y)) ν := Integrable.of_mem_Icc (μ:=ν) a b
    ((hf.comp (measurable_const.prodMk measurable_id)).aemeasurable)
    (Filter.Eventually.of_forall fun y => hb (x,y))
  have hm : Measurable m := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hml (x) : a ≤ m x := by
    change a ≤ ∫ y, f (x,y) ∂ν
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono (μ:=ν) (integrable_const a) (his x) (fun y => (hb (x,y)).1)
  have hosc (x x' : X) : m x-m x' ≤ L := by
    have h : (∫ y, f (x,y) ∂ν) ≤ ∫ y, f (x',y)+(L:ℝ) ∂ν :=
      integral_mono (his x) ((his x').add (integrable_const (L:ℝ)))
        (fun y => (sub_le_iff_le_add.mp (hchange x x' y)).trans_eq (add_comm ..))
    rw [integral_add (his x') (integrable_const _),integral_const,probReal_univ,one_smul] at h
    change m x ≤ m x'+L at h
    linarith only [h]
  have hhead := subgaussian_of_oscillation μ hm hml L hosc
  have hM : (∫ x, m x ∂μ)=M := (integral_prod f hi).symm
  have hglobal := hasSubgaussianMGF_of_mem_Icc (μ:=μ.prod ν) hf.aemeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hglobal.integrable_exp_mul,?_⟩
  intro t
  have hfactor (x : X) :
      (∫ y, exp (t*(f (x,y)-M)) ∂ν)=exp (t*(m x-M))*mgf (fun y => f (x,y)-m x) ν t := by
    rw [mgf,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [←exp_add]
    congr 1
    ring
  change (∫ p, exp (t*(f p-M)) ∂(μ.prod ν))≤_
  rw [integral_prod _ (hglobal.integrable_exp_mul t)]
  have hbound (x) : (∫ y, exp (t*(f (x,y)-M)) ∂ν) ≤
      exp (t*(m x-M))*exp ((c:ℝ)*t^2/2) := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left ((hrest x).mgf_le t) (exp_pos _).le
  have hleft := (hglobal.integrable_exp_mul t).integral_prod_left
  have hright := (hhead.integrable_exp_mul t).mul_const (exp ((c:ℝ)*t^2/2))
  rw [hM] at hright
  apply (integral_mono hleft hright hbound).trans
  rw [integral_mul_const]
  have hhead' := hhead.mgf_le t
  rw [mgf,hM] at hhead'
  apply (mul_le_mul_of_nonneg_right hhead' (exp_pos _).le).trans_eq
  rw [←exp_add,NNReal.coe_add]
  congr 1
  ring

end
end GaloisForLFunctions.HTGeometry.PhaseFluctuations
