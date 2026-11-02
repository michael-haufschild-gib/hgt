import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Stratified quadrature for simultaneous spline moments

One interior point per unit cell approximates the integral of a bounded
Hilbert-space-valued function with squared error at most the cell count
times the squared bound. The mean-square selection argument also gives a
simultaneous coordinatewise estimate for finite families of complex functions.
This permits sparse sampling of spline numerator and Jacobian entries.
-/

open MeasureTheory Set Finset
open scoped RealInnerProductSpace
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A mean-zero correction can increase squared error by at most its second
moment, while avoiding any prescribed null set. -/
lemma exists_sample_sq_error_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → E}
    (hf : Integrable f μ) (hfsq : Integrable (fun x => ‖f x‖^2) μ)
    {N : Set α} (hN : μ N=0) (S : E) :
    ∃ x, x ∉ N ∧ ‖S+(f x-∫ y, f y ∂μ)‖^2 ≤ ‖S‖^2+∫ y, ‖f y‖^2 ∂μ := by
  let m := ∫ y, f y ∂μ
  let v := S-m
  have hi : Integrable (fun x => ‖v+f x‖^2) μ := by
    simp_rw [norm_add_sq_real]
    exact ((integrable_const _).add ((hf.const_inner v).const_mul 2)).add hfsq
  have he : (∫ x, ‖v+f x‖^2 ∂μ)=‖v‖^2+2*(inner ℝ v m) + ∫ x, ‖f x‖^2 ∂μ := by
    simp_rw [norm_add_sq_real]
    have hinner : Integrable (fun x => 2*(inner ℝ v (f x))) μ :=
      (hf.const_inner v).const_mul 2
    have hsum : Integrable (fun x => ‖v‖^2+2*(inner ℝ v (f x))) μ :=
      (integrable_const _).add hinner
    rw [integral_add hsum hfsq, integral_add (integrable_const (‖v‖^2)) hinner,
      integral_const_mul, integral_inner hf]
    simp only [integral_const, probReal_univ, one_smul, m]
  obtain ⟨x,hx,hbound⟩ := exists_notMem_null_le_integral hi hN
  have hS := norm_add_sq_real v m
  rw [show v+m=S by dsimp only [v]; exact sub_add_cancel _ _] at hS
  refine ⟨x,hx,?_⟩
  have hxid : S+(f x-m)=v+f x := by dsimp only [v]; abel
  change ‖S+(f x-m)‖^2 ≤ _
  rw [hxid]
  rw [he] at hbound
  nlinarith only [hbound,hS,sq_nonneg ‖m‖]

#print axioms exists_sample_sq_error_le

/-- A unit cell supplies an interior point with bounded squared-error increment. -/
lemma exists_unit_cell_sample {f : ℝ → E} (hf : Continuous f)
    {B : ℝ} (_hB : 0 ≤ B) (hbound : ∀ x, ‖f x‖ ≤ B) (S : E) :
    ∃ x ∈ Ioo (0:ℝ) 1,
      ‖S+(f x-∫ y in (0:ℝ)..1, f y)‖^2 ≤ ‖S‖^2+B^2 := by
  let μ : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by simp [μ, Measure.restrict_apply]⟩
  have hfi : Integrable f μ := hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hfsq : Integrable (fun x => ‖f x‖^2) μ :=
    (hf.norm.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hnull : μ (Ioo (0:ℝ) 1)ᶜ=0 := by simp [μ, Measure.restrict_apply]
  obtain ⟨x,hx,he⟩ := exists_sample_sq_error_le hfi hfsq hnull S
  have hmean : (∫ y, f y ∂μ)=(∫ y in (0:ℝ)..1, f y) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  have hsq : (∫ y, ‖f y‖^2 ∂μ) ≤ B^2 := by
    have hh := integral_mono_ae hfsq (integrable_const (B^2))
      (Filter.Eventually.of_forall fun y => pow_le_pow_left₀ (norm_nonneg _) (hbound y) 2)
    simpa only [integral_const,probReal_univ,one_smul] using hh
  refine ⟨x,by simpa only [mem_compl_iff,not_not] using hx,?_⟩
  rw [hmean] at he
  exact he.trans (add_le_add le_rfl hsq)

/-- One point in each cell simultaneously controls a finite vector of moments.
The squared unnormalized quadrature error grows at most linearly. -/
theorem exists_stratified_samples (n : ℕ) :
    ∀ (f : Fin n → ℝ → E), (∀ j, Continuous (f j)) →
    ∀ B : ℝ, 0 ≤ B → (∀ j x, ‖f j x‖ ≤ B) →
    ∃ x : Fin n → ℝ, (∀ j, x j ∈ Ioo (0:ℝ) 1) ∧
      ‖∑ j, (f j (x j)-∫ y in (0:ℝ)..1, f j y)‖^2 ≤ (n:ℝ)*B^2 := by
  induction n with
  | zero =>
    intro f hf B hB hbound
    refine ⟨Fin.elim0,fun j => Fin.elim0 j,?_⟩
    simp only [Fin.sum_univ_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      zero_pow,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
    intro f hf B hB hbound
    obtain ⟨x,hx,herr⟩ := ih (fun j => f j.succ) (fun j => hf j.succ) B hB
      (fun j y => hbound j.succ y)
    let S := ∑ j, (f j.succ (x j)-∫ y in (0:ℝ)..1, f j.succ y)
    obtain ⟨u,hu,he⟩ := exists_unit_cell_sample (hf 0) hB (hbound 0) S
    refine ⟨Fin.cons u x,?_,?_⟩
    · intro j
      exact Fin.cases hu (fun k => hx k) j
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
      rw [show f 0 u-(∫ y in (0:ℝ)..1, f 0 y)+
        (∑ j, (f j.succ (x j)-∫ y in (0:ℝ)..1, f j.succ y))=
        S+(f 0 u-∫ y in (0:ℝ)..1, f 0 y) by exact add_comm _ _]
      have hs : ‖S‖^2 ≤ (n:ℝ)*B^2 := herr
      rw [Nat.cast_succ]
      nlinarith only [he,hs]

#print axioms exists_unit_cell_sample
#print axioms exists_stratified_samples


/-- Translated unit cells give quadrature with linear squared error and one
interior node in each cell. -/
theorem exists_stratified_quadrature {f : ℝ → E} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, ‖f x‖ ≤ B) (a : ℝ) (n : ℕ) :
    ∃ x : Fin n → ℝ, (∀ j, x j ∈ Ioo (a+j.val) (a+j.val+1)) ∧
      ‖(∑ j, f (x j))-∫ y in a..(a+n), f y‖^2 ≤ (n:ℝ)*B^2 := by
  let g : Fin n → ℝ → E := fun j u => f (a+j.val+u)
  have hg (j) : Continuous (g j) := hf.comp (continuous_const.add continuous_id)
  obtain ⟨u,hu,he⟩ := exists_stratified_samples n g hg B hB (fun j y => hbound _)
  refine ⟨fun j => a+j.val+u j,?_,?_⟩
  · intro j
    have hj := hu j
    constructor <;> linarith only [hj.1,hj.2]
  · have hcell (j : Fin n) : (∫ y in (0:ℝ)..1, g j y)=
        ∫ y in (a+j.val)..(a+j.val+1), f y := by
      simpa only [g,add_zero] using
        (intervalIntegral.integral_comp_add_left (f := f) (a := 0) (b := 1) (a+j.val))
    have hsum : (∑ j : Fin n, ∫ y in (a+j.val)..(a+j.val+1), f y)=
        ∫ y in a..(a+n), f y := by
      have hh := intervalIntegral.sum_integral_adjacent_intervals
        (μ := volume) (a := fun k : ℕ => a+k) (n := n)
        (fun k _ => hf.intervalIntegrable (a+k) (a+(k+1:ℕ)))
      rw [← Fin.sum_univ_eq_sum_range] at hh
      simpa only [Nat.cast_zero,add_zero,Nat.cast_add,Nat.cast_one,← add_assoc] using hh
    simp_rw [hcell] at he
    rw [sum_sub_distrib,hsum] at he
    exact he

#print axioms exists_stratified_quadrature

/-- Finitely many bounded complex functions admit one common stratified
quadrature with coordinatewise error controlled by the dimension. -/
theorem exists_stratified_complex_quadrature {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i x, ‖f i x‖ ≤ B) (a : ℝ) (n : ℕ) :
    ∃ x : Fin n → ℝ, (∀ j, x j ∈ Ioo (a+j.val) (a+j.val+1)) ∧
      ∀ i, ‖(∑ j, f i (x j))-∫ y in a..(a+n), f i y‖^2 ≤
        (n:ℝ)*(((Fintype.card ι:ℝ)+1)*B)^2 := by
  classical
  let e := (EuclideanSpace.equiv ι ℂ).symm
  let F : ℝ → EuclideanSpace ℂ ι := fun y => e (fun i => f i y)
  have hF : Continuous F := e.continuous.comp (continuous_pi hf)
  have hcoord (y : ℝ) (i : ι) : F y i=f i y := rfl
  have hnorm (y : ℝ) : ‖F y‖ ≤ ((Fintype.card ι:ℝ)+1)*B := by
    have hs : ‖F y‖^2 ≤ (Fintype.card ι:ℝ)*B^2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc
        _ ≤ ∑ i : ι, B^2 := sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hbound i y) 2
        _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]
    have hcard : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    have htarget : 0 ≤ ((Fintype.card ι:ℝ)+1)*B := by positivity
    have hmul := mul_nonneg
      (show 0 ≤ (Fintype.card ι:ℝ)^2+(Fintype.card ι:ℝ)+1 by positivity)
      (sq_nonneg B)
    nlinarith only [hs,norm_nonneg (F y),htarget,hmul]
  obtain ⟨x,hx,he⟩ := exists_stratified_quadrature hF (by positivity) hnorm a n
  refine ⟨x,hx,?_⟩
  intro i
  let L : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv ι ℂ).toContinuousLinearMap
  have hL (v : EuclideanSpace ℂ ι) : L v=v i := rfl
  have hint : (∫ y in a..(a+n), F y) i=∫ y in a..(a+n), f i y := by
    exact (L.intervalIntegral_comp_comm (hF.intervalIntegrable a (a+n))).symm
  have hc := PiLp.norm_apply_le ((∑ j, F (x j))-∫ y in a..(a+n), F y) i
  have hid : ((∑ j, F (x j))-∫ y in a..(a+n), F y) i=
      (∑ j, f i (x j))-∫ y in a..(a+n), f i y := by
    change L ((∑ j, F (x j))-∫ y in a..(a+n), F y)=_
    rw [map_sub,map_sum]
    change (∑ j, f i (x j))-(∫ y in a..(a+n), F y) i=_
    rw [hint]
  rw [hid] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) hc 2).trans he

#print axioms exists_stratified_complex_quadrature

end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
