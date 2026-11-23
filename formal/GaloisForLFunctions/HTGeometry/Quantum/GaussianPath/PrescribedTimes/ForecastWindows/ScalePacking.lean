import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SymmetricDilations.Scales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Timing concentration at the inverse-square-root Gaussian dimension scale -/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
open SymmetricDilations
noncomputable section

private theorem disjoint_row {ι : Type*} [Fintype ι] {q : ℕ} (a : Fin q→ℝ) (ha : ∀ i, a i ∈ Icc (1/2:ℝ) 2)
    {t w : ℝ} (ht : 0 < t) (hw : 0 ≤ w) (hs : ∀ i j, i≠j → 2*w ≤ |a i-a j| * t)
    (f : (ι→ℝ)→ℝ) (hf : Measurable f) (hscale : ∀ i x, a i*f (a i • x)=f x) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    let E := f ⁻¹' Ioc t (t+w)
    (∑ i, μ.real ((fun x : ι→ℝ => a i • x) ⁻¹' E)) ≤ 1 := by
  intro μ E
  let A (i : Fin q) := (fun x : ι→ℝ => a i • x) ⁻¹' E
  have hm (i) : MeasurableSet (A i) := (measurableSet_Ioc.preimage hf).preimage (measurable_id.const_smul _)
  have hl (i) (x) (hx : x∈A i) : a i*t < f x ∧ f x ≤ a i*t+2*w := by
    have hp : 0 < a i := (by norm_num : (0:ℝ) < 1/2).trans_le (ha i).1
    have hy : f (a i • x) ∈ Ioc t (t+w) := hx
    refine ⟨(mul_lt_mul_of_pos_left hy.1 hp).trans_eq (hscale i x),?_⟩
    rw [←hscale i x]
    exact (mul_le_mul_of_nonneg_left hy.2 hp.le).trans ((mul_add ..).trans_le
      (add_le_add_left (mul_le_mul_of_nonneg_right (ha i).2 hw) _))
  have hd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    have h := hs i j hij
    rcases le_total (a i) (a j) with h'|h'
    · rw [abs_of_nonpos (sub_nonpos.mpr h')] at h
      linarith only [h,(hl i x hi).2,(hl j x hj).1]
    · rw [abs_of_nonneg (sub_nonneg.mpr h')] at h
      linarith only [h,(hl j x hj).2,(hl i x hi).1]
  exact (measureReal_iUnion_fintype (μ:=μ) hd hm).symm.trans_le measureReal_le_one

/-- Opposite inverse-variance shifts cost a bounded Gaussian density factor
through dimension to the power minus one half. Each separated row can land
in a forecast interval at most once. -/
theorem scale_grid_bound {ι : Type*} [Fintype ι] [Nonempty ι] (f : (ι→ℝ)→ℝ) (hf : Measurable f)
    (hscale : ∀ a>0, ∀ x, a*f (a • x)=f x) (q : ℕ) {t w : ℝ} (ht : 0 < t) (hw : 0 < w)
    (hroom : 256*(q:ℝ)*sqrt (Fintype.card ι)*w ≤ t) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    (q:ℝ)*μ.real (f ⁻¹' Ioc t (t+w)) ≤ 2 := by
  intro μ
  let E := f ⁻¹' Ioc t (t+w)
  let L := sqrt (Fintype.card ι)
  let d := 128*w/t
  let h (i : Fin q) := d*(i.val:ℝ)
  have hL : 1 ≤ L := one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ Fintype.card ι from Fintype.card_pos))
  have hL' := zero_le_one.trans hL
  have hd : 0 < d := div_pos (mul_pos (by norm_num) hw) ht
  have hdt : d*t=128*w := div_mul_cancel₀ _ ht.ne'
  have hcap : d*(q:ℝ)*L ≤ 1/2 := by
    rw [show d*(q:ℝ)*L=(128*(q:ℝ)*L*w)/t by dsimp only [d]; ring]
    apply (div_le_iff₀ ht).mpr
    linarith only [hroom]
  have hpos (i : Fin q) : 0 ≤ h i := mul_nonneg hd.le (Nat.cast_nonneg _)
  have hhalf (i : Fin q) : h i*L ≤ 1/2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr i.isLt.le) hd.le) hL').trans hcap
  have hb (i) : |h i| ≤ 1/2 := by
    rw [abs_of_nonneg (hpos i)]
    exact (le_mul_of_one_le_right (hpos i) hL).trans (hhalf i)
  have hm (i) : (Fintype.card ι:ℝ)*(h i)^2 ≤ 1/2 := by
    have hh := mul_self_le_mul_self (mul_nonneg (hpos i) hL') (hhalf i)
    have hs : L^2=(Fintype.card ι:ℝ) := sq_sqrt (Nat.cast_nonneg _)
    linarith only [hh,congrArg (fun v : ℝ => v*(h i)^2) hs]
  have hgap (i j : Fin q) (ne : i≠j) : d ≤ |h i-h j| := by
    have hl : (1:ℝ) ≤ |(i.val:ℝ)-j.val| := by
      rcases lt_or_gt_of_ne (fun he => ne (Fin.ext he) : i.val≠j.val) with hh|hh
      · have h₁ : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast (show i.val+1 ≤ j.val from hh)
        rw [abs_of_nonpos (by linarith only [h₁])]
        linarith only [h₁]
      · have h₁ : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast (show j.val+1 ≤ i.val from hh)
        rw [abs_of_nonneg (by linarith only [h₁])]
        linarith only [h₁]
    rw [show h i-h j=d*((i.val:ℝ)-j.val) by dsimp only [h]; ring,abs_mul,abs_of_pos hd]
    exact le_mul_of_one_le_right hd.le hl
  have row (y : Fin q→ℝ) (hy : ∀ i, |y i| ≤ 1/2) (hg : ∀ i j, i≠j → d ≤ |y i-y j|) :
      (∑ i, μ.real ((fun x : ι→ℝ => scale (y i) • x) ⁻¹' E)) ≤ 1 := by
    apply disjoint_row _ (fun i => scale_bounds (hy i)) ht hw.le _ f hf
      (fun i => hscale _ ((by norm_num : (0:ℝ) < 1/2).trans_le (scale_bounds (hy i)).1))
    intro i j ne
    have h₁ := mul_le_mul_of_nonneg_right (hg i j ne) ht.le
    have h₂ := mul_le_mul_of_nonneg_right (scale_gap (hy i) (hy j)).1 ht.le
    linarith only [h₁,h₂,hdt]
  have plus := row h hb hgap
  have minus := row (fun i => -h i) (fun i => (abs_neg _).trans_le (hb i))
    (fun i j ne => by simpa only [neg_sub_neg,abs_sub_comm (h j)] using hgap i j ne)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => bounded_precision_price (hb i) (hm i) E (measurableSet_Ioc.preimage hf))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_add_distrib] at hsum
  exact hsum.trans (by linarith only [plus,minus])

#print axioms scale_grid_bound
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
