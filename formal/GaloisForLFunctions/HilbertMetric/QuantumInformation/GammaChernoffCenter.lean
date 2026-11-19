import GaloisForLFunctions.HilbertMetric.QuantumInformation.GammaRateDivergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Chernoff center of two Gamma rates

The optimal Chernoff tilt has rate equal to the logarithmic mean of the
two rates. It is the unique equal-divergence point of the fixed-shape
family when the rates differ. The optimization gap is the elementary
nonnegative function r−1−log r of the tilted rate ratio.
-/

noncomputable section
open MeasureTheory Real Set InformationTheory
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing.GammaAffinity

def centerRate (s t : ℝ) := if s=t then exp s else (exp s-exp t)/(s-t)

private theorem center_symm (s t : ℝ) : centerRate s t=centerRate t s := by
  by_cases h : s=t
  · subst t; rfl
  · simp only [centerRate,h,Ne.symm h,if_false]
    rw [← neg_sub s t,← neg_sub (exp s) (exp t),neg_div_neg_eq]

private theorem center_between {s t : ℝ} (h : t<s) : exp t<centerRate s t ∧ centerRate s t<exp s := by
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope exp exp h continuous_exp.continuousOn
    (fun x _ => hasDerivAt_exp x)
  rw [centerRate,if_neg h.ne',← he]
  exact ⟨exp_lt_exp.mpr hc.1,exp_lt_exp.mpr hc.2⟩

theorem center_pos (s t : ℝ) : 0<centerRate s t := by
  rcases lt_trichotomy s t with h|h|h
  · rw [center_symm]; exact (exp_pos s).trans (center_between h).1
  · subst t; simp [centerRate,exp_pos]
  · exact (exp_pos t).trans (center_between h).1

private theorem center_secant (s t : ℝ) : centerRate s t*(s-t)=exp s-exp t := by
  by_cases h : s=t
  · subst t; simp
  · simp [centerRate,h,sub_ne_zero.mpr h]

private def fraction (s t : ℝ) := if s=t then 1/2 else (centerRate s t-exp t)/(exp s-exp t)

private theorem ordered_fraction {s t : ℝ} (h : t<s) : 0<fraction s t ∧ fraction s t<1 := by
  obtain ⟨hl,hr⟩ := center_between h
  have hp := sub_pos.mpr (exp_lt_exp.mpr h)
  rw [fraction,if_neg h.ne']
  exact ⟨div_pos (sub_pos.mpr hl) hp,(div_lt_one hp).mpr (sub_lt_sub_right hr _)⟩

private theorem fraction_symm (s t : ℝ) : fraction s t=1-fraction t s := by
  by_cases h : s=t
  · subst t; norm_num [fraction]
  · have hn := sub_ne_zero.mpr (Real.exp_injective.ne h)
    simp only [fraction,h,Ne.symm h,if_false,← center_symm s t]
    rw [← neg_sub (exp s) (exp t)]
    field_simp [hn]
    ring

/-- The equal-rate case chooses the symmetric tilt. -/
def centerWeight (s t : ℝ) : Weight := ⟨fraction s t,by
  rcases lt_trichotomy t s with h|h|h
  · exact ordered_fraction h
  · subst t; norm_num [fraction]
  · rw [fraction_symm]
    obtain ⟨hl,hr⟩ := ordered_fraction h
    constructor <;> linarith only [hl,hr]⟩

theorem tilted_rate (s t : ℝ) : mixRate (centerWeight s t).val s t=centerRate s t := by
  unfold mixRate centerWeight fraction
  by_cases h : s=t
  · subst t; simp [centerRate]; ring
  · rw [if_neg h]
    field_simp [sub_ne_zero.mpr (Real.exp_injective.ne h)]
    ring

private theorem mix_positive (p : Weight) (s t : ℝ) : 0<mixRate p.val s t :=
  add_pos (mul_pos p.property.1 (exp_pos _)) (mul_pos (sub_pos.mpr p.property.2) (exp_pos _))

/-- Exact gap above the optimal logarithmic Chernoff affinity. -/
theorem chernoff_gap (p : Weight) (s t : ℝ) :
    let r := mixRate p.val s t/centerRate s t
    logAffinity p.val s t-logAffinity (centerWeight s t).val s t = r-1-log r := by
  intro r
  let q := (centerWeight s t).val
  have linear : mixRate p.val s t-centerRate s t=(p.val-q)*(exp s-exp t) := by
    rw [← tilted_rate]
    unfold mixRate q
    ring
  have ratio : r-1=(p.val-q)*(s-t) := by
    change mixRate p.val s t/centerRate s t-1=_
    field_simp [(center_pos s t).ne']
    linear_combination linear-(p.val-q)*(center_secant s t)
  change logAffinity p.val s t-logAffinity q s t=_
  rw [ratio,logAffinity,logAffinity,show mixRate q s t=centerRate s t from tilted_rate s t]
  dsimp only [r]
  rw [log_div (mix_positive p s t).ne' (center_pos s t).ne']
  ring

/-- The logarithmic-mean tilt minimizes the actual density integral.
Equality describes all minimizers, including coincident rates. -/
theorem optimal_chernoff (a : Shape) (p : Weight) (s t : ℝ) :
    let C := fun q : Weight => ∫ x, (density a s x)^q.val*(density a t x)^(1-q.val)
    C (centerWeight s t)≤C p ∧ (C (centerWeight s t)=C p ↔ s=t ∨ p=centerWeight s t) := by
  intro C
  let q := centerWeight s t
  let r := mixRate p.val s t/centerRate s t
  have hr : 0<r := div_pos (mix_positive p _ _) (center_pos _ _)
  have gap := chernoff_gap p s t
  change logAffinity p.val s t-logAffinity q.val s t=r-1-log r at gap
  have bound : logAffinity q.val s t≤logAffinity p.val s t := by linarith only [gap,log_le_sub_one_of_pos hr]
  have val (w : Weight) : C w=exp (a.val*logAffinity w.val s t) := chernoff_mass a w s t
  rw [val,val,exp_le_exp,exp_inj,mul_right_inj' a.property.ne']
  refine ⟨mul_le_mul_of_nonneg_left bound a.property.le,?_⟩
  change logAffinity q.val s t=logAffinity p.val s t ↔ s=t ∨ p=q
  constructor
  · intro h
    by_cases hs : s=t
    · exact Or.inl hs
    right
    have e : r=1 := by
      by_contra hn
      linarith only [gap,h,log_lt_sub_one_of_pos hr hn]
    have hm := (div_eq_one_iff_eq (center_pos s t).ne').mp e
    rw [← tilted_rate] at hm
    apply Subtype.ext
    apply mul_right_cancel₀ (sub_ne_zero.mpr (Real.exp_injective.ne hs))
    change p.val*(exp s-exp t)=q.val*(exp s-exp t)
    change mixRate p.val s t=mixRate q.val s t at hm
    unfold mixRate at hm
    linarith only [hm]
  · rintro (e|e)
    · subst t
      have hh (w : Weight) : logAffinity w.val s s=0 := by
        simp only [logAffinity,mixRate,show w.val*exp s+(1-w.val)*exp s=exp s by ring,log_exp]
        ring
      rw [hh,hh]
    · rw [e]

/-- Equal directed KL divergences from a member of the Gamma family
single out the logarithmic mean, except when the references coincide. -/
theorem equal_divergence_iff (a : Shape) (u s t : ℝ) :
    (klDiv (law a u) (law a s)).toReal=(klDiv (law a u) (law a t)).toReal ↔
      s=t ∨ exp u=centerRate s t := by
  rw [(rate_kl a u s).2,(rate_kl a u t).2,mul_right_inj' a.property.ne',exp_sub,exp_sub]
  by_cases h : s=t
  · subst t; simp
  · simp only [h,false_or]
    rw [centerRate,if_neg h,eq_div_iff (sub_ne_zero.mpr h)]
    constructor <;> intro he
    · field_simp [exp_ne_zero] at he
      linarith only [he]
    · field_simp [exp_ne_zero]
      linarith only [he]

#print axioms tilted_rate
#print axioms chernoff_gap
#print axioms optimal_chernoff
#print axioms equal_divergence_iff
end GaloisForLFunctions.HilbertMetric.CauchyDephasing.GammaAffinity
