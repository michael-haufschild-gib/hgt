import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A common load for weighted competitive modes

In the synchronized amplitude system of Fan–Giaretto–Soave, the
fraction of each self-interaction paid by the common product solves
v + t a v^r = 1. Each fraction decreases continuously from one to
zero as the load parameter t increases. Their weighted geometric mean
therefore prescribes every positive fraction and the load uniquely.
-/

noncomputable section
open Finset Set
namespace HTGeometry.WeightedCriticalModes

private theorem has_fraction {r : ℝ} (hr : 0<r) {s : ℝ} (hs : 0≤s) :
    ∃ v : ℝ, 0<v ∧ v≤1 ∧ v+s*v^r=1 := by
  let f (v : ℝ) := v+s*v^r
  have cont : Continuous f := continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hr.le))
  have lo : f 0≤1 := by simp [f,Real.zero_rpow hr.ne']
  have hi : 1≤f 1 := by simpa [f] using hs
  obtain ⟨v,hv,h⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num) cont.continuousOn ⟨lo,hi⟩
  refine ⟨v,hv.1.lt_of_ne ?_,hv.2,h⟩
  rintro rfl
  simp [f,Real.zero_rpow hr.ne'] at h

/-- Fraction of a single positive mode taken by the product coupling. -/
def fraction (r s : ℝ) : ℝ :=
  if h : 0<r ∧ 0≤s then (has_fraction h.1 h.2).choose else 1

theorem fraction_spec {r s : ℝ} (hr : 0<r) (hs : 0≤s) :
    0<fraction r s ∧ fraction r s≤1 ∧ fraction r s+s*(fraction r s)^r=1 := by
  rw [fraction,dif_pos ⟨hr,hs⟩]
  exact (has_fraction hr hs).choose_spec

theorem fraction_unique {r s v : ℝ} (hr : 0<r) (hs : 0≤s) (hv : 0<v)
    (h : v+s*v^r=1) : v=fraction r s := by
  have q := fraction_spec hr hs
  have inc {x y : ℝ} (hx : 0<x) (lt : x<y) : x+s*x^r<y+s*y^r :=
    add_lt_add_of_lt_of_le lt (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le lt.le hr.le) hs)
  rcases lt_trichotomy v (fraction r s) with lt|eq|lt
  · exact False.elim ((inc hv lt).ne (h.trans q.2.2.symm))
  · exact eq
  · exact False.elim ((inc q.1 lt).ne (q.2.2.trans h.symm))

theorem fraction_strictAnti {r : ℝ} (hr : 0<r) : StrictAntiOn (fraction r) (Set.Ici 0) := by
  intro s hs t ht hst
  have a := fraction_spec hr hs
  have b := fraction_spec hr ht
  by_contra! up
  have price := mul_lt_mul_of_pos_right hst (Real.rpow_pos_of_pos a.1 r)
  have rest := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow a.1.le up hr.le) ht
  linarith only [price,rest,up,a.2.2,b.2.2]

private theorem fraction_difference {r s t : ℝ} (hr : 0<r) (hs : 0≤s) (hst : s≤t) :
    fraction r s-fraction r t≤t-s := by
  have ht := hs.trans hst
  have a := fraction_spec hr hs
  have b := fraction_spec hr ht
  have order := (fraction_strictAnti hr).antitoneOn hs ht hst
  have pow := Real.rpow_le_rpow b.1.le order hr.le
  have small := Real.rpow_le_rpow b.1.le b.2.1 hr.le
  rw [Real.one_rpow] at small
  have main := mul_le_mul_of_nonneg_left pow hs
  have step := mul_le_mul_of_nonneg_left small (sub_nonneg.mpr hst)
  linarith only [a.2.2,b.2.2,main,step]

/-- Uniform unit Lipschitz constant for the inverse response for
every positive power, including powers below one. -/
theorem fraction_lipschitz {r : ℝ} (hr : 0<r) : LipschitzOnWith 1 (fraction r) (Set.Ici 0) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x hx y hy
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  rcases le_total x y with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr ((fraction_strictAnti hr).antitoneOn hx hy h)),
      abs_of_nonpos (sub_nonpos.mpr h),neg_sub]
    exact fraction_difference hr hx h
  · rw [abs_of_nonpos (sub_nonpos.mpr ((fraction_strictAnti hr).antitoneOn hy hx h)),neg_sub,
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact fraction_difference hr hy h

variable {ι : Type*} [Fintype ι]

/-- Weighted geometric mean on positive mode densities. -/
def geometricMean (w v : ι → ℝ) : ℝ := Real.exp (∑ i, w i*Real.log (v i))

theorem geometricMean_const {w : ι → ℝ} (hw : ∑ i,w i=1) {c : ℝ} (hc : 0<c) :
    geometricMean w (fun _ => c)=c := by
  rw [geometricMean,←sum_mul,hw,one_mul,Real.exp_log hc]

theorem geometricMean_mul (w : ι → ℝ) {x y : ι → ℝ} (hx : ∀ i, 0<x i) (hy : ∀ i, 0<y i) :
    geometricMean w (fun i => x i*y i)=geometricMean w x*geometricMean w y := by
  simp only [geometricMean,fun i => Real.log_mul (hx i).ne' (hy i).ne',mul_add,sum_add_distrib,Real.exp_add]

theorem geometricMean_mono {w x y : ι → ℝ} (hw : ∀ i, 0≤w i) (hx : ∀ i, 0<x i)
    (hxy : ∀ i, x i≤y i) : geometricMean w x≤geometricMean w y :=
  Real.exp_le_exp.mpr (sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (Real.log_le_log (hx i) (hxy i)) (hw i))

theorem geometricMean_lt [Nonempty ι] {w x y : ι → ℝ} (hw : ∀ i, 0<w i) (hx : ∀ i, 0<x i)
    (hxy : ∀ i, x i<y i) : geometricMean w x<geometricMean w y :=
  Real.exp_lt_exp.mpr (sum_lt_sum_of_nonempty univ_nonempty fun i _ =>
    mul_lt_mul_of_pos_left (Real.log_lt_log (hx i) (hxy i)) (hw i))

/-- A prescribed fraction of the weighted geometric self-interaction
determines exactly one positive load. The coefficients and interaction
weights may vary independently between modes. -/
theorem unique_prescribed_load [Nonempty ι] {w a : ι → ℝ} {r γ : ℝ}
    (hw : ∀ i, 0<w i) (mass : ∑ i,w i=1) (ha : ∀ i, 0<a i)
    (hr : 0<r) (hγ : 0<γ) (sub : γ<1) :
    ∃! t : ℝ, 0<t ∧ geometricMean w (fun i => fraction r (a i*t))=γ := by
  let f (t : ℝ) := geometricMean w (fun i => fraction r (a i*t))
  have dec : StrictAntiOn f (Set.Ici 0) := by
    intro x hx y hy xy
    exact geometricMean_lt hw (fun i => (fraction_spec hr (mul_nonneg (ha i).le hy)).1) fun i =>
      fraction_strictAnti hr (mul_nonneg (ha i).le hx) (mul_nonneg (ha i).le hy)
        (mul_lt_mul_of_pos_left xy (ha i))
  have cont : ContinuousOn f (Set.Ici 0) := by
    apply Real.continuous_exp.comp_continuousOn
    apply continuousOn_finsetSum
    intro i _
    have arg : ContinuousOn (fun t : ℝ => fraction r (a i*t)) (Set.Ici 0) :=
      (fraction_lipschitz hr).continuousOn.comp (continuous_const.mul continuous_id).continuousOn
        (fun t ht => mul_nonneg (ha i).le ht)
    exact continuousOn_const.mul (arg.log fun t ht => (fraction_spec hr (mul_nonneg (ha i).le ht)).1.ne')
  have init : f 0=1 := by
    have one : fraction r 0=1 := by simpa only [zero_mul,add_zero] using (fraction_spec hr le_rfl).2.2
    simpa only [f,mul_zero,one] using geometricMean_const (w:=w) mass zero_lt_one
  let T := (∑ i, (a i)⁻¹)/γ^r
  have pow := Real.rpow_pos_of_pos hγ r
  have T0 : 0≤T := div_nonneg (sum_nonneg fun i _ => (inv_pos.mpr (ha i)).le) pow.le
  have endpt : f T≤γ := by
    rw [←geometricMean_const (w:=w) mass hγ]
    apply geometricMean_mono (fun i => (hw i).le) (fun i => (fraction_spec hr (mul_nonneg (ha i).le T0)).1)
    intro i
    have invle := single_le_sum (s:=univ) (f:=fun j => (a j)⁻¹)
      (fun j _ => (inv_pos.mpr (ha j)).le) (mem_univ i)
    have need : 1≤(a i*T)*γ^r := by
      have h := mul_le_mul_of_nonneg_left invle (ha i).le
      rw [mul_inv_cancel₀ (ha i).ne'] at h
      simpa only [T,mul_assoc,div_mul_cancel₀ _ pow.ne'] using h
    have spec := fraction_spec hr (mul_nonneg (ha i).le T0)
    by_contra! lt
    have cost := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hγ.le lt.le hr.le) (mul_nonneg (ha i).le T0)
    linarith only [need,spec.1,spec.2.2,cost]
  obtain ⟨t,ht,eq⟩ := intermediate_value_Icc' T0 (cont.mono (fun _ h => h.1)) ⟨endpt,sub.le.trans_eq init.symm⟩
  have pos : 0<t := ht.1.lt_of_ne (fun h => by rw [←h,init] at eq; exact sub.ne' eq)
  exact ⟨t,⟨pos,eq⟩,fun z hz => dec.injOn hz.1.le ht.1 (hz.2.trans eq.symm)⟩

#print axioms fraction_lipschitz
#print axioms unique_prescribed_load
end HTGeometry.WeightedCriticalModes
