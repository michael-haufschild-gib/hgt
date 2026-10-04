import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! # Complete-source selection of the critical third-slope boundary direction. -/

namespace HTGeometry.BoundedUnstableSelection
noncomputable section
open Set Filter Topology

/-- A positive outward velocity cannot persist on a complete bounded ray. -/
theorem no_bounded_escape (f f' : ℝ → ℝ) (b M c : ℝ) (hc : 0<c)
    (hd : ∀ x, b≤x → HasDerivAt f (f' x) x)
    (hM : ∀ x, b≤x → f x≤M)
    (hout : ∀ x, b≤x → f b≤f x → c≤f' x) : False := by
  have hbound : ∀ x, b≤x → f b≤f x := by
    intro x hx
    have he : -f x≤ -f b := by
      apply image_le_of_deriv_right_lt_deriv_boundary
        (f := fun y => -f y) (f' := fun y => -f' y) (a := b) (b := x)
        (fun y hy => (hd y hy.1).neg.continuousAt.continuousWithinAt)
        (fun y hy => (hd y hy.1).neg.hasDerivWithinAt)
        (B := fun _ => -f b) (B' := fun _ => 0) le_rfl
        (fun y => hasDerivAt_const y (-f b)) ?_ ⟨hx,le_rfl⟩
      intro y hy he
      have hdy := hout y hy.1 (by linarith only [he])
      linarith only [hdy,hc]
    linarith only [he]
  have hm : MonotoneOn (fun x => f x-c*x) (Ici b) := by
    have hd1 (x : ℝ) (hx : b≤x) :
        HasDerivAt (fun y => f y-c*y) (f' x-c) x := by
      convert (hd x hx).sub ((hasDerivAt_id x).const_mul c) using 1 <;>
        first | rfl | simp
    apply monotoneOn_of_deriv_nonneg (convex_Ici b)
      (fun x hx => (hd1 x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd1 x (show b≤x from
        (show b<x by simpa only [interior_Ici,mem_Ioi] using hx).le)).differentiableAt.differentiableWithinAt)
    intro x hx
    have hbx : b≤x := (show b<x by simpa only [interior_Ici,mem_Ioi] using hx).le
    rw [(hd1 x hbx).deriv]
    exact sub_nonneg.mpr (hout x hbx (hbound x hbx))
  let x := b+(M-f b+1)/c
  have hx : b≤x := by
    have hb := hM b le_rfl
    dsimp [x]
    have hp : 0≤(M-f b+1)/c := div_nonneg (by linarith) hc.le
    linarith
  have he : c*(x-b)=M-f b+1 := by dsimp [x]; field_simp [hc.ne']; ring
  have hi := hm (show b∈Ici b by simp) hx hx
  have hb := hM x hx
  linarith only [he,hi,hb]

/-- A bounded complete solution of an outward linear equation selects its equilibrium.
The forcing may vary arbitrarily, provided that it tends to zero. -/
theorem tendsto_equilibrium (f f' gain err : ℝ → ℝ) (a lo hi L c g : ℝ)
    (hc : 0<c) (hg : 0<g)
    (hd : ∀ x, a≤x → HasDerivAt f (f' x) x)
    (hb : ∀ x, a≤x → lo≤f x ∧ f x≤hi)
    (hgain : ∀ x, a≤x → g≤gain x)
    (hode : ∀ x, a≤x → f' x=gain x*(c*(f x-L)+err x))
    (herr : Tendsto err atTop (𝓝 0)) : Tendsto f atTop (𝓝 L) := by
  have hband (ε : ℝ) (hε : 0<ε) : ∀ᶠ x in atTop, L-ε<f x ∧ f x<L+ε := by
    have hce : 0<c*ε/2 := by positivity
    have hl := herr.eventually_const_lt (show -c*ε/2<0 by linarith)
    have hu := herr.eventually_lt_const hce
    obtain ⟨N,hN⟩ := eventually_atTop.1 (hl.and hu)
    refine eventually_atTop.2 ⟨max a N,?_⟩
    intro b hbb
    have hab : a≤b := (le_max_left a N).trans hbb
    have hNb : N≤b := (le_max_right a N).trans hbb
    have hcg : 0<g*(c*ε/2) := mul_pos hg hce
    constructor
    · by_contra hn
      have hf : f b≤L-ε := le_of_not_gt hn
      apply no_bounded_escape (fun x => -f x) (fun x => -f' x) b (-lo)
        (g*(c*ε/2)) hcg (fun x hx => (hd x (hab.trans hx)).neg)
        (fun x hx => by linarith only [(hb x (hab.trans hx)).1])
      intro x hbx hfx
      have hE := (hN x (hNb.trans hbx)).2
      have hlin : c*(f x-L)+err x≤ -(c*ε/2) := by nlinarith
      have hgg := hgain x (hab.trans hbx)
      have hp := mul_le_mul_of_nonneg_left hlin (show 0≤gain x by linarith)
      have hpp := mul_le_mul_of_nonpos_right hgg (show -(c*ε/2)≤0 by linarith)
      rw [hode x (hab.trans hbx)]
      nlinarith only [hp,hpp]
    · by_contra hn
      have hf : L+ε≤f b := le_of_not_gt hn
      apply no_bounded_escape f f' b hi (g*(c*ε/2)) hcg
        (fun x hx => hd x (hab.trans hx)) (fun x hx => (hb x (hab.trans hx)).2)
      intro x hbx hfx
      have hE := (hN x (hNb.trans hbx)).1
      have hlin : c*ε/2≤c*(f x-L)+err x := by nlinarith
      have hgg := hgain x (hab.trans hbx)
      have hp := mul_le_mul_of_nonneg_left hlin (show 0≤gain x by linarith)
      have hpp := mul_le_mul_of_nonneg_right hgg hce.le
      rw [hode x (hab.trans hbx)]
      exact hpp.trans hp
  apply tendsto_order.2
  constructor
  · intro b hb
    have he := hband (L-b) (sub_pos.mpr hb)
    filter_upwards [he] with x hx
    linarith only [hx.1]
  · intro b hb
    have he := hband (b-L) (sub_pos.mpr hb)
    filter_upwards [he] with x hx
    linarith only [hx.2]

end
end HTGeometry.BoundedUnstableSelection
