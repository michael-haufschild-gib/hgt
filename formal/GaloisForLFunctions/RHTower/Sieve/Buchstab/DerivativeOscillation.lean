import GaloisForLFunctions.RHTower.Sieve.Buchstab.UnitOscillation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Oscillation of every derivative of the Buchstab error

Differentiation increases the damping coefficient in the delay equation
by one. Multiplication by the corresponding power of the argument restores
positivity propagation. The mean value theorem provides both signs at
arbitrarily large arguments in every derivative order.
-/

namespace RHTower.Sieve.Buchstab
open Set Filter Topology
noncomputable section

/-- Explicit extension of the kth derivative on its smooth ray. -/
def delayJet : ℕ → ℝ → ℝ
  | 0 => fun x => buchstab x-enclosureLimit
  | n+1 => fun x => (delayJet n (x-1)-((n:ℝ)+1)*delayJet n x)/x

theorem delayJet_hasDerivAt (n : ℕ) (x : Ioi ((n:ℝ)+2)) :
    HasDerivAt (delayJet n) (delayJet (n+1) x) x.val := by
  induction n with
  | zero =>
    have hd := (hasDerivAt_buchstab ⟨x.val,by simpa using x.property⟩).sub_const enclosureLimit
    apply hd.congr_deriv
    dsimp [delayJet]
    ring
  | succ n ih =>
    have hx : (n:ℝ)+1+2 < x.val := by simpa only [mem_Ioi,Nat.cast_succ] using x.property
    have hn : x.val ≠ 0 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hd := ih ⟨x.val,show (n:ℝ)+2<x.val by linarith⟩
    have h₁ := (ih ⟨x.val-1,show (n:ℝ)+2<x.val-1 by linarith⟩).comp x.val
      ((hasDerivAt_id x.val).sub_const 1)
    let c := (n:ℝ)+1
    have hnum : HasDerivAt (fun t => delayJet n (t-1)-c*delayJet n t)
        (delayJet (n+1) (x.val-1)-c*delayJet (n+1) x.val) x.val := by
      simpa only [Function.comp_def,id_eq,mul_one] using h₁.fun_sub (hd.const_mul c)
    apply (hnum.fun_div (hasDerivAt_id x.val) hn).congr_deriv
    change ((delayJet (n+1) (x.val-1)-c*delayJet (n+1) x.val)*x.val -
        (delayJet n (x.val-1)-c*delayJet n x.val)*1)/x.val^2 =
      (delayJet (n+1) (x.val-1)-(((n+1:ℕ):ℝ)+1)*delayJet (n+1) x.val)/x.val
    have hv : delayJet n (x.val-1)-c*delayJet n x.val = delayJet (n+1) x.val*x.val :=
      (div_mul_cancel₀ _ hn).symm
    rw [hv]
    simp only [Nat.cast_succ,c]
    field_simp [hn]
    ring

private theorem jet_continuousAt (n : ℕ) {x : ℝ} (hx : (n:ℝ)+1<x) :
    ContinuousAt (delayJet n) x := by
  induction n generalizing x with
  | zero =>
    have hx' : 1 < x := by simpa using hx
    exact (continuousOn_buchstab.continuousAt (Ici_mem_nhds hx')).sub continuousAt_const
  | succ n ih =>
    rw [Nat.cast_succ] at hx
    have hs : ContinuousAt (fun t : ℝ => t-1) x := continuousAt_id.sub continuousAt_const
    have hprev : ContinuousAt (fun t => delayJet n (t-1)) x :=
      ContinuousAt.comp (f := fun t : ℝ => t-1) (x := x) (ih (x := x-1) (by linarith)) hs
    have hnow := ih (x := x) (by linarith)
    exact (hprev.sub (continuousAt_const.mul hnow)).div continuousAt_id
      (show x ≠ 0 by linarith [Nat.cast_nonneg (α:=ℝ) n])

/-- The recurrence gives the actual ordinary iterated derivatives, including
all integer junctions to the right of the indicated endpoint. -/
theorem delayJet_eq_iteratedDeriv (n : ℕ) (x : Ioi ((n:ℝ)+1)) :
    iteratedDeriv n (fun t => buchstab t-enclosureLimit) x.val = delayJet n x := by
  induction n with
  | zero => simp [delayJet]
  | succ n ih =>
    have hx : (n:ℝ)+1+1 < x.val := by simpa only [mem_Ioi,Nat.cast_succ] using x.property
    have he : iteratedDeriv n (fun t => buchstab t-enclosureLimit) =ᶠ[𝓝 x.val] delayJet n := by
      filter_upwards [lt_mem_nhds (show (n:ℝ)+1<x.val by linarith)] with t ht
      exact ih ⟨t,ht⟩
    rw [iteratedDeriv_succ,he.deriv_eq]
    exact (delayJet_hasDerivAt n ⟨x.val,show (n:ℝ)+2<x.val by linarith⟩).deriv

private theorem jet_cofinal (n : ℕ) (a : ℝ) :
    (∃ t, a<t ∧ delayJet n t<0) ∧ (∃ t, a<t ∧ 0<delayJet n t) := by
  induction n generalizing a with
  | zero =>
    let b := max a 1+1
    have hab : a < b := by dsimp [b]; linarith only [le_max_left a 1]
    have hb : 1 ≤ b := by dsimp [b]; linarith only [le_max_right a 1]
    obtain ⟨⟨t,ht,hs⟩,⟨u,hu,hs'⟩⟩ := buchstab_oscillates_each_unit ⟨b,hb⟩
    exact ⟨⟨t,hab.trans_le ht.1,sub_neg.mpr hs⟩,⟨u,hab.trans_le hu.1,sub_pos.mpr hs'⟩⟩
  | succ n ih =>
    let b := max a ((n:ℝ)+2)
    have mean {t u : ℝ} (ht : b<t) (hu : t<u) :
        ∃ v ∈ Ioo t u, delayJet (n+1) v=(delayJet n u-delayJet n t)/(u-t) := by
      have h₀ := (le_max_right a ((n:ℝ)+2)).trans_lt ht
      exact exists_hasDerivAt_eq_slope _ _ hu
        (fun v hv => (jet_continuousAt n (show (n:ℝ)+1<v by linarith [hv.1])).continuousWithinAt)
        (fun v hv => delayJet_hasDerivAt n ⟨v,h₀.trans hv.1⟩)
    obtain ⟨⟨t,ht,htneg⟩,⟨u,hu,hupos⟩⟩ := ih b
    obtain ⟨t',ht',htneg'⟩ := (ih u).1
    obtain ⟨u',hu',hupos'⟩ := (ih t).2
    obtain ⟨v,hv,he⟩ := mean hu ht'
    obtain ⟨w,hw,he'⟩ := mean ht hu'
    refine ⟨⟨v,(le_max_left a _).trans_lt (hu.trans hv.1),?_⟩,
      ⟨w,(le_max_left a _).trans_lt (ht.trans hw.1),?_⟩⟩
    · rw [he]
      exact div_neg_of_neg_of_pos (sub_neg.mpr (htneg'.trans hupos)) (sub_pos.mpr ht')
    · rw [he']
      exact div_pos (sub_pos.mpr (htneg.trans hupos')) (sub_pos.mpr hu')

/-- After multiplying by x^(n+1), the sole forcing term is the delayed
value times the positive weight x^n. -/
theorem delayJet_weighted_deriv (n : ℕ) (x : Ioi ((n:ℝ)+2)) :
    HasDerivAt (fun t : ℝ => t^(n+1)*delayJet n t) (x.val^n*delayJet n (x.val-1)) x.val := by
  have hn := Nat.cast_nonneg (α:=ℝ) n
  have hpos : x.val ≠ 0 := ne_of_gt (by linarith [show (n:ℝ)+2<x.val from x.property])
  apply (((hasDerivAt_id x.val).pow (n+1)).mul (delayJet_hasDerivAt n x)).congr_deriv
  simp only [Pi.pow_apply,Nat.add_sub_cancel,Nat.cast_succ,id_eq,mul_one,delayJet]
  rw [pow_succ]
  field_simp [hpos]
  ring

private theorem jet_sign_forward (n : ℕ) (s a : ℝ) (ha : (n:ℝ)+1<a)
    (hs : ∀ t ∈ Icc a (a+1), 0 ≤ s*delayJet n t) :
    ∀ t ≥ a, 0 ≤ s*delayJet n t := by
  let W := fun x : ℝ => s*(x^(n+1)*delayJet n x)
  have hstep (j : ℕ) : ∀ t ∈ Icc (a+j) (a+j+1), 0 ≤ s*delayJet n t := by
    induction j with
    | zero => simpa using hs
    | succ j ih =>
      intro t ht
      simp only [Nat.cast_succ] at ht
      let b := a+j+1
      have hbt : b ≤ t := by dsimp [b]; linarith [ht.1]
      have htb : t ≤ b+1 := by dsimp [b]; linarith [ht.2]
      have hba : (n:ℝ)+2 < b := by dsimp [b]; linarith [Nat.cast_nonneg (α:=ℝ) j]
      have hb := ih b ⟨by dsimp [b]; linarith,le_rfl⟩
      rcases hbt.eq_or_lt with h|h
      · exact h ▸ hb
      have hW (v : ℝ) (hv : v ∈ Ioo b t) : HasDerivAt W (s*(v^n*delayJet n (v-1))) v :=
        (delayJet_weighted_deriv n ⟨v,hba.trans hv.1⟩).const_mul s
      obtain ⟨v,hv,he⟩ := exists_hasDerivAt_eq_slope W _ h
        (fun v hv => (continuousAt_const.mul ((continuousAt_id.pow _).mul
          (jet_continuousAt n (show (n:ℝ)+1<v by linarith [hv.1])))).continuousWithinAt) hW
      have hv₁ := ih (v-1) ⟨by dsimp [b] at hv; linarith [hv.1],
        by change v-1 ≤ b; linarith [hv.2]⟩
      have hvpos : 0 ≤ v := by linarith [hv.1,Nat.cast_nonneg (α:=ℝ) n]
      have hsl : 0 ≤ (W t-W b)/(t-b) := by
        rw [← he,mul_left_comm]
        exact mul_nonneg (pow_nonneg hvpos _) hv₁
      have hle : W b ≤ W t := sub_nonneg.mp (by
        simpa only [zero_mul] using (le_div_iff₀ (sub_pos.mpr h)).mp hsl)
      have hw : 0 ≤ W b := by
        dsimp only [W]
        rw [mul_left_comm]
        exact mul_nonneg (pow_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n]) _) hb
      have h' := hw.trans hle
      dsimp only [W] at h'
      rw [mul_left_comm] at h'
      exact nonneg_of_mul_nonneg_right h' (pow_pos (by linarith [Nat.cast_nonneg (α:=ℝ) n]) _)
  intro t ht
  exact hstep ⌊t-a⌋₊ t ⟨by linarith [Nat.floor_le (sub_nonneg.mpr ht)],
    by linarith [Nat.lt_floor_add_one (t-a)]⟩

/-- Every derivative of the centered Buchstab function takes both strict
signs in each sliding unit window on its smooth ray. -/
theorem iteratedDeriv_oscillates_each_unit (n : ℕ) (a : Ioi ((n:ℝ)+1)) :
    (∃ t ∈ Icc a.val (a.val+1), iteratedDeriv n (fun u => buchstab u-enclosureLimit) t < 0) ∧
    (∃ t ∈ Icc a.val (a.val+1), 0 < iteratedDeriv n (fun u => buchstab u-enclosureLimit) t) := by
  have he (t : ℝ) (ht : t ∈ Icc a.val (a.val+1)) :=
    delayJet_eq_iteratedDeriv n ⟨t,a.property.trans_le ht.1⟩
  constructor
  · by_contra! hn
    have hs := jet_sign_forward n 1 a.val a.property (fun t ht => by
      simpa only [one_mul,← he t ht] using hn t ht)
    obtain ⟨t,ht,hneg⟩ := (jet_cofinal n a.val).1
    simpa only [one_mul,not_le.mpr hneg] using hs t ht.le
  · by_contra! hn
    have hs := jet_sign_forward n (-1) a.val a.property (fun t ht => by
      simpa only [neg_one_mul,neg_nonneg,← he t ht] using hn t ht)
    obtain ⟨t,ht,hpos⟩ := (jet_cofinal n a.val).2
    simpa only [neg_one_mul,neg_nonneg,not_le.mpr hpos] using hs t ht.le
end
end RHTower.Sieve.Buchstab
