import GaloisForLFunctions.RHTower.WeilTailPanelPositiveCompletion

/-!
# Sharp preserved-prefix capacity of tail-panel completion

At the first window `L = base + 1`, the last integer strictly below
`2 * exp (2 * L)` is a common positive spike coordinate. The first probe sees
no coefficient beyond that integer. These two facts determine the exact
prefix length compatible with arbitrary simultaneous panel-height targets.
-/

open Complex MeasureTheory Set Zeta23
open scoped BigOperators

noncomputable section

namespace RHTower

private theorem two_lt_exp_window (base : ℕ) :
    2 < Real.exp (2 * ((base + 1 : ℕ) : ℝ)) := by
  have hb : (1 : ℝ) ≤ ((base + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ base + 1 by omega)
  have hx : 0 < 2 * ((base + 1 : ℕ) : ℝ) := by linarith only [hb]
  have h := Real.add_one_lt_exp hx.ne'
  linarith only [hb, h]

/-- Last integer strictly below the support endpoint of the first panel probe. -/
def weilLogShiftSharpLiftIndex (base : ℕ) : ℕ :=
  ⌈2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌉₊ - 1

/-- Exact integer boundary, without any irrationality assumption on the endpoint. -/
theorem weilLogShiftSharpLiftIndex_bounds (base : ℕ) :
    Real.exp (2 * ((base + 1 : ℕ) : ℝ)) < (weilLogShiftSharpLiftIndex base : ℝ) ∧
    (weilLogShiftSharpLiftIndex base : ℝ) < 2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ)) ∧
    ∀ n : ℕ, weilLogShiftSharpLiftIndex base < n ↔
      2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
  have hc : 1 ≤ ⌈2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌉₊ :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  have heq : ⌈2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌉₊ =
      weilLogShiftSharpLiftIndex base + 1 := by
    unfold weilLogShiftSharpLiftIndex
    omega
  have hhi : (weilLogShiftSharpLiftIndex base : ℝ) <
      2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ)) :=
    Nat.lt_ceil.mp (by omega)
  have hle : 2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ)) ≤
      (weilLogShiftSharpLiftIndex base : ℝ) + 1 := by
    have h := Nat.le_ceil (2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ)))
    rw [heq] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hE := two_lt_exp_window base
  refine ⟨by linarith only [hle, hE], hhi, ?_⟩
  intro n
  rw [← Nat.ceil_le]
  omega

private theorem outerSpike_kernel (base n : ℕ)
    (hlo : Real.exp (2 * ((base + 1 : ℕ) : ℝ)) < (n : ℝ))
    (hhi : (n : ℝ) < 2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ)))
    (m : Finset.Icc 2 ⌊Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌋₊) :
    0 < truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ) (Real.log n - Real.log m.1) ∧
    EF.weilTest (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log m.1))
        (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log m.1)) (Real.log n) +
      EF.weilTest (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log m.1))
        (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log m.1)) (-Real.log n) =
      ((-2 * truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ)
        (Real.log n - Real.log m.1) : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hlo
  have hm2 : (2 : ℝ) ≤ m.1 := by exact_mod_cast (Finset.mem_Icc.mp m.2).1
  have hm0 : (0 : ℝ) < m.1 := by linarith only [hm2]
  have hmE : (m.1 : ℝ) ≤ Real.exp (2 * ((base + 1 : ℕ) : ℝ)) :=
    (by exact_mod_cast (Finset.mem_Icc.mp m.2).2 :
      (m.1 : ℝ) ≤ (⌊Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌋₊ : ℝ)).trans
        (Nat.floor_le (Real.exp_pos _).le)
  have hc := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hclo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hm2
  have hchi := Real.log_le_log hm0 hmE
  rw [Real.log_exp] at hchi
  have hylo := Real.log_lt_log (Real.exp_pos _) hlo
  rw [Real.log_exp] at hylo
  have hyhi := Real.log_lt_log hn0 hhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne', Real.log_exp] at hyhi
  have hyc : 0 < Real.log n - Real.log m.1 := by linarith only [hylo, hchi]
  have hpos : 0 < truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ)
      (Real.log n - Real.log m.1) := by
    apply (truncatedRiemannAutocorr_pos_iff _ _).mpr
    rw [abs_of_pos hyc]
    linarith only [hyhi, hclo]
  have h0 : truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ) (Real.log n) = 0 :=
    truncatedRiemannAutocorr_eq_zero (hylo.le.trans (le_abs_self _))
  have h1 : truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ) (Real.log n + Real.log m.1) = 0 := by
    apply truncatedRiemannAutocorr_eq_zero
    have ha := le_abs_self (Real.log n + Real.log m.1)
    linarith only [hylo, hclo, hc, ha]
  refine ⟨hpos, ?_⟩
  rw [logShiftRiemannPair_eq, h0, h1]
  push_cast
  ring

/-- Exact gain at any common positive spike coordinate between exp(2L) and 2exp(2L). -/
theorem weilLogShiftWindowPanel_outerSpike (base n : ℕ)
    (hlo : Real.exp (2 * ((base + 1 : ℕ) : ℝ)) < (n : ℝ))
    (hhi : (n : ℝ) < 2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ)))
    (lam : ℕ → ℝ) (a : ℝ)
    (m : Finset.Icc 2 ⌊Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌋₊) :
    weilLogShiftWindowPanel (base + 1) (fun j => lam j + if j = n then a else 0) m =
      weilLogShiftWindowPanel (base + 1) lam m +
        ((a * (2 * truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ)
          (Real.log n - Real.log m.1) / Real.sqrt n) : ℝ) : ℂ) := by
  let v : ℕ → ℝ := fun j => lam j + if j = n then a else 0
  let g := EF.weilTest
    (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log m.1))
    (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log m.1))
  have hE := two_lt_exp_window base
  have hn2 : 2 ≤ n := by exact_mod_cast hE.le.trans hlo.le
  have hn4 : (n : ℝ) ≤ Real.exp (4 * ((base + 1 : ℕ) : ℝ)) := by
    rw [show 4 * ((base + 1 : ℕ) : ℝ) =
      2 * ((base + 1 : ℕ) : ℝ) + 2 * ((base + 1 : ℕ) : ℝ) by ring, Real.exp_add]
    nlinarith only [hE, hhi]
  have hmem : n ∈ Finset.Icc 2 ⌊Real.exp (4 * ((base + 1 : ℕ) : ℝ))⌋₊ :=
    Finset.mem_Icc.mpr ⟨hn2, Nat.le_floor hn4⟩
  have hsum : (∑ j ∈ Finset.Icc 2 ⌊Real.exp (4 * ((base + 1 : ℕ) : ℝ))⌋₊,
      (((v j - lam j) / Real.sqrt j : ℝ) : ℂ) * (g (Real.log j) + g (-Real.log j))) =
      ((a / Real.sqrt n : ℝ) : ℂ) *
        ((-2 * truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ)
          (Real.log n - Real.log m.1) : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single n]
    · simp only [v, ite_true, add_sub_cancel_left]
      rw [(outerSpike_kernel base n hlo hhi m).2]
    · intro j _ hj
      simp only [v, if_neg hj, add_zero, sub_self, zero_div, Complex.ofReal_zero, zero_mul]
    · intro hn
      exact False.elim (hn hmem)
  have hd := weilLogShiftWindowPanel_sub (base + 1) v lam m
  change weilLogShiftWindowPanel (base + 1) v m - weilLogShiftWindowPanel (base + 1) lam m =
    -∑ j ∈ Finset.Icc 2 ⌊Real.exp (4 * ((base + 1 : ℕ) : ℝ))⌋₊,
      (((v j - lam j) / Real.sqrt j : ℝ) : ℂ) * (g (Real.log j) + g (-Real.log j)) at hd
  rw [hsum] at hd
  change weilLogShiftWindowPanel (base + 1) v m = _
  calc _ = weilLogShiftWindowPanel (base + 1) lam m +
      (weilLogShiftWindowPanel (base + 1) v m - weilLogShiftWindowPanel (base + 1) lam m) := by ring
    _ = _ := by rw [hd]; push_cast; ring

/-- A prescribed common outer coordinate suffices to lift every entry of one finite panel. -/
theorem exists_weilLogShiftWindowPanel_outerSpike (base n : ℕ)
    (hlo : Real.exp (2 * ((base + 1 : ℕ) : ℝ)) < (n : ℝ))
    (hhi : (n : ℝ) < 2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ)))
    (lam : ℕ → ℝ) (r : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ m, r < (weilLogShiftWindowPanel (base + 1)
      (fun j => lam j + if j = n then a else 0) m).re := by
  classical
  let slope (m : Finset.Icc 2 ⌊Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌋₊) : ℝ :=
    2 * truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ) (Real.log n - Real.log m.1) / Real.sqrt n
  let cost (m : Finset.Icc 2 ⌊Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌋₊) : ℝ :=
    max ((r - (weilLogShiftWindowPanel (base + 1) lam m).re) / slope m) 0
  let a : ℝ := 1 + ∑ m, cost m
  have hcost (m) : 0 ≤ cost m := le_max_right _ _
  have ha : 0 < a := by
    have hs : 0 ≤ ∑ m, cost m := Finset.sum_nonneg fun m _ => hcost m
    dsimp only [a]
    linarith only [hs]
  have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hlo
  have hslope (m) : 0 < slope m :=
    div_pos (mul_pos (by norm_num) (outerSpike_kernel base n hlo hhi m).1)
      (Real.sqrt_pos.mpr hn0)
  refine ⟨a, ha, ?_⟩
  intro m
  have hsingle : cost m ≤ ∑ j, cost j :=
    Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ m)
  have hratio : (r - (weilLogShiftWindowPanel (base + 1) lam m).re) / slope m < a := by
    have hmax : (r - (weilLogShiftWindowPanel (base + 1) lam m).re) / slope m ≤ cost m :=
      le_max_left _ _
    dsimp only [a]
    linarith only [hsingle, hmax]
  have hg := congrArg Complex.re (weilLogShiftWindowPanel_outerSpike base n hlo hhi lam a m)
  simp only [Complex.add_re, Complex.ofReal_re] at hg
  have hr := (div_lt_iff₀ (hslope m)).mp hratio
  change r - (weilLogShiftWindowPanel (base + 1) lam m).re <
    a * (2 * truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ)
      (Real.log n - Real.log m.1) / Real.sqrt n) at hr
  linarith only [hg, hr]

private theorem firstProbe_pair_eq_zero (base n : ℕ)
    (hn : weilLogShiftSharpLiftIndex base < n) :
    EF.weilTest (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2))
        (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2)) (Real.log n) +
      EF.weilTest (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2))
        (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2)) (-Real.log n) = 0 := by
  have hnE := (weilLogShiftSharpLiftIndex_bounds base).2.2 n |>.mp hn
  have hy := Real.log_le_log
    (by positivity : 0 < 2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ))) hnE
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne', Real.log_exp] at hy
  have hc := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h0 : truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ) (Real.log n) = 0 := by
    apply truncatedRiemannAutocorr_eq_zero
    have ha := le_abs_self (Real.log (n : ℝ))
    linarith only [hy, hc, ha]
  have h1 : truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ) (Real.log n + Real.log 2) = 0 := by
    apply truncatedRiemannAutocorr_eq_zero
    have ha := le_abs_self (Real.log (n : ℝ) + Real.log 2)
    linarith only [hy, hc, ha]
  have h2 : truncatedRiemannAutocorr ((base + 1 : ℕ) : ℝ) (Real.log n - Real.log 2) = 0 := by
    apply truncatedRiemannAutocorr_eq_zero
    have ha := le_abs_self (Real.log (n : ℝ) - Real.log 2)
    linarith only [hy, ha]
  rw [logShiftRiemannPair_eq, h0, h1, h2]
  norm_num

/-- The m=2 probe depends exactly on a finite head: all coefficients beyond the sharp
integer boundary are invisible even when the replacement tail is arbitrary. -/
theorem weilLogShift_firstProbe_tail_invariant (base : ℕ) (lam mu : ℕ → ℝ)
    (hhead : ∀ n : ℕ, n ≤ weilLogShiftSharpLiftIndex base → lam n = mu n) :
    weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2))
      (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2))) =
    weilFullFunctional mu (EF.weilTest
      (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2))
      (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2))) := by
  let m : Finset.Icc 2 ⌊Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌋₊ :=
    ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_floor (two_lt_exp_window base).le⟩⟩
  let g := EF.weilTest (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2))
    (logShiftRiemannDifference ((base + 1 : ℕ) : ℝ) (Real.log 2))
  have hsum : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (4 * ((base + 1 : ℕ) : ℝ))⌋₊,
      (((mu n - lam n) / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n))) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    by_cases hn : n ≤ weilLogShiftSharpLiftIndex base
    · rw [hhead n hn]
      simp only [sub_self, zero_div, Complex.ofReal_zero, zero_mul]
    · rw [firstProbe_pair_eq_zero base n (lt_of_not_ge hn), mul_zero]
  have hd := weilLogShiftWindowPanel_sub (base + 1) mu lam m
  change weilLogShiftWindowPanel (base + 1) mu m - weilLogShiftWindowPanel (base + 1) lam m =
    -∑ n ∈ Finset.Icc 2 ⌊Real.exp (4 * ((base + 1 : ℕ) : ℝ))⌋₊,
      (((mu n - lam n) / Real.sqrt n : ℝ) : ℂ) * (g (Real.log n) + g (-Real.log n)) at hd
  rw [hsum, neg_zero] at hd
  exact (sub_eq_zero.mp hd).symm

/-- Universal strict tail-panel completion while preserving a prescribed finite prefix. -/
def WeilTailPanelHeadCompletable (base B : ℕ) : Prop :=
  ∀ (lam height : ℕ → ℝ), ∃ mu : ℕ → ℝ,
    (∀ n, lam n ≤ mu n) ∧ (∀ n : ℕ, n ≤ B → mu n = lam n) ∧
    ∀ k : ℕ, base + 1 ≤ k → ∀ m, height k < (weilLogShiftWindowPanel k mu m).re

private theorem sharpIndex_lt_next_window (base : ℕ) :
    (weilLogShiftSharpLiftIndex base : ℝ) < Real.exp (2 * ((base + 2 : ℕ) : ℝ)) := by
  have he : (2 : ℝ) < Real.exp 2 := by simpa using two_lt_exp_window 0
  have h := mul_lt_mul_of_pos_right he (Real.exp_pos (2 * ((base + 1 : ℕ) : ℝ)))
  apply (weilLogShiftSharpLiftIndex_bounds base).2.1.trans
  calc _ < Real.exp 2 * Real.exp (2 * ((base + 1 : ℕ) : ℝ)) := h
    _ = Real.exp (2 * ((base + 2 : ℕ) : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring

/-- Sharp classification: arbitrary simultaneous tail-panel heights are attainable for
every prescribed prefix precisely when its last index precedes the last active first-probe atom. -/
theorem weilTailPanelHeadCompletable_iff (base B : ℕ) :
    WeilTailPanelHeadCompletable base B ↔ B < weilLogShiftSharpLiftIndex base := by
  unfold WeilTailPanelHeadCompletable
  constructor
  · intro h
    by_contra hB
    have hNB : weilLogShiftSharpLiftIndex base ≤ B := le_of_not_gt hB
    let m : Finset.Icc 2 ⌊Real.exp (2 * ((base + 1 : ℕ) : ℝ))⌋₊ :=
      ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_floor (two_lt_exp_window base).le⟩⟩
    let seed : ℕ → ℝ := fun _ => 0
    let r : ℝ := (weilLogShiftWindowPanel (base + 1) seed m).re
    obtain ⟨mu, _, hhead, hpanel⟩ := h seed (fun _ => r)
    have heq := weilLogShift_firstProbe_tail_invariant base seed mu
      (fun n hn => (hhead n (hn.trans hNB)).symm)
    change weilLogShiftWindowPanel (base + 1) seed m =
      weilLogShiftWindowPanel (base + 1) mu m at heq
    have hp := hpanel (base + 1) (le_refl _) m
    dsimp only [r] at hp
    rw [← heq] at hp
    exact (lt_irrefl _) hp
  · intro hB lam height
    have hN := weilLogShiftSharpLiftIndex_bounds base
    obtain ⟨a, ha, hfirst⟩ := exists_weilLogShiftWindowPanel_outerSpike base
      (weilLogShiftSharpLiftIndex base) hN.1 hN.2.1 lam (height (base + 1))
    let v : ℕ → ℝ := fun n => lam n + if n = weilLogShiftSharpLiftIndex base then a else 0
    have hlv (n : ℕ) : lam n ≤ v n := by
      dsimp only [v]
      split_ifs <;> linarith only [ha]
    obtain ⟨mu, hvmu, hhead, hpanel⟩ := exists_weilLogShiftTail_positive_completion (base + 1) v height
    refine ⟨mu, fun n => (hlv n).trans (hvmu n), ?_, ?_⟩
    · intro n hn
      have hnN : n < weilLogShiftSharpLiftIndex base := hn.trans_lt hB
      have hnr : (n : ℝ) < (weilLogShiftSharpLiftIndex base : ℝ) := by exact_mod_cast hnN
      have h := hhead n (hnr.trans (sharpIndex_lt_next_window base)).le
      simpa only [v, if_neg hnN.ne, add_zero] using h
    · intro k hk m
      by_cases hk0 : k = base + 1
      · subst k
        apply (hfirst m).trans_le
        apply weilLogShiftWindowPanel_outer_mono _ v mu hvmu ?_ m
        intro n hn
        have hb : Real.exp (2 * ((base + 1 : ℕ) : ℝ)) ≤
            Real.exp (2 * ((base + 2 : ℕ) : ℝ)) := by
          apply Real.exp_le_exp.mpr
          push_cast
          linarith
        exact (hhead n (hn.trans hb)).symm
      · exact hpanel k (by omega) m

end RHTower

end
