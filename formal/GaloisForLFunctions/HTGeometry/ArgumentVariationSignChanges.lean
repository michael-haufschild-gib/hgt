import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Argument variation is controlled by the sign changes of the real part

If a nonvanishing continuous curve has real part of constant sign on a connected set, then a
continuous logarithm of the curve has imaginary part confined to one strip
`(2kπ − π/2, 2kπ + π/2)` or `(2kπ + π/2, 2kπ + 3π/2)`, because the real part is
`exp(Re L) cos(Im L)` and the image of a connected set under a continuous real function is an
interval.  An interval avoiding every zero of the cosine has length at most `π`.

Splitting a compact interval at the zeros of the real part therefore bounds the total variation of
the argument by `π` per cell.  That is Backlund's step: a bound on the number of sign changes of
`Re f` is a bound on the argument variation of `f`.
-/

open Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## An interval of length more than `π` meets a zero of the cosine -/

theorem exists_cos_eq_zero_of_pi_lt {x y : ℝ} (h : x + Real.pi < y) :
    ∃ z ∈ Icc x y, Real.cos z = 0 := by
  set k : ℤ := ⌈(x - Real.pi / 2) / Real.pi⌉ with hk
  refine ⟨Real.pi / 2 + k * Real.pi, ⟨?_, ?_⟩, ?_⟩
  · have h1 : (x - Real.pi / 2) / Real.pi ≤ (k : ℝ) := Int.le_ceil _
    rw [div_le_iff₀ Real.pi_pos] at h1
    linarith
  · have h2 : (k : ℝ) < (x - Real.pi / 2) / Real.pi + 1 := Int.ceil_lt_add_one _
    rw [div_add' _ _ _ Real.pi_pos.ne', lt_div_iff₀ Real.pi_pos] at h2
    linarith
  · rw [Real.cos_eq_zero_iff]
    exact ⟨k, by ring⟩

/-! ## The strip confinement -/

/-- **Constant sign of the real part confines the argument to a strip of width `π`.** -/
theorem abs_im_sub_le_pi_of_re_ne_zero {J : Set ℝ} (hJ : IsPreconnected J)
    {γ L : ℝ → ℂ} (hL : ContinuousOn L J)
    (hexp : ∀ t ∈ J, Complex.exp (L t) = γ t)
    (hre : ∀ t ∈ J, (γ t).re ≠ 0) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    |(L t).im - (L s).im| ≤ Real.pi := by
  set f : ℝ → ℝ := fun u => (L u).im with hf
  have hfc : ContinuousOn f J := Complex.continuous_im.comp_continuousOn hL
  have hcos : ∀ u ∈ J, Real.cos (f u) ≠ 0 := by
    intro u hu hcu
    refine hre u hu ?_
    have hval : (γ u).re = Real.exp (L u).re * Real.cos (L u).im := by
      rw [← hexp u hu, Complex.exp_re]
    rw [hval, hf] at *
    simp only at hcu
    rw [hcu, mul_zero]
  by_contra hcon
  rw [not_le] at hcon
  have himg : IsPreconnected (f '' J) := hJ.image f hfc
  have hord : OrdConnected (f '' J) := himg.ordConnected
  rcases le_or_gt (f s) (f t) with hst | hst
  · have hgap : f s + Real.pi < f t := by
      rw [abs_of_nonneg (by linarith)] at hcon
      linarith
    obtain ⟨z, hz, hcz⟩ := exists_cos_eq_zero_of_pi_lt hgap
    have hzmem : z ∈ f '' J :=
      hord.out (mem_image_of_mem f hs) (mem_image_of_mem f ht) hz
    obtain ⟨u, hu, hfu⟩ := hzmem
    exact hcos u hu (by rw [hfu, hcz])
  · have hgap : f t + Real.pi < f s := by
      rw [abs_of_neg (by linarith)] at hcon
      linarith
    obtain ⟨z, hz, hcz⟩ := exists_cos_eq_zero_of_pi_lt hgap
    have hzmem : z ∈ f '' J :=
      hord.out (mem_image_of_mem f ht) (mem_image_of_mem f hs) hz
    obtain ⟨u, hu, hfu⟩ := hzmem
    exact hcos u hu (by rw [hfu, hcz])

/-! ## Extension to the closed cell -/

/-- The strip bound extends to the endpoints of a cell whose interior is free of sign changes. -/
theorem abs_im_sub_le_pi_of_re_ne_zero_Ioo {a b : ℝ} (hab : a < b) {γ L : ℝ → ℂ}
    (hL : ContinuousOn L (Icc a b))
    (hexp : ∀ t ∈ Icc a b, Complex.exp (L t) = γ t)
    (hre : ∀ t ∈ Ioo a b, (γ t).re ≠ 0) :
    |(L b).im - (L a).im| ≤ Real.pi := by
  set f : ℝ → ℝ := fun u => (L u).im with hf
  have hfc : ContinuousOn f (Icc a b) := Complex.continuous_im.comp_continuousOn hL
  have hopen : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, |f t - f s| ≤ Real.pi := by
    intro s hs t ht
    refine abs_im_sub_le_pi_of_re_ne_zero (isPreconnected_Ioo)
      (hL.mono Ioo_subset_Icc_self) (fun u hu => hexp u (Ioo_subset_Icc_self hu)) hre hs ht
  have hclosure : Icc a b ⊆ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
  have hstep : ∀ t ∈ Ioo a b, ∀ s ∈ Icc a b, |f t - f s| ≤ Real.pi := by
    intro t ht s hs
    have hne : (𝓝[Ioo a b] s).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hclosure hs)
    have hcont : ContinuousWithinAt (fun u => |f t - f u|) (Ioo a b) s := by
      refine ContinuousWithinAt.mono ?_ Ioo_subset_Icc_self
      exact (continuous_abs.comp_continuousOn ((continuousOn_const).sub hfc)) s hs
    refine le_of_tendsto hcont.tendsto ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hopen u hu t ht
  have hall : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |f t - f s| ≤ Real.pi := by
    intro s hs t ht
    have hne : (𝓝[Ioo a b] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hclosure ht)
    have hcont : ContinuousWithinAt (fun u => |f u - f s|) (Ioo a b) t := by
      refine ContinuousWithinAt.mono ?_ Ioo_subset_Icc_self
      exact (continuous_abs.comp_continuousOn (hfc.sub continuousOn_const)) t ht
    refine le_of_tendsto hcont.tendsto ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hstep u hu s hs
  exact hall a (left_mem_Icc.mpr hab.le) b (right_mem_Icc.mpr hab.le)

/-! ## The cell count -/

/-- **Backlund's step.**  The argument variation across a compact interval is at most `π` times one
more than the number of sign changes of the real part. -/
theorem abs_im_sub_le_of_finite_re_zeros {a b : ℝ} (hab : a ≤ b) {γ L : ℝ → ℂ}
    (hL : ContinuousOn L (Icc a b))
    (hexp : ∀ t ∈ Icc a b, Complex.exp (L t) = γ t)
    (Z : Finset ℝ) (hZ : ∀ t ∈ Ioo a b, (γ t).re = 0 → t ∈ Z) :
    |(L b).im - (L a).im| ≤ (((Z.filter (fun z => z ∈ Ioo a b)).card : ℝ) + 1) * Real.pi := by
  classical
  induction hn : (Z.filter (fun z => z ∈ Ioo a b)).card using Nat.strong_induction_on generalizing
      a b Z with
  | _ n ih =>
      rcases eq_or_lt_of_le hab with heq | hlt
      · subst heq
        simp only [sub_self, abs_zero]
        positivity
      · rcases Finset.eq_empty_or_nonempty (Z.filter (fun z => z ∈ Ioo a b)) with hemp | ⟨c, hc⟩
        · have hre : ∀ t ∈ Ioo a b, (γ t).re ≠ 0 := by
            intro t ht hzero
            have : t ∈ Z.filter (fun z => z ∈ Ioo a b) :=
              Finset.mem_filter.mpr ⟨hZ t ht hzero, ht⟩
            rw [hemp] at this
            exact absurd this (Finset.notMem_empty t)
          refine le_trans (abs_im_sub_le_pi_of_re_ne_zero_Ioo hlt hL hexp hre) ?_
          nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) n]
        · obtain ⟨hcZ, hcIoo⟩ := Finset.mem_filter.mp hc
          have hac : a < c := hcIoo.1
          have hcb : c < b := hcIoo.2
          have hsub1 : Icc a c ⊆ Icc a b := Icc_subset_Icc_right hcb.le
          have hsub2 : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hac.le
          set W : Finset ℝ := Z.erase c with hW
          have hZ1 : ∀ t ∈ Ioo a c, (γ t).re = 0 → t ∈ W := by
            intro t ht hzero
            refine Finset.mem_erase.mpr ⟨ne_of_lt ht.2, hZ t ⟨ht.1, lt_trans ht.2 hcb⟩ hzero⟩
          have hZ2 : ∀ t ∈ Ioo c b, (γ t).re = 0 → t ∈ W := by
            intro t ht hzero
            refine Finset.mem_erase.mpr ⟨ne_of_gt ht.1, hZ t ⟨lt_trans hac ht.1, ht.2⟩ hzero⟩
          set n₁ : ℕ := (W.filter (fun z => z ∈ Ioo a c)).card with hn₁
          set n₂ : ℕ := (W.filter (fun z => z ∈ Ioo c b)).card with hn₂
          have hdisj : Disjoint (W.filter (fun z => z ∈ Ioo a c))
              (W.filter (fun z => z ∈ Ioo c b)) := by
            rw [Finset.disjoint_left]
            intro x hx hx'
            obtain ⟨-, h1⟩ := Finset.mem_filter.mp hx
            obtain ⟨-, h2⟩ := Finset.mem_filter.mp hx'
            exact absurd (lt_trans h1.2 h2.1) (lt_irrefl x)
          have hunion : (W.filter (fun z => z ∈ Ioo a c)) ∪ (W.filter (fun z => z ∈ Ioo c b))
              ⊆ (Z.filter (fun z => z ∈ Ioo a b)).erase c := by
            intro x hx
            rcases Finset.mem_union.mp hx with h | h <;>
              obtain ⟨hxW, hxI⟩ := Finset.mem_filter.mp h
            · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxW).1,
                Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hxW).2,
                  ⟨hxI.1, lt_trans hxI.2 hcb⟩⟩⟩
            · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxW).1,
                Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hxW).2,
                  ⟨lt_trans hac hxI.1, hxI.2⟩⟩⟩
          have hcard : n₁ + n₂ + 1 ≤ n := by
            have h1 : n₁ + n₂ = ((W.filter (fun z => z ∈ Ioo a c))
                ∪ (W.filter (fun z => z ∈ Ioo c b))).card := (Finset.card_union_of_disjoint hdisj).symm
            have h2 : ((W.filter (fun z => z ∈ Ioo a c))
                ∪ (W.filter (fun z => z ∈ Ioo c b))).card
                ≤ ((Z.filter (fun z => z ∈ Ioo a b)).erase c).card := Finset.card_le_card hunion
            have h3 : ((Z.filter (fun z => z ∈ Ioo a b)).erase c).card
                = (Z.filter (fun z => z ∈ Ioo a b)).card - 1 := Finset.card_erase_of_mem hc
            have h4 : 1 ≤ (Z.filter (fun z => z ∈ Ioo a b)).card :=
              Finset.card_pos.mpr ⟨c, hc⟩
            omega
          have hb1 := ih n₁ (by omega) hac.le (hL.mono hsub1)
            (fun t ht => hexp t (hsub1 ht)) W hZ1 rfl
          have hb2 := ih n₂ (by omega) hcb.le (hL.mono hsub2)
            (fun t ht => hexp t (hsub2 ht)) W hZ2 rfl
          have htri : |(L b).im - (L a).im| ≤ |(L c).im - (L a).im| + |(L b).im - (L c).im| := by
            have : (L b).im - (L a).im = ((L c).im - (L a).im) + ((L b).im - (L c).im) := by ring
            rw [this]
            exact abs_add_le _ _
          have hncast : ((n₁ : ℝ) + 1) * Real.pi + ((n₂ : ℝ) + 1) * Real.pi
              ≤ ((n : ℝ) + 1) * Real.pi := by
            have hc1 : (n₁ : ℝ) + (n₂ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hcard
            nlinarith [Real.pi_pos]
          linarith [htri, hb1, hb2, hncast]

end GaloisForLFunctions.HTGeometry
