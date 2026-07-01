/-
# Winding of a loop around a variable basepoint, and its constancy on connected sets

The `Pi1CMinusZero` engine (`π₁(ℂ*) ≅ ℤ` via `degZ`) computes the winding of a loop around `0`. Here
we make the **basepoint variable**: for a loop `L` in `ℂ` and a point `q ∉ image L`, the winding
`windPt L q` is `degZ` of the normalized loop `t ↦ (L t − q)/(L 0 − q)`.

The main theorem, `windPt_const_of_isPreconnected`, is the standard fact that the winding number is
locally constant in the basepoint and therefore **constant across any preconnected set disjoint from
the loop's image**. The engine had winding-around-`0`; this is winding-around-a-connected-region.

This is the missing analytic atom for the connected-case winding parity `hodd`: the level-`n` `ρ`-loop
has image in the exterior `escapeLevel c n`, so both `0` and `c` lie in the connected sublevel set
`C_n = (escapeLevel c n)ᶜ` (`isPreconnected_escapeLevel_compl`), off the loop — hence the loop winds
the same amount around `0` as around `c`.
-/
import GaloisForLFunctions.Bottcher.Pi1CMinusZero

open Topology unitInterval
open Pi1CMinusZero

namespace Bottcher

noncomputable section

/-- The winding loop of `L` around a point `q` (not on `L`): `t ↦ (L t − q)/(L 0 − q)`, based at `1`. -/
def normLoop {a : ℂ} (L : Path a a) (q : ℂ) (hq : ∀ t : I, (L t : ℂ) ≠ q) :
    Path one_cs one_cs where
  toFun t := ⟨((L t : ℂ) - q) / ((L 0 : ℂ) - q),
    div_ne_zero (sub_ne_zero.mpr (hq t)) (sub_ne_zero.mpr (hq 0))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((L.continuous.sub continuous_const).div_const _)
  source' := by
    apply Subtype.ext
    show ((L 0 : ℂ) - q) / ((L 0 : ℂ) - q) = 1
    exact div_self (sub_ne_zero.mpr (hq 0))
  target' := by
    apply Subtype.ext
    show ((L 1 : ℂ) - q) / ((L 0 : ℂ) - q) = 1
    rw [L.target, L.source]
    exact div_self (sub_ne_zero.mpr (by rw [← L.source]; exact hq 0))

/-- Winding number of the loop `L` around the point `q`. -/
def windPt {a : ℂ} (L : Path a a) (q : ℂ) (hq : ∀ t : I, (L t : ℂ) ≠ q) : ℤ :=
  degZ ⟦normLoop L q hq⟧

/-- **Straight-line homotopy invariance of the winding point.** If the whole segment `[x, y]` misses
the image of `L`, the winding of `L` around `x` equals the winding around `y` — the normalized loops
are homotopic through the straight-line family `t ↦ (L t − seg u)/(L 0 − seg u)`. -/
theorem windPt_eq_of_segment {a : ℂ} (L : Path a a) (x y : ℂ)
    (hseg : ∀ (u : I) (t : I), (L t : ℂ) ≠ x + (u : ℝ) • (y - x))
    (hx : ∀ t : I, (L t : ℂ) ≠ x) (hy : ∀ t : I, (L t : ℂ) ≠ y) :
    windPt L x hx = windPt L y hy := by
  set seg : I → ℂ := fun u => x + (u : ℝ) • (y - x) with hsegdef
  have hcontseg : Continuous seg := by fun_prop
  have hden : ∀ u : I, (L 0 : ℂ) - seg u ≠ 0 := fun u => sub_ne_zero.mpr (hseg u 0)
  have hnum : ∀ (u t : I), (L t : ℂ) - seg u ≠ 0 := fun u t => sub_ne_zero.mpr (hseg u t)
  have hseg0 : seg 0 = x := by simp [hsegdef]
  have hseg1 : seg 1 = y := by simp [hsegdef]
  have hHom : Path.Homotopy (normLoop L x hx) (normLoop L y hy) :=
    { toFun := fun p => ⟨((L p.2 : ℂ) - seg p.1) / ((L 0 : ℂ) - seg p.1),
        div_ne_zero (hnum p.1 p.2) (hden p.1)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.div
        · exact (L.continuous.comp continuous_snd).sub (hcontseg.comp continuous_fst)
        · exact continuous_const.sub (hcontseg.comp continuous_fst)
        · exact fun p => hden p.1
      map_zero_left := by
        intro s
        apply Subtype.ext
        show ((L s : ℂ) - seg 0) / ((L 0 : ℂ) - seg 0) = ((L s : ℂ) - x) / ((L 0 : ℂ) - x)
        rw [hseg0]
      map_one_left := by
        intro s
        apply Subtype.ext
        show ((L s : ℂ) - seg 1) / ((L 0 : ℂ) - seg 1) = ((L s : ℂ) - y) / ((L 0 : ℂ) - y)
        rw [hseg1]
      prop' := by
        intro t s hs
        apply Subtype.ext
        rcases hs with hs | hs
        · subst hs
          show ((L 0 : ℂ) - seg t) / ((L 0 : ℂ) - seg t) = ((L 0 : ℂ) - x) / ((L 0 : ℂ) - x)
          rw [div_self (hden t), div_self (sub_ne_zero.mpr (hx 0))]
        · rw [Set.mem_singleton_iff] at hs
          subst hs
          have hL10 : (L 1 : ℂ) = (L 0 : ℂ) := by rw [L.target, L.source]
          show ((L 1 : ℂ) - seg t) / ((L 0 : ℂ) - seg t) = ((L 1 : ℂ) - x) / ((L 0 : ℂ) - x)
          rw [hL10, div_self (hden t), div_self (sub_ne_zero.mpr (hx 0))] }
  exact congrArg degZ (Quotient.sound ⟨hHom⟩)

set_option maxHeartbeats 1000000 in
/-- **Winding around a point is constant across a preconnected set off the loop.** If `S` is
preconnected and disjoint from the image of `L`, then `L` winds the same amount around every point of
`S`. Winding is locally constant on the complement of the compact loop image — small balls are convex,
so `windPt_eq_of_segment` applies — and a locally constant map is constant on a preconnected set. -/
theorem windPt_const_of_isPreconnected {a : ℂ} (L : Path a a)
    {S : Set ℂ} (hS : IsPreconnected S) (hSL : ∀ q ∈ S, ∀ t : I, (L t : ℂ) ≠ q)
    {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) :
    windPt L p (hSL p hp) = windPt L q (hSL q hq) := by
  have hclosed : IsClosed (Set.range (fun t : I => (L t : ℂ))) :=
    (isCompact_range L.continuous).isClosed
  have hLC : IsLocallyConstant (fun z : ↥S => windPt L (↑z) (hSL ↑z z.2)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z
    have hznot : (z : ℂ) ∉ Set.range (fun t : I => (L t : ℂ)) := by
      rintro ⟨t, ht⟩; exact hSL (↑z) z.2 t ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl (↑z) hznot
    refine ⟨Subtype.val ⁻¹' Metric.ball (↑z : ℂ) ε,
      Metric.isOpen_ball.preimage continuous_subtype_val,
      Set.mem_preimage.mpr (Metric.mem_ball_self hε), ?_⟩
    intro w hw
    have hwball : (↑w : ℂ) ∈ Metric.ball (↑z : ℂ) ε := hw
    refine (windPt_eq_of_segment L (↑z) (↑w) ?_ (hSL ↑z z.2) (hSL ↑w w.2)).symm
    intro u t hcontra
    have hsegball : ((↑z : ℂ) + (u : ℝ) • ((↑w : ℂ) - (↑z : ℂ))) ∈ Metric.ball (↑z : ℂ) ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      have h1 : ‖(u : ℝ)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg u)]; exact unitInterval.le_one u
      have h2 : ‖(↑w : ℂ) - (↑z : ℂ)‖ < ε := by
        rw [← dist_eq_norm, ← Metric.mem_ball]; exact hwball
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) h1) h2
    exact hball hsegball ⟨t, hcontra⟩
  haveI : PreconnectedSpace ↥S := isPreconnected_iff_preconnectedSpace.mp hS
  have key : (fun z : ↥S => windPt L (↑z) (hSL ↑z z.2)) ⟨p, hp⟩
           = (fun z : ↥S => windPt L (↑z) (hSL ↑z z.2)) ⟨q, hq⟩ :=
    hLC.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _)
  exact key

end

end Bottcher
