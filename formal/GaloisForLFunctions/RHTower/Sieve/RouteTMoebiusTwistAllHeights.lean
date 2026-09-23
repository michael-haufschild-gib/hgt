import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusContour
import GaloisForLFunctions.RHTower.Sieve.SmoothVsSharp

/-!
# The Route-T twisted Möbius contour at every frequency

`Sieve/RouteTMoebiusContour.exists_norm_tsum_moebiusTwist_smoothWeight_le_routeT` requires the twist
to exceed the Perron half-height by the fixed base ordinate, so that every ordinate of the shifted
rectangle lies in the quantitative high-ordinate region.  That hypothesis is not needed: on the
remaining ordinates `|Im s| ≤ routeTInverseBaseHeight` the rectangle sits inside a fixed compact box
on which `1/ζ` is bounded by an absolute constant
(`Sieve/RouteTMoebiusContour.exists_bound_invZeta_fixed_box`, valid on `1 − δ ≤ Re s ≤ 2`), so the
edge constant is `max M (routeTContourEdgeBound A (|τ|+U))` on all three shifted edges.

The right abscissa is left free.  Taking it to be `routeTContourRight A (|τ|+U) = 1 + Δ`, as the
separated version does, costs a factor `(N+H)^Δ = exp(log N/(log(|τ|+U))^{9/10})`, harmless only
when `log(|τ|+U) ≍ log N`; for lower frequencies the abscissa must be pulled back towards
`1 + 1/log N`, and the rectangle bound is then `(N+H)^{1−shift}` up to polylogarithms.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1600000 in
/-- **Route-T four-edge Perron bound for twisted smoothed Möbius sums, at every frequency.** -/
theorem exists_norm_tsum_moebiusTwist_smoothWeight_le_routeT_allHeights :
    ∃ (A C C' M δ : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M ∧ 0 < δ ∧
      ∀ N H τ U d : ℝ, 0 < N → 0 < H → 1 ≤ U → 1 < d → d ≤ 2 →
      routeTInverseBaseHeight ≤ |τ| + U →
      d ≤ routeTContourRight A (|τ| + U) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          moebiusTwist τ n *
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * ((Real.exp (22 / 4) * (1 + 1 / (d - 1))) *
              (C / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) * (N + H + 1) ^ d)) / U
          + max M (routeTContourEdgeBound A (|τ| + U)) *
              (C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ) * (N + H + 1) ^ d) / U ^ (0 + 1) *
                (d - routeTContourLeft A δ (|τ| + U))
          + max M (routeTContourEdgeBound A (|τ| + U)) *
              (C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ) * (N + H + 1) ^ d) / U ^ (0 + 1) *
                (d - routeTContourLeft A δ (|τ| + U))
          + max M (routeTContourEdgeBound A (|τ| + U)) *
              (2 * ((N + H) ^ routeTContourLeft A δ (|τ| + U) /
                    routeTContourLeft A δ (|τ| + U))
                + 2 * (C / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) *
                    (N + H + 1) ^ routeTContourLeft A δ (|τ| + U))) := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  obtain ⟨C, hC, hdec1⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨C', hC', hdec0⟩ := exists_bound_mellin_smoothWeight_uniform_upto 0
  obtain ⟨δz, hδz, hzfbox⟩ := exists_zero_free_box routeTInverseBaseHeight
  obtain ⟨δm, hδm, M, hM, hbdbox⟩ :=
    exists_bound_invZeta_fixed_box (by
      have hbase := routeTInverseBaseHeight_ge
      linarith : (0 : ℝ) ≤ routeTInverseBaseHeight)
  refine ⟨A, C, C', M, min δz δm, hC, hC', hM, lt_min hδz hδm, ?_⟩
  intro N H τ U d hN hH hU hd1 hd2 hbase hdright
  set δ : ℝ := min δz δm with hδdef
  have hδ : 0 < δ := lt_min hδz hδm
  set S : ℝ := |τ| + U with hSdef
  set c : ℝ := routeTContourLeft A δ S with hcdef
  set Mh : ℝ := routeTContourEdgeBound A S with hMhdef
  set Mc : ℝ := max M Mh with hMcdef
  set Md : ℝ := Real.exp (22 / 4) * (1 + 1 / (d - 1)) with hMddef
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have hS : routeTInverseBaseHeight ≤ S := by
    rw [hSdef]; exact hbase
  have hc0 : 0 < c := by
    rw [hcdef]; exact routeTContourLeft_pos (A := A) (δ := δ) (T := S)
  have hc1 : c ≤ 1 := by
    rw [hcdef]; exact routeTContourLeft_le_one (A := A) (T := S) hδ
  have hcright : c ≤ routeTContourRight A S := by
    rw [hcdef]; exact routeTContourLeft_le_right (A := A) (T := S) hδ
  have hcd : c ≤ d := by linarith
  have hbox : ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 1 →
      |s.im| ≤ routeTInverseBaseHeight → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hslo hshi him hs1
    refine hzfbox s ?_ hshi him hs1
    have : δ ≤ δz := by rw [hδdef]; exact min_le_left _ _
    linarith
  have hzfS : ∀ s ∈ Set.uIcc c (routeTContourRight A S) ×ℂ Set.uIcc (-S) S,
      s ≠ 1 → riemannZeta s ≠ 0 := by
    rw [hcdef]
    exact routeT_contour_zero_free hA hδ hbox hS
  have hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + U)) (|τ| + U),
      s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hs hs1
    refine hzfS s ?_ hs1
    rw [Complex.mem_reProdIm] at hs ⊢
    refine ⟨?_, ?_⟩
    · rw [Set.uIcc_of_le hcd] at hs
      rw [Set.uIcc_of_le hcright]
      exact ⟨hs.1.1, le_trans hs.1.2 hdright⟩
    · rw [← hSdef] at hs
      exact hs.2
  have hMd : (0 : ℝ) ≤ Md := by
    rw [hMddef]
    have hinv : (0 : ℝ) < 1 / (d - 1) := one_div_pos.2 (by linarith)
    positivity
  have hMh : (0 : ℝ) ≤ Mh := by
    rw [hMhdef, routeTContourEdgeBound]
    exact Real.exp_nonneg _
  have hMc : (0 : ℝ) ≤ Mc := le_trans hM (le_max_left _ _)
  have hcbox : 1 - δm ≤ c := by
    have hshift := routeTContourShift_le_box_half A δ S
    have hδm' : δ ≤ δm := by rw [hδdef]; exact min_le_right _ _
    rw [hcdef, routeTContourLeft]
    linarith
  have hedge : ∀ x y : ℝ, c ≤ x → x ≤ d → |y| ≤ U →
      ‖invZeta ((x : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I)‖ ≤ Mc := by
    intro x y hxlo hxhi hy
    by_cases hylow : |y + τ| ≤ routeTInverseBaseHeight
    · have hre : (((x : ℝ) : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I).re = x := by simp
      have him : (((x : ℝ) : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I).im = y + τ := by simp
      have hlow := hbdbox ((x : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I)
        (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact hylow)
      exact le_trans hlow (le_max_left _ _)
    · have hybase : routeTInverseBaseHeight ≤ |y + τ| := le_of_lt (lt_of_not_ge hylow)
      have hyS : |y + τ| ≤ S := by
        rw [hSdef]
        calc |y + τ| ≤ |y| + |τ| := abs_add_le _ _
          _ ≤ U + |τ| := add_le_add hy le_rfl
          _ = |τ| + U := by ring
      have hne : ((x : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I) ≠ 1 := by
        intro heq
        have him := congrArg Complex.im heq
        simp at him
        rw [him, abs_zero] at hybase
        linarith [routeTInverseBaseHeight_ge]
      rw [norm_invZeta_eq hne]
      have hhigh := norm_inv_riemannZeta_le_routeT_contour hA hybase hyS
        (by rw [← hcdef]; exact hxlo) (le_trans hxhi hdright)
      exact le_trans hhigh (le_max_right _ _)
  have hFd : ∀ y : ℝ,
      ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Md := by
    intro y
    have harg : ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) =
        (d : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg, hMddef]
    exact norm_invZeta_right_le (d := d) (y := y + τ) hd1
  have hFt : ∀ x ∈ Set.Ioc c d,
      ‖invZeta ((x : ℂ) + ((U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc := by
    intro x hx
    have harg : ((x : ℂ) + ((U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I) =
        (x : ℂ) + ((U + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg]
    exact hedge x U hx.1.le hx.2 (by rw [abs_of_nonneg hU0])
  have hFb : ∀ x ∈ Set.Ioc c d,
      ‖invZeta ((x : ℂ) + ((-U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc := by
    intro x hx
    have harg : ((x : ℂ) + ((-U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I) =
        (x : ℂ) + (((-U) + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg]
    exact hedge x (-U) hx.1.le hx.2 (by rw [abs_neg, abs_of_nonneg hU0])
  have hFc : ∀ y ∈ Set.Icc (-U) U,
      ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc := by
    intro y hy
    have harg : ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) =
        (c : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [harg]
    exact hedge c y le_rfl hcd (abs_le.2 hy)
  have hFccont : ContinuousOn
      (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      (Set.uIcc (-U) U) :=
    continuousOn_invZetaTwist_left_line τ hU0 hc1 hd1.le hzf
  exact norm_tsum_moebiusTwist_smoothWeight_le_sharp hN hH 0 τ hd1 hc0 hcd hU
    hMd hMc hMc hzf hFd hFt hFb hFc hFccont
    (fun s hs hsd => hdec1 N H hN hH d s hs hsd)
    (fun s hs hsd => hdec0 N H hN hH d s hs hsd)
    (fun s hs hsc => hdec1 N H hN hH c s hs hsc)

end

end RHTower.Sieve

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- The right-hand side of the all-frequency Route-T rectangle bound. -/
def routeTMoebiusAllHeightsSmoothBound (A C C' M δ N H τ U d : ℝ) : ℝ :=
  2 * ((Real.exp (22 / 4) * (1 + 1 / (d - 1))) *
        (C / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) * (N + H + 1) ^ d)) / U
    + max M (routeTContourEdgeBound A (|τ| + U)) *
        (C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ) * (N + H + 1) ^ d) / U ^ (0 + 1) *
          (d - routeTContourLeft A δ (|τ| + U))
    + max M (routeTContourEdgeBound A (|τ| + U)) *
        (C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ) * (N + H + 1) ^ d) / U ^ (0 + 1) *
          (d - routeTContourLeft A δ (|τ| + U))
    + max M (routeTContourEdgeBound A (|τ| + U)) *
        (2 * ((N + H) ^ routeTContourLeft A δ (|τ| + U) /
              routeTContourLeft A δ (|τ| + U))
          + 2 * (C / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) *
              (N + H + 1) ^ routeTContourLeft A δ (|τ| + U)))

/-- **The sharp twisted Mertens sum on the all-frequency Route-T contour.**  Removing the smoothing
costs the window length `H + 1`. -/
theorem exists_norm_sum_moebiusTwist_le_routeTSharp_allHeights :
    ∃ (A C C' M δ : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M ∧ 0 < δ ∧
      ∀ N H τ U d : ℝ, 0 < N → 0 < H → 1 ≤ U → 1 < d → d ≤ 2 →
      routeTInverseBaseHeight ≤ |τ| + U →
      d ≤ routeTContourRight A (|τ| + U) →
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n‖
        ≤ routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ U d / (2 * Real.pi) + (H + 1) := by
  obtain ⟨A, C, C', M, δ, hC, hC', hM, hδ, hmain⟩ :=
    exists_norm_tsum_moebiusTwist_smoothWeight_le_routeT_allHeights
  refine ⟨A, C, C', M, δ, hC, hC', hM, hδ, ?_⟩
  intro N H τ U d hN hH hU hd1 hd2 hbase hdright
  set S : ℂ := ∑' n : ℕ, moebiusTwist τ n *
    ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) with hSdef
  set P : ℂ := ∑ n ∈ Finset.range (⌊N⌋₊ + 1), moebiusTwist τ n with hPdef
  have hraw := hmain N H τ U d hN hH hU hd1 hd2 hbase hdright
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsmul : ‖(2 * Real.pi : ℝ) • S‖ = 2 * Real.pi * ‖S‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpi.le]
  have hS : ‖S‖ ≤ routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ U d / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi, mul_comm, ← hsmul]
    simpa only [routeTMoebiusAllHeightsSmoothBound, hSdef] using hraw
  have hcmp : ‖S - P‖ ≤ H + 1 := by
    simpa only [hSdef, hPdef] using norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one
      (a := moebiusTwist τ) (norm_moebiusTwist_le_one τ) hN hH
  have htri : ‖P‖ ≤ ‖S‖ + ‖S - P‖ := by
    have := norm_sub_le S (S - P)
    simpa using this
  exact htri.trans (add_le_add hS hcmp)

end

end RHTower.Sieve
