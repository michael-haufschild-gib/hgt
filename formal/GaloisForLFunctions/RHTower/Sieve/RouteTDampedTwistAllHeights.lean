import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusTwistAllHeights
import GaloisForLFunctions.RHTower.Sieve.DampedTwistSharpSubstitution
import GaloisForLFunctions.RHTower.Sieve.DampedTwistContourBound
import GaloisForLFunctions.RHTower.Sieve.DampedShiftBound
import GaloisForLFunctions.RHTower.Sieve.DampedSaving
import GaloisForLFunctions.RHTower.Sieve.RouteTContourRateBounds

/-!
# The Route-T contour for the Ramaré cofactor, at every frequency

`1/(ω_P(n)+1) = ∫₀¹ u^{ω_P(n)} du` turns the Ramaré cofactor into an average of the damped twisted
Möbius coefficients, whose Dirichlet series is `(1/ζ(s))·∏_{p∈P}(1−u p^{−s})/(1−p^{−s})`.  The
correction factor is bounded on the whole rectangle by
`Sieve/DampedCorrBound.dampedCorrBound P c = ∏_{p∈P}(1+p^{−c})/(1−p^{−c})` as soon as the left
abscissa `c` is at least one half, which `Sieve/RouteTContourRateBounds.routeTContourLeft_ge_half`
supplies unconditionally.  So the all-frequency rectangle bound of
`Sieve/RouteTMoebiusTwistAllHeights` carries over verbatim with every edge constant multiplied by
that one factor.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Route-T four-edge Perron bound for the damped twisted Möbius sum, at every frequency.** -/
theorem exists_norm_tsum_dampedTwist_smoothWeight_le_routeT_allHeights :
    ∃ (A C C' M δ : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M ∧ 0 < δ ∧
      ∀ (P : Finset ℕ) (u N H τ U d : ℝ), (∀ q ∈ P, q.Prime) → 0 ≤ u → u ≤ 1 →
      0 < N → 0 < H → 1 ≤ U → 1 < d → d ≤ 2 →
      routeTInverseBaseHeight ≤ |τ| + U →
      d ≤ routeTContourRight A (|τ| + U) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P u τ n *
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * ((Real.exp (22 / 4) * (1 + 1 / (d - 1))
                * dampedCorrBound P (routeTContourLeft A δ (|τ| + U))) *
              (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ d)) / U
          + (max M (routeTContourEdgeBound A (|τ| + U))
                * dampedCorrBound P (routeTContourLeft A δ (|τ| + U))) *
              (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d) / U ^ (0 + 1) *
                (d - routeTContourLeft A δ (|τ| + U))
          + (max M (routeTContourEdgeBound A (|τ| + U))
                * dampedCorrBound P (routeTContourLeft A δ (|τ| + U))) *
              (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d) / U ^ (0 + 1) *
                (d - routeTContourLeft A δ (|τ| + U))
          + (max M (routeTContourEdgeBound A (|τ| + U))
                * dampedCorrBound P (routeTContourLeft A δ (|τ| + U))) *
              (2 * ((N + H) ^ routeTContourLeft A δ (|τ| + U) /
                    routeTContourLeft A δ (|τ| + U))
                + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 *
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
  intro P u N H τ U d hPprime hu0 hu1 hN hH hU hd1 hd2 hbase hdright
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  set δ : ℝ := min δz δm with hδdef
  have hδ : 0 < δ := lt_min hδz hδm
  set S : ℝ := |τ| + U with hSdef
  set c : ℝ := routeTContourLeft A δ S with hcdef
  set Mh : ℝ := routeTContourEdgeBound A S with hMhdef
  set Mc : ℝ := max M Mh with hMcdef
  set Kd : ℝ := dampedCorrBound P c with hKddef
  set Md : ℝ := Real.exp (22 / 4) * (1 + 1 / (d - 1)) with hMddef
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have hS : routeTInverseBaseHeight ≤ S := by rw [hSdef]; exact hbase
  have hc12 : (1 : ℝ) / 2 ≤ c := by rw [hcdef]; exact routeTContourLeft_ge_half A δ S
  have hc0 : (0 : ℝ) < c := by linarith
  have hc1 : c ≤ 1 := by rw [hcdef]; exact routeTContourLeft_le_one hδ
  have hcright : c ≤ routeTContourRight A S := by
    rw [hcdef]; exact routeTContourLeft_le_right (A := A) (T := S) hδ
  have hcd : c ≤ d := by linarith
  have hKd0 : (0 : ℝ) ≤ Kd := by rw [hKddef]; exact dampedCorrBound_nonneg hP2 hc12
  have hbox : ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ 1 →
      |s.im| ≤ routeTInverseBaseHeight → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hslo hshi him hs1
    refine hzfbox s ?_ hshi him hs1
    have : δ ≤ δz := by rw [hδdef]; exact min_le_left _ _
    linarith
  have hzfS : ∀ s ∈ Set.uIcc c (routeTContourRight A S) ×ℂ Set.uIcc (-S) S,
      s ≠ 1 → riemannZeta s ≠ 0 := by
    rw [hcdef]; exact routeT_contour_zero_free hA hδ hbox hS
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
  have hMd0 : (0 : ℝ) ≤ Md := by
    rw [hMddef]
    have hinv : (0 : ℝ) < 1 / (d - 1) := one_div_pos.2 (by linarith)
    positivity
  have hMh0 : (0 : ℝ) ≤ Mh := by
    rw [hMhdef, routeTContourEdgeBound]; exact Real.exp_nonneg _
  have hMc0 : (0 : ℝ) ≤ Mc := le_trans hM (le_max_left _ _)
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
      ‖dampedInvZeta P u ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Md * Kd := by
    intro y
    have hre : (((d : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I).re = d := by simp
    have harg : ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) =
        (d : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hbase' : ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Md := by
      rw [harg, hMddef]
      exact norm_invZeta_right_le (d := d) (y := y + τ) hd1
    rw [hKddef]
    exact norm_dampedInvZeta_shift_le hP2 hu0 hu1 hc12 (by rw [hre]; exact hcd) τ hMd0 hbase'
  have hFt : ∀ x ∈ Set.Ioc c d,
      ‖dampedInvZeta P u ((x : ℂ) + ((U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖
        ≤ Mc * Kd := by
    intro x hx
    have hre : (((x : ℝ) : ℂ) + ((U : ℝ) : ℂ) * Complex.I).re = x := by simp
    have harg : ((x : ℂ) + ((U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I) =
        (x : ℂ) + ((U + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hbase' : ‖invZeta ((x : ℂ) + ((U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc := by
      rw [harg]
      exact hedge x U hx.1.le hx.2 (by rw [abs_of_nonneg hU0])
    rw [hKddef]
    exact norm_dampedInvZeta_shift_le hP2 hu0 hu1 hc12 (by rw [hre]; exact hx.1.le) τ hMc0 hbase'
  have hFb : ∀ x ∈ Set.Ioc c d,
      ‖dampedInvZeta P u ((x : ℂ) + ((-U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖
        ≤ Mc * Kd := by
    intro x hx
    have hre : (((x : ℝ) : ℂ) + ((-U : ℝ) : ℂ) * Complex.I).re = x := by simp
    have harg : ((x : ℂ) + ((-U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I) =
        (x : ℂ) + (((-U) + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hbase' : ‖invZeta ((x : ℂ) + ((-U : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖
        ≤ Mc := by
      rw [harg]
      exact hedge x (-U) hx.1.le hx.2 (by rw [abs_neg, abs_of_nonneg hU0])
    rw [hKddef]
    exact norm_dampedInvZeta_shift_le hP2 hu0 hu1 hc12 (by rw [hre]; exact hx.1.le) τ hMc0 hbase'
  have hFc : ∀ y ∈ Set.Icc (-U) U,
      ‖dampedInvZeta P u ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖
        ≤ Mc * Kd := by
    intro y hy
    have hre : (((c : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I).re = c := by simp
    have harg : ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) =
        (c : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hbase' : ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc := by
      rw [harg]
      exact hedge c y le_rfl hcd (abs_le.2 hy)
    rw [hKddef]
    exact norm_dampedInvZeta_shift_le hP2 hu0 hu1 hc12 (by rw [hre]) τ hMc0 hbase'
  have hFccont : ContinuousOn
      (fun y : ℝ => dampedInvZeta P u ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      (Set.uIcc (-U) U) :=
    continuousOn_dampedInvZetaTwist_left_line hP2 u τ hU0 hc0 hc1 hd1.le hzf
  exact norm_tsum_dampedTwist_smoothWeight_le_sharp hPprime hu0 hu1 hN hH 0 τ hd1 hc0 hcd hU
    (by positivity) (by positivity) (by positivity) hzf hFd hFt hFb hFc hFccont
    (fun s hs hsd => hdec1 N H hN hH d s hs hsd)
    (fun s hs hsd => hdec0 N H hN hH d s hs hsd)
    (fun s hs hsc => hdec1 N H hN hH c s hs hsc)

end

end RHTower.Sieve

namespace RHTower.Sieve

open Complex Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- The right-hand side of the all-frequency Route-T rectangle bound for the damped sum. -/
def routeTDampedAllHeightsSmoothBound (A C C' M δ : ℝ) (P : Finset ℕ) (N H τ U d : ℝ) : ℝ :=
  2 * ((Real.exp (22 / 4) * (1 + 1 / (d - 1))
          * dampedCorrBound P (routeTContourLeft A δ (|τ| + U))) *
        (C / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ d)) / U
    + (max M (routeTContourEdgeBound A (|τ| + U))
          * dampedCorrBound P (routeTContourLeft A δ (|τ| + U))) *
        (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d) / U ^ (0 + 1) *
          (d - routeTContourLeft A δ (|τ| + U))
    + (max M (routeTContourEdgeBound A (|τ| + U))
          * dampedCorrBound P (routeTContourLeft A δ (|τ| + U))) *
        (C' / H ^ 1 * (N + H + 1) ^ 1 * (N + H + 1) ^ d) / U ^ (0 + 1) *
          (d - routeTContourLeft A δ (|τ| + U))
    + (max M (routeTContourEdgeBound A (|τ| + U))
          * dampedCorrBound P (routeTContourLeft A δ (|τ| + U))) *
        (2 * ((N + H) ^ routeTContourLeft A δ (|τ| + U) /
              routeTContourLeft A δ (|τ| + U))
          + 2 * (C / H ^ 2 * (N + H + 1) ^ 2 *
              (N + H + 1) ^ routeTContourLeft A δ (|τ| + U)))

/-- **The sharp damped twisted sum on the all-frequency Route-T contour.** -/
theorem exists_norm_sum_dampedTwist_le_routeTSharp_allHeights :
    ∃ (A C C' M δ : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M ∧ 0 < δ ∧
      ∀ (P : Finset ℕ) (u N H τ U d : ℝ), (∀ q ∈ P, q.Prime) → 0 ≤ u → u ≤ 1 →
      0 < N → 0 < H → 1 ≤ U → 1 < d → d ≤ 2 →
      routeTInverseBaseHeight ≤ |τ| + U →
      d ≤ routeTContourRight A (|τ| + U) →
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedTwist P u τ n‖
        ≤ routeTDampedAllHeightsSmoothBound A C C' M δ P N H τ U d / (2 * Real.pi) + (H + 1) := by
  obtain ⟨A, C, C', M, δ, hC, hC', hM, hδ, hmain⟩ :=
    exists_norm_tsum_dampedTwist_smoothWeight_le_routeT_allHeights
  refine ⟨A, C, C', M, δ, hC, hC', hM, hδ, ?_⟩
  intro P u N H τ U d hPprime hu0 hu1 hN hH hU hd1 hd2 hbase hdright
  set S : ℂ := ∑' n : ℕ, dampedTwist P u τ n *
    ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) with hSdef
  set Pr : ℂ := ∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedTwist P u τ n with hPrdef
  have hraw := hmain P u N H τ U d hPprime hu0 hu1 hN hH hU hd1 hd2 hbase hdright
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsmul : ‖(2 * Real.pi : ℝ) • S‖ = 2 * Real.pi * ‖S‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpi.le]
  have hS : ‖S‖ ≤ routeTDampedAllHeightsSmoothBound A C C' M δ P N H τ U d / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi, mul_comm, ← hsmul]
    simpa only [routeTDampedAllHeightsSmoothBound, hSdef] using hraw
  have hcmp : ‖S - Pr‖ ≤ H + 1 := by
    simpa only [hSdef, hPrdef] using norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one
      (a := dampedTwist P u τ) (norm_dampedTwist_le_one hu0 hu1 τ) hN hH
  have htri : ‖Pr‖ ≤ ‖S‖ + ‖S - Pr‖ := by
    have := norm_sub_le S (S - Pr)
    simpa using this
  exact htri.trans (add_le_add hS hcmp)

end

end RHTower.Sieve
