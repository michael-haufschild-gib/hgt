import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussBulkLowEdgeFloor
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceAction

/-!
# Parabolic floor for adaptive mixed arithmetic source action

The drift-removed adaptive mixed/completed source action used by both degree coercivity and
hyperbolic reset has exact reciprocal-mass weight four.  Its normalized Jacobi dissipation
contains four copies of the first lower edge.  Since shifted-Xi normalized `beta_1` has one
degree-independent far-right floor, one universal threshold forces

`1 / 4 < w^(4 : ℕ) * sourceAction(w,n)`

simultaneously in every degree at least two and every sufficiently large positive admission
block.  This is a source-first noncollapse theorem, not a reporter or orientation map.

More sharply, normalized projective Gauss-root spread is strictly dominated by half this
dissipation.  The corpus cofinal-spread theorem therefore upgrades noncollapse to divergence:
along every cofinal mass-and-degree schedule carrying positive actual blocks, the renormalized
literal source action tends to infinity.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Normalized Jacobi dissipation has exact coordinate weight four relative to actual mass. -/
theorem dimensionlessCumulativeJacobiDissipation_eq_fourth_mul_actual
    {w : ℝ} (hw : 1 < w) {n : ℕ}
    (hA : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 4)).PosDef) :
    dimensionlessCumulativeJacobiDissipation w n =
      w ^ (4 : ℕ) * xiShiftedCanonicalAdmissionCumulativeJacobiDissipation (w ^ (2 : ℕ)) n := by
  have hN0 := xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual hw (n + 4) hA
  have hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef := by
    simpa only [xiShiftedFarRightNormalizedHankelMatrix] using hN0
  have halpha : ∀ j, j ≤ n →
      HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j =
        w ^ (2 : ℕ) * HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) j := by
    intro j hj
    have hNj : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hN
    have hAj : (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hA
    change HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j =
      w ^ (2 : ℕ) * HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) j
    exact normalizedAlpha_eq_square_mul_actualAlpha hw j hNj hAj
  have hbeta : ∀ j, j ≤ n + 1 →
      HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) j =
        w ^ (4 : ℕ) * HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) j := by
    intro j hj
    have hNj : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hN
    have hAj : (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hA
    change HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) j =
      w ^ (4 : ℕ) * HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) j
    exact normalizedBeta_eq_fourth_mul_actualBeta hw j hNj hAj
  have hsumAlphaSq :
      (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) j ^ (2 : ℕ)) =
      w ^ (4 : ℕ) * ∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha (xiShiftedRealMomentSequence w) j ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [halpha j (Finset.mem_range.mp hj).le]
    ring
  have hsumBeta :
      (∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) j) =
      w ^ (4 : ℕ) * ∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoBeta (xiShiftedRealMomentSequence w) j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := (Finset.mem_range.mp hj).le
    rw [hbeta j (hjn.trans (Nat.le_succ n))]
  dsimp only [dimensionlessCumulativeJacobiDissipation,
    xiShiftedCanonicalAdmissionCumulativeJacobiDissipation]
  have hseq : (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) =
      xiShiftedRealMomentSequence w := rfl
  rw [hseq]
  rw [hsumAlphaSq, hsumBeta, halpha n le_rfl,
    hbeta n (by omega), hbeta (n + 1) le_rfl]
  ring

/-- Four copies of the first lower Jacobi edge survive inside every degree-at-least-two
dimensionless dissipation. -/
theorem four_mul_lowEdge_lt_dimensionlessCumulativeJacobiDissipation
    {w : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    4 * HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) 1 <
      dimensionlessCumulativeJacobiDissipation w n := by
  let s := xiShiftedFarRightNormalizedMoment w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hbetaNonneg : ∀ j ∈ Finset.range n,
      0 ≤ HTGeometry.monicOrthoBeta s j := by
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by
        have := Finset.mem_range.mp hj
        omega)).le
  have hone : 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hprefix : HTGeometry.monicOrthoBeta s 1 ≤
      ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
    calc
      HTGeometry.monicOrthoBeta s 1 =
          ∑ j ∈ ({1} : Finset ℕ), HTGeometry.monicOrthoBeta s j := by simp
      _ ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.singleton_subset_iff.mpr hone)
          (fun j hj _ => hbetaNonneg j hj)
  have halphaSq : 0 ≤ 2 * (∑ j ∈ Finset.range n,
      HTGeometry.monicOrthoAlpha s j ^ (2 : ℕ)) +
      HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) := by positivity
  have hterminal : 0 < 2 * (n + 1 : ℝ) *
      (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1)) := by
    have hnBeta := HTGeometry.monicOrthoBeta_pos_below hbelow (by omega : 0 < n) (by omega)
    have hn1Beta :=
      HTGeometry.monicOrthoBeta_pos_below hbelow (by omega : 0 < n + 1) (by omega)
    positivity
  unfold dimensionlessCumulativeJacobiDissipation
  dsimp only [s] at hprefix halphaSq hterminal ⊢
  nlinarith

/-- **Uniform parabolic source floor.** One mass threshold works simultaneously in every degree:
after the forced `w^(4 : ℕ)` coordinate renormalization, the literal drift-removed adaptive
mixed/completed arithmetic source action is greater than `1/4`. -/
theorem exists_uniform_adaptiveMixedCompletedSourceAction_parabolicFloor :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ w ≥ W, ∀ n : ℕ, 2 ≤ n →
      (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (n + 4)).PosDef →
      (1 / 4 : ℝ) < w ^ (4 : ℕ) *
        xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w n := by
  have hbeta := tendsto_dimensionless_monicOrthoBeta (n := 1) (by omega)
  rw [monicOrthoBeta_normalizedCentralBinom_one] at hbeta
  have hev : ∀ᶠ w : ℝ in atTop,
      (1 / 16 : ℝ) < HTGeometry.monicOrthoBeta
        (xiShiftedFarRightNormalizedMoment w) 1 :=
    hbeta.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.1 hev
  let W := max W₀ 2
  refine ⟨W, le_max_right _ _, ?_⟩
  intro w hw n hn hA
  have hwW₀ : W₀ ≤ w := le_trans (le_max_left _ _) hw
  have hw1 : 1 < w := lt_of_lt_of_le (by norm_num)
    (le_trans (le_max_right W₀ 2) hw)
  have hN0 := xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual hw1 (n + 4) hA
  have hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef := by
    simpa only [xiShiftedFarRightNormalizedHankelMatrix] using hN0
  have hNsmall : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hN
  have hDlow :=
    four_mul_lowEdge_lt_dimensionlessCumulativeJacobiDissipation hn hNsmall
  have hbetaFloor := hW₀ w hwW₀
  have hquarter : (1 / 4 : ℝ) < dimensionlessCumulativeJacobiDissipation w n := by
    nlinarith
  have hscale :=
    dimensionlessCumulativeJacobiDissipation_eq_fourth_mul_actual hw1 hA
  have hAsmall : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hsource :=
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
      (lt_trans (by norm_num) hw1) (by omega) hAsmall
  rw [hsource, ← hscale]
  exact hquarter

/-- Projective Gauss-root spread is strictly dominated by half the dimensionless cumulative
Jacobi dissipation.  The missing positive terms are the alpha center, the terminal alpha square,
and the two terminal beta edges. -/
theorem two_mul_projectiveGaussRootSpread_lt_dimensionlessCumulativeJacobiDissipation
    {w : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    2 * projectiveGaussRootSpread (xiShiftedFarRightNormalizedMoment w) n <
      dimensionlessCumulativeJacobiDissipation w n := by
  let s := xiShiftedFarRightNormalizedMoment w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [projectiveGaussRootSpread_eq_alphaDispersion_add_betaInventory
    hbelow hn (by omega)]
  unfold projectiveJacobiLowerAlphaDispersion
    dimensionlessCumulativeJacobiDissipation
  have hnpos : 0 < (n : ℝ) := by positivity
  have hcenter : 0 ≤
      (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) ^ (2 : ℕ) / (n : ℝ) := by
    positivity
  have hterminal : 0 < 2 * (n + 1 : ℝ) *
      (HTGeometry.monicOrthoBeta s n + HTGeometry.monicOrthoBeta s (n + 1)) := by
    have hnBeta := HTGeometry.monicOrthoBeta_pos_below hbelow (by omega : 0 < n) (by omega)
    have hn1Beta :=
      HTGeometry.monicOrthoBeta_pos_below hbelow (by omega : 0 < n + 1) (by omega)
    positivity
  dsimp only [s] at hcenter hterminal ⊢
  nlinarith [sq_nonneg
    (HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) n)]

/-- **Cofinal source divergence.** On every cofinal mass-and-degree schedule with positive
actual admission blocks, the forced `w^(4 : ℕ)` renormalization of the literal drift-removed adaptive
mixed/completed source action tends to infinity. -/
theorem tendsto_renormalized_adaptiveMixedCompletedSourceAction_along_cofinal_positive_blocks
    (w : ℕ → ℝ) (n : ℕ → ℕ)
    (hw : Tendsto w atTop atTop) (hn : Tendsto n atTop atTop)
    (hH : ∀ l, (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (w l)) (n l + 4)).PosDef) :
    Tendsto (fun l => (w l) ^ (4 : ℕ) *
      xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction (w l) (n l))
      atTop atTop := by
  have hHsmall : ∀ l, (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (w l)) (n l + 2)).PosDef := by
    intro l
    exact momentHankel_posDef_of_le (by omega) (hH l)
  have hspread :=
    tendsto_projectiveGaussRootSpread_along_cofinal_actual_positive_blocks
      w n hw hn hHsmall
  have hD : Tendsto (fun l => dimensionlessCumulativeJacobiDissipation (w l) (n l))
      atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hspread
    filter_upwards [hn.eventually_ge_atTop 2, hw.eventually_gt_atTop 1] with l hnl hwl
    have hN0 := xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual
      hwl (n l + 2) (hHsmall l)
    have hN : (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment (w l)) (n l + 2)).PosDef := by
      simpa only [xiShiftedFarRightNormalizedHankelMatrix] using hN0
    have hdom :=
      two_mul_projectiveGaussRootSpread_lt_dimensionlessCumulativeJacobiDissipation hnl hN
    have hspreadNonneg := projectiveGaussRootSpread_pos
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hN) hnl (by omega)
    linarith
  apply hD.congr'
  filter_upwards [hn.eventually_ge_atTop 2, hw.eventually_gt_atTop 1] with l hnl hwl
  have hscale := dimensionlessCumulativeJacobiDissipation_eq_fourth_mul_actual
    (n := n l) hwl (hH l)
  have hAsmall : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (w l)) (n l + 2)).PosDef :=
    momentHankel_posDef_of_le (m := n l + 2) (N := n l + 4) (by omega) (hH l)
  have hsource :=
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
      (n := n l) (lt_trans (by norm_num) hwl) (by omega : 0 < n l) hAsmall
  rw [hsource, ← hscale]

end
end XiShiftedCanonicalAdmission
end RHTower
