import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionGaussEdgeArithmeticSource
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveCofinalSpread
import GaloisForLFunctions.RHTower.XiShiftedHankelStrictFrontierCurvatureRenewal

/-!
# Degree-uniform low-edge floor for adaptive completed arithmetic bulk

Remove from literal adaptive mixed/completed source only its exact Gaussian-invisible newborn
norm.  Remaining admission-selected bulk is not merely positive: normalized completed-square
geometry forces it above twice first Christoffel edge, independently of current degree.

For shifted-Xi normalized admission first edge tends `1/8`.  Hence one far-right mass threshold
forces a uniform `1/8` lower bound for source bulk at every degree at least two and every actual
positive block.  No orientation map, fixed reporter, or reflection aggregation occurs.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Relative adaptive completed arithmetic bulk after removing exact Gaussian-invisible newborn
norm.  Both terms are selected by current canonical admission before observation. -/
def relativeArithmeticGaussBulk (w : ℝ) (n : ℕ) : ℝ :=
  relativeArithmeticSource w n -
    (n + 1 : ℝ) / 16 * admissionChristoffelScaleSq w n

/-- Exact literal source/newborn-norm quotient.  Numerator is mass-scaled adaptive mixed completed
`P^sharp` arithmetic source minus exact next admitted norm lost by current Gaussian observation. -/
theorem relativeArithmeticGaussBulk_eq_literal (w : ℝ) (n : ℕ) :
    relativeArithmeticGaussBulk w n =
      (w ^ (4 * n + 5) / Real.log w *
          xiShiftedAdaptiveMixedCompletedArithmeticSource w
            (sourceCoordinateAdmission w n) -
        (n + 1 : ℝ) * normalizedAdmissionNorm w (n + 1)) /
      normalizedAdmissionNorm w n := by
  unfold relativeArithmeticGaussBulk relativeArithmeticSource
    admissionChristoffelScaleSq
  ring

/-- Generic completed-square floor.  After newborn edge is removed, first retained Christoffel
edge contributes twice and current edge makes inequality strict. -/
theorem two_mul_lowEdge_lt_adaptiveOrthoJacobiEnergy_sub_nextEdge
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n + 2 ≤ N) :
    2 * HTGeometry.monicOrthoBeta s 1 <
      HTGeometry.adaptiveOrthoJacobiEnergy s n -
        (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s (n + 1) := by
  have hsquares : 0 ≤ ∑ j ∈ Finset.range n,
      (HTGeometry.monicOrthoAlpha s j +
        HTGeometry.monicOrthoAlpha s n / 2) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag : 0 ≤ (3 * (n : ℝ) / 4 + 1) *
      HTGeometry.monicOrthoAlpha s n ^ 2 := by
    positivity
  have hbeta_nonneg : ∀ j ∈ Finset.range n,
      0 ≤ HTGeometry.monicOrthoBeta s j := by
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hone : 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hlow : HTGeometry.monicOrthoBeta s 1 ≤
      ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j := by
    calc
      HTGeometry.monicOrthoBeta s 1 =
          ∑ j ∈ ({1} : Finset ℕ), HTGeometry.monicOrthoBeta s j := by simp
      _ ≤ ∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta s j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.singleton_subset_iff.mpr hone)
          (fun j hj _ => hbeta_nonneg j hj)
  have hcurrent : 0 < (n + 1 : ℝ) * HTGeometry.monicOrthoBeta s n := by
    exact mul_pos (by positivity)
      (HTGeometry.monicOrthoBeta_pos_below h (by omega) (by omega))
  unfold HTGeometry.adaptiveOrthoJacobiEnergy
  nlinarith

/-- Exact current-admission Jacobi form of literal Gaussian-visible arithmetic bulk. -/
theorem relativeArithmeticGaussBulk_eq_visibleEnergy
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    relativeArithmeticGaussBulk w n =
      HTGeometry.adaptiveOrthoJacobiEnergy
          (xiShiftedFarRightNormalizedMoment w) n -
        (n + 1 : ℝ) * HTGeometry.monicOrthoBeta
          (xiShiftedFarRightNormalizedMoment w) (n + 1) := by
  rw [relativeArithmeticGaussBulk,
    relativeArithmeticSource_eq_adaptiveOrthoJacobiEnergy hw hn hH,
    admissionChristoffelScaleSq_eq_sixteen_mul_monicOrthoBeta hH]
  ring

/-- Degree-free source coercivity: visible adaptive arithmetic bulk strictly retains twice first
Christoffel edge, even if every higher shape coordinate degenerates. -/
theorem two_mul_lowEdge_lt_relativeArithmeticGaussBulk
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 2 ≤ n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    2 * HTGeometry.monicOrthoBeta
        (xiShiftedFarRightNormalizedMoment w) 1 <
      relativeArithmeticGaussBulk w n := by
  rw [relativeArithmeticGaussBulk_eq_visibleEnergy hw (by omega) hH]
  exact two_mul_lowEdge_lt_adaptiveOrthoJacobiEnergy_sub_nextEdge
    (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) hn le_rfl

/-- One mass threshold gives nonzero adaptive arithmetic bulk simultaneously at every degree.
Hypothesis is normalized positive block; no degree-dependent recession threshold occurs. -/
theorem exists_uniform_relativeArithmeticGaussBulk_eighth_of_normalized :
    ∃ W : ℝ, ∀ w ≥ W, ∀ n : ℕ, 2 ≤ n →
      (HTGeometry.momentHankelMatrix
        (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef →
      (1 / 8 : ℝ) < relativeArithmeticGaussBulk w n := by
  have hbeta := tendsto_dimensionless_monicOrthoBeta (n := 1) (by omega)
  rw [monicOrthoBeta_normalizedCentralBinom_one] at hbeta
  have hev : ∀ᶠ w : ℝ in atTop,
      (1 / 16 : ℝ) < HTGeometry.monicOrthoBeta
        (xiShiftedFarRightNormalizedMoment w) 1 :=
    hbeta.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨W, hW⟩ := eventually_atTop.1 hev
  refine ⟨max W 2, ?_⟩
  intro w hw n hn hH
  have hwW : W ≤ w := le_trans (le_max_left _ _) hw
  have hw1 : 1 < w := lt_of_lt_of_le (by norm_num)
    (le_trans (le_max_right _ _) hw)
  have hlow := two_mul_lowEdge_lt_relativeArithmeticGaussBulk hw1 hn hH
  have hbetaFloor := hW w hwW
  nlinarith

/-- Same degree-uniform source floor for literal actual shifted-Xi positive blocks.  Coordinate
normalization is exact congruence, not asymptotic replacement. -/
theorem exists_uniform_relativeArithmeticGaussBulk_eighth_of_actual :
    ∃ W : ℝ, ∀ w ≥ W, ∀ n : ℕ, 2 ≤ n →
      (HTGeometry.momentHankelMatrix
        (xiShiftedRealMomentSequence w) (n + 2)).PosDef →
      (1 / 8 : ℝ) < relativeArithmeticGaussBulk w n := by
  obtain ⟨W, hW⟩ := exists_uniform_relativeArithmeticGaussBulk_eighth_of_normalized
  refine ⟨max W 2, ?_⟩
  intro w hw n hn hH
  have hwW : W ≤ w := le_trans (le_max_left _ _) hw
  have hw1 : 1 < w := lt_of_lt_of_le (by norm_num)
    (le_trans (le_max_right _ _) hw)
  have hnormalized : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef := by
    have h := xiShiftedFarRightNormalizedHankelMatrix_posDef_of_actual
      hw1 (n + 2) hH
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using h
  exact hW w hwW n hn hnormalized

/-- **Strict-frontier noncollapse.**  Beyond one universal mass threshold, every point on right
positive ray of every occupied strict frontier carries same normalized literal arithmetic-bulk
floor, although frontier degree may escape to infinity. -/
theorem exists_uniform_strictFrontier_right_relativeArithmeticGaussBulk_eighth :
    ∃ W : ℝ, 2 ≤ W ∧
      ∀ {n : ℕ}, 0 < n → (xiShiftedHigherBlockFailureSet n).Nonempty →
        xiShiftedHigherBlockTerminalFrontier n <
          xiShiftedHigherBlockTerminalFrontier (n + 1) →
        W ^ 2 ≤ xiShiftedHigherBlockTerminalFrontier (n + 1) →
        ∀ {v : ℝ}, xiShiftedHigherBlockTerminalFrontier (n + 1) < v →
          (1 / 8 : ℝ) < relativeArithmeticGaussBulk (Real.sqrt v) (n + 1) := by
  obtain ⟨W₀, hW₀⟩ := exists_uniform_relativeArithmeticGaussBulk_eighth_of_actual
  let W := max W₀ 2
  refine ⟨W, le_max_right _ _, ?_⟩
  intro n hn hne hstrict hfrontier v hv
  have hy : 0 < xiShiftedHigherBlockTerminalFrontier (n + 1) := by
    obtain ⟨u, hu⟩ := hne
    have hule := le_xiShiftedHigherBlockTerminalFrontier_of_mem hu
    exact lt_of_le_of_lt (hu.1.trans hule) hstrict
  have hv0 : 0 ≤ v := (hy.trans hv).le
  have hWnonneg : 0 ≤ W := le_trans (by norm_num) (le_max_right W₀ 2)
  have hsqrt : W ≤ Real.sqrt v := by
    have hsqrt0 := Real.sqrt_nonneg v
    have hsquare := Real.sq_sqrt hv0
    nlinarith
  have hblock : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt v)) ((n + 1) + 2)).PosDef := by
    have hactual := xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
      (n := n + 1) hv0 hv
    change (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment ((Real.sqrt v) ^ 2) k).re)
      ((n + 1) + 2)).PosDef
    rw [Real.sq_sqrt hv0]
    exact hactual
  exact hW₀ (Real.sqrt v) (le_trans (le_max_left _ _) hsqrt)
    (n + 1) (by omega) hblock

/-- **Closed cofinal source-noncollapse dichotomy.**  Either RH holds, or above every mass
threshold there is an occupied strict renewal whose entire later positive ray carries normalized
literal adaptive arithmetic bulk greater than `1/8`.  Degree may escape, producer cannot. -/
theorem riemannHypothesis_or_cofinal_uniform_relativeArithmeticGaussBulk_eighth :
    RiemannHypothesis ∨
      ∃ W : ℝ, 2 ≤ W ∧ ∀ A : ℝ,
        ∃ n : ℕ, 0 < n ∧ (xiShiftedHigherBlockFailureSet n).Nonempty ∧
          A < xiShiftedHigherBlockTerminalFrontier n ∧
          xiShiftedHigherBlockTerminalFrontier n <
            xiShiftedHigherBlockTerminalFrontier (n + 1) ∧
          ∀ {v : ℝ}, xiShiftedHigherBlockTerminalFrontier (n + 1) < v →
            (1 / 8 : ℝ) < relativeArithmeticGaussBulk (Real.sqrt v) (n + 1) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    obtain ⟨W, hW2, hW⟩ :=
      exists_uniform_strictFrontier_right_relativeArithmeticGaussBulk_eighth
    refine ⟨W, hW2, ?_⟩
    intro A
    let T := max (max A (W ^ 2)) (xiShiftedHigherBlockTerminalFrontier 0)
    obtain ⟨n, hne, hTn, hstrict, _⟩ :=
      exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hRH T
    have hn : 0 < n := by
      by_contra hn0
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      exact (not_lt_of_ge (le_max_right _ _)) hTn
    have hAn : A < xiShiftedHigherBlockTerminalFrontier n :=
      (le_trans (le_max_left _ _) (le_max_left _ _)).trans_lt hTn
    have hWfrontier : W ^ 2 ≤
        xiShiftedHigherBlockTerminalFrontier (n + 1) := by
      have hWn : W ^ 2 < xiShiftedHigherBlockTerminalFrontier n :=
        (le_trans (le_max_right _ _) (le_max_left _ _)).trans_lt hTn
      exact hWn.trans hstrict |>.le
    refine ⟨n, hn, hne, hAn, hstrict, ?_⟩
    intro v hv
    exact hW hn hne hstrict hWfrontier hv

end
end XiShiftedCanonicalAdmission
end RHTower
