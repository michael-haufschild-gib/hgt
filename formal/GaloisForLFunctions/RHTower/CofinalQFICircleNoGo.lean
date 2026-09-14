import GaloisForLFunctions.RHTower.FiniteCutoffQFIHigherContactNoGo

/-!
# Joint escape does not fill the QFI boundary circle

Even eventual escape of two exactly compensating complex processes does not force their QFI-ball
images to occupy every boundary phase.  An explicit pair escapes at every sufficiently late cutoff,
has zero total at every cutoff, and remains on one real diameter of the QFI ball.  No subsequence of
its first coordinate can converge to the boundary phase `i`.

This closes the inference from multi-process escape to a full phase link.  Any source route using
such a link must prove phase occupation from its arithmetic transition law.
-/

open Filter
open scoped Topology

noncomputable section
namespace RHTower.DeletionMixedRefinement

/-- A cofinal complex escape confined to one phase. -/
def singlePhaseEscape (N : ℕ) : ℂ := (N + 1 : ℕ)

@[simp] theorem singlePhaseEscape_neg_sum (N : ℕ) :
    singlePhaseEscape N + -singlePhaseEscape N = 0 := by
  simp

/-- The one-phase example leaves every norm-bounded set. -/
theorem tendsto_norm_singlePhaseEscape :
    Tendsto (fun N : ℕ => ‖singlePhaseEscape N‖) atTop atTop := by
  have h : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  convert h using 1
  ext N
  rw [singlePhaseEscape, Complex.norm_natCast]
  norm_num

/-- Every QFI-ball image of the example remains on the real diameter. -/
@[simp] theorem qfiOpenBallCoordinate_singlePhaseEscape_im (N : ℕ) :
    (qfiOpenBallCoordinate (singlePhaseEscape N)).im = 0 := by
  rw [qfiOpenBallCoordinate_eq]
  simp [singlePhaseEscape]

/-- No reindexing of the example can approach the boundary phase `i`. -/
theorem no_singlePhaseEscape_qfi_subsequence_tendsTo_I (k : ℕ → ℕ) :
    ¬ Tendsto (fun N => qfiOpenBallCoordinate (singlePhaseEscape (k N)))
      atTop (𝓝 Complex.I) := by
  intro h
  have him := Complex.continuous_im.continuousAt.tendsto.comp h
  have him' :
      Tendsto (fun N => (qfiOpenBallCoordinate (singlePhaseEscape (k N))).im)
        atTop (𝓝 Complex.I.im) := by
    simp only [Function.comp_def] at him
    exact him
  have hzero :
      (fun N => (qfiOpenBallCoordinate (singlePhaseEscape (k N))).im) =
        fun _ : ℕ => (0 : ℝ) := by
    funext N
    exact qfiOpenBallCoordinate_singlePhaseEscape_im (k N)
  rw [hzero] at him'
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hEq : (0 : ℝ) = Complex.I.im := tendsto_nhds_unique hconst him'
  norm_num at hEq

/-- Strong joint escape and exact compensation coexist with omission of a boundary phase. -/
theorem exists_eventual_joint_escape_exactly_compensated_single_qfi_phase :
    ∃ x y : ℕ → ℂ,
      Tendsto (fun N => ‖x N‖) atTop atTop ∧
      Tendsto (fun N => ‖y N‖) atTop atTop ∧
      (∀ N, x N + y N = 0) ∧
      (∀ N, (qfiOpenBallCoordinate (x N)).im = 0) ∧
      (∀ k : ℕ → ℕ,
        ¬ Tendsto (fun N => qfiOpenBallCoordinate (x (k N))) atTop (𝓝 Complex.I)) := by
  refine ⟨singlePhaseEscape, fun N => -singlePhaseEscape N,
    tendsto_norm_singlePhaseEscape, ?_, singlePhaseEscape_neg_sum,
    qfiOpenBallCoordinate_singlePhaseEscape_im,
    no_singlePhaseEscape_qfi_subsequence_tendsTo_I⟩
  simpa only [norm_neg] using tendsto_norm_singlePhaseEscape

end RHTower.DeletionMixedRefinement
