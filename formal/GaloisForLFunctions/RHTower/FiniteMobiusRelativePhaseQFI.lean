import GaloisForLFunctions.RHTower.FiniteMobiusLeftOverflowEscape
import GaloisForLFunctions.HTGeometry.ConstitutivePolarAmplitudeFisherPhase

/-!
# Compensated source escape has balanced relative-phase QFI

Treat rectangle overflow and continuation--recovery interaction as two independently phase-coded
channels of one experiment.  Their common phase is unobservable; the relative phase is generated
by velocities `+1` and `-1`.  The resulting pure-state QFI is four times the variance of those
velocities under the two normalized channel weights.

At every strict-left nontrivial zero, a strictly increasing cutoff subsequence makes both channels
escape while their sum tends to `-1`.  Along that subsequence their normalized weights tend to an
equal split, so relative-phase QFI tends to `4`.  No escape direction is selected or assumed.
-/

open Complex Filter Set
open scoped Topology BigOperators

namespace RHTower.DeletionMixedRefinement

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squared mass of two phase-coded source channels. -/
def compensatedPairMass (x y : ℂ) : ℝ := ‖x‖ ^ (2 : ℕ) + ‖y‖ ^ (2 : ℕ)

/-- Normalized weights of two source channels. -/
def compensatedPairPhaseWeights (x y : ℂ) : Fin 2 → ℝ :=
  ![‖x‖ ^ (2 : ℕ) / compensatedPairMass x y,
    ‖y‖ ^ (2 : ℕ) / compensatedPairMass x y]

/-- Opposite phase velocities distinguish the two source laws. -/
def relativePhaseVelocity : Fin 2 → ℤ := ![1, -1]

/-- QFI of the controlled relative phase for a compensated pair. -/
def compensatedPairRelativePhaseQFI (x y : ℂ) : ℝ :=
  4 * velVar (compensatedPairPhaseWeights x y) relativePhaseVelocity

/-- Exact two-channel relative-phase QFI formula. -/
theorem compensatedPairRelativePhaseQFI_eq (x y : ℂ) :
    compensatedPairRelativePhaseQFI x y =
      16 * ‖x‖ ^ (2 : ℕ) * ‖y‖ ^ (2 : ℕ) / (‖x‖ ^ (2 : ℕ) + ‖y‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
  simp [compensatedPairRelativePhaseQFI, velVar, velMean,
    compensatedPairPhaseWeights, compensatedPairMass, relativePhaseVelocity]
  field_simp
  ring

/-- An asymptotically opposite pair has balanced relative-phase QFI. -/
theorem tendsto_compensatedPairRelativePhaseQFI_of_ratio
    {ι : Type*} {l : Filter ι} [NeBot l] (x y : ι → ℂ)
    (hx : Tendsto (fun n => ‖x n‖) l atTop)
    (hratio : Tendsto (fun n => y n * (x n)⁻¹) l (nhds (-1))) :
    Tendsto (fun n => compensatedPairRelativePhaseQFI (x n) (y n)) l (nhds 4) := by
  have hxnz : ∀ᶠ n in l, x n ≠ 0 := eventually_ne_of_tendsto_norm_atTop hx 0
  have hnormRatio : Tendsto (fun n => ‖y n * (x n)⁻¹‖) l (nhds 1) := by
    simpa using hratio.norm
  have hmodel : Tendsto (fun n =>
      16 * ‖y n * (x n)⁻¹‖ ^ (2 : ℕ) / (1 + ‖y n * (x n)⁻¹‖ ^ (2 : ℕ)) ^ (2 : ℕ))
      l (nhds 4) := by
    have hcontinuous : ContinuousAt (fun r : ℝ =>
        16 * r ^ (2 : ℕ) / (1 + r ^ (2 : ℕ)) ^ (2 : ℕ)) 1 := by
      exact (continuousAt_const.mul (continuousAt_id.pow 2)).div
        ((continuousAt_const.add (continuousAt_id.pow 2)).pow 2) (by norm_num)
    convert hcontinuous.tendsto.comp hnormRatio using 1
    · rfl
    · norm_num
  apply hmodel.congr'
  filter_upwards [hxnz] with n hn
  rw [compensatedPairRelativePhaseQFI_eq, norm_mul, norm_inv]
  have hnorm : ‖x n‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  field_simp

/-- Escape with a finite compensated total forces balanced relative-phase QFI. -/
theorem tendsto_compensatedPairRelativePhaseQFI_balanced
    {ι : Type*} {l : Filter ι} [NeBot l] {c : ℂ} (x y : ι → ℂ)
    (hx : Tendsto (fun n => ‖x n‖) l atTop)
    (hsum : Tendsto (fun n => x n + y n) l (nhds c)) :
    Tendsto (fun n => compensatedPairRelativePhaseQFI (x n) (y n)) l (nhds 4) := by
  have hxnz : ∀ᶠ n in l, x n ≠ 0 := eventually_ne_of_tendsto_norm_atTop hx 0
  have hxInvNorm : Tendsto (fun n => ‖x n‖⁻¹) l (nhds 0) :=
    tendsto_inv_atTop_zero.comp hx
  have hxInv : Tendsto (fun n => (x n)⁻¹) l (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_inv] using hxInvNorm
  have hratio : Tendsto (fun n => y n * (x n)⁻¹) l (nhds (-1)) := by
    have hscaled := hsum.mul hxInv
    have hshift := hscaled.sub (tendsto_const_nhds (x := (1 : ℂ)))
    have heq : ∀ᶠ n in l,
        (x n + y n) * (x n)⁻¹ - 1 = y n * (x n)⁻¹ :=
      hxnz.mono fun n hn => by
        rw [add_mul, mul_inv_cancel₀ hn]
        ring
    simpa using hshift.congr' heq
  exact tendsto_compensatedPairRelativePhaseQFI_of_ratio x y hx hratio

/-- Head/correction infinity has the same balanced phase QFI at every open-strip point. -/
theorem tendsto_headCorrectionRelativePhaseQFI_balanced
    (s : FiniteCutoffOpenStripPoint) :
    Tendsto (fun N => compensatedPairRelativePhaseQFI
      (finiteZetaFormationHead N s.1)
      (finiteCutoffContinuationCorrection N s.1)) atTop (nhds 4) := by
  have hsum : Tendsto (fun N =>
      finiteZetaFormationHead N s.1 + finiteCutoffContinuationCorrection N s.1)
      atTop (nhds (riemannZeta s.1)) :=
    (tendsto_finiteCutoffZeta_at_openStrip s).congr'
      (Filter.Eventually.of_forall fun N =>
        (finiteZetaFormationHead_add_continuationCorrection N s.1).symm)
  exact tendsto_compensatedPairRelativePhaseQFI_balanced
    (fun N => finiteZetaFormationHead N s.1)
    (fun N => finiteCutoffContinuationCorrection N s.1)
    (tendsto_norm_finiteZetaFormationHead_atTop s) hsum

/-- One cofinal joint-escape cutoff above each integer threshold. -/
noncomputable def jointEscapeChoice
    (rho : StrictLeftNontrivialZetaZero) (N : ℕ) : ℕ :=
  Classical.choose (exists_joint_overflow_escape_after rho (N : ℝ) N)

theorem jointEscapeChoice_spec
    (rho : StrictLeftNontrivialZetaZero) (N : ℕ) :
    N ≤ jointEscapeChoice rho N ∧
      (N : ℝ) < ‖finiteMobiusOverflow (jointEscapeChoice rho N) rho.1.1‖ ∧
      (N : ℝ) < ‖finiteCorrectionRecoveryInteraction
        (jointEscapeChoice rho N) rho.1.1‖ :=
  Classical.choose_spec (exists_joint_overflow_escape_after rho (N : ℝ) N)

/-- Every strict-left zero has a cofinal source history with balanced relative-phase QFI. -/
theorem strictLeftZero_exists_balancedRelativePhaseQFI
    (rho : StrictLeftNontrivialZetaZero) :
    ∃ k : ℕ → ℕ,
      StrictMono k ∧
      Tendsto (fun N => ‖finiteMobiusOverflow (k N) rho.1.1‖) atTop atTop ∧
      Tendsto (fun N => ‖finiteCorrectionRecoveryInteraction (k N) rho.1.1‖)
        atTop atTop ∧
      Tendsto (fun N => compensatedPairRelativePhaseQFI
        (finiteMobiusOverflow (k N) rho.1.1)
        (finiteCorrectionRecoveryInteraction (k N) rho.1.1)) atTop (nhds 4) := by
  obtain ⟨phi, hphi, hk⟩ :=
    Filter.strictMono_subseq_of_id_le (fun N => (jointEscapeChoice_spec rho N).1)
  let k := jointEscapeChoice rho ∘ phi
  have hk' : StrictMono k := hk
  have hphiTop : Tendsto phi atTop atTop := hphi.tendsto_atTop
  have hphiReal : Tendsto (fun N => (phi N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hphiTop
  have hx : Tendsto (fun N => ‖finiteMobiusOverflow (k N) rho.1.1‖)
      atTop atTop := by
    refine tendsto_atTop.2 (fun R => ?_)
    filter_upwards [hphiReal.eventually (eventually_gt_atTop R)] with N hN
    simpa [k] using (hN.trans (jointEscapeChoice_spec rho (phi N)).2.1).le
  have hy : Tendsto (fun N =>
      ‖finiteCorrectionRecoveryInteraction (k N) rho.1.1‖) atTop atTop := by
    refine tendsto_atTop.2 (fun R => ?_)
    filter_upwards [hphiReal.eventually (eventually_gt_atTop R)] with N hN
    simpa [k] using (hN.trans (jointEscapeChoice_spec rho (phi N)).2.2).le
  have hsum : Tendsto (fun N =>
      finiteMobiusOverflow (k N) rho.1.1 +
        finiteCorrectionRecoveryInteraction (k N) rho.1.1) atTop (nhds (-1)) := by
    have hbase : Tendsto (fun N : ℕ =>
        finiteMobiusOverflow N rho.1.1 +
          finiteCorrectionRecoveryInteraction N rho.1.1) atTop (nhds (-1)) := by
      simpa [finiteMobiusOverflow, finiteCorrectionRecoveryInteraction] using
        tendsto_finiteMobiusBoundaryFailureTotal_at_zero rho.1
    exact hbase.comp hk'.tendsto_atTop
  refine ⟨k, hk', hx, hy, ?_⟩
  exact tendsto_compensatedPairRelativePhaseQFI_balanced
    (fun N => finiteMobiusOverflow (k N) rho.1.1)
    (fun N => finiteCorrectionRecoveryInteraction (k N) rho.1.1) hx hsum

end

end RHTower.DeletionMixedRefinement
