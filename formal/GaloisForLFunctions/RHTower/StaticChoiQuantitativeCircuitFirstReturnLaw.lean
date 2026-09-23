import GaloisForLFunctions.RHTower.StaticChoiCircuitExcursionFirstReturnLaw
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeRecurrenceUpperLaw

/-!
# Quantitative first re-entry after a static Choi hard block

A static spectral Choi trajectory differs from its zero-anchored projective
representative only by a global phase and time reversal.  The phase is
operationally invisible.  Consequently the rank-only Dirichlet recurrence
deadline for the full spectral representative supplies a quantitative return
to the identity target of the projective trajectory.

Combining that return with closedness of a finite circuit-capture set turns
every certified circuit-free block into a pair of consecutive captures.  If
the block starts at `u` and has width `W`, the first re-entry is no later than

`(ceil (u + W) + 1) * (Q + 1) ^ d`,

where `d` is projective spectral dimension and `Q` fixes return resolution.
No maximal-projective, randomness, locality, or spectral-gap premise enters
this recurrence deadline.
-/

open Set Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The zero-anchored projective Choi vector is the full spectral Choi vector
at reversed time, multiplied by the invisible anchor phase. -/
theorem projectiveChoiVector_eq_phase_smul_staticSpectralChoiVector_neg
    {d : ℕ} (energy : Fin (d + 1) → ℝ) (t : ℝ) :
    fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)) =
      finiteObserverHamiltonianVertexPhase t energy 0 •
        staticSpectralChoiVector (d + 1) (-t) energy := by
  ext ij
  simp only [fullUniformPhaseChoiVector_apply, staticSpectralChoiVector,
    PiLp.smul_apply]
  rcases ij with ⟨i, j⟩
  by_cases hij : i = j
  · simp only [hij, if_pos]
    subst j
    rw [fourier_projectiveChoiPhase_eq_exp,
      fourier_finiteHamiltonianAddCirclePhase]
    unfold finiteObserverHamiltonianVertexPhase
    change
      ((Real.sqrt ((d + 1 : ℕ) : ℝ))⁻¹ : ℂ) *
          Complex.exp (((t * Fin.cases 0 (zeroProjectiveFrequency energy) i : ℝ) : ℂ) *
            Complex.I) =
        Complex.exp (Complex.I * (t * energy 0 : ℝ)) *
          (((Real.sqrt ((d + 1 : ℕ) : ℝ))⁻¹ : ℂ) *
            Complex.exp (Complex.I * ((-t) * energy i : ℝ)))
    rw [show
      Complex.exp (Complex.I * (t * energy 0 : ℝ)) *
          (((Real.sqrt ((d + 1 : ℕ) : ℝ))⁻¹ : ℂ) *
            Complex.exp (Complex.I * ((-t) * energy i : ℝ))) =
        ((Real.sqrt ((d + 1 : ℕ) : ℝ))⁻¹ : ℂ) *
          (Complex.exp (Complex.I * (t * energy 0 : ℝ)) *
            Complex.exp (Complex.I * ((-t) * energy i : ℝ))) by ring_nf]
    rw [← Complex.exp_add]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cases_succ, zeroProjectiveFrequency]
      push_cast
      ring_nf
  · simp [hij]

/-- Operational distance to the identity channel is unchanged by passing
between the projective and full spectral representatives. -/
theorem pureStateTraceDistance_projectiveChoi_zero_eq_staticSpectral_neg
    {d : ℕ} (energy : Fin (d + 1) → ℝ) (t : ℝ) :
    pureStateTraceDistance
        (fullUniformPhaseChoiVector (d + 1)
          (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
        (fullUniformPhaseChoiVector (d + 1)
          (zeroAnchoredPhase d
            (0 : Fin d → UnitAddCircle))) =
      pureStateTraceDistance
        (staticSpectralChoiVector (d + 1) (-t) energy)
        (staticSpectralChoiVector (d + 1) 0 energy) := by
  have hzero : projectivePhysicalPhaseFlow energy 0 =
      (0 : Fin d → UnitAddCircle) := by
    funext i
    simp [projectivePhysicalPhaseFlow]
  rw [← hzero]
  rw [projectiveChoiVector_eq_phase_smul_staticSpectralChoiVector_neg]
  rw [projectiveChoiVector_eq_phase_smul_staticSpectralChoiVector_neg]
  simp only [neg_zero]
  rw [_root_.HTGeometry.pureStateTraceDistance_smul_left]
  · simp [finiteObserverHamiltonianVertexPhase]
  · exact finiteObserverHamiltonianVertexPhase_norm t energy 0

/-- **Quantitative consecutive-capture law.**  A continuous circuit-free
block has a literal first re-entry whose deadline is the dimension-rank
Dirichlet recurrence bound.  The target dictionary need only be finite and
contain the identity Choi channel. -/
theorem pureChoiCircuitTarget_quantitativeConsecutiveVisitGap
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (identity : PaddedCircuitWord gate s)
    (hidentity : target identity =
      fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))
    {eps u W : ℝ} (heps : 0 ≤ eps) (hu : 0 ≤ u) (hW : 0 ≤ W)
    (havoid : ∀ t ∈ Icc u (u + W),
      ∀ w, eps < pureStateTraceDistance
        (fullUniformPhaseChoiVector (d + 1)
          (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
        (target w))
    (Q : ℕ)
    (hQ : 2 * (2 * Real.pi / (Q + 1 : ℝ)) ^ (2 : ℕ) ≤ eps ^ (2 : ℕ)) :
    ∃ tExit tReturn : ℝ,
      tExit ∈ Icc 0 u ∧
      tReturn ∈ Icc (u + W)
        ((((Nat.ceil (u + W) + 1) * (Q + 1) ^ d : ℕ) : ℝ)) ∧
      (∃ w, pureStateTraceDistance
        (fullUniformPhaseChoiVector (d + 1)
          (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tExit)))
        (target w) ≤ eps) ∧
      (∃ w, pureStateTraceDistance
        (fullUniformPhaseChoiVector (d + 1)
          (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy tReturn)))
        (target w) ≤ eps) ∧
      tExit < tReturn ∧ W ≤ tReturn - tExit ∧
      ∀ t ∈ Ioo tExit tReturn,
        ¬ ∃ w, pureStateTraceDistance
          (fullUniformPhaseChoiVector (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (target w) ≤ eps := by
  let orbit : ℝ → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) := fun t =>
    fullUniformPhaseChoiVector (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
  let capture : Set ℝ :=
    {t | ∃ w, pureStateTraceDistance (orbit t) (target w) ≤ eps}
  have horbit : Continuous orbit := continuous_projectivePureChoiVector energy
  have hcapture : IsClosed capture :=
    isClosed_finite_pureStateTraceDistance_captureTimeSet orbit horbit target eps
  have hpre : ∃ t ∈ Icc 0 u, t ∈ capture := by
    refine ⟨0, ⟨le_rfl, hu⟩, identity, ?_⟩
    dsimp only [orbit]
    rw [hidentity]
    have hflow0 : projectivePhysicalPhaseFlow energy 0 =
        (0 : Fin d → UnitAddCircle) := by
      funext i
      simp [projectivePhysicalPhaseFlow]
    rw [hflow0]
    unfold pureStateTraceDistance
    rw [inner_self_eq_norm_sq_to_K,
      fullUniformPhaseChoiVector_norm (Nat.succ_pos d)]
    norm_num
    exact heps
  let M : ℕ := Nat.ceil (u + W)
  obtain ⟨n, hnM, hnBound, hnRec⟩ :=
    exists_staticSpectralChoi_recurrence_after
      (Nat.succ_pos d) energy (-1) Q M
  have hnDist : pureStateTraceDistance
      (staticSpectralChoiVector (d + 1) (-(n : ℝ)) energy)
      (staticSpectralChoiVector (d + 1) 0 energy) ≤ eps := by
    rw [_root_.HTGeometry.pureStateTraceDistance_comm]
    have hsq : pureStateTraceDistance
          (staticSpectralChoiVector (d + 1) 0 energy)
          (staticSpectralChoiVector (d + 1) (-(n : ℝ)) energy) ^ (2 : ℕ) ≤
        eps ^ (2 : ℕ) := by
      simpa [Nat.succ_eq_add_one] using hnRec.trans hQ
    exact (sq_le_sq₀ (pureStateTraceDistance_nonneg _ _) heps).mp hsq
  have hnProjective : pureStateTraceDistance (orbit n)
      (target identity) ≤ eps := by
    dsimp only [orbit]
    rw [hidentity,
      pureStateTraceDistance_projectiveChoi_zero_eq_staticSpectral_neg]
    simpa using hnDist
  have hstart : u + W ≤ (n : ℝ) := by
    exact (Nat.le_ceil (u + W)).trans (by
      exact_mod_cast (le_of_lt hnM))
  have hend : (n : ℝ) ≤
      ((((Nat.ceil (u + W) + 1) * (Q + 1) ^ d : ℕ) : ℝ)) := by
    exact_mod_cast hnBound
  have hpost : ∃ t ∈ Icc (u + W)
      ((((Nat.ceil (u + W) + 1) * (Q + 1) ^ d : ℕ) : ℝ)),
      t ∈ capture := by
    refine ⟨n, ⟨hstart, hend⟩, identity, hnProjective⟩
  have havoidCapture : ∀ t ∈ Icc u (u + W), t ∉ capture := by
    intro t ht htCapture
    obtain ⟨w, hw⟩ := htCapture
    exact (not_le_of_gt (havoid t ht w)) hw
  obtain ⟨tExit, tReturn, htExit, htReturn,
      htExitCapture, htReturnCapture, hlt, hwidth, hbetween⟩ :=
    exists_consecutive_mem_separated_by_avoided_Icc
      hcapture hW hpre hpost havoidCapture
  exact ⟨tExit, tReturn, htExit, htReturn, htExitCapture,
    htReturnCapture, hlt, hwidth, hbetween⟩

end RHTower
