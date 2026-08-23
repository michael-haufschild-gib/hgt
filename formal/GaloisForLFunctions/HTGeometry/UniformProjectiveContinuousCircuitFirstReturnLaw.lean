import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw
import GaloisForLFunctions.HTGeometry.ContinuousFirstReturnGapLaw

/-!
# Uniform projective first return to a continuous circuit set

Compactness closes the gap between a continuous-circuit hard interval and a
literal first re-entry.  The capture set uses distance to the complete compact
image of every circuit architecture in the gate budget, saturated by global
phase.  Its closedness produces consecutive visits on both sides of each hard
block.  No gate discretisation enters the first-return step.
-/

open Matrix Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The zero-gate circuit places the identity in every phase-saturated bounded
circuit image. -/
theorem one_mem_phaseCircuitMatrixImageAtMost (n s : ℕ) :
    (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈
      phaseCircuitMatrixImageAtMost n s := by
  let A : TwoQubitArchitecture n 0 := ⟨Fin.elim0, fun r => Fin.elim0 r⟩
  let C : TwoQubitCircuit n := ⟨0, A, Fin.elim0⟩
  rw [mem_phaseCircuitMatrixImageAtMost_iff]
  refine ⟨1, by norm_num, C, by simp [C], ?_⟩
  simp [C, A, TwoQubitCircuit.eval, TwoQubitArchitecture.contraction]

/-- Distance to a nonempty compact target is achieved by an actual target. -/
theorem exists_compactTarget_minDist
    {X : Type*} [PseudoMetricSpace X] {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (x : X) :
    ∃ y ∈ K, dist x y = Metric.infDist x K := by
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKne
    (continuous_const.dist continuous_id).continuousOn
  letI : Nonempty K := hKne.to_subtype
  have hmin' : ∀ z ∈ K, dist x y ≤ dist x z := by
    change ∀ᶠ z in Filter.principal K, dist x y ≤ dist x z at hmin
    simpa only [Filter.eventually_principal] using hmin
  refine ⟨y, hy, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hy)⟩
  rw [Metric.infDist_eq_iInf]
  exact le_ciInf fun z => hmin' z z.2

/-- Capture times at fixed distance from a target form a closed set. -/
theorem isClosed_compactTargetCaptureTimeSet
    {X : Type*} [PseudoMetricSpace X]
    (orbit : ℝ → X) (horbit : Continuous orbit)
    (K : Set X) (eps : ℝ) :
    IsClosed {t | Metric.infDist (orbit t) K ≤ eps} := by
  exact isClosed_le ((by fun_prop : Continuous fun t =>
    Metric.infDist (orbit t) K)) continuous_const

/-- **Complete continuous-circuit first-return law.**  Every fixed-error hard
block supplied by projective spectral entropy lies inside one genuine
excursion between consecutive visits to the entire continuous circuit image.
The visits are actual circuits, not net points, and every intervening time is
far from every allowed circuit and every global phase. -/
theorem maximallyProjective_projectiveSpectralCircuitTarget_consecutiveVisitGaps_of_entropy
    {n d s : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hEntropy : atMostQuarterCircuitEntropyBound n s < ((2 ^ d : ℕ) : ℝ)) :
    ∃ W : ℝ, 0 < W ∧ ∃ gap B : ℝ, 0 ≤ gap ∧ 0 ≤ B ∧
      ∀ a : ℝ, ∃ u tExit tReturn : ℝ,
        u ∈ Icc a (a + gap) ∧
        tExit ∈ Icc (u - B) u ∧
        tReturn ∈ Icc (u + W) (u + W + B) ∧
        (∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
          C.gateCount ≤ s ∧
          ‖projectiveSpectralMatrix e V
              (RHTower.projectivePhysicalPhaseFlow energy tExit) -
            c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
              (1 / 20 : ℝ)) ∧
        (∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
          C.gateCount ≤ s ∧
          ‖projectiveSpectralMatrix e V
              (RHTower.projectivePhysicalPhaseFlow energy tReturn) -
            c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
              (1 / 20 : ℝ)) ∧
        tExit < tReturn ∧ W ≤ tReturn - tExit ∧
        ∀ t ∈ Ioo tExit tReturn,
          ∀ c : ℂ, ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
            C.gateCount ≤ s → (1 / 20 : ℝ) <
              ‖projectiveSpectralMatrix e V
                  (RHTower.projectivePhysicalPhaseFlow energy t) -
                c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  let orbit : ℝ → Matrix (Fin n → Bool) (Fin n → Bool) ℂ := fun t =>
    projectiveSpectralMatrix e V
      (RHTower.projectivePhysicalPhaseFlow energy t)
  let K := phaseCircuitMatrixImageAtMost n s
  let capture : Set ℝ := {t | Metric.infDist (orbit t) K ≤ (1 / 20 : ℝ)}
  have horbit : Continuous orbit :=
    (continuous_projectiveSpectralMatrix e V).comp
      (RHTower.uniformContinuous_projectivePhysicalPhaseFlow energy).continuous
  have hKcompact : IsCompact K := isCompact_phaseCircuitMatrixImageAtMost n s
  have hKne : K.Nonempty := phaseCircuitMatrixImageAtMost_nonempty n s
  have hcapture : IsClosed capture :=
    isClosed_compactTargetCaptureTimeSet orbit horbit K (1 / 20 : ℝ)
  obtain ⟨W, hW, gap, hgap, hhard⟩ :=
    maximallyProjective_projectiveSpectralCircuitHardIntervals_uniformError_of_entropy
      energy hmax e V hEntropy
  let U : Set (Fin d → UnitAddCircle) :=
    (projectiveSpectralMatrix e V) ⁻¹'
      Metric.ball (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) (1 / 20 : ℝ)
  have hUopen : IsOpen U :=
    Metric.isOpen_ball.preimage (continuous_projectiveSpectralMatrix e V)
  have horbitZero : projectiveSpectralMatrix e V (0 : Fin d → UnitAddCircle) = 1 := by
    have hdiag : Matrix.diagonal (fun q : Fin n → Bool =>
        fourier 1 (RHTower.zeroAnchoredPhase d
          (0 : Fin d → UnitAddCircle) (e q))) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        rw [Matrix.diagonal_apply_eq]
        simp only [Matrix.one_apply, if_pos]
        generalize hr : e i = r
        refine Fin.cases ?_ (fun k => ?_) r <;>
          simp [RHTower.zeroAnchoredPhase]
      · simp [hij]
    rw [projectiveSpectralMatrix, hdiag, Matrix.mul_one]
    exact V.2.2
  have hUne : U.Nonempty := by
    refine ⟨0, ?_⟩
    simp [U, Metric.mem_ball, horbitZero]
  obtain ⟨B, hB, hrec⟩ := denseAddOrbit_open_hits_syndetically
    (RHTower.projectivePhysicalPhaseFlowHom energy)
    (RHTower.denseRange_projectivePhysicalPhaseFlowHom energy hmax)
    hUopen hUne
  refine ⟨W, hW, gap, B, hgap, hB, ?_⟩
  intro a
  obtain ⟨u, hu, huHard⟩ := hhard a
  have hpre : ∃ t ∈ Icc (u - B) u, t ∈ capture := by
    obtain ⟨t, ht, htU⟩ := hrec (u - B)
    change RHTower.projectivePhysicalPhaseFlow energy t ∈ U at htU
    refine ⟨t, ⟨ht.1, by linarith [ht.2]⟩, ?_⟩
    have hdist : dist (orbit t) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) <
        (1 / 20 : ℝ) := by
      simpa [U, orbit, Metric.mem_ball] using htU
    have honeK : (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈ K := by
      exact one_mem_phaseCircuitMatrixImageAtMost n s
    exact (Metric.infDist_le_dist_of_mem honeK).trans hdist.le
  have hpost : ∃ t ∈ Icc (u + W) (u + W + B), t ∈ capture := by
    obtain ⟨t, ht, htU⟩ := hrec (u + W)
    change RHTower.projectivePhysicalPhaseFlow energy t ∈ U at htU
    refine ⟨t, ht, ?_⟩
    have hdist : dist (orbit t) (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) <
        (1 / 20 : ℝ) := by
      simpa [U, orbit, Metric.mem_ball] using htU
    have honeK : (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈ K := by
      exact one_mem_phaseCircuitMatrixImageAtMost n s
    exact (Metric.infDist_le_dist_of_mem honeK).trans hdist.le
  have havoid : ∀ t ∈ Icc u (u + W), t ∉ capture := by
    intro t ht htcap
    have hfar : (1 / 10 : ℝ) ≤ Metric.infDist (orbit t) K := by
      rw [Metric.le_infDist hKne]
      intro M hM
      obtain ⟨c, hc, C, hCs, rfl⟩ :=
        mem_phaseCircuitMatrixImageAtMost_iff.mp hM
      simpa [orbit, dist_eq_norm] using huHard t ht c hc C hCs
    exact (not_le_of_gt (by norm_num : (1 / 20 : ℝ) < 1 / 10))
      (hfar.trans htcap)
  obtain ⟨tExit, tReturn, htExit, htReturn, hExit, hReturn,
      hlt, hwidth, hbetween⟩ :=
    exists_consecutive_mem_separated_by_avoided_Icc
      hcapture hW.le hpre hpost havoid
  obtain ⟨MExit, hMExit, hMExitDist⟩ :=
    exists_compactTarget_minDist hKcompact hKne (orbit tExit)
  obtain ⟨cExit, hcExit, CExit, hCExit, rfl⟩ :=
    mem_phaseCircuitMatrixImageAtMost_iff.mp hMExit
  have hExit' : ‖orbit tExit -
      cExit • (CExit.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
        (1 / 20 : ℝ) := by
    rw [← dist_eq_norm, hMExitDist]
    exact hExit
  obtain ⟨MReturn, hMReturn, hMReturnDist⟩ :=
    exists_compactTarget_minDist hKcompact hKne (orbit tReturn)
  obtain ⟨cReturn, hcReturn, CReturn, hCReturn, rfl⟩ :=
    mem_phaseCircuitMatrixImageAtMost_iff.mp hMReturn
  have hReturn' : ‖orbit tReturn -
      cReturn • (CReturn.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
        (1 / 20 : ℝ) := by
    rw [← dist_eq_norm, hMReturnDist]
    exact hReturn
  refine ⟨u, tExit, tReturn, hu, htExit, htReturn,
    ⟨cExit, hcExit, CExit, hCExit, by simpa [orbit] using hExit'⟩,
    ⟨cReturn, hcReturn, CReturn, hCReturn, by simpa [orbit] using hReturn'⟩,
    hlt, hwidth, ?_⟩
  intro t ht c hc C hCs
  have hfar : (1 / 20 : ℝ) < Metric.infDist (orbit t) K :=
    lt_of_not_ge (hbetween t ht)
  have hmem : c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ∈ K :=
    mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨c, hc, C, hCs, rfl⟩
  exact hfar.trans_le (by
    simpa [orbit, dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (x := orbit t) hmem))

/-- Physical Schrödinger form of the complete continuous-circuit first-return
law, with global phase treated as operationally invisible. -/
theorem maximallyProjective_unitaryEvolution_continuousCircuitTarget_consecutiveVisitGaps_of_entropy
    {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy (fun i => hH.eigenvalues (e.symm i)))
    (hEntropy : atMostQuarterCircuitEntropyBound n s < ((2 ^ d : ℕ) : ℝ)) :
    ∃ W : ℝ, 0 < W ∧ ∃ gap B : ℝ, 0 ≤ gap ∧ 0 ≤ B ∧
      ∀ a : ℝ, ∃ u tExit tReturn : ℝ,
        u ∈ Icc a (a + gap) ∧
        tExit ∈ Icc (u - B) u ∧
        tReturn ∈ Icc (u + W) (u + W + B) ∧
        (∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
          C.gateCount ≤ s ∧
          ‖unitaryEvolution H tExit -
            c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
              (1 / 20 : ℝ)) ∧
        (∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
          C.gateCount ≤ s ∧
          ‖unitaryEvolution H tReturn -
            c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
              (1 / 20 : ℝ)) ∧
        tExit < tReturn ∧ W ≤ tReturn - tExit ∧
        ∀ t ∈ Ioo tExit tReturn,
          ∀ c : ℂ, ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
            C.gateCount ≤ s → (1 / 20 : ℝ) <
              ‖unitaryEvolution H t -
                c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨W, hW, gap, B, hgap, hB, hblocks⟩ :=
    maximallyProjective_projectiveSpectralCircuitTarget_consecutiveVisitGaps_of_entropy
      (fun i => hH.eigenvalues (e.symm i)) hmax e
      (hermitianEigenbasisUnitary hH) hEntropy
  refine ⟨W, hW, gap, B, hgap, hB, ?_⟩
  intro a
  obtain ⟨u, tExit, tReturn, hu, htExit, htReturn,
      ⟨cExit, hcExit, CExit, hCExit, hExit⟩,
      ⟨cReturn, hcReturn, CReturn, hCReturn, hReturn⟩,
      hlt, hwidth, hbetween⟩ := hblocks a
  let anchor : ℝ → ℂ := fun t =>
    Complex.exp (-(Complex.I * (t * hH.eigenvalues (e.symm 0))))
  have hanchor (t : ℝ) : ‖anchor t‖ = 1 := by
    dsimp [anchor]
    rw [Complex.norm_exp]
    simp
  have hphysical (t : ℝ) : unitaryEvolution H t =
      anchor t • projectiveSpectralMatrix e
        (hermitianEigenbasisUnitary hH)
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) := by
    exact unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix e hH t
  have hExitPhysical : ‖unitaryEvolution H tExit -
      (anchor tExit * cExit) •
        (CExit.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
        (1 / 20 : ℝ) := by
    rw [hphysical]
    have hfactor :
        anchor tExit • projectiveSpectralMatrix e
              (hermitianEigenbasisUnitary hH)
                (RHTower.projectivePhysicalPhaseFlow
                  (fun i => hH.eigenvalues (e.symm i)) tExit) -
            (anchor tExit * cExit) •
              (CExit.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
          anchor tExit •
            (projectiveSpectralMatrix e (hermitianEigenbasisUnitary hH)
                (RHTower.projectivePhysicalPhaseFlow
                  (fun i => hH.eigenvalues (e.symm i)) tExit) -
              cExit •
                (CExit.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
      module
    rw [hfactor, norm_smul, hanchor, one_mul]
    exact hExit
  have hReturnPhysical : ‖unitaryEvolution H tReturn -
      (anchor tReturn * cReturn) •
        (CReturn.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ ≤
        (1 / 20 : ℝ) := by
    rw [hphysical]
    have hfactor :
        anchor tReturn • projectiveSpectralMatrix e
              (hermitianEigenbasisUnitary hH)
                (RHTower.projectivePhysicalPhaseFlow
                  (fun i => hH.eigenvalues (e.symm i)) tReturn) -
            (anchor tReturn * cReturn) •
              (CReturn.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
          anchor tReturn •
            (projectiveSpectralMatrix e (hermitianEigenbasisUnitary hH)
                (RHTower.projectivePhysicalPhaseFlow
                  (fun i => hH.eigenvalues (e.symm i)) tReturn) -
              cReturn •
                (CReturn.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
      module
    rw [hfactor, norm_smul, hanchor, one_mul]
    exact hReturn
  refine ⟨u, tExit, tReturn, hu, htExit, htReturn,
    ⟨anchor tExit * cExit, by simp [hanchor, hcExit],
      CExit, hCExit, hExitPhysical⟩,
    ⟨anchor tReturn * cReturn, by simp [hanchor, hcReturn],
      CReturn, hCReturn, hReturnPhysical⟩,
    hlt, hwidth, ?_⟩
  intro t ht c hc C hCs
  have hanchorNe : anchor t ≠ 0 := norm_ne_zero_iff.mp (by
    rw [hanchor]
    norm_num)
  let cProjective := (anchor t)⁻¹ * c
  have hcProjective : ‖cProjective‖ = 1 := by
    simp [cProjective, hanchor, hc]
  have hproj := hbetween t ht cProjective hcProjective C hCs
  rw [hphysical]
  have hfactor :
      anchor t • projectiveSpectralMatrix e
            (hermitianEigenbasisUnitary hH)
              (RHTower.projectivePhysicalPhaseFlow
                (fun i => hH.eigenvalues (e.symm i)) t) -
          c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
        anchor t •
          (projectiveSpectralMatrix e (hermitianEigenbasisUnitary hH)
              (RHTower.projectivePhysicalPhaseFlow
                (fun i => hH.eigenvalues (e.symm i)) t) -
            cProjective •
              (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
    dsimp [cProjective]
    rw [smul_sub, smul_smul]
    rw [show anchor t * ((anchor t)⁻¹ * c) = c by
      rw [← mul_assoc, mul_inv_cancel₀ hanchorNe, one_mul]]
  rw [hfactor, norm_smul, hanchor, one_mul]
  exact hproj

end

end GaloisForLFunctions.HTGeometry
