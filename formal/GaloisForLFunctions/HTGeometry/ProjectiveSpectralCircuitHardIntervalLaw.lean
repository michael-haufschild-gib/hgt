import GaloisForLFunctions.HTGeometry.ProjectiveSpectralTorusContinuousCircuitHardnessLaw
import GaloisForLFunctions.RHTower.StaticChoiSyndeticComplexityLaw
import GaloisForLFunctions.RHTower.StaticChoiContinuousHardGapLaw

/-!
# Syndetic continuous-circuit-hard intervals for every maximal spectral flow

The projective hard seed on an arbitrary eigenbasis torus is an open robust
target.  Maximal projective spectral rank makes the physical relative-phase
flow dense, so compact-group recurrence visits this target syndetically.
Uniform continuity then thickens every visit into one common positive-duration
interval.  The result covers the complete continuous `SU(4)` circuit family,
all architectures, and arbitrary global phase; no finite gate dictionary is
used.
-/

open Matrix Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Physical-basis unitary matrix associated with a zero-anchored projective
spectral phase. -/
def projectiveSpectralMatrix {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (x : Fin d → UnitAddCircle) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
    Matrix.diagonal (fun q => fourier 1 (RHTower.zeroAnchoredPhase d x (e q))) *
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1

theorem continuous_projectiveSpectralMatrix {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
    Continuous (projectiveSpectralMatrix e V) := by
  have hphase : ∀ q : Fin (d + 1), Continuous (fun x : Fin d → UnitAddCircle =>
      fourier 1 (RHTower.zeroAnchoredPhase d x q)) := by
    intro q
    refine Fin.cases ?_ (fun i => ?_) q
    · change Continuous (fun _ : Fin d → UnitAddCircle =>
        fourier 1 (0 : UnitAddCircle))
      exact continuous_const
    · change Continuous (fun x : Fin d → UnitAddCircle => fourier 1 (x i))
      exact (fourier (T := (1 : ℝ)) 1).continuous.comp (continuous_apply i)
  have hdiag : Continuous (fun x : Fin d → UnitAddCircle =>
      Matrix.diagonal (fun q : Fin n → Bool =>
        fourier 1 (RHTower.zeroAnchoredPhase d x (e q)))) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hij : i = j
    · subst j
      simpa using hphase (e i)
    · simpa [Matrix.diagonal_apply_ne _ hij] using
        (continuous_const : Continuous (fun _ : Fin d → UnitAddCircle => (0 : ℂ)))
  exact (continuous_const.mul hdiag).mul continuous_const

/-- Relative additive phase extracted from an arbitrary unit complex packet. -/
def projectivePhaseOfUnitPacket {d : ℕ}
    (phase : Fin (d + 1) → ℂ) (hphase : ∀ i, ‖phase i‖ = 1) :
    Fin d → UnitAddCircle := fun i =>
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
    ⟨phase i.succ / phase 0, by
      change phase i.succ / phase 0 ∈ Metric.sphere (0 : ℂ) 1
      rw [Metric.mem_sphere, dist_zero_right]
      rw [norm_div, hphase i.succ, hphase 0, div_one]⟩

theorem fourier_projectivePhaseOfUnitPacket {d : ℕ}
    (phase : Fin (d + 1) → ℂ) (hphase : ∀ i, ‖phase i‖ = 1)
    (i : Fin d) :
    fourier 1 (projectivePhaseOfUnitPacket phase hphase i) =
      phase i.succ / phase 0 := by
  rw [fourier_one]
  rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
  exact congrArg Subtype.val
    ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply
      ⟨phase i.succ / phase 0, by
        change phase i.succ / phase 0 ∈ Metric.sphere (0 : ℂ) 1
        rw [Metric.mem_sphere, dist_zero_right]
        rw [norm_div, hphase i.succ, hphase 0, div_one]⟩)

/-- A determinant-one packet is its zero-anchored projective representative
times its first global phase. -/
theorem spectralPhaseUnitary_eq_phase_zero_smul_projectiveSpectralMatrix
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (phase : Fin (d + 1) → ℂ) (hphase : ∀ i, ‖phase i‖ = 1) :
    (spectralPhaseUnitary e V phase hphase :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      phase 0 • projectiveSpectralMatrix e V
        (projectivePhaseOfUnitPacket phase hphase) := by
  have hp0 : phase 0 ≠ 0 := norm_ne_zero_iff.mp (by rw [hphase 0]; norm_num)
  have hdiag : Matrix.diagonal (phase ∘ e) =
      phase 0 • Matrix.diagonal (fun q =>
        fourier 1 (RHTower.zeroAnchoredPhase d
          (projectivePhaseOfUnitPacket phase hphase) (e q))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.smul_apply,
        Matrix.diagonal_apply_eq]
      simp only [smul_eq_mul]
      let r := e i
      change phase r = phase 0 * fourier 1
        (RHTower.zeroAnchoredPhase d
          (projectivePhaseOfUnitPacket phase hphase) r)
      refine Fin.cases ?_ (fun k => ?_) r
      · simp [RHTower.zeroAnchoredPhase]
      · rw [show RHTower.zeroAnchoredPhase d
            (projectivePhaseOfUnitPacket phase hphase) k.succ =
            projectivePhaseOfUnitPacket phase hphase k by rfl,
          fourier_projectivePhaseOfUnitPacket]
        field_simp
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply,
        Matrix.diagonal_apply_ne _ hij]
      simp
  change ((V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
      Matrix.diagonal (phase ∘ e)) *
      (V⁻¹ : Matrix.unitaryGroup (Fin n → Bool) ℂ).1 = _
  rw [hdiag]
  simp only [projectiveSpectralMatrix, Matrix.mul_smul, Matrix.smul_mul]

/-- Projective form of the universal spectral-torus hard seed. -/
theorem exists_fixedError_projectivePhase_continuousCircuitHard
    {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hs : s * 16 < d) :
    ∃ x : Fin d → UnitAddCircle,
      ∃ ε : ℝ, 0 < ε ∧
        ∀ (c : ℂ), ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
          C.gateCount ≤ s →
          ε ≤ ‖projectiveSpectralMatrix e V x -
            c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨phase, hphase, _hprod, ε, hε, hhard⟩ :=
    exists_fixedError_projectiveSpectralPhase_continuousCircuitHard e V hs
  let x := projectivePhaseOfUnitPacket phase hphase
  refine ⟨x, ε, hε, ?_⟩
  intro c hc C hCs
  have hp0 : ‖phase 0‖ = 1 := hphase 0
  have h := hhard (phase 0 * c) (by rw [norm_mul, hp0, hc, one_mul]) C hCs
  rw [spectralPhaseUnitary_eq_phase_zero_smul_projectiveSpectralMatrix] at h
  have hfactor :
      phase 0 • projectiveSpectralMatrix e V x -
          (phase 0 * c) •
            (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
        phase 0 • (projectiveSpectralMatrix e V x -
          c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
    module
  rw [hfactor, norm_smul, hp0, one_mul] at h
  exact h

/-- Every maximally projective spectrum reaches fixed-error continuous-circuit
hard endpoints syndetically in physical time, for its actual eigenbasis. -/
theorem maximallyProjective_projectiveSpectralCircuitHardTimes_syndetic
    {n d s : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hs : s * 16 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ t ∈ Set.Icc a (a + L),
        ∀ (c : ℂ), ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
          C.gateCount ≤ s →
          ε ≤ ‖projectiveSpectralMatrix e V
              (RHTower.projectivePhysicalPhaseFlow energy t) -
            c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨x, ε, hε, hhard⟩ :=
    exists_fixedError_projectivePhase_continuousCircuitHard e V hs
  let U : Set (Fin d → UnitAddCircle) :=
    (projectiveSpectralMatrix e V) ⁻¹'
      Metric.ball (projectiveSpectralMatrix e V x) (ε / 2)
  have hUopen : IsOpen U :=
    Metric.isOpen_ball.preimage (continuous_projectiveSpectralMatrix e V)
  have hUne : U.Nonempty := by
    refine ⟨x, ?_⟩
    simp [U, Metric.mem_ball, hε]
  obtain ⟨L, hL, hhit⟩ := denseAddOrbit_open_hits_syndetically
    (RHTower.projectivePhysicalPhaseFlowHom energy)
    (RHTower.denseRange_projectivePhysicalPhaseFlowHom energy hmax)
    hUopen hUne
  refine ⟨ε / 2, by positivity, L, hL, ?_⟩
  intro a
  obtain ⟨t, ht, htU⟩ := hhit a
  change RHTower.projectivePhysicalPhaseFlow energy t ∈ U at htU
  refine ⟨t, ht, ?_⟩
  have hclose : ‖projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy t) -
      projectiveSpectralMatrix e V x‖ < ε / 2 := by
    simpa [U, Metric.mem_ball, dist_eq_norm] using htU
  intro c hc C hCs
  have hseed := hhard c hc C hCs
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (projectiveSpectralMatrix e V x)
    (projectiveSpectralMatrix e V
      (RHTower.projectivePhysicalPhaseFlow energy t))
    (c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
  have hclose' : ‖projectiveSpectralMatrix e V x -
      projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy t)‖ < ε / 2 := by
    simpa [norm_sub_rev] using hclose
  linarith

/-- **Syndetic fixed-width continuous-circuit plateau blocks.**  For every
maximally projective spectrum and its actual eigenbasis, if `16s < D - 1`,
one positive error, one positive duration, and one finite recurrence gap work
forever.  Every gap window contains a full interval on which every circuit of
at most `s` continuous two-qubit gates is excluded, even up to global phase. -/
theorem maximallyProjective_projectiveSpectralCircuitHardIntervals_syndetic
    {n d s : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hs : s * 16 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : ℝ, 0 < W ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ a : ℝ, ∃ u ∈ Set.Icc a (a + L),
        ∀ t ∈ Set.Icc u (u + W),
          ∀ (c : ℂ), ‖c‖ = 1 → ∀ C : TwoQubitCircuit n,
            C.gateCount ≤ s →
            ε ≤ ‖projectiveSpectralMatrix e V
                (RHTower.projectivePhysicalPhaseFlow energy t) -
              c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨x, ε, hε, hhard⟩ :=
    exists_fixedError_projectivePhase_continuousCircuitHard e V hs
  have hucP : UniformContinuous (projectiveSpectralMatrix e V) :=
    CompactSpace.uniformContinuous_of_continuous
      (continuous_projectiveSpectralMatrix e V)
  have hucFlow := RHTower.uniformContinuous_projectivePhysicalPhaseFlow energy
  have huc : UniformContinuous (fun t : ℝ =>
      projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy t)) :=
    hucP.comp hucFlow
  obtain ⟨eta, heta, hmod⟩ :=
    (Metric.uniformContinuous_iff.mp huc) (ε / 4) (by positivity)
  let U : Set (Fin d → UnitAddCircle) :=
    (projectiveSpectralMatrix e V) ⁻¹'
      Metric.ball (projectiveSpectralMatrix e V x) (ε / 4)
  have hUopen : IsOpen U :=
    Metric.isOpen_ball.preimage (continuous_projectiveSpectralMatrix e V)
  have hUne : U.Nonempty := by
    refine ⟨x, ?_⟩
    simp [U, Metric.mem_ball, hε]
  obtain ⟨L, hL, hhit⟩ := denseAddOrbit_open_hits_syndetically
    (RHTower.projectivePhysicalPhaseFlowHom energy)
    (RHTower.denseRange_projectivePhysicalPhaseFlowHom energy hmax)
    hUopen hUne
  refine ⟨ε / 2, by positivity, eta / 2, by positivity, L, hL, ?_⟩
  intro a
  obtain ⟨u, hu, huU⟩ := hhit a
  change RHTower.projectivePhysicalPhaseFlow energy u ∈ U at huU
  refine ⟨u, hu, ?_⟩
  have huclose : ‖projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy u) -
      projectiveSpectralMatrix e V x‖ < ε / 4 := by
    simpa [U, Metric.mem_ball, dist_eq_norm] using huU
  intro t ht c hc C hCs
  have htu : dist t u < eta := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hmove := hmod htu
  have htclose : ‖projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy t) -
      projectiveSpectralMatrix e V x‖ < ε / 2 := by
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy t))
      (projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy u))
      (projectiveSpectralMatrix e V x)
    rw [dist_eq_norm] at hmove
    linarith
  have hseed := hhard c hc C hCs
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (projectiveSpectralMatrix e V x)
    (projectiveSpectralMatrix e V
      (RHTower.projectivePhysicalPhaseFlow energy t))
    (c • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
  have htclose' : ‖projectiveSpectralMatrix e V x -
      projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy t)‖ < ε / 2 := by
    simpa [norm_sub_rev] using htclose
  linarith

end
end GaloisForLFunctions.HTGeometry
