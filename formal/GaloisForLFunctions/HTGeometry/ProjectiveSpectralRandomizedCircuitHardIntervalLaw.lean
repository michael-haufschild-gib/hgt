import GaloisForLFunctions.RHTower.ContinuousCircuitChoiRandomizationLaw
import GaloisForLFunctions.HTGeometry.OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

/-!
# Randomized circuit hardness on projective spectral hard intervals

A maximally projective finite spectrum produces syndetic positive-width intervals on which its
spectral orbit is separated, in normalized Choi trace distance, from every bounded two-qubit
circuit.  The same intervals defeat every finite randomized mixture of such circuits: its average
pure-Choi fidelity has a fixed deficit independent of the number of branches.

This closes the finite-randomization loophole without discretizing the continuous gate set.
-/

open Matrix Set Topology
open scoped Matrix.Norms.L2Operator BigOperators NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower
open _root_.RHTower
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw

/-- The unitary represented by a point of the projective spectral phase torus. -/
def projectiveSpectralUnitary {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (x : Fin d → UnitAddCircle) :
    Matrix.unitaryGroup (Fin n → Bool) ℂ :=
  spectralPhaseUnitary e V
    (fun q => fourier 1 (RHTower.zeroAnchoredPhase d x q))
    (by
      intro q
      rw [fourier_apply, Circle.norm_coe])

@[simp] theorem projectiveSpectralUnitary_coe {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (x : Fin d → UnitAddCircle) :
    (projectiveSpectralUnitary e V x :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      projectiveSpectralMatrix e V x := rfl

/--
**Growing-replica randomized hard-interval law.**

For every maximally projective finite spectrum and every circuit budget below one sixteenth of its
projective spectral dimension, there are syndetic positive-width time intervals on which:

* every continuous two-qubit circuit within the budget has a fixed positive normalized Choi
  trace-distance from the spectral evolution; and
* every finite probability mixture of such circuits has a fixed pure-Choi fidelity deficit.

The deficit is independent of the finite branch type, so the conclusion survives an arbitrarily
large finite circuit union or randomized algorithm.
-/
theorem maximallyProjective_projectiveSpectralRandomizedCircuitHardIntervals_syndetic
    {n d s : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : MaximallyProjectiveEnergy energy)
    (e : (Fin n → Bool) ≃ Fin (d + 1))
    (V : Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hs : s * 16 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : ℝ, 0 < W ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ a : ℝ, ∃ u ∈ Set.Icc a (a + L),
        ∀ t ∈ Set.Icc u (u + W),
          (∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
            ε ≤ choiDist
              (projectiveSpectralUnitary e V
                (RHTower.projectivePhysicalPhaseFlow energy t) :
                  Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
              (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) ∧
          ∀ {C : Type*} [Fintype C]
            (circuit : C → TwoQubitCircuit n),
            (∀ i, (circuit i).gateCount ≤ s) →
            ∀ (weight : C → ℝ≥0), (∑ i, weight i) = 1 →
              (∑ i, (weight i : ℝ) *
                ‖inner ℂ
                  (choiVector
                    (projectiveSpectralUnitary e V
                      (RHTower.projectivePhysicalPhaseFlow energy t) :
                        Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
                  (choiVector ((circuit i).eval :
                    Matrix (Fin n → Bool) (Fin n → Bool) ℂ))‖ ^ 2) ≤
                1 - ε ^ 2 := by
  obtain ⟨x, εop, hεop, hhard⟩ :=
    exists_fixedError_projectivePhase_continuousCircuitHard e V hs
  let Ux := projectiveSpectralUnitary e V x
  have hexclude : ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
      ∀ c : ℂ, ‖c‖ = 1 →
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≠
          c • (Ux : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    intro C hCs c hc hEq
    have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
    have hcinv : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
    have hrecover : c⁻¹ •
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
          (Ux : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
      rw [hEq, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hsep := hhard c⁻¹ hcinv C hCs
    rw [← projectiveSpectralUnitary_coe, ← hrecover, sub_self, norm_zero] at hsep
    linarith
  obtain ⟨δ, hδ, hseed⟩ :=
    GaloisForLFunctions.RHTower.exists_positive_choiDist_of_projectiveCircuit_exclusion
      Ux.2.1 hexclude
  let O : Set (Fin d → UnitAddCircle) :=
    {y | choiDist
      (Ux : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
      (projectiveSpectralUnitary e V y :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) < δ / 4}
  have hcontU : Continuous (fun y : Fin d → UnitAddCircle =>
      (projectiveSpectralUnitary e V y :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
    simpa only [projectiveSpectralUnitary_coe] using
      continuous_projectiveSpectralMatrix e V
  have hOopen : IsOpen O := by
    exact isOpen_lt
      ((GaloisForLFunctions.RHTower.continuous_choiDist_left
        (Ux : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).comp hcontU)
      continuous_const
  have hOne : O.Nonempty := by
    refine ⟨x, ?_⟩
    change choiDist
      (Ux : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
      (Ux : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) < δ / 4
    rw [choiDist_self Fintype.card_pos Ux.2.1]
    linarith
  obtain ⟨L, hL, hhit⟩ := denseAddOrbit_open_hits_syndetically
    (RHTower.projectivePhysicalPhaseFlowHom energy)
    (RHTower.denseRange_projectivePhysicalPhaseFlowHom energy hmax)
    hOopen hOne
  have hucP : UniformContinuous (projectiveSpectralMatrix e V) :=
    CompactSpace.uniformContinuous_of_continuous
      (continuous_projectiveSpectralMatrix e V)
  have hucFlow := RHTower.uniformContinuous_projectivePhysicalPhaseFlow energy
  have huc : UniformContinuous (fun t : ℝ =>
      projectiveSpectralMatrix e V
        (RHTower.projectivePhysicalPhaseFlow energy t)) :=
    hucP.comp hucFlow
  obtain ⟨eta, heta, hmod⟩ :=
    (Metric.uniformContinuous_iff.mp huc) (δ / 4) (by positivity)
  refine ⟨δ / 2, by positivity, eta / 2, by positivity, L, hL, ?_⟩
  intro a
  obtain ⟨u, hu, huO⟩ := hhit a
  refine ⟨u, hu, ?_⟩
  intro t ht
  have htu : dist t u < eta := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  have hmoveOp := hmod htu
  have hmove : choiDist
      (projectiveSpectralUnitary e V
        (RHTower.projectivePhysicalPhaseFlow energy u) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
      (projectiveSpectralUnitary e V
        (RHTower.projectivePhysicalPhaseFlow energy t) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) < δ / 4 := by
    apply lt_of_le_of_lt
      (choiDist_le_l2_opNorm_sub _ _
          (projectiveSpectralUnitary e V
            (RHTower.projectivePhysicalPhaseFlow energy u)).2.1
          (projectiveSpectralUnitary e V
            (RHTower.projectivePhysicalPhaseFlow energy t)).2.1)
    simpa only [projectiveSpectralUnitary_coe, dist_eq_norm,
      norm_sub_rev] using hmoveOp
  have huSeed : choiDist
      (Ux : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
      (projectiveSpectralUnitary e V
        (RHTower.projectivePhysicalPhaseFlow energy u) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) < δ / 4 := huO
  have hpoint : ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
      δ / 2 ≤ choiDist
        (projectiveSpectralUnitary e V
          (RHTower.projectivePhysicalPhaseFlow energy t) :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    intro C hCs
    have htri1 := choiDist_triangle Fintype.card_pos Ux.2.1
      (projectiveSpectralUnitary e V
        (RHTower.projectivePhysicalPhaseFlow energy u)).2.1
      (C.eval).2.1
    have htri2 := choiDist_triangle Fintype.card_pos
      (projectiveSpectralUnitary e V
        (RHTower.projectivePhysicalPhaseFlow energy u)).2.1
      (projectiveSpectralUnitary e V
        (RHTower.projectivePhysicalPhaseFlow energy t)).2.1
      (C.eval).2.1
    have hseedC := hseed C hCs
    linarith
  refine ⟨hpoint, ?_⟩
  intro C _ circuit hgate weight hweight
  exact GaloisForLFunctions.RHTower.randomizedChoiFidelity_le_of_choiDist_floor
    (projectiveSpectralUnitary e V
      (RHTower.projectivePhysicalPhaseFlow energy t)).2.1
    (fun i => (circuit i).eval) weight hweight (by positivity)
    (fun i => hpoint (circuit i) (hgate i))

end
end GaloisForLFunctions.HTGeometry
