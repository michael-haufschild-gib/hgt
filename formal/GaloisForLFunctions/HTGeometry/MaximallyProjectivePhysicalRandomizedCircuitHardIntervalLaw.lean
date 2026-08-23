import GaloisForLFunctions.HTGeometry.ProjectiveSpectralRandomizedCircuitHardIntervalLaw
import GaloisForLFunctions.HTGeometry.MaximallyProjectivePhysicalCircuitHardIntervalLaw

/-!
# Physical randomized-circuit-hard intervals

Normalized Choi distance removes the anchor phase relating a Hermitian Hamiltonian's exact
Schrödinger evolution to its projective spectral flow.  Projective randomized hardness therefore
transfers without loss to the physical evolution.
-/

open Matrix Set Topology
open scoped Matrix.Norms.L2Operator BigOperators NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

open StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower
open _root_.RHTower

/--
**Universal physical randomized hard-interval law.**  Every finite Hermitian Hamiltonian with
maximally projective spectrum has syndetic positive-width intervals on which every bounded
continuous two-qubit circuit has a fixed normalized Choi error and every finite randomized mixture
of such circuits has a fixed pure-Choi fidelity deficit, independent of its support size.
-/
theorem maximallyProjective_unitaryEvolution_randomizedCircuitHardIntervals_syndetic
    {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy (fun i => hH.eigenvalues (e.symm i)))
    (hs : s * 16 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : ℝ, 0 < W ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ a : ℝ, ∃ u ∈ Set.Icc a (a + L),
        ∀ t ∈ Set.Icc u (u + W),
          (∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
            ε ≤ choiDist (unitaryEvolution H t)
              (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) ∧
          ∀ {C : Type u} [Fintype C]
            (circuit : C → TwoQubitCircuit n),
            (∀ i, (circuit i).gateCount ≤ s) →
            ∀ (weight : C → ℝ≥0), (∑ i, weight i) = 1 →
              (∑ i, (weight i : ℝ) *
                ‖inner ℂ (choiVector (unitaryEvolution H t))
                  (choiVector ((circuit i).eval :
                    Matrix (Fin n → Bool) (Fin n → Bool) ℂ))‖ ^ 2) ≤
                1 - ε ^ 2 := by
  obtain ⟨ε, hε, W, hW, L, hL, hhard⟩ :=
    maximallyProjective_projectiveSpectralRandomizedCircuitHardIntervals_syndetic.{u}
      (fun i => hH.eigenvalues (e.symm i)) hmax e
      (hermitianEigenbasisUnitary hH) hs
  refine ⟨ε, hε, W, hW, L, hL, ?_⟩
  intro a
  obtain ⟨u, hu, huHard⟩ := hhard a
  refine ⟨u, hu, ?_⟩
  intro t ht
  obtain ⟨hprojective, _⟩ := huHard t ht
  let anchor : ℂ :=
    Complex.exp (-(Complex.I * (t * hH.eigenvalues (e.symm 0))))
  have hanchor : ‖anchor‖ = 1 := by
    unfold anchor
    rw [Complex.norm_exp]
    simp
  have hphysical : ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
      ε ≤ choiDist (unitaryEvolution H t)
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    intro C hCs
    rw [unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix]
    rw [GaloisForLFunctions.RHTower.choiDist_smul_left anchor hanchor]
    simpa only [projectiveSpectralUnitary_coe] using hprojective C hCs
  refine ⟨hphysical, ?_⟩
  intro C _ circuit hgate weight hweight
  have hU : (unitaryEvolution H t)ᴴ * unitaryEvolution H t = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp
      (unitaryEvolution_mem_unitary hH.isSelfAdjoint t)
  exact GaloisForLFunctions.RHTower.randomizedChoiFidelity_le_of_choiDist_floor
    hU (fun i => (circuit i).eval) weight hweight hε.le
    (fun i => hphysical (circuit i) (hgate i))

end
end GaloisForLFunctions.HTGeometry
