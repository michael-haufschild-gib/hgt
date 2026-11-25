import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.MatrixLevels
import GaloisForLFunctions.HTGeometry.Quantum.AttainedOrbitCircuitMaximum
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.PrecisionFloor

/-! # Algebraic contacts of the projective Schrödinger evolution -/

open Set Metric Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
open PrecisionReturns
noncomputable section

/-- Evolution with the phase of the reference eigenvalue removed. -/
def relativeOrbit {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (H : selfAdjoint (Square (Bits N))) (t : ℝ) :=
  projectiveSpectralMatrix e (hermitianEigenbasisUnitary H.2.isHermitian)
    (RHTower.projectivePhysicalPhaseFlow (H.2.isHermitian.eigenvalues ∘ e.symm) t)

theorem continuous_relativeOrbit {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (H : selfAdjoint (Square (Bits N))) :
    Continuous (relativeOrbit e H) := (continuous_projectiveSpectralMatrix e _).comp
      (RHTower.uniformContinuous_projectivePhysicalPhaseFlow _).continuous

theorem infDist_relativeOrbit {N d : ℕ} (e : Bits N ≃ Fin (d+1)) (H : selfAdjoint (Square (Bits N)))
    (s : ℕ) (t : ℝ) : infDist (relativeOrbit e H t) (phaseCircuitMatrixImageAtMost N s)=
      orbitCircuitDistance H s t := by
  have iff (u : ℝ) : orbitCircuitDistance H s t≤u ↔
      infDist (relativeOrbit e H t) (phaseCircuitMatrixImageAtMost N s)≤u :=
    ((hasProjectiveCircuitApproximation_iff_infDist ..).symm.trans
      (physical_circuit_approximation_iff_spectral_capture e H s u t)).trans
      ((mem_projectiveContinuousCircuitCaptureTarget_iff e _ s u _).trans (hasProjectiveCircuitApproximation_iff_infDist ..))
  exact le_antisymm ((iff _).mp le_rfl) ((iff _).mpr le_rfl)

/-- Arbitrarily close earlier times have positive distance different
from the contact height. This includes both tangencies and entries. -/
private theorem contact_closure {f : ℝ → ℝ} (hf : Continuous f) {a v r : ℝ}
    (hav : a<v) (hr : 0<r) (hv : f v=r) (hprior : ∀ t∈Ioo a v, f t≠r) :
    v∈closure {t | 0<f t ∧ f t≠r} := by
  have hpos : ∀ᶠ t in 𝓝[<] v, 0<f t := nhdsWithin_le_nhds
    (hf.continuousAt.eventually (lt_mem_nhds (hr.trans_eq hv.symm)))
  have ha : ∀ᶠ t in 𝓝[<] v, a<t := nhdsWithin_le_nhds (lt_mem_nhds hav)
  have hl : ∀ᶠ t in 𝓝[<] v, t<v := self_mem_nhdsWithin
  exact mem_closure_of_tendsto (tendsto_id'.mpr (nhdsWithin_le_nhds : 𝓝[<] v ≤ 𝓝 v))
    ((hpos.and (ha.and hl)).mono (fun t ht => ⟨ht.1,hprior t ht.2⟩))

/-- A finite family of orbit-nonzero polynomials detects every first
contact at the given height, at all origins. The polynomial is in
relative matrix entries, so common spectral phase has been removed. -/
theorem orbit_contact_equations {R : Type*} [CommRing R] (κ : R →+* ℝ) {N d : ℕ}
    (e : Bits N ≃ Fin (d+1)) (H : selfAdjoint (Square (Bits N))) (s : ℕ) (r : R) (hr : 0<κ r) :
    let ev (t : ℝ) := entryEval κ (relativeOrbit e H t)
    ∃ F : Finset (EntryPolynomial N R), (∀ p∈F, ∃ t, ev t p≠0) ∧
      ∀ (a v : ℝ), a<v → orbitCircuitDistance H s v=κ r →
        (∀ t∈Ioo a v, orbitCircuitDistance H s t≠κ r) → ∃ p∈F, ev v p=0 := by
  obtain ⟨F,hF,hz⟩ := matrix_level_equations κ _ (continuous_relativeOrbit e H) s r
  refine ⟨F,hF,?_⟩
  intro a v hav hv hprior
  apply hz v ((infDist_relativeOrbit ..).trans hv)
  simpa only [infDist_relativeOrbit] using contact_closure (orbitCircuitDistance_lipschitz H s).continuous hav hr hv hprior

/-- A first affordable time from outside the tube is approached from above. -/
theorem firstVisit_left_contact {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ) (a : ℝ)
    {ε : ℝ} (hε : 0<ε) (hout : ε<orbitCircuitDistance H s a) :
    let v := firstVisit H a s ε
    a<v ∧ orbitCircuitDistance H s v=ε ∧ ∀ t∈Ioo a v, ε<orbitCircuitDistance H s t := by
  let v := firstVisit H a s ε
  have hl := firstVisit_isLeast H a s hε
  have hv := ExactContacts.CoarseVisits.firstVisit_distance H a s hε hout
  refine ⟨lt_of_le_of_ne hl.1.1 (fun h => hout.ne' ((congrArg (orbitCircuitDistance H s) h).trans hv)),hv,?_⟩
  intro t ht
  by_contra! h
  exact ht.2.not_ge (hl.2 ⟨ht.1.le,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr h⟩)

#print axioms orbit_contact_equations
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
