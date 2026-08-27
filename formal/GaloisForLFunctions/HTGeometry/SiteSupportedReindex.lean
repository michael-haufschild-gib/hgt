import GaloisForLFunctions.HTGeometry.ContinuousCircuitMetricEntropyLaw
import GaloisForLFunctions.HTGeometry.SiteSupportedLocalHamiltonian

/-!
# Site support and operator norm under qubit relabelling

An equivalence of physical sites induces the corresponding configuration equivalence.  Matrix
reindexing transports intrinsic site support to the image packet and preserves the physical
operator norm exactly.
-/

open scoped Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry

/-- Qubit configurations relabelled by a site equivalence. -/
def qubitConfigurationEquiv {V W : Type*} (e : V ≃ W) :
    FiniteQubitConfiguration V ≃ FiniteQubitConfiguration W :=
  Equiv.arrowCongr e (Equiv.refl Bool)

/-- Site support transports along a physical relabelling. -/
theorem isSiteSupported_reindexAlgEquiv
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (e : V ≃ W) (S : Finset V)
    {H : Matrix (FiniteQubitConfiguration V) (FiniteQubitConfiguration V) ℂ}
    (hH : IsSiteSupported S H) :
    IsSiteSupported (S.map e.toEmbedding)
      (Matrix.reindexAlgEquiv ℂ ℂ (qubitConfigurationEquiv e) H) := by
  constructor
  · rintro x y ⟨w, hw, hxy⟩
    apply hH.1
    refine ⟨e.symm w, ?_, ?_⟩
    · intro hm
      exact hw (Finset.mem_map.mpr ⟨e.symm w, hm, e.apply_symm_apply w⟩)
    · change x (e (e.symm w)) ≠ y (e (e.symm w))
      rw [e.apply_symm_apply]
      exact hxy
  · intro x y x' y' hx hy hout hout'
    apply hH.2
    · intro v hv
      have hev : e v ∈ S.map e.toEmbedding := Finset.mem_map.mpr ⟨v, hv, rfl⟩
      simpa [qubitConfigurationEquiv] using hx (e v) hev
    · intro v hv
      have hev : e v ∈ S.map e.toEmbedding := Finset.mem_map.mpr ⟨v, hv, rfl⟩
      simpa [qubitConfigurationEquiv] using hy (e v) hev
    · intro v hv
      have hev : e v ∉ S.map e.toEmbedding := by
        intro hm
        obtain ⟨z, hz, hez⟩ := Finset.mem_map.mp hm
        exact hv (e.injective hez ▸ hz)
      simpa [qubitConfigurationEquiv] using hout (e v) hev
    · intro v hv
      have hev : e v ∉ S.map e.toEmbedding := by
        intro hm
        obtain ⟨z, hz, hez⟩ := Finset.mem_map.mp hm
        exact hv (e.injective hez ▸ hz)
      simpa [qubitConfigurationEquiv] using hout' (e v) hev

/-- Simultaneous row-column reindexing preserves the physical operator norm. -/
theorem l2_opNorm_reindexAlgEquiv_eq
    {I J : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    [Fintype J] [Nonempty J] [DecidableEq J]
    (e : I ≃ J) (H : Matrix I I ℂ) :
    ‖Matrix.reindexAlgEquiv ℂ ℂ e H‖ = ‖H‖ := by
  apply le_antisymm (l2_opNorm_reindexAlgEquiv_le e H)
  have hback := l2_opNorm_reindexAlgEquiv_le e.symm
    (Matrix.reindexAlgEquiv ℂ ℂ e H)
  simpa using hback

/-- Self-adjointness is invariant under simultaneous row-column reindexing. -/
theorem isSelfAdjoint_reindexAlgEquiv
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) {H : Matrix I I ℂ} (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (Matrix.reindexAlgEquiv ℂ ℂ e H) := by
  exact Matrix.isHermitian_iff_isSelfAdjoint.mp
    ((Matrix.isHermitian_iff_isSelfAdjoint.mpr hH).reindex e)

end GaloisForLFunctions.HTGeometry
