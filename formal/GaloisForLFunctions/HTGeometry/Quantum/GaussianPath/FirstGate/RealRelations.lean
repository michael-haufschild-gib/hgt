import GaloisForLFunctions.HTGeometry.QuditPathRecurrenceCollisionCapstone
import GaloisForLFunctions.HTGeometry.RealRelationRootPacketBridge

/-! # Almost-sure avoidance of a prescribed real spectral relation -/
open Matrix MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section

/-- Every simple labeling of the roots gives the same elementary
symmetric coefficients after specialization of the Hamiltonian. -/
private theorem root_coefficients {m D : ℕ} (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (θ : Fin m → ℝ) (e : Fin D → ℝ) (hi : Function.Injective e)
    (hr : ∀ i, matrixCharpolyRelation (spectralEnsembleMatrix P θ,(e i:ℂ))=0) :
    ∀ j : Fin (Fintype.card (Fin D)),
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (θ i:ℂ))
          (matrixCharacteristicElementaryPolynomial (spectralGenericMatrix P) j) =
        ((MvPolynomial.eval e (MvPolynomial.esymm (Fin D) ℝ (j.val+1)):ℝ):ℂ) := by
  intro j
  rw [eval_matrixCharacteristicElementaryPolynomial,map_spectralGenericMatrix_eq θ,
    matrixCharacteristicElementaryCoefficient_eq_rootPacket _ (fun i => (e i:ℂ))
      (fun a b h => hi (Complex.ofReal_injective h)) hr j]
  exact esymm_eval₂_cast e (j.val+1)

/-- Even a fixed nonrational balanced linear relation has probability
zero. The exceptional set covers all permutations of the energy labels. -/
theorem ae_no_fixed_real_relation {m D : ℕ} (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (hs : SpectrumEscapesRealRelations (range (spectralEnsembleMatrix P)))
    (c : Fin D → ℝ) (hbal : ∑ i, c i=0) (hc : c≠0) :
    ∀ᵐ θ ∂(volume : Measure (Fin m → ℝ)), ∀ e : Fin D → ℝ, Function.Injective e →
      (∀ i, matrixCharpolyRelation (spectralEnsembleMatrix P θ,(e i:ℂ))=0) → ∑ i, c i*e i ≠ 0 := by
  classical
  let F := matrixCharacteristicElementaryPolynomial (spectralGenericMatrix P)
  let Q := linearRelationObstructionPullback F c
  obtain ⟨_,⟨p,rfl⟩,e,hi,hr,hesc⟩ := hs c hbal hc
  have hw : MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (p i:ℂ)) Q ≠ 0 := by
    rw [show Q=linearRelationObstructionPullback F c from rfl,
      eval_linearRelationObstructionPullback_value F c _ e (root_coefficients P p e hi hr)]
    exact_mod_cast (linearRelationOrbitValue_ne_zero_iff c e).mpr hesc
  have hfull := (complexPolynomialRealAvoidanceSet_dense_residual_fullMeasure
    (fun _ : ℕ => Q) (fun _ => ⟨p,hw⟩)).2.2
  have ha : ∀ᵐ θ ∂(volume : Measure (Fin m → ℝ)), θ ∈ complexPolynomialRealAvoidanceSet (fun _ : ℕ => Q) :=
    ae_iff.mpr hfull
  filter_upwards [ha] with θ hθ E hE hroot hrel
  exact hθ 0 (eval_linearRelationObstructionPullback_eq_zero F c _ E (root_coefficients P θ E hE hroot) hrel)

#print axioms ae_no_fixed_real_relation
end
end GaloisForLFunctions.HTGeometry.FirstGate
