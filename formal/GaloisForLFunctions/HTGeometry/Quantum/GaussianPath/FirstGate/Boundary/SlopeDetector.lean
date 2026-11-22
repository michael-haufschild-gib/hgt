import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.TraceRatios
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.Branches
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.FieldBranchRows
import GaloisForLFunctions.HTGeometry.RootPacketPowerSum

/-! # A polynomial certificate for distinction by a fixed diagonal field -/
open Matrix MvPolynomial Filter Topology
open GaloisForLFunctions.HTGeometry.SpectralJets
open GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
variable {D m : ℕ} {R : Type*} [CommRing R]

private def slopeDen (M : Matrix (Fin D) (Fin D) (MvPolynomial (Fin m) R)) (u : Fin D→R) :=
  atZeroField ((pderiv none (fieldCharacteristic M (fun j (_ : Fin 1) => C (u j))))^2)

/-- Homogenize the powers of the field slope with its squared spectral separant. -/
def slopeDetector (M : Matrix (Fin D) (Fin D) (MvPolynomial (Fin m) R)) (u : Fin D→R) :=
  ratioTrace M (fieldRow M (fun j (_ : Fin 1) => u j) 1 [0]) (slopeDen M u)

private theorem eval_slopeDen (M : Matrix (Fin D) (Fin D) (MvPolynomial (Fin m) R)) (u : Fin D→R)
    (φ : R →+* ℂ) (x : Fin m→ℂ) (y : ℂ) :
    eval₂ φ (fun o : Option (Fin m) => o.elim y x) (slopeDen M u) =
      (eval (fun o : Option (Fin 1) => o.elim y 0)
        (pderiv none (fieldCharacteristic ((eval₂Hom φ x).mapMatrix M) (fun j (_ : Fin 1) => φ (u j)))))^2 := by
  rw [slopeDen,eval_atZeroField,map_pow,←pderiv_map,map_fieldCharacteristic]
  simp only [eval_pow,Function.comp_def,eval₂Hom_C]
  rfl

/-- On any simple root labeling the polynomial is nonzero exactly when every
pair of slopes is different. No ordering of the roots appears in the detector. -/
theorem slopeDetector_iff (M : Matrix (Fin D) (Fin D) (MvPolynomial (Fin m) R)) (u : Fin D→R)
    (φ : R →+* ℂ) (x : Fin m→ℂ) (f : Fin D→ℂ→ℂ)
    (hf : ∀ j, AnalyticAt ℂ (f j) 0 ∧ ∀ᶠ s in 𝓝 0,
      matrixCharpolyRelation ((eval₂Hom φ x).mapMatrix M+s • diagonal (fun i => φ (u i)),f j s)=0)
    (hi : Function.Injective (fun j => f j 0)) :
    eval₂Hom φ x (slopeDetector M u)≠0 ↔ Function.Injective (fun j => deriv (f j) 0) := by
  let H := (eval₂Hom φ x).mapMatrix M
  let U (j : Fin D) (_ : Fin 1) := φ (u j)
  let E (j : Fin D) := f j 0
  let p := fieldCharacteristic H U
  let χ (j : Fin D) (o : Option (Fin 1)) := o.elim (E j) 0
  have hz (j) : matrixCharpolyRelation (H,E j)=0 := by
    simpa only [zero_smul,add_zero,E,H] using (hf j).2.self_of_nhds
  have hs := separable_of_branches H (diagonal (fun i => φ (u i))) f (fun j => (hf j).2) hi
  have hd (j) : eval (χ j) (pderiv none p) ≠ 0 := by
    apply field_separant H U hs
    simpa only [Matrix.eval_charpoly,matrixCharpolyRelation] using hz j
  have ht (k : ℕ) : eval₂Hom φ x (M^k).trace = ∑ j, E j^k := by
    rw [←trace_mapMatrix,map_pow]
    exact (sum_pow_rootPacket_eq_trace_pow_fin H E hi hz k).symm
  unfold slopeDetector
  apply ratioTrace_distinguishes _ _ _ _ _ E _ hi ht
  · intro j
    rw [eval_slopeDen]
    exact pow_ne_zero _ (hd j)
  · intro j
    let G (y : Fin 1→ℂ) := f j (y 0)
    have hG : AnalyticAt ℂ G 0 := (hf j).1.comp (f := fun y : Fin 1→ℂ => y 0) (x := 0)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _)
    have hroot : ∀ᶠ y in 𝓝 (0 : Fin 1→ℂ),
        matrixCharpolyRelation (H+diagonal (fun i => fieldEnergy (U i) y),G y)=0 := by
      have hlim : Tendsto (fun y : Fin 1→ℂ => y 0) (𝓝 0) (𝓝 0) := (continuous_apply 0).continuousAt.tendsto
      filter_upwards [hlim.eventually (hf j).2] with y hy
      have heq : diagonal (fun i => fieldEnergy (U i) y) = y 0 • diagonal (fun i => φ (u i)) := by
        ext a b
        by_cases hab : a=b <;> simp [hab,U,fieldEnergy,mul_comm]
      rwa [heq]
    have hmix : mixed [0] G 0=deriv (f j) 0 := by simp [mixed,G,coordLine]
    have hrow := field_row_of_branch H U hs G hG hroot [0]
    rw [eval_fieldRow,eval_slopeDen]
    simpa only [List.length_cons,List.length_nil,zero_add,mul_one,hmix,G,Pi.zero_apply,U,E,H,RingHom.mapMatrix_apply,Function.comp_def] using! hrow

#print axioms slopeDetector_iff
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
