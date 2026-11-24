import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.BoundedFields.AffineGrid
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.BoundedFields.AffineCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.Witness

/-! # A bounded integer field witness for the physical spectral minor -/
open Matrix MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

private theorem affine_field_coe {n m : ℕ} (c : Fin m→ℝ) (V : Fin n→Fin m→ℝ) (b : Fin n→ℕ) :
    affinePoint (fun a => (c a:ℂ)) (fun i a => (V i a:ℂ)) (fun i => (b i:ℂ)+1) =
      fun a => (fieldPoint c V b a:ℂ) := by
  funext a
  simp only [affinePoint,fieldPoint,Complex.ofReal_add,Complex.ofReal_sum,
    Complex.ofReal_mul,Complex.ofReal_natCast,Nat.cast_add,Nat.cast_one]

/-- The positive onsite strengths can be chosen at most one more than the
detector degree. Only the N physical field coordinates are interpolated. -/
theorem bounded_product_detector_witness (n : ℕ) (j : Bool) :
    let L := 2*n+order j
    let D : ℕ := 2^(n+1)
    let d := D*(2*(1+2*L*D))
    ∃ (b : Fin (n+1)→ℕ) (k : Fin D) (v : Fin D→List (Fin (n+1))),
      (∀ s, b s≤d) ∧ (∀ i, ∃ u, Suffix n u ∧ v i=letters j u) ∧
      (∀ i, (v i).length≤L) ∧ ∃ θ : Coordinates (n+1)→ℝ,
      synthesis (chainPauliFin (n+1)) (fun a => (θ a:ℂ)) =
        reindex (qubitConfigFin (n+1)) (qubitConfigFin (n+1)) (background n b 0) ∧
      eval₂Hom GaussianInt.toComplex (fun a => (θ a:ℂ))
        (pathDetector (n+1) L (detectorRows k (fun i => (v i).map (fieldIndex n))))≠0 := by
  intro L D d
  obtain ⟨b₀,k,v,hv,hl,θ,hθ,hdet⟩ := product_detector_witness n j
  obtain ⟨c,V,he,hfields⟩ := affine_product_fields n b₀ θ hθ
  let rows := detectorRows k (fun i => (v i).map (fieldIndex n))
  let Q := pathDetector (n+1) L rows
  let f := map GaussianInt.toComplex Q
  have hd : f.totalDegree≤d := (show f.totalDegree≤Q.totalDegree from
    Finset.sup_mono (support_map_subset GaussianInt.toComplex Q)).trans (pathDetector_degree _ _ rows
      (detectorRows_bound k _ (fun i => by simpa only [List.length_map] using hl i)))
  have hval (b : Fin (n+1)→ℕ) :
      eval (affinePoint (fun a => (c a:ℂ)) (fun i a => (V i a:ℂ)) (fun s => (b s:ℂ)+1)) f =
      eval₂Hom GaussianInt.toComplex (fun a => (fieldPoint c V b a:ℂ)) Q := by
    rw [affine_field_coe]
    exact eval_map ..
  have hstart := hval b₀
  rw [he] at hstart
  obtain ⟨b,hb,hn⟩ := positive_grid_on_family f _ _ _ (hstart.trans_ne hdet) hd
  exact ⟨b,k,v,hb,hv,hl,fieldPoint c V b,hfields b,(hval b).symm.trans_ne hn⟩

#print axioms bounded_product_detector_witness
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
