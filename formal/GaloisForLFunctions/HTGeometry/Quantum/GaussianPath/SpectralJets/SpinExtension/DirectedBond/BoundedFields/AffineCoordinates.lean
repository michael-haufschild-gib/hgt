import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.BoundedFields.SiteCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.NumberedSlice

/-! # An affine coefficient map through a prescribed product witness -/
open Matrix
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

def fieldPoint {n m : ℕ} (c : Fin m→ℝ) (V : Fin n→Fin m→ℝ) (B : Fin n→ℕ) (a : Fin m) :=
  c a+∑ i, V i a*((B i+1:ℕ):ℝ)

private theorem synth_fieldPoint {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : Fin m→E) (c : Fin m→ℝ) (V : Fin n→Fin m→ℝ) (B : Fin n→ℕ) :
    synthesis P (fun a => (fieldPoint c V B a:ℂ)) =
      synthesis P (fun a => (c a:ℂ))+∑ i, height (B i) • synthesis P (fun a => (V i a:ℂ)) := by
  have he : (fun a => (fieldPoint c V B a:ℂ)) =
      (fun a => (c a:ℂ))+∑ i, height (B i) • (fun a => (V i a:ℂ)) := by
    funext a
    simp only [fieldPoint,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,height,
      Complex.ofReal_add,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast,Nat.cast_add,Nat.cast_one]
    simp only [mul_comm]
  rw [he,map_add,map_sum]
  simp only [map_smul]

private theorem numbered_product (n : ℕ) (B : Fin (n+1)→ℕ) :
    reindex (qubitConfigFin (n+1)) (qubitConfigFin (n+1)) (background n B 0) =
      ∑ i, height (B i) • reindex (qubitConfigFin (n+1)) (qubitConfigFin (n+1)) (siteTerm n i) := by
  rw [product_site_sum]
  ext i j
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.sum_apply,Matrix.smul_apply,
    Complex.real_smul,height,Nat.cast_add,Nat.cast_one,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]

/-- Each onsite axis has a real physical lift. The constant correction lies
in the synthesis kernel and ensures the affine map passes through the given
coefficient vector itself. -/
theorem affine_product_fields (n : ℕ) (B₀ : Fin (n+1)→ℕ) (θ : Coordinates (n+1)→ℝ)
    (h₀ : synthesis (chainPauliFin (n+1)) (fun a => (θ a:ℂ)) =
      reindex (qubitConfigFin (n+1)) (qubitConfigFin (n+1)) (background n B₀ 0)) :
    ∃ (c : Coordinates (n+1)→ℝ) (V : Fin (n+1) → Coordinates (n+1)→ℝ),
      fieldPoint c V B₀=θ ∧ ∀ B, synthesis (chainPauliFin (n+1)) (fun a => (fieldPoint c V B a:ℂ)) =
        reindex (qubitConfigFin (n+1)) (qubitConfigFin (n+1)) (background n B 0) := by
  let q := qubitConfigFin (n+1)
  let P := chainPauliFin (n+1)
  have hl (i : Fin (n+1)) : ∃ v : Coordinates (n+1)→ℝ,
      synthesis P (fun a => (v a:ℂ))=reindex q q (siteTerm n i) := by
    obtain ⟨v,hv⟩ := mem_range_spectralEnsembleMatrix_of_mem_span
      (reindexFin_mem_span_range_chainPauliFin (siteTerm_mem n i))
    exact ⟨v,by rw [synthesis_apply]; exact hv⟩
  choose V hv using hl
  let c (a) := θ a-∑ i, V i a*((B₀ i+1:ℕ):ℝ)
  have he : fieldPoint c V B₀=θ := by funext a; simp only [fieldPoint,c,sub_add_cancel]
  have hc : synthesis P (fun a => (c a:ℂ))=0 := by
    have hb := synth_fieldPoint P c V B₀
    rw [he,h₀,numbered_product] at hb
    simp only [hv] at hb
    exact (add_left_eq_self.mp hb.symm)
  refine ⟨c,V,he,fun B => ?_⟩
  rw [synth_fieldPoint,hc,zero_add,numbered_product]
  simp only [hv]

#print axioms affine_product_fields
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
