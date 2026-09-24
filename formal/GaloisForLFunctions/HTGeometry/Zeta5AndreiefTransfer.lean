import Mathlib

/-!
# Andréief identity from the zeta-five determinant argument

`domino14/zeta5`, §6.10, uses the identity to convert an integrated Gram
determinant into an integral of two determinants. This version isolates the
real-valued identity for reuse by the corpus's moment and Hankel modules.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Finset Equiv

noncomputable section

private theorem permute_pi_preserving {n : ℕ} (μ : Measure ℝ) [SigmaFinite μ]
    (ρ : Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i => x (ρ i))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  have h := measurePreserving_arrowCongr' (fun _ : Fin n => μ) (fun _ => μ) ρ.symm
    (MeasurableEquiv.refl ℝ) (fun _ => MeasurePreserving.id μ)
  convert h using 1
  ext x i
  simp [MeasurableEquiv.arrowCongr', Equiv.arrowCongr']

/-- Andréief's determinant-integral identity for a finite real family. -/
theorem zeta5_andreief {n : ℕ} (μ : Measure ℝ) [SigmaFinite μ]
    (φ ψ : Fin n → ℝ → ℝ)
    (hint : ∀ i j, Integrable (fun x => φ i x * ψ j x) μ) :
    (Matrix.of fun i j => ∫ x, φ i x * ψ j x ∂μ).det =
      1 / n.factorial * ∫ x : Fin n → ℝ,
        (Matrix.of fun a b => φ a (x b)).det *
          (Matrix.of fun a b => ψ a (x b)).det
          ∂(Measure.pi fun _ => μ) := by
  let P : (Fin n → ℝ) → ℝ := fun x => (Matrix.of fun a b => φ a (x b)).det
  let I : (Fin n → ℝ) → ℝ := fun x => P x * ∏ i, ψ i (x i)
  have hIexpand : I = fun x => ∑ σ : Perm (Fin n),
      (Perm.sign σ : ℝ) * ∏ i, (φ (σ i) (x i) * ψ i (x i)) := by
    funext x
    simp only [I, P, Matrix.det_apply', Matrix.of_apply, Finset.sum_mul,
      Finset.prod_mul_distrib, mul_assoc]
  have hIint : Integrable I (Measure.pi fun _ => μ) := by
    rw [hIexpand]
    exact integrable_finsetSum _ fun σ _ =>
      (Integrable.fintype_prod (f := fun i t => φ (σ i) t * ψ i t)
        fun i => hint _ _).const_mul _
  have hdet : (Matrix.of fun i j => ∫ x, φ i x * ψ j x ∂μ).det =
      ∫ x, I x ∂(Measure.pi fun _ => μ) := by
    rw [hIexpand, integral_finsetSum _ fun σ _ =>
      (Integrable.fintype_prod (f := fun i t => φ (σ i) t * ψ i t)
        fun i => hint _ _).const_mul _, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_const_mul]
    congr 1
    rw [integral_fintype_prod_eq_prod (f := fun i t => φ (σ i) t * ψ i t)]
    rfl
  have hperm : ∀ ρ : Perm (Fin n), ∀ x : Fin n → ℝ,
      I (fun i => x (ρ i)) =
        (Perm.sign ρ : ℝ) * (P x * ∏ i, ψ i (x (ρ i))) := by
    intro ρ x
    simp only [I, P]
    have hmatrix : (Matrix.of fun a b => φ a (x (ρ b))) =
        (Matrix.of fun a b => φ a (x b)).submatrix id ρ := by
      ext a b; rfl
    rw [hmatrix, Matrix.det_permute']
    ring
  have hpreserve := permute_pi_preserving (n := n) μ
  calc
    (Matrix.of fun i j => ∫ x, φ i x * ψ j x ∂μ).det
        = 1 / n.factorial * ∑ _ρ : Perm (Fin n),
            ∫ x, I x ∂(Measure.pi fun _ => μ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul, hdet]
          field_simp
    _ = 1 / n.factorial * ∑ ρ : Perm (Fin n),
          ∫ x, I (fun i => x (ρ i)) ∂(Measure.pi fun _ => μ) := by
        congr 1
        refine Finset.sum_congr rfl fun ρ _ => ?_
        have h := (measurePreserving_arrowCongr' (fun _ : Fin n => μ)
          (fun _ => μ) ρ.symm (MeasurableEquiv.refl ℝ)
          (fun _ => MeasurePreserving.id μ)).integral_comp' I
        rw [← h]
        rfl
    _ = _ := by
        congr 1
        have hintperm : ∀ ρ : Perm (Fin n),
            Integrable (fun x : Fin n → ℝ => I (fun i => x (ρ i)))
              (Measure.pi fun _ => μ) := fun ρ =>
          (hpreserve ρ).integrable_comp_of_integrable hIint
        rw [← integral_finsetSum _ fun ρ _ => hintperm ρ]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hperm]
        show _ = P x * _
        rw [← Matrix.det_transpose (Matrix.of fun a b => ψ a (x b)),
          Matrix.det_apply' (Matrix.of fun a b => ψ a (x b)).transpose,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ _ => ?_
        simp only [Matrix.transpose_apply, Matrix.of_apply]
        ring

end

end GaloisForLFunctions.HTGeometry
