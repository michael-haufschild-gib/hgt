import GaloisForLFunctions.HTGeometry.ProductCliffordLabelAction
import GaloisForLFunctions.HTGeometry.GaussianSignedPermutationInvariance
import GaloisForLFunctions.HTGeometry.CollisionEnsembleLaw

/-!
# Product-Clifford covariance of a weighted Pauli ensemble

A Pauli ensemble whose weights depend only on the support of the label is carried by conjugation
with a product Clifford onto the same ensemble with signed and permuted coefficients: the
relabelling preserves supports, hence weights, and the conjugation phases are signs.  The centred
product Gaussian coefficient law is invariant under that signed permutation, so the whole ensemble
law is invariant under product-Clifford conjugation.
-/

open Matrix MeasureTheory

open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The real sign of the conjugation phase. -/
def productCliffordSign (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) : ℝ :=
  if productCliffordPhase g P = 1 then 1 else -1

theorem productCliffordSign_eq_one_or_neg_one (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) :
    productCliffordSign g P = 1 ∨ productCliffordSign g P = -1 := by
  rw [productCliffordSign]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ofReal_productCliffordSign (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) :
    ((productCliffordSign g P : ℝ) : ℂ) = productCliffordPhase g P := by
  rw [productCliffordSign]
  split
  · rename_i h
    rw [h]
    norm_num
  · rename_i h
    rcases productCliffordPhase_eq_one_or_neg_one g P with h1 | h1
    · exact absurd h1 h
    · rw [h1]
      norm_num

/-- Weights that depend only on the support of a Pauli label. -/
def SupportInvariantWeight (w : (σ → Option (Fin 3)) → ℝ) : Prop :=
  ∀ P Q : σ → Option (Fin 3), (∀ s, P s = none ↔ Q s = none) → w P = w Q

theorem supportInvariantWeight_relabel {w : (σ → Option (Fin 3)) → ℝ}
    (hw : SupportInvariantWeight w) (g : σ → QubitTwoDesign.BinaryOctahedral)
    (P : σ → Option (Fin 3)) : w (productCliffordRelabel g P) = w P :=
  hw _ _ fun s => productCliffordRelabel_none_iff g P s

/-- The weighted Pauli ensemble Hamiltonian at one coefficient vector. -/
def pauliEnsemble (w J : (σ → Option (Fin 3)) → ℝ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  ∑ P, ((w P * J P : ℝ) : ℂ) • finitePauliMatrix P

/-- The signed permutation of coefficients induced by a product Clifford. -/
def cliffordCoefficientMap (g : σ → QubitTwoDesign.BinaryOctahedral)
    (J : (σ → Option (Fin 3)) → ℝ) : (σ → Option (Fin 3)) → ℝ :=
  fun Q => productCliffordSign g ((productCliffordRelabelEquiv g).symm Q) *
    J ((productCliffordRelabelEquiv g).symm Q)

/-- **Conjugation covariance of the weighted Pauli ensemble.**  Conjugating by a product Clifford
is the same as applying the induced signed permutation to the coefficients. -/
theorem pauliEnsemble_conj (w : (σ → Option (Fin 3)) → ℝ) (hw : SupportInvariantWeight w)
    (g : σ → QubitTwoDesign.BinaryOctahedral) (J : (σ → Option (Fin 3)) → ℝ) :
    finiteProductCliffordGate g * pauliEnsemble w J * (finiteProductCliffordGate g)ᴴ =
      pauliEnsemble w (cliffordCoefficientMap g J) := by
  classical
  rw [pauliEnsemble, Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ P : σ → Option (Fin 3),
      finiteProductCliffordGate g * (((w P * J P : ℝ) : ℂ) • finitePauliMatrix P) *
          (finiteProductCliffordGate g)ᴴ =
        ((w (productCliffordRelabel g P) *
            cliffordCoefficientMap g J (productCliffordRelabel g P) : ℝ) : ℂ) •
          finitePauliMatrix (productCliffordRelabel g P) := by
    intro P
    rw [Matrix.mul_smul, Matrix.smul_mul,
      finiteProductCliffordGate_conj_finitePauliMatrix_relabel g P, smul_smul,
      supportInvariantWeight_relabel hw g P]
    congr 1
    rw [cliffordCoefficientMap]
    have hsymm : (productCliffordRelabelEquiv g).symm (productCliffordRelabel g P) = P := by
      have : (productCliffordRelabelEquiv g) P = productCliffordRelabel g P := rfl
      rw [← this, Equiv.symm_apply_apply]
    rw [hsymm, ← ofReal_productCliffordSign g P]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun P (_ : P ∈ Finset.univ) => hterm P, pauliEnsemble]
  exact Fintype.sum_equiv (productCliffordRelabelEquiv g) _ _ fun P => rfl

/-- **The signed permutation preserves the centred product Gaussian coefficient law.** -/
theorem measurePreserving_cliffordCoefficientMap
    (g : σ → QubitTwoDesign.BinaryOctahedral) (v : NNReal) :
    MeasurePreserving (cliffordCoefficientMap g)
      (centredProductGaussian (σ → Option (Fin 3)) v)
      (centredProductGaussian (σ → Option (Fin 3)) v) := by
  have h := measurePreserving_signedPerm (productCliffordRelabelEquiv g).symm
    (ε := fun Q => productCliffordSign g ((productCliffordRelabelEquiv g).symm Q))
    (fun Q => productCliffordSign_eq_one_or_neg_one g _) v
  exact h

theorem measurable_pauliEnsemble_entry (w : (σ → Option (Fin 3)) → ℝ)
    (x y : FiniteQubitConfiguration σ) :
    Measurable fun J : (σ → Option (Fin 3)) → ℝ => pauliEnsemble w J x y := by
  classical
  have hrw : ∀ J : (σ → Option (Fin 3)) → ℝ, pauliEnsemble w J x y =
      ∑ P, ((w P * J P : ℝ) : ℂ) * finitePauliMatrix P x y := by
    intro J
    rw [pauliEnsemble]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [hrw]
  refine Finset.measurable_sum _ fun P _ => Measurable.mul ?_ measurable_const
  exact Complex.measurable_ofReal.comp (measurable_const.mul (measurable_pi_apply P))

/-- **Product-Clifford invariance of the mean collision.**  The mean spectral collision of the
weighted Pauli Gaussian ensemble at a state equals its mean collision at any product-Clifford
rotation of that state. -/
theorem integral_spectralCollision_pauliEnsemble_clifford_eq
    (w : (σ → Option (Fin 3)) → ℝ) (hw : SupportInvariantWeight w) (v : NNReal)
    (g : σ → QubitTwoDesign.BinaryOctahedral)
    (ψ : FiniteQubitConfiguration σ → ℂ)
    {e : ((σ → Option (Fin 3)) → ℝ) →
      FiniteQubitConfiguration σ → FiniteQubitConfiguration σ → ℂ}
    {lam : ((σ → Option (Fin 3)) → ℝ) → FiniteQubitConfiguration σ → ℝ}
    (hae : ∀ᵐ J ∂(centredProductGaussian (σ → Option (Fin 3)) v),
      IsOrthoEigenBasis (pauliEnsemble w J) (e J) (lam J) ∧ Function.Injective (lam J)) :
    (∫ J, spectralCollision (e J) ((finiteProductCliffordGate g)ᴴ *ᵥ ψ)
        ∂(centredProductGaussian (σ → Option (Fin 3)) v)) =
      ∫ J, spectralCollision (e J) ψ ∂(centredProductGaussian (σ → Option (Fin 3)) v) := by
  refine integral_spectralCollision_conj_eq (Hf := fun J => pauliEnsemble w J)
    (fun x y => measurable_pauliEnsemble_entry w x y) ψ hae
    (U := (finiteProductCliffordGate g)ᴴ) ?_ ?_
    (T := cliffordCoefficientMap g) (measurePreserving_cliffordCoefficientMap g v) ?_
  · rw [Matrix.conjTranspose_conjTranspose]
    exact finiteProductCliffordGate_mul_conjTranspose g
  · rw [Matrix.conjTranspose_conjTranspose]
    exact finiteProductCliffordGate_unitary g
  · refine Filter.Eventually.of_forall fun J => ?_
    rw [Matrix.conjTranspose_conjTranspose, pauliEnsemble_conj w hw g J]

end GaloisForLFunctions.HTGeometry
