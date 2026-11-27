import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.MultiplicityPairs

/-! # One integer polynomial for all nontrivial replica energy differences -/
open Finset MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] {q : ℕ}

private def factor (p : Pair I q) : MvPolynomial I ℤ :=
  linearRelationPoly (mode p)

def polynomial (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) : MvPolynomial I ℤ :=
  ∏ p : Pair I q, factor p

theorem symmetric (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :
    (polynomial I q).IsSymmetric := by
  classical
  intro s
  unfold polynomial
  rw [map_prod]
  apply Fintype.prod_equiv (relabel s)
  intro p
  simp only [factor,linearRelationPoly,map_sum,map_mul,rename_C,rename_X]
  exact Fintype.sum_equiv s _ _ fun i => by rw [mode_relabel]

/-- The value depends only on the elementary symmetric functions of the spectrum. -/
def coefficient (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) : MvPolynomial (Fin (Fintype.card I)) ℤ :=
  (MvPolynomial.esymmAlgEquiv I ℤ rfl).symm ⟨polynomial I q,symmetric I q⟩

theorem eval_coefficient (E : I→ℂ) (q : ℕ) :
    aeval (fun i : Fin (Fintype.card I) => aeval E (esymm I ℤ (i.val+1))) (coefficient I q)=
      ∏ p : Pair I q, (∑ j, (mode p j:ℂ)*E j) := by
  have he : (esymmAlgHom I ℤ (Fintype.card I) (coefficient I q)).val=polynomial I q :=
    congrArg Subtype.val ((esymmAlgEquiv I ℤ rfl).apply_symm_apply ⟨_,symmetric I q⟩)
  have h := congrArg (aeval E) he
  rw [esymmAlgHom_apply] at h
  have heC (z : ℤ) : (aeval E) (C z : MvPolynomial I ℤ)=(z:ℂ) := by simp
  simpa only [comp_aeval_apply,polynomial,factor,linearRelationPoly,map_prod,map_sum,map_mul,heC,aeval_X] using h

/-- Product of all unequal-multiplicity differences in the given spectrum. -/
def value (E : I→ℝ) (q : ℕ) := ∏ p : Pair I q, gap E p

theorem value_ne_zero {E : I→ℝ} (h : MaximallyProjectiveEnergy E) (q : ℕ) : value E q≠0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ => gap_ne_zero h p

theorem value_perm (s : Equiv.Perm I) (E : I→ℝ) (q : ℕ) : value (E ∘ s) q=value E q :=
  Fintype.prod_equiv (relabel s) _ _ fun p => gap_relabel s E p

theorem value_scale (c : ℝ) (E : I→ℝ) (q : ℕ) :
    value (fun i => c*E i) q=c^(Fintype.card (Pair I q))*value E q := by
  unfold value gap
  simp only [show ∀ a b : ℝ, a*(c*b)=c*(a*b) from fun a b => by ring,←Finset.mul_sum,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

#print axioms eval_coefficient
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
