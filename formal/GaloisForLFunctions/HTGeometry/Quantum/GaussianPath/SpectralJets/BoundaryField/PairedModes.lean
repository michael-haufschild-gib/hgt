import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.DistinctLabels

/-! # Testing a weighted relation between two spectra on the same parameter space -/
open Matrix MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
variable {ι : Type*} [Fintype ι] {D : ℕ}

/-- The first set of labels survives in the coefficient variables during
elimination of the second spectrum. Each packet can be permuted independently. -/
def pairedModeTest (M N : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ)) (c d : Fin D→ℂ) :
    MvPolynomial ι ℂ :=
  let q : MvPolynomial (RootVariables (RootVariables ι D) D) ℂ :=
    (∑ j, C (c j)*X (baseVariable D (rootVariable D j))) -
      ∑ j, C (d j)*X (rootVariable D j)
  eliminateLabels M (eliminateLabels (extendPencil N D) q)

theorem pairedModeTest_eq_zero_iff (M N : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι→ℂ) (E F c d : Fin D→ℂ) (hE : Function.Injective E) (hF : Function.Injective F)
    (hM : ∀ k : ℕ, eval x (M^k).trace=∑ j, E j^k)
    (hN : ∀ k : ℕ, eval x (N^k).trace=∑ j, F j^k) :
    eval x (pairedModeTest M N c d)=0 ↔ ∃ σ τ : Equiv.Perm (Fin D),
      (∑ j, c j*E (σ j))=∑ j, d j*F (τ j) := by
  rw [pairedModeTest,eval_eliminateLabels_eq_zero_iff M x E hE hM]
  apply exists_congr
  intro σ
  rw [eval_eliminateLabels_eq_zero_iff (extendPencil N D) (assignRoots x D (E ∘ σ)) F hF
    (fun k => (extend_trace N x D (E ∘ σ) k).trans (hN k))]
  apply exists_congr
  intro τ
  simp only [map_sub,map_sum,map_mul,eval_C,eval_X,assignRoots_base,assignRoots_root,
    Function.comp_apply,sub_eq_zero]

/-- A nonzero value certifies simplicity of both spectra and separation of
all pairs of labelings. -/
def separationTest (M N : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ)) (c d : Fin D→ℂ) :=
  rootProduct M 1 * rootProduct N 1 * pairedModeTest M N c d

theorem separationTest_ne_zero_iff (M N : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι→ℂ) (E F c d : Fin D→ℂ)
    (hM : ∀ k : ℕ, eval x (M^k).trace=∑ j, E j^k)
    (hN : ∀ k : ℕ, eval x (N^k).trace=∑ j, F j^k) :
    eval x (separationTest M N c d)≠0 ↔ Function.Injective E ∧ Function.Injective F ∧
      ∀ σ τ : Equiv.Perm (Fin D), (∑ j, c j*E (σ j))≠∑ j, d j*F (τ j) := by
  have simple (A : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ)) (f : Fin D→ℂ)
      (ht : ∀ k : ℕ, eval x (A^k).trace=∑ j, f j^k) :
      eval x (rootProduct A 1)≠0 ↔ Function.Injective f := by
    rw [eval_rootProduct A x f ht]
    simp only [map_one,Finset.prod_const_one,mul_one]
    rw [←Matrix.det_vandermonde_ne_zero_iff]
    constructor
    · exact fun h => fun he => h (by rw [he]; norm_num)
    · exact pow_ne_zero 2
  rw [separationTest,map_mul,map_mul,mul_ne_zero_iff,mul_ne_zero_iff,simple M E hM,simple N F hN]
  constructor
  · rintro ⟨⟨he,hf⟩,h⟩
    exact ⟨he,hf,fun σ τ hs => h ((pairedModeTest_eq_zero_iff M N x E F c d he hf hM hN).mpr ⟨σ,τ,hs⟩)⟩
  · rintro ⟨he,hf,h⟩
    refine ⟨⟨he,hf⟩,?_⟩
    intro hz
    obtain ⟨σ,τ,hs⟩ := (pairedModeTest_eq_zero_iff M N x E F c d he hf hM hN).mp hz
    exact h σ τ hs

#print axioms separationTest_ne_zero_iff
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
