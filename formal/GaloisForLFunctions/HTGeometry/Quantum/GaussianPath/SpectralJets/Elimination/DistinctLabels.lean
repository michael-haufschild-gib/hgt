import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.RootVariables

/-! # Polynomial elimination over complete labelings of a simple spectrum -/
open MvPolynomial Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι : Type*} [Fintype ι] {D : ℕ}

private def labelDiscriminant (ι : Type*) (D : ℕ) : MvPolynomial (RootVariables ι D) ℂ :=
  (Matrix.vandermonde (fun i : Fin D => X (rootVariable (ι := ι) D i))).det^2

omit [Fintype ι] in
private theorem eval_labelDiscriminant (x : ι→ℂ) (v : Fin D→ℂ) :
    eval (assignRoots x D v) (labelDiscriminant ι D)=(Matrix.vandermonde v).det^2 := by
  rw [labelDiscriminant,map_pow,RingHom.map_det]
  congr 2
  ext i j
  simp [Matrix.vandermonde_apply]

/-- A repeated assignment has zero Vandermonde, whereas each bijective
assignment has the spectral discriminant. The two terms make repeated
assignments invisible to the vanishing test. -/
def eliminateLabels (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (q : MvPolynomial (RootVariables ι D) ℂ) : MvPolynomial ι ℂ :=
  let d := labelDiscriminant ι D
  eliminateRoots M D (rename (baseVariable D) (rootProduct M 1)-d+d*q)

theorem eval_eliminateLabels_eq_zero_iff (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι→ℂ) (E : Fin D→ℂ) (hi : Function.Injective E)
    (ht : ∀ k : ℕ, eval x (M^k).trace=∑ j, E j^k) (q : MvPolynomial (RootVariables ι D) ℂ) :
    eval x (eliminateLabels M q)=0 ↔
      ∃ σ : Equiv.Perm (Fin D), eval (assignRoots x D (E ∘ σ)) q=0 := by
  classical
  have hdet (F : Fin D→ℂ) (hF : ∀ k : ℕ, eval x (M^k).trace=∑ j, F j^k) :
      eval x (rootProduct M 1)=(Matrix.vandermonde F).det^2 := by
    simpa using eval_rootProduct M x F hF 1
  have hd : eval x (rootProduct M 1)≠0 := hdet E ht ▸ pow_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.mpr hi)
  have hbase (s : Fin D→Fin D) :
      eval (assignRoots x D (E ∘ s)) (rename (baseVariable D) (rootProduct M 1))=eval x (rootProduct M 1) := by
    rw [eval_rename]
    exact congrArg (fun z => eval z (rootProduct M 1)) (funext fun j => assignRoots_base x D _ j)
  have hperm (σ : Equiv.Perm (Fin D)) :
      (Matrix.vandermonde (E ∘ σ)).det^2=eval x (rootProduct M 1) := by
    apply (hdet _ ?_).symm
    intro k
    exact (ht k).trans (Equiv.sum_comp σ (fun j => E j^k)).symm
  rw [eliminateLabels,eval_eliminateRoots_eq_zero_iff M x E hi ht]
  constructor
  · rintro ⟨s,hs⟩
    change eval (assignRoots x D (E ∘ s)) _=0 at hs
    rw [map_add,map_sub,map_mul,hbase,eval_labelDiscriminant] at hs
    by_cases hin : Function.Injective s
    · let σ := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hin)
      change eval x (rootProduct M 1)-(Matrix.vandermonde (E ∘ σ)).det^2+
        (Matrix.vandermonde (E ∘ σ)).det^2*eval (assignRoots x D (E ∘ σ)) q=0 at hs
      rw [hperm,sub_self,zero_add] at hs
      exact ⟨σ,(mul_eq_zero.mp hs).resolve_left hd⟩
    · have hv : (Matrix.vandermonde (E ∘ s)).det=0 := by
        by_contra h
        exact hin (Function.Injective.of_comp (Matrix.det_vandermonde_ne_zero_iff.mp h))
      rw [hv,zero_pow (by decide),sub_zero,zero_mul,add_zero] at hs
      exact (hd hs).elim
  · rintro ⟨σ,hσ⟩
    refine ⟨σ,?_⟩
    change eval (assignRoots x D (E ∘ σ)) _=0
    rw [map_add,map_sub,map_mul,hbase,eval_labelDiscriminant,hperm,hσ,mul_zero,sub_self,zero_add]

#print axioms eval_eliminateLabels_eq_zero_iff
end
end GaloisForLFunctions.HTGeometry.SpectralJets
