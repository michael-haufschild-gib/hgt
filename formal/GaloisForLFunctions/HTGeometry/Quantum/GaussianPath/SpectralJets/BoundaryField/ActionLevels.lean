import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.DistinctLabels
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Elimination.LineRoots

/-! # Finite level sets for every labeling along a spectral pencil -/
open Matrix MvPolynomial Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
noncomputable section
variable {ι : Type*} [Fintype ι] {D : ℕ}

/-- The polynomial vanishes at a simple matrix exactly when a permutation
of its spectrum has weighted sum v. -/
def actionLevel (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ)) (c : Fin D→ℂ) (v : ℂ) :=
  eliminateLabels M ((∑ i, C (c i)*X (rootVariable D i))-C v)

theorem actionLevel_eq_zero_iff (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (x : ι→ℂ) (E c : Fin D→ℂ) (v : ℂ) (hi : Function.Injective E)
    (ht : ∀ k : ℕ, eval x (M^k).trace=∑ i, E i^k) :
    eval x (actionLevel M c v)=0 ↔ ∃ σ : Equiv.Perm (Fin D), (∑ i, c i*E (σ i))=v := by
  rw [actionLevel,eval_eliminateLabels_eq_zero_iff M x E hi ht]
  simp only [map_sub,map_sum,map_mul,eval_C,eval_X,assignRoots_root,Function.comp_apply,sub_eq_zero]

/-- Two simple settings with disjoint weighted spectra force every action
level to be attained at only finitely many real settings. Degenerate settings
are included in the exceptional finite set. -/
theorem finite_action_fibers (M : Matrix (Fin D) (Fin D) (MvPolynomial ι ℂ))
    (z : ι→Polynomial ℂ) (E : ℝ→Fin D→ℂ) (c : Fin D→ℂ)
    (ht : ∀ (t : ℝ) (k : ℕ), eval (fun i => (z i).eval (t:ℂ)) (M^k).trace=∑ i, E t i^k)
    {a b : ℝ} (ha : Function.Injective (E a)) (hb : Function.Injective (E b))
    (hsep : ∀ σ τ : Equiv.Perm (Fin D), (∑ i, c i*E a (σ i))≠∑ i, c i*E b (τ i)) (v : ℂ) :
    {t : ℝ | ¬Function.Injective (E t) ∨ ∃ σ : Equiv.Perm (Fin D), (∑ i, c i*E t (σ i))=v}.Finite := by
  classical
  let x (t : ℝ) (i : ι) := (z i).eval (t:ℂ)
  let P := linePolynomial z (actionLevel M c v)
  let Q := linePolynomial z (rootProduct M 1)
  have hP (t : ℝ) (h : Function.Injective (E t)) : P.eval (t:ℂ)=0 ↔
      ∃ σ : Equiv.Perm (Fin D), (∑ i, c i*E t (σ i))=v := by
    dsimp only [P]
    rw [eval_linePolynomial]
    exact actionLevel_eq_zero_iff M (x t) _ _ _ h (ht t)
  have hQ (t : ℝ) : Q.eval (t:ℂ)=(vandermonde (E t)).det^2 := by
    dsimp only [Q]
    rw [eval_linePolynomial]
    simpa only [map_one,Finset.prod_const_one,mul_one] using eval_rootProduct M (x t) (E t) (ht t) 1
  have hp : P≠0 := by
    intro he
    obtain ⟨σ,hσ⟩ := (hP a ha).mp (by rw [he,Polynomial.eval_zero])
    obtain ⟨τ,hτ⟩ := (hP b hb).mp (by rw [he,Polynomial.eval_zero])
    exact hsep σ τ (hσ.trans hτ.symm)
  have hq : Q≠0 := by
    intro he
    have hh := hQ a
    rw [he,Polynomial.eval_zero] at hh
    exact pow_ne_zero 2 (det_vandermonde_ne_zero_iff.mpr ha) hh.symm
  apply ((lineCuts Q ∪ lineCuts P).finite_toSet).subset
  intro t ht'
  by_cases hi : Function.Injective (E t)
  · exact Finset.mem_union_right _ (mem_lineCuts hp ((hP t hi).mpr (ht'.resolve_left (fun h => h hi))))
  · apply Finset.mem_union_left _ (mem_lineCuts hq ?_)
    have hd : (vandermonde (E t)).det=0 := by
      by_contra hn
      exact hi (det_vandermonde_ne_zero_iff.mp hn)
    rw [hQ,hd,zero_pow (by decide)]

#print axioms finite_action_fibers
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField
