import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.PhysicalMinor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.BranchRescaling

/-! # Roots of the normalized polynomial are physical field branches -/
open Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- The holomorphic extension in the independent onsite Z fields. -/
def fieldHamiltonian (n : ℕ) (v : ℝ) (h : Fin (n+2) → ℂ) :=
  pathHamiltonian (splitShell n v) + diagonal (fun j => fieldEnergy (spinVector j) h)

theorem fieldHamiltonian_real (n : ℕ) (v : ℝ) (h : Fin (n+2) → ℝ) :
    fieldHamiltonian n v (fun i => (h i:ℂ)) = pathHamiltonian (splitShell n v+longitudinalShell h) := by
  change _ = pathHamiltonianLM n (_+_)
  rw [map_add]
  exact congrArg (pathHamiltonian (splitShell n v)+·) (longitudinal_matrix h).symm

private theorem field_reflection (n : ℕ) (v : ℝ) (x r : ℂ) (h : Fin (n+2) → ℂ) :
    let H := pathHamiltonian (splitShell n v)
    let g := fun j => -fieldEnergy (spinVector j) h
    (scalar _ x-H+(-r) • diagonal g).det=(scalar _ x-H+r • diagonal g).det := by
  intro H g
  let e := reversal (n+2)
  have hg (j) : g (reverseSpins j)= -g j := by
    simp [g,spinVector_rev,fieldEnergy,Finset.sum_neg_distrib]
  have he : Matrix.reindex e e (scalar _ x-H+r • diagonal g)=scalar _ x-H+(-r) • diagonal g := by
    ext i j
    change (scalar _ x-H+r • diagonal g) (reverseSpins i) (reverseSpins j)=_
    have hij : reverseSpins i=reverseSpins j ↔ i=j := e.injective.eq_iff
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.scalar_apply,
      Matrix.diagonal_apply,hij,smul_eq_mul,H,reversed_split,hg]
    split_ifs <;> ring
  rw [←he,Matrix.det_reindex_self]

theorem eval_physicalPolynomial {n : ℕ} (v : ℝ) (E : (Fin (n+2) → Bool) → ℂ)
    (hE : (pathHamiltonian (splitShell n v)).charpoly = ∏ j, Polynomial.X-Polynomial.C (E j))
    (s : Fin (n+1) → Bool) (h : Fin (n+2) → ℂ) (z : ℂ) :
    let j := representative s
    let t := reverseSpins j
    let b := (E j+E t)/2
    let r := (E j-E t)/2
    r^2 * MvPolynomial.eval (fun o : Option (Fin (n+2)) => o.elim z h) (physicalPolynomial v E s) =
      2*matrixCharpolyRelation (fieldHamiltonian n v (r • h),b+r*z) := by
  intro j t b r
  let H := pathHamiltonian (splitShell n v)
  let g (i) := -fieldEnergy (spinVector i) h
  have hchar : (scalar _ (b+r*z)-H).det=∏ i, b+r*z-E i := by
    rw [←Matrix.eval_charpoly,hE,Polynomial.eval_prod]
    simp
  have he : MvPolynomial.eval (fun o : Option (Fin (n+2)) => o.elim z h) (physicalPolynomial v E s) =
      rescaledDet H E g j t b r z := by
    simp only [physicalPolynomial,pairPolynomial,map_rescaledDet,MvPolynomial.eval_C,MvPolynomial.eval_X,
      map_neg,eval_fieldPoly,Option.elim_some,Option.elim_none,Matrix.map_map,Function.comp_def]
    rfl
  rw [he,rescaled_identity _ _ _ _ _ (reversed_ne j) _ _ _ (by dsimp [b,r]; ring)
    (by dsimp [b,r]; ring) hchar (field_reflection n v _ _ h)]
  apply congrArg (fun A => 2*A.det)
  ext i k
  by_cases hik : i=k
  · subst k
    simp only [fieldHamiltonian,Matrix.add_apply,Matrix.sub_apply,Matrix.diagonal_apply_eq,
      Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,g,H,fieldEnergy]
    simp_rw [mul_left_comm _ r]
    rw [←Finset.mul_sum]
    ring
  · simp [fieldHamiltonian,Matrix.smul_apply,Matrix.diagonal_apply_ne _ hik,H]

end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
