/-
# Finite Gram matrices and the kernel energy form

A kernel all of whose finite Gram matrices are positive semidefinite is a positive semidefinite
kernel in the coefficient-vector sense, and conversely.  The passage is the enumeration of the
support of a finitely supported coefficient vector.
-/
import GaloisForLFunctions.HTGeometry.PosSemidefKernelGram

noncomputable section

open scoped ComplexOrder ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} {K : X → X → ℂ}

/-- **From finite Gram matrices to the kernel energy form.** -/
theorem isPSDKernel_of_forall_posSemidef (hherm : ∀ x y, conj (K x y) = K y x)
    (h : ∀ (n : ℕ) (w : Fin n → X), (Matrix.of fun j k => K (w j) (w k)).PosSemidef) :
    IsPSDKernel K := by
  classical
  refine ⟨hherm, fun c => ?_⟩
  set s : Finset X := c.support with hs
  set n : ℕ := s.card with hn
  set e : Fin n ≃ s := (s.equivFin).symm with he
  set w : Fin n → X := fun j => ((e j : s) : X) with hw
  have hmat : (Matrix.of fun j k => K (w k) (w j)).PosSemidef := (h n w).transpose
  have hquad := hmat.dotProduct_mulVec_nonneg (fun j => c (w j))
  have hval : star (fun j => c (w j)) ⬝ᵥ
      (Matrix.of fun j k => K (w k) (w j)).mulVec (fun j => c (w j))
      = ∑ j : Fin n, ∑ k : Fin n, conj (c (w j)) * c (w k) * K (w k) (w j) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hval] at hquad
  have hsum : (c.sum fun y a => c.sum fun x b => conj a * b * K x y)
      = ∑ j : Fin n, ∑ k : Fin n, conj (c (w j)) * c (w k) * K (w k) (w j) := by
    rw [Finsupp.sum, ← Finset.sum_coe_sort s
      (fun a => c.sum fun x b => conj (c a) * b * K x a),
      ← Equiv.sum_comp e (fun p : s => (c.sum fun x b => conj (c (p : X)) * b * K x (p : X)))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finsupp.sum, ← Finset.sum_coe_sort s
      (fun a => conj (c (w j)) * c a * K a (w j)),
      ← Equiv.sum_comp e (fun p : s => conj (c (w j)) * c ((p : X)) * K ((p : X)) (w j))]
  rw [hsum]
  have hre := Complex.le_def.mp hquad
  simpa using hre.1

end GaloisForLFunctions.HTGeometry
