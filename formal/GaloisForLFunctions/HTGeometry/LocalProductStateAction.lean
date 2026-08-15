import GaloisForLFunctions.HTGeometry.FinitePauliConjugationLaw

/-!
# Sitewise action on a product state

A matrix that factors over the qubits acts on a product state one qubit at a time: the
distributive law for a product of sums over a finite index turns the configuration sum defining
the matrix-vector product into a product of single-qubit matrix-vector products.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- A product state of the qubit configuration space. -/
def localProductState (w : σ → Bool → ℂ) : FiniteQubitConfiguration σ → ℂ :=
  fun x => ∏ s, w s (x s)

/-- **A local matrix acts sitewise on a product state.** -/
theorem finiteLocalMatrix_mulVec_localProductState (M : σ → Matrix Bool Bool ℂ)
    (w : σ → Bool → ℂ) :
    finiteLocalMatrix M *ᵥ localProductState w =
      localProductState fun s => (M s) *ᵥ (w s) := by
  classical
  funext x
  have hlhs : (finiteLocalMatrix M *ᵥ localProductState w) x =
      ∑ y : FiniteQubitConfiguration σ, ∏ s, (M s (x s) (y s) * w s (y s)) := by
    simp only [Matrix.mulVec, dotProduct, finiteLocalMatrix, localProductState]
    exact Finset.sum_congr rfl fun y _ => (Finset.prod_mul_distrib).symm
  have hsplit : (∏ s, ∑ b : Bool, M s (x s) b * w s b) =
      ∑ y ∈ Fintype.piFinset fun _ : σ => (Finset.univ : Finset Bool),
        ∏ s, (M s (x s) (y s) * w s (y s)) :=
    Finset.prod_univ_sum (fun _ : σ => (Finset.univ : Finset Bool))
      (fun s b => M s (x s) b * w s b)
  have hrhs : (∏ s, ((M s) *ᵥ (w s)) (x s)) = ∏ s, ∑ b : Bool, M s (x s) b * w s b := by
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [Matrix.mulVec, dotProduct]
  rw [hlhs, localProductState, hrhs, hsplit, Fintype.piFinset_univ]

/-- The squared length of a product state factors. -/
theorem sum_normSq_localProductState (w : σ → Bool → ℂ) :
    (∑ x : FiniteQubitConfiguration σ, ‖localProductState w x‖ ^ 2) =
      ∏ s, ∑ b : Bool, ‖w s b‖ ^ 2 := by
  classical
  have hsplit : (∏ s, ∑ b : Bool, ‖w s b‖ ^ 2) =
      ∑ y ∈ Fintype.piFinset fun _ : σ => (Finset.univ : Finset Bool),
        ∏ s, ‖w s (y s)‖ ^ 2 :=
    Finset.prod_univ_sum (fun _ : σ => (Finset.univ : Finset Bool))
      (fun s b => ‖w s b‖ ^ 2)
  rw [hsplit, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [localProductState, norm_prod, ← Finset.prod_pow]

end GaloisForLFunctions.HTGeometry
