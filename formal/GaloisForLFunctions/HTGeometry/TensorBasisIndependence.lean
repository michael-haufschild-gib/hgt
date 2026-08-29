import GaloisForLFunctions.HTGeometry.SigmaConstantsDisjointness

/-!
# Linear independence of a constants basis over the Picard–Vessiot ring

A `C`-basis of the constants subalgebra of the tensor square stays linearly independent over the
Picard–Vessiot ring itself.  The mechanism is the corpus's `basisIndependentOver_of_constants`:
a `σ`-simple ring forces the coefficients of a vanishing combination of constants to be constants,
hence — when the ring has no new constants — to come from the base field, where the basis is
independent by construction.

* `linearIndependent_of_basisIndependentOver`;
* `linearIndependent_constants_basis`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- `BasisIndependentOver` is linear independence. -/
theorem linearIndependent_of_basisIndependentOver {ι : Type*} (b : ι → A)
    (h : BasisIndependentOver R b) : LinearIndependent R b := by
  rw [linearIndependent_iff']
  intro s g hs i hi
  refine h s g ?_ i hi
  rw [← hs]
  exact Finset.sum_congr rfl fun j _ => (Algebra.smul_def (g j) (b j)).symm

variable {C : Type*} [Field C] [Algebra C R] [Algebra C A] [IsScalarTower C R A]

/-- **A basis of a subalgebra of constants is independent over the base ring.** -/
theorem linearIndependent_constants_basis [Nontrivial R]
    (σR : R ≃+* R) (σA : A ≃+* A)
    (hcompat : ∀ r : R, σA (algebraMap R A r) = algebraMap R A (σR r))
    (hsimple : IsSigmaSimple σR)
    (E : Subalgebra C A) (hEconst : ∀ e : E, σA (e : A) = (e : A))
    (hnonew : ∀ r : R, σR r = r → ∃ c : C, r = algebraMap C R c)
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι C E) :
    LinearIndependent R (fun i => ((b i : E) : A)) := by
  classical
  refine linearIndependent_of_basisIndependentOver _ ?_
  refine basisIndependentOver_of_constants σR σA hcompat hsimple
    (fun i => ((b i : E) : A)) (fun j => hEconst (b j)) ?_
  intro t d hconst hsum j hj
  choose! c hc using fun (k : ι) (hk : k ∈ t) => hnonew (d k) (hconst k hk)
  have hEsum : E.val (∑ k ∈ t, c k • b k) = 0 := by
    rw [map_sum, ← hsum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [map_smul, Algebra.smul_def, hc k hk, ← IsScalarTower.algebraMap_apply C R A]
    rfl
  have hzero : (∑ k ∈ t, c k • b k) = (0 : E) := Subtype.ext hEsum
  have hbi := b.linearIndependent
  rw [linearIndependent_iff'] at hbi
  rw [hc j hj, hbi t c hzero j hj, map_zero]

end

end GaloisForLFunctions.HTGeometry
