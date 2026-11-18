import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# The integral obstruction in the simplex facet frame

In the normalized Fano triangle of Choi and Jang, Lemma 2.1, the three
side points are the sums of pairs of coordinate vectors. In dimension
`n+1` the analogous columns sum all but one basis vector. Their cokernel
is cyclic of order `n` over the integers, with the same presentation over
every commutative coefficient ring.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset LinearMap
noncomputable section

variable (R : Type*) [CommRing R] (n : ℕ)

/-- Evaluation of the incidence matrix with zero diagonal and all other entries one. -/
def facetSums : (Fin (n+1) → R) →ₗ[R] (Fin (n+1) → R) where
  toFun x i := (∑ j, x j) - x i
  map_add' x y := by ext i; simp [sum_add_distrib]; ring
  map_smul' r x := by ext i; simp [mul_sub, mul_sum]

/-- Total output equals the simplex dimension times total input. -/
theorem sum_facetSums (x : Fin (n+1) → R) :
    ∑ i, facetSums R n x i = (n:R) * ∑ j, x j := by
  simp [facetSums, sum_sub_distrib, nsmul_eq_mul]
  ring

/-- A lift exists exactly when the total coordinate sum is divisible by the dimension. -/
theorem mem_range_facetSums (y : Fin (n+1) → R) :
    y ∈ range (facetSums R n) ↔ (n:R) ∣ ∑ i, y i := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, sum_facetSums R n x⟩
  · rintro ⟨b,hb⟩
    refine ⟨fun i => b-y i, ?_⟩
    ext i
    simp [facetSums, sum_sub_distrib, nsmul_eq_mul, hb]
    ring

/-- Kernel vectors are exactly the constant vectors annihilated by the dimension. -/
theorem mem_ker_facetSums (x : Fin (n+1) → R) :
    x ∈ ker (facetSums R n) ↔ ∃ b : R, (n:R)*b = 0 ∧ x = fun _ => b := by
  constructor
  · intro h
    have hz : facetSums R n x = 0 := h
    have hb (i : Fin (n+1)) : x i = ∑ j, x j := by
      have hh := congrFun hz i
      exact (sub_eq_zero.mp hh).symm
    refine ⟨_, ?_, funext hb⟩
    rw [← sum_facetSums, hz]
    simp
  · rintro ⟨b,hb,rfl⟩
    apply LinearMap.mem_ker.mpr
    ext i
    simp [facetSums, nsmul_eq_mul, add_mul, hb]

/-- The obstruction homomorphism takes the total sum modulo the dimension ideal. -/
def facetObstruction : (Fin (n+1) → R) →ₗ[R] R ⧸ Ideal.span ({(n:R)} : Set R) :=
  (Ideal.span ({(n:R)} : Set R)).mkQ.comp (∑ i, LinearMap.proj i)

theorem facetObstruction_apply (x : Fin (n+1) → R) :
    facetObstruction R n x = Submodule.Quotient.mk (∑ i, x i) := by
  simp [facetObstruction]

/-- The obstruction detects every failure to lift over the coefficient ring. -/
theorem ker_facetObstruction : ker (facetObstruction R n) = range (facetSums R n) := by
  ext x
  rw [LinearMap.mem_ker, facetObstruction_apply, Submodule.Quotient.mk_eq_zero,
    Ideal.mem_span_singleton, mem_range_facetSums]

theorem facetObstruction_surjective : Function.Surjective (facetObstruction R n) := by
  intro z
  obtain ⟨b,rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine ⟨Pi.single 0 b, ?_⟩
  rw [facetObstruction_apply]
  simp

/-- The sole invariant factor of the facet frame that can fail to be a unit is `n`. -/
def facetSumsCokernelEquiv :
    ((Fin (n+1) → R) ⧸ range (facetSums R n)) ≃ₗ[R] R ⧸ Ideal.span ({(n:R)} : Set R) :=
  (Submodule.quotEquivOfEq _ _ (ker_facetObstruction R n).symm).trans
    ((facetObstruction R n).quotKerEquivOfSurjective (facetObstruction_surjective R n))

/-- The obstruction survives exactly where the residue characteristic divides the
dimension. This includes the binary side-point dependence in a Fano triangle. -/
theorem facetSums_surjective_iff (K : Type*) [Field K] :
    Function.Surjective (facetSums K n) ↔ (n:K) ≠ 0 := by
  constructor
  · intro h hn
    have hm : Pi.single (M := fun _ : Fin (n+1) => K) 0 1 ∈ range (facetSums K n) := h _
    have hd := (mem_range_facetSums K n _).mp hm
    simpa [hn] using hd
  · intro hn y
    apply (mem_range_facetSums K n y).mpr
    exact (isUnit_iff_ne_zero.mpr hn).dvd _

#print axioms mem_ker_facetSums
#print axioms facetSumsCokernelEquiv
#print axioms facetSums_surjective_iff

end
end GaloisForLFunctions.RepresentationLifting
