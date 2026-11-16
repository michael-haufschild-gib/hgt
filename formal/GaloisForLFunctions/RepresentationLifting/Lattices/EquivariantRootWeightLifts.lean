import GaloisForLFunctions.RepresentationLifting.Lattices.RootWeightCokernel
import Mathlib.Tactic.Ring

/-!
# Permutations and integral lifts of type-A weights

Permuting coordinates acts trivially on the root-to-weight cokernel.
Multiplication by an integer lifts from weights to roots exactly when the
number of coordinates divides that integer. The lift is explicit and unique.

These are the integral sum-zero mechanisms used in Proposition 4.2 of
Donovan–Wang–Zhang, *The D-equivalence conjecture for hyperkähler varieties
of generalized Kummer type*, https://arxiv.org/abs/2611.04118.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting
variable (ι : Type*) [Fintype ι]

/-- Coordinate permutations preserve the integral sum-zero lattice. -/
def permuteRoot (σ : Equiv.Perm ι) : coordinateRootLattice ι →ₗ[ℤ] coordinateRootLattice ι where
  toFun v := ⟨fun i => v.val (σ i), (Equiv.sum_comp σ v.val).trans v.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Permute a weight and restore its zero pivot coordinate. -/
def permuteWeight (p : ι) (σ : Equiv.Perm ι) :
    coordinateWeightLattice ι p →ₗ[ℤ] coordinateWeightLattice ι p where
  toFun w := ⟨fun i => w.val (σ i) - w.val (σ p), sub_self _⟩
  map_add' v w := by
    ext i
    change (v.val (σ i) + w.val (σ i)) - (v.val (σ p) + w.val (σ p)) =
      (v.val (σ i) - v.val (σ p)) + (w.val (σ i) - w.val (σ p))
    abel
  map_smul' c w := by
    ext i
    change c * w.val (σ i) - c * w.val (σ p) =
      c * (w.val (σ i) - w.val (σ p))
    exact (mul_sub _ _ _).symm

/-- The permutation defect is always a root weight. -/
theorem permuteWeight_sub_mem_range (p : ι) (σ : Equiv.Perm ι)
    (w : coordinateWeightLattice ι p) :
    permuteWeight ι p σ w - w ∈ LinearMap.range (rootToWeight ι p) := by
  rw [mem_range_rootToWeight_iff]
  refine ⟨-w.val (σ p), ?_⟩
  change (∑ i, ((w.val (σ i) - w.val (σ p)) - w.val i)) = _
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Equiv.sum_comp σ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Every permutation fixes every class in the root-to-weight cokernel. -/
theorem permuteWeight_quotient (p : ι) (σ : Equiv.Perm ι)
    (w : coordinateWeightLattice ι p) :
    (Submodule.Quotient.mk (permuteWeight ι p σ w) :
      coordinateWeightLattice ι p ⧸ LinearMap.range (rootToWeight ι p)) =
        Submodule.Quotient.mk w :=
  (Submodule.Quotient.eq _).mpr (permuteWeight_sub_mem_range ι p σ w)

/-- Clear the denominator in the rational projection to the sum-zero hyperplane. -/
def scaledWeightLift (p : ι) (k : ℤ) :
    coordinateWeightLattice ι p →ₗ[ℤ] coordinateRootLattice ι where
  toFun w := ⟨fun i => (Fintype.card ι : ℤ) * k * w.val i - k * ∑ j, w.val j, by
    change (∑ i, ((Fintype.card ι : ℤ) * k * w.val i - k * ∑ j, w.val j)) = 0
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring⟩
  map_add' v w := by
    ext i
    change (Fintype.card ι : ℤ) * k * (v.val i + w.val i) -
      k * (∑ j, (v.val j + w.val j)) = _
    rw [Finset.sum_add_distrib]
    change _ = ((Fintype.card ι : ℤ) * k * v.val i - k * ∑ j, v.val j) +
      ((Fintype.card ι : ℤ) * k * w.val i - k * ∑ j, w.val j)
    ring
  map_smul' c w := by
    ext i
    change (Fintype.card ι : ℤ) * k * (c * w.val i) -
      k * (∑ j, c * w.val j) =
        c * ((Fintype.card ι : ℤ) * k * w.val i - k * ∑ j, w.val j)
    rw [← Finset.mul_sum]
    ring

theorem rootToWeight_scaledWeightLift (p : ι) (k : ℤ)
    (w : coordinateWeightLattice ι p) :
    rootToWeight ι p (scaledWeightLift ι p k w) = ((Fintype.card ι : ℤ) * k) • w := by
  ext i
  change ((Fintype.card ι : ℤ) * k * w.val i - k * ∑ j, w.val j) -
    ((Fintype.card ι : ℤ) * k * w.val p - k * ∑ j, w.val j) =
      ((Fintype.card ι : ℤ) * k) * w.val i
  have hp : w.val p = 0 := w.property
  rw [hp]
  ring

/-- The denominator-clearing lift commutes with all coordinate permutations. -/
theorem scaledWeightLift_permute (p : ι) (k : ℤ) (σ : Equiv.Perm ι)
    (w : coordinateWeightLattice ι p) :
    scaledWeightLift ι p k (permuteWeight ι p σ w) =
      permuteRoot ι σ (scaledWeightLift ι p k w) := by
  ext i
  change (Fintype.card ι : ℤ) * k * (w.val (σ i) - w.val (σ p)) -
    k * (∑ j, (w.val (σ j) - w.val (σ p))) =
      (Fintype.card ι : ℤ) * k * w.val (σ i) - k * ∑ j, w.val j
  rw [Finset.sum_sub_distrib, Equiv.sum_comp σ, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- Scalar multiplication lifts integrally precisely at multiples of the lattice index. -/
theorem exists_rootWeight_lift_iff [Nontrivial ι] (p : ι) (a : ℤ) :
    (∃ L : coordinateWeightLattice ι p →ₗ[ℤ] coordinateRootLattice ι,
      ∀ w, rootToWeight ι p (L w) = a • w) ↔ (Fintype.card ι : ℤ) ∣ a := by
  classical
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨j, hj⟩ := exists_ne p
    let w : coordinateWeightLattice ι p :=
      ⟨Pi.single j 1, by change (Pi.single j (1 : ℤ) : ι → ℤ) p = 0; simp [Ne.symm hj]⟩
    have hw : a • w ∈ LinearMap.range (rootToWeight ι p) := ⟨L w, hL w⟩
    rw [mem_range_rootToWeight_iff] at hw
    change (Fintype.card ι : ℤ) ∣ ∑ i, a * (Pi.single j (1 : ℤ) : ι → ℤ) i at hw
    simpa [← Finset.mul_sum] using hw
  · rintro ⟨k, rfl⟩
    exact ⟨scaledWeightLift ι p k, rootToWeight_scaledWeightLift ι p k⟩

/-- Injectivity of the root inclusion forces uniqueness of every integral scalar lift. -/
theorem rootWeight_lift_unique (p : ι) (a : ℤ)
    (L M : coordinateWeightLattice ι p →ₗ[ℤ] coordinateRootLattice ι)
    (hL : ∀ w, rootToWeight ι p (L w) = a • w)
    (hM : ∀ w, rootToWeight ι p (M w) = a • w) : L = M := by
  apply LinearMap.ext
  intro w
  exact rootToWeight_injective ι p ((hL w).trans (hM w).symm)

#print axioms permuteWeight_quotient
#print axioms scaledWeightLift_permute
#print axioms exists_rootWeight_lift_iff
#print axioms rootWeight_lift_unique
end GaloisForLFunctions.RepresentationLifting
