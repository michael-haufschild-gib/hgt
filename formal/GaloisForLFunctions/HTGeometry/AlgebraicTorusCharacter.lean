import GaloisForLFunctions.HTGeometry.AffineExponentialGroupHopf

/-!
# Algebraic characters of a split torus

A point `y : ι → Lˣ` evaluates a finitely supported integral character by the finite Laurent
monomial `∏ i, y i ^ m i`.  This file packages that character as an additive homomorphism and
the induced algebra map from the group algebra.  Unlike the existing analytic torus characters,
the construction works over an arbitrary field extension and is the point-evaluation layer for
split diagonalizable group schemes.
-/

namespace GaloisForLFunctions.HTGeometry
namespace AlgebraicTorusCharacter

noncomputable section

variable {ι k L : Type*} [Field k] [Field L] [Algebra k L]

/-- Value of a finitely supported integral character at a split-torus point. -/
def character (y : ι → Lˣ) (m : ι →₀ ℤ) : Lˣ :=
  ∏ i ∈ m.support, y i ^ m i

@[simp] theorem character_zero (y : ι → Lˣ) :
    character y (0 : ι →₀ ℤ) = 1 := by
  simp [character]

theorem character_apply_of_subset {m : ι →₀ ℤ} {s : Finset ι}
    (hm : m.support ⊆ s) (y : ι → Lˣ) :
    character y m = ∏ i ∈ s, y i ^ m i := by
  classical
  rw [character]
  refine Finset.prod_subset hm (fun i _ hi ↦ ?_)
  rw [Finsupp.notMem_support_iff.mp hi, zpow_zero]

/-- Character values multiply when integral exponent vectors add. -/
theorem character_add (y : ι → Lˣ) (m n : ι →₀ ℤ) :
    character y (m + n) = character y m * character y n := by
  classical
  let s : Finset ι := m.support ∪ n.support ∪ (m + n).support
  have hm : m.support ⊆ s := (Finset.subset_union_left).trans Finset.subset_union_left
  have hn : n.support ⊆ s := (Finset.subset_union_right).trans Finset.subset_union_left
  have hmn : (m + n).support ⊆ s := Finset.subset_union_right
  rw [character_apply_of_subset hmn y, character_apply_of_subset hm y,
    character_apply_of_subset hn y, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [Finsupp.add_apply, zpow_add]

/-- Character evaluation is multiplicative in the torus point. -/
theorem character_mul_point (y z : ι → Lˣ) (m : ι →₀ ℤ) :
    character (y * z) m = character y m * character z m := by
  classical
  rw [character, character, character, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ ↦ ?_)
  rw [Pi.mul_apply, mul_zpow]

@[simp] theorem character_one_point (m : ι →₀ ℤ) :
    character (1 : ι → Lˣ) m = 1 := by
  classical
  simp [character]

@[simp] theorem character_inv_point (y : ι → Lˣ) (m : ι →₀ ℤ) :
    character y⁻¹ m = (character y m)⁻¹ := by
  apply mul_left_cancel (a := character y m)
  rw [← character_mul_point, mul_inv_cancel, character_one_point, mul_inv_cancel]

/-- A split-torus point is an additive character of its integral character lattice. -/
def addHom (y : ι → Lˣ) : (ι →₀ ℤ) →+ Additive Lˣ where
  toFun m := Additive.ofMul (character y m)
  map_zero' := by simp
  map_add' m n := by
    apply Additive.toMul.injective
    exact character_add y m n

@[simp] theorem addHom_apply_toMul (y : ι → Lˣ) (m : ι →₀ ℤ) :
    (addHom y m).toMul = character y m := rfl

@[simp] theorem character_neg (y : ι → Lˣ) (m : ι →₀ ℤ) :
    character y (-m) = (character y m)⁻¹ := by
  apply Additive.ofMul.injective
  change addHom y (-m) = -(addHom y m)
  exact map_neg (addHom y) m

@[simp] theorem character_single (y : ι → Lˣ) (i : ι) (z : ℤ) :
    character y (Finsupp.single i z) = y i ^ z := by
  classical
  by_cases hz : z = 0
  · subst z
    simp
  · rw [character]
    simp [hz]

/-- Multiplicative character used by group-algebra evaluation. -/
def monoidHom (y : ι → Lˣ) : Multiplicative (ι →₀ ℤ) →* L where
  toFun m := (character y m.toAdd : L)
  map_one' := by simp
  map_mul' m n := by
    exact congrArg Units.val (character_add y m.toAdd n.toAdd)

/-- Evaluation of the split-torus group algebra at an `L`-valued point. -/
def eval (y : ι → Lˣ) : AddMonoidAlgebra k (ι →₀ ℤ) →ₐ[k] L :=
  AddMonoidAlgebra.lift k L (ι →₀ ℤ) (monoidHom y)

@[simp] theorem eval_single (y : ι → Lˣ) (m : ι →₀ ℤ) (c : k) :
    eval y (AddMonoidAlgebra.single m c) = algebraMap k L c * (character y m : L) := by
  simp [eval, monoidHom, Algebra.smul_def]

end
end AlgebraicTorusCharacter
end GaloisForLFunctions.HTGeometry
