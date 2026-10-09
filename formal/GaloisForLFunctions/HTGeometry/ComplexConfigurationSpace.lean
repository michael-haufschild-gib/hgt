import GaloisForLFunctions.HTGeometry.ComplexPolynomialComplementPathConnected
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Finite ordered complex configurations

The locus of injective tuples is open, path connected, and dense. Connectedness uses
the corpus theorem for complex polynomial complements; density uses affine perturbations
avoiding finitely many collision parameters.
-/

open Set Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.FiniteComplexConfiguration
noncomputable section

def space (m : ℕ) : Set (Fin m → ℂ) := {b | Function.Injective b}

def discriminant (m : ℕ) : MvPolynomial (Fin m) ℂ :=
  ∏ i, ∏ j ∈ (Finset.univ : Finset (Fin m)).filter (fun j => i < j),
    (MvPolynomial.X i - MvPolynomial.X j)

theorem eval_discriminant_ne_zero_iff (m : ℕ) (b : Fin m → ℂ) :
    MvPolynomial.eval b (discriminant m) ≠ 0 ↔ Function.Injective b := by
  classical
  simp only [discriminant, map_prod, map_sub, MvPolynomial.eval_X,
    Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const, Finset.mem_filter, true_and,
    ne_eq, sub_eq_zero]
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h i j hlt hij
    · exact h j i hgt hij.symm
  · intro h i j hij heq
    exact (ne_of_lt hij) (h heq)

/-- The natural-index tuple supplies one configuration in every finite dimension. -/
theorem injective_natTuple (m : ℕ) : Function.Injective (fun i : Fin m => (i.val : ℂ)) := by
  intro i j hij
  apply Fin.ext
  change (i.val : ℂ) = (j.val : ℂ) at hij
  exact_mod_cast hij

theorem space_eq_nonzeroLocus (m : ℕ) :
    space m = {b | MvPolynomial.eval b (discriminant m) ≠ 0} := by
  ext b
  exact (eval_discriminant_ne_zero_iff m b).symm

theorem isOpen_space (m : ℕ) : IsOpen (space m) := by
  rw [space_eq_nonzeroLocus]
  exact isOpen_ne_fun (MvPolynomial.continuous_eval (discriminant m)) continuous_const

/-- Finite ordered configurations in C are path connected. -/
theorem isPathConnected_space (m : ℕ) : IsPathConnected (space m) := by
  rw [space_eq_nonzeroLocus]
  exact isPathConnected_complexMvPolynomial_nonzeroLocus (discriminant m)
    ((eval_discriminant_ne_zero_iff m _).mpr (injective_natTuple m))

/-- A finite set of forbidden affine perturbations cannot obstruct density of configurations. -/
theorem dense_space (m : ℕ) : Dense (space m) := by
  intro b
  apply mem_closure_iff_nhds.mpr
  intro V hV
  let perturb : ℂ → (Fin m → ℂ) := fun t i => b i + t * (i.val : ℂ)
  let bad : Set ℂ := Set.range (fun p : Fin m × Fin m =>
    (b p.2 - b p.1) / ((p.1.val : ℂ) - (p.2.val : ℂ)))
  have hbad : bad.Finite := Set.finite_range _
  have hcont : Continuous perturb := by unfold perturb; fun_prop
  have hzero : perturb 0 = b := by ext i; simp [perturb]
  have hpre : perturb ⁻¹' V ∈ 𝓝 (0 : ℂ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    rwa [hzero]
  obtain ⟨t, htbad, htV⟩ := (hbad.countable.dense_compl ℝ).inter_nhds_nonempty hpre
  refine ⟨perturb t, htV, ?_⟩
  intro i j hij
  by_contra hne
  have hd : (i.val : ℂ) - (j.val : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact fun heq => hne (injective_natTuple m heq)
  apply htbad
  refine ⟨(i, j), ?_⟩
  apply (div_eq_iff hd).mpr
  dsimp [perturb] at hij
  linear_combination -hij

end
end GaloisForLFunctions.HTGeometry.FiniteComplexConfiguration
