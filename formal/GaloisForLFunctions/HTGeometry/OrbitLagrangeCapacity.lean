import GaloisForLFunctions.HTGeometry.ProductCapacityRealization
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Analytic.Polynomial

/-!
# An explicit translation orbit realizing every finite capacity

The capacity dichotomy on a product domain is stated for an observation packet which is the identity
at one point of the first factor.  This file exhibits such a packet explicitly, so the realization
half is not merely conditional on an interpolation hypothesis: the Lagrange basis at the first `n`
points of a translation orbit is entire, and the orbit observation matrix it defines is the identity
at the base point.

Consequently, for every `n`, an explicit observable on `ℂ × V` whose translation orbit is built from
an `n`-element differentially independent palette has `n` differentially independent translates,
while no `n + 1` observations mixed from that palette are ever differentially independent.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open Matrix GaloisForLFunctions

noncomputable section

/-! ### The nodes of a translation orbit -/

/-- The `k`-th point of the translation orbit of `x₀` by `a`. -/
def orbitNode (x₀ a : ℂ) {n : ℕ} (k : Fin n) : ℂ := x₀ + (k : ℕ) * a

theorem orbitNode_injOn {x₀ a : ℂ} (ha : a ≠ 0) {n : ℕ} :
    Set.InjOn (orbitNode x₀ a (n := n)) ↑(Finset.univ : Finset (Fin n)) := by
  intro i _ j _ h
  rw [orbitNode, orbitNode] at h
  have h1 : ((i : ℕ) : ℂ) * a = ((j : ℕ) : ℂ) * a := add_left_cancel h
  have h2 : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := mul_right_cancel₀ ha h1
  exact Fin.ext (by exact_mod_cast h2)

/-! ### The orbit Lagrange packet -/

/-- The `j`-th Lagrange basis function of the orbit nodes, translated by `i` steps. -/
def orbitLagrangeFun (x₀ a : ℂ) {n : ℕ} (i j : Fin n) : ℂ → ℂ :=
  fun z => (Lagrange.basis Finset.univ (orbitNode x₀ a) j).eval (z + (i : ℕ) * a)

theorem analyticOnNhd_orbitLagrangeFun (x₀ a : ℂ) {n : ℕ} (i j : Fin n) (U : Set ℂ) :
    AnalyticOnNhd ℂ (orbitLagrangeFun x₀ a i j) U := by
  have hbase : AnalyticOnNhd ℂ (fun z : ℂ => z + (i : ℕ) * a) U :=
    analyticOnNhd_id.add analyticOnNhd_const
  have h := hbase.aeval_polynomial (Lagrange.basis Finset.univ (orbitNode x₀ a) j)
  have heq : (fun z : ℂ => Polynomial.aeval (z + (i : ℕ) * a)
      (Lagrange.basis Finset.univ (orbitNode x₀ a) j)) = orbitLagrangeFun x₀ a i j := by
    funext z
    simp [orbitLagrangeFun, Polynomial.aeval_def]
  rwa [heq] at h

/-- The value of the translated Lagrange basis at the base point is the Kronecker delta. -/
theorem orbitLagrangeFun_apply {x₀ a : ℂ} (ha : a ≠ 0) {n : ℕ} (i j : Fin n) :
    orbitLagrangeFun x₀ a i j x₀ = if i = j then 1 else 0 := by
  have hnode : x₀ + (i : ℕ) * a = orbitNode x₀ a i := rfl
  rw [orbitLagrangeFun, hnode]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    exact Lagrange.eval_basis_self (orbitNode_injOn ha) (Finset.mem_univ i)
  · rw [if_neg hij]
    exact Lagrange.eval_basis_of_ne (Ne.symm hij) (Finset.mem_univ i)

/-- The orbit observation packet, as analytic germs on the plane. -/
def orbitLagrangeGerm (x₀ a : ℂ) {n : ℕ} (i j : Fin n) :
    analyticGermSubringOn (Set.univ : Set ℂ) :=
  ⟨((orbitLagrangeFun x₀ a i j : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ),
    ⟨orbitLagrangeFun x₀ a i j, analyticOnNhd_orbitLagrangeFun x₀ a i j _, rfl⟩⟩

/-- The orbit observation matrix. -/
def orbitLagrangeMatrix (x₀ a : ℂ) (n : ℕ) :
    Matrix (Fin n) (Fin n) (analyticGermSubringOn (Set.univ : Set ℂ)) :=
  Matrix.of fun i j => orbitLagrangeGerm x₀ a i j

/-- **The orbit observation matrix is the identity at the base point.** -/
theorem orbitLagrangeMatrix_eval {x₀ a : ℂ} (ha : a ≠ 0) (n : ℕ) :
    (orbitLagrangeMatrix x₀ a n).map (analyticGermEval (Set.mem_univ x₀)) = 1 := by
  ext i j
  rw [Matrix.map_apply, orbitLagrangeMatrix, Matrix.of_apply,
    analyticGermEval_of_coe (Set.mem_univ x₀) (f := orbitLagrangeFun x₀ a i j) rfl,
    orbitLagrangeFun_apply ha, Matrix.one_apply]

/-! ### The realization -/

/-- **An explicit translation orbit realizes capacity `n`.**  With the entire Lagrange packet as
observation matrix, every `n`-element differentially independent palette of the product field yields
`n` differentially independent observations over the meromorphic field of the first factor. -/
theorem orbitLagrange_capacity_realization {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {V : Set F} (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (v : F)
    {n : ℕ} {a : ℂ} (ha : a ≠ 0) (x₀ : ℂ) :
    letI := isDomain_analyticGermSubringOn (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
      Set.univ_nonempty
    letI := isDomain_analyticGermSubringOn ((Set.univ : Set ℂ) ×ˢ V) (isOpen_univ.prod hVo)
      (isPreconnected_univ.prod hVc) (Set.univ_nonempty.prod hVne)
    letI := dirMeroFieldDifferential (isOpen_univ.prod hVo) (isPreconnected_univ.prod hVc)
      (Set.univ_nonempty.prod hVne) ((0 : ℂ), v)
    letI : Algebra (dirMeroField (Set.univ : Set ℂ)) (dirMeroField ((Set.univ : Set ℂ) ×ˢ V)) :=
      (meroPullbackFst isOpen_univ isPreconnected_univ Set.univ_nonempty (isOpen_univ.prod hVo)
        (isPreconnected_univ.prod hVc) (Set.univ_nonempty.prod hVne) hVne).toAlgebra
    ∀ y : Fin n → dirMeroField ((Set.univ : Set ℂ) ×ˢ V),
      DifferentialIndependent (dirMeroField (Set.univ : Set ℂ)) y →
      DifferentialIndependent (dirMeroField (Set.univ : Set ℂ))
        (matrixLinearForms ((orbitLagrangeMatrix x₀ a n).map
          (algebraMap (analyticGermSubringOn (Set.univ : Set ℂ))
            (dirMeroField (Set.univ : Set ℂ)))) y) :=
  productCapacity_realization isOpen_univ isPreconnected_univ Set.univ_nonempty hVo hVc hVne v
    (Set.mem_univ x₀) (orbitLagrangeMatrix x₀ a n) (orbitLagrangeMatrix_eval ha n)

end

end GaloisForLFunctions.HTGeometry
