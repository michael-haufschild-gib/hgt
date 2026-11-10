import GaloisForLFunctions.HyperbolicArakelovTheory.TheRestrictedGreenProductHasSummableSources
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# A single-point Green kernel on the full restricted adelic product

Monotone point-source iteration for the actual `p⁻²`-weighted adjacency
operator is bounded by the restricted critical product. A summable place
majorant passes the iteration limit through the infinite adjacency sum.
The result is the least nonnegative unit-source solution in the operator
domain, with a strictly positive diagonal and no finite-place cutoff.
The constant-function adjacency rows diverge; spatial decay supplies the
convergence domain of the Green kernel.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic AdelicAdjacency CoupledProductObstruction

/-- Successive finite occupation depths, allowing every prime at each step. -/
def occupationPartial (x : FiniteVertices) : ℕ → FiniteVertices → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun y => (pointMass x y + adjacency (occupationPartial x n) y) / edge

/-- The occupation limit is defined on the full restricted product. -/
def green (x y : FiniteVertices) : ℝ := ⨆ n : ℕ, occupationPartial x n y

/-- Supersolutions belong to the actual convergence domain of weighted adjacency. -/
def supersolutions (x : FiniteVertices) : Set (FiniteVertices → ℝ) :=
  {u | (∀ y, 0 ≤ u y) ∧ InDomain u ∧
    ∀ y, pointMass x y ≤ edge * u y - adjacency u y}

private theorem pointMass_nonneg (x y : FiniteVertices) : 0 ≤ pointMass x y := by
  unfold pointMass
  split_ifs <;> norm_num

/-- The same product barrier bounds every occupation depth at every vertex. -/
theorem partial_bounds (x : FiniteVertices) (n : ℕ) :
    (∀ y, 0 ≤ occupationPartial x n y) ∧ occupationPartial x n ≤ barrier x := by
  induction n with
  | zero => exact ⟨fun _ => le_rfl, barrier_nonneg x⟩
  | succ n ih =>
    have hd := inDomain_of_le_barrier x ih.1 ih.2
    refine ⟨fun y => div_nonneg
      (add_nonneg (pointMass_nonneg x y) (adjacency_nonneg ih.1 y)) edge_pos.le, ?_⟩
    intro y
    apply (div_le_iff₀ edge_pos).mpr
    have hm := adjacency_mono hd (barrier_inDomain x) ih.2 y
    have hb := barrier_source x y
    nlinarith only [hm, hb]

theorem partial_nonneg (x : FiniteVertices) (n : ℕ) (y : FiniteVertices) :
    0 ≤ occupationPartial x n y := (partial_bounds x n).1 y

theorem partial_le_barrier (x : FiniteVertices) (n : ℕ) : occupationPartial x n ≤ barrier x :=
  (partial_bounds x n).2

theorem partial_inDomain (x : FiniteVertices) (n : ℕ) : InDomain (occupationPartial x n) :=
  inDomain_of_le_barrier x (partial_nonneg x n) (partial_le_barrier x n)

private theorem partial_le_succ (x : FiniteVertices) (n : ℕ) :
    occupationPartial x n ≤ occupationPartial x (n + 1) := by
  induction n with
  | zero => exact partial_nonneg x 1
  | succ n ih =>
    intro y
    exact div_le_div_of_nonneg_right
      (add_le_add (le_refl (pointMass x y))
        (adjacency_mono (partial_inDomain x n) (partial_inDomain x (n + 1)) ih y))
      edge_pos.le

theorem partial_mono (x y : FiniteVertices) : Monotone (fun n => occupationPartial x n y) :=
  monotone_nat_of_le_succ (fun n => partial_le_succ x n y)

private theorem partial_bddAbove (x y : FiniteVertices) :
    BddAbove (Set.range (fun n => occupationPartial x n y)) := by
  refine ⟨barrier x y, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact partial_le_barrier x n y

/-- Pointwise monotone convergence is controlled by an explicitly constructed finite barrier. -/
theorem tendsto_partial (x y : FiniteVertices) :
    Tendsto (fun n => occupationPartial x n y) atTop (𝓝 (green x y)) :=
  tendsto_atTop_ciSup (partial_mono x y) (partial_bddAbove x y)

theorem green_nonneg (x y : FiniteVertices) : 0 ≤ green x y :=
  le_ciSup (partial_bddAbove x y) 0

theorem green_le_barrier (x : FiniteVertices) : green x ≤ barrier x :=
  fun y => ciSup_le (fun n => partial_le_barrier x n y)

/-- The Green kernel belongs to the absolute-convergence domain of weighted adjacency. -/
theorem green_inDomain (x : FiniteVertices) : InDomain (green x) :=
  inDomain_of_le_barrier x (green_nonneg x) (green_le_barrier x)

/-- The product majorant permits passage through the entire countable adjacency sum. -/
theorem tendsto_adjacency_partial (x y : FiniteVertices) :
    Tendsto (fun n => adjacency (occupationPartial x n) y) atTop (𝓝 (adjacency (green x) y)) := by
  apply tendsto_tsum_of_dominated_convergence (barrier_inDomain x y)
  · intro p
    exact (tendsto_finsetSum (neighbors p (y.1 p))
      (fun z _ => tendsto_partial x (replaceVertex p y z))).const_mul (weight p)
  · exact Eventually.of_forall fun n p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (placeTerm_nonneg p (partial_nonneg x n) y)]
      exact placeTerm_mono p (partial_le_barrier x n) y

/-- A genuine single full-product point source, with no omitted finite place. -/
theorem green_source (x y : FiniteVertices) :
    edge * green x y - adjacency (green x) y = pointMass x y := by
  have hs (n : ℕ) : edge * occupationPartial x (n + 1) y -
      adjacency (occupationPartial x n) y = pointMass x y := by
    rw [occupationPartial, mul_div_cancel₀ _ edge_pos.ne']
    ring
  have hl := (((tendsto_partial x y).comp (tendsto_add_atTop_nat 1)).const_mul edge).sub
    (tendsto_adjacency_partial x y)
  have hc : Tendsto (fun n : ℕ => edge * occupationPartial x (n + 1) y - adjacency (occupationPartial x n) y)
      atTop (𝓝 (pointMass x y)) := by
    simpa only [hs] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => pointMass x y) atTop (𝓝 (pointMass x y)))
  exact tendsto_nhds_unique hl hc

private theorem partial_le_supersolution (x : FiniteVertices) {u : FiniteVertices → ℝ}
    (hu : u ∈ supersolutions x) (n : ℕ) : occupationPartial x n ≤ u := by
  induction n with
  | zero => exact hu.1
  | succ n ih =>
    intro y
    apply (div_le_iff₀ edge_pos).mpr
    have hm := adjacency_mono (partial_inDomain x n) hu.2.1 ih y
    have hs := hu.2.2 y
    nlinarith only [hm, hs]

/-- Minimality among all nonnegative supersolutions in the operator domain; no growth bound is imposed. -/
theorem green_isLeast (x : FiniteVertices) : IsLeast (supersolutions x) (green x) := by
  refine ⟨⟨green_nonneg x, green_inDomain x, fun y => (green_source x y).symm.le⟩, ?_⟩
  intro u hu y
  exact ciSup_le (fun n => partial_le_supersolution x hu n y)

/-- The full weighted kernel has a strictly positive diagonal with explicit bounds. -/
theorem green_self_bounds (x : FiniteVertices) :
    1 / edge ≤ green x x ∧ green x x ≤ 1 / mass := by
  constructor
  · apply (div_le_iff₀ edge_pos).mpr
    have hs := green_source x x
    rw [pointMass, if_pos rfl] at hs
    have ha := adjacency_nonneg (green_nonneg x) x
    nlinarith only [hs, ha]
  · simpa only [barrier, product_self] using green_le_barrier x x

theorem green_self_pos (x : FiniteVertices) : 0 < green x x :=
  (one_div_pos.mpr edge_pos).trans_le (green_self_bounds x).1

private theorem pointMass_smul (a : FiniteAdelicGroup) (x y : FiniteVertices) :
    pointMass (a • x) (a • y) = pointMass x y := by
  simp only [pointMass, (MulAction.injective a).eq_iff]

private theorem partial_smul (a : FiniteAdelicGroup) (x : FiniteVertices) (n : ℕ)
    (y : FiniteVertices) : occupationPartial (a • x) n (a • y) = occupationPartial x n y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    have he : (fun z => occupationPartial (a • x) n (a • z)) = occupationPartial x n := funext ih
    change (pointMass (a • x) (a • y) + adjacency (occupationPartial (a • x) n) (a • y)) / edge =
      (pointMass x y + adjacency (occupationPartial x n) y) / edge
    rw [adjacency_smul, he, pointMass_smul]

/-- The full weighted Green kernel is invariant under simultaneous finite adelic transport. -/
theorem green_smul (a : FiniteAdelicGroup) (x y : FiniteVertices) :
    green (a • x) (a • y) = green x y := by
  simp only [green, partial_smul]

/-- Constant-function rows diverge, even though the spatially decaying Green source is well-defined. -/
theorem constant_row_not_summable (y : FiniteVertices) :
    ¬ Summable (fun p : Prime => placeTerm p (fun _ => 1) y) := by
  intro hs
  apply Nat.Primes.not_summable_one_div
  apply Summable.of_nonneg_of_le (fun p => one_div_nonneg.mpr (Nat.cast_nonneg p.1)) ?_ hs
  intro p
  have hp : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hrow : placeTerm p (fun _ => 1) y = ((p.1 : ℝ) + 1) / (p.1 : ℝ) ^ 2 := by
    simp only [placeTerm, localAdj, Finset.sum_const, card_neighbors, nsmul_eq_mul,
      mul_one, Nat.cast_add, Nat.cast_one, weight]
    ring
  rw [hrow]
  apply (div_le_div_iff₀ hp (sq_pos_of_pos hp)).mpr
  nlinarith only [hp]

#print axioms green_inDomain
#print axioms tendsto_adjacency_partial
#print axioms green_source
#print axioms green_isLeast
#print axioms green_self_bounds
#print axioms green_self_pos
#print axioms green_smul
#print axioms constant_row_not_summable

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
