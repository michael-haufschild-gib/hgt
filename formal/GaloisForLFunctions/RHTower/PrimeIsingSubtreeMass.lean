import GaloisForLFunctions.RHTower.PrimeIsingTreeBalancedVarianceRankNoGo

/-!
# Subtree mass for nonuniform prime Ising trees

Apply the rooted-cluster argument of Lemma 16.2 in *Ordinary two-point
correlations of multiplicative functions* (OpenAI, September 24, 2026) to the
existing normalized FK expansion. Unequal edge couplings are allowed.

A root's descendant cluster is nontrivial with probability one minus the
product of its outgoing cut probabilities. Summing this exact expression over
all possible roots gives the expected number of nontrivial descendant clusters,
bounded by the existing vertex count. These overlapping descendant clusters
are indexed by their roots, rather than connected components of the whole tree.

Source: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf
-/


namespace GaloisForLFunctions.RHTower
noncomputable section

private theorem cluster_list_sum_sub {α : Type*} (xs : List α) (f g : α → ℝ) :
    (xs.map (fun x => f x - g x)).sum = (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring


/-- Expectation under the existing normalized FK bond weights. -/
def treeBondExpectation (T : PrimeIsingTree) (f : PrimeIsingBondTree → ℝ) : ℝ :=
  ((treeBondConfigurations T).map fun B => treeBondCoefficient B * f B).sum

/-- Forest form of FK expectation. -/
def forestBondExpectation (F : PrimeIsingForest) (f : PrimeIsingBondForest → ℝ) : ℝ :=
  ((forestBondConfigurations F).map fun B => forestBondCoefficient B * f B).sum

@[simp] theorem treeBondExpectation_const (T : PrimeIsingTree) (a : ℝ) :
    treeBondExpectation T (fun _ => a) = a := by
  rw [treeBondExpectation, List.sum_map_mul_right,
    sum_treeBondCoefficient_treeBondConfigurations, one_mul]

@[simp] theorem forestBondExpectation_const (F : PrimeIsingForest) (a : ℝ) :
    forestBondExpectation F (fun _ => a) = a := by
  rw [forestBondExpectation, List.sum_map_mul_right,
    sum_forestBondCoefficient_forestBondConfigurations, one_mul]

theorem treeBondExpectation_add (T : PrimeIsingTree) (f g : PrimeIsingBondTree → ℝ) :
    treeBondExpectation T (fun B => f B + g B) =
      treeBondExpectation T f + treeBondExpectation T g := by
  simp only [treeBondExpectation, mul_add, List.sum_map_add]

theorem forestBondExpectation_add (F : PrimeIsingForest) (f g : PrimeIsingBondForest → ℝ) :
    forestBondExpectation F (fun B => f B + g B) =
      forestBondExpectation F f + forestBondExpectation F g := by
  simp only [forestBondExpectation, mul_add, List.sum_map_add]

theorem treeBondExpectation_sub (T : PrimeIsingTree) (f g : PrimeIsingBondTree → ℝ) :
    treeBondExpectation T (fun B => f B - g B) =
      treeBondExpectation T f - treeBondExpectation T g := by
  simp only [treeBondExpectation, mul_sub, cluster_list_sum_sub]

theorem forestBondExpectation_sub (F : PrimeIsingForest) (f g : PrimeIsingBondForest → ℝ) :
    forestBondExpectation F (fun B => f B - g B) =
      forestBondExpectation F f - forestBondExpectation F g := by
  simp only [forestBondExpectation, mul_sub, cluster_list_sum_sub]

theorem forestBondExpectation_mul_left (F : PrimeIsingForest) (a : ℝ)
    (f : PrimeIsingBondForest → ℝ) :
    forestBondExpectation F (fun B => a * f B) = a * forestBondExpectation F f := by
  simp only [forestBondExpectation, mul_left_comm _ a, List.sum_map_mul_left]

@[simp] theorem treeBondExpectation_node (p : Nat.Primes) (F : PrimeIsingForest)
    (f : PrimeIsingBondTree → ℝ) :
    treeBondExpectation (.node p F) f =
      forestBondExpectation F (fun B => f (.node p B)) := by
  simp [treeBondExpectation, treeBondConfigurations, forestBondExpectation,
    List.map_map, Function.comp_def, treeBondCoefficient]

private theorem cluster_sum_flatMap_map {α β : Type*}
    (xs : List α) (f : α → List β) (g : β → ℝ) :
    ((xs.flatMap f).map g).sum =
      (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The existing FK law factors into independent child, tail, and edge choices. -/
theorem forestBondExpectation_cons (c : FerromagneticCoupling)
    (T : PrimeIsingTree) (F : PrimeIsingForest) (f : PrimeIsingBondForest → ℝ) :
    forestBondExpectation (.cons c T F) f =
      treeBondExpectation T (fun B => forestBondExpectation F (fun C =>
        c.coefficient * f (.cons .cut c B C) +
          (1 - c.coefficient) * f (.cons .synchronized c B C))) := by
  unfold forestBondExpectation treeBondExpectation
  rw [forestBondConfigurations, cluster_sum_flatMap_map]
  simp_rw [cluster_sum_flatMap_map]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    forestBondCoefficient]
  apply congrArg (fun h : PrimeIsingBondTree → ℝ => ((treeBondConfigurations T).map h).sum)
  funext B
  rw [← List.sum_map_mul_left]
  apply congrArg (fun h : PrimeIsingBondForest → ℝ => ((forestBondConfigurations F).map h).sum)
  funext C
  ring

/-- Product of the probabilities of cutting every edge leaving the root. -/
def forestRootCutProduct : PrimeIsingForest → ℝ
  | .nil => 1
  | .cons c _ tail => c.coefficient * forestRootCutProduct tail

/-- Indicator that the root's descendant cluster is a singleton. -/
def forestRootSingletonIndicator : PrimeIsingBondForest → ℝ
  | .nil => 1
  | .cons .cut _ _ tail => forestRootSingletonIndicator tail
  | .cons .synchronized _ _ _ => 0

def treeRootSingletonIndicator : PrimeIsingBondTree → ℝ
  | .node _ branches => forestRootSingletonIndicator branches

/-- Root isolation depends only on the incident edges, even in a nonuniform tree. -/
theorem forestBondExpectation_rootSingleton (F : PrimeIsingForest) :
    forestBondExpectation F forestRootSingletonIndicator = forestRootCutProduct F := by
  cases F with
  | nil => simp [forestBondExpectation, forestBondConfigurations,
      forestBondCoefficient, forestRootSingletonIndicator, forestRootCutProduct]
  | cons c child tail =>
      rw [forestBondExpectation_cons]
      simp only [forestRootSingletonIndicator, mul_zero, add_zero,
        forestBondExpectation_mul_left, forestBondExpectation_rootSingleton,
        treeBondExpectation_const, forestRootCutProduct]

/-- Anisotropic rooted-subtree mass: total probability of a non-singleton root cluster. -/
theorem treeBondExpectation_nontrivialRoot (p : Nat.Primes) (F : PrimeIsingForest) :
    treeBondExpectation (.node p F) (fun B => 1 - treeRootSingletonIndicator B) =
      1 - forestRootCutProduct F := by
  rw [treeBondExpectation_sub, treeBondExpectation_const, treeBondExpectation_node]
  change 1 - forestBondExpectation F forestRootSingletonIndicator = _
  rw [forestBondExpectation_rootSingleton]

mutual
  /-- Count vertices whose descendant cluster contains at least one edge. -/
  def treeNontrivialRootCount : PrimeIsingBondTree → ℝ
    | .node _ branches =>
        1 - forestRootSingletonIndicator branches + forestNontrivialRootCount branches

  /-- Forest form of the count of non-singleton descendant clusters. -/
  def forestNontrivialRootCount : PrimeIsingBondForest → ℝ
    | .nil => 0
    | .cons _ _ child tail => treeNontrivialRootCount child + forestNontrivialRootCount tail
end

mutual
  /-- Exact anisotropic mass summed over all possible subtree tops. -/
  def treeSubtreeMass : PrimeIsingTree → ℝ
    | .node _ branches => 1 - forestRootCutProduct branches + forestSubtreeMass branches

  /-- Forest form of the sum over possible subtree tops. -/
  def forestSubtreeMass : PrimeIsingForest → ℝ
    | .nil => 0
    | .cons _ child tail => treeSubtreeMass child + forestSubtreeMass tail
end

mutual
  /-- The paper's subtree-mass identity for the existing nonuniform FK tree family. -/
  theorem treeBondExpectation_nontrivialRootCount (T : PrimeIsingTree) :
      treeBondExpectation T treeNontrivialRootCount = treeSubtreeMass T := by
    cases T with
    | node p branches =>
        rw [treeBondExpectation_node]
        change forestBondExpectation branches (fun B =>
          1 - forestRootSingletonIndicator B + forestNontrivialRootCount B) = _
        rw [forestBondExpectation_add, forestBondExpectation_sub,
          forestBondExpectation_const, forestBondExpectation_rootSingleton,
          forestBondExpectation_nontrivialRootCount]
        rfl

  /-- Forest form of the exact subtree-mass identity. -/
  theorem forestBondExpectation_nontrivialRootCount (F : PrimeIsingForest) :
      forestBondExpectation F forestNontrivialRootCount = forestSubtreeMass F := by
    cases F with
    | nil => simp [forestBondExpectation, forestBondConfigurations,
        forestBondCoefficient, forestNontrivialRootCount, forestSubtreeMass]
    | cons c child tail =>
        rw [forestBondExpectation_cons]
        have hedge (x y : ℝ) : c.coefficient * (x + y) +
            (1 - c.coefficient) * (x + y) = x + y := by ring
        simp_rw [forestNontrivialRootCount, hedge, forestBondExpectation_add,
          forestBondExpectation_const, treeBondExpectation_add,
          treeBondExpectation_const, treeBondExpectation_nontrivialRootCount,
          forestBondExpectation_nontrivialRootCount]
        rfl
end

/-- Every root-isolation product is nonnegative. -/
theorem forestRootCutProduct_nonneg (F : PrimeIsingForest) :
    0 ≤ forestRootCutProduct F := by
  cases F with
  | nil => exact zero_le_one
  | cons c child tail =>
      exact mul_nonneg c.nonneg (forestRootCutProduct_nonneg tail)

mutual
  /-- The total nontrivial subtree mass never exceeds the number of vertices. -/
  theorem treeSubtreeMass_le_vertexCount (T : PrimeIsingTree) :
      treeSubtreeMass T ≤ primeIsingTreeVertexCount T := by
    cases T with
    | node p branches =>
        have hp := forestRootCutProduct_nonneg branches
        have hf := forestSubtreeMass_le_vertexCount branches
        simp only [treeSubtreeMass, primeIsingTreeVertexCount, Nat.cast_add, Nat.cast_one]
        linarith

  /-- Forest form of the vertex bound. -/
  theorem forestSubtreeMass_le_vertexCount (F : PrimeIsingForest) :
      forestSubtreeMass F ≤ primeIsingForestVertexCount F := by
    cases F with
    | nil => simp [forestSubtreeMass, primeIsingForestVertexCount]
    | cons c child tail =>
        simp only [forestSubtreeMass, primeIsingForestVertexCount, Nat.cast_add]
        exact add_le_add (treeSubtreeMass_le_vertexCount child)
          (forestSubtreeMass_le_vertexCount tail)
end

/-- Uniform control of descendant-cluster counts for every existing prime Ising tree. -/
theorem treeBondExpectation_nontrivialRootCount_le (T : PrimeIsingTree) :
    treeBondExpectation T treeNontrivialRootCount ≤ primeIsingTreeVertexCount T := by
  rw [treeBondExpectation_nontrivialRootCount]
  exact treeSubtreeMass_le_vertexCount T

end
end GaloisForLFunctions.RHTower
