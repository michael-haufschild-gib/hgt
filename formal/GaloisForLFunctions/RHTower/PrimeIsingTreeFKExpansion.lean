import GaloisForLFunctions.RHTower.IsingCavityRapidityAudioCascade

/-!
# Fortuin--Kasteleyn expansion of prime Ising trees

For a normalized ferromagnetic disagreement weight `c ∈ [0,1]`, the local edge factors have the
exact deletion--contraction decomposition

`(a + c b, c a + b) = c (a+b, a+b) + (1-c) (a,b)`.

The first term cuts the edge and sums the child spin independently.  The second opens a
synchronized bond and forces the child root spin to equal the parent spin.  This file enumerates
all cut/synchronized bond configurations of an arbitrary finite prime Ising tree and proves that
their nonnegative weighted sum is exactly the original conditional weights and partition.

This `[BRIDGE]` is directly useful to the source problem: arbitrary tree approximants are positive
Fortuin--Kasteleyn mixtures of synchronized prime clusters, rather than a new opaque function
class.  The theorem does not prove that the completed prime source belongs to this cone.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Whether an FK edge is cut or opened as a synchronized bond. -/
inductive IsingBondState where
  | cut
  | synchronized
  deriving DecidableEq

mutual
  /-- A bond-resolved tree configuration retaining the original prime labels. -/
  inductive PrimeIsingBondTree where
    | node (prime : Nat.Primes) (branches : PrimeIsingBondForest)

  /-- A bond-resolved forest retaining the original couplings and one FK state per edge. -/
  inductive PrimeIsingBondForest where
    | nil
    | cons (state : IsingBondState) (coupling : FerromagneticCoupling)
        (child : PrimeIsingBondTree) (tail : PrimeIsingBondForest)
end

mutual
  /-- All FK bond configurations of a finite tree. -/
  def treeBondConfigurations : PrimeIsingTree → List PrimeIsingBondTree
    | .node p branches =>
        (forestBondConfigurations branches).map (PrimeIsingBondTree.node p)

  /-- All independent cut/open choices in a finite forest. -/
  def forestBondConfigurations : PrimeIsingForest → List PrimeIsingBondForest
    | .nil => [.nil]
    | .cons c child tail =>
        (treeBondConfigurations child).flatMap fun childConfig =>
          (forestBondConfigurations tail).flatMap fun tailConfig =>
            [.cons .cut c childConfig tailConfig,
              .cons .synchronized c childConfig tailConfig]
end

mutual
  /-- FK coefficient of a tree configuration. -/
  def treeBondCoefficient : PrimeIsingBondTree → ℝ
    | .node _ branches => forestBondCoefficient branches

  /-- Product of `c` over cut edges and `1-c` over synchronized edges. -/
  def forestBondCoefficient : PrimeIsingBondForest → ℝ
    | .nil => 1
    | .cons state c child tail =>
        (match state with
          | .cut => c.coefficient
          | .synchronized => 1 - c.coefficient) *
            treeBondCoefficient child * forestBondCoefficient tail
end

mutual
  /-- Conditional weights of one fixed FK bond configuration. -/
  def bondTreeConditionalWeights
      (u : Nat.Primes → ℂ) : PrimeIsingBondTree → ℂ × ℂ
    | .node p branches =>
        let factors := bondForestConditionalFactors u branches
        (factors.1, u p * factors.2)

  /-- Forest factors of one fixed FK configuration.  A cut edge contributes the whole child
  partition to both parent spins; a synchronized edge retains the matching conditional weight. -/
  def bondForestConditionalFactors
      (u : Nat.Primes → ℂ) : PrimeIsingBondForest → ℂ × ℂ
    | .nil => (1, 1)
    | .cons state _ child tail =>
        let childWeights := bondTreeConditionalWeights u child
        let tailFactors := bondForestConditionalFactors u tail
        match state with
        | .cut =>
            ((childWeights.1 + childWeights.2) * tailFactors.1,
              (childWeights.1 + childWeights.2) * tailFactors.2)
        | .synchronized =>
            (childWeights.1 * tailFactors.1, childWeights.2 * tailFactors.2)
end

/-- Full partition of one fixed FK bond configuration. -/
def bondTreePartition (u : Nat.Primes → ℂ) (T : PrimeIsingBondTree) : ℂ :=
  (bondTreeConditionalWeights u T).1 + (bondTreeConditionalWeights u T).2

/-- The root connected-component field product together with the field products of every
detached connected component in one FK bond configuration. -/
structure BondClusterData where
  rootProduct : ℂ
  detachedProducts : List ℂ

mutual
  /-- Connected-component field products of a bond-resolved tree. -/
  def bondTreeClusterData
      (u : Nat.Primes → ℂ) : PrimeIsingBondTree → BondClusterData
    | .node p branches =>
        let data := bondForestClusterData u branches
        ⟨u p * data.rootProduct, data.detachedProducts⟩

  /-- Component data contributed by a forest relative to its fixed parent spin. -/
  def bondForestClusterData
      (u : Nat.Primes → ℂ) : PrimeIsingBondForest → BondClusterData
    | .nil => ⟨1, []⟩
    | .cons state _ child tail =>
        let childData := bondTreeClusterData u child
        let tailData := bondForestClusterData u tail
        match state with
        | .cut =>
            ⟨tailData.rootProduct,
              childData.rootProduct :: childData.detachedProducts ++
                tailData.detachedProducts⟩
        | .synchronized =>
            ⟨childData.rootProduct * tailData.rootProduct,
              childData.detachedProducts ++ tailData.detachedProducts⟩
end

/-- Product of the two-state partition blocks of all components detached from the root. -/
def BondClusterData.detachedPartition (data : BondClusterData) : ℂ :=
  (data.detachedProducts.map fun z => 1 + z).prod

mutual
  /-- A fixed FK tree configuration has one synchronized root component and independent
  synchronized detached components. -/
  theorem bondTreeConditionalWeights_eq_clusterData
      (u : Nat.Primes → ℂ) (T : PrimeIsingBondTree) :
      bondTreeConditionalWeights u T =
        let data := bondTreeClusterData u T
        (data.detachedPartition, data.rootProduct * data.detachedPartition) := by
    cases T with
    | node p branches =>
        rw [bondTreeConditionalWeights, bondTreeClusterData,
          bondForestConditionalFactors_eq_clusterData u branches]
        simp only [BondClusterData.detachedPartition]
        ext <;> ring

  /-- Forest form of the connected-component factorization. -/
  theorem bondForestConditionalFactors_eq_clusterData
      (u : Nat.Primes → ℂ) (F : PrimeIsingBondForest) :
      bondForestConditionalFactors u F =
        let data := bondForestClusterData u F
        (data.detachedPartition, data.rootProduct * data.detachedPartition) := by
    cases F with
    | nil =>
        simp [bondForestConditionalFactors, bondForestClusterData,
          BondClusterData.detachedPartition]
    | cons state c child tail =>
        have hchild := bondTreeConditionalWeights_eq_clusterData u child
        have htail := bondForestConditionalFactors_eq_clusterData u tail
        cases state with
        | cut =>
            simp only [bondForestConditionalFactors, bondForestClusterData]
            rw [hchild, htail]
            simp only [BondClusterData.detachedPartition, List.map_cons,
              List.map_append, List.prod_cons, List.prod_append]
            ext <;> ring
        | synchronized =>
            simp only [bondForestConditionalFactors, bondForestClusterData]
            rw [hchild, htail]
            simp only [BondClusterData.detachedPartition, List.map_append,
              List.prod_append]
            ext <;> ring
end

/-- Every fixed FK bond configuration factors exactly as the product of the synchronized
two-state blocks of its connected components. -/
theorem bondTreePartition_eq_clusterProduct
    (u : Nat.Primes → ℂ) (T : PrimeIsingBondTree) :
    bondTreePartition u T =
      let data := bondTreeClusterData u T
      (1 + data.rootProduct) * data.detachedPartition := by
  rw [bondTreePartition, bondTreeConditionalWeights_eq_clusterData]
  ring

/-- Real scaling of a pair of complex conditional weights. -/
private def scaleConditionalPair (r : ℝ) (w : ℂ × ℂ) : ℂ × ℂ :=
  ((r : ℂ) * w.1, (r : ℂ) * w.2)

/-- Weighted conditional pair of an FK tree configuration. -/
private def weightedBondTreeConditionalWeights
    (u : Nat.Primes → ℂ) (T : PrimeIsingBondTree) : ℂ × ℂ :=
  scaleConditionalPair (treeBondCoefficient T) (bondTreeConditionalWeights u T)

/-- Weighted forest pair of an FK forest configuration. -/
private def weightedBondForestConditionalFactors
    (u : Nat.Primes → ℂ) (F : PrimeIsingBondForest) : ℂ × ℂ :=
  scaleConditionalPair (forestBondCoefficient F) (bondForestConditionalFactors u F)

/-- The local FK deletion--contraction identity for arbitrary child conditional weights. -/
theorem isingEdgeFactors_eq_cut_add_synchronized
    (c : FerromagneticCoupling) (a b : ℂ) :
    (a + (c.coefficient : ℂ) * b, (c.coefficient : ℂ) * a + b) =
      ((c.coefficient : ℂ) * (a + b) + (1 - c.coefficient : ℝ) * a,
        (c.coefficient : ℂ) * (a + b) + (1 - c.coefficient : ℝ) * b) := by
  ext <;> push_cast <;> ring

/-- At one edge with independent fields, the interacting partition is the nonnegative mixture of
the cut independent-spin partition and the synchronized two-spin cluster. -/
theorem treePartition_singleEdge_fields_eq_fkMixture
    (p q : Nat.Primes) (c : FerromagneticCoupling) (u : Nat.Primes → ℂ) :
    treePartition u (singleEdgePrimeIsingTree p q c) =
      (c.coefficient : ℂ) * (1 + u p) * (1 + u q) +
        ((1 - c.coefficient : ℝ) : ℂ) * (1 + u p * u q) := by
  simp [treePartition, singleEdgePrimeIsingTree, treeConditionalWeights,
    forestConditionalFactors]
  ring

/-- Common-field form: every Lee--Yang pair block interpolates exactly between the independent
two-spin partition and the synchronized two-spin cluster. -/
theorem leeYangPairBlock_eq_fkMixture
    (c : FerromagneticCoupling) (z : ℂ) :
    leeYangPairBlock c.coefficient z =
      (c.coefficient : ℂ) * (1 + z) ^ 2 +
        ((1 - c.coefficient : ℝ) : ℂ) * (1 + z ^ 2) := by
  simp only [leeYangPairBlock]
  push_cast
  ring

mutual
  /-- Every FK tree coefficient is nonnegative. -/
  theorem treeBondCoefficient_nonneg (T : PrimeIsingBondTree) :
      0 ≤ treeBondCoefficient T := by
    cases T with
    | node _ branches => exact forestBondCoefficient_nonneg branches

  /-- Every FK forest coefficient is nonnegative. -/
  theorem forestBondCoefficient_nonneg (F : PrimeIsingBondForest) :
      0 ≤ forestBondCoefficient F := by
    cases F with
    | nil => simp [forestBondCoefficient]
    | cons state c child tail =>
        simp only [forestBondCoefficient]
        apply mul_nonneg (mul_nonneg ?_ (treeBondCoefficient_nonneg child))
          (forestBondCoefficient_nonneg tail)
        cases state with
        | cut => exact c.nonneg
        | synchronized => exact sub_nonneg.mpr c.le_one
end

private theorem sum_flatMap_map
    {α β M : Type*} [AddCommMonoid M]
    (xs : List α) (f : α → List β) (g : β → M) :
    ((xs.flatMap f).map g).sum =
      (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem list_sum_fst {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (xs : List (M × N)) : xs.sum.1 = (xs.map Prod.fst).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem list_sum_snd {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (xs : List (M × N)) : xs.sum.2 = (xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_flatMap_map_product
    {α β R : Type*} [CommSemiring R]
    (xs : List α) (ys : List β) (f : α → R) (g : β → R) :
    ((xs.flatMap fun x => ys.map fun y => f x * g y)).sum =
      (xs.map f).sum * (ys.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.sum_append, List.sum_map_mul_left, ih, add_mul]

private theorem sum_map_sum_map_product
    {α β R : Type*} [CommSemiring R]
    (xs : List α) (ys : List β) (f : α → R) (g : β → R) :
    (xs.map fun x => (ys.map fun y => f x * g y).sum).sum =
      (xs.map f).sum * (ys.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [List.sum_map_mul_left, ih]
      ring

private theorem sum_map_add
    {α M : Type*} [AddCommMonoid M] (xs : List α) (f g : α → M) :
    (xs.map f).sum + (xs.map g).sum = (xs.map fun x => f x + g x).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      abel

private theorem sum_map_congr
    {α M : Type*} [AddCommMonoid M] (xs : List α) (f g : α → M)
    (h : ∀ x ∈ xs, f x = g x) : (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem sum_flatMap_flatMap_map
    {α β γ M : Type*} [AddCommMonoid M]
    (xs : List α) (ys : List β) (h : α → β → List γ) (g : γ → M) :
    ((xs.flatMap fun x => ys.flatMap fun y => h x y).map g).sum =
      (xs.map fun x => (ys.map fun y => ((h x y).map g).sum).sum).sum := by
  rw [sum_flatMap_map]
  apply sum_map_congr
  intro x hx
  exact sum_flatMap_map ys (h x) g

mutual
  /-- FK coefficients of all bond configurations of a tree sum to one. -/
  theorem sum_treeBondCoefficient_treeBondConfigurations (T : PrimeIsingTree) :
      ((treeBondConfigurations T).map treeBondCoefficient).sum = 1 := by
    cases T with
    | node p branches =>
        rw [treeBondConfigurations, List.map_map]
        simpa [Function.comp_def, treeBondCoefficient] using
          sum_forestBondCoefficient_forestBondConfigurations branches

  /-- Forest form of normalization of the FK bond weights. -/
  theorem sum_forestBondCoefficient_forestBondConfigurations (F : PrimeIsingForest) :
      ((forestBondConfigurations F).map forestBondCoefficient).sum = 1 := by
    cases F with
    | nil => simp [forestBondConfigurations, forestBondCoefficient]
    | cons c child tail =>
        rw [forestBondConfigurations, sum_flatMap_flatMap_map]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          forestBondCoefficient]
        ring_nf
        rw [sum_map_sum_map_product,
          sum_treeBondCoefficient_treeBondConfigurations child,
          sum_forestBondCoefficient_forestBondConfigurations tail]
        norm_num
end

mutual
  /-- Exact arbitrary-tree FK expansion of both conditional weights. -/
  theorem treeConditionalWeights_eq_sum_bondConfigurations
      (u : Nat.Primes → ℂ) (T : PrimeIsingTree) :
      treeConditionalWeights u T =
        ((treeBondConfigurations T).map
          (weightedBondTreeConditionalWeights u)).sum := by
    cases T with
    | node p branches =>
        rw [treeConditionalWeights, treeBondConfigurations,
          List.map_map, forestConditionalFactors_eq_sum_bondConfigurations u branches]
        ext
        · rw [list_sum_fst, list_sum_fst]
          simp [Function.comp_def, weightedBondTreeConditionalWeights,
            scaleConditionalPair, bondTreeConditionalWeights,
            treeBondCoefficient, weightedBondForestConditionalFactors]
        · rw [list_sum_snd, list_sum_snd]
          simp only [List.map_map]
          calc
            u p * (List.map (fun F => (weightedBondForestConditionalFactors u F).2)
                (forestBondConfigurations branches)).sum =
                (List.map (fun F => u p *
                  (weightedBondForestConditionalFactors u F).2)
                  (forestBondConfigurations branches)).sum :=
              (List.sum_map_mul_left _ _ _).symm
            _ = (List.map
                (fun F => (weightedBondTreeConditionalWeights u
                  (PrimeIsingBondTree.node p F)).2)
                (forestBondConfigurations branches)).sum := by
              apply sum_map_congr
              intro F hF
              simp [weightedBondTreeConditionalWeights, scaleConditionalPair,
                weightedBondForestConditionalFactors]
              rw [treeBondCoefficient, bondTreeConditionalWeights]
              ring

  /-- Exact arbitrary-forest FK expansion of both conditional factors. -/
  theorem forestConditionalFactors_eq_sum_bondConfigurations
      (u : Nat.Primes → ℂ) (F : PrimeIsingForest) :
      forestConditionalFactors u F =
        ((forestBondConfigurations F).map
          (weightedBondForestConditionalFactors u)).sum := by
    cases F with
    | nil =>
        simp [forestConditionalFactors, forestBondConfigurations,
          weightedBondForestConditionalFactors, scaleConditionalPair,
          forestBondCoefficient, bondForestConditionalFactors]
    | cons c child tail =>
        rw [forestConditionalFactors, forestBondConfigurations]
        have hchild := treeConditionalWeights_eq_sum_bondConfigurations u child
        have htail := forestConditionalFactors_eq_sum_bondConfigurations u tail
        ext
        · rw [list_sum_fst, List.map_map, sum_flatMap_flatMap_map]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          simp only [Function.comp_apply, weightedBondForestConditionalFactors,
            scaleConditionalPair, forestBondCoefficient, bondForestConditionalFactors]
          push_cast
          ring_nf
          simp_rw [show ∀ x y,
              (c.coefficient : ℂ) * (treeBondCoefficient x : ℂ) *
                    (forestBondCoefficient y : ℂ) *
                    (bondTreeConditionalWeights u x).2 *
                    (bondForestConditionalFactors u y).1 +
                  (treeBondCoefficient x : ℂ) * (forestBondCoefficient y : ℂ) *
                    (bondTreeConditionalWeights u x).1 *
                    (bondForestConditionalFactors u y).1 =
                (((treeBondCoefficient x : ℂ) *
                    (bondTreeConditionalWeights u x).1) +
                  (c.coefficient : ℂ) * (treeBondCoefficient x : ℂ) *
                    (bondTreeConditionalWeights u x).2) *
                  ((forestBondCoefficient y : ℂ) *
                    (bondForestConditionalFactors u y).1) by
              intro x y
              ring]
          rw [sum_map_sum_map_product]
          have hchildFst := congrArg Prod.fst hchild
          have hchildSnd := congrArg Prod.snd hchild
          have htailFst := congrArg Prod.fst htail
          rw [list_sum_fst] at hchildFst htailFst
          rw [list_sum_snd] at hchildSnd
          have hchildFst' : (treeConditionalWeights u child).1 =
              ((treeBondConfigurations child).map fun x =>
                (treeBondCoefficient x : ℂ) *
                  (bondTreeConditionalWeights u x).1).sum := by
            simpa [Function.comp_def, weightedBondTreeConditionalWeights,
              scaleConditionalPair] using hchildFst
          have hchildSnd' : (treeConditionalWeights u child).2 =
              ((treeBondConfigurations child).map fun x =>
                (treeBondCoefficient x : ℂ) *
                  (bondTreeConditionalWeights u x).2).sum := by
            simpa [Function.comp_def, weightedBondTreeConditionalWeights,
              scaleConditionalPair] using hchildSnd
          have htailFst' : (forestConditionalFactors u tail).1 =
              ((forestBondConfigurations tail).map fun y =>
                (forestBondCoefficient y : ℂ) *
                  (bondForestConditionalFactors u y).1).sum := by
            simpa [Function.comp_def, weightedBondForestConditionalFactors,
              scaleConditionalPair] using htailFst
          have hfactor :
              ((treeBondConfigurations child).map fun x =>
                (treeBondCoefficient x : ℂ) *
                    (bondTreeConditionalWeights u x).1 +
                  (c.coefficient : ℂ) * (treeBondCoefficient x : ℂ) *
                    (bondTreeConditionalWeights u x).2).sum =
                (treeConditionalWeights u child).1 +
                  (c.coefficient : ℂ) * (treeConditionalWeights u child).2 := by
            calc
              _ = ((treeBondConfigurations child).map fun x =>
                    (treeBondCoefficient x : ℂ) *
                      (bondTreeConditionalWeights u x).1).sum +
                  ((treeBondConfigurations child).map fun x =>
                    (c.coefficient : ℂ) *
                      ((treeBondCoefficient x : ℂ) *
                        (bondTreeConditionalWeights u x).2)).sum :=
                by simpa only [mul_assoc] using (sum_map_add _ _ _).symm
              _ = ((treeBondConfigurations child).map fun x =>
                    (treeBondCoefficient x : ℂ) *
                      (bondTreeConditionalWeights u x).1).sum +
                  (c.coefficient : ℂ) *
                    ((treeBondConfigurations child).map fun x =>
                      (treeBondCoefficient x : ℂ) *
                        (bondTreeConditionalWeights u x).2).sum := by
                rw [List.sum_map_mul_left]
              _ = _ := by rw [← hchildFst', ← hchildSnd']
          rw [hfactor, ← htailFst']
          ring
        · rw [list_sum_snd, List.map_map, sum_flatMap_flatMap_map]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          simp only [Function.comp_apply, weightedBondForestConditionalFactors,
            scaleConditionalPair, forestBondCoefficient, bondForestConditionalFactors]
          push_cast
          ring_nf
          simp_rw [show ∀ x y,
              (c.coefficient : ℂ) * (treeBondCoefficient x : ℂ) *
                    (forestBondCoefficient y : ℂ) *
                    (bondTreeConditionalWeights u x).1 *
                    (bondForestConditionalFactors u y).2 +
                  (treeBondCoefficient x : ℂ) * (forestBondCoefficient y : ℂ) *
                    (bondTreeConditionalWeights u x).2 *
                    (bondForestConditionalFactors u y).2 =
                ((c.coefficient : ℂ) * (treeBondCoefficient x : ℂ) *
                    (bondTreeConditionalWeights u x).1 +
                  (treeBondCoefficient x : ℂ) *
                    (bondTreeConditionalWeights u x).2) *
                  ((forestBondCoefficient y : ℂ) *
                    (bondForestConditionalFactors u y).2) by
              intro x y
              ring]
          rw [sum_map_sum_map_product]
          have hchildFst := congrArg Prod.fst hchild
          have hchildSnd := congrArg Prod.snd hchild
          have htailSnd := congrArg Prod.snd htail
          rw [list_sum_fst] at hchildFst
          rw [list_sum_snd] at hchildSnd htailSnd
          have hchildFst' : (treeConditionalWeights u child).1 =
              ((treeBondConfigurations child).map fun x =>
                (treeBondCoefficient x : ℂ) *
                  (bondTreeConditionalWeights u x).1).sum := by
            simpa [Function.comp_def, weightedBondTreeConditionalWeights,
              scaleConditionalPair] using hchildFst
          have hchildSnd' : (treeConditionalWeights u child).2 =
              ((treeBondConfigurations child).map fun x =>
                (treeBondCoefficient x : ℂ) *
                  (bondTreeConditionalWeights u x).2).sum := by
            simpa [Function.comp_def, weightedBondTreeConditionalWeights,
              scaleConditionalPair] using hchildSnd
          have htailSnd' : (forestConditionalFactors u tail).2 =
              ((forestBondConfigurations tail).map fun y =>
                (forestBondCoefficient y : ℂ) *
                  (bondForestConditionalFactors u y).2).sum := by
            simpa [Function.comp_def, weightedBondForestConditionalFactors,
              scaleConditionalPair] using htailSnd
          have hfactor :
              ((treeBondConfigurations child).map fun x =>
                (c.coefficient : ℂ) * (treeBondCoefficient x : ℂ) *
                    (bondTreeConditionalWeights u x).1 +
                  (treeBondCoefficient x : ℂ) *
                    (bondTreeConditionalWeights u x).2).sum =
                (c.coefficient : ℂ) * (treeConditionalWeights u child).1 +
                  (treeConditionalWeights u child).2 := by
            calc
              _ = ((treeBondConfigurations child).map fun x =>
                    (c.coefficient : ℂ) *
                      ((treeBondCoefficient x : ℂ) *
                        (bondTreeConditionalWeights u x).1)).sum +
                  ((treeBondConfigurations child).map fun x =>
                    (treeBondCoefficient x : ℂ) *
                      (bondTreeConditionalWeights u x).2).sum :=
                by simpa only [mul_assoc] using (sum_map_add _ _ _).symm
              _ = (c.coefficient : ℂ) *
                    ((treeBondConfigurations child).map fun x =>
                      (treeBondCoefficient x : ℂ) *
                        (bondTreeConditionalWeights u x).1).sum +
                  ((treeBondConfigurations child).map fun x =>
                    (treeBondCoefficient x : ℂ) *
                      (bondTreeConditionalWeights u x).2).sum := by
                rw [List.sum_map_mul_left]
              _ = _ := by rw [← hchildFst', ← hchildSnd']
          rw [hfactor, ← htailSnd']
          ring
end

/-- **Positive FK expansion.**  The full Ising-tree partition is the finite sum over all bond
configurations, with coefficient `product(c_cut) product(1-c_open)`. -/
theorem treePartition_eq_sum_bondConfigurations
    (u : Nat.Primes → ℂ) (T : PrimeIsingTree) :
    treePartition u T =
      ((treeBondConfigurations T).map fun B =>
        (treeBondCoefficient B : ℂ) * bondTreePartition u B).sum := by
  rw [treePartition, treeConditionalWeights_eq_sum_bondConfigurations]
  rw [list_sum_fst, list_sum_snd]
  simp only [bondTreePartition, List.map_map]
  rw [sum_map_add]
  apply sum_map_congr
  intro B hB
  simp [weightedBondTreeConditionalWeights, scaleConditionalPair]
  ring

/-- Prime-field two-site consumer: an interacting edge is the positive interpolation between the
existing independent prime-spin partition and synchronized prime-cluster partition. -/
theorem primeIsingTreePartition_singleEdge_eq_fkMixture
    (p q : Nat.Primes) (hpq : p ≠ q) (c : FerromagneticCoupling) (z : ℂ) :
    primeIsingTreePartition (singleEdgePrimeIsingTree p q c) z =
      (c.coefficient : ℂ) *
          _root_.RHTower.independentPrimeLeeYangPartition {p, q} z +
        (((1 - c.coefficient : ℝ) : ℂ) *
          synchronizedPrimeClusterPartition {p, q} z) := by
  rw [primeIsingTreePartition, treePartition_singleEdge_fields_eq_fkMixture]
  simp [hpq, _root_.RHTower.independentPrimeLeeYangPartition,
    synchronizedPrimeClusterPartition, synchronizedPrimeClusterField]
  ring

end


end GaloisForLFunctions.RHTower
