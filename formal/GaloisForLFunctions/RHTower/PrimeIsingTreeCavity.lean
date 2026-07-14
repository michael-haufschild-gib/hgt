import GaloisForLFunctions.HTGeometry.CayleySchur
import GaloisForLFunctions.RHTower.PrimeWordSynchronizedCluster
import GaloisForLFunctions.RHTower.PrimeEulerFerromagneticInteraction
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

/-!
# Prime Ising trees from the ferromagnetic cavity map

For a normalized ferromagnetic disagreement weight `c ∈ [0,1]`, the exact Ising child-to-parent
cavity update is

`T_c(r) = (c + r) / (1 + c r)`.

This is literally the Blaschke factor from `HTGeometry.CayleySchur` with node `-c`.  Hence it
preserves the closed unit disk.  The strict factor at every prime-labelled vertex then keeps the
full rooted-tree cavity ratio in the open disk, while global spin inversion reduces the exterior
polydisk to the interior.

The resulting `[BRIDGE]` proves that every zero of every finite prime-labelled ferromagnetic Ising
tree lies on the centered critical line.  It also connects directly to existing corpus surfaces:
the one-edge constant-field tree is `leeYangPairBlock`, its prime-Euler specialization is
`primeEulerFerromagneticBlock`, and a zero-disagreement duplicate-free prime chain is
`synchronizedPrimeClusterPartition`.  No claim is made that the completed source is already a
limit of these trees.
-/

open Complex Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A normalized ferromagnetic disagreement weight `exp(-2J)` in the interval `[0,1]`. -/
structure FerromagneticCoupling where
  coefficient : ℝ
  nonneg : 0 ≤ coefficient
  le_one : coefficient ≤ 1

/-- The child-to-parent Ising cavity update. -/
def cavityTransfer (c : FerromagneticCoupling) (r : ℂ) : ℂ :=
  ((c.coefficient : ℂ) + r) / (1 + (c.coefficient : ℂ) * r)

/-- The cavity update is literally the `HTGeometry` Blaschke factor at the real node `-c`. -/
theorem cavityTransfer_eq_blaschkeFactor (c : FerromagneticCoupling) (r : ℂ) :
    cavityTransfer c r =
      (r - (-(c.coefficient : ℂ))) /
        (1 - (starRingEnd ℂ) (-(c.coefficient : ℂ)) * r) := by
  simp [cavityTransfer, add_comm]

/-- The exact local cavity gap identity.  Both disk factors are visible before division. -/
theorem normSq_cavityTransfer_gap (c : FerromagneticCoupling) (r : ℂ) :
    Complex.normSq (1 + (c.coefficient : ℂ) * r) -
        Complex.normSq ((c.coefficient : ℂ) + r) =
      (1 - c.coefficient ^ 2) * (1 - Complex.normSq r) := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- A cavity denominator cannot vanish when the incoming ratio is in the open disk. -/
theorem cavityTransfer_den_ne_zero (c : FerromagneticCoupling) {r : ℂ}
    (hr : ‖r‖ < 1) :
    1 + (c.coefficient : ℂ) * r ≠ 0 := by
  intro hzero
  have heq : (c.coefficient : ℂ) * r = -1 := by
    linear_combination hzero
  have hcNorm : ‖(c.coefficient : ℂ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg c.nonneg] using c.le_one
  have hlt : ‖(c.coefficient : ℂ) * r‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcNorm (norm_nonneg r))
      (by simpa using hr)
  rw [heq, norm_neg, norm_one] at hlt
  exact lt_irrefl 1 hlt

/-- The `HTGeometry` Blaschke theorem makes every ferromagnetic cavity update contractive. -/
theorem norm_cavityTransfer_le_one (c : FerromagneticCoupling) {r : ℂ}
    (hr : ‖r‖ < 1) :
    ‖cavityTransfer c r‖ ≤ 1 := by
  have hcNorm : ‖(-(c.coefficient : ℂ))‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg c.nonneg] using c.le_one
  have hden := cavityTransfer_den_ne_zero c hr
  have hschur := GaloisForLFunctions.blaschke_schur
    (-(c.coefficient : ℂ)) r hcNorm (le_of_lt hr) (by simpa using hden)
  simpa [cavityTransfer, add_comm] using hschur

mutual
  /-- A finite rooted prime-labelled Ising tree. -/
  inductive PrimeIsingTree where
    | node (prime : Nat.Primes) (branches : PrimeIsingForest)

  /-- A finite ordered forest of coupled child branches. -/
  inductive PrimeIsingForest where
    | nil
    | cons (coupling : FerromagneticCoupling)
        (child : PrimeIsingTree) (tail : PrimeIsingForest)
end

/-- Zero disagreement weight, the fully synchronized ferromagnetic limit. -/
def zeroFerromagneticCoupling : FerromagneticCoupling where
  coefficient := 0
  nonneg := le_rfl
  le_one := by norm_num

/-- Unit disagreement weight, equivalently zero physical interaction. -/
def unitFerromagneticCoupling : FerromagneticCoupling where
  coefficient := 1
  nonneg := by norm_num
  le_one := le_rfl

/-- The tree with one edge and two prime-labelled vertices. -/
def singleEdgePrimeIsingTree
    (p q : Nat.Primes) (c : FerromagneticCoupling) : PrimeIsingTree :=
  .node p (.cons c (.node q .nil) .nil)

/-- A prime word represented as a zero-disagreement chain. -/
def synchronizedPrimeChain : Nat.Primes → List Nat.Primes → PrimeIsingTree
  | p, [] => .node p .nil
  | p, q :: tail =>
      .node p (.cons zeroFerromagneticCoupling (synchronizedPrimeChain q tail) .nil)

/-- A prime word represented as a chain of physically decoupled edges. -/
def independentPrimeChain : Nat.Primes → List Nat.Primes → PrimeIsingTree
  | p, [] => .node p .nil
  | p, q :: tail =>
      .node p (.cons unitFerromagneticCoupling (independentPrimeChain q tail) .nil)

mutual
  /-- Conditional `(root plus, root minus)` partition weights. -/
  def treeConditionalWeights (u : Nat.Primes → ℂ) : PrimeIsingTree → ℂ × ℂ
    | .node p branches =>
        let factors := forestConditionalFactors u branches
        (factors.1, u p * factors.2)

  /-- Products of the plus- and minus-root edge factors over a forest. -/
  def forestConditionalFactors (u : Nat.Primes → ℂ) : PrimeIsingForest → ℂ × ℂ
    | .nil => (1, 1)
    | .cons c child tail =>
        let childWeights := treeConditionalWeights u child
        let tailFactors := forestConditionalFactors u tail
        ((childWeights.1 + (c.coefficient : ℂ) * childWeights.2) * tailFactors.1,
          ((c.coefficient : ℂ) * childWeights.1 + childWeights.2) * tailFactors.2)
end

/-- The full finite-tree Ising partition. -/
def treePartition (u : Nat.Primes → ℂ) (T : PrimeIsingTree) : ℂ :=
  (treeConditionalWeights u T).1 + (treeConditionalWeights u T).2

mutual
  /-- Product of all vertex fields in a tree. -/
  def treeFieldProduct (u : Nat.Primes → ℂ) : PrimeIsingTree → ℂ
    | .node p branches => u p * forestFieldProduct u branches

  /-- Product of all vertex fields in a forest. -/
  def forestFieldProduct (u : Nat.Primes → ℂ) : PrimeIsingForest → ℂ
    | .nil => 1
    | .cons _ child tail => treeFieldProduct u child * forestFieldProduct u tail
end

/-- The ratio of the two edge factors is the cavity transfer of the child ratio. -/
theorem ratio_edge_eq_cavityTransfer (c : FerromagneticCoupling) {a b : ℂ}
    (ha : a ≠ 0) (hden : a + (c.coefficient : ℂ) * b ≠ 0) :
    ((c.coefficient : ℂ) * a + b) / (a + (c.coefficient : ℂ) * b) =
      cavityTransfer c (b / a) := by
  rw [cavityTransfer]
  field_simp

private theorem ratio_product_eq {a b x y : ℂ} (ha : a ≠ 0) (hx : x ≠ 0) :
    (b * y) / (a * x) = (b / a) * (y / x) := by
  field_simp

mutual
  /-- The root-plus conditional weight is nonzero and the full tree cavity ratio is strictly
  inside the disk whenever every vertex field is strictly inside. -/
  theorem treeConditionalWeights_inside
      (u : Nat.Primes → ℂ) (hu : ∀ p, ‖u p‖ < 1) (T : PrimeIsingTree) :
      (treeConditionalWeights u T).1 ≠ 0 ∧
        ‖(treeConditionalWeights u T).2 / (treeConditionalWeights u T).1‖ < 1 := by
    cases T with
    | node p branches =>
        have hf := forestConditionalFactors_inside u hu branches
        constructor
        · exact hf.1
        · change ‖(u p * (forestConditionalFactors u branches).2) /
              (forestConditionalFactors u branches).1‖ < 1
          rw [div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv, norm_mul]
          calc
            ‖u p‖ * ‖(forestConditionalFactors u branches).2 /
                (forestConditionalFactors u branches).1‖ ≤ ‖u p‖ * 1 :=
              mul_le_mul_of_nonneg_left hf.2 (norm_nonneg _)
            _ < 1 := by simpa using hu p

  /-- The plus forest factor is nonzero and the forest ratio is in the closed disk. -/
  theorem forestConditionalFactors_inside
      (u : Nat.Primes → ℂ) (hu : ∀ p, ‖u p‖ < 1) (F : PrimeIsingForest) :
      (forestConditionalFactors u F).1 ≠ 0 ∧
        ‖(forestConditionalFactors u F).2 / (forestConditionalFactors u F).1‖ ≤ 1 := by
    cases F with
    | nil => simp [forestConditionalFactors]
    | cons c child tail =>
        have ht := treeConditionalWeights_inside u hu child
        have hf := forestConditionalFactors_inside u hu tail
        let a := (treeConditionalWeights u child).1
        let b := (treeConditionalWeights u child).2
        let x := (forestConditionalFactors u tail).1
        let y := (forestConditionalFactors u tail).2
        have ha : a ≠ 0 := ht.1
        have hdenTransfer := cavityTransfer_den_ne_zero c ht.2
        have hab : a + (c.coefficient : ℂ) * b ≠ 0 := by
          rw [show a + (c.coefficient : ℂ) * b =
            a * (1 + (c.coefficient : ℂ) * (b / a)) by field_simp [ha]]
          exact mul_ne_zero ha hdenTransfer
        constructor
        · change (a + (c.coefficient : ℂ) * b) * x ≠ 0
          exact mul_ne_zero hab hf.1
        · change ‖(((c.coefficient : ℂ) * a + b) * y) /
              ((a + (c.coefficient : ℂ) * b) * x)‖ ≤ 1
          rw [ratio_product_eq hab hf.1,
            ratio_edge_eq_cavityTransfer c ha hab, norm_mul]
          exact mul_le_one₀ (norm_cavityTransfer_le_one c ht.2)
            (norm_nonneg _) hf.2
end

/-- Open-polydisk fields make every finite ferromagnetic tree partition nonzero. -/
theorem treePartition_ne_zero_of_fields_inside
    (u : Nat.Primes → ℂ) (hu : ∀ p, ‖u p‖ < 1) (T : PrimeIsingTree) :
    treePartition u T ≠ 0 := by
  have h := treeConditionalWeights_inside u hu T
  rw [treePartition]
  intro hzero
  have hratio : (treeConditionalWeights u T).2 /
      (treeConditionalWeights u T).1 = -1 := by
    apply (div_eq_iff h.1).2
    rw [neg_mul]
    linear_combination hzero
  have hnorm : ‖(treeConditionalWeights u T).2 /
      (treeConditionalWeights u T).1‖ = 1 := by
    rw [hratio, norm_neg, norm_one]
  linarith [h.2]

mutual
  /-- Spin inversion swaps the two conditional tree weights after multiplication by all fields. -/
  theorem treeConditionalWeights_reciprocal
      (u : Nat.Primes → ℂ) (hu : ∀ p, u p ≠ 0) (T : PrimeIsingTree) :
      (treeConditionalWeights u T).1 =
          treeFieldProduct u T *
            (treeConditionalWeights (fun p => (u p)⁻¹) T).2 ∧
        (treeConditionalWeights u T).2 =
          treeFieldProduct u T *
            (treeConditionalWeights (fun p => (u p)⁻¹) T).1 := by
    cases T with
    | node p branches =>
        have hf := forestConditionalFactors_reciprocal u hu branches
        simp only [treeConditionalWeights, treeFieldProduct]
        constructor
        · rw [hf.1]
          field_simp [hu p]
        · rw [hf.2]
          ring

  /-- Spin inversion swaps the two conditional forest factors. -/
  theorem forestConditionalFactors_reciprocal
      (u : Nat.Primes → ℂ) (hu : ∀ p, u p ≠ 0) (F : PrimeIsingForest) :
      (forestConditionalFactors u F).1 =
          forestFieldProduct u F *
            (forestConditionalFactors (fun p => (u p)⁻¹) F).2 ∧
        (forestConditionalFactors u F).2 =
          forestFieldProduct u F *
            (forestConditionalFactors (fun p => (u p)⁻¹) F).1 := by
    cases F with
    | nil => simp [forestConditionalFactors, forestFieldProduct]
    | cons c child tail =>
        have ht := treeConditionalWeights_reciprocal u hu child
        have hf := forestConditionalFactors_reciprocal u hu tail
        simp only [forestConditionalFactors, forestFieldProduct]
        constructor
        · rw [ht.1, ht.2, hf.1]
          ring
        · rw [ht.1, ht.2, hf.2]
          ring
end

mutual
  theorem treeFieldProduct_ne_zero
      (u : Nat.Primes → ℂ) (hu : ∀ p, u p ≠ 0) (T : PrimeIsingTree) :
      treeFieldProduct u T ≠ 0 := by
    cases T with
    | node p branches =>
        exact mul_ne_zero (hu p) (forestFieldProduct_ne_zero u hu branches)

  theorem forestFieldProduct_ne_zero
      (u : Nat.Primes → ℂ) (hu : ∀ p, u p ≠ 0) (F : PrimeIsingForest) :
      forestFieldProduct u F ≠ 0 := by
    cases F with
    | nil => simp [forestFieldProduct]
    | cons _ child tail =>
        exact mul_ne_zero (treeFieldProduct_ne_zero u hu child)
          (forestFieldProduct_ne_zero u hu tail)
end

/-- Global spin inversion gives the exact reciprocal partition identity. -/
theorem treePartition_reciprocal
    (u : Nat.Primes → ℂ) (hu : ∀ p, u p ≠ 0) (T : PrimeIsingTree) :
    treePartition u T =
      treeFieldProduct u T * treePartition (fun p => (u p)⁻¹) T := by
  have h := treeConditionalWeights_reciprocal u hu T
  rw [treePartition, treePartition, h.1, h.2]
  ring

/-- The one-edge tree at a common field is exactly the existing quadratic Lee--Yang block. -/
theorem treePartition_singleEdge_constantField
    (p q : Nat.Primes) (c : FerromagneticCoupling) (v : ℂ) :
    treePartition (fun _ => v) (singleEdgePrimeIsingTree p q c) =
      leeYangPairBlock c.coefficient v := by
  simp [treePartition, singleEdgePrimeIsingTree, treeConditionalWeights,
    forestConditionalFactors, leeYangPairBlock]
  ring

/-- Conditional weights of the fully synchronized prime chain. -/
theorem treeConditionalWeights_synchronizedPrimeChain
    (u : Nat.Primes → ℂ) (p : Nat.Primes) (tail : List Nat.Primes) :
    treeConditionalWeights u (synchronizedPrimeChain p tail) =
      (1, u p * (tail.map u).prod) := by
  induction tail generalizing p with
  | nil => simp [synchronizedPrimeChain, treeConditionalWeights, forestConditionalFactors]
  | cons q tail ih =>
      rw [synchronizedPrimeChain, treeConditionalWeights, forestConditionalFactors, ih]
      ext <;> simp [forestConditionalFactors, zeroFerromagneticCoupling]

/-- Zero disagreement along a chain recovers its synchronized two-state partition. -/
theorem treePartition_synchronizedPrimeChain
    (u : Nat.Primes → ℂ) (p : Nat.Primes) (tail : List Nat.Primes) :
    treePartition u (synchronizedPrimeChain p tail) =
      1 + ((p :: tail).map u).prod := by
  rw [treePartition, treeConditionalWeights_synchronizedPrimeChain]
  simp

/-- Unit disagreement weight makes a connected tree presentation factor as independent spins. -/
theorem treePartition_independentPrimeChain
    (u : Nat.Primes → ℂ) (p : Nat.Primes) (tail : List Nat.Primes) :
    treePartition u (independentPrimeChain p tail) =
      ((p :: tail).map (fun q => 1 + u q)).prod := by
  induction tail generalizing p with
  | nil => simp [independentPrimeChain, treePartition, treeConditionalWeights,
      forestConditionalFactors]
  | cons q tail ih =>
      simp [independentPrimeChain, treePartition, treeConditionalWeights,
        forestConditionalFactors, unitFerromagneticCoupling]
      change treePartition u (independentPrimeChain q tail) +
          u p * treePartition u (independentPrimeChain q tail) =
        (1 + u p) * ((1 + u q) * (tail.map (fun r => 1 + u r)).prod)
      rw [ih q]
      simp only [List.map_cons, List.prod_cons]
      ring

/-- Prime-field specialization of the finite Ising-tree partition. -/
def primeIsingTreePartition (T : PrimeIsingTree) (z : ℂ) : ℂ :=
  treePartition (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T

/-- The physical Euler square-root amplitude packaged as a tree-edge coupling. -/
def primeEulerFerromagneticCoupling (p : Nat.Primes) : FerromagneticCoupling where
  coefficient := _root_.RHTower.primeEulerFerromagneticCoefficient p
  nonneg := (_root_.RHTower.primeEulerFerromagneticCoefficient_pos p).le
  le_one := _root_.RHTower.primeEulerFerromagneticCoefficient_le_one p

/-- The prior source-native two-spin block is the one-edge member of the tree model. -/
theorem primeIsingTreePartition_singleEdge_eq_primeEulerFerromagneticBlock
    (p : Nat.Primes) (z : ℂ) :
    primeIsingTreePartition
        (singleEdgePrimeIsingTree p p (primeEulerFerromagneticCoupling p)) z =
      _root_.RHTower.primeEulerFerromagneticBlock p z := by
  simp [primeIsingTreePartition, singleEdgePrimeIsingTree, treePartition,
    treeConditionalWeights, forestConditionalFactors, primeEulerFerromagneticCoupling,
    _root_.RHTower.primeEulerFerromagneticBlock, leeYangPairBlock]
  ring

/-- On a duplicate-free word, its synchronized chain is exactly the existing support cluster. -/
theorem primeIsingTreePartition_synchronizedPrimeChain_eq_cluster
    (p : Nat.Primes) (tail : List Nat.Primes) (hword : (p :: tail).Nodup) (z : ℂ) :
    primeIsingTreePartition (synchronizedPrimeChain p tail) z =
      synchronizedPrimeClusterPartition
        (GaloisForLFunctions.primeWordSupport (p :: tail)) z := by
  rw [primeIsingTreePartition, treePartition_synchronizedPrimeChain]
  rw [synchronizedPrimeClusterPartition, synchronizedPrimeClusterField]
  change 1 + (((p :: tail).map
      (fun q => _root_.RHTower.centeredPrimeLeeYangField q z)).prod) =
    1 + ∏ q ∈ (p :: tail).toFinset,
      _root_.RHTower.centeredPrimeLeeYangField q z
  congr 1
  exact (List.prod_toFinset
    (fun q => _root_.RHTower.centeredPrimeLeeYangField q z) hword).symm

/-- On a duplicate-free word, its unit-disagreement chain is the existing independent partition. -/
theorem primeIsingTreePartition_independentPrimeChain_eq_independent
    (p : Nat.Primes) (tail : List Nat.Primes) (hword : (p :: tail).Nodup) (z : ℂ) :
    primeIsingTreePartition (independentPrimeChain p tail) z =
      _root_.RHTower.independentPrimeLeeYangPartition
        (GaloisForLFunctions.primeWordSupport (p :: tail)) z := by
  rw [primeIsingTreePartition, treePartition_independentPrimeChain]
  rw [_root_.RHTower.independentPrimeLeeYangPartition]
  change (((p :: tail).map
      (fun q => 1 + _root_.RHTower.centeredPrimeLeeYangField q z)).prod) =
    ∏ q ∈ (p :: tail).toFinset,
      (1 + _root_.RHTower.centeredPrimeLeeYangField q z)
  exact (List.prod_toFinset
    (fun q => 1 + _root_.RHTower.centeredPrimeLeeYangField q z) hword).symm

/-- Every centered prime field is nonzero. -/
theorem centeredPrimeLeeYangField_ne_zero (p : Nat.Primes) (z : ℂ) :
    _root_.RHTower.centeredPrimeLeeYangField p z ≠ 0 := by
  rw [_root_.RHTower.centeredPrimeLeeYangField,
    _root_.RHTower.centeredPrimeMark]
  exact Complex.exp_ne_zero _

/-- Negating the centered spectral coordinate inverts every prime field. -/
theorem centeredPrimeLeeYangField_neg (p : Nat.Primes) (z : ℂ) :
    _root_.RHTower.centeredPrimeLeeYangField p (-z) =
      (_root_.RHTower.centeredPrimeLeeYangField p z)⁻¹ := by
  rw [_root_.RHTower.centeredPrimeLeeYangField,
    _root_.RHTower.centeredPrimeLeeYangField,
    _root_.RHTower.centeredPrimeMark,
    _root_.RHTower.centeredPrimeMark, ← Complex.exp_neg]
  congr 1
  ring

/-- Every centered prime field is entire in the centered spectral coordinate. -/
theorem differentiable_centeredPrimeLeeYangField (p : Nat.Primes) :
    Differentiable ℂ (_root_.RHTower.centeredPrimeLeeYangField p) := by
  unfold _root_.RHTower.centeredPrimeLeeYangField _root_.RHTower.centeredPrimeMark
  fun_prop

mutual
  /-- Conditional tree weights are entire whenever every input field is entire. -/
  theorem differentiable_treeConditionalWeights
      (u : Nat.Primes → ℂ → ℂ) (hu : ∀ p, Differentiable ℂ (u p))
      (T : PrimeIsingTree) :
      Differentiable ℂ (fun z => (treeConditionalWeights (fun p => u p z) T).1) ∧
        Differentiable ℂ (fun z => (treeConditionalWeights (fun p => u p z) T).2) := by
    cases T with
    | node p branches =>
        have hf := differentiable_forestConditionalFactors u hu branches
        simp only [treeConditionalWeights]
        constructor
        · exact hf.1
        · exact (hu p).mul hf.2

  /-- Conditional forest factors are entire whenever every input field is entire. -/
  theorem differentiable_forestConditionalFactors
      (u : Nat.Primes → ℂ → ℂ) (hu : ∀ p, Differentiable ℂ (u p))
      (F : PrimeIsingForest) :
      Differentiable ℂ (fun z => (forestConditionalFactors (fun p => u p z) F).1) ∧
        Differentiable ℂ (fun z => (forestConditionalFactors (fun p => u p z) F).2) := by
    cases F with
    | nil => simp [forestConditionalFactors]
    | cons c child tail =>
        have ht := differentiable_treeConditionalWeights u hu child
        have hf := differentiable_forestConditionalFactors u hu tail
        simp only [forestConditionalFactors]
        constructor
        · exact (ht.1.add ((differentiable_const _).mul ht.2)).mul hf.1
        · exact (((differentiable_const _).mul ht.1).add ht.2).mul hf.2
end

/-- Every finite prime-labelled tree partition is entire. -/
theorem differentiable_primeIsingTreePartition (T : PrimeIsingTree) :
    Differentiable ℂ (primeIsingTreePartition T) := by
  have h := differentiable_treeConditionalWeights
    (fun p => _root_.RHTower.centeredPrimeLeeYangField p)
    differentiable_centeredPrimeLeeYangField T
  change Differentiable ℂ (fun z =>
    (treeConditionalWeights
      (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T).1 +
    (treeConditionalWeights
      (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T).2)
  exact h.1.add h.2

/-- Prime-labelled trees are zero-free below the centered critical line. -/
theorem primeIsingTreePartition_ne_zero_of_im_lt_zero
    (T : PrimeIsingTree) {z : ℂ} (hz : z.im < 0) :
    primeIsingTreePartition T z ≠ 0 := by
  apply treePartition_ne_zero_of_fields_inside
  intro p
  exact (_root_.RHTower.norm_centeredPrimeLeeYangField_lt_one_iff p z).mpr hz

/-- Spin inversion makes prime-labelled trees zero-free above the centered critical line. -/
theorem primeIsingTreePartition_ne_zero_of_im_gt_zero
    (T : PrimeIsingTree) {z : ℂ} (hz : 0 < z.im) :
    primeIsingTreePartition T z ≠ 0 := by
  have hneg : primeIsingTreePartition T (-z) ≠ 0 := by
    apply primeIsingTreePartition_ne_zero_of_im_lt_zero
    simpa using neg_lt_zero.mpr hz
  have hrecip := treePartition_reciprocal
    (fun p => _root_.RHTower.centeredPrimeLeeYangField p z)
    (fun p => centeredPrimeLeeYangField_ne_zero p z) T
  have hinv : treePartition
      (fun p => (_root_.RHTower.centeredPrimeLeeYangField p z)⁻¹) T =
      primeIsingTreePartition T (-z) := by
    congr 2
    funext p
    exact (centeredPrimeLeeYangField_neg p z).symm
  rw [hinv] at hrecip
  rw [primeIsingTreePartition, hrecip]
  exact mul_ne_zero
    (treeFieldProduct_ne_zero _
      (fun p => centeredPrimeLeeYangField_ne_zero p z) T) hneg

/-- Every zero of every finite prime-labelled ferromagnetic Ising tree lies on the centered line. -/
theorem primeIsingTreePartition_zero_im
    (T : PrimeIsingTree) {z : ℂ} (hz : primeIsingTreePartition T z = 0) :
    z.im = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact primeIsingTreePartition_ne_zero_of_im_lt_zero T hneg hz
  · exact primeIsingTreePartition_ne_zero_of_im_gt_zero T hpos hz

/-- Direct tree-model capstone: locally uniform convergence of prime Ising trees to `XiC` proves
RH.  Entireness and real-zero localization are discharged by the tree theory. -/
theorem riemannHypothesis_of_primeIsingTreePartition_tendstoLocallyUniformly
    (T : ℕ → PrimeIsingTree)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n)) _root_.RHTower.XiC atTop) :
    RiemannHypothesis := by
  apply _root_.RHTower.riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants hconv
  · exact Filter.Eventually.of_forall (fun n => differentiable_primeIsingTreePartition (T n))
  · exact Filter.Eventually.of_forall (fun n z hz =>
      primeIsingTreePartition_zero_im (T n) hz)

/-- The route-facing capstone with a zero-free entire normalization: if prime Ising trees converge
locally uniformly to `E * XiC`, then RH follows.  Every finite zero-location and entireness
hypothesis is internal; only the source comparison and zero-free normalization remain. -/
theorem riemannHypothesis_of_primeIsingTreePartition_tendstoLocallyUniformly_mul_XiC
    (T : ℕ → PrimeIsingTree) (E : ℂ → ℂ)
    (hE : AnalyticOnNhd ℂ E Set.univ) (hEne : ∀ z, E z ≠ 0)
    (hconv : TendstoLocallyUniformly
      (fun n => primeIsingTreePartition (T n))
      (fun z => E z * _root_.RHTower.XiC z) atTop) :
    RiemannHypothesis := by
  rw [_root_.RHTower.rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  let z : ℂ := (ρ - 1 / 2) * (-I)
  have hXiC : _root_.RHTower.XiC z = 0 := by
    rw [_root_.RHTower.XiC]
    have harg : (1 : ℂ) / 2 + z * I = ρ := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have htargetAnalytic : AnalyticOnNhd ℂ
      (fun w => E w * _root_.RHTower.XiC w) Set.univ :=
    hE.mul _root_.RHTower.XiC_analytic
  have him : z.im = 0 := _root_.RHTower.zero_mem_closed_of_tendstoLocallyUniformly
    hconv htargetAnalytic
    (Filter.Eventually.of_forall (fun n => differentiable_primeIsingTreePartition (T n)))
    (isClosed_eq Complex.continuous_im continuous_const)
    (Filter.Eventually.of_forall (fun n w hw =>
      primeIsingTreePartition_zero_im (T n) hw))
    (mul_ne_zero (hEne 0) _root_.RHTower.XiC_zero_ne)
    (by rw [hXiC, mul_zero])
  have hzIm : z.im = 1 / 2 - ρ.re := by
    simp [z]
  have hre : ρ.re = 1 / 2 := by linarith [him, hzIm]
  exact (ne_of_gt (_root_.RHTower.mem_rightHalf.mp hρ)) hre

end


end GaloisForLFunctions.RHTower
