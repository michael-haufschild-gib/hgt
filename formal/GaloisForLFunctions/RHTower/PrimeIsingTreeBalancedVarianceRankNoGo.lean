import GaloisForLFunctions.RHTower.PrimeIsingTreeBalancedCentering
import GaloisForLFunctions.RHTower.PrimeIsingTreeFKExpansion
import GaloisForLFunctions.HTGeometry.FiniteSpectralHankelRank

/-!
# Variance and spectral-rank obstruction for balanced prime Ising trees

The positive Fortuin--Kasteleyn expansion of a finite ferromagnetic tree resolves each bond
configuration into independent synchronized clusters.  The centered spin observable of a cluster
has variance one quarter of the square of its total logarithmic prime mass.  Because all prime
logarithms are positive, merging clusters can only increase the sum of squared cluster masses.

This file starts the unconditional no-go for locally uniform approximation of the pointed Xi germ
by balanced finite prime Ising trees.  The first layer constructed here is the exact source-side
cluster geometry: every FK configuration has cluster-square mass at least the sum of the squared
prime logarithms of its vertices, hence at least one `(log 2)^2` unit per vertex.
-/

open Complex Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

mutual
  /-- Sum of squared logarithmic prime masses over the vertices of a tree. -/
  def treePrimeLeeYangSqMass : PrimeIsingTree → ℝ
    | .node p branches =>
        _root_.RHTower.primeLeeYangLog p ^ 2 + forestPrimeLeeYangSqMass branches

  /-- Forest form of the vertexwise squared prime mass. -/
  def forestPrimeLeeYangSqMass : PrimeIsingForest → ℝ
    | .nil => 0
    | .cons _ child tail =>
        treePrimeLeeYangSqMass child + forestPrimeLeeYangSqMass tail
end

mutual
  /-- Number of prime-labelled vertices in a tree. -/
  def primeIsingTreeVertexCount : PrimeIsingTree → ℕ
    | .node _ branches => 1 + primeIsingForestVertexCount branches

  /-- Number of vertices in all trees of a forest. -/
  def primeIsingForestVertexCount : PrimeIsingForest → ℕ
    | .nil => 0
    | .cons _ child tail =>
        primeIsingTreeVertexCount child + primeIsingForestVertexCount tail
end

mutual
  /-- Forget the cut/open state of every bond while retaining the underlying Ising tree. -/
  def PrimeIsingBondTree.eraseBondStates : PrimeIsingBondTree → PrimeIsingTree
    | .node p branches => .node p branches.eraseBondStates

  /-- Forest form of bond-state erasure. -/
  def PrimeIsingBondForest.eraseBondStates : PrimeIsingBondForest → PrimeIsingForest
    | .nil => .nil
    | .cons _ coupling child tail =>
        .cons coupling child.eraseBondStates tail.eraseBondStates
end

/-- Real cluster masses of one bond-resolved configuration.  `rootMass` is the component still
attached to the root; `detachedMasses` contains every component separated by a cut bond. -/
structure BondClusterMassData where
  rootMass : ℝ
  detachedMasses : List ℝ

mutual
  /-- Logarithmic prime masses of all clusters in a bond-resolved tree. -/
  def bondTreeClusterMassData : PrimeIsingBondTree → BondClusterMassData
    | .node p branches =>
        let data := bondForestClusterMassData branches
        ⟨_root_.RHTower.primeLeeYangLog p + data.rootMass, data.detachedMasses⟩

  /-- Cluster masses contributed by a forest relative to its parent component. -/
  def bondForestClusterMassData : PrimeIsingBondForest → BondClusterMassData
    | .nil => ⟨0, []⟩
    | .cons state _ child tail =>
        let childData := bondTreeClusterMassData child
        let tailData := bondForestClusterMassData tail
        match state with
        | .cut =>
            ⟨tailData.rootMass,
              childData.rootMass :: childData.detachedMasses ++
                tailData.detachedMasses⟩
        | .synchronized =>
            ⟨childData.rootMass + tailData.rootMass,
              childData.detachedMasses ++ tailData.detachedMasses⟩
end

/-- Total squared cluster mass. -/
def BondClusterMassData.sqMass (data : BondClusterMassData) : ℝ :=
  data.rootMass ^ 2 + (data.detachedMasses.map fun m => m ^ 2).sum

/-- All cluster masses, with the root component first. -/
def BondClusterMassData.allMasses (data : BondClusterMassData) : List ℝ :=
  data.rootMass :: data.detachedMasses

/-- Centered characteristic factor of one synchronized cluster. -/
def centeredClusterFactor (mass : ℝ) (z : ℂ) : ℂ :=
  Complex.cos ((mass : ℂ) / 2 * z)

/-- Product of the centered characteristic factors of independent FK clusters. -/
def centeredClusterProduct : List ℝ → ℂ → ℂ
  | [], _ => 1
  | mass :: tail, z => centeredClusterFactor mass z * centeredClusterProduct tail z

/-- Uncentered two-state cluster product. -/
def uncenteredClusterProduct (masses : List ℝ) (z : ℂ) : ℂ :=
  (masses.map fun mass =>
    1 + Complex.exp (-((mass : ℝ) : ℂ) * I * z)).prod

/-- One-cluster half-mass centering identity. -/
theorem exp_halfMass_mul_one_add_exp_neg_eq_two_mul_centeredClusterFactor
    (mass : ℝ) (z : ℂ) :
    Complex.exp ((mass : ℂ) * I * z / 2) *
        (1 + Complex.exp (-(mass : ℂ) * I * z)) =
      2 * centeredClusterFactor mass z := by
  unfold centeredClusterFactor
  rw [Complex.cos, mul_add, mul_one, ← Complex.exp_add]
  have hplus : (mass : ℂ) * I * z / 2 = (mass : ℂ) / 2 * z * I := by ring
  rw [hplus]
  have hminus : (mass : ℂ) / 2 * z * I + -(mass : ℂ) * I * z =
      -((mass : ℂ) / 2 * z) * I := by ring
  rw [hminus]
  ring

/-- Simultaneous half-mass centering turns independent synchronized cluster blocks into their
centered cosine product. -/
theorem exp_halfTotalMass_mul_uncenteredClusterProduct
    (masses : List ℝ) (z : ℂ) :
    Complex.exp ((((masses.sum : ℝ) : ℂ) * I * z) / 2) *
        uncenteredClusterProduct masses z =
      (2 : ℂ) ^ masses.length * centeredClusterProduct masses z := by
  induction masses with
  | nil => simp [uncenteredClusterProduct, centeredClusterProduct]
  | cons mass tail ih =>
      simp only [List.sum_cons, List.length_cons, uncenteredClusterProduct,
        List.map_cons, List.prod_cons, centeredClusterProduct, pow_succ]
      rw [show ((((mass + tail.sum : ℝ) : ℂ) * I * z) / 2) =
          (mass : ℂ) * I * z / 2 + (((tail.sum : ℝ) : ℂ) * I * z) / 2 by
        push_cast
        ring, Complex.exp_add]
      rw [show Complex.exp ((mass : ℂ) * I * z / 2) *
            Complex.exp (((tail.sum : ℝ) : ℂ) * I * z / 2) *
              ((1 + Complex.exp (-(mass : ℂ) * I * z)) *
                (List.map
                  (fun m => 1 + Complex.exp (-((m : ℝ) : ℂ) * I * z)) tail).prod) =
          (Complex.exp ((mass : ℂ) * I * z / 2) *
              (1 + Complex.exp (-(mass : ℂ) * I * z))) *
            (Complex.exp (((tail.sum : ℝ) : ℂ) * I * z / 2) *
              uncenteredClusterProduct tail z) by
        unfold uncenteredClusterProduct
        ring]
      rw [exp_halfMass_mul_one_add_exp_neg_eq_two_mul_centeredClusterFactor, ih]
      ring

theorem differentiable_centeredClusterFactor (mass : ℝ) :
    Differentiable ℂ (centeredClusterFactor mass) := by
  unfold centeredClusterFactor
  fun_prop

theorem differentiable_centeredClusterProduct (masses : List ℝ) :
    Differentiable ℂ (centeredClusterProduct masses) := by
  induction masses with
  | nil => simp [centeredClusterProduct]
  | cons mass tail ih =>
      simp only [centeredClusterProduct]
      exact (differentiable_centeredClusterFactor mass).mul ih

@[simp] theorem centeredClusterFactor_zero (mass : ℝ) :
    centeredClusterFactor mass 0 = 1 := by
  simp [centeredClusterFactor]

@[simp] theorem centeredClusterProduct_zero (masses : List ℝ) :
    centeredClusterProduct masses 0 = 1 := by
  induction masses with
  | nil => simp [centeredClusterProduct]
  | cons mass tail ih => simp [centeredClusterProduct, ih]

theorem iteratedDeriv_one_centeredClusterFactor_zero (mass : ℝ) :
    iteratedDeriv 1 (centeredClusterFactor mass) 0 = 0 := by
  unfold centeredClusterFactor
  rw [iteratedDeriv_comp_const_mul Complex.contDiff_cos ((mass : ℂ) / 2)]
  dsimp
  simp only [mul_zero]
  have h : iteratedDeriv 1 Complex.cos 0 = 0 := by simp
  rw [h, mul_zero]

theorem iteratedDeriv_two_centeredClusterFactor_zero (mass : ℝ) :
    iteratedDeriv 2 (centeredClusterFactor mass) 0 = -((mass : ℂ) ^ 2) / 4 := by
  unfold centeredClusterFactor
  rw [iteratedDeriv_comp_const_mul Complex.contDiff_cos ((mass : ℂ) / 2)]
  dsimp
  simp only [mul_zero]
  have h : iteratedDeriv 2 Complex.cos 0 = -1 := by
    simpa using congrFun (Complex.iteratedDeriv_even_cos 1) 0
  rw [h]
  ring

theorem iteratedDeriv_one_centeredClusterProduct_zero (masses : List ℝ) :
    iteratedDeriv 1 (centeredClusterProduct masses) 0 = 0 := by
  induction masses with
  | nil => simp [centeredClusterProduct]
  | cons mass tail ih =>
      rw [show centeredClusterProduct (mass :: tail) =
          centeredClusterFactor mass * centeredClusterProduct tail by rfl]
      rw [iteratedDeriv_mul (n := 1) (x := (0 : ℂ))
        (differentiable_centeredClusterFactor mass).contDiff.contDiffAt
        (differentiable_centeredClusterProduct tail).contDiff.contDiffAt]
      norm_num [Finset.sum_range_succ, iteratedDeriv_zero,
        iteratedDeriv_one_centeredClusterFactor_zero, ih]

/-- The second central jet of an independent cluster packet is minus one quarter of its total
squared cluster mass. -/
theorem iteratedDeriv_two_centeredClusterProduct_zero (masses : List ℝ) :
    iteratedDeriv 2 (centeredClusterProduct masses) 0 =
      -(((masses.map fun mass => mass ^ 2).sum : ℝ) : ℂ) / 4 := by
  induction masses with
  | nil =>
      simp only [centeredClusterProduct]
      rw [iteratedDeriv_const]
      simp
  | cons mass tail ih =>
      rw [show centeredClusterProduct (mass :: tail) =
          centeredClusterFactor mass * centeredClusterProduct tail by rfl]
      rw [iteratedDeriv_mul (n := 2) (x := (0 : ℂ))
        (differentiable_centeredClusterFactor mass).contDiff.contDiffAt
        (differentiable_centeredClusterProduct tail).contDiff.contDiffAt]
      norm_num [Finset.sum_range_succ, iteratedDeriv_zero,
        iteratedDeriv_two_centeredClusterFactor_zero,
        iteratedDeriv_one_centeredClusterFactor_zero,
        iteratedDeriv_one_centeredClusterProduct_zero, ih]
      push_cast
      ring

mutual
  /-- The root cluster of every bond tree has nonnegative mass. -/
  theorem bondTreeClusterMassData_rootMass_nonneg (T : PrimeIsingBondTree) :
      0 ≤ (bondTreeClusterMassData T).rootMass := by
    cases T with
    | node p branches =>
        simp only [bondTreeClusterMassData]
        exact add_nonneg (_root_.RHTower.primeLeeYangLog_pos p).le
          (bondForestClusterMassData_rootMass_nonneg branches)

  /-- The forest component still joined to its parent has nonnegative mass. -/
  theorem bondForestClusterMassData_rootMass_nonneg (F : PrimeIsingBondForest) :
      0 ≤ (bondForestClusterMassData F).rootMass := by
    cases F with
    | nil => simp [bondForestClusterMassData]
    | cons state coupling child tail =>
        cases state with
        | cut =>
            simpa [bondForestClusterMassData] using
              bondForestClusterMassData_rootMass_nonneg tail
        | synchronized =>
            simp only [bondForestClusterMassData]
            exact add_nonneg (bondTreeClusterMassData_rootMass_nonneg child)
              (bondForestClusterMassData_rootMass_nonneg tail)
end

mutual
  /-- The complex field-product cluster data are exactly the exponentials of the real cluster
  masses. -/
  theorem bondTreeClusterData_centered_eq_massData
      (T : PrimeIsingBondTree) (z : ℂ) :
      bondTreeClusterData
          (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T =
        let massData := bondTreeClusterMassData T
        ⟨Complex.exp (-(massData.rootMass : ℂ) * I * z),
          massData.detachedMasses.map fun mass : ℝ =>
            Complex.exp (-(mass : ℂ) * I * z)⟩ := by
    cases T with
    | node p branches =>
        rw [bondTreeClusterData, bondTreeClusterMassData,
          bondForestClusterData_centered_eq_massData branches z,
          centeredPrimeLeeYangField_eq_massExp]
        simp only
        congr 1
        · rw [← Complex.exp_add]
          congr 1
          push_cast
          ring

  /-- Forest form of the exponential cluster-mass identification. -/
  theorem bondForestClusterData_centered_eq_massData
      (F : PrimeIsingBondForest) (z : ℂ) :
      bondForestClusterData
          (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) F =
        let massData := bondForestClusterMassData F
        ⟨Complex.exp (-(massData.rootMass : ℂ) * I * z),
          massData.detachedMasses.map fun mass : ℝ =>
            Complex.exp (-(mass : ℂ) * I * z)⟩ := by
    cases F with
    | nil => simp [bondForestClusterData, bondForestClusterMassData]
    | cons state coupling child tail =>
        cases state with
        | cut =>
            rw [bondForestClusterData, bondForestClusterMassData,
              bondTreeClusterData_centered_eq_massData child z,
              bondForestClusterData_centered_eq_massData tail z]
            simp
        | synchronized =>
            rw [bondForestClusterData, bondForestClusterMassData,
              bondTreeClusterData_centered_eq_massData child z,
              bondForestClusterData_centered_eq_massData tail z]
            simp only [List.map_append]
            congr 1
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
end

/-- A fixed FK bond partition is the uncentered product of the two-state blocks of its real
cluster masses. -/
theorem bondTreePartition_centered_eq_uncenteredClusterProduct
    (T : PrimeIsingBondTree) (z : ℂ) :
    bondTreePartition
        (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T =
      uncenteredClusterProduct (bondTreeClusterMassData T).allMasses z := by
  rw [bondTreePartition_eq_clusterProduct,
    bondTreeClusterData_centered_eq_massData]
  simp only [BondClusterData.detachedPartition, BondClusterMassData.allMasses,
    uncenteredClusterProduct, List.map_cons, List.prod_cons, List.map_map]
  congr 1

/-- The total cluster mass is the total prime mass of the bond-resolved tree. -/
def bondTreePrimeLeeYangMass (T : PrimeIsingBondTree) : ℝ :=
  treePrimeLeeYangMass T.eraseBondStates

/-- Total prime mass of a bond-resolved forest after forgetting the bond states. -/
def bondForestPrimeLeeYangMass (F : PrimeIsingBondForest) : ℝ :=
  forestPrimeLeeYangMass F.eraseBondStates

mutual
  /-- Cluster masses partition the vertex masses of a bond-resolved tree. -/
  theorem sum_allMasses_bondTreeClusterMassData (T : PrimeIsingBondTree) :
      (bondTreeClusterMassData T).allMasses.sum = bondTreePrimeLeeYangMass T := by
    cases T with
    | node p branches =>
        simp only [BondClusterMassData.allMasses, bondTreeClusterMassData,
          List.sum_cons, bondTreePrimeLeeYangMass, PrimeIsingBondTree.eraseBondStates,
          treePrimeLeeYangMass]
        have hforest := sum_allMasses_bondForestClusterMassData branches
        simp only [BondClusterMassData.allMasses, List.sum_cons,
          bondForestPrimeLeeYangMass] at hforest
        linarith

  /-- Forest form of additivity of the FK cluster masses. -/
  theorem sum_allMasses_bondForestClusterMassData (F : PrimeIsingBondForest) :
      (bondForestClusterMassData F).allMasses.sum = bondForestPrimeLeeYangMass F := by
    cases F with
    | nil =>
        simp [BondClusterMassData.allMasses, bondForestClusterMassData,
          bondForestPrimeLeeYangMass, PrimeIsingBondForest.eraseBondStates,
          forestPrimeLeeYangMass]
    | cons state coupling child tail =>
        have hchild := sum_allMasses_bondTreeClusterMassData child
        have htail := sum_allMasses_bondForestClusterMassData tail
        simp only [BondClusterMassData.allMasses, List.sum_cons,
          bondTreePrimeLeeYangMass] at hchild
        simp only [BondClusterMassData.allMasses, List.sum_cons,
          bondForestPrimeLeeYangMass] at htail
        cases state with
        | cut =>
            simp only [BondClusterMassData.allMasses, bondForestClusterMassData,
              List.sum_cons, List.sum_append, bondForestPrimeLeeYangMass,
              PrimeIsingBondForest.eraseBondStates, forestPrimeLeeYangMass]
            linarith
        | synchronized =>
            simp only [BondClusterMassData.allMasses, bondForestClusterMassData,
              List.sum_cons, List.sum_append, bondForestPrimeLeeYangMass,
              PrimeIsingBondForest.eraseBondStates, forestPrimeLeeYangMass]
            linarith
end

/-- The half-mass centered partition of one fixed FK bond configuration. -/
def centeredBondTreePartition (T : PrimeIsingBondTree) (z : ℂ) : ℂ :=
  Complex.exp (((bondTreePrimeLeeYangMass T : ℝ) : ℂ) * I * z / 2) *
    bondTreePartition
      (fun p => _root_.RHTower.centeredPrimeLeeYangField p z) T

/-- A centered FK configuration is a power of two times the product of its centered cluster
characteristic factors. -/
theorem centeredBondTreePartition_eq_clusterProduct (T : PrimeIsingBondTree) :
    centeredBondTreePartition T = fun z =>
      (2 : ℂ) ^ (bondTreeClusterMassData T).allMasses.length *
        centeredClusterProduct (bondTreeClusterMassData T).allMasses z := by
  funext z
  rw [centeredBondTreePartition,
    bondTreePartition_centered_eq_uncenteredClusterProduct]
  rw [← sum_allMasses_bondTreeClusterMassData T]
  exact exp_halfTotalMass_mul_uncenteredClusterProduct
    (bondTreeClusterMassData T).allMasses z

/-- Exact second central jet of one FK configuration. -/
theorem iteratedDeriv_two_centeredBondTreePartition_zero
    (T : PrimeIsingBondTree) :
    iteratedDeriv 2 (centeredBondTreePartition T) 0 =
      -((2 : ℂ) ^ (bondTreeClusterMassData T).allMasses.length *
          (((bondTreeClusterMassData T).sqMass : ℝ) : ℂ)) / 4 := by
  rw [centeredBondTreePartition_eq_clusterProduct]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_two_centeredClusterProduct_zero]
  simp only [BondClusterMassData.allMasses, List.map_cons, List.sum_cons,
    BondClusterMassData.sqMass]
  push_cast
  ring

mutual
  /-- Merging positive-mass FK components can only increase the total square mass. -/
  theorem treePrimeLeeYangSqMass_erase_le_clusterSqMass (T : PrimeIsingBondTree) :
      treePrimeLeeYangSqMass T.eraseBondStates ≤
        (bondTreeClusterMassData T).sqMass := by
    cases T with
    | node p branches =>
        have hforest :=
          forestPrimeLeeYangSqMass_erase_le_clusterSqMass branches
        have hroot := bondForestClusterMassData_rootMass_nonneg branches
        have hp := (_root_.RHTower.primeLeeYangLog_pos p).le
        simp only [PrimeIsingBondTree.eraseBondStates, treePrimeLeeYangSqMass,
          bondTreeClusterMassData, BondClusterMassData.sqMass] at hforest ⊢
        nlinarith

  /-- Forest form of the FK cluster-square floor. -/
  theorem forestPrimeLeeYangSqMass_erase_le_clusterSqMass
      (F : PrimeIsingBondForest) :
      forestPrimeLeeYangSqMass F.eraseBondStates ≤
        (bondForestClusterMassData F).sqMass := by
    cases F with
    | nil => simp [PrimeIsingBondForest.eraseBondStates,
        forestPrimeLeeYangSqMass, bondForestClusterMassData,
        BondClusterMassData.sqMass]
    | cons state coupling child tail =>
        have hchild := treePrimeLeeYangSqMass_erase_le_clusterSqMass child
        have htail := forestPrimeLeeYangSqMass_erase_le_clusterSqMass tail
        cases state with
        | cut =>
            simp only [PrimeIsingBondForest.eraseBondStates,
              forestPrimeLeeYangSqMass, bondForestClusterMassData,
              BondClusterMassData.sqMass, List.map_cons, List.map_append,
              List.sum_cons, List.sum_append] at hchild htail ⊢
            linarith
        | synchronized =>
            have hchildRoot := bondTreeClusterMassData_rootMass_nonneg child
            have htailRoot := bondForestClusterMassData_rootMass_nonneg tail
            simp only [PrimeIsingBondForest.eraseBondStates,
              forestPrimeLeeYangSqMass, bondForestClusterMassData,
              BondClusterMassData.sqMass, List.map_append,
              List.sum_append] at hchild htail ⊢
            nlinarith
end

mutual
  /-- Erasing any enumerated bond configuration recovers its original tree. -/
  theorem eraseBondStates_eq_of_mem_treeBondConfigurations
      (T : PrimeIsingTree) {B : PrimeIsingBondTree}
      (hB : B ∈ treeBondConfigurations T) :
      B.eraseBondStates = T := by
    cases T with
    | node p branches =>
        simp only [treeBondConfigurations, List.mem_map] at hB
        obtain ⟨bondBranches, hmem, rfl⟩ := hB
        simp only [PrimeIsingBondTree.eraseBondStates]
        rw [eraseBondStates_eq_of_mem_forestBondConfigurations branches hmem]

  /-- Forest form of erasure for an enumerated bond configuration. -/
  theorem eraseBondStates_eq_of_mem_forestBondConfigurations
      (F : PrimeIsingForest) {B : PrimeIsingBondForest}
      (hB : B ∈ forestBondConfigurations F) :
      B.eraseBondStates = F := by
    cases F with
    | nil =>
        simp only [forestBondConfigurations, List.mem_singleton] at hB
        subst B
        rfl
    | cons coupling child tail =>
        simp only [forestBondConfigurations, List.mem_flatMap] at hB
        obtain ⟨bondChild, hchild, hB⟩ := hB
        obtain ⟨bondTail, htail, hB⟩ := hB
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
        rcases hB with rfl | rfl
        · simp only [PrimeIsingBondForest.eraseBondStates]
          rw [eraseBondStates_eq_of_mem_treeBondConfigurations child hchild,
            eraseBondStates_eq_of_mem_forestBondConfigurations tail htail]
        · simp only [PrimeIsingBondForest.eraseBondStates]
          rw [eraseBondStates_eq_of_mem_treeBondConfigurations child hchild,
            eraseBondStates_eq_of_mem_forestBondConfigurations tail htail]
end

/-- Every enumerated FK configuration has cluster-square mass at least the vertexwise squared
prime mass of the original tree. -/
theorem treePrimeLeeYangSqMass_le_bondConfiguration_clusterSqMass
    (T : PrimeIsingTree) {B : PrimeIsingBondTree}
    (hB : B ∈ treeBondConfigurations T) :
    treePrimeLeeYangSqMass T ≤ (bondTreeClusterMassData B).sqMass := by
  rw [← eraseBondStates_eq_of_mem_treeBondConfigurations T hB]
  exact treePrimeLeeYangSqMass_erase_le_clusterSqMass B

mutual
  /-- One `(log 2)^2` floor per prime-labelled vertex. -/
  theorem vertexCount_mul_logTwo_sq_le_treePrimeLeeYangSqMass
      (T : PrimeIsingTree) :
      (primeIsingTreeVertexCount T : ℝ) * Real.log 2 ^ 2 ≤
        treePrimeLeeYangSqMass T := by
    cases T with
    | node p branches =>
        have hforest :=
          vertexCount_mul_logTwo_sq_le_forestPrimeLeeYangSqMass branches
        have hp := log_two_le_primeLeeYangLog p
        have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
        have hpSq : Real.log 2 ^ 2 ≤ _root_.RHTower.primeLeeYangLog p ^ 2 := by
          nlinarith
        simp only [primeIsingTreeVertexCount, treePrimeLeeYangSqMass]
        push_cast
        nlinarith

  /-- Forest form of the per-vertex square-mass floor. -/
  theorem vertexCount_mul_logTwo_sq_le_forestPrimeLeeYangSqMass
      (F : PrimeIsingForest) :
      (primeIsingForestVertexCount F : ℝ) * Real.log 2 ^ 2 ≤
        forestPrimeLeeYangSqMass F := by
    cases F with
    | nil => simp [primeIsingForestVertexCount, forestPrimeLeeYangSqMass]
    | cons coupling child tail =>
        have hchild := vertexCount_mul_logTwo_sq_le_treePrimeLeeYangSqMass child
        have htail := vertexCount_mul_logTwo_sq_le_forestPrimeLeeYangSqMass tail
        simp only [primeIsingForestVertexCount, forestPrimeLeeYangSqMass]
        push_cast
        nlinarith
end

/-- **Source-pure FK variance floor.**  Every bond configuration carries at least one squared
`log 2` unit of cluster mass per original vertex.  After the centered independent cluster signs
are introduced, division by four gives the corresponding spin-variance floor. -/
theorem vertexCount_mul_logTwo_sq_le_bondConfiguration_clusterSqMass
    (T : PrimeIsingTree) {B : PrimeIsingBondTree}
    (hB : B ∈ treeBondConfigurations T) :
    (primeIsingTreeVertexCount T : ℝ) * Real.log 2 ^ 2 ≤
      (bondTreeClusterMassData B).sqMass :=
  (vertexCount_mul_logTwo_sq_le_treePrimeLeeYangSqMass T).trans
    (treePrimeLeeYangSqMass_le_bondConfiguration_clusterSqMass T hB)

end

end GaloisForLFunctions.RHTower
