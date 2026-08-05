import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalSingletEdgeCasimirBridge
import GaloisForLFunctions.HTGeometry.VisibleKernelRecoveryHallExpansion
import GaloisForLFunctions.QuantumAlg.Util.HilbertSchmidt

/-!
# Positive graph edge-Casimir recovery

The common-kernel classification of separate physical edge Casimirs does not
by itself control their sum. This file supplies the missing noncancellation:
Hermitian commutators are self-adjoint in Hilbert--Schmidt geometry, so the
graph sum of their squares has an exact sum-of-squared-residuals energy.

On the product-Clifford singlet sector of every finite connected qubit graph,
the graph-summed operator therefore has exactly global identity and global
replica swap as zero modes. Its summands remain literal weight-two collective
Pauli double commutators and land in the ordinary q-local family shadow.
-/

open scoped BigOperators Matrix Kronecker InnerProductSpace
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg

/-- Hilbert realization of a finite square matrix by flattening both indices. -/
abbrev FiniteMatrixHilbert (n : Type*) := EuclideanSpace ℂ (n × n)

/-- Linear equivalence between finite matrices and their flattened Hilbert space. -/
def finiteMatrixHilbertEquiv {n : Type*} [Fintype n] :
    Matrix n n ℂ ≃ₗ[ℂ] FiniteMatrixHilbert n where
  toFun A := WithLp.toLp 2 (fun p => A p.1 p.2)
  invFun x i j := x.ofLp (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv x := by
    apply WithLp.ofLp_injective 2
    rfl

/-- Flattened Euclidean inner product is exactly the matrix Hilbert--Schmidt
inner product. -/
theorem inner_finiteMatrixHilbertEquiv_eq_hsInner
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    inner ℂ (finiteMatrixHilbertEquiv A) (finiteMatrixHilbertEquiv B) =
      hsInner A B := by
  simp only [finiteMatrixHilbertEquiv, hsInner, Matrix.trace,
    PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Commutation by a Hermitian matrix is self-adjoint for Hilbert--Schmidt
geometry. -/
theorem hsInner_ringCommutator_selfAdjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (H X Y : Matrix n n ℂ) (hH : Hᴴ = H) :
    hsInner (ringCommutator H X) Y =
      hsInner X (ringCommutator H Y) := by
  simp only [hsInner, ringCommutator, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, hH, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_sub]
  rw [← Matrix.trace_mul_cycle Xᴴ Y H]
  simp only [Matrix.mul_assoc]

/-- Every doubled collective Pauli generator is Hermitian. -/
theorem finiteTwoReplicaCollectiveGenerator_conjTranspose
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) :
    (finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P)ᴴ =
      finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P := by
  rw [Matrix.conjTranspose_add,
    finiteTwoReplicaPauliLeft_conjTranspose,
    finiteTwoReplicaPauliRight_conjTranspose]

/-- The sum of left- and right-replica commutators is commutation by the
doubled collective generator. -/
theorem finiteTwoReplicaCollectiveCommutator_eq_generator
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) (X : FiniteTwoReplicaMatrix V) :
    finiteTwoReplicaCollectiveCommutatorLinear P X =
      ringCommutator
        (finiteTwoReplicaPauliLeft P + finiteTwoReplicaPauliRight P) X := by
  simp [finiteTwoReplicaCollectiveCommutatorLinear,
    finiteTwoReplicaCollectiveCommutator, ringCommutator,
    Matrix.add_mul, Matrix.mul_add]
  abel

/-- Literal collective Pauli commutators are Hilbert--Schmidt self-adjoint. -/
theorem finiteTwoReplicaCollectiveCommutator_hsInner_selfAdjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) (X Y : FiniteTwoReplicaMatrix V) :
    hsInner (finiteTwoReplicaCollectiveCommutatorLinear P X) Y =
      hsInner X (finiteTwoReplicaCollectiveCommutatorLinear P Y) := by
  rw [finiteTwoReplicaCollectiveCommutator_eq_generator,
    finiteTwoReplicaCollectiveCommutator_eq_generator]
  exact hsInner_ringCommutator_selfAdjoint _ X Y
    (finiteTwoReplicaCollectiveGenerator_conjTranspose P)

/-- One collective double commutator has expectation equal to the squared
Hilbert--Schmidt norm of its first commutator. -/
theorem finiteTwoReplicaCollectiveCommutator_hilbert_energy
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) (X : FiniteTwoReplicaMatrix V) :
    inner ℂ (finiteMatrixHilbertEquiv X)
        (finiteMatrixHilbertEquiv
          (finiteTwoReplicaCollectiveCommutatorLinear P
            (finiteTwoReplicaCollectiveCommutatorLinear P X))) =
      inner ℂ
        (finiteMatrixHilbertEquiv
          (finiteTwoReplicaCollectiveCommutatorLinear P X))
        (finiteMatrixHilbertEquiv
          (finiteTwoReplicaCollectiveCommutatorLinear P X)) := by
  rw [inner_finiteMatrixHilbertEquiv_eq_hsInner,
    inner_finiteMatrixHilbertEquiv_eq_hsInner]
  exact (finiteTwoReplicaCollectiveCommutator_hsInner_selfAdjoint
    P X (finiteTwoReplicaCollectiveCommutatorLinear P X)).symm

/-- Ordered-edge sum of all literal nine-term physical edge Casimirs. Edge
duplication changes the positive weights but not the kernel. -/
noncomputable def finiteTwoReplicaPhysicalGraphCasimir
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    FiniteTwoReplicaMatrix V →ₗ[ℂ] FiniteTwoReplicaMatrix V := by
  classical
  exact ∑ e : V × V,
    if G.Adj e.1 e.2 then finiteTwoReplicaPhysicalEdgeCasimir e.1 e.2 else 0

/-- Sum of squared Hilbert--Schmidt residuals of all physical edge
commutators. -/
noncomputable def finiteTwoReplicaPhysicalGraphEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : FiniteTwoReplicaMatrix V) : ℝ := by
  classical
  exact ∑ e : V × V, if G.Adj e.1 e.2 then
    ∑ a : Fin 3, ∑ b : Fin 3,
      ‖finiteMatrixHilbertEquiv
        (finiteTwoReplicaCollectiveCommutatorLinear
          (finiteEdgePauliLabel e.1 e.2 a b) X)‖ ^ 2
    else 0

/-- Exact graph energy identity: graph-Casimir expectation is the sum of all
squared first-commutator residuals. -/
theorem re_inner_finiteTwoReplicaPhysicalGraphCasimir_eq_energy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : FiniteTwoReplicaMatrix V) :
    Complex.re (inner ℂ (finiteMatrixHilbertEquiv X)
      (finiteMatrixHilbertEquiv
        (finiteTwoReplicaPhysicalGraphCasimir G X))) =
      finiteTwoReplicaPhysicalGraphEnergy G X := by
  classical
  simp only [finiteTwoReplicaPhysicalGraphCasimir,
    finiteTwoReplicaPhysicalGraphEnergy, LinearMap.sum_apply,
    map_sum, inner_sum, map_sum]
  change Complex.reCLM (∑ e : V × V,
      inner ℂ (finiteMatrixHilbertEquiv X)
        (finiteMatrixHilbertEquiv
          ((if G.Adj e.1 e.2 then
              finiteTwoReplicaPhysicalEdgeCasimir e.1 e.2 else 0) X))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.Adj e.1 e.2
  · rw [if_pos he, if_pos he]
    simp only [finiteTwoReplicaPhysicalEdgeCasimir,
      LinearMap.sum_apply, map_sum, inner_sum, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [LinearMap.comp_apply,
      finiteTwoReplicaCollectiveCommutator_hilbert_energy,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  · simp [he]

/-- **Positive graph edge-Casimir kernel law.** On the physical product-
Clifford singlet sector of every finite nonempty connected graph, the single
graph-summed Casimir has exactly global identity and global replica swap as
zero modes. -/
theorem finiteTwoReplicaPhysicalGraphCasimir_embed_eq_zero_iff
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Preconnected)
    (c : TwoReplicaGlobalCoeff V) :
    finiteTwoReplicaPhysicalGraphCasimir G
        (finiteTwoReplicaSwapInvariantEmbed c) = 0 ↔
      ∃ a b : ℂ, c = twoReplicaGlobalSynchronizedCoeff a b := by
  classical
  let X : FiniteTwoReplicaMatrix V := finiteTwoReplicaSwapInvariantEmbed c
  constructor
  · intro hzero
    have henergy : finiteTwoReplicaPhysicalGraphEnergy G X = 0 := by
      rw [← re_inner_finiteTwoReplicaPhysicalGraphCasimir_eq_energy,
        hzero]
      simp
    change (∑ e : V × V, if G.Adj e.1 e.2 then
        ∑ a : Fin 3, ∑ b : Fin 3,
          ‖finiteMatrixHilbertEquiv
            (finiteTwoReplicaCollectiveCommutatorLinear
              (finiteEdgePauliLabel e.1 e.2 a b) X)‖ ^ 2
      else 0) = 0 at henergy
    have hedgeZero : ∀ ⦃u v⦄, G.Adj u v →
        finiteTwoReplicaPhysicalEdgeCasimir u v X = 0 := by
      intro u v huv
      have houterNonneg : ∀ e ∈ (Finset.univ : Finset (V × V)),
          0 ≤ if G.Adj e.1 e.2 then
            ∑ a : Fin 3, ∑ b : Fin 3,
              ‖finiteMatrixHilbertEquiv
                (finiteTwoReplicaCollectiveCommutatorLinear
                  (finiteEdgePauliLabel e.1 e.2 a b) X)‖ ^ 2
          else 0 := by
        intro e _
        by_cases he : G.Adj e.1 e.2
        · rw [if_pos he]
          exact Finset.sum_nonneg fun a _ =>
            Finset.sum_nonneg fun b _ => sq_nonneg _
        · simp [he]
      have houter :
          (if G.Adj u v then
            ∑ a : Fin 3, ∑ b : Fin 3,
              ‖finiteMatrixHilbertEquiv
                (finiteTwoReplicaCollectiveCommutatorLinear
                  (finiteEdgePauliLabel u v a b) X)‖ ^ 2
          else 0) = 0 := by
        have hall :=
          (Finset.sum_eq_zero_iff_of_nonneg houterNonneg).mp henergy
        exact hall (u, v) (Finset.mem_univ (u, v))
      have hedgeEnergy :
          (∑ a : Fin 3, ∑ b : Fin 3,
            ‖finiteMatrixHilbertEquiv
              (finiteTwoReplicaCollectiveCommutatorLinear
                (finiteEdgePauliLabel u v a b) X)‖ ^ 2) = 0 := by
        simpa [huv] using houter
      have hcomm (a b : Fin 3) :
          finiteTwoReplicaCollectiveCommutatorLinear
              (finiteEdgePauliLabel u v a b) X = 0 := by
        have ha :
            (∑ b : Fin 3,
              ‖finiteMatrixHilbertEquiv
                (finiteTwoReplicaCollectiveCommutatorLinear
                  (finiteEdgePauliLabel u v a b) X)‖ ^ 2) = 0 := by
          apply (Finset.sum_eq_zero_iff_of_nonneg
            (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)).mp
              hedgeEnergy a (Finset.mem_univ a)
        have hab :
            ‖finiteMatrixHilbertEquiv
              (finiteTwoReplicaCollectiveCommutatorLinear
                (finiteEdgePauliLabel u v a b) X)‖ ^ 2 = 0 := by
          apply (Finset.sum_eq_zero_iff_of_nonneg
            (fun b _ => sq_nonneg _)).mp ha b (Finset.mem_univ b)
        apply finiteMatrixHilbertEquiv.injective
        apply norm_eq_zero.mp
        exact sq_eq_zero_iff.mp hab
      simp only [finiteTwoReplicaPhysicalEdgeCasimir,
        LinearMap.sum_apply, LinearMap.comp_apply]
      simp_rw [hcomm]
      simp
    exact (finiteTwoReplicaPhysical_connectedGraph_kernel_iff hG c).mp
      (by simpa [X] using hedgeZero)
  · intro hsync
    have hedgeZero : ∀ ⦃u v⦄, G.Adj u v →
        finiteTwoReplicaPhysicalEdgeCasimir u v
          (finiteTwoReplicaSwapInvariantEmbed c) = 0 :=
      (finiteTwoReplicaPhysical_connectedGraph_kernel_iff hG c).mpr hsync
    simp only [finiteTwoReplicaPhysicalGraphCasimir,
      LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro e _
    by_cases he : G.Adj e.1 e.2
    · simp [he, hedgeZero he]
    · simp [he]

/-- If every first edge image is hidden in `W`, the graph Casimir return lies
in the ordinary weight-at-most-`q` family shadow of `W`. -/
theorem finiteTwoReplicaPhysicalGraphCasimir_mem_qlocalShadow
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) (G : SimpleGraph V)
    (W : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (X : FiniteTwoReplicaMatrix V)
    (himages : ∀ ⦃u v⦄, G.Adj u v → ∀ a b : Fin 3,
      finiteTwoReplicaCollectiveCommutatorLinear
        (finiteEdgePauliLabel u v a b) X ∈ W) :
    finiteTwoReplicaPhysicalGraphCasimir G X ∈
      linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W := by
  classical
  simp only [finiteTwoReplicaPhysicalGraphCasimir,
    LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro e _
  by_cases he : G.Adj e.1 e.2
  · rw [if_pos he]
    simp only [finiteTwoReplicaPhysicalEdgeCasimir,
      LinearMap.sum_apply, LinearMap.comp_apply]
    apply Submodule.sum_mem
    intro a _
    apply Submodule.sum_mem
    intro b _
    let Pq : FiniteQLocalPauliLabel V q :=
      ⟨finiteEdgePauliLabel e.1 e.2 a b, by
        rw [finitePauliWeight_finiteEdgePauliLabel he.ne]
        exact hq⟩
    have hfirst :
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteEdgePauliLabel e.1 e.2 a b) X ∈ W :=
      himages he a b
    have hout :
        finiteTwoReplicaQLocalCollectiveCommutatorLinear V q Pq
            (finiteTwoReplicaCollectiveCommutatorLinear
              (finiteEdgePauliLabel e.1 e.2 a b) X) ∈
          linearFamilyShadow
            (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W :=
      (le_iSup (fun P : FiniteQLocalPauliLabel V q =>
        W.map (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q P)) Pq)
        ⟨_, hfirst, rfl⟩
    simpa [finiteTwoReplicaQLocalCollectiveCommutatorLinear, Pq] using hout
  · simp [he]

/-- Linear physical realization of the two synchronized coefficients: global
identity and global replica swap. -/
def finiteTwoReplicaGlobalSynchronizedMap
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] :
    (ℂ × ℂ) →ₗ[ℂ] FiniteTwoReplicaMatrix V where
  toFun z := finiteTwoReplicaSwapInvariantEmbed
    (twoReplicaGlobalSynchronizedCoeff z.1 z.2)
  map_add' z w := by
    rw [← LinearMap.map_add]
    congr 1
    funext x
    by_cases hx0 : x = twoReplicaAllIdentity
    · simp [twoReplicaGlobalSynchronizedCoeff, hx0]
    by_cases hx1 : x = twoReplicaAllSwap
    · simp [twoReplicaGlobalSynchronizedCoeff, hx1,
        (twoReplicaAllIdentity_ne_allSwap (V := V)).symm]
    · simp [twoReplicaGlobalSynchronizedCoeff, hx0, hx1]
  map_smul' a z := by
    rw [← LinearMap.map_smul]
    congr 1
    funext x
    by_cases hx0 : x = twoReplicaAllIdentity
    · simp [twoReplicaGlobalSynchronizedCoeff, hx0]
    by_cases hx1 : x = twoReplicaAllSwap
    · simp [twoReplicaGlobalSynchronizedCoeff, hx1,
        (twoReplicaAllIdentity_ne_allSwap (V := V)).symm]
    · simp [twoReplicaGlobalSynchronizedCoeff, hx0, hx1]

/-- Physical two-dimensional subspace spanned by global identity and global
replica swap. -/
def finiteTwoReplicaGlobalSynchronizedSubmodule
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V] :
    Submodule ℂ (FiniteTwoReplicaMatrix V) :=
  LinearMap.range (finiteTwoReplicaGlobalSynchronizedMap (V := V))

/-- Membership in the synchronized physical submodule is exactly an explicit
global identity/global-swap linear combination. -/
theorem mem_finiteTwoReplicaGlobalSynchronizedSubmodule_iff
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (X : FiniteTwoReplicaMatrix V) :
    X ∈ finiteTwoReplicaGlobalSynchronizedSubmodule (V := V) ↔
      ∃ a b : ℂ, X = finiteTwoReplicaSwapInvariantEmbed
        (twoReplicaGlobalSynchronizedCoeff a b) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.2, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨(a, b), rfl⟩

/-- Inside the full physical swap-word range, graph-Casimir vanishing is
equivalent to membership in the synchronized two-mode subspace. -/
theorem finiteTwoReplicaPhysicalGraphCasimir_eq_zero_iff_of_mem_swapRange
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Preconnected)
    {X : FiniteTwoReplicaMatrix V}
    (hX : X ∈ LinearMap.range
      (finiteTwoReplicaSwapInvariantEmbed (V := V))) :
    finiteTwoReplicaPhysicalGraphCasimir G X = 0 ↔
      X ∈ finiteTwoReplicaGlobalSynchronizedSubmodule (V := V) := by
  rcases hX with ⟨c, rfl⟩
  rw [finiteTwoReplicaPhysicalGraphCasimir_embed_eq_zero_iff hG]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact (mem_finiteTwoReplicaGlobalSynchronizedSubmodule_iff _).2
      ⟨a, b, rfl⟩
  · intro h
    rcases (mem_finiteTwoReplicaGlobalSynchronizedSubmodule_iff _).1 h with
      ⟨a, b, hab⟩
    exact ⟨a, b, finiteTwoReplicaSwapInvariantEmbed_injective hab⟩

/-- Exact physical submodule identity: the graph-Casimir kernel intersected
with the product-Clifford singlet range is the synchronized two-mode space. -/
theorem finiteTwoReplicaPhysicalGraphCasimir_ker_inf_swapRange
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Preconnected) :
    LinearMap.ker (finiteTwoReplicaPhysicalGraphCasimir G) ⊓
        LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)) =
      finiteTwoReplicaGlobalSynchronizedSubmodule (V := V) := by
  ext X
  constructor
  · rintro ⟨hzero, hsinglet⟩
    exact (finiteTwoReplicaPhysicalGraphCasimir_eq_zero_iff_of_mem_swapRange
      hG hsinglet).1 (LinearMap.mem_ker.mp hzero)
  · intro hsync
    have hshape :=
      (mem_finiteTwoReplicaGlobalSynchronizedSubmodule_iff X).1 hsync
    rcases hshape with ⟨a, b, rfl⟩
    constructor
    · apply LinearMap.mem_ker.mpr
      exact (finiteTwoReplicaPhysicalGraphCasimir_embed_eq_zero_iff hG _).2
        ⟨a, b, rfl⟩
    · exact ⟨twoReplicaGlobalSynchronizedCoeff a b, rfl⟩

/-- The graph Casimir preserves the complete physical swap-word range. -/
theorem finiteTwoReplicaPhysicalGraphCasimir_mem_swapRange
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {X : FiniteTwoReplicaMatrix V}
    (hX : X ∈ LinearMap.range
      (finiteTwoReplicaSwapInvariantEmbed (V := V))) :
    finiteTwoReplicaPhysicalGraphCasimir G X ∈
      LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)) := by
  classical
  rcases hX with ⟨c, rfl⟩
  simp only [finiteTwoReplicaPhysicalGraphCasimir,
    LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro e _
  by_cases he : G.Adj e.1 e.2
  · rw [if_pos he,
      finiteTwoReplicaPhysicalEdgeCasimir_intertwines_swapCoeff he.ne]
    exact ⟨twoReplicaGlobalEdgeCasimirCoeff e.1 e.2 c, rfl⟩
  · simp [he]

end

end GaloisForLFunctions.HTGeometry
