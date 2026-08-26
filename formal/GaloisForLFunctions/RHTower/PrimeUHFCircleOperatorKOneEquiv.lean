import GaloisForLFunctions.RHTower.PrimeUHFRelativeFiniteStageApproximation

/-!
# Prime UHF circle operator K-one continuity equivalence

Literal finite matrix-stage unitary loops form the same operator-`K₁` group after passage to the
matrix AF direct limit as based unitary loops in the norm-completed prime UHF algebra.  Surjectivity
uses finite-stage polygonal approximation; injectivity uses relative two-parameter approximation.
-/

open Filter Topology
open scoped ContinuousFunctionalCalculus Ring
open GaloisForLFunctions.HTGeometry

namespace PrimeQuasiLocalCharge

noncomputable section

noncomputable local instance {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (FundamentalGroup G 1) :=
  fundamentalGroupCommGroup

local instance primeAFCircleOperatorKOneModuleContinuityEquiv
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k) :
    Module ℤ (PrimeAFCircleOperatorKOne hd) :=
  Module.DirectLimit.module
    (fun i ↦ MatrixAFStageOperatorKOne localDim i)
    (fun i j hij ↦ matrixAFOperatorKOneTransition hd i j hij)

local instance primeUHFCircleOperatorKOneModuleContinuityEquiv
    (localDim : ℕ → ℕ) [Fact (∀ k, 0 < localDim k)] :
    Module ℤ (PrimeUHFCircleOperatorKOne localDim) :=
  AddCommGroup.toIntModule (PrimeUHFCircleOperatorKOne localDim)

theorem matrixAFStageUnitaryTransition_succ
    (localDim : ℕ → ℕ) (i : ℕ)
    (U : Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ) :
    matrixAFStageUnitaryTransition localDim (Nat.le_succ i) U =
      unitaryGroupReindex (matrixAFStageSuccIndexEquiv localDim i)
        (amplifyUnitary (localDim (i + 1)) U) := by
  apply Subtype.ext
  change matrixAFStageTransition localDim i (i + 1) (Nat.le_succ i)
      (U : PrimeAFMatrixStageAlgebra localDim i) = _
  rw [matrixAFStageTransition_succ localDim le_rfl,
    matrixAFStageTransition_self]
  rfl

/-- Explicit based path induced by an all-pair finite-stage unitary transition. -/
def matrixAFStageUnitaryTransitionBasedPath
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    {i j : ℕ} (hij : i ≤ j)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim j)) ℂ) 1 :=
  basedMapPath
    ⟨matrixAFStageUnitaryTransition localDim hij,
      continuous_matrixAFStageUnitaryTransition Fact.out hij⟩ 1 1
    (map_one (matrixAFStageUnitaryTransition localDim hij)) p

theorem matrixAFStageUnitaryTransitionBasedPath_eq_cast
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    {i j : ℕ} (hij : i ≤ j)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    matrixAFStageUnitaryTransitionBasedPath hij p =
      (p.map (continuous_matrixAFStageUnitaryTransition Fact.out hij)).cast
        (map_one (matrixAFStageUnitaryTransition localDim hij)).symm
        (map_one (matrixAFStageUnitaryTransition localDim hij)).symm := by
  apply Path.ext
  funext t
  rfl

@[simp] theorem matrixAFStageUnitaryTransitionBasedPath_self
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (i : ℕ)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    matrixAFStageUnitaryTransitionBasedPath (le_refl i) p = p := by
  apply Path.ext
  funext t
  change matrixAFStageUnitaryTransition localDim (le_refl i) (p t) = p t
  apply Subtype.ext
  change matrixAFStageTransition localDim i i (le_refl i)
      (p t : PrimeAFMatrixStageAlgebra localDim i) = p t
  calc
    matrixAFStageTransition localDim i i (le_refl i)
        (p t : PrimeAFMatrixStageAlgebra localDim i) =
        (StarAlgHom.id ℂ (PrimeAFMatrixStageAlgebra localDim i))
          (p t : PrimeAFMatrixStageAlgebra localDim i) :=
      congrArg
        (fun f : PrimeAFMatrixStageAlgebra localDim i →⋆ₐ[ℂ]
            PrimeAFMatrixStageAlgebra localDim i =>
          f (p t : PrimeAFMatrixStageAlgebra localDim i))
        (matrixAFStageTransition_self localDim i)
    _ = p t := rfl

theorem matrixAFStageUnitaryTransitionBasedPath_succ
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    {i j : ℕ} (hij : i ≤ j)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    matrixAFStageUnitaryTransitionBasedPath (Nat.le.step hij) p =
      unitaryGroupReindexBasedPath (matrixAFStageSuccIndexEquiv localDim j)
        (amplifyUnitaryBasedPath (localDim (j + 1))
          (matrixAFStageUnitaryTransitionBasedPath hij p)) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change matrixAFStageTransition localDim i (j + 1) (Nat.le.step hij)
      (p t : PrimeAFMatrixStageAlgebra localDim i) =
    matrixAFStageSuccHom localDim j
      (matrixAFStageTransition localDim i j hij
        (p t : PrimeAFMatrixStageAlgebra localDim i))
  rw [matrixAFStageTransition_succ localDim hij]
  rfl

theorem matrixAFPhysicalSuccKOneHom_apply_based_path
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (i : ℕ)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    matrixAFPhysicalSuccKOneHom localDim i
        (Additive.ofMul (Path.Homotopic.Quotient.mk p)) =
      Additive.ofMul (Path.Homotopic.Quotient.mk
        (unitaryGroupReindexBasedPath (matrixAFStageSuccIndexEquiv localDim i)
          (amplifyUnitaryBasedPath (localDim (i + 1)) p))) := by
  change unitaryGroupReindexKOneHom (matrixAFStageSuccIndexEquiv localDim i)
      (amplifyUnitaryKOneHom (localDim (i + 1))
        (Additive.ofMul (Path.Homotopic.Quotient.mk p))) = _
  rw [amplifyUnitaryKOneHom_apply_based,
    unitaryGroupReindexKOneHom_apply_based]
  rfl

theorem finiteMatrixOperatorKOneCharge_transitionBasedPath
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    {i j : ℕ} (hij : i ≤ j)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    finiteMatrixOperatorKOneCharge
        (Additive.ofMul (Path.Homotopic.Quotient.mk
          (matrixAFStageUnitaryTransitionBasedPath hij p))) =
      (chargeTransitionFactor localDim i j : ℤ) *
        finiteMatrixOperatorKOneCharge
          (Additive.ofMul (Path.Homotopic.Quotient.mk p)) := by
  induction hij using Nat.leRec with
  | refl =>
      rw [matrixAFStageUnitaryTransitionBasedPath_self,
        chargeTransitionFactor_self, Nat.cast_one, one_mul]
  | @le_succ_of_le j hij ih =>
      rw [matrixAFStageUnitaryTransitionBasedPath_succ hij]
      have hphysical := matrixAFPhysicalSuccKOneHom_apply_based_path
        (localDim := localDim) j
        (matrixAFStageUnitaryTransitionBasedPath hij p)
      calc
        finiteMatrixOperatorKOneCharge
            (Additive.ofMul (Path.Homotopic.Quotient.mk
              (unitaryGroupReindexBasedPath
                (matrixAFStageSuccIndexEquiv localDim j)
                (amplifyUnitaryBasedPath (localDim (j + 1))
                  (matrixAFStageUnitaryTransitionBasedPath hij p))))) =
            finiteMatrixOperatorKOneCharge
              (matrixAFPhysicalSuccKOneHom localDim j
                (Additive.ofMul (Path.Homotopic.Quotient.mk
                  (matrixAFStageUnitaryTransitionBasedPath hij p)))) :=
          congrArg finiteMatrixOperatorKOneCharge hphysical.symm
        _ = (localDim (j + 1) : ℤ) *
            finiteMatrixOperatorKOneCharge
              (Additive.ofMul (Path.Homotopic.Quotient.mk
                (matrixAFStageUnitaryTransitionBasedPath hij p))) :=
          matrixAFPhysicalSuccKOneHom_charge localDim j _
        _ = (chargeTransitionFactor localDim i (j + 1) : ℤ) *
            finiteMatrixOperatorKOneCharge
              (Additive.ofMul (Path.Homotopic.Quotient.mk p)) := by
          rw [ih, ← mul_assoc, ← Nat.cast_mul]
          have hfactor : localDim (j + 1) * chargeTransitionFactor localDim i j =
              chargeTransitionFactor localDim i (j + 1) := by
            rw [Nat.mul_comm]
            simpa using chargeTransitionFactor_mul hij (Nat.le_succ j)
          rw [hfactor]

theorem matrixAFOperatorKOneTransition_apply_based_path
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    {i j : ℕ} (hij : i ≤ j)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1) :
    matrixAFOperatorKOneTransition Fact.out i j hij
        (Additive.ofMul (Path.Homotopic.Quotient.mk p)) =
      Additive.ofMul (Path.Homotopic.Quotient.mk
        (matrixAFStageUnitaryTransitionBasedPath hij p)) := by
  apply (matrixAFStageOperatorKOneEquivInt Fact.out j).injective
  rw [matrixAFOperatorKOneTransition_charge, chargeTransition_apply]
  exact finiteMatrixOperatorKOneCharge_transitionBasedPath hij p |>.symm

theorem exists_commonStageUnitaryVertices
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    {m : ℕ} (x : Fin (m + 2) → unitary (PrimeUHFAlgebra localDim))
    (hx₀ : x 0 = 1) (hx₁ : x (Fin.last (m + 1)) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ)
      (W : Fin (m + 2) →
        Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim N)) ℂ),
      W 0 = 1 ∧ W (Fin.last (m + 1)) = 1 ∧
        ∀ k, ‖(matrixAFStageUnitaryToUHF N (W k) : PrimeUHFAlgebra localDim) -
          (x k : PrimeUHFAlgebra localDim)‖ < ε := by
  have happ : ∀ k : Fin (m + 2), ∃ (i : ℕ)
      (V : Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ),
      ‖(matrixAFStageUnitaryToUHF i V : PrimeUHFAlgebra localDim) -
        (x k : PrimeUHFAlgebra localDim)‖ < ε := by
    intro k
    exact exists_matrixAFStageUnitary_norm_sub_lt (x k) hε
  choose i V hV using happ
  let N := ∑ k : Fin (m + 2), i k
  have hiN : ∀ k, i k ≤ N := by
    intro k
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (i j)) (Finset.mem_univ k)
  let W : Fin (m + 2) →
      Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim N)) ℂ := fun k =>
    if hk : k = 0 ∨ k = Fin.last (m + 1) then 1
    else matrixAFStageUnitaryTransition localDim (hiN k) (V k)
  refine ⟨N, W, ?_, ?_, ?_⟩
  · simp [W]
  · simp [W]
  · intro k
    by_cases hk : k = 0 ∨ k = Fin.last (m + 1)
    · rcases hk with rfl | rfl
      · simp [W, hx₀, hε]
      · simp [W, hx₁, hε]
    · rw [show W k = matrixAFStageUnitaryTransition localDim (hiN k) (V k) by
          simp [W, hk]]
      rw [matrixAFStageUnitaryToUHF_transition]
      exact hV k

def matrixAFStagePolarPathToUHF
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (N : ℕ)
    (U V : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim N)) ℂ)
    (hclose : ‖(V : PrimeAFMatrixStageAlgebra localDim N) - U‖ ≤ 1 / 16) :
    Path (matrixAFStageUnitaryToUHF N U)
      (matrixAFStageUnitaryToUHF N V) := by
  letI : Nonempty (Fin (matrixAFStageDimension localDim N)) :=
    Fin.pos_iff_nonempty.mp (matrixAFStageDimension_pos Fact.out N)
  exact (cstarPolarSegment U V hclose).map
    (continuous_matrixAFStageUnitaryToUHF N)

theorem norm_matrixAFStagePolarPathToUHF_sub_left_le
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (N : ℕ)
    (U V : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim N)) ℂ)
    (hclose : ‖(V : PrimeAFMatrixStageAlgebra localDim N) - U‖ ≤ 1 / 16)
    (t : unitInterval) :
    ‖((matrixAFStagePolarPathToUHF N U V hclose t :
        unitary (PrimeUHFAlgebra localDim)) : PrimeUHFAlgebra localDim) -
      (matrixAFStageUnitaryToUHF N U : PrimeUHFAlgebra localDim)‖ ≤
      7 * ‖(V : PrimeAFMatrixStageAlgebra localDim N) - U‖ := by
  letI : Nonempty (Fin (matrixAFStageDimension localDim N)) :=
    Fin.pos_iff_nonempty.mp (matrixAFStageDimension_pos Fact.out N)
  change ‖matrixAFStageToUHF N
      (((cstarPolarSegment U V hclose t :
        Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim N)) ℂ) :
          PrimeAFMatrixStageAlgebra localDim N)) -
      matrixAFStageToUHF N (U : PrimeAFMatrixStageAlgebra localDim N)‖ ≤ _
  rw [← map_sub, norm_matrixAFStageToUHF]
  exact norm_cstarPolarSegment_sub_left_le U V hclose t

theorem pathMap_concat
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} (x : Fin (n + 1) → X)
    (P : ∀ k : Fin n, Path (x k.castSucc) (x k.succ))
    (f : X → Y) (hf : Continuous f) :
    (Path.concat x P).map hf =
      Path.concat (f ∘ x) (fun k => (P k).map hf) := by
  induction n with
  | zero =>
      simp only [Path.concat_zero]
      apply Path.ext
      funext s
      change f (x 0) = f (x 0)
      rfl
  | succ n ih =>
      rw [Path.concat_succ, Path.concat_succ]
      calc
        ((Path.concat (x ∘ Fin.castSucc) (fun k => P k.castSucc)).trans
            (P (Fin.last n))).map hf =
            ((Path.concat (x ∘ Fin.castSucc) (fun k => P k.castSucc)).map hf).trans
              ((P (Fin.last n)).map hf) :=
          Path.map_trans _ _ hf
        _ = (Path.concat ((f ∘ x) ∘ Fin.castSucc)
            (fun k => (P k.castSucc).map hf)).trans
              ((P (Fin.last n)).map hf) := by
          rw [ih (x ∘ Fin.castSucc) (fun k => P k.castSucc)]
          rfl

theorem pathHomotopic_cast
    {X : Type*} [TopologicalSpace X]
    {x₀ x₁ y₀ y₁ : X} (p q : Path x₀ x₁)
    (hy₀ : y₀ = x₀) (hy₁ : y₁ = x₁)
    (h : p.Homotopic q) :
    (p.cast hy₀ hy₁).Homotopic (q.cast hy₀ hy₁) := by
  subst x₀
  subst x₁
  simpa using h

theorem cast_refl_trans_trans_refl_homotopic
    {X : Type*} [TopologicalSpace X]
    {x x₀ x₁ : X} {h₀ : x₀ = x} {h₁ : x₁ = x}
    {p : Path x₀ x₁} {q : Path x x}
    (h : p.Homotopic (q.cast h₀ h₁)) :
    ((Path.refl x).cast rfl h₀ |>.trans
      (p.trans ((Path.refl x).cast h₁ rfl))).Homotopic q := by
  subst_vars
  exact Path.Homotopic.trans
    (Path.Homotopic.trans ⟨Path.Homotopy.reflTrans _⟩
      ⟨Path.Homotopy.transRefl _⟩) h

set_option maxHeartbeats 800000 in
theorem exists_matrixAFStageBasedPath_homotopic
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (p : Path (1 : unitary (PrimeUHFAlgebra localDim)) 1) :
    ∃ (N : ℕ)
      (e : Path (1 : Matrix.unitaryGroup
        (Fin (matrixAFStageDimension localDim N)) ℂ) 1),
      (matrixAFStageToUHFBasedPath N e).Homotopic p := by
  let ε : ℝ := 1 / 1024
  let c : unitary (PrimeUHFAlgebra localDim) →
      Set (unitary (PrimeUHFAlgebra localDim)) := fun u => Metric.ball u ε
  have hε : 0 < ε := by norm_num [ε]
  have hcOpen : ∀ u, IsOpen (c u) := fun u => Metric.isOpen_ball
  have hcCover : Set.univ ⊆ ⋃ u, c u := by
    intro u _
    apply Set.mem_iUnion.mpr
    exact ⟨u, by simpa [c] using hε⟩
  obtain ⟨n, t, ht₀, ht₁, hpiece⟩ :=
    GaloisForLFunctions.HTGeometry.exists_path_partition_unitInterval_of_open_cover
      hcOpen hcCover p
  choose z hz using hpiece
  let a : Fin (n + 2) → unitary (PrimeUHFAlgebra localDim) := fun k => p (t k)
  have ha₀ : a 0 = 1 := by simp [a, ht₀, p.source]
  have ha₁ : a (Fin.last (n + 1)) = 1 := by simp [a, ht₁, p.target]
  obtain ⟨N, W, hW₀, hW₁, hWa⟩ :=
    exists_commonStageUnitaryVertices a ha₀ ha₁ hε
  let q : Fin (n + 2) → unitary (PrimeUHFAlgebra localDim) :=
    matrixAFStageUnitaryToUHF N ∘ W
  have hq₀ : q 0 = 1 := by simp [q, hW₀]
  have hq₁ : q (Fin.last (n + 1)) = 1 := by simp [q, hW₁]
  have hqaNorm : ∀ k, ‖(a k : PrimeUHFAlgebra localDim) - (q k :
      PrimeUHFAlgebra localDim)‖ ≤ 1 / 16 := by
    intro k
    have h := (hWa k).le
    rw [norm_sub_rev]
    exact h.trans (by norm_num [ε])
  let G : ∀ k : Fin (n + 2), Path (q k) (a k) := fun k =>
    cstarPolarSegment (q k) (a k) (hqaNorm k)
  let F : ∀ k : Fin (n + 1), Path (a k.castSucc) (a k.succ) := fun k => by
    exact p.subpath (t k.castSucc) (t k.succ)
  have haLeftCenter : ∀ k : Fin (n + 1), dist (a k.castSucc) (z k) < ε := by
    intro k
    have hmem : p (t k.castSucc) ∈ c (z k) :=
      hz k ⟨t k.castSucc, Set.left_mem_uIcc, rfl⟩
    simpa [a, c, Metric.mem_ball] using hmem
  have haRightCenter : ∀ k : Fin (n + 1), dist (a k.succ) (z k) < ε := by
    intro k
    have hmem : p (t k.succ) ∈ c (z k) :=
      hz k ⟨t k.succ, Set.right_mem_uIcc, rfl⟩
    simpa [a, c, Metric.mem_ball] using hmem
  have hqaDist : ∀ k, dist (q k) (a k) < ε := by
    intro k
    simpa [q, a, Subtype.dist_eq, dist_eq_norm] using hWa k
  have hqPairDist : ∀ k : Fin (n + 1),
      dist (q k.succ) (q k.castSucc) < 4 * ε := by
    intro k
    have h₁ := dist_triangle (q k.succ) (a k.succ) (q k.castSucc)
    have h₂ := dist_triangle (a k.succ) (z k) (q k.castSucc)
    have h₃ := dist_triangle (z k) (a k.castSucc) (q k.castSucc)
    have hL := hqaDist k.castSucc
    have hR := hqaDist k.succ
    have hcL := haLeftCenter k
    have hcR := haRightCenter k
    have hL' := hL
    rw [dist_comm] at hL'
    have hcL' := hcL
    rw [dist_comm] at hcL'
    linarith
  have hWPair : ∀ k : Fin (n + 1),
      ‖(W k.succ : PrimeAFMatrixStageAlgebra localDim N) -
          (W k.castSucc : PrimeAFMatrixStageAlgebra localDim N)‖ ≤
        1 / 16 := by
    intro k
    calc
      ‖(W k.succ : PrimeAFMatrixStageAlgebra localDim N) -
          (W k.castSucc : PrimeAFMatrixStageAlgebra localDim N)‖ =
          ‖matrixAFStageToUHF N
            ((W k.succ : PrimeAFMatrixStageAlgebra localDim N) -
              (W k.castSucc : PrimeAFMatrixStageAlgebra localDim N))‖ :=
        (norm_matrixAFStageToUHF N _).symm
      _ = dist (q k.succ) (q k.castSucc) := by
        rw [map_sub]
        change ‖(q k.succ : PrimeUHFAlgebra localDim) - q k.castSucc‖ = _
        rw [Subtype.dist_eq, dist_eq_norm]
      _ ≤ 1 / 16 := (hqPairDist k).le.trans (by norm_num [ε])
  letI : Nonempty (Fin (matrixAFStageDimension localDim N)) :=
    Fin.pos_iff_nonempty.mp (matrixAFStageDimension_pos Fact.out N)
  let ePiece : ∀ k : Fin (n + 1), Path (W k.castSucc) (W k.succ) := fun k =>
    cstarPolarSegment (W k.castSucc) (W k.succ) (hWPair k)
  let E : ∀ k : Fin (n + 1), Path (q k.castSucc) (q k.succ) := fun k =>
    matrixAFStagePolarPathToUHF N (W k.castSucc) (W k.succ) (hWPair k)
  let D : ∀ k : Fin (n + 1), Path (q k.castSucc) (q k.succ) := fun k =>
    (G k.castSucc).trans ((F k).trans (G k.succ).symm)
  have hGCenterLeft : ∀ (k : Fin (n + 1)) (s : unitInterval),
      dist (G k.castSucc s) (z k) < 1 / 16 := by
    intro k s
    have hGq : dist (G k.castSucc s) (q k.castSucc) ≤
        7 * dist (a k.castSucc) (q k.castSucc) := by
      simpa [G, Subtype.dist_eq, dist_eq_norm] using
        norm_cstarPolarSegment_sub_left_le (q k.castSucc) (a k.castSucc)
          (hqaNorm k.castSucc) s
    have h₁ := dist_triangle (G k.castSucc s) (q k.castSucc) (z k)
    have h₂ := dist_triangle (q k.castSucc) (a k.castSucc) (z k)
    have hqa := hqaDist k.castSucc
    have hqa' := hqa
    rw [dist_comm] at hqa'
    have hac := haLeftCenter k
    calc
      dist (G k.castSucc s) (z k) ≤
          dist (G k.castSucc s) (q k.castSucc) +
            dist (q k.castSucc) (z k) := h₁
      _ ≤ 7 * dist (a k.castSucc) (q k.castSucc) +
          (dist (q k.castSucc) (a k.castSucc) +
            dist (a k.castSucc) (z k)) := add_le_add hGq h₂
      _ < 7 * ε + (ε + ε) := add_lt_add
        (mul_lt_mul_of_pos_left hqa' (by norm_num)) (add_lt_add hqa hac)
      _ < 1 / 16 := by norm_num [ε]
  have hGCenterRight : ∀ (k : Fin (n + 1)) (s : unitInterval),
      dist (G k.succ s) (z k) < 1 / 16 := by
    intro k s
    have hGq : dist (G k.succ s) (q k.succ) ≤
        7 * dist (a k.succ) (q k.succ) := by
      simpa [G, Subtype.dist_eq, dist_eq_norm] using
        norm_cstarPolarSegment_sub_left_le (q k.succ) (a k.succ)
          (hqaNorm k.succ) s
    have h₁ := dist_triangle (G k.succ s) (q k.succ) (z k)
    have h₂ := dist_triangle (q k.succ) (a k.succ) (z k)
    have hqa := hqaDist k.succ
    have hqa' := hqa
    rw [dist_comm] at hqa'
    have hac := haRightCenter k
    calc
      dist (G k.succ s) (z k) ≤
          dist (G k.succ s) (q k.succ) + dist (q k.succ) (z k) := h₁
      _ ≤ 7 * dist (a k.succ) (q k.succ) +
          (dist (q k.succ) (a k.succ) + dist (a k.succ) (z k)) :=
        add_le_add hGq h₂
      _ < 7 * ε + (ε + ε) := add_lt_add
        (mul_lt_mul_of_pos_left hqa' (by norm_num)) (add_lt_add hqa hac)
      _ < 1 / 16 := by norm_num [ε]
  have hFCenter : ∀ (k : Fin (n + 1)) (s : unitInterval),
      dist (F k s) (z k) < 1 / 16 := by
    intro k s
    have hrange : F k s ∈ Set.range (F k) := ⟨s, rfl⟩
    have himage : F k s ∈ p '' Set.uIcc (t k.castSucc) (t k.succ) := by
      rw [← Path.range_subpath p (t k.castSucc) (t k.succ)]
      exact hrange
    have := hz k himage
    have hdist : dist (F k s) (z k) < ε := by
      simpa [c, Metric.mem_ball] using (show F k s ∈ c (z k) from this)
    exact hdist.trans (by norm_num [ε])
  have hDCenter : ∀ (k : Fin (n + 1)) (s : unitInterval),
      dist (D k s) (z k) < 1 / 16 := by
    intro k s
    have hmem : D k s ∈ Set.range (D k) := ⟨s, rfl⟩
    change D k s ∈ Set.range ((G k.castSucc).trans
      ((F k).trans (G k.succ).symm)) at hmem
    rw [Path.trans_range, Path.trans_range, Path.symm_range] at hmem
    rcases hmem with hmem | hmem | hmem
    · obtain ⟨r, hr⟩ := hmem
      rw [← hr]
      exact hGCenterLeft k r
    · obtain ⟨r, hr⟩ := hmem
      rw [← hr]
      exact hFCenter k r
    · obtain ⟨r, hr⟩ := hmem
      rw [← hr]
      exact hGCenterRight k r
  have hECenter : ∀ (k : Fin (n + 1)) (s : unitInterval),
      dist (E k s) (z k) < 1 / 16 := by
    intro k s
    have hEq : dist (E k s) (q k.castSucc) ≤
        7 * ‖(W k.succ : PrimeAFMatrixStageAlgebra localDim N) -
          (W k.castSucc : PrimeAFMatrixStageAlgebra localDim N)‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]
      have hEk : E k = matrixAFStagePolarPathToUHF N
          (W k.castSucc) (W k.succ) (hWPair k) := rfl
      rw [hEk]
      exact norm_matrixAFStagePolarPathToUHF_sub_left_le N
        (W k.castSucc) (W k.succ) (hWPair k) s
    have hstageDist :
        ‖(W k.succ : PrimeAFMatrixStageAlgebra localDim N) -
          (W k.castSucc : PrimeAFMatrixStageAlgebra localDim N)‖ =
          dist (q k.succ) (q k.castSucc) := by
      calc
        ‖(W k.succ : PrimeAFMatrixStageAlgebra localDim N) -
            (W k.castSucc : PrimeAFMatrixStageAlgebra localDim N)‖ =
            ‖matrixAFStageToUHF N
              ((W k.succ : PrimeAFMatrixStageAlgebra localDim N) -
                (W k.castSucc : PrimeAFMatrixStageAlgebra localDim N))‖ :=
          (norm_matrixAFStageToUHF N _).symm
        _ = dist (q k.succ) (q k.castSucc) := by
          rw [map_sub]
          change ‖(q k.succ : PrimeUHFAlgebra localDim) - q k.castSucc‖ = _
          rw [Subtype.dist_eq, dist_eq_norm]
    rw [hstageDist] at hEq
    have h₁ := dist_triangle (E k s) (q k.castSucc) (z k)
    have h₂ := dist_triangle (q k.castSucc) (a k.castSucc) (z k)
    have hp := hqPairDist k
    have hqa := hqaDist k.castSucc
    have hac := haLeftCenter k
    calc
      dist (E k s) (z k) ≤ dist (E k s) (q k.castSucc) +
          dist (q k.castSucc) (z k) := h₁
      _ ≤ 7 * dist (q k.succ) (q k.castSucc) +
          (dist (q k.castSucc) (a k.castSucc) +
            dist (a k.castSucc) (z k)) := add_le_add hEq h₂
      _ < 7 * (4 * ε) + (ε + ε) := add_lt_add
        (mul_lt_mul_of_pos_left hp (by norm_num)) (add_lt_add hqa hac)
      _ < 1 / 16 := by norm_num [ε]
  have hDE : ∀ k : Fin (n + 1), (D k).Homotopic (E k) := by
    intro k
    exact ⟨unitaryPathsHomotopyOfNormSubLtTwo (D k) (E k) (fun s => by
      have htri := dist_triangle (E k s) (z k) (D k s)
      have hE := hECenter k s
      have hD := hDCenter k s
      have hD' := hD
      rw [dist_comm] at hD'
      have hdist : dist (E k s) (D k s) < 2 := by linarith
      simpa [Subtype.dist_eq, dist_eq_norm] using hdist)⟩
  let stageConcat : Path (W 0) (W (Fin.last (n + 1))) :=
    Path.concat W ePiece
  let e : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim N)) ℂ) 1 :=
    stageConcat.cast hW₀.symm hW₁.symm
  refine ⟨N, e, ?_⟩
  have hG₀point : ∀ s, G 0 s = 1 := by
    intro s
    apply Subtype.ext
    change cstarPolarNearOne
      (cstarAffineSegment (q 0 : PrimeUHFAlgebra localDim)
        (a 0 : PrimeUHFAlgebra localDim) s) = 1
    have haff : cstarAffineSegment (q 0 : PrimeUHFAlgebra localDim)
        (a 0 : PrimeUHFAlgebra localDim) s = 1 := by
      have hqcoe : (q 0 : PrimeUHFAlgebra localDim) = 1 :=
        congrArg Subtype.val hq₀
      have hacoe : (a 0 : PrimeUHFAlgebra localDim) = 1 :=
        congrArg Subtype.val ha₀
      exact (congrArg₂ (fun x y : PrimeUHFAlgebra localDim =>
        cstarAffineSegment x y s) hqcoe hacoe).trans
          (cstarAffineSegment_self (1 : PrimeUHFAlgebra localDim) s)
    rw [haff]
    exact cstarPolarNearOne_unitary
      (1 : unitary (PrimeUHFAlgebra localDim))
  have hG₁point : ∀ s, G (Fin.last (n + 1)) s = 1 := by
    intro s
    apply Subtype.ext
    change cstarPolarNearOne
      (cstarAffineSegment (q (Fin.last (n + 1)) : PrimeUHFAlgebra localDim)
        (a (Fin.last (n + 1)) : PrimeUHFAlgebra localDim) s) = 1
    have haff : cstarAffineSegment
        (q (Fin.last (n + 1)) : PrimeUHFAlgebra localDim)
        (a (Fin.last (n + 1)) : PrimeUHFAlgebra localDim) s = 1 := by
      have hqcoe : (q (Fin.last (n + 1)) : PrimeUHFAlgebra localDim) = 1 :=
        congrArg Subtype.val hq₁
      have hacoe : (a (Fin.last (n + 1)) : PrimeUHFAlgebra localDim) = 1 :=
        congrArg Subtype.val ha₁
      exact (congrArg₂ (fun x y : PrimeUHFAlgebra localDim =>
        cstarAffineSegment x y s) hqcoe hacoe).trans
          (cstarAffineSegment_self (1 : PrimeUHFAlgebra localDim) s)
    rw [haff]
    exact cstarPolarNearOne_unitary
      (1 : unitary (PrimeUHFAlgebra localDim))
  have hG₀ : (G 0).cast hq₀.symm rfl =
      (Path.refl 1).cast rfl ha₀ := by
    apply Path.ext
    funext s
    exact hG₀point s
  have hG₁ : (G (Fin.last (n + 1))).symm.cast rfl hq₁.symm =
      (Path.refl 1).cast ha₁ rfl := by
    apply Path.ext
    funext s
    change G (Fin.last (n + 1)) (unitInterval.symm s) = 1
    exact hG₁point _
  let concatD : Path (q 0) (q (Fin.last (n + 1))) := Path.concat q D
  let concatE : Path (q 0) (q (Fin.last (n + 1))) := Path.concat q E
  let concatA : Path (a 0) (a (Fin.last (n + 1))) := Path.concat a F
  let R : Path (q 0) (q (Fin.last (n + 1))) :=
    (G 0).trans (concatA.trans (G (Fin.last (n + 1))).symm)
  have hConcatDE : concatD.Homotopic concatE := by
    let H : ∀ k : Fin (n + 1), (D k).Homotopy (E k) := fun k =>
      Classical.choice (hDE k)
    exact ⟨Path.Homotopy.concat q D E H⟩
  have hCancel : concatD.Homotopic R := by
    exact GaloisForLFunctions.HTGeometry.concat_trans_trans_symm_homotopic
      a q F G
  have hER : concatE.Homotopic R := hConcatDE.symm.trans hCancel
  have hERcast :
      (concatE.cast hq₀.symm hq₁.symm).Homotopic
        (R.cast hq₀.symm hq₁.symm) :=
    pathHomotopic_cast concatE R hq₀.symm hq₁.symm hER
  have hRcast : R.cast hq₀.symm hq₁.symm =
      ((G 0).cast hq₀.symm rfl).trans
        (concatA.trans
          ((G (Fin.last (n + 1))).symm.cast rfl hq₁.symm)) := by
    apply Path.ext
    funext s
    rfl
  have hConcatA : concatA.Homotopic (p.cast ha₀ ha₁) := by
    apply Path.Homotopic.trans
      ⟨Path.Homotopy.concatSubpath p t⟩
    exact ⟨unitaryPathsHomotopyOfNormSubLtTwo
      (p.subpath (t 0) (t (Fin.last (n + 1)))) (p.cast ha₀ ha₁)
      (fun s => by
        rw! (castMode := .all) [ht₀, ht₁, Path.subpath_zero_one]
        change ‖(p s : PrimeUHFAlgebra localDim) - (p s : PrimeUHFAlgebra localDim)‖ < 2
        simp)⟩
  have hRbase :
      (((Path.refl 1).cast rfl ha₀).trans
        (concatA.trans ((Path.refl 1).cast ha₁ rfl))).Homotopic p :=
    cast_refl_trans_trans_refl_homotopic hConcatA
  have hRtoP : (R.cast hq₀.symm hq₁.symm).Homotopic p := by
    rw [hRcast, hG₀, hG₁]
    exact hRbase
  have hConcatEToP : (concatE.cast hq₀.symm hq₁.symm).Homotopic p :=
    hERcast.trans hRtoP
  let f : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim N)) ℂ →
      unitary (PrimeUHFAlgebra localDim) := matrixAFStageUnitaryToUHF N
  have hMapConcat : stageConcat.map (continuous_matrixAFStageUnitaryToUHF N) =
      concatE := by
    have h := pathMap_concat W ePiece f
      (continuous_matrixAFStageUnitaryToUHF N)
    simpa [stageConcat, concatE, q, E, ePiece, f,
      matrixAFStagePolarPathToUHF] using h
  have hBasedPath : matrixAFStageToUHFBasedPath N e =
      (stageConcat.map (continuous_matrixAFStageUnitaryToUHF N)).cast
        hq₀.symm hq₁.symm := by
    apply Path.ext
    funext s
    rfl
  rw [hBasedPath, hMapConcat]
  exact hConcatEToP

theorem primeAFCircleOperatorKOneToUHF_surjective
    {localDim : ℕ → ℕ} [hd : Fact (∀ k, 0 < localDim k)] :
    Function.Surjective
      (primeAFCircleOperatorKOneToUHF (localDim := localDim)) := by
  intro y
  let g : FundamentalGroup (unitary (PrimeUHFAlgebra localDim)) 1 :=
    Additive.toMul y
  have hy : y = Additive.ofMul g := rfl
  rw [hy]
  refine Path.Homotopic.Quotient.ind (motive := fun g : FundamentalGroup
      (unitary (PrimeUHFAlgebra localDim)) 1 =>
      ∃ x, primeAFCircleOperatorKOneToUHF (localDim := localDim) x =
        Additive.ofMul g) ?_ g
  intro p
  obtain ⟨N, e, he⟩ := exists_matrixAFStageBasedPath_homotopic p
  let qe : FundamentalGroup (Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim N)) ℂ) 1 :=
    Path.Homotopic.Quotient.mk e
  refine ⟨finiteStageMatrixOperatorKOne (localDim := localDim) hd.out N
    (Additive.ofMul qe), ?_⟩
  rw [primeAFCircleOperatorKOneToUHF_finiteStage,
    matrixAFStageToUHFKOne_apply_based]
  apply Additive.toMul.injective
  change matrixAFStageToUHFBasedKOneMap N qe =
    Path.Homotopic.Quotient.mk p
  change Path.Homotopic.Quotient.mk (matrixAFStageToUHFBasedPath N e) =
    Path.Homotopic.Quotient.mk p
  exact Path.Homotopic.Quotient.eq.mpr he

theorem primeAFCircleOperatorKOneToUHF_injective
    {localDim : ℕ → ℕ} [hd : Fact (∀ k, 0 < localDim k)] :
    Function.Injective
      (primeAFCircleOperatorKOneToUHF (localDim := localDim)) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hx : primeAFCircleOperatorKOneToUHF (localDim := localDim) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨i, xi, hxi⟩ :=
    primeAFCircleOperatorKOne_has_finiteAncestor hd.out (x - y)
  rw [← hxi]
  rw [← hxi] at hx
  let q : FundamentalGroup
      (Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ) 1 :=
    Additive.toMul xi
  have hxiq : xi = Additive.ofMul q := rfl
  rw [hxiq] at hx ⊢
  refine Path.Homotopic.Quotient.ind (motive := fun q : FundamentalGroup
      (Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ) 1 =>
      primeAFCircleOperatorKOneToUHF (localDim := localDim)
          (finiteStageMatrixOperatorKOne hd.out i (Additive.ofMul q)) = 0 →
        finiteStageMatrixOperatorKOne hd.out i (Additive.ofMul q) = 0) ?_ q hx
  intro p hp
  rw [primeAFCircleOperatorKOneToUHF_finiteStage,
    matrixAFStageToUHFKOne_apply_based] at hp
  have hquot : Path.Homotopic.Quotient.mk
      (matrixAFStageToUHFBasedPath i p) =
      Path.Homotopic.Quotient.mk (Path.refl 1) := by
    have hzero : (0 : PrimeUHFCircleOperatorKOne localDim) =
        Additive.ofMul (Path.Homotopic.Quotient.mk
          (Path.refl (1 : unitary (PrimeUHFAlgebra localDim)))) := rfl
    exact Additive.ofMul.injective (hp.trans hzero)
  obtain ⟨H⟩ := Path.Homotopic.Quotient.eq.mp hquot
  obtain ⟨M, hiM, hnull⟩ :=
    exists_finiteStage_nullhomotopy_of_UHF_nullhomotopy i p H
  have hnull' : (matrixAFStageUnitaryTransitionBasedPath hiM p).Homotopic
      (Path.refl 1) := by
    rw [matrixAFStageUnitaryTransitionBasedPath_eq_cast]
    exact hnull
  have htransitionZero :
      matrixAFOperatorKOneTransition hd.out i M hiM
          (Additive.ofMul (Path.Homotopic.Quotient.mk p)) = 0 := by
    rw [matrixAFOperatorKOneTransition_apply_based_path]
    apply Additive.ofMul.injective
    exact Path.Homotopic.Quotient.eq.mpr hnull'
  have hdirect : finiteStageMatrixOperatorKOne hd.out M
      (matrixAFOperatorKOneTransition hd.out i M hiM
        (Additive.ofMul (Path.Homotopic.Quotient.mk p))) =
      finiteStageMatrixOperatorKOne hd.out i
        (Additive.ofMul (Path.Homotopic.Quotient.mk p)) :=
    Module.DirectLimit.of_f
      (R := ℤ) (G := fun i ↦ MatrixAFStageOperatorKOne localDim i)
      (f := fun i j hij ↦ matrixAFOperatorKOneTransition hd.out i j hij)
      (hij := hiM)
  rw [htransitionZero, map_zero] at hdirect
  exact hdirect.symm

/-- Exact continuity isomorphism from finite matrix-loop colimit to completed-UHF loops. -/
def primeAFCircleOperatorKOneEquivUHF
    {localDim : ℕ → ℕ} [hd : Fact (∀ k, 0 < localDim k)] :
    PrimeAFCircleOperatorKOne hd.out ≃ₗ[ℤ]
      PrimeUHFCircleOperatorKOne localDim :=
  LinearEquiv.ofBijective primeAFCircleOperatorKOneToUHF
    ⟨primeAFCircleOperatorKOneToUHF_injective,
      primeAFCircleOperatorKOneToUHF_surjective⟩

/-- Every completed-UHF circle operator-`K₁` class has a literal finite matrix-stage ancestor. -/
theorem primeUHFCircleOperatorKOne_has_finiteMatrixAncestor
    {localDim : ℕ → ℕ} [hd : Fact (∀ k, 0 < localDim k)]
    (y : PrimeUHFCircleOperatorKOne localDim) :
    ∃ (i : ℕ) (x : MatrixAFStageOperatorKOne localDim i),
      matrixAFStageToUHFKOne i x = y := by
  obtain ⟨q, hq⟩ := primeAFCircleOperatorKOneToUHF_surjective y
  obtain ⟨i, x, hx⟩ :=
    primeAFCircleOperatorKOne_has_finiteAncestor hd.out q
  refine ⟨i, x, ?_⟩
  calc
    matrixAFStageToUHFKOne i x =
        primeAFCircleOperatorKOneToUHF
          (finiteStageMatrixOperatorKOne hd.out i x) := by
      rw [primeAFCircleOperatorKOneToUHF_finiteStage]
    _ = primeAFCircleOperatorKOneToUHF q := congrArg _ hx
    _ = y := hq

/-- Every nonzero completed-UHF circle charge already occurs at a nonzero finite matrix stage. -/
theorem nonzero_primeUHFCircleOperatorKOne_has_nonzero_finiteMatrixAncestor
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    {y : PrimeUHFCircleOperatorKOne localDim} (hy : y ≠ 0) :
    ∃ (i : ℕ) (x : MatrixAFStageOperatorKOne localDim i),
      x ≠ 0 ∧ matrixAFStageToUHFKOne i x = y := by
  obtain ⟨i, x, hx⟩ := primeUHFCircleOperatorKOne_has_finiteMatrixAncestor y
  refine ⟨i, x, ?_, hx⟩
  intro hzero
  subst x
  exact hy (by simpa using hx.symm)

/-- If every finite matrix-stage ancestor of a completed-UHF circle class vanishes, so does it. -/
theorem primeUHFCircleOperatorKOne_eq_zero_of_all_finiteAncestors_zero
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (y : PrimeUHFCircleOperatorKOne localDim)
    (hzero : ∀ (i : ℕ) (x : MatrixAFStageOperatorKOne localDim i),
      matrixAFStageToUHFKOne i x = y → x = 0) :
    y = 0 := by
  obtain ⟨i, x, hx⟩ := primeUHFCircleOperatorKOne_has_finiteMatrixAncestor y
  have hxzero := hzero i x hx
  subst x
  simpa using hx.symm

/-- Uniformly close based unitary loops have the same completed-UHF circle class. -/
theorem primeUHFCircleOperatorKOne_eq_of_uniform_norm_sub_lt_two
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (p q : Path (1 : unitary (PrimeUHFAlgebra localDim)) 1)
    (hclose : ∀ t, ‖(p t : PrimeUHFAlgebra localDim) - q t‖ < 2) :
    Additive.ofMul (Path.Homotopic.Quotient.mk p) =
      Additive.ofMul (Path.Homotopic.Quotient.mk q) := by
  apply Additive.ofMul.injective
  exact Path.Homotopic.Quotient.eq.mpr
    ⟨unitaryPathsHomotopyOfNormSubLtTwo p q (fun t => by
      rw [norm_sub_rev]
      exact hclose t)⟩

/-- A uniform limit of zero-class completed-UHF unitary loops still has zero class. -/
theorem primeUHFCircleOperatorKOne_eq_zero_of_uniform_limit
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (u : ℕ → Path (1 : unitary (PrimeUHFAlgebra localDim)) 1)
    (p : Path (1 : unitary (PrimeUHFAlgebra localDim)) 1)
    (hu : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t,
      ‖(u n t : PrimeUHFAlgebra localDim) - p t‖ < ε)
    (hzero : ∀ n,
      Additive.ofMul (Path.Homotopic.Quotient.mk (u n)) =
        (0 : PrimeUHFCircleOperatorKOne localDim)) :
    Additive.ofMul (Path.Homotopic.Quotient.mk p) =
      (0 : PrimeUHFCircleOperatorKOne localDim) := by
  obtain ⟨N, hN⟩ := hu 2 (by norm_num)
  rw [primeUHFCircleOperatorKOne_eq_of_uniform_norm_sub_lt_two p (u N)
    (fun t => by
      rw [norm_sub_rev]
      exact hN N le_rfl t)]
  exact hzero N

end
end PrimeQuasiLocalCharge
