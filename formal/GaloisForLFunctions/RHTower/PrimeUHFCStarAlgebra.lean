import GaloisForLFunctions.HTGeometry.KroneckerIdentityIsometry
import GaloisForLFunctions.HTGeometry.LinearIsometryCompletion
import GaloisForLFunctions.RHTower.PrimeAFMatrixOperatorKOneDirectLimit
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Topology.UniformSpace.Completion

/-!
# Literal norm-completed prime UHF algebra

This module constructs the analytic algebra omitted by the earlier charge-colimit calculation.
Finite stages are complex matrix C-star algebras with Euclidean operator norm.  Successor maps are
literal tensor-identity amplifications followed by canonical index flattening.  Their all-pair
maps are composites of successor maps, so functoriality is structural; their isometry follows from
the exact Kronecker identity norm theorem.

The algebraic directed limit receives the representative operator norm.  Its norm completion is
then equipped, by density, with its complex algebra structure, continuous involution, C-star
identity, and a literal `CStarAlgebra` instance.  No operator-K-theory group is defined here.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker
open GaloisForLFunctions.HTGeometry

namespace PrimeQuasiLocalCharge

noncomputable section

/-- Raw complex matrices with the Euclidean operator norm carry the assembled C-star structure. -/
noncomputable instance matrixL2CStarAlgebra
    (n : Type*) [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) := CStarAlgebra.mk

/-- Tensor a matrix with a finite identity as a unital star-algebra homomorphism. -/
def kroneckerOneStarAlgHom
    {m : Type*} [Fintype m] [DecidableEq m] (d : ℕ) :
    Matrix m m ℂ →⋆ₐ[ℂ] Matrix (m × Fin d) (m × Fin d) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := by ext; simp
  map_add' A B := by ext; simp [add_mul]
  commutes' c := by
    ext p q
    rcases p with ⟨i, a⟩
    rcases q with ⟨j, b⟩
    by_cases hij : i = j <;> by_cases hab : a = b <;>
      simp [Algebra.algebraMap_eq_smul_one, hij, hab]
  map_star' A := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.conjTranspose_kronecker A (1 : Matrix (Fin d) (Fin d) ℂ)).symm

/-- Simultaneous row-column reindexing as a star-algebra equivalence on raw matrices. -/
def matrixReindexStarAlgEquiv
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  CStarMatrix.reindexₐ ℂ ℂ e

/-- Canonical flattening of a stage index and the newly adjoined local index. -/
def matrixAFStageSuccIndexEquiv (localDim : ℕ → ℕ) (i : ℕ) :
    Fin (matrixAFStageDimension localDim i) × Fin (localDim (i + 1)) ≃
      Fin (matrixAFStageDimension localDim (i + 1)) :=
  finProdFinEquiv

/-- Successor-stage inclusion by identity-factor amplification and canonical index flattening. -/
def matrixAFStageSuccHom (localDim : ℕ → ℕ) (i : ℕ) :
    Matrix (Fin (matrixAFStageDimension localDim i))
        (Fin (matrixAFStageDimension localDim i)) ℂ →⋆ₐ[ℂ]
      Matrix (Fin (matrixAFStageDimension localDim (i + 1)))
        (Fin (matrixAFStageDimension localDim (i + 1))) ℂ :=
  (matrixReindexStarAlgEquiv (matrixAFStageSuccIndexEquiv localDim i)).toStarAlgHom.comp
    (kroneckerOneStarAlgHom (localDim (i + 1)))

/-- All-pair stage inclusion, defined as the literal composite of successor inclusions. -/
def matrixAFStageTransition (localDim : ℕ → ℕ) (i j : ℕ) (hij : i ≤ j) :
    Matrix (Fin (matrixAFStageDimension localDim i))
        (Fin (matrixAFStageDimension localDim i)) ℂ →⋆ₐ[ℂ]
      Matrix (Fin (matrixAFStageDimension localDim j))
        (Fin (matrixAFStageDimension localDim j)) ℂ :=
  Nat.leRec (StarAlgHom.id ℂ _)
    (fun {k} _ previous => (matrixAFStageSuccHom localDim k).comp previous) hij

@[simp] theorem matrixAFStageTransition_self (localDim : ℕ → ℕ) (i : ℕ) :
    matrixAFStageTransition localDim i i le_rfl = StarAlgHom.id ℂ _ := by
  simp [matrixAFStageTransition, Nat.leRec_self]

theorem matrixAFStageTransition_succ (localDim : ℕ → ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    matrixAFStageTransition localDim i (j + 1) (Nat.le.step hij) =
      (matrixAFStageSuccHom localDim j).comp
        (matrixAFStageTransition localDim i j hij) := by
  unfold matrixAFStageTransition
  apply Nat.leRec_succ

theorem matrixAFStageTransition_comp (localDim : ℕ → ℕ)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (matrixAFStageTransition localDim j k hjk).comp
        (matrixAFStageTransition localDim i j hij) =
      matrixAFStageTransition localDim i k (hij.trans hjk) := by
  induction hjk using Nat.leRec with
  | refl =>
      simp
  | @le_succ_of_le k hjk ih =>
    rw [matrixAFStageTransition_succ localDim hjk,
        matrixAFStageTransition_succ localDim (hij.trans hjk)]
    apply StarAlgHom.ext
    intro A
    exact congrArg (matrixAFStageSuccHom localDim k)
      (DFunLike.congr_fun ih A)

instance matrixAFStageDirectedSystem (localDim : ℕ → ℕ) :
    DirectedSystem
      (fun i : ℕ => Matrix (Fin (matrixAFStageDimension localDim i))
        (Fin (matrixAFStageDimension localDim i)) ℂ)
      (fun i j hij => matrixAFStageTransition localDim i j hij) where
  map_self := by
    intro i A
    rw [matrixAFStageTransition_self]
    rfl
  map_map := by
    intro k j i hij hjk A
    exact DFunLike.congr_fun (matrixAFStageTransition_comp localDim hij hjk) A

/-- A positive-dimensional physical successor inclusion is isometric. -/
theorem norm_matrixAFStageSuccHom {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) (i : ℕ)
    (A : Matrix (Fin (matrixAFStageDimension localDim i))
      (Fin (matrixAFStageDimension localDim i)) ℂ) :
    ‖matrixAFStageSuccHom localDim i A‖ = ‖A‖ := by
  letI : Nonempty (Fin (localDim (i + 1))) := Fin.pos_iff_nonempty.mp (hd (i + 1))
  calc
    ‖matrixAFStageSuccHom localDim i A‖ =
        ‖A ⊗ₖ (1 : Matrix (Fin (localDim (i + 1)))
          (Fin (localDim (i + 1))) ℂ)‖ := by
      exact StarAlgEquiv.norm_map
        (matrixReindexStarAlgEquiv (matrixAFStageSuccIndexEquiv localDim i)) _
    _ = ‖A‖ := l2_opNorm_kronecker_one A

/-- Every all-pair finite-stage inclusion is isometric. -/
theorem norm_matrixAFStageTransition {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) {i j : ℕ} (hij : i ≤ j)
    (A : Matrix (Fin (matrixAFStageDimension localDim i))
      (Fin (matrixAFStageDimension localDim i)) ℂ) :
    ‖matrixAFStageTransition localDim i j hij A‖ = ‖A‖ := by
  induction hij using Nat.leRec with
  | refl =>
      rw [DFunLike.congr_fun (matrixAFStageTransition_self localDim i) A]
      rfl
  | @le_succ_of_le j hij ih =>
      rw [DFunLike.congr_fun (matrixAFStageTransition_succ localDim hij) A]
      change ‖matrixAFStageSuccHom localDim j
        (matrixAFStageTransition localDim i j hij A)‖ = ‖A‖
      rw [norm_matrixAFStageSuccHom hd, ih]

abbrev PrimeAFMatrixStageAlgebra (localDim : ℕ → ℕ) (i : ℕ) :=
  Matrix (Fin (matrixAFStageDimension localDim i))
    (Fin (matrixAFStageDimension localDim i)) ℂ

/-- Algebraic union of finite prime-matrix stages. -/
abbrev PrimeAFAlgebraicLimit (localDim : ℕ → ℕ) :=
  DirectLimit (PrimeAFMatrixStageAlgebra localDim)
    (fun i j hij => matrixAFStageTransition localDim i j hij)

noncomputable instance primeAFAlgebraicLimitRing (localDim : ℕ → ℕ) :
    Ring (PrimeAFAlgebraicLimit localDim) := inferInstance

noncomputable instance primeAFAlgebraicLimitStarRing (localDim : ℕ → ℕ) :
    StarRing (PrimeAFAlgebraicLimit localDim) := inferInstance

noncomputable instance primeAFAlgebraicLimitAlgebra (localDim : ℕ → ℕ) :
    Algebra ℂ (PrimeAFAlgebraicLimit localDim) := inferInstance

/-- Operator norm on the algebraic direct limit; well-defined because every stage map is isometric. -/
def primeAFAlgebraicLimitNorm {localDim : ℕ → ℕ}
    (hd : ∀ k, 0 < localDim k) : PrimeAFAlgebraicLimit localDim → ℝ :=
  Quotient.lift (fun x => ‖x.2‖) fun x y hxy => by
    obtain ⟨k, hxk, hyk, hxy⟩ := hxy
    calc
      ‖x.2‖ = ‖matrixAFStageTransition localDim x.1 k hxk x.2‖ :=
        (norm_matrixAFStageTransition hd hxk x.2).symm
      _ = ‖matrixAFStageTransition localDim y.1 k hyk y.2‖ := congrArg norm hxy
      _ = ‖y.2‖ := norm_matrixAFStageTransition hd hyk y.2

noncomputable instance primeAFAlgebraicLimitNormInst
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    Norm (PrimeAFAlgebraicLimit localDim) where
  norm := primeAFAlgebraicLimitNorm Fact.out

@[simp] theorem norm_primeAFAlgebraicLimit_mk
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] (i : ℕ)
    (A : PrimeAFMatrixStageAlgebra localDim i) :
    ‖(⟦⟨i, A⟩⟧ : PrimeAFAlgebraicLimit localDim)‖ = ‖A‖ := rfl

theorem primeAFAlgebraicLimitNormedSpaceCore
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    NormedSpace.Core ℂ (PrimeAFAlgebraicLimit localDim) where
  norm_nonneg q := by
    induction q using DirectLimit.induction with
    | ih i A => simp
  norm_smul c q := by
    induction q using DirectLimit.induction with
    | ih i A =>
        rw [DirectLimit.smul_def]
        rw [norm_primeAFAlgebraicLimit_mk, norm_primeAFAlgebraicLimit_mk]
        calc
          ‖c • A‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (c • A)‖ :=
            (Matrix.l2_opNorm_toEuclideanCLM (c • A)).symm
          _ = ‖c • Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ := by rw [map_smul]
          _ = ‖c‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ := norm_smul _ _
          _ = ‖c‖ * ‖A‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]
  norm_triangle q r := by
    induction q, r using DirectLimit.induction₂ with
    | ih i A B =>
        rw [DirectLimit.add_def]
        simp
        exact norm_add_le A B
  norm_eq_zero_iff := by
    intro q
    induction q using DirectLimit.induction with
    | ih i A =>
        constructor
        · intro hA
          rw [norm_primeAFAlgebraicLimit_mk] at hA
          have : A = 0 := norm_eq_zero.mp hA
          subst A
          rw [← DirectLimit.zero_def i]
        · intro hzero
          rw [hzero]
          rw [DirectLimit.zero_def 0, norm_primeAFAlgebraicLimit_mk]
          exact norm_zero

noncomputable instance primeAFAlgebraicLimitNormedAddCommGroup
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    NormedAddCommGroup (PrimeAFAlgebraicLimit localDim) :=
  .ofCore primeAFAlgebraicLimitNormedSpaceCore

noncomputable instance primeAFAlgebraicLimitNormedSpace
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    NormedSpace ℂ (PrimeAFAlgebraicLimit localDim) :=
  .ofCore primeAFAlgebraicLimitNormedSpaceCore

noncomputable instance primeAFAlgebraicLimitNormedRing
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    NormedRing (PrimeAFAlgebraicLimit localDim) where
  dist_eq q r := by
    rw [dist_comm, dist_eq_norm]
    congr 1
    abel
  norm_mul_le q r := by
    induction q, r using DirectLimit.induction₂ with
    | ih i A B =>
        rw [DirectLimit.mul_def]
        simp only [norm_primeAFAlgebraicLimit_mk]
        exact norm_mul_le A B

noncomputable instance primeAFAlgebraicLimitNormedAlgebra
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    NormedAlgebra ℂ (PrimeAFAlgebraicLimit localDim) where
  norm_smul_le c q := by
    rw [norm_smul]

noncomputable instance primeAFAlgebraicLimitCStarRing
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    CStarRing (PrimeAFAlgebraicLimit localDim) where
  norm_mul_self_le q := by
    induction q using DirectLimit.induction with
    | ih i A =>
        rw [DirectLimit.star_def, DirectLimit.mul_def]
        simp only [norm_primeAFAlgebraicLimit_mk]
        exact CStarRing.norm_mul_self_le A

/-- The algebraic finite-stage union has unit norm; stage zero is a nonzero scalar matrix. -/
noncomputable instance primeAFAlgebraicLimitNormOneClass
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    NormOneClass (PrimeAFAlgebraicLimit localDim) where
  norm_one := by
    change primeAFAlgebraicLimitNorm Fact.out
      (1 : PrimeAFAlgebraicLimit localDim) = 1
    rw [DirectLimit.one_def 0]
    change ‖(1 : PrimeAFMatrixStageAlgebra localDim 0)‖ = 1
    letI : Nonempty (Fin (matrixAFStageDimension localDim 0)) :=
      Fin.pos_iff_nonempty.mp (matrixAFStageDimension_pos Fact.out 0)
    exact norm_one

noncomputable instance primeAFAlgebraicLimitNontrivial
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    Nontrivial (PrimeAFAlgebraicLimit localDim) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hn := congrArg norm h
  rw [norm_zero, norm_one] at hn
  norm_num at hn

/-- Norm completion of the literal finite-prime matrix union. -/
abbrev PrimeUHFAlgebra (localDim : ℕ → ℕ) [Fact (∀ k, 0 < localDim k)] :=
  UniformSpace.Completion (PrimeAFAlgebraicLimit localDim)

/-- Norm completion preserves the norm-one and nontrivial unit of the algebraic union. -/
noncomputable instance primeUHFAlgebraNormOneClass
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    NormOneClass (PrimeUHFAlgebra localDim) where
  norm_one := by
    rw [← UniformSpace.Completion.coe_one,
      UniformSpace.Completion.norm_coe]
    exact norm_one

noncomputable instance primeUHFAlgebraNontrivial
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    Nontrivial (PrimeUHFAlgebra localDim) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hn := congrArg norm h
  rw [norm_zero, norm_one] at hn
  norm_num at hn

/-- Scalar inclusion into the completed UHF algebra. -/
def primeUHFAlgebraMap
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    ℂ →+* PrimeUHFAlgebra localDim :=
  UniformSpace.Completion.coeRingHom.comp
    (algebraMap ℂ (PrimeAFAlgebraicLimit localDim))

noncomputable instance primeUHFAlgebraAlgebra
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    Algebra ℂ (PrimeUHFAlgebra localDim) where
  algebraMap := primeUHFAlgebraMap
  commutes' c x := by
    refine UniformSpace.Completion.induction_on x (isClosed_eq ?_ ?_) ?_
    · exact continuous_const.mul continuous_id
    · exact continuous_id.mul continuous_const
    · intro A
      change (↑((algebraMap ℂ (PrimeAFAlgebraicLimit localDim)) c) :
          PrimeUHFAlgebra localDim) * ↑A =
        ↑A * ↑((algebraMap ℂ (PrimeAFAlgebraicLimit localDim)) c)
      rw [← UniformSpace.Completion.coe_mul, ← UniformSpace.Completion.coe_mul]
      exact congrArg UniformSpace.Completion.coe' (Algebra.commutes c A)
  smul_def' c x := by
    refine UniformSpace.Completion.induction_on x (isClosed_eq ?_ ?_) ?_
    · have hc : Continuous (fun _ : PrimeUHFAlgebra localDim => c) := continuous_const
      have hx : Continuous (fun x : PrimeUHFAlgebra localDim => x) := continuous_id
      exact hc.smul hx
    · have hc : Continuous (fun _ : PrimeUHFAlgebra localDim =>
          (↑((algebraMap ℂ (PrimeAFAlgebraicLimit localDim)) c) :
            PrimeUHFAlgebra localDim)) := continuous_const
      have hx : Continuous (fun x : PrimeUHFAlgebra localDim => x) := continuous_id
      exact hc.mul hx
    · intro A
      change c • (↑A : PrimeUHFAlgebra localDim) =
        (↑((algebraMap ℂ (PrimeAFAlgebraicLimit localDim)) c) :
          PrimeUHFAlgebra localDim) * ↑A
      rw [← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_mul,
        Algebra.smul_def]

noncomputable instance primeUHFAlgebraNormedAlgebra
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    NormedAlgebra ℂ (PrimeUHFAlgebra localDim) where
  norm_smul_le c x := by
    rw [norm_smul]

theorem norm_star_primeAFAlgebraicLimit
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (q : PrimeAFAlgebraicLimit localDim) : ‖star q‖ = ‖q‖ := by
  induction q using DirectLimit.induction with
  | ih i A =>
      rw [DirectLimit.star_def]
      simp only [norm_primeAFAlgebraicLimit_mk]
      exact norm_star A

/-- Algebraic involution followed by the canonical inclusion into the completion. -/
def primeAFStarToCompletionLinearIsometry
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    PrimeAFAlgebraicLimit localDim →ₗᵢ[ℝ] PrimeUHFAlgebra localDim where
  toFun q := (↑(star q) : PrimeUHFAlgebra localDim)
  map_add' q r := by
    rw [star_add, UniformSpace.Completion.coe_add]
  map_smul' r q := by
    change (↑(star ((r : ℂ) • q)) : PrimeUHFAlgebra localDim) =
      r • (↑(star q) : PrimeUHFAlgebra localDim)
    rw [star_smul]
    simp only [RCLike.star_def, Complex.conj_ofReal]
    exact UniformSpace.Completion.coe_smul (r : ℂ) (star q)
  norm_map' q := by
    change ‖(↑(star q) : PrimeUHFAlgebra localDim)‖ = ‖q‖
    rw [UniformSpace.Completion.norm_coe, norm_star_primeAFAlgebraicLimit]

/-- Continuous involution on the completed UHF algebra. -/
def primeUHFStar
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    PrimeUHFAlgebra localDim →ₗᵢ[ℝ] PrimeUHFAlgebra localDim :=
  completionExtendₗᵢ primeAFStarToCompletionLinearIsometry

noncomputable instance primeUHFAlgebraStar
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    Star (PrimeUHFAlgebra localDim) where
  star := primeUHFStar

@[simp] theorem star_primeUHFAlgebra_coe
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (q : PrimeAFAlgebraicLimit localDim) :
    star (q : PrimeUHFAlgebra localDim) = (↑(star q) : PrimeUHFAlgebra localDim) := by
  change primeUHFStar (localDim := localDim) (q : PrimeUHFAlgebra localDim) = _
  exact completionExtendₗᵢ_coe
    (primeAFStarToCompletionLinearIsometry (localDim := localDim)) q

noncomputable instance primeUHFAlgebraStarRing
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    StarRing (PrimeUHFAlgebra localDim) where
  star_involutive x := by
    refine UniformSpace.Completion.induction_on x (isClosed_eq ?_ ?_) ?_
    · exact (primeUHFStar (localDim := localDim)).continuous.comp
        (primeUHFStar (localDim := localDim)).continuous
    · exact continuous_id
    · intro q
      rw [star_primeUHFAlgebra_coe, star_primeUHFAlgebra_coe, star_star]
  star_mul x y := by
    refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq ?_ ?_) ?_
    · exact (primeUHFStar (localDim := localDim)).continuous.comp continuous_mul
    · exact ((primeUHFStar (localDim := localDim)).continuous.comp continuous_snd).mul
        ((primeUHFStar (localDim := localDim)).continuous.comp continuous_fst)
    · intro q r
      rw [← UniformSpace.Completion.coe_mul, star_primeUHFAlgebra_coe,
        star_mul, star_primeUHFAlgebra_coe, star_primeUHFAlgebra_coe,
        ← UniformSpace.Completion.coe_mul]
  star_add x y := (primeUHFStar (localDim := localDim)).map_add x y

noncomputable instance primeUHFAlgebraStarModule
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    StarModule ℂ (PrimeUHFAlgebra localDim) where
  star_smul c x := by
    refine UniformSpace.Completion.induction_on x (isClosed_eq ?_ ?_) ?_
    · exact (primeUHFStar (localDim := localDim)).continuous.comp
        (continuous_const_smul c)
    · exact (continuous_const_smul (star c)).comp
        (primeUHFStar (localDim := localDim)).continuous
    · intro q
      rw [← UniformSpace.Completion.coe_smul, star_primeUHFAlgebra_coe,
        star_smul, star_primeUHFAlgebra_coe,
        ← UniformSpace.Completion.coe_smul]

noncomputable instance primeUHFAlgebraCStarRing
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    CStarRing (PrimeUHFAlgebra localDim) where
  norm_mul_self_le x := by
    refine UniformSpace.Completion.induction_on x (isClosed_le ?_ ?_) ?_
    · exact continuous_norm.mul continuous_norm
    · exact continuous_norm.comp
        ((primeUHFStar (localDim := localDim)).continuous.mul continuous_id)
    · intro q
      rw [UniformSpace.Completion.norm_coe, star_primeUHFAlgebra_coe,
        ← UniformSpace.Completion.coe_mul, UniformSpace.Completion.norm_coe]
      exact CStarRing.norm_mul_self_le q

/-- The norm completion of the finite-prime matrix union is a literal C-star algebra. -/
noncomputable instance primeUHFAlgebraCStarAlgebra
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)] :
    CStarAlgebra (PrimeUHFAlgebra localDim) := CStarAlgebra.mk

end

end PrimeQuasiLocalCharge
