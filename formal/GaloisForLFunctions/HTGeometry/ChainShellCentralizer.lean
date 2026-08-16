import GaloisForLFunctions.HTGeometry.ChainCentralizerClassification
import GaloisForLFunctions.HTGeometry.QuantitativeKernelRigidity

/-!
# The two-local shell of an open chain and its centralizer

The real two-local shell of an open chain is the range of the linear map sending a scalar, a family
of one-site fields and a family of edge couplings to the corresponding Hermitian operator.  If the
edge couplings are invertible and one of them is field rigid, the operators of the shell commuting
with a fixed one are exactly its real multiples plus multiples of the identity, and the distance to
that plane is controlled by the norm of the commutator.
-/

open Finset Matrix

open scoped Matrix.Norms.Frobenius

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {m : ℕ}

theorem chainEdgeOp_add (J L : Fin m → Fin 3 → Fin 3 → ℝ) :
    chainEdgeOp (fun v a b => J v a b + L v a b) = chainEdgeOp J + chainEdgeOp L := by
  rw [chainEdgeOp, chainEdgeOp, chainEdgeOp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← add_smul]
  congr 1
  push_cast
  ring

theorem real_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ)
    (M : Matrix ι ι ℂ) : ((c : ℂ)) • M = c • M := by
  ext x y
  simp [Complex.real_smul]

/-- The real two-local shell parameters: a scalar, the one-site fields, the edge couplings. -/
abbrev ShellParam (m : ℕ) :=
  ℝ × ((Fin (m + 1) → Fin 3 → ℝ) × (Fin m → Fin 3 → Fin 3 → ℝ))

/-- The operators of the chain. -/
abbrev ShellMat (m : ℕ) :=
  Matrix (FiniteQubitConfiguration (Fin (m + 1))) (FiniteQubitConfiguration (Fin (m + 1))) ℂ

/-- **The two-local shell operator of a parameter triple.** -/
def shellMap (m : ℕ) : ShellParam m →ₗ[ℝ] ShellMat m where
  toFun p := p.1 • (1 : ShellMat m) + chainSiteOp p.2.1 + chainEdgeOp p.2.2
  map_add' p q := by
    have h1 : chainSiteOp (p.2.1 + q.2.1) = chainSiteOp p.2.1 + chainSiteOp q.2.1 :=
      chainSiteOp_add p.2.1 q.2.1
    have h2 : chainEdgeOp (p.2.2 + q.2.2) = chainEdgeOp p.2.2 + chainEdgeOp q.2.2 :=
      chainEdgeOp_add p.2.2 q.2.2
    show (p.1 + q.1) • (1 : ShellMat m) + chainSiteOp (p.2.1 + q.2.1) +
      chainEdgeOp (p.2.2 + q.2.2) = _
    rw [h1, h2, add_smul]
    abel
  map_smul' c p := by
    have h1 : chainSiteOp (c • p.2.1) = c • chainSiteOp p.2.1 := by
      rw [← real_smul_matrix, ← chainSiteOp_smul]
      rfl
    have h2 : chainEdgeOp (c • p.2.2) = c • chainEdgeOp p.2.2 := by
      rw [← real_smul_matrix, ← chainEdgeOp_smul]
      rfl
    show (c * p.1) • (1 : ShellMat m) + chainSiteOp (c • p.2.1) + chainEdgeOp (c • p.2.2) = _
    rw [h1, h2, mul_smul]
    show _ = c • (p.1 • (1 : ShellMat m) + chainSiteOp p.2.1 + chainEdgeOp p.2.2)
    rw [smul_add, smul_add]

theorem shellMap_apply (p : ShellParam m) :
    shellMap m p = p.1 • (1 : ShellMat m) + chainSiteOp p.2.1 + chainEdgeOp p.2.2 := rfl

/-- The real two-local shell of the open chain. -/
def chainShell (m : ℕ) : Submodule ℝ (ShellMat m) := LinearMap.range (shellMap m)

theorem mem_chainShell (A : ShellMat m) : A ∈ chainShell m ↔ ∃ p : ShellParam m, shellMap m p = A :=
  LinearMap.mem_range

theorem one_mem_chainShell : (1 : ShellMat m) ∈ chainShell m := by
  refine (mem_chainShell _).mpr ⟨(1, 0, 0), ?_⟩
  rw [shellMap_apply, one_smul]
  have h1 : chainSiteOp (0 : Fin (m + 1) → Fin 3 → ℝ) = 0 := by
    rw [chainSiteOp]
    refine Finset.sum_eq_zero fun p _ => ?_
    show ((0 : ℝ) : ℂ) • _ = 0
    rw [Complex.ofReal_zero, zero_smul]
  have h2 : chainEdgeOp (0 : Fin m → Fin 3 → Fin 3 → ℝ) = 0 := by
    rw [chainEdgeOp]
    refine Finset.sum_eq_zero fun p _ => ?_
    show ((0 : ℝ) : ℂ) • _ = 0
    rw [Complex.ofReal_zero, zero_smul]
  rw [h1, h2, add_zero, add_zero]

theorem shellMap_mem_chainShell (p : ShellParam m) : shellMap m p ∈ chainShell m :=
  LinearMap.mem_range_self _ _


theorem shellMap_apply_assoc (p : ShellParam m) :
    shellMap m p = p.1 • (1 : ShellMat m) + (chainSiteOp p.2.1 + chainEdgeOp p.2.2) := by
  rw [shellMap_apply, add_assoc]

theorem sub_mul_comm_add_smul_one (X Y : ShellMat m) (c d : ℝ) :
    (c • (1 : ShellMat m) + X) * (d • (1 : ShellMat m) + Y) -
      (d • (1 : ShellMat m) + Y) * (c • (1 : ShellMat m) + X) = X * Y - Y * X := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_add, smul_smul, mul_comm]
  abel

/-- **The centralizer of a chain shell operator inside the shell.**

An operator of the two-local shell commutes with a shell operator whose edge couplings are
invertible and one of which is field rigid exactly when it is a real multiple of that operator plus
a real multiple of the identity. -/
theorem commute_shellMap_iff (hm : 2 ≤ m) (p0 : ShellParam m)
    (hJdet : ∀ v : Fin m, IsUnit (Matrix.det (p0.2.2 v)))
    (v0 : Fin m) (hrigid : FieldRigid (p0.2.2 v0))
    {A : ShellMat m} (hA : A ∈ chainShell m) :
    (shellMap m p0 * A = A * shellMap m p0) ↔
      ∃ lam mu : ℝ, A = lam • shellMap m p0 + mu • (1 : ShellMat m) := by
  classical
  constructor
  · intro hcomm
    obtain ⟨p, hp⟩ := (mem_chainShell A).mp hA
    have hcomm' : (chainSiteOp p0.2.1 + chainEdgeOp p0.2.2) *
        (chainSiteOp p.2.1 + chainEdgeOp p.2.2) =
        (chainSiteOp p.2.1 + chainEdgeOp p.2.2) * (chainSiteOp p0.2.1 + chainEdgeOp p0.2.2) := by
      have hz : shellMap m p0 * shellMap m p - shellMap m p * shellMap m p0 = 0 := by
        rw [hp]
        exact sub_eq_zero_of_eq hcomm
      rw [shellMap_apply_assoc p0, shellMap_apply_assoc p,
        sub_mul_comm_add_smul_one] at hz
      exact sub_eq_zero.mp hz
    obtain ⟨c, hK, hh⟩ := exists_scalar_of_commute_chain hm p0.2.1 p.2.1 p0.2.2 p.2.2
      hJdet v0 hrigid hcomm'
    have hsite : chainSiteOp p.2.1 = c • chainSiteOp p0.2.1 := by
      have hfun : p.2.1 = fun s a => c * p0.2.1 s a := by
        funext s a
        exact hh s a
      rw [hfun, chainSiteOp_smul, real_smul_matrix]
    have hedge : chainEdgeOp p.2.2 = c • chainEdgeOp p0.2.2 := by
      have hfun : p.2.2 = fun v a b => c * p0.2.2 v a b := by
        funext v a b
        simpa using congrFun (congrFun (hK v) a) b
      rw [hfun, chainEdgeOp_smul, real_smul_matrix]
    refine ⟨c, p.1 - c * p0.1, ?_⟩
    rw [← hp, shellMap_apply_assoc p, shellMap_apply_assoc p0, hsite, hedge, smul_add, smul_smul,
      sub_smul, mul_smul]
    rw [smul_add]
    abel
  · rintro ⟨lam, mu, rfl⟩
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]


/-- The commutator with a fixed shell operator, restricted to the shell. -/
def chainAd (m : ℕ) (p0 : ShellParam m) : (chainShell m) →ₗ[ℝ] ShellMat m where
  toFun A := shellMap m p0 * (A : ShellMat m) - (A : ShellMat m) * shellMap m p0
  map_add' A B := by
    simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c A := by
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub]

theorem chainAd_apply (p0 : ShellParam m) (A : chainShell m) :
    chainAd m p0 A = shellMap m p0 * (A : ShellMat m) - (A : ShellMat m) * shellMap m p0 := rfl


/-- **Quantitative tangent rigidity of the open chain.**

The distance from a shell operator to the plane spanned by the identity and a fixed shell operator
with invertible, somewhere field-rigid couplings is bounded by a fixed multiple of the norm of the
commutator with that operator. -/
theorem exists_gamma_pos_infDist_le (hm : 2 ≤ m) (p0 : ShellParam m)
    (hJdet : ∀ v : Fin m, IsUnit (Matrix.det (p0.2.2 v)))
    (v0 : Fin m) (hrigid : FieldRigid (p0.2.2 v0)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ A ∈ chainShell m,
      γ * Metric.infDist A {B : ShellMat m | ∃ lam mu : ℝ,
        B = lam • shellMap m p0 + mu • (1 : ShellMat m)} ≤
        ‖shellMap m p0 * A - A * shellMap m p0‖ := by
  classical
  obtain ⟨γ, hγ, hle⟩ := exists_pos_infDist_le (chainAd m p0)
  refine ⟨γ, hγ, fun A hA => ?_⟩
  have himg : (Subtype.val '' (LinearMap.ker (chainAd m p0) : Set (chainShell m))) =
      {B : ShellMat m | ∃ lam mu : ℝ, B = lam • shellMap m p0 + mu • (1 : ShellMat m)} := by
    ext B
    constructor
    · rintro ⟨⟨C, hC⟩, hmem, rfl⟩
      have hcomm : shellMap m p0 * C = C * shellMap m p0 := by
        have hker := LinearMap.mem_ker.mp hmem
        rw [chainAd_apply] at hker
        exact sub_eq_zero.mp hker
      exact (commute_shellMap_iff hm p0 hJdet v0 hrigid hC).mp hcomm
    · rintro ⟨lam, mu, rfl⟩
      have hmem : lam • shellMap m p0 + mu • (1 : ShellMat m) ∈ chainShell m :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ (shellMap_mem_chainShell p0))
          (Submodule.smul_mem _ _ one_mem_chainShell)
      refine ⟨⟨_, hmem⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, chainAd_apply, sub_eq_zero]
      exact (commute_shellMap_iff hm p0 hJdet v0 hrigid hmem).mpr ⟨lam, mu, rfl⟩
  have hiso := Metric.infDist_image (Φ := (Subtype.val : chainShell m → ShellMat m))
    (x := (⟨A, hA⟩ : chainShell m))
    (t := (LinearMap.ker (chainAd m p0) : Set (chainShell m))) isometry_subtype_coe
  rw [show ((⟨A, hA⟩ : chainShell m) : ShellMat m) = A from rfl] at hiso
  rw [← himg, hiso]
  exact hle ⟨A, hA⟩


/-- A one-parameter group commuting with an operator has a commuting generator. -/
theorem commute_of_exp_smul_commute (H B : ShellMat m)
    (hexp : ∀ s : ℝ, NormedSpace.exp (s • B) * H = H * NormedSpace.exp (s • B)) :
    B * H = H * B := by
  have hd1 : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • B) * H)
      ((NormedSpace.exp ((0 : ℝ) • B) * B) * H) 0 :=
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0).mul_const H
  have hd2 : HasDerivAt (fun s : ℝ => H * NormedSpace.exp (s • B))
      (H * (NormedSpace.exp ((0 : ℝ) • B) * B)) 0 :=
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0).const_mul H
  have hfun : (fun s : ℝ => NormedSpace.exp (s • B) * H) =
      fun s : ℝ => H * NormedSpace.exp (s • B) := funext hexp
  rw [hfun] at hd1
  have huniq := hd1.unique hd2
  simpa using huniq

/-- **Exact tangent rigidity of the open chain.**

A shell operator generating a one-parameter unitary group that commutes with a shell operator with
invertible, somewhere field-rigid couplings is a real multiple of that operator plus a real multiple
of the identity. -/
theorem exists_scalar_of_unitary_group_commute (hm : 2 ≤ m) (p0 : ShellParam m)
    (hJdet : ∀ v : Fin m, IsUnit (Matrix.det (p0.2.2 v)))
    (v0 : Fin m) (hrigid : FieldRigid (p0.2.2 v0))
    {A : ShellMat m} (hA : A ∈ chainShell m)
    (hexp : ∀ s : ℝ, NormedSpace.exp (s • ((-Complex.I) • A)) * shellMap m p0 =
      shellMap m p0 * NormedSpace.exp (s • ((-Complex.I) • A))) :
    ∃ lam mu : ℝ, A = lam • shellMap m p0 + mu • (1 : ShellMat m) := by
  have hcomm0 := commute_of_exp_smul_commute (shellMap m p0) ((-Complex.I) • A) hexp
  have hcomm : shellMap m p0 * A = A * shellMap m p0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul] at hcomm0
    have hI : (-Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
    exact (smul_right_injective (ShellMat m) hI hcomm0).symm
  exact (commute_shellMap_iff hm p0 hJdet v0 hrigid hA).mp hcomm

end GaloisForLFunctions.HTGeometry
