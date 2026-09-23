import GaloisForLFunctions.HTGeometry.KroneckerAmplification

/-!
# Isometry of matrix amplification by an identity ancilla

Kronecker amplification by a nonempty identity ancilla preserves the Euclidean operator norm.
The upper bound is the blockwise estimate from `KroneckerAmplification`.  For the lower bound,
embed the original Euclidean space isometrically into one fixed ancilla coordinate and observe that
the amplified operator restricts there to the original operator.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d n : Type*} [Fintype d] [DecidableEq d] [Fintype n] [DecidableEq n]

/-- Isometric inclusion into one fixed ancilla coordinate. -/
def euclideanAncillaEmbed (a : n) :
    EuclideanSpace ℂ d →ₗᵢ[ℂ] EuclideanSpace ℂ (d × n) where
  toFun x := (EuclideanSpace.equiv (d × n) ℂ).symm fun p =>
    if p.2 = a then x.ofLp p.1 else 0
  map_add' x y := by
    apply (EuclideanSpace.equiv (d × n) ℂ).injective
    ext p
    by_cases hp : p.2 = a <;> simp [hp]
  map_smul' c x := by
    apply (EuclideanSpace.equiv (d × n) ℂ).injective
    ext p
    by_cases hp : p.2 = a <;> simp [hp]
  norm_map' x := by
    change ‖(EuclideanSpace.equiv (d × n) ℂ).symm
      (fun p => if p.2 = a then x.ofLp p.1 else 0)‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_euclideanOfFun]
    change (∑ p : d × n, ‖if p.2 = a then x.ofLp p.1 else 0‖ ^ (2 : ℕ)) = ‖x‖ ^ (2 : ℕ)
    rw [Fintype.sum_prod_type]
    have hinner : ∀ i : d,
        (∑ b : n, ‖if b = a then x.ofLp i else 0‖ ^ (2 : ℕ)) = ‖x.ofLp i‖ ^ (2 : ℕ) := by
      intro i
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hba
        simp [hba]
      · exact fun ha => (ha (Finset.mem_univ a)).elim
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i]
    simpa using (norm_sq_euclideanOfFun x.ofLp).symm

omit [DecidableEq d] in
@[simp] theorem euclideanAncillaEmbed_apply
    (a : n) (x : EuclideanSpace ℂ d) (p : d × n) :
    (euclideanAncillaEmbed a x).ofLp p = if p.2 = a then x.ofLp p.1 else 0 := by
  rfl

/-- The amplified matrix intertwines the fixed-coordinate inclusion with the original matrix. -/
theorem toEuclideanCLM_kronecker_one_euclideanAncillaEmbed
    (A : Matrix d d ℂ) (a : n) (x : EuclideanSpace ℂ d) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix n n ℂ))
        (euclideanAncillaEmbed a x) =
      euclideanAncillaEmbed a (Matrix.toEuclideanCLM (𝕜 := ℂ) A x) := by
  ext p
  rcases p with ⟨i, b⟩
  rw [Matrix.ofLp_toEuclideanCLM, kronecker_one_mulVec]
  change (A *ᵥ fun l => if b = a then x.ofLp l else 0) i =
    if b = a then (Matrix.toEuclideanCLM (𝕜 := ℂ) A x).ofLp i else 0
  by_cases hba : b = a
  · subst b
    simp [Matrix.ofLp_toEuclideanCLM]
  · simp [Matrix.mulVec, dotProduct, hba]

/-- Amplification by a nonempty identity ancilla cannot decrease the operator norm. -/
theorem l2_opNorm_le_kronecker_one [Nonempty n] (A : Matrix d d ℂ) :
    ‖A‖ ≤ ‖A ⊗ₖ (1 : Matrix n n ℂ)‖ := by
  let a : n := Classical.arbitrary n
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) A
  let S := Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ (1 : Matrix n n ℂ))
  have hTS : ‖T‖ ≤ ‖S‖ := by
    refine T.opNorm_le_bound (norm_nonneg _) fun x => ?_
    calc
      ‖T x‖ = ‖euclideanAncillaEmbed a (T x)‖ :=
        (euclideanAncillaEmbed a).norm_map _ |>.symm
      _ = ‖S (euclideanAncillaEmbed a x)‖ := by
        rw [toEuclideanCLM_kronecker_one_euclideanAncillaEmbed]
      _ ≤ ‖S‖ * ‖euclideanAncillaEmbed a x‖ := S.le_opNorm _
      _ = ‖S‖ * ‖x‖ := by rw [(euclideanAncillaEmbed a).norm_map]
  calc
    ‖A‖ = ‖T‖ := (Matrix.l2_opNorm_toEuclideanCLM A).symm
    _ ≤ ‖S‖ := hTS
    _ = ‖A ⊗ₖ (1 : Matrix n n ℂ)‖ := Matrix.l2_opNorm_toEuclideanCLM _

/-- Kronecker amplification by a nonempty identity ancilla is isometric. -/
theorem l2_opNorm_kronecker_one [Nonempty n] (A : Matrix d d ℂ) :
    ‖A ⊗ₖ (1 : Matrix n n ℂ)‖ = ‖A‖ :=
  le_antisymm (l2_opNorm_kronecker_one_le A) (l2_opNorm_le_kronecker_one A)

end

end GaloisForLFunctions.HTGeometry
