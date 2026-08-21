import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The trilinear cancellation class and its anticommutator realization

This file formalises §3.1–§3.2 of Boudourides, *Hodge Coercivity and Global Dynamics in Two-Field
Edge-Cochain Systems with MHD-Type Cancellation* (arXiv:2608.19360).

A continuous bilinear interaction `B : V × V → V` belongs to the *cancellation class* when the
trilinear form `b(a,b,c) = ⟨B(a,b), c⟩` is antisymmetric in its last two slots (equation (4)).
The consequences recorded here are the pointwise identity `b(a,b,b) = 0`, the two-field energy
neutrality (9), the closure of the class under linear combinations and orthogonal restriction,
and the quantitative estimates (8) and (10).

## Main results

* `IsCancelling` — equation (4).
* `IsCancelling.inner_self_eq_zero`, `IsCancelling.energy_cancel` — equation (9).
* `IsCancelling.add`, `IsCancelling.smul`, `isCancelling_projectedInteraction` — the closure
  properties of §3.2.
* `isCancelling_anticommutatorInteraction` — **Proposition 1**: for a self-adjoint bilinear
  family `S` and a skew-adjoint `J`, the projected anticommutator `P (S(a) J + J S(a)) b` is
  an admissible interaction.
* `norm_diagAnticommutatorInteraction_le` — estimate (8) for the diagonal realization
  `D(a) J + J D(a)` on `EuclideanSpace`.
* `eq_zero_of_symmetric_of_cancelling` — **Remark 1** in sharp form: a symmetric family can
  satisfy (4) only by vanishing identically, which is why the commutator `D(a)J - JD(a)` fails.
* `IsCancelling.norm_sub_le`, `IsCancelling.norm_quadratic_sub_le` — estimates (10) and §3.4.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry.HodgeEdgeCochain

/-! ## Finite-dimensional bilinear maps -/

section Bilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimension every bilinear map is automatically a continuous bilinear map. -/
noncomputable def bilinearCLM (Bl : E →ₗ[ℝ] E →ₗ[ℝ] E) : E →L[ℝ] E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := E)).toLinearMap.comp Bl)

@[simp] theorem bilinearCLM_apply (Bl : E →ₗ[ℝ] E →ₗ[ℝ] E) (a b : E) :
    bilinearCLM Bl a b = Bl a b := rfl

end Bilinear

/-! ## The cancellation class -/

section Cancelling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equation (4).**  The trilinear form `b(a,b,c) = ⟨B(a,b), c⟩` of a continuous bilinear
interaction is antisymmetric in its last two arguments. -/
def IsCancelling (B : E →L[ℝ] E →L[ℝ] E) : Prop :=
  ∀ a b c : E, ⟪B a b, c⟫_ℝ = -⟪B a c, b⟫_ℝ

variable {B B₁ B₂ : E →L[ℝ] E →L[ℝ] E}

/-- `b(a,b,b) = 0`: the diagonal of the trilinear form vanishes. -/
theorem IsCancelling.inner_self_eq_zero (hB : IsCancelling B) (a b : E) :
    ⟪B a b, b⟫_ℝ = 0 := by
  have h := hB a b b
  linarith

/-- **Equation (9).**  The two-field nonlinearity `N(u,h)` is energy neutral. -/
theorem IsCancelling.energy_cancel (hB : IsCancelling B) (u h : E) :
    ⟪B u u - B h h, u⟫_ℝ + ⟪B u h - B h u, h⟫_ℝ = 0 := by
  rw [inner_sub_left, inner_sub_left]
  have h1 : ⟪B u u, u⟫_ℝ = 0 := hB.inner_self_eq_zero u u
  have h2 : ⟪B u h, h⟫_ℝ = 0 := hB.inner_self_eq_zero u h
  have h3 : ⟪B h h, u⟫_ℝ = -⟪B h u, h⟫_ℝ := hB h h u
  rw [h1, h2, h3]
  ring

/-- The cancellation class is closed under sums. -/
theorem IsCancelling.add (h₁ : IsCancelling B₁) (h₂ : IsCancelling B₂) :
    IsCancelling (B₁ + B₂) := by
  intro a b c
  have e₁ := h₁ a b c
  have e₂ := h₂ a b c
  simp only [add_apply, inner_add_left]
  rw [e₁, e₂]
  ring

/-- The cancellation class is closed under scalar multiples. -/
theorem IsCancelling.smul (hB : IsCancelling B) (r : ℝ) : IsCancelling (r • B) := by
  intro a b c
  have e := hB a b c
  simp only [smul_apply, real_inner_smul_left]
  rw [e]
  ring

/-- Hence the class is closed under arbitrary linear combinations `α B₁ + γ B₂`. -/
theorem IsCancelling.linear_combination (h₁ : IsCancelling B₁) (h₂ : IsCancelling B₂)
    (α γ : ℝ) : IsCancelling (α • B₁ + γ • B₂) := (h₁.smul α).add (h₂.smul γ)

/-- **Estimate (8).**  A continuous bilinear interaction is bounded by its operator norm. -/
theorem norm_interaction_le (B : E →L[ℝ] E →L[ℝ] E) (a b : E) :
    ‖B a b‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ := B.le_opNorm₂ a b

/-- **Estimate (10).**  Bilinearity gives the local Lipschitz estimate. -/
theorem norm_interaction_sub_le (B : E →L[ℝ] E →L[ℝ] E) (a b c d : E) :
    ‖B a b - B c d‖ ≤ ‖B‖ * (‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖) := by
  have hsplit : B a b - B c d = B (a - c) b + B c (b - d) := by
    simp [map_sub]
  calc ‖B a b - B c d‖ = ‖B (a - c) b + B c (b - d)‖ := by rw [hsplit]
    _ ≤ ‖B (a - c) b‖ + ‖B c (b - d)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖a - c‖ * ‖b‖ + ‖B‖ * ‖c‖ * ‖b - d‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ = ‖B‖ * (‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖) := by ring

/-- **§3.4.**  On a ball of radius `R` the quadratic term is Lipschitz with constant `2‖B‖R`. -/
theorem norm_interaction_diag_sub_le (B : E →L[ℝ] E →L[ℝ] E) {a c : E} {R : ℝ}
    (ha : ‖a‖ ≤ R) (hc : ‖c‖ ≤ R) :
    ‖B a a - B c c‖ ≤ 2 * ‖B‖ * R * ‖a - c‖ := by
  have hR : 0 ≤ R := le_trans (norm_nonneg a) ha
  have hb := norm_interaction_sub_le B a a c c
  have hnn : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have h1 : ‖B‖ * (‖a - c‖ * ‖a‖ + ‖c‖ * ‖a - c‖) ≤ 2 * ‖B‖ * R * ‖a - c‖ := by
    have : ‖a - c‖ * ‖a‖ + ‖c‖ * ‖a - c‖ ≤ 2 * R * ‖a - c‖ := by
      nlinarith [norm_nonneg (a - c), norm_nonneg a, norm_nonneg c]
    nlinarith [norm_nonneg (a - c)]
  linarith

/-- **Estimate (10) for the mixed pair.** -/
theorem norm_interaction_mixed_sub_le (B : E →L[ℝ] E →L[ℝ] E) {a b c d : E} {R : ℝ}
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) (_hd : ‖d‖ ≤ R) :
    ‖B a b - B c d‖ ≤ ‖B‖ * R * (‖a - c‖ + ‖b - d‖) := by
  have hR : 0 ≤ R := le_trans (norm_nonneg a) ha
  have hbb := norm_interaction_sub_le B a b c d
  have hnn : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have : ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ ≤ R * (‖a - c‖ + ‖b - d‖) := by
    nlinarith [norm_nonneg (a - c), norm_nonneg (b - d)]
  nlinarith

end Cancelling

/-! ## Skew-adjoint realizations -/

section Realization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A family of operators is *skew* when each member is skew-symmetric. -/
def IsSkewFamily (M : E →L[ℝ] E →L[ℝ] E) : Prop :=
  ∀ a x y : E, ⟪M a x, y⟫_ℝ = -⟪x, M a y⟫_ℝ

/-- A family of operators is *symmetric* when each member is symmetric. -/
def IsSymmFamily (M : E →L[ℝ] E →L[ℝ] E) : Prop :=
  ∀ a x y : E, ⟪M a x, y⟫_ℝ = ⟪x, M a y⟫_ℝ

/-- The projected interaction `B(a,b) = P M(a) b` on a subspace `W`. -/
noncomputable def projectedBil (W : Submodule ℝ E) (M : E →L[ℝ] E →L[ℝ] E) :
    ↥W →ₗ[ℝ] ↥W →ₗ[ℝ] ↥W where
  toFun a :=
    { toFun := fun b => W.orthogonalProjectionOnto (M (a : E) (b : E))
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  map_add' := by intro x y; ext b; simp
  map_smul' := by intro c x; ext b; simp

/-- The projected interaction, as a continuous bilinear map on `W`. -/
noncomputable def projectedInteraction (W : Submodule ℝ E) (M : E →L[ℝ] E →L[ℝ] E) :
    ↥W →L[ℝ] ↥W →L[ℝ] ↥W := bilinearCLM (projectedBil W M)

@[simp] theorem projectedInteraction_apply (W : Submodule ℝ E) (M : E →L[ℝ] E →L[ℝ] E)
    (a b : ↥W) :
    ((projectedInteraction W M a b : ↥W) : E) = W.starProjection (M (a : E) (b : E)) := by
  rfl

/-- **The cancellation mechanism.**  Projecting a skew family onto a subspace produces an
interaction in the cancellation class.  This covers both the anticommutator realization of §3.1
and the orthogonal-restriction closure of §3.2. -/
theorem isCancelling_projectedInteraction (W : Submodule ℝ E) {M : E →L[ℝ] E →L[ℝ] E}
    (hM : IsSkewFamily M) : IsCancelling (projectedInteraction W M) := by
  intro a b c
  have hproj : ∀ x : E, ∀ w : ↥W, ⟪W.starProjection x, (w : E)⟫_ℝ = ⟪x, (w : E)⟫_ℝ := by
    intro x w
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr w.2]
  rw [Submodule.coe_inner, Submodule.coe_inner, projectedInteraction_apply,
    projectedInteraction_apply, hproj, hproj, hM (a : E) (b : E) (c : E),
    real_inner_comm (b : E) (M (a : E) (c : E))]

/-- The anticommutator family `M(a) = S(a) J + J S(a)`. -/
noncomputable def anticommutatorBil (S : E →L[ℝ] E →L[ℝ] E) (J : E →L[ℝ] E) :
    E →ₗ[ℝ] E →ₗ[ℝ] E where
  toFun a :=
    { toFun := fun b => S a (J b) + J (S a b)
      map_add' := by intro x y; simp; abel
      map_smul' := by intro c x; simp [smul_add] }
  map_add' := by intro x y; ext b; simp; abel
  map_smul' := by intro c x; ext b; simp [smul_add]

/-- The anticommutator family, as a continuous bilinear map. -/
noncomputable def anticommutator (S : E →L[ℝ] E →L[ℝ] E) (J : E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] E := bilinearCLM (anticommutatorBil S J)

@[simp] theorem anticommutator_apply (S : E →L[ℝ] E →L[ℝ] E) (J : E →L[ℝ] E) (a b : E) :
    anticommutator S J a b = S a (J b) + J (S a b) := rfl

/-- The commutator family `S(a) J - J S(a)`. -/
noncomputable def commutatorBil (S : E →L[ℝ] E →L[ℝ] E) (J : E →L[ℝ] E) :
    E →ₗ[ℝ] E →ₗ[ℝ] E where
  toFun a :=
    { toFun := fun b => S a (J b) - J (S a b)
      map_add' := by intro x y; simp; abel
      map_smul' := by intro c x; simp [smul_sub] }
  map_add' := by intro x y; ext b; simp; abel
  map_smul' := by intro c x; ext b; simp [smul_sub]

/-- The commutator family, as a continuous bilinear map. -/
noncomputable def commutatorFamily (S : E →L[ℝ] E →L[ℝ] E) (J : E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] E := bilinearCLM (commutatorBil S J)

@[simp] theorem commutatorFamily_apply (S : E →L[ℝ] E →L[ℝ] E) (J : E →L[ℝ] E) (a b : E) :
    commutatorFamily S J a b = S a (J b) - J (S a b) := rfl

/-- **Proposition 1 (skewness).**  For a symmetric family `S` and a skew operator `J` the
anticommutator `S(a) J + J S(a)` is skew. -/
theorem isSkewFamily_anticommutator {S : E →L[ℝ] E →L[ℝ] E} {J : E →L[ℝ] E}
    (hS : IsSymmFamily S) (hJ : ∀ x y : E, ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ) :
    IsSkewFamily (anticommutator S J) := by
  intro a x y
  rw [anticommutator_apply, inner_add_left, hS a (J x) y, hJ x (S a y), hJ (S a x) y,
    hS a x (J y), anticommutator_apply, inner_add_right]
  ring

/-- **Remark 1.**  For a symmetric family `S` and a skew operator `J` the *commutator*
`S(a) J - J S(a)` is symmetric. -/
theorem isSymmFamily_commutator {S : E →L[ℝ] E →L[ℝ] E} {J : E →L[ℝ] E}
    (hS : IsSymmFamily S) (hJ : ∀ x y : E, ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ) :
    IsSymmFamily (commutatorFamily S J) := by
  intro a x y
  rw [commutatorFamily_apply, inner_sub_left, hS a (J x) y, hJ x (S a y), hJ (S a x) y,
    hS a x (J y), commutatorFamily_apply, inner_sub_right]
  ring

omit [FiniteDimensional ℝ E] in
/-- **Remark 1, sharp form.**  A symmetric family can satisfy the trilinear cancellation identity
only by vanishing identically.  Hence the ordinary commutator can never supply a nontrivial
admissible interaction. -/
theorem eq_zero_of_symmFamily_of_cancelling {M : E →L[ℝ] E →L[ℝ] E}
    (hM : IsSymmFamily M) (hc : ∀ a b c : E, ⟪M a b, c⟫_ℝ = -⟪M a c, b⟫_ℝ) (a b : E) :
    M a b = 0 := by
  have key : ∀ c : E, ⟪M a b, c⟫_ℝ = 0 := by
    intro c
    have h1 := hc a b c
    have h2 : ⟪M a c, b⟫_ℝ = ⟪M a b, c⟫_ℝ := by
      rw [hM a c b, real_inner_comm]
    linarith
  have := key (M a b)
  exact inner_self_eq_zero.mp this

/-- **Proposition 1.**  The projected anticommutator is an admissible interaction. -/
theorem isCancelling_anticommutatorInteraction (W : Submodule ℝ E) {S : E →L[ℝ] E →L[ℝ] E}
    {J : E →L[ℝ] E} (hS : IsSymmFamily S) (hJ : ∀ x y : E, ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ) :
    IsCancelling (projectedInteraction W (anticommutator S J)) :=
  isCancelling_projectedInteraction W (isSkewFamily_anticommutator hS hJ)

/-- **§3.2 (orthogonal restriction).**  Restricting an admissible interaction to a subspace by
orthogonal projection preserves admissibility. -/
theorem isCancelling_restrict (W : Submodule ℝ E) {B : E →L[ℝ] E →L[ℝ] E}
    (hB : IsCancelling B) : IsCancelling (projectedInteraction W B) := by
  refine isCancelling_projectedInteraction W ?_
  intro a x y
  rw [hB a x y, real_inner_comm x (B a y)]

end Realization

/-! ## The explicit diagonal realization of Proposition 1 -/

section Diagonal

variable {ι : Type*} [Fintype ι]

/-- `D(a) b = (a₁b₁, …, a_m b_m)`: multiplication by the coordinate vector `a` in an oriented
edge basis.  This is the diagonal matrix `D(a) = diag(a₁, …, a_m)` of Proposition 1. -/
noncomputable def diagBil :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun a :=
    { toFun := fun b => (WithLp.toLp 2 (fun i => a i * b i) : EuclideanSpace ℝ ι)
      map_add' := by intro x y; ext i; simp [PiLp.add_apply]; ring
      map_smul' := by intro c x; ext i; simp [PiLp.smul_apply]; ring }
  map_add' := by intro x y; ext b i; simp [PiLp.add_apply]; ring
  map_smul' := by intro c x; ext b i; simp [PiLp.smul_apply]; ring

/-- The diagonal family, as a continuous bilinear map. -/
noncomputable def diagOp (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  bilinearCLM (diagBil (ι := ι))

@[simp] theorem diagOp_apply (a b : EuclideanSpace ℝ ι) (i : ι) :
    (diagOp ι a b) i = a i * b i := rfl

/-- `D(a)` is symmetric. -/
theorem isSymmFamily_diagOp : IsSymmFamily (diagOp ι) := by
  intro a x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, diagOp_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `‖D(a) b‖ ≤ ‖a‖ ‖b‖`: the diagonal operator is bounded by the Euclidean norm of its
symbol. -/
theorem norm_diagOp_apply_le (a b : EuclideanSpace ℝ ι) :
    ‖diagOp ι a b‖ ≤ ‖a‖ * ‖b‖ := by
  have hcoord : ∀ i : ι, (a i) ^ 2 ≤ ‖a‖ ^ 2 := by
    intro i
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun j => (a j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hsq : ‖diagOp ι a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq b,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [diagOp_apply, mul_pow]
    exact mul_le_mul_of_nonneg_right (hcoord i) (sq_nonneg (b i))
  have h1 : (0 : ℝ) ≤ ‖a‖ * ‖b‖ := mul_nonneg (norm_nonneg a) (norm_nonneg b)
  nlinarith [norm_nonneg (diagOp ι a b)]

/-- **Proposition 1 (explicit realization).**  For a skew-symmetric `J`, the projected
anticommutator `B(a,b) = P (D(a) J + J D(a)) b` is an admissible interaction. -/
theorem isCancelling_diagAnticommutatorInteraction (W : Submodule ℝ (EuclideanSpace ℝ ι))
    {J : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    (hJ : ∀ x y : EuclideanSpace ℝ ι, ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ) :
    IsCancelling (projectedInteraction W (anticommutator (diagOp ι) J)) :=
  isCancelling_anticommutatorInteraction W isSymmFamily_diagOp hJ

/-- **Estimate (8).**  `‖B(a,b)‖ ≤ 2 ‖J‖ ‖a‖ ‖b‖` for the diagonal anticommutator realization. -/
theorem norm_diagAnticommutatorInteraction_le (W : Submodule ℝ (EuclideanSpace ℝ ι))
    (J : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (a b : ↥W) :
    ‖projectedInteraction W (anticommutator (diagOp ι) J) a b‖ ≤ 2 * ‖J‖ * ‖a‖ * ‖b‖ := by
  have hcoe : ‖projectedInteraction W (anticommutator (diagOp ι) J) a b‖
      = ‖W.starProjection (anticommutator (diagOp ι) J (a : EuclideanSpace ℝ ι)
          (b : EuclideanSpace ℝ ι))‖ := rfl
  have hproj := W.norm_starProjection_apply_le
    (anticommutator (diagOp ι) J (a : EuclideanSpace ℝ ι) (b : EuclideanSpace ℝ ι))
  have h1 : ‖diagOp ι (a : EuclideanSpace ℝ ι) (J (b : EuclideanSpace ℝ ι))‖
      ≤ ‖a‖ * (‖J‖ * ‖b‖) := by
    refine le_trans (norm_diagOp_apply_le _ _) ?_
    exact mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg (a : EuclideanSpace ℝ ι))
  have h2 : ‖J (diagOp ι (a : EuclideanSpace ℝ ι) (b : EuclideanSpace ℝ ι))‖
      ≤ ‖J‖ * (‖a‖ * ‖b‖) := by
    refine le_trans (J.le_opNorm _) ?_
    exact mul_le_mul_of_nonneg_left (norm_diagOp_apply_le _ _) (norm_nonneg J)
  have hM : ‖anticommutator (diagOp ι) J (a : EuclideanSpace ℝ ι)
      (b : EuclideanSpace ℝ ι)‖ ≤ 2 * ‖J‖ * ‖a‖ * ‖b‖ := by
    rw [anticommutator_apply]
    calc ‖diagOp ι (a : EuclideanSpace ℝ ι) (J (b : EuclideanSpace ℝ ι))
          + J (diagOp ι (a : EuclideanSpace ℝ ι) (b : EuclideanSpace ℝ ι))‖
        ≤ ‖diagOp ι (a : EuclideanSpace ℝ ι) (J (b : EuclideanSpace ℝ ι))‖
          + ‖J (diagOp ι (a : EuclideanSpace ℝ ι) (b : EuclideanSpace ℝ ι))‖ := norm_add_le _ _
      _ ≤ ‖a‖ * (‖J‖ * ‖b‖) + ‖J‖ * (‖a‖ * ‖b‖) := add_le_add h1 h2
      _ = 2 * ‖J‖ * ‖a‖ * ‖b‖ := by ring
  rw [hcoe]
  linarith

end Diagonal

end GaloisForLFunctions.HTGeometry.HodgeEdgeCochain
