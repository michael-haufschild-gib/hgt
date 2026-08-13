import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Lattice.Nat

/-!
# Resource-filtered relation rank, recurrence, and tidal acceleration

This module formalizes the algebraic rank floor, its attained generic value, the exact recurrence
obstruction to a monotone continuous observable, and the initial normal acceleration of an
operator-exponential orbit.  These are the dependency-closed parts of the
resource-filtered-relation card that do not depend on the still-missing real-analytic zero-set
measure theorem or bipartite matrix cross-fibre infrastructure.
-/

namespace HTGeometry.ConstraintRelativity

open Filter Topology

/-! ## Conserved full rank and resource-filtered rank -/

theorem finrank_inf_lower_bound
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (R Q : Submodule K V) :
    Module.finrank K R + Module.finrank K Q - Module.finrank K V ≤
      Module.finrank K (R ⊓ Q : Submodule K V) := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq R Q
  have hsup : Module.finrank K (R ⊔ Q : Submodule K V) ≤ Module.finrank K V :=
    Submodule.finrank_le _
  rw [Nat.sub_le_iff_le_add]
  calc
    Module.finrank K R + Module.finrank K Q =
        Module.finrank K (R ⊔ Q : Submodule K V) +
          Module.finrank K (R ⊓ Q : Submodule K V) := hdim.symm
    _ ≤ Module.finrank K V + Module.finrank K (R ⊓ Q : Submodule K V) :=
      Nat.add_le_add_right hsup _
    _ = Module.finrank K (R ⊓ Q : Submodule K V) + Module.finrank K V :=
      Nat.add_comm _ _

section RelationRank

variable {K V M : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The exact relation space transported by an invertible evolution. -/
noncomputable def transportedRelation (U : M → V ≃ₗ[K] V) (R₀ : Submodule K V) (x : M) :
    Submodule K V := Submodule.map (U x : V →ₗ[K] V) R₀

/-- Resource-visible relation rank `dim(U(x)R₀ ∩ Q)`. -/
noncomputable def accessibleRelationRank (U : M → V ≃ₗ[K] V)
    (R₀ Q : Submodule K V) (x : M) : ℕ :=
  Module.finrank K (transportedRelation U R₀ x ⊓ Q : Submodule K V)

/-- The attained minimum resource-visible relation rank. -/
noncomputable def genericAccessibleRank (U : M → V ≃ₗ[K] V)
    (R₀ Q : Submodule K V) : ℕ :=
  sInf (Set.range (accessibleRelationRank U R₀ Q))

omit [FiniteDimensional K V] in
/-- **Card Theorem 2.1, conserved full rank.** Invertible evolution preserves exact relation rank. -/
theorem finrank_transportedRelation (U : M → V ≃ₗ[K] V) (R₀ : Submodule K V) (x : M) :
    Module.finrank K (transportedRelation U R₀ x) = Module.finrank K R₀ := by
  exact LinearEquiv.finrank_map_eq (U x) R₀

/-- **Card Theorem 2.1(1).** Every accessible rank obeys the Grassmann lower bound. -/
theorem accessibleRelationRank_lower_bound (U : M → V ≃ₗ[K] V)
    (R₀ Q : Submodule K V) (x : M) :
    Module.finrank K R₀ + Module.finrank K Q - Module.finrank K V ≤
      accessibleRelationRank U R₀ Q x := by
  rw [accessibleRelationRank, ← finrank_transportedRelation U R₀ x]
  exact finrank_inf_lower_bound (transportedRelation U R₀ x) Q

omit [FiniteDimensional K V] in
/-- The minimum defining `genericAccessibleRank` is attained. -/
theorem exists_accessibleRelationRank_eq_generic [Nonempty M]
    (U : M → V ≃ₗ[K] V) (R₀ Q : Submodule K V) :
    ∃ x, accessibleRelationRank U R₀ Q x = genericAccessibleRank U R₀ Q := by
  have hrange : (Set.range (accessibleRelationRank U R₀ Q)).Nonempty := Set.range_nonempty _
  obtain ⟨x, hx⟩ := Nat.sInf_mem hrange
  exact ⟨x, hx⟩

omit [FiniteDimensional K V] in
/-- Every visible rank lies above the attained generic rank. -/
theorem genericAccessibleRank_le [Nonempty M] (U : M → V ≃ₗ[K] V)
    (R₀ Q : Submodule K V) (x : M) :
    genericAccessibleRank U R₀ Q ≤ accessibleRelationRank U R₀ Q x :=
  Nat.sInf_le ⟨x, rfl⟩

/-- The generic rank obeys the same Grassmann lower bound. -/
theorem genericAccessibleRank_lower_bound [Nonempty M] (U : M → V ≃ₗ[K] V)
    (R₀ Q : Submodule K V) :
    Module.finrank K R₀ + Module.finrank K Q - Module.finrank K V ≤
      genericAccessibleRank U R₀ Q := by
  obtain ⟨x, hx⟩ := exists_accessibleRelationRank_eq_generic U R₀ Q
  rw [← hx]
  exact accessibleRelationRank_lower_bound U R₀ Q x

/-- **Card Theorem 2.1(5).** One transverse orbit point forces the generic rank to attain the
dimensionally allowed minimum. -/
theorem genericAccessibleRank_eq_lowerBound_of_exists_transverse [Nonempty M]
    (U : M → V ≃ₗ[K] V) (R₀ Q : Submodule K V)
    (h : ∃ x, accessibleRelationRank U R₀ Q x =
      Module.finrank K R₀ + Module.finrank K Q - Module.finrank K V) :
    genericAccessibleRank U R₀ Q =
      Module.finrank K R₀ + Module.finrank K Q - Module.finrank K V := by
  obtain ⟨x, hx⟩ := h
  apply le_antisymm
  · simpa [hx] using genericAccessibleRank_le U R₀ Q x
  · exact genericAccessibleRank_lower_bound U R₀ Q

end RelationRank

/-! ## Continuous visibility -/

/-- Finite-dimensional soft visibility `Tr(P_R(x) P_Q)` in orthonormal coordinates. -/
def softVisibility {X n : Type*} [Fintype n] [DecidableEq n]
    (P_R : X → Matrix n n ℝ) (P_Q : Matrix n n ℝ) (x : X) : ℝ :=
  Matrix.trace (P_R x * P_Q)

/-- **Card §3.** Soft visibility is continuous whenever the moving projection is continuous. -/
theorem continuous_softVisibility
    {X n : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n]
    (P_R : X → Matrix n n ℝ) (P_Q : Matrix n n ℝ) (hP : Continuous P_R) :
    Continuous (softVisibility P_R P_Q) := by
  unfold softVisibility
  fun_prop

/-! ## Recurrence forbids a nonconstant monotone law -/

/-- **Card Theorem 4.1.** On a recurrent forward orbit, a continuous observable that is monotone
in time is constant.  An additive `NNReal` action is the exact algebraic semiflow law; continuity
of the action is not needed once recurrence of the chosen orbit is supplied. -/
theorem recurrence_no_go
    {X : Type*} [TopologicalSpace X] [AddAction NNReal X]
    (C : X → ℝ) (x : X) (t : ℕ → NNReal)
    (ht : Tendsto t atTop atTop)
    (hrec : Tendsto (fun j => t j +ᵥ x) atTop (nhds x))
    (hC : ContinuousAt C x)
    (hmono : Monotone (fun s : NNReal => C (s +ᵥ x))) :
    ∀ s : NNReal, C (s +ᵥ x) = C x := by
  intro s
  apply le_antisymm
  · have hlim : Tendsto (fun j => C (t j +ᵥ x)) atTop (nhds (C x)) :=
      hC.tendsto.comp hrec
    refine ge_of_tendsto hlim ?_
    filter_upwards [ht.eventually (eventually_ge_atTop s)] with j hj
    exact hmono hj
  · calc
      C x = C ((0 : NNReal) +ᵥ x) := by rw [zero_vadd]
      _ ≤ C (s +ᵥ x) := hmono (bot_le : (0 : NNReal) ≤ s)

/-! ## Exact normal acceleration -/

open scoped RealInnerProductSpace

/-- A zero-based differentiable curve has squared-norm second derivative twice the squared norm of
its initial velocity. -/
theorem secondDeriv_norm_sq_of_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (y y' : ℝ → H) (y'' : H)
    (hy : ∀ t, HasDerivAt y (y' t) t)
    (hy' : HasDerivAt y' y'' 0)
    (hy0 : y 0 = 0) :
    deriv (deriv (fun t => ‖y t‖ ^ 2)) 0 = 2 * ‖y' 0‖ ^ 2 := by
  have hfirst : deriv (fun t => ‖y t‖ ^ 2) = fun t => 2 * inner ℝ (y t) (y' t) := by
    funext t
    exact (hy t).norm_sq.deriv
  rw [hfirst]
  have hinner := (hy 0).inner ℝ hy'
  have hmul := hinner.const_mul 2
  rw [hy0, inner_zero_left, zero_add, real_inner_self_eq_norm_sq] at hmul
  exact hmul.deriv

section Tidal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The bounded-generator orbit `e^{tA}x`. -/
noncomputable def operatorOrbit (A : H →L[ℝ] H) (x : H) (t : ℝ) : H :=
  NormedSpace.exp (t • A) x

theorem hasDerivAt_operatorOrbit (A : H →L[ℝ] H) (x : H) (t : ℝ) :
    HasDerivAt (operatorOrbit A x) (A (operatorOrbit A x t)) t := by
  change HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A) x)
    (A (NormedSpace.exp (t • A) x)) t
  have he := hasDerivAt_exp_smul_const' A t
  have hx : HasDerivAt (fun _ : ℝ => x) 0 t := hasDerivAt_const t x
  simpa using he.clm_apply hx

/-- Hidden weight vector `(I-P)e^{tA}x`, expressed as projection to `Lᗮ`. -/
noncomputable def normalOrbit (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (A : H →L[ℝ] H) (x : H) (t : ℝ) : H :=
  Lᗮ.starProjection (operatorOrbit A x t)

theorem hasDerivAt_normalOrbit (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (A : H →L[ℝ] H) (x : H) (t : ℝ) :
    HasDerivAt (normalOrbit L A x) (Lᗮ.starProjection (A (operatorOrbit A x t))) t := by
  change HasDerivAt (fun u : ℝ => Lᗮ.starProjection (operatorOrbit A x u))
    (Lᗮ.starProjection (A (operatorOrbit A x t))) t
  have hp : HasDerivAt (fun _ : ℝ => Lᗮ.starProjection) 0 t :=
    hasDerivAt_const t Lᗮ.starProjection
  simpa using hp.clm_apply (hasDerivAt_operatorOrbit A x t)

omit [CompleteSpace H] in
theorem normalOrbit_zero (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (A : H →L[ℝ] H) {x : H} (hx : x ∈ L) : normalOrbit L A x 0 = 0 := by
  simp [normalOrbit, operatorOrbit, Submodule.starProjection_orthogonal,
    Submodule.starProjection_eq_self_iff.mpr hx]

/-- **Card Theorem 5.1, `(5.2)`.** Initial hidden-weight acceleration is exactly twice the squared
normal component of the generator. -/
theorem normalAcceleration (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (A : H →L[ℝ] H) {x : H} (hx : x ∈ L) :
    deriv (deriv (fun t => ‖normalOrbit L A x t‖ ^ 2)) 0 =
      2 * ‖Lᗮ.starProjection (A x)‖ ^ 2 := by
  have hA : HasDerivAt (fun t => A (operatorOrbit A x t)) (A (A x)) 0 := by
    have hconst : HasDerivAt (fun _ : ℝ => A) 0 0 := hasDerivAt_const 0 A
    simpa [operatorOrbit] using hconst.clm_apply (hasDerivAt_operatorOrbit A x 0)
  have hp : HasDerivAt
      (fun t => Lᗮ.starProjection (A (operatorOrbit A x t)))
      (Lᗮ.starProjection (A (A x))) 0 := by
    have hconst : HasDerivAt (fun _ : ℝ => Lᗮ.starProjection) 0 0 :=
      hasDerivAt_const 0 Lᗮ.starProjection
    simpa using hconst.clm_apply hA
  have h := secondDeriv_norm_sq_of_eq_zero
    (normalOrbit L A x)
    (fun t => Lᗮ.starProjection (A (operatorOrbit A x t)))
    (Lᗮ.starProjection (A (A x)))
    (hasDerivAt_normalOrbit L A x) hp (normalOrbit_zero L A hx)
  simpa [operatorOrbit] using h

/-- Intrinsic skew-adjointness condition for a bounded real Hilbert-space generator. -/
def IsSkewAdjointGenerator (A : H →L[ℝ] H) : Prop :=
  ∀ u v, inner ℝ (A u) v = -inner ℝ u (A v)

/-- A bounded skew-adjoint generator preserves squared norm along its exponential orbit. -/
theorem operatorOrbit_norm_sq_eq (A : H →L[ℝ] H) (hA : IsSkewAdjointGenerator A)
    (x : H) (t : ℝ) : ‖operatorOrbit A x t‖ ^ 2 = ‖x‖ ^ 2 := by
  let f : ℝ → ℝ := fun s => ‖operatorOrbit A x s‖ ^ 2
  have hf : Differentiable ℝ f := fun s => (hasDerivAt_operatorOrbit A x s).norm_sq.differentiableAt
  have hderiv : ∀ s, deriv f s = 0 := by
    intro s
    rw [(hasDerivAt_operatorOrbit A x s).norm_sq.deriv]
    have hzero : inner ℝ (operatorOrbit A x s) (A (operatorOrbit A x s)) = 0 := by
      have hskew := hA (operatorOrbit A x s) (operatorOrbit A x s)
      have hsymm : inner ℝ (operatorOrbit A x s) (A (operatorOrbit A x s)) =
          inner ℝ (A (operatorOrbit A x s)) (operatorOrbit A x s) :=
        real_inner_comm _ _
      linarith [hskew, hsymm]
    rw [hzero, mul_zero]
  have hconst := is_const_of_deriv_eq_zero hf hderiv t 0
  simpa [f, operatorOrbit] using hconst

/-- Visible component `P e^{tA}x`. -/
noncomputable def visibleOrbit (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (A : H →L[ℝ] H) (x : H) (t : ℝ) : H :=
  L.starProjection (operatorOrbit A x t)

/-- **Card Theorem 5.1, `(5.3)`.** Visible weight has negative twice-normal acceleration for a
skew-adjoint generator. -/
theorem visibleAcceleration (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (A : H →L[ℝ] H) (hA : IsSkewAdjointGenerator A) {x : H} (hx : x ∈ L) :
    deriv (deriv (fun t => ‖visibleOrbit L A x t‖ ^ 2)) 0 =
      -2 * ‖Lᗮ.starProjection (A x)‖ ^ 2 := by
  have hvisible :
      (fun t => ‖visibleOrbit L A x t‖ ^ 2) =
        fun t => ‖x‖ ^ 2 - ‖normalOrbit L A x t‖ ^ 2 := by
    funext t
    have hpyth := L.norm_sq_eq_add_norm_sq_starProjection (operatorOrbit A x t)
    have hnorm := operatorOrbit_norm_sq_eq A hA x t
    dsimp [visibleOrbit, normalOrbit]
    linarith
  rw [hvisible, deriv_const_sub']
  change deriv (-(deriv (fun t => ‖normalOrbit L A x t‖ ^ 2))) 0 = _
  rw [deriv.neg]
  rw [normalAcceleration L A hx]
  ring

end Tidal

end HTGeometry.ConstraintRelativity
