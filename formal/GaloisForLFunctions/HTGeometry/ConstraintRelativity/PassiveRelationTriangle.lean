import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Passive relation triangles

Raw-flat unitary transport between three Hilbert spaces acquires selected holonomy after
orthogonal projection at each observer.  This file proves the exact three-leak Gauss law, energy
telescoping, work/holonomy identity, sharp universal norm bound, flatness criterion, and cofinal
vanishing law.
-/

namespace HTGeometry.ConstraintRelativity

open Filter Topology

open scoped ComplexConjugate

/-- A raw-flat passive unitary triangle with an observer-selected subspace at each vertex. -/
structure PassiveRelationTriangle
    (H₀ H₁ H₂ : Type*)
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] where
  L₀ : Submodule ℂ H₀
  L₁ : Submodule ℂ H₁
  L₂ : Submodule ℂ H₂
  projectable₀ : L₀.HasOrthogonalProjection
  projectable₁ : L₁.HasOrthogonalProjection
  projectable₂ : L₂.HasOrthogonalProjection
  U₀ : H₀ ≃ₗᵢ[ℂ] H₁
  U₁ : H₁ ≃ₗᵢ[ℂ] H₂
  U₂ : H₂ ≃ₗᵢ[ℂ] H₀
  rawFlat : ∀ x, U₂ (U₁ (U₀ x)) = x

namespace PassiveRelationTriangle

variable {H₀ H₁ H₂ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- **Card Proposition 2.1, cyclic spectrum.** Rectangular cyclic products have identical
characteristic determinants, hence identical nonzero eigenvalues with algebraic multiplicity. -/
theorem det_one_sub_smul_mul_comm
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (t : ℂ) (A : Matrix m n ℂ) (B : Matrix n m ℂ) :
    Matrix.det (1 - t • (A * B)) = Matrix.det (1 - t • (B * A)) := by
  simpa only [Matrix.smul_mul, Matrix.mul_smul] using
    Matrix.det_one_sub_mul_comm (t • A) B

noncomputable def stage₁ (T : PassiveRelationTriangle H₀ H₁ H₂) (x : H₀) : H₁ := by
  letI := T.projectable₁
  exact T.L₁.starProjection (T.U₀ x)

noncomputable def stage₂ (T : PassiveRelationTriangle H₀ H₁ H₂) (x : H₀) : H₂ := by
  letI := T.projectable₂
  exact T.L₂.starProjection (T.U₁ (T.stage₁ x))

noncomputable def cycleOutput (T : PassiveRelationTriangle H₀ H₁ H₂) (x : H₀) : H₀ := by
  letI := T.projectable₀
  exact T.L₀.starProjection (T.U₂ (T.stage₂ x))

/-- Selected cycle `P₀U₂P₂U₁P₁U₀P₀`. -/
noncomputable def selectedHolonomy (T : PassiveRelationTriangle H₀ H₁ H₂) (x : H₀) : H₀ := by
  letI := T.projectable₀
  exact T.cycleOutput (T.L₀.starProjection x)

/-- First relation leak `(I-P₁)U₀x`. -/
noncomputable def leakA (T : PassiveRelationTriangle H₀ H₁ H₂) (x : H₀) : H₁ := by
  letI := T.projectable₁
  exact T.L₁ᗮ.starProjection (T.U₀ x)

/-- Second relation leak `(I-P₂)U₁P₁U₀x`. -/
noncomputable def leakB (T : PassiveRelationTriangle H₀ H₁ H₂) (x : H₀) : H₂ := by
  letI := T.projectable₂
  exact T.L₂ᗮ.starProjection (T.U₁ (T.stage₁ x))

/-- Third relation leak `(I-P₀)U₂P₂U₁P₁U₀x`. -/
noncomputable def leakC (T : PassiveRelationTriangle H₀ H₁ H₂) (x : H₀) : H₀ := by
  letI := T.projectable₀
  exact T.L₀ᗮ.starProjection (T.U₂ (T.stage₂ x))

/-- Selected holonomy defect `Ωx=x-Hx`. -/
noncomputable def omega (T : PassiveRelationTriangle H₀ H₁ H₂) (x : H₀) : H₀ :=
  x - T.selectedHolonomy x

/-- Total relation-leak energy. -/
noncomputable def work (T : PassiveRelationTriangle H₀ H₁ H₂) (x : H₀) : ℝ :=
  ‖T.leakA x‖ ^ (2 : ℕ) + ‖T.leakB x‖ ^ (2 : ℕ) + ‖T.leakC x‖ ^ (2 : ℕ)

theorem selectedHolonomy_of_mem (T : PassiveRelationTriangle H₀ H₁ H₂)
    {x : H₀} (hx : x ∈ T.L₀) : T.selectedHolonomy x = T.cycleOutput x := by
  letI := T.projectable₀
  simp [selectedHolonomy, Submodule.starProjection_eq_self_iff.mpr hx]

/-- **Card `(3.1)`.** Selected holonomy defect is the transported sum of the three ordered leaks. -/
theorem omega_eq_transported_leaks (T : PassiveRelationTriangle H₀ H₁ H₂)
    {x : H₀} (hx : x ∈ T.L₀) :
    T.omega x = T.U₂ (T.U₁ (T.leakA x)) + T.U₂ (T.leakB x) + T.leakC x := by
  letI := T.projectable₀
  letI := T.projectable₁
  letI := T.projectable₂
  have h₁ : T.U₀ x = T.stage₁ x + T.leakA x := by
    simpa [stage₁, leakA] using
      (T.L₁.starProjection_add_starProjection_orthogonal (T.U₀ x)).symm
  have h₂ : T.U₁ (T.stage₁ x) = T.stage₂ x + T.leakB x := by
    simpa [stage₂, leakB] using
      (T.L₂.starProjection_add_starProjection_orthogonal (T.U₁ (T.stage₁ x))).symm
  have h₃ : T.U₂ (T.stage₂ x) = T.cycleOutput x + T.leakC x := by
    simpa [cycleOutput, leakC] using
      (T.L₀.starProjection_add_starProjection_orthogonal (T.U₂ (T.stage₂ x))).symm
  rw [omega, selectedHolonomy_of_mem T hx]
  nth_rewrite 1 [← T.rawFlat x]
  rw [h₁, map_add, map_add, h₂, map_add, h₃]
  abel

/-- **Card `(3.2)`.** Three Pythagorean losses telescope to selected-cycle contraction. -/
theorem work_eq_norm_sq_sub_norm_sq_holonomy
    (T : PassiveRelationTriangle H₀ H₁ H₂) {x : H₀} (hx : x ∈ T.L₀) :
    T.work x = ‖x‖ ^ (2 : ℕ) - ‖T.selectedHolonomy x‖ ^ (2 : ℕ) := by
  letI := T.projectable₀
  letI := T.projectable₁
  letI := T.projectable₂
  have h₁ := T.L₁.norm_sq_eq_add_norm_sq_starProjection (T.U₀ x)
  have h₂ := T.L₂.norm_sq_eq_add_norm_sq_starProjection (T.U₁ (T.stage₁ x))
  have h₃ := T.L₀.norm_sq_eq_add_norm_sq_starProjection (T.U₂ (T.stage₂ x))
  simp only [LinearIsometryEquiv.norm_map] at h₁ h₂ h₃
  rw [show T.L₁.starProjection (T.U₀ x) = T.stage₁ x by rfl,
    show T.L₁ᗮ.starProjection (T.U₀ x) = T.leakA x by rfl] at h₁
  rw [show T.L₂.starProjection (T.U₁ (T.stage₁ x)) = T.stage₂ x by rfl,
    show T.L₂ᗮ.starProjection (T.U₁ (T.stage₁ x)) = T.leakB x by rfl] at h₂
  rw [show T.L₀.starProjection (T.U₂ (T.stage₂ x)) = T.cycleOutput x by rfl,
    show T.L₀ᗮ.starProjection (T.U₂ (T.stage₂ x)) = T.leakC x by rfl,
    ← selectedHolonomy_of_mem T hx] at h₃
  dsimp [work]
  linarith

/-- **Card `(3.3)`.** Work is determined by contraction against the oriented holonomy defect. -/
theorem work_eq_two_re_inner_omega_sub_norm_sq
    (T : PassiveRelationTriangle H₀ H₁ H₂) {x : H₀} (hx : x ∈ T.L₀) :
    T.work x = 2 * RCLike.re (inner ℂ x (T.omega x)) - ‖T.omega x‖ ^ (2 : ℕ) := by
  have henergy := T.work_eq_norm_sq_sub_norm_sq_holonomy hx
  have hhol : T.selectedHolonomy x = x - T.omega x := by
    simp [omega]
  have hnorm := norm_sub_sq (𝕜 := ℂ) x (T.omega x)
  rw [hhol] at henergy
  linarith

theorem norm_omega_le_sum_leaks (T : PassiveRelationTriangle H₀ H₁ H₂)
    {x : H₀} (hx : x ∈ T.L₀) :
    ‖T.omega x‖ ≤ ‖T.leakA x‖ + ‖T.leakB x‖ + ‖T.leakC x‖ := by
  rw [T.omega_eq_transported_leaks hx]
  calc
    ‖T.U₂ (T.U₁ (T.leakA x)) + T.U₂ (T.leakB x) + T.leakC x‖
        ≤ ‖T.U₂ (T.U₁ (T.leakA x)) + T.U₂ (T.leakB x)‖ + ‖T.leakC x‖ :=
      norm_add_le _ _
    _ ≤ (‖T.U₂ (T.U₁ (T.leakA x))‖ + ‖T.U₂ (T.leakB x)‖) + ‖T.leakC x‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
    _ = ‖T.leakA x‖ + ‖T.leakB x‖ + ‖T.leakC x‖ := by simp

/-- **Card `(3.4)`.** Universal three-port bound `‖Ωx‖² ≤ 3W(x)`. -/
theorem norm_omega_sq_le_three_mul_work
    (T : PassiveRelationTriangle H₀ H₁ H₂) {x : H₀} (hx : x ∈ T.L₀) :
    ‖T.omega x‖ ^ (2 : ℕ) ≤ 3 * T.work x := by
  have hnorm := T.norm_omega_le_sum_leaks hx
  have hsum_nonneg :
      0 ≤ ‖T.leakA x‖ + ‖T.leakB x‖ + ‖T.leakC x‖ :=
    add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hsquare := (sq_le_sq₀ (norm_nonneg (T.omega x)) hsum_nonneg).2 hnorm
  have hthree :
      (‖T.leakA x‖ + ‖T.leakB x‖ + ‖T.leakC x‖) ^ (2 : ℕ) ≤
        3 * (‖T.leakA x‖ ^ (2 : ℕ) + ‖T.leakB x‖ ^ (2 : ℕ) + ‖T.leakC x‖ ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (‖T.leakA x‖ - ‖T.leakB x‖),
      sq_nonneg (‖T.leakB x‖ - ‖T.leakC x‖),
      sq_nonneg (‖T.leakC x‖ - ‖T.leakA x‖)]
  dsimp [work]
  exact hsquare.trans hthree

/-- Selected cycle is flat exactly when every leak vanishes. -/
theorem selectedHolonomy_eq_iff_leaks_eq_zero
    (T : PassiveRelationTriangle H₀ H₁ H₂) {x : H₀} (hx : x ∈ T.L₀) :
    T.selectedHolonomy x = x ↔
      T.leakA x = 0 ∧ T.leakB x = 0 ∧ T.leakC x = 0 := by
  constructor
  · intro hflat
    have hwork := T.work_eq_norm_sq_sub_norm_sq_holonomy hx
    rw [hflat, sub_self] at hwork
    have ha : ‖T.leakA x‖ ^ (2 : ℕ) = 0 := by
      dsimp [work] at hwork
      nlinarith [sq_nonneg ‖T.leakA x‖, sq_nonneg ‖T.leakB x‖,
        sq_nonneg ‖T.leakC x‖]
    have hb : ‖T.leakB x‖ ^ (2 : ℕ) = 0 := by
      dsimp [work] at hwork
      nlinarith [sq_nonneg ‖T.leakA x‖, sq_nonneg ‖T.leakB x‖,
        sq_nonneg ‖T.leakC x‖]
    have hc : ‖T.leakC x‖ ^ (2 : ℕ) = 0 := by
      dsimp [work] at hwork
      nlinarith [sq_nonneg ‖T.leakA x‖, sq_nonneg ‖T.leakB x‖,
        sq_nonneg ‖T.leakC x‖]
    exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp ha),
      norm_eq_zero.mp (sq_eq_zero_iff.mp hb),
      norm_eq_zero.mp (sq_eq_zero_iff.mp hc)⟩
  · rintro ⟨ha, hb, hc⟩
    have hgauss := T.omega_eq_transported_leaks hx
    rw [ha, hb, hc, map_zero, map_zero, add_zero] at hgauss
    have homega : T.omega x = 0 := by simpa using hgauss
    simpa [omega] using (sub_eq_zero.mp homega).symm

/-- **Card Corollary 3.3.** Uniformly vanishing leaks force selected holonomy defect to vanish. -/
theorem omega_tendsto_zero_of_leaks
    {ι : Type*} {l : Filter ι}
    (T : ι → PassiveRelationTriangle H₀ H₁ H₂) (x : ι → H₀)
    (hx : ∀ n, x n ∈ (T n).L₀)
    (ha : Tendsto (fun n => (T n).leakA (x n)) l (𝓝 0))
    (hb : Tendsto (fun n => (T n).leakB (x n)) l (𝓝 0))
    (hc : Tendsto (fun n => (T n).leakC (x n)) l (𝓝 0)) :
    Tendsto (fun n => (T n).omega (x n)) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg ((T n).omega (x n)))
    (Eventually.of_forall fun n => (T n).norm_omega_le_sum_leaks (hx n)) ?_
  simpa using ((tendsto_norm_zero.comp ha).add (tendsto_norm_zero.comp hb)).add
    (tendsto_norm_zero.comp hc)

section FrameCovariance

variable {H₀' H₁' H₂' : Type*}
  [NormedAddCommGroup H₀'] [InnerProductSpace ℂ H₀']
  [NormedAddCommGroup H₁'] [InnerProductSpace ℂ H₁']
  [NormedAddCommGroup H₂'] [InnerProductSpace ℂ H₂']

/-- Gauge transport of a passive triangle by vertexwise unitaries. -/
noncomputable def gaugeTransport (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') :
    PassiveRelationTriangle H₀' H₁' H₂' where
  L₀ := T.L₀.map (g₀.toLinearEquiv : H₀ →ₗ[ℂ] H₀')
  L₁ := T.L₁.map (g₁.toLinearEquiv : H₁ →ₗ[ℂ] H₁')
  L₂ := T.L₂.map (g₂.toLinearEquiv : H₂ →ₗ[ℂ] H₂')
  projectable₀ := by
    letI := T.projectable₀
    infer_instance
  projectable₁ := by
    letI := T.projectable₁
    infer_instance
  projectable₂ := by
    letI := T.projectable₂
    infer_instance
  U₀ := (g₀.symm.trans T.U₀).trans g₁
  U₁ := (g₁.symm.trans T.U₁).trans g₂
  U₂ := (g₂.symm.trans T.U₂).trans g₀
  rawFlat x := by simp [LinearIsometryEquiv.trans_apply, T.rawFlat]

@[simp] theorem gaugeTransport_L₀ (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') :
    (T.gaugeTransport g₀ g₁ g₂).L₀ = T.L₀.map (g₀.toLinearEquiv : H₀ →ₗ[ℂ] H₀') := rfl

@[simp] theorem gaugeTransport_L₁ (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') :
    (T.gaugeTransport g₀ g₁ g₂).L₁ = T.L₁.map (g₁.toLinearEquiv : H₁ →ₗ[ℂ] H₁') := rfl

@[simp] theorem gaugeTransport_L₂ (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') :
    (T.gaugeTransport g₀ g₁ g₂).L₂ = T.L₂.map (g₂.toLinearEquiv : H₂ →ₗ[ℂ] H₂') := rfl

@[simp] theorem gaugeTransport_U₀_apply (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₀') :
    (T.gaugeTransport g₀ g₁ g₂).U₀ x = g₁ (T.U₀ (g₀.symm x)) := by
  rfl

@[simp] theorem gaugeTransport_U₁_apply (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₁') :
    (T.gaugeTransport g₀ g₁ g₂).U₁ x = g₂ (T.U₁ (g₁.symm x)) := by
  rfl

@[simp] theorem gaugeTransport_U₂_apply (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₂') :
    (T.gaugeTransport g₀ g₁ g₂).U₂ x = g₀ (T.U₂ (g₂.symm x)) := by
  rfl

@[simp]
theorem gaugeTransport_stage₁ (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₀) :
    (T.gaugeTransport g₀ g₁ g₂).stage₁ (g₀ x) = g₁ (T.stage₁ x) := by
  letI := T.projectable₁
  simp [stage₁, LinearIsometryEquiv.trans_apply,
    Submodule.starProjection_map_apply]

@[simp]
theorem gaugeTransport_stage₂ (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₀) :
    (T.gaugeTransport g₀ g₁ g₂).stage₂ (g₀ x) = g₂ (T.stage₂ x) := by
  letI := T.projectable₁
  letI := T.projectable₂
  simp [stage₂, Submodule.starProjection_map_apply]

@[simp]
theorem gaugeTransport_cycleOutput (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₀) :
    (T.gaugeTransport g₀ g₁ g₂).cycleOutput (g₀ x) = g₀ (T.cycleOutput x) := by
  letI := T.projectable₀
  letI := T.projectable₁
  letI := T.projectable₂
  simp [cycleOutput, Submodule.starProjection_map_apply]

/-- **Card Proposition 2.1, covariance.** Selected holonomy is conjugated by vertex gauge. -/
@[simp]
theorem gaugeTransport_selectedHolonomy (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₀) :
    (T.gaugeTransport g₀ g₁ g₂).selectedHolonomy (g₀ x) =
      g₀ (T.selectedHolonomy x) := by
  letI := T.projectable₀
  letI := T.projectable₁
  letI := T.projectable₂
  simp [selectedHolonomy, Submodule.starProjection_map_apply]

@[simp]
theorem gaugeTransport_leakA (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₀) :
    (T.gaugeTransport g₀ g₁ g₂).leakA (g₀ x) = g₁ (T.leakA x) := by
  letI := T.projectable₁
  simp [leakA, ← Submodule.map_orthogonal_equiv, Submodule.starProjection_map_apply]

@[simp]
theorem gaugeTransport_leakB (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₀) :
    (T.gaugeTransport g₀ g₁ g₂).leakB (g₀ x) = g₂ (T.leakB x) := by
  letI := T.projectable₁
  letI := T.projectable₂
  simp [leakB, ← Submodule.map_orthogonal_equiv, Submodule.starProjection_map_apply]

@[simp]
theorem gaugeTransport_leakC (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₀) :
    (T.gaugeTransport g₀ g₁ g₂).leakC (g₀ x) = g₀ (T.leakC x) := by
  letI := T.projectable₀
  letI := T.projectable₁
  letI := T.projectable₂
  simp [leakC, ← Submodule.map_orthogonal_equiv, Submodule.starProjection_map_apply]

/-- **Card Proposition 2.1, energy.** Each leakage norm and total work are gauge invariant. -/
theorem gaugeTransport_leak_norms_and_work (T : PassiveRelationTriangle H₀ H₁ H₂)
    (g₀ : H₀ ≃ₗᵢ[ℂ] H₀') (g₁ : H₁ ≃ₗᵢ[ℂ] H₁') (g₂ : H₂ ≃ₗᵢ[ℂ] H₂') (x : H₀) :
    ‖(T.gaugeTransport g₀ g₁ g₂).leakA (g₀ x)‖ = ‖T.leakA x‖ ∧
    ‖(T.gaugeTransport g₀ g₁ g₂).leakB (g₀ x)‖ = ‖T.leakB x‖ ∧
    ‖(T.gaugeTransport g₀ g₁ g₂).leakC (g₀ x)‖ = ‖T.leakC x‖ ∧
    (T.gaugeTransport g₀ g₁ g₂).work (g₀ x) = T.work x := by
  simp [work]

end FrameCovariance

end PassiveRelationTriangle

end HTGeometry.ConstraintRelativity
