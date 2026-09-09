import GaloisForLFunctions.RHTower.FokasLenellsExactLipschitz

/-!
# Exact anisotropic stability region

A joint bound using separate time and space weights holds precisely when
each weight dominates its actual initial generator norm. The full jump and
its Cauchy compression have the same admissible region of weights.
-/

namespace RHTower.FokasLenells
noncomputable section

private theorem two_parameter_norm_sub_le
    {E : Type*} [SeminormedAddCommGroup E]
    (T : ℝ → ℝ → E) (A B : ℝ)
    (ht : ∀ x s t, ‖T s x - T t x‖ ≤ A * ‖s-t‖)
    (hx : ∀ t x y, ‖T t x - T t y‖ ≤ B * ‖x-y‖)
    (t x s y : ℝ) :
    ‖T t x - T s y‖ ≤ A * ‖t-s‖ + B * ‖x-y‖ := by
  calc
    _ ≤ ‖T t x - T s x‖ + ‖T s x - T s y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (ht x t s) (hx s x y)

private theorem two_parameter_lipschitz_iff
    {E : Type*} [SeminormedAddCommGroup E]
    (T : ℝ → ℝ → E) (Kt Kx : ℝ)
    (ht : ∀ x L, (∀ s t, ‖T s x - T t x‖ ≤ L * ‖s-t‖) ↔ Kt ≤ L)
    (hx : ∀ t L, (∀ x y, ‖T t x - T t y‖ ≤ L * ‖x-y‖) ↔ Kx ≤ L)
    (A B : ℝ) :
    (∀ t x s y, ‖T t x - T s y‖ ≤ A * ‖t-s‖ + B * ‖x-y‖) ↔
      Kt ≤ A ∧ Kx ≤ B := by
  constructor
  · intro h
    constructor
    · apply (ht 0 A).1
      intro s t
      simpa using h s 0 t 0
    · apply (hx 0 B).1
      intro x y
      simpa using h 0 x 0 y
  · intro h
    exact two_parameter_norm_sub_le T A B
      (fun x => (ht x A).2 h.1) (fun t => (hx t B).2 h.2)

/-- The exact admissible time and space weights for joint stability of the actual directMultiplier. -/
theorem directMultiplier_joint_lipschitz_iff (q : SchwartzMap ℝ ℂ) (reverse : Bool) (A B : ℝ) :
    (∀ t x s y, ‖directMultiplier q t x reverse - directMultiplier q s y reverse‖ ≤
      A * ‖t-s‖ + B * ‖x-y‖) ↔ ‖directTimeMultiplier q 0 0 reverse‖ ≤ A ∧ ‖directSpaceMultiplier q 0 0 reverse‖ ≤ B :=
  two_parameter_lipschitz_iff (fun t x => directMultiplier q t x reverse) ‖directTimeMultiplier q 0 0 reverse‖ ‖directSpaceMultiplier q 0 0 reverse‖
    (fun x L => directMultiplier_time_lipschitz_iff q x reverse L)
    (fun t L => directMultiplier_space_lipschitz_iff q t reverse L) A B

/-- Joint operator stability with both independently optimal initial generator weights. -/
theorem norm_directMultiplier_joint_sub_le_initial_generators (q : SchwartzMap ℝ ℂ) (reverse : Bool) (t x s y : ℝ) :
    ‖directMultiplier q t x reverse - directMultiplier q s y reverse‖ ≤
      ‖directTimeMultiplier q 0 0 reverse‖ * ‖t-s‖ + ‖directSpaceMultiplier q 0 0 reverse‖ * ‖x-y‖ :=
  (directMultiplier_joint_lipschitz_iff q reverse ‖directTimeMultiplier q 0 0 reverse‖ ‖directSpaceMultiplier q 0 0 reverse‖).2 ⟨le_rfl, le_rfl⟩ t x s y

/-- The exact admissible time and space weights for joint stability of the actual directJumpPerturbation. -/
theorem directJumpPerturbation_joint_lipschitz_iff (q : SchwartzMap ℝ ℂ) (A B : ℝ) :
    (∀ t x s y, ‖directJumpPerturbation q t x - directJumpPerturbation q s y‖ ≤
      A * ‖t-s‖ + B * ‖x-y‖) ↔ ‖directJumpTimeOperator q 0 0‖ ≤ A ∧ ‖directJumpSpaceOperator q 0 0‖ ≤ B :=
  two_parameter_lipschitz_iff (fun t x => directJumpPerturbation q t x) ‖directJumpTimeOperator q 0 0‖ ‖directJumpSpaceOperator q 0 0‖
    (fun x L => directJumpPerturbation_time_lipschitz_iff q x L)
    (fun t L => directJumpPerturbation_space_lipschitz_iff q t L) A B

/-- Joint operator stability with both independently optimal initial generator weights. -/
theorem norm_directJumpPerturbation_joint_sub_le_initial_generators (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    ‖directJumpPerturbation q t x - directJumpPerturbation q s y‖ ≤
      ‖directJumpTimeOperator q 0 0‖ * ‖t-s‖ + ‖directJumpSpaceOperator q 0 0‖ * ‖x-y‖ :=
  (directJumpPerturbation_joint_lipschitz_iff q ‖directJumpTimeOperator q 0 0‖ ‖directJumpSpaceOperator q 0 0‖).2 ⟨le_rfl, le_rfl⟩ t x s y

/-- The exact admissible time and space weights for joint stability of the actual directCauchyOperator. -/
theorem directCauchyOperator_joint_lipschitz_iff (q : SchwartzMap ℝ ℂ) (A B : ℝ) :
    (∀ t x s y, ‖directCauchyOperator q t x - directCauchyOperator q s y‖ ≤
      A * ‖t-s‖ + B * ‖x-y‖) ↔ ‖directJumpTimeOperator q 0 0‖ ≤ A ∧ ‖directJumpSpaceOperator q 0 0‖ ≤ B :=
  two_parameter_lipschitz_iff (fun t x => directCauchyOperator q t x) ‖directJumpTimeOperator q 0 0‖ ‖directJumpSpaceOperator q 0 0‖
    (fun x L => directCauchyOperator_time_lipschitz_iff q x L)
    (fun t L => directCauchyOperator_space_lipschitz_iff q t L) A B

/-- Joint operator stability with both independently optimal initial generator weights. -/
theorem norm_directCauchyOperator_joint_sub_le_initial_generators (q : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    ‖directCauchyOperator q t x - directCauchyOperator q s y‖ ≤
      ‖directJumpTimeOperator q 0 0‖ * ‖t-s‖ + ‖directJumpSpaceOperator q 0 0‖ * ‖x-y‖ :=
  (directCauchyOperator_joint_lipschitz_iff q ‖directJumpTimeOperator q 0 0‖ ‖directJumpSpaceOperator q 0 0‖).2 ⟨le_rfl, le_rfl⟩ t x s y

/-- Cauchy compression has exactly the same region of joint Lipschitz weights as the full jump. -/
theorem directCauchyOperator_joint_lipschitz_iff_jump (q : SchwartzMap ℝ ℂ) (A B : ℝ) :
    (∀ t x s y, ‖directCauchyOperator q t x - directCauchyOperator q s y‖ ≤
      A * ‖t-s‖ + B * ‖x-y‖) ↔
    (∀ t x s y, ‖directJumpPerturbation q t x - directJumpPerturbation q s y‖ ≤
      A * ‖t-s‖ + B * ‖x-y‖) := by
  rw [directCauchyOperator_joint_lipschitz_iff, directJumpPerturbation_joint_lipschitz_iff]

end
end RHTower.FokasLenells
