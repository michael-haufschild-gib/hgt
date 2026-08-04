import GaloisForLFunctions.HTGeometry.PeriodicHomotopy

/-!
# Averaging over a period preserves smoothness

The derivative of the average of a map over a period is the average of its derivative, and the same
holds for the weighted average used by the homotopy operator.  So both operations raise the order of
differentiability by induction: a map of class `C^n` has average of class `C^n`, hence a smooth map
has smooth average.  Mathlib has differentiation under the integral sign but not this statement.

* `averageOp_contDiff` : the average of a map of class `C^n` is of class `C^n`.
* `weightHomotopy_contDiff` : the same for the weighted average.
* `averageOp_contDiff_infty`, `weightHomotopy_contDiff_infty` : the smooth case.
-/

set_option maxSynthPendingDepth 3

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ContDiff

section Smoothness

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ}

/-- The average of a continuous map is continuous. -/
theorem averageOp_continuous {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] {p : 𝕜} {β : (Fin r → 𝕜) → X} (hβ : Continuous β) (j : Fin r) :
    Continuous (averageOp p β j) := by
  refine continuous_parametric_unitIntegral ?_
  have hcurve : Continuous fun q : (Fin r → 𝕜) × ℝ => periodCurve p q.1 j q.2 := by
    show Continuous fun q : (Fin r → 𝕜) × ℝ =>
      q.1 + ((q.2 : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
    have hcast : Continuous fun q : (Fin r → 𝕜) × ℝ => ((q.2 : 𝕜) * p) :=
      (RCLike.continuous_ofReal.comp continuous_snd).mul continuous_const
    exact continuous_fst.add (hcast.smul continuous_const)
  exact hβ.comp hcurve

/-- The weighted average of a continuous map is continuous. -/
theorem weightHomotopy_continuous {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] {p : 𝕜} {γ : (Fin r → 𝕜) → X} (hγ : Continuous γ) (j : Fin r) :
    Continuous (weightHomotopy p γ j) := by
  refine continuous_parametric_unitIntegral ?_
  have hcurve : Continuous fun q : (Fin r → 𝕜) × ℝ => periodCurve p q.1 j q.2 := by
    show Continuous fun q : (Fin r → 𝕜) × ℝ =>
      q.1 + ((q.2 : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
    have hcast : Continuous fun q : (Fin r → 𝕜) × ℝ => ((q.2 : 𝕜) * p) :=
      (RCLike.continuous_ofReal.comp continuous_snd).mul continuous_const
    exact continuous_fst.add (hcast.smul continuous_const)
  have hweight : Continuous fun q : (Fin r → 𝕜) × ℝ => (1 : 𝕜) - ((q.2 : ℝ) : 𝕜) :=
    continuous_const.sub (RCLike.continuous_ofReal.comp continuous_snd)
  exact hweight.smul (hγ.comp hcurve)

end Smoothness

section ContDiff

variable {𝕜 : Type u} [RCLike 𝕜] {r : ℕ}

/-- **The average of a map of class `C^n` over a period is of class `C^n`.**  The derivative of the
average is the average of the derivative, so the statement follows by induction on the order. -/
theorem averageOp_contDiff (n : ℕ) : ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X]
    {β : (Fin r → 𝕜) → X} {p : 𝕜} (j : Fin r), ContDiff 𝕜 n β → ContDiff 𝕜 n (averageOp p β j) := by
  induction n with
  | zero =>
      intro X _ _ _ _ _ β p j hβ
      rw [Nat.cast_zero, contDiff_zero] at hβ ⊢
      exact averageOp_continuous hβ j
  | succ m ih =>
      intro X _ _ _ _ _ β p j hβ
      rw [Nat.cast_succ] at hβ ⊢
      rw [contDiff_succ_iff_fderiv (𝕜 := 𝕜) (f := β) (n := (m : WithTop ℕ∞))] at hβ
      obtain ⟨hdiff, -, hfd⟩ := hβ
      have hcont : Continuous (fderiv 𝕜 β) := hfd.continuous
      have hfderiv : fderiv 𝕜 (averageOp p β j) = averageOp p (fderiv 𝕜 β) j := by
        funext w
        exact (averageOp_hasFDerivAt hdiff hcont j w).fderiv
      rw [contDiff_succ_iff_fderiv (𝕜 := 𝕜) (f := averageOp p β j) (n := (m : WithTop ℕ∞))]
      refine ⟨averageOp_differentiable hdiff hcont j, ?_, ?_⟩
      · intro hω
        exact absurd hω (by simp)
      · rw [hfderiv]
        exact ih j hfd

/-- **The weighted average of a map of class `C^n` over a period is of class `C^n`.** -/
theorem weightHomotopy_contDiff (n : ℕ) : ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X]
    {γ : (Fin r → 𝕜) → X} {p : 𝕜} (j : Fin r),
    ContDiff 𝕜 n γ → ContDiff 𝕜 n (weightHomotopy p γ j) := by
  induction n with
  | zero =>
      intro X _ _ _ _ _ γ p j hγ
      rw [Nat.cast_zero, contDiff_zero] at hγ ⊢
      exact weightHomotopy_continuous hγ j
  | succ m ih =>
      intro X _ _ _ _ _ γ p j hγ
      rw [Nat.cast_succ] at hγ ⊢
      rw [contDiff_succ_iff_fderiv (𝕜 := 𝕜) (f := γ) (n := (m : WithTop ℕ∞))] at hγ
      obtain ⟨hdiff, -, hfd⟩ := hγ
      have hcont : Continuous (fderiv 𝕜 γ) := hfd.continuous
      have hfderiv : fderiv 𝕜 (weightHomotopy p γ j) = weightHomotopy p (fderiv 𝕜 γ) j := by
        funext w
        exact (weightHomotopy_hasFDerivAt hdiff hcont j w).fderiv
      rw [contDiff_succ_iff_fderiv (𝕜 := 𝕜) (f := weightHomotopy p γ j) (n := (m : WithTop ℕ∞))]
      refine ⟨weightHomotopy_differentiable hdiff hcont j, ?_, ?_⟩
      · intro hω
        exact absurd hω (by simp)
      · rw [hfderiv]
        exact ih j hfd

/-- **The average of a smooth map over a period is smooth.** -/
theorem averageOp_contDiff_infty {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X]
    {β : (Fin r → 𝕜) → X} {p : 𝕜} (j : Fin r) (hβ : ContDiff 𝕜 ∞ β) :
    ContDiff 𝕜 ∞ (averageOp p β j) :=
  contDiff_infty.2 fun n => averageOp_contDiff n j (contDiff_infty.1 hβ n)

/-- **The weighted average of a smooth map over a period is smooth.** -/
theorem weightHomotopy_contDiff_infty {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X]
    {γ : (Fin r → 𝕜) → X} {p : 𝕜} (j : Fin r) (hγ : ContDiff 𝕜 ∞ γ) :
    ContDiff 𝕜 ∞ (weightHomotopy p γ j) :=
  contDiff_infty.2 fun n => weightHomotopy_contDiff n j (contDiff_infty.1 hγ n)

end ContDiff

end GaloisForLFunctions.HTGeometry
