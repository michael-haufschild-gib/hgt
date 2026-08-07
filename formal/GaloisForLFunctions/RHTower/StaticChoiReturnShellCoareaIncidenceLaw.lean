import GaloisForLFunctions.HTGeometry.ReplicaReturnShellCoareaIncidenceLaw
import GaloisForLFunctions.RHTower.LagResolvedStaticChoiShortcutDichotomyLaw

/-!
# Static-Choi return-shell coarea incidence law

The lag-resolved shortcut split removes the component of every circuit target
along its permitted orbit anchor.  Here the residual norm is computed exactly
and fed into the return-shell replica incidence theorem.  Approximate
longitudinal targets therefore pay the `r`th power of their remaining squared
norm; exact past-orbit targets pay zero.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Pythagorean identity for lag-resolved return removal.  For a normalized
target, remaining transverse squared norm is exactly one minus anchor
fidelity. -/
theorem norm_sq_staticChoiAnchorResidual_eq_one_sub_norm_sq_component
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (anchor : ℝ)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) :
    ‖staticChoiAnchorResidual energy anchor target‖ ^ 2 =
      1 - ‖staticChoiAnchorComponent energy anchor target‖ ^ 2 := by
  let a := staticChoiAnchorComponent energy anchor target •
    staticSpectralChoiVector d anchor energy
  let z := staticChoiAnchorResidual energy anchor target
  have horth : inner ℂ a z = 0 := by
    unfold a z
    rw [inner_smul_left, inner_staticChoiAnchorResidual_eq_zero hd]
    simp
  have hpy :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a z horth
  have hsum : a + z = target :=
    staticChoiTarget_eq_anchor_add_residual energy anchor target
  have ha : ‖a‖ = ‖staticChoiAnchorComponent energy anchor target‖ := by
    unfold a
    rw [norm_smul, staticSpectralChoiVector_norm hd, mul_one]
  rw [hsum, htarget, ha] at hpy
  dsimp [z] at hpy
  linarith

/-- Return-removed target family, with one anchor chosen for each occupied
target in each residual-radius shell. -/
def staticChoiReturnShellResidualTarget
    {d : ℕ} {B : Type*} (C : B → Type*)
    (energy : Fin d → ℝ)
    (anchor : ∀ b, C b → ℝ)
    (target : ∀ b, C b → EuclideanSpace ℂ (Fin d × Fin d))
    (b : B) (c : C b) : Fin d × Fin d → ℂ :=
  staticChoiAnchorResidual energy (anchor b c) (target b c)

/-- The exact residual identity converts a one-copy shell-radius cap into the
norm premise of the abstract coarea incidence law. -/
theorem norm_sq_staticChoiReturnShellResidualTarget_le
    {d : ℕ} (hd : 0 < d) {B : Type*} (C : B → Type*)
    (energy : Fin d → ℝ)
    (anchor : ∀ b, C b → ℝ)
    (target : ∀ b, C b → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ b c, ‖target b c‖ = 1)
    (radius : B → ℝ)
    (hradiusCap : ∀ b c,
      1 - ‖staticChoiAnchorComponent energy (anchor b c) (target b c)‖ ^ 2 ≤
        radius b)
    (b : B) (c : C b) :
    ‖WithLp.toLp 2
      (staticChoiReturnShellResidualTarget C energy anchor target b c)‖ ^ 2 ≤
        radius b := by
  change ‖staticChoiAnchorResidual energy (anchor b c) (target b c)‖ ^ 2 ≤
    radius b
  rw [norm_sq_staticChoiAnchorResidual_eq_one_sub_norm_sq_component
    hd energy (anchor b c) (htarget b c)]
  exact hradiusCap b c

/-- **Static-Choi quenched return-shell incidence capstone.**  After the
permitted return component is removed, complete residual capture is bounded
by one source integral.  Every source fibre sheet remains counted, duplicate
target labels within a shell are invisible, and each occupied shell is
weighted by the `r`th power of its exact transverse squared-radius. -/
theorem measure_completeStaticChoiReturnShellCapture_le_projectionMoment
    {X B : Type*} [MeasurableSpace X] [Fintype B]
    (μ : Measure X) [IsFiniteMeasure μ]
    {d : ℕ} (hd : 0 < d) {r : ℕ} (hr : 0 < r)
    (C : B → Type*) (energy : Fin d → ℝ)
    (anchor : ∀ b, C b → ℝ)
    (target : ∀ b, C b → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ b c, ‖target b c‖ = 1)
    (state : X → Fin d × Fin d → ℂ)
    (radius : B → ℝ) (hradius : ∀ b, 0 ≤ radius b)
    (hradiusCap : ∀ b c,
      1 - ‖staticChoiAnchorComponent energy (anchor b c) (target b c)‖ ^ 2 ≤
        radius b)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hint : Integrable
      (fun x => replicaReturnShellProjectionMass r C
        (staticChoiReturnShellResidualTarget C energy anchor target)
        radius (state x)) μ) :
    μ.real {x | ∃ b, ∃ c,
      threshold ≤ finitePureStateFidelity (state x)
        (staticChoiReturnShellResidualTarget C energy anchor target b c)} ≤
      (∫ x, replicaReturnShellProjectionMass r C
        (staticChoiReturnShellResidualTarget C energy anchor target)
        radius (state x) ∂μ) / threshold ^ r := by
  exact measure_completePureStateReturnShellCapture_le_projectionMoment
    μ hr C (staticChoiReturnShellResidualTarget C energy anchor target)
      state radius hradius
      (norm_sq_staticChoiReturnShellResidualTarget_le
        hd C energy anchor target htarget radius hradiusCap)
      threshold hthreshold hint

end RHTower
