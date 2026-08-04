import GaloisForLFunctions.RHTower.DeningerAverageHomotopy

/-!
# Invariance under the period flow

Averaging over one period produces a map invariant under the whole translation flow in that
direction, because the integral of a periodic map over an interval of one period does not depend on
where the interval starts.  Averaging in one direction preserves invariance in the others, and a map
invariant in every coordinate direction has vanishing derivative, hence is constant.

* `deningerFlowInvariant` : invariance under translation along a coordinate period direction.
* `deningerAverageOp_flowInvariant` : the average is invariant in the direction it averages.
* `deningerConst_of_flowInvariant` : invariance in every direction forces constancy.
-/

namespace RHTower

open Complex

section FlowInvariance

variable {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **Invariance under the translation flow** in a coordinate period direction. -/
def deningerFlowInvariant (β : (Fin r → ℂ) → X) (j : Fin r) : Prop :=
  ∀ (t : ℝ) (w : Fin r → ℂ), β (deningerPeriodCurve w j t) = β w

/-- Composing two translations along the same period direction adds the parameters. -/
theorem deningerPeriodCurve_trans (w : Fin r → ℂ) (j : Fin r) (t s : ℝ) :
    deningerPeriodCurve (deningerPeriodCurve w j t) j s = deningerPeriodCurve w j (t + s) := by
  show w + ((t : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ) +
      ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ) =
    w + (((t + s : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
  rw [add_assoc, ← add_smul]
  congr 1
  push_cast
  ring_nf

/-- Translations along two coordinate period directions commute. -/
theorem deningerPeriodCurve_comm (w : Fin r → ℂ) (i j : Fin r) (t s : ℝ) :
    deningerPeriodCurve (deningerPeriodCurve w i t) j s =
      deningerPeriodCurve (deningerPeriodCurve w j s) i t := by
  show w + ((t : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single i (1 : ℂ) : Fin r → ℂ) +
      ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ) =
    w + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ) +
      ((t : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single i (1 : ℂ) : Fin r → ℂ)
  abel

/-- One step along a period direction is a translation by the period. -/
theorem deningerPeriodCurve_succ (w : Fin r → ℂ) (j : Fin r) (t : ℝ) :
    deningerPeriodCurve w j (t + 1) = deningerPeriodCurve w j t +
      (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
  show w + (((t + 1 : ℝ) : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ) =
    w + ((t : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ) +
      (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
  rw [add_assoc, ← add_smul]
  congr 1
  push_cast
  ring_nf

omit [CompleteSpace X] in
/-- **The average over a period is invariant under the flow in the direction it averages.** -/
theorem deningerAverageOp_flowInvariant {β : (Fin r → ℂ) → X} (j : Fin r)
    (hper : ∀ w : Fin r → ℂ,
      β (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = β w) :
    deningerFlowInvariant (deningerAverageOp β j) j := by
  intro t w
  have hg : Function.Periodic (fun u : ℝ => β (deningerPeriodCurve w j u)) 1 := by
    intro u
    show β (deningerPeriodCurve w j (u + 1)) = β (deningerPeriodCurve w j u)
    rw [deningerPeriodCurve_succ, hper]
  show (∫ s in (0 : ℝ)..1, β (deningerPeriodCurve (deningerPeriodCurve w j t) j s)) =
    ∫ s in (0 : ℝ)..1, β (deningerPeriodCurve w j s)
  have hshift : (∫ s in (0 : ℝ)..1, β (deningerPeriodCurve (deningerPeriodCurve w j t) j s)) =
      ∫ s in (0 : ℝ)..1, (fun u : ℝ => β (deningerPeriodCurve w j u)) (t + s) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    show β (deningerPeriodCurve (deningerPeriodCurve w j t) j s) =
      β (deningerPeriodCurve w j (t + s))
    rw [deningerPeriodCurve_trans]
  rw [hshift, intervalIntegral.integral_comp_add_left
    (fun u : ℝ => β (deningerPeriodCurve w j u)) t, add_zero]
  have hper' := hg.intervalIntegral_add_eq t 0
  rw [zero_add] at hper'
  exact hper'

omit [CompleteSpace X] in
/-- **Averaging in one direction preserves invariance in the others.** -/
theorem deningerAverageOp_flowInvariant_of {β : (Fin r → ℂ) → X} {i : Fin r} (j : Fin r)
    (hinv : deningerFlowInvariant β i) : deningerFlowInvariant (deningerAverageOp β j) i := by
  intro t w
  show (∫ s in (0 : ℝ)..1, β (deningerPeriodCurve (deningerPeriodCurve w i t) j s)) =
    ∫ s in (0 : ℝ)..1, β (deningerPeriodCurve w j s)
  refine intervalIntegral.integral_congr fun s _ => ?_
  show β (deningerPeriodCurve (deningerPeriodCurve w i t) j s) = β (deningerPeriodCurve w j s)
  rw [deningerPeriodCurve_comm, hinv t]

omit [CompleteSpace X] in
/-- An invariant map has vanishing derivative in the direction of invariance. -/
theorem deningerFderiv_period_eq_zero {β : (Fin r → ℂ) → X} (hdiff : Differentiable ℂ β)
    {j : Fin r} (hinv : deningerFlowInvariant β j) (w : Fin r → ℂ) :
    (fderiv ℂ β w) ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = 0 := by
  have hconst : (fun t : ℝ => β (deningerPeriodCurve w j t)) = fun _ : ℝ => β w := by
    funext t
    exact hinv t w
  have hzero : HasDerivAt (fun t : ℝ => β (deningerPeriodCurve w j t)) 0 0 := by
    rw [hconst]
    exact hasDerivAt_const _ _
  have hchain : HasDerivAt (fun t : ℝ => β (deningerPeriodCurve w j t))
      ((fderiv ℂ β (deningerPeriodCurve w j 0))
        ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ))) 0 := by
    have hfd := (hdiff (deningerPeriodCurve w j 0)).hasFDerivAt
    exact (hfd.restrictScalars ℝ).comp_hasDerivAt 0 (deningerPeriodCurve_hasDerivAt w j 0)
  rw [deningerPeriodCurve_zero] at hchain
  exact hchain.unique hzero

omit [CompleteSpace X] in
/-- A continuous linear map vanishing on the coordinate vectors vanishes. -/
theorem deningerCLM_eq_zero_of_single {L : (Fin r → ℂ) →L[ℂ] X}
    (h : ∀ j : Fin r, L (Pi.single j (1 : ℂ) : Fin r → ℂ) = 0) : L = 0 := by
  classical
  refine ContinuousLinearMap.ext fun u => ?_
  have hbasis : ∀ j : Fin r,
      (fun l => if j = l then (1 : ℂ) else 0) = (Pi.single j (1 : ℂ) : Fin r → ℂ) := by
    intro j
    funext l
    rw [Pi.single_apply]
    by_cases hl : j = l
    · rw [if_pos hl, if_pos hl.symm]
    · rw [if_neg hl, if_neg (Ne.symm hl)]
  conv_lhs => rw [show u = ∑ j, u j • (fun l => if j = l then (1 : ℂ) else 0) from pi_eq_sum_univ u]
  rw [_root_.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, hbasis j, h j, smul_zero]

omit [CompleteSpace X] in
/-- **A map invariant under the flow in every coordinate direction is constant.** -/
theorem deningerConst_of_flowInvariant {β : (Fin r → ℂ) → X} (hdiff : Differentiable ℂ β)
    (hinv : ∀ j : Fin r, deningerFlowInvariant β j) (w w' : Fin r → ℂ) : β w = β w' := by
  have htwopi : (2 * Real.pi * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hfd : ∀ y : Fin r → ℂ, fderiv ℂ β y = 0 := by
    intro y
    refine deningerCLM_eq_zero_of_single fun j => ?_
    have hsmul := deningerFderiv_period_eq_zero hdiff (hinv j) y
    rw [map_smul] at hsmul
    have hscale := congrArg (fun x : X => (2 * Real.pi * Complex.I)⁻¹ • x) hsmul
    show (fderiv ℂ β y) (Pi.single j (1 : ℂ) : Fin r → ℂ) = 0
    rw [smul_smul, inv_mul_cancel₀ htwopi, one_smul, smul_zero] at hscale
    exact hscale
  exact is_const_of_fderiv_eq_zero hdiff hfd w w'

end FlowInvariance

end RHTower
