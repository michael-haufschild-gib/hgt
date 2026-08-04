import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.RCLike.Basic

/-!
# Averaging over a period on a coordinate space

For a map on a finite coordinate space over `ℝ` or `ℂ` and a nonzero period in one coordinate
direction, the average over one period is again defined on the whole space, is differentiable with
the average of the derivative, preserves periodicity in every coordinate, and is invariant under the
whole translation flow in the averaged direction.  A map invariant under the flow in every direction
is constant.  This is the mechanism behind the computation of the cohomology of a torus, in the model
where a form on the torus is a periodic form on the covering space.

* `periodCurve` : the curve traversing one period in a coordinate direction.
* `averageOp` : the average of a map over one period.
* `const_of_flowInvariant` : invariance in every direction forces constancy.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

section PeriodCurve

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The curve traversing one period in a coordinate direction. -/
noncomputable def periodCurve (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (s : ℝ) : Fin r → 𝕜 :=
  w + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)

theorem periodCurve_zero (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) : periodCurve p w j 0 = w := by
  show w + (((0 : ℝ) : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) = w
  norm_num

theorem periodCurve_one (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) :
    periodCurve p w j 1 = w + p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) := by
  show w + (((1 : ℝ) : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) = _
  norm_num

theorem periodCurve_add (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (c : Fin r → 𝕜) (s : ℝ) :
    periodCurve p (w + c) j s = periodCurve p w j s + c := by
  show w + c + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) =
    (w + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) + c
  abel

theorem periodCurve_trans (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (t s : ℝ) :
    periodCurve p (periodCurve p w j t) j s = periodCurve p w j (t + s) := by
  show w + ((t : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) +
      ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) =
    w + (((t + s : ℝ) : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
  rw [add_assoc, ← add_smul]
  congr 1
  push_cast
  ring_nf

theorem periodCurve_comm (p : 𝕜) (w : Fin r → 𝕜) (i j : Fin r) (t s : ℝ) :
    periodCurve p (periodCurve p w i t) j s = periodCurve p (periodCurve p w j s) i t := by
  show w + ((t : 𝕜) * p) • (Pi.single i (1 : 𝕜) : Fin r → 𝕜) +
      ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) =
    w + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) +
      ((t : 𝕜) * p) • (Pi.single i (1 : 𝕜) : Fin r → 𝕜)
  abel

theorem periodCurve_succ (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (t : ℝ) :
    periodCurve p w j (t + 1) = periodCurve p w j t + p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) := by
  show w + (((t + 1 : ℝ) : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) =
    w + ((t : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) +
      p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
  rw [add_assoc, ← add_smul]
  congr 1
  push_cast
  ring_nf

theorem continuous_periodCurve (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) :
    Continuous (periodCurve p w j) := by
  show Continuous fun s : ℝ => w + ((s : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
  have hcast : Continuous fun s : ℝ => ((s : 𝕜) * p) := by
    exact (RCLike.continuous_ofReal.mul continuous_const)
  exact continuous_const.add (hcast.smul continuous_const)

/-- **The period curve is differentiable** with constant derivative the period vector. -/
theorem periodCurve_hasDerivAt (p : 𝕜) (w : Fin r → 𝕜) (j : Fin r) (s : ℝ) :
    HasDerivAt (periodCurve p w j) (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) s := by
  have h1 : HasDerivAt (fun t : ℝ => ((t : 𝕜))) 1 s := by
    simpa using (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt (x := s)
  have h2 : HasDerivAt (fun t : ℝ => ((t : 𝕜) * p)) p s := by
    have h := h1.mul_const p
    rwa [one_mul] at h
  have h3 := h2.smul_const (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
  exact h3.const_add w

end PeriodCurve

section AverageOperator

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X]

/-- **The average of a map over one period** in a coordinate direction. -/
noncomputable def averageOp (p : 𝕜) (β : (Fin r → 𝕜) → X) (j : Fin r) (w : Fin r → 𝕜) : X :=
  ∫ s in (0 : ℝ)..1, β (periodCurve p w j s)

omit [NormedSpace 𝕜 X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X] in
/-- **The average preserves periodicity** in every coordinate. -/
theorem averageOp_periodic {p : 𝕜} {β : (Fin r → 𝕜) → X} (j : Fin r) {l : Fin r}
    (hper : ∀ w : Fin r → 𝕜, β (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = β w)
    (w : Fin r → 𝕜) :
    averageOp p β j (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = averageOp p β j w := by
  show (∫ s in (0 : ℝ)..1, β (periodCurve p (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) j s)) =
    ∫ s in (0 : ℝ)..1, β (periodCurve p w j s)
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [periodCurve_add, hper]

/-- The swept set of a period curve over a ball is compact. -/
theorem periodCurve_image_isCompact (p : 𝕜) (w₀ : Fin r → 𝕜) (j : Fin r) :
    IsCompact ((fun q : ℝ × (Fin r → 𝕜) => periodCurve p q.2 j q.1) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)) := by
  haveI : ProperSpace (Fin r → 𝕜) := FiniteDimensional.proper 𝕜 (Fin r → 𝕜)
  refine IsCompact.image ((isCompact_Icc).prod (isCompact_closedBall w₀ 1)) ?_
  show Continuous fun q : ℝ × (Fin r → 𝕜) =>
    q.2 + ((q.1 : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
  have hcast : Continuous fun q : ℝ × (Fin r → 𝕜) => ((q.1 : 𝕜) * p) :=
    (RCLike.continuous_ofReal.comp continuous_fst).mul continuous_const
  exact continuous_snd.add (hcast.smul continuous_const)

theorem periodCurve_mem_image {p : 𝕜} {w₀ : Fin r → 𝕜} {j : Fin r} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : Fin r → 𝕜} (hx : x ∈ Metric.closedBall w₀ 1) :
    periodCurve p x j t ∈ (fun q : ℝ × (Fin r → 𝕜) => periodCurve p q.2 j q.1) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1) :=
  ⟨(t, x), ⟨ht, hx⟩, rfl⟩

omit [SMulCommClass ℝ 𝕜 X] in
/-- **The derivative of the average is the average of the derivative.** -/
theorem averageOp_hasFDerivAt {p : 𝕜} {β : (Fin r → 𝕜) → X} (hdiff : Differentiable 𝕜 β)
    (hcont' : Continuous (fderiv 𝕜 β)) (j : Fin r) (w₀ : Fin r → 𝕜) :
    HasFDerivAt (averageOp p β j)
      (∫ s in (0 : ℝ)..1, fderiv 𝕜 β (periodCurve p w₀ j s)) w₀ := by
  have hKne : ((fun q : ℝ × (Fin r → 𝕜) => periodCurve p q.2 j q.1) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)).Nonempty :=
    ⟨periodCurve p w₀ j 0, periodCurve_mem_image
      ⟨le_refl 0, zero_le_one⟩ (Metric.mem_closedBall_self zero_le_one)⟩
  have hnorm : Continuous fun x : Fin r → 𝕜 => ‖fderiv 𝕜 β x‖ :=
    (continuous_norm (E := (Fin r → 𝕜) →L[𝕜] X)).comp hcont'
  obtain ⟨q₀, -, hq₀⟩ := IsCompact.exists_isMaxOn (periodCurve_image_isCompact p w₀ j) hKne
    (f := fun x => ‖fderiv 𝕜 β x‖) (Continuous.continuousOn hnorm)
  have hbound : ∀ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Metric.ball w₀ 1,
      ‖fderiv 𝕜 β (periodCurve p x j t)‖ ≤ ‖fderiv 𝕜 β q₀‖ := by
    intro t ht x hx
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    exact hq₀ (periodCurve_mem_image ht01 (Metric.ball_subset_closedBall hx))
  have htranslate : ∀ (t : ℝ) (x : Fin r → 𝕜),
      HasFDerivAt (fun y : Fin r → 𝕜 => β (periodCurve p y j t))
        (fderiv 𝕜 β (periodCurve p x j t)) x := by
    intro t x
    have hshift : HasFDerivAt (fun y : Fin r → 𝕜 => periodCurve p y j t)
        (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜)) x :=
      (hasFDerivAt_id x).add_const (((t : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))
    have h := ((hdiff (periodCurve p x j t)).hasFDerivAt).comp x hshift
    rwa [ContinuousLinearMap.comp_id] at h
  refine _root_.intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (x : Fin r → 𝕜) (t : ℝ) => β (periodCurve p x j t))
    (F' := fun (x : Fin r → 𝕜) (t : ℝ) => fderiv 𝕜 β (periodCurve p x j t))
    (bound := fun _ : ℝ => ‖fderiv 𝕜 β q₀‖)
    (Metric.ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hdiff.continuous.comp (continuous_periodCurve p x j)).aestronglyMeasurable)
    ((hdiff.continuous.comp (continuous_periodCurve p w₀ j)).intervalIntegrable 0 1)
    ((hcont'.comp (continuous_periodCurve p w₀ j)).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun t _ x _ => htranslate t x)

end AverageOperator

section FlowInvariance

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X]

/-- **Invariance under the translation flow** in a coordinate period direction. -/
def FlowInvariant (p : 𝕜) (β : (Fin r → 𝕜) → X) (j : Fin r) : Prop :=
  ∀ (t : ℝ) (w : Fin r → 𝕜), β (periodCurve p w j t) = β w

omit [NormedSpace 𝕜 X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X] in
/-- **The average over a period is invariant under the flow in the direction it averages.** -/
theorem averageOp_flowInvariant {p : 𝕜} {β : (Fin r → 𝕜) → X} (j : Fin r)
    (hper : ∀ w : Fin r → 𝕜, β (w + p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) = β w) :
    FlowInvariant p (averageOp p β j) j := by
  intro t w
  have hg : Function.Periodic (fun u : ℝ => β (periodCurve p w j u)) 1 := by
    intro u
    show β (periodCurve p w j (u + 1)) = β (periodCurve p w j u)
    rw [periodCurve_succ, hper]
  show (∫ s in (0 : ℝ)..1, β (periodCurve p (periodCurve p w j t) j s)) =
    ∫ s in (0 : ℝ)..1, β (periodCurve p w j s)
  have hshift : (∫ s in (0 : ℝ)..1, β (periodCurve p (periodCurve p w j t) j s)) =
      ∫ s in (0 : ℝ)..1, (fun u : ℝ => β (periodCurve p w j u)) (t + s) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    show β (periodCurve p (periodCurve p w j t) j s) = β (periodCurve p w j (t + s))
    rw [periodCurve_trans]
  rw [hshift, intervalIntegral.integral_comp_add_left
    (fun u : ℝ => β (periodCurve p w j u)) t, add_zero]
  have hper' := hg.intervalIntegral_add_eq t 0
  rw [zero_add] at hper'
  exact hper'

omit [NormedSpace 𝕜 X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X] in
/-- **Averaging in one direction preserves invariance in the others.** -/
theorem averageOp_flowInvariant_of {p : 𝕜} {β : (Fin r → 𝕜) → X} {i : Fin r} (j : Fin r)
    (hinv : FlowInvariant p β i) : FlowInvariant p (averageOp p β j) i := by
  intro t w
  show (∫ s in (0 : ℝ)..1, β (periodCurve p (periodCurve p w i t) j s)) =
    ∫ s in (0 : ℝ)..1, β (periodCurve p w j s)
  refine intervalIntegral.integral_congr fun s _ => ?_
  show β (periodCurve p (periodCurve p w i t) j s) = β (periodCurve p w j s)
  rw [periodCurve_comm, hinv t]

omit [SMulCommClass ℝ 𝕜 X] in
/-- An invariant map has vanishing derivative in the direction of invariance. -/
theorem fderiv_period_eq_zero {p : 𝕜} {β : (Fin r → 𝕜) → X} (hdiff : Differentiable 𝕜 β)
    {j : Fin r} (hinv : FlowInvariant p β j) (w : Fin r → 𝕜) :
    (fderiv 𝕜 β w) (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) = 0 := by
  have hconst : (fun t : ℝ => β (periodCurve p w j t)) = fun _ : ℝ => β w := by
    funext t
    exact hinv t w
  have hzero : HasDerivAt (fun t : ℝ => β (periodCurve p w j t)) 0 0 := by
    rw [hconst]
    exact hasDerivAt_const _ _
  have hchain : HasDerivAt (fun t : ℝ => β (periodCurve p w j t))
      ((fderiv 𝕜 β (periodCurve p w j 0)) (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))) 0 := by
    have hfd := (hdiff (periodCurve p w j 0)).hasFDerivAt
    exact (hfd.restrictScalars ℝ).comp_hasDerivAt 0 (periodCurve_hasDerivAt p w j 0)
  rw [periodCurve_zero] at hchain
  exact hchain.unique hzero

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X] in
/-- A continuous linear map vanishing on the coordinate vectors vanishes. -/
theorem clm_eq_zero_of_single {L : (Fin r → 𝕜) →L[𝕜] X}
    (h : ∀ j : Fin r, L (Pi.single j (1 : 𝕜) : Fin r → 𝕜) = 0) : L = 0 := by
  classical
  refine ContinuousLinearMap.ext fun u => ?_
  have hbasis : ∀ j : Fin r,
      (fun l => if j = l then (1 : 𝕜) else 0) = (Pi.single j (1 : 𝕜) : Fin r → 𝕜) := by
    intro j
    funext l
    rw [Pi.single_apply]
    by_cases hl : j = l
    · rw [if_pos hl, if_pos hl.symm]
    · rw [if_neg hl, if_neg (Ne.symm hl)]
  conv_lhs => rw [show u = ∑ j, u j • (fun l => if j = l then (1 : 𝕜) else 0) from pi_eq_sum_univ u]
  rw [_root_.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, hbasis j, h j, smul_zero]

omit [SMulCommClass ℝ 𝕜 X] in
/-- **A map invariant under the flow in every coordinate direction is constant.** -/
theorem const_of_flowInvariant {p : 𝕜} (hp : p ≠ 0) {β : (Fin r → 𝕜) → X}
    (hdiff : Differentiable 𝕜 β) (hinv : ∀ j : Fin r, FlowInvariant p β j) (w w' : Fin r → 𝕜) :
    β w = β w' := by
  have hfd : ∀ y : Fin r → 𝕜, fderiv 𝕜 β y = 0 := by
    intro y
    refine clm_eq_zero_of_single fun j => ?_
    have hsmul := fderiv_period_eq_zero hdiff (hinv j) y
    rw [map_smul] at hsmul
    have hscale := congrArg (fun x : X => p⁻¹ • x) hsmul
    show (fderiv 𝕜 β y) (Pi.single j (1 : 𝕜) : Fin r → 𝕜) = 0
    rw [smul_smul, inv_mul_cancel₀ hp, one_smul, smul_zero] at hscale
    exact hscale
  exact is_const_of_fderiv_eq_zero hdiff hfd w w'

end FlowInvariance

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

section IntegralHelpers

/-- Continuity of a parametric interval integral, with the target abstract so that instance search
succeeds on iterated continuous-linear-map spaces. -/
theorem continuous_parametric_unitIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y] {f : Y → ℝ → X}
    (hf : Continuous (Function.uncurry f)) :
    Continuous fun y => ∫ t in (0 : ℝ)..1, f y t :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 1

/-- Pulling a continuous linear map out of an interval integral of a continuous function. -/
theorem unitIntegral_comp_comm {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y] (L : X →L[𝕜] Y) (f : ℝ → X) (hf : Continuous f) :
    L (∫ t in (0 : ℝ)..1, f t) = ∫ t in (0 : ℝ)..1, L (f t) := by
  rw [_root_.intervalIntegral.integral_of_le zero_le_one,
    _root_.intervalIntegral.integral_of_le zero_le_one]
  exact (ContinuousLinearMap.integral_comp_comm L ((hf.intervalIntegrable 0 1).1)).symm

end IntegralHelpers

section AverageC1

open ContinuousAlternatingMap

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X]

omit [SMulCommClass ℝ 𝕜 X] in
/-- The average is differentiable. -/
theorem averageOp_differentiable {p : 𝕜} {β : (Fin r → 𝕜) → X} (hdiff : Differentiable 𝕜 β)
    (hcont' : Continuous (fderiv 𝕜 β)) (j : Fin r) :
    Differentiable 𝕜 (averageOp p β j) :=
  fun w => (averageOp_hasFDerivAt hdiff hcont' j w).differentiableAt

omit [SMulCommClass ℝ 𝕜 X] in
/-- **The average is continuously differentiable.** -/
theorem averageOp_fderiv_continuous {p : 𝕜} {β : (Fin r → 𝕜) → X} (hdiff : Differentiable 𝕜 β)
    (hcont' : Continuous (fderiv 𝕜 β)) (j : Fin r) :
    Continuous (fderiv 𝕜 (averageOp p β j)) := by
  have hfd : fderiv 𝕜 (averageOp p β j) =
      fun w => ∫ s in (0 : ℝ)..1, fderiv 𝕜 β (periodCurve p w j s) := by
    funext w
    exact (averageOp_hasFDerivAt hdiff hcont' j w).fderiv
  rw [hfd]
  refine continuous_parametric_unitIntegral ?_
  have hcurve : Continuous fun q : (Fin r → 𝕜) × ℝ => periodCurve p q.1 j q.2 := by
    show Continuous fun q : (Fin r → 𝕜) × ℝ =>
      q.1 + ((q.2 : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
    have hcast : Continuous fun q : (Fin r → 𝕜) × ℝ => ((q.2 : 𝕜) * p) :=
      (RCLike.continuous_ofReal.comp continuous_snd).mul continuous_const
    exact continuous_fst.add (hcast.smul continuous_const)
  exact hcont'.comp hcurve

end AverageC1

section AverageExtDeriv

open ContinuousAlternatingMap

variable {𝕜 : Type*} [RCLike 𝕜] {r n : ℕ}

/-- **The average commutes with the exterior derivative.** -/
theorem averageOp_extDeriv {p : 𝕜} {β : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜}
    (hdiff : Differentiable 𝕜 β) (hcont' : Continuous (fderiv 𝕜 β)) (j : Fin r) (w : Fin r → 𝕜) :
    extDeriv (averageOp p β j) w =
      ∫ s in (0 : ℝ)..1, extDeriv β (periodCurve p w j s) := by
  have hcont : Continuous fun s : ℝ => fderiv 𝕜 β (periodCurve p w j s) :=
    hcont'.comp (continuous_periodCurve p w j)
  rw [extDeriv, (averageOp_hasFDerivAt hdiff hcont' j w).fderiv]
  exact unitIntegral_comp_comm (𝕜 := 𝕜) (alternatizeUncurryFinCLM 𝕜 (Fin r → 𝕜) 𝕜 (n := n))
    (fun s => fderiv 𝕜 β (periodCurve p w j s)) hcont

end AverageExtDeriv

end GaloisForLFunctions.HTGeometry
