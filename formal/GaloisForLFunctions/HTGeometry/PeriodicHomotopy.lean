import GaloisForLFunctions.HTGeometry.PeriodicAveraging
import GaloisForLFunctions.HTGeometry.AlternatingContraction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The average over a period is homotopic to the identity

The average of a closed form over one period differs from the form by an exact form: the weighted
average of the contraction against the period direction is a primitive of the difference.  The weight
comes from integrating the Cartan formula along the period, where the directional derivative of the
form is the derivative of the form along the period curve, and one integration by parts turns the
double integral into a single one.

* `weightHomotopy` : the weighted average of a map over one period.
* `weightHomotopy_hasFDerivAt` : its derivative is the weighted average of the derivative.
* `averageOp_sub_eq_extDeriv` : the average of a closed form differs from it by an exact form.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ContinuousAlternatingMap

section WeightHomotopy

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X]

/-- **The weighted average of a map over one period** in a coordinate direction.  The weight
`1 - s` is what makes it a primitive of the difference between the average and the map. -/
noncomputable def weightHomotopy (p : 𝕜) (γ : (Fin r → 𝕜) → X) (j : Fin r) (w : Fin r → 𝕜) : X :=
  ∫ s in (0 : ℝ)..1, (1 - (s : 𝕜)) • γ (periodCurve p w j s)

omit [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X] in
/-- The weighted average preserves periodicity in every coordinate. -/
theorem weightHomotopy_periodic {p : 𝕜} {γ : (Fin r → 𝕜) → X} (j : Fin r) {l : Fin r}
    (hper : ∀ w : Fin r → 𝕜, γ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = γ w)
    (w : Fin r → 𝕜) :
    weightHomotopy p γ j (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = weightHomotopy p γ j w := by
  show (∫ s in (0 : ℝ)..1,
      (1 - (s : 𝕜)) • γ (periodCurve p (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) j s)) =
    ∫ s in (0 : ℝ)..1, (1 - (s : 𝕜)) • γ (periodCurve p w j s)
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [periodCurve_add, hper]

omit [NormedSpace 𝕜 X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X] in
/-- The bound on the weight along the segment. -/
theorem weight_norm_le {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖(1 : 𝕜) - (s : 𝕜)‖ ≤ 1 := by
  have hcast : (1 : 𝕜) - (s : 𝕜) = ((1 - s : ℝ) : 𝕜) := by push_cast; ring
  rw [hcast, RCLike.norm_ofReal, abs_le]
  constructor <;> [linarith [hs.2]; linarith [hs.1]]

omit [SMulCommClass ℝ 𝕜 X] in
/-- **The derivative of the weighted average is the weighted average of the derivative.** -/
theorem weightHomotopy_hasFDerivAt {p : 𝕜} {γ : (Fin r → 𝕜) → X} (hdiff : Differentiable 𝕜 γ)
    (hcont' : Continuous (fderiv 𝕜 γ)) (j : Fin r) (w₀ : Fin r → 𝕜) :
    HasFDerivAt (weightHomotopy p γ j)
      (∫ s in (0 : ℝ)..1, (1 - (s : 𝕜)) • fderiv 𝕜 γ (periodCurve p w₀ j s)) w₀ := by
  have hweightcont : Continuous fun s : ℝ => (1 : 𝕜) - (s : 𝕜) :=
    continuous_const.sub RCLike.continuous_ofReal
  have hKne : ((fun q : ℝ × (Fin r → 𝕜) => periodCurve p q.2 j q.1) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)).Nonempty :=
    ⟨periodCurve p w₀ j 0, periodCurve_mem_image
      ⟨le_refl 0, zero_le_one⟩ (Metric.mem_closedBall_self zero_le_one)⟩
  have hnorm : Continuous fun x : Fin r → 𝕜 => ‖fderiv 𝕜 γ x‖ :=
    (continuous_norm (E := (Fin r → 𝕜) →L[𝕜] X)).comp hcont'
  obtain ⟨q₀, -, hq₀⟩ := IsCompact.exists_isMaxOn (periodCurve_image_isCompact p w₀ j) hKne
    (f := fun x => ‖fderiv 𝕜 γ x‖) (Continuous.continuousOn hnorm)
  set C : ℝ := ‖fderiv 𝕜 γ q₀‖ with hCdef
  have hbound : ∀ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Metric.ball w₀ 1,
      ‖(1 - (t : 𝕜)) • fderiv 𝕜 γ (periodCurve p x j t)‖ ≤ C := by
    intro t ht x hx
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    have hpt : ‖fderiv 𝕜 γ (periodCurve p x j t)‖ ≤ C :=
      hq₀ (periodCurve_mem_image ht01 (Metric.ball_subset_closedBall hx))
    refine le_trans (ContinuousLinearMap.opNorm_smul_le _ _) ?_
    calc ‖(1 : 𝕜) - (t : 𝕜)‖ * ‖fderiv 𝕜 γ (periodCurve p x j t)‖
        ≤ 1 * C := mul_le_mul (weight_norm_le ht01) hpt
          (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = C := one_mul _
  have htranslate : ∀ (t : ℝ) (x : Fin r → 𝕜),
      HasFDerivAt (fun y : Fin r → 𝕜 => (1 - (t : 𝕜)) • γ (periodCurve p y j t))
        ((1 - (t : 𝕜)) • fderiv 𝕜 γ (periodCurve p x j t)) x := by
    intro t x
    have hshift : HasFDerivAt (fun y : Fin r → 𝕜 => periodCurve p y j t)
        (ContinuousLinearMap.id 𝕜 (Fin r → 𝕜)) x :=
      (hasFDerivAt_id x).add_const (((t : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))
    have h := ((hdiff (periodCurve p x j t)).hasFDerivAt).comp x hshift
    rw [ContinuousLinearMap.comp_id] at h
    exact h.const_smul _
  refine _root_.intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (x : Fin r → 𝕜) (t : ℝ) => (1 - (t : 𝕜)) • γ (periodCurve p x j t))
    (F' := fun (x : Fin r → 𝕜) (t : ℝ) => (1 - (t : 𝕜)) • fderiv 𝕜 γ (periodCurve p x j t))
    (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hweightcont.smul (hdiff.continuous.comp (continuous_periodCurve p x j))).aestronglyMeasurable)
    ((hweightcont.smul
      (hdiff.continuous.comp (continuous_periodCurve p w₀ j))).intervalIntegrable 0 1)
    ((hweightcont.smul (hcont'.comp (continuous_periodCurve p w₀ j))).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun t _ x _ => htranslate t x)

omit [SMulCommClass ℝ 𝕜 X] in
/-- The weighted average is differentiable. -/
theorem weightHomotopy_differentiable {p : 𝕜} {γ : (Fin r → 𝕜) → X} (hdiff : Differentiable 𝕜 γ)
    (hcont' : Continuous (fderiv 𝕜 γ)) (j : Fin r) :
    Differentiable 𝕜 (weightHomotopy p γ j) :=
  fun w => (weightHomotopy_hasFDerivAt hdiff hcont' j w).differentiableAt

omit [SMulCommClass ℝ 𝕜 X] in
/-- The weighted average is continuously differentiable. -/
theorem weightHomotopy_fderiv_continuous {p : 𝕜} {γ : (Fin r → 𝕜) → X}
    (hdiff : Differentiable 𝕜 γ) (hcont' : Continuous (fderiv 𝕜 γ)) (j : Fin r) :
    Continuous (fderiv 𝕜 (weightHomotopy p γ j)) := by
  have hfd : fderiv 𝕜 (weightHomotopy p γ j) =
      fun w => ∫ s in (0 : ℝ)..1, (1 - (s : 𝕜)) • fderiv 𝕜 γ (periodCurve p w j s) := by
    funext w
    exact (weightHomotopy_hasFDerivAt hdiff hcont' j w).fderiv
  rw [hfd]
  refine continuous_parametric_unitIntegral ?_
  have hcurve : Continuous fun q : (Fin r → 𝕜) × ℝ => periodCurve p q.1 j q.2 := by
    show Continuous fun q : (Fin r → 𝕜) × ℝ =>
      q.1 + ((q.2 : 𝕜) * p) • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)
    have hcast : Continuous fun q : (Fin r → 𝕜) × ℝ => ((q.2 : 𝕜) * p) :=
      (RCLike.continuous_ofReal.comp continuous_snd).mul continuous_const
    exact continuous_fst.add (hcast.smul continuous_const)
  have hweight : Continuous fun q : (Fin r → 𝕜) × ℝ => (1 : 𝕜) - ((q.2 : ℝ) : 𝕜) :=
    continuous_const.sub (RCLike.continuous_ofReal.comp continuous_snd)
  exact hweight.smul (hcont'.comp hcurve)

end WeightHomotopy

section HomotopyFormula

variable {𝕜 : Type*} [RCLike 𝕜] {r n : ℕ}

/-- The exterior derivative of the weighted average is the weighted average of the exterior
derivative. -/
theorem weightHomotopy_extDeriv {p : 𝕜} {γ : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜}
    (hdiff : Differentiable 𝕜 γ) (hcont' : Continuous (fderiv 𝕜 γ)) (j : Fin r) (w : Fin r → 𝕜) :
    extDeriv (weightHomotopy p γ j) w =
      ∫ s in (0 : ℝ)..1, (1 - (s : 𝕜)) • extDeriv γ (periodCurve p w j s) := by
  have hweightcont : Continuous fun s : ℝ => (1 : 𝕜) - (s : 𝕜) :=
    continuous_const.sub RCLike.continuous_ofReal
  have hcont : Continuous fun s : ℝ => (1 - (s : 𝕜)) • fderiv 𝕜 γ (periodCurve p w j s) :=
    hweightcont.smul (hcont'.comp (continuous_periodCurve p w j))
  have hcomm : alternatizeUncurryFin
        (∫ s in (0 : ℝ)..1, (1 - (s : 𝕜)) • fderiv 𝕜 γ (periodCurve p w j s)) =
      ∫ s in (0 : ℝ)..1, (alternatizeUncurryFinCLM 𝕜 (Fin r → 𝕜) 𝕜 (n := n))
        ((1 - (s : 𝕜)) • fderiv 𝕜 γ (periodCurve p w j s)) :=
    unitIntegral_comp_comm (𝕜 := 𝕜) (alternatizeUncurryFinCLM 𝕜 (Fin r → 𝕜) 𝕜 (n := n))
      (fun s => (1 - (s : 𝕜)) • fderiv 𝕜 γ (periodCurve p w j s)) hcont
  rw [extDeriv, (weightHomotopy_hasFDerivAt hdiff hcont' j w).fderiv, hcomm]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show (alternatizeUncurryFinCLM 𝕜 (Fin r → 𝕜) 𝕜 (n := n))
      ((1 - (s : 𝕜)) • fderiv 𝕜 γ (periodCurve p w j s)) =
    (1 - (s : 𝕜)) • extDeriv γ (periodCurve p w j s)
  rw [map_smul]
  rfl

/-- **The average of a closed form over a period differs from the form by an exact form.**  The
primitive is the weighted average of the contraction against the period direction: the Cartan
formula turns the directional derivative into the exterior derivative of the contraction, and one
integration by parts along the period produces the average. -/
theorem averageOp_sub_eq_extDeriv {p : 𝕜}
    {β : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜} (hdiff : Differentiable 𝕜 β)
    (hcont' : Continuous (fderiv 𝕜 β)) (hclosed : ∀ w : Fin r → 𝕜, extDeriv β w = 0) (j : Fin r)
    (w : Fin r → 𝕜) :
    extDeriv (weightHomotopy p (fun y => contractCLM (𝕜 := 𝕜)
        (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) (β y)) j) w =
      averageOp p β j w - β w := by
  set V : Fin r → 𝕜 := p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) with hV
  set γ : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜 :=
    fun y => contractCLM (𝕜 := 𝕜) V (β y) with hγ
  have hγdiff : Differentiable 𝕜 γ := by
    intro y
    exact ((contractCLM (𝕜 := 𝕜) (n := n) V).differentiableAt).comp y (hdiff y)
  have hγfd : ∀ y : Fin r → 𝕜,
      fderiv 𝕜 γ y = (contractCLM (𝕜 := 𝕜) V).comp (fderiv 𝕜 β y) := by
    intro y
    have h := ((contractCLM (𝕜 := 𝕜) (n := n) V).hasFDerivAt).comp y (hdiff y).hasFDerivAt
    exact h.fderiv
  have hγcont : Continuous (fderiv 𝕜 γ) := by
    have hfun : fderiv 𝕜 γ = fun y => (contractCLM (𝕜 := 𝕜) V).comp (fderiv 𝕜 β y) := by
      funext y
      exact hγfd y
    rw [hfun]
    exact isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk hcont')
  -- the Cartan formula for a closed form
  have hcartan : ∀ y : Fin r → 𝕜, extDeriv γ y = (fderiv 𝕜 β y) V := by
    intro y
    rw [hγ, extDeriv_contract (hdiff y) V, cartan_contract]
    rw [show alternatizeUncurryFin (fderiv 𝕜 β y) =
      (0 : (Fin r → 𝕜) [⋀^Fin (n + 1 + 1)]→L[𝕜] 𝕜) from hclosed y]
    rw [_root_.map_zero, sub_zero]
  -- the derivative of the form along the period curve
  have hcurvecont : Continuous (periodCurve p w j) := continuous_periodCurve p w j
  have hderiv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => β (periodCurve p w j t))
      ((fderiv 𝕜 β (periodCurve p w j s)) V) s := by
    intro s
    have hfd := (hdiff (periodCurve p w j s)).hasFDerivAt
    exact (hfd.restrictScalars ℝ).comp_hasDerivAt s (periodCurve_hasDerivAt p w j s)
  have hbetacont : Continuous fun s : ℝ => β (periodCurve p w j s) :=
    hdiff.continuous.comp hcurvecont
  have hdcont : Continuous fun s : ℝ => (fderiv 𝕜 β (periodCurve p w j s)) V :=
    (ContinuousLinearMap.apply 𝕜 ((Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜) V).continuous.comp
      (hcont'.comp hcurvecont)
  have hweightcont : Continuous fun s : ℝ => (1 : 𝕜) - (s : 𝕜) :=
    continuous_const.sub RCLike.continuous_ofReal
  -- integration by parts along the period
  have hcast : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ((t : 𝕜))) 1 s := fun s => by
    simpa using (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt (x := s)
  have hweightderiv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (1 : 𝕜) - (t : 𝕜)) (-1) s :=
    fun s => (hcast s).const_sub 1
  have hprod : ∀ s : ℝ, HasDerivAt
      (fun t : ℝ => (1 - (t : 𝕜)) • β (periodCurve p w j t))
      ((1 - (s : 𝕜)) • ((fderiv 𝕜 β (periodCurve p w j s)) V) +
        (-1 : 𝕜) • β (periodCurve p w j s)) s :=
    fun s => (hweightderiv s).smul (hderiv s)
  have hprodcont : Continuous fun s : ℝ =>
      (1 - (s : 𝕜)) • ((fderiv 𝕜 β (periodCurve p w j s)) V) +
        (-1 : 𝕜) • β (periodCurve p w j s) :=
    (hweightcont.smul hdcont).add (hbetacont.const_smul (-1 : 𝕜))
  have hftc := _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hprod s)
    (hprodcont.intervalIntegrable 0 1)
  have hint1 : IntervalIntegrable
      (fun s : ℝ => (1 - (s : 𝕜)) • ((fderiv 𝕜 β (periodCurve p w j s)) V))
      MeasureTheory.volume 0 1 :=
    (hweightcont.smul hdcont).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable
      (fun s : ℝ => (-1 : 𝕜) • β (periodCurve p w j s)) MeasureTheory.volume 0 1 :=
    (hbetacont.const_smul (-1 : 𝕜)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hint1 hint2] at hftc
  have hend : (1 - ((1 : ℝ) : 𝕜)) • β (periodCurve p w j 1) = 0 := by
    have h0 : (1 : 𝕜) - ((1 : ℝ) : 𝕜) = 0 := by norm_num
    rw [h0]
    ext v
    show (0 : 𝕜) • (β (periodCurve p w j 1) v) =
      (0 : (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜) v
    rw [show ((0 : (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜) v) = (0 : 𝕜) from rfl, smul_eq_mul,
      zero_mul]
  have hstart : (1 - ((0 : ℝ) : 𝕜)) • β (periodCurve p w j 0) = β w := by
    rw [periodCurve_zero]
    have h1 : (1 : 𝕜) - ((0 : ℝ) : 𝕜) = 1 := by norm_num
    rw [h1]
    ext v
    show (1 : 𝕜) • (β w v) = β w v
    rw [smul_eq_mul, one_mul]
  rw [hend, hstart, zero_sub] at hftc
  have hsecond : (∫ s in (0 : ℝ)..1, (-1 : 𝕜) • β (periodCurve p w j s)) =
      -averageOp p β j w := by
    rw [intervalIntegral.integral_smul]
    show (-1 : 𝕜) • (averageOp p β j w) = -averageOp p β j w
    ext v
    show (-1 : 𝕜) • (averageOp p β j w v) = (-(averageOp p β j w)) v
    rw [show ((-(averageOp p β j w)) v) = -(averageOp p β j w v) from rfl,
      smul_eq_mul, neg_one_mul]
  rw [hsecond] at hftc
  -- assembling the two halves
  rw [weightHomotopy_extDeriv hγdiff hγcont j w]
  rw [intervalIntegral.integral_congr (g := fun s =>
    (1 - (s : 𝕜)) • ((fderiv 𝕜 β (periodCurve p w j s)) V))
    (fun s _ => by rw [hcartan (periodCurve p w j s)])]
  rw [← sub_eq_add_neg] at hftc
  rw [sub_eq_neg_add]
  exact sub_eq_iff_eq_add.mp hftc

end HomotopyFormula

end GaloisForLFunctions.HTGeometry
