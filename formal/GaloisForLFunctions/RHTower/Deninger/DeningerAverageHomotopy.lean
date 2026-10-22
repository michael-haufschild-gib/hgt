import GaloisForLFunctions.RHTower.Deninger.DeningerContractDeriv

/-!
# The average over a period is homotopic to the identity

The average of a form over one period differs from the form by an exact form: the weighted average
of the contraction against the period direction is a primitive of the difference.  The weight comes
from integrating the Cartan formula along the period, where the directional derivative of the form
is the derivative of the form along the period curve, and one integration by parts turns the double
integral into a single one.

* `deningerWeightHomotopy` : the weighted average of a map over one period.
* `deningerWeightHomotopy_hasFDerivAt` : its derivative is the weighted average of the derivative.
* `deningerAverageOp_sub_eq_extDeriv` : the average of a closed form differs from it by an exact
  form.
-/

namespace RHTower

open Complex MeasureTheory ContinuousAlternatingMap

section WeightHomotopy

variable {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- **The weighted average of a map over one period** in a coordinate direction.  The weight
`1 - s` is what makes it a primitive of the difference between the average and the map. -/
noncomputable def deningerWeightHomotopy (γ : (Fin r → ℂ) → X) (j : Fin r) (w : Fin r → ℂ) : X :=
  ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) • γ (deningerPeriodCurve w j s)

omit [CompleteSpace X] in
/-- The weighted average preserves periodicity in every coordinate. -/
theorem deningerWeightHomotopy_periodic {γ : (Fin r → ℂ) → X} (j : Fin r) {l : Fin r}
    (hper : ∀ w : Fin r → ℂ,
      γ (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = γ w)
    (w : Fin r → ℂ) :
    deningerWeightHomotopy γ j (w + (2 * Real.pi * Complex.I) •
        (Pi.single l (1 : ℂ) : Fin r → ℂ)) = deningerWeightHomotopy γ j w := by
  show (∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) • γ (deningerPeriodCurve (w + (2 * Real.pi * Complex.I) •
      (Pi.single l (1 : ℂ) : Fin r → ℂ)) j s)) =
    ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) • γ (deningerPeriodCurve w j s)
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [deningerPeriodCurve_add, hper]

/-- The bound on the weight along the segment. -/
theorem deningerWeight_norm_le {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) : ‖(1 : ℂ) - (s : ℂ)‖ ≤ 1 := by
  have hcast : (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> [linarith [hs.2]; linarith [hs.1]]

omit [CompleteSpace X] in
/-- **The derivative of the weighted average is the weighted average of the derivative.** -/
theorem deningerWeightHomotopy_hasFDerivAt {γ : (Fin r → ℂ) → X} (hdiff : Differentiable ℂ γ)
    (hcont' : Continuous (fderiv ℂ γ)) (j : Fin r) (w₀ : Fin r → ℂ) :
    HasFDerivAt (deningerWeightHomotopy γ j)
      (∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) • fderiv ℂ γ (deningerPeriodCurve w₀ j s)) w₀ := by
  have hcurvecont : ∀ x : Fin r → ℂ, Continuous (deningerPeriodCurve x j) := by
    intro x
    show Continuous fun s : ℝ =>
      x + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
    fun_prop
  have hweightcont : Continuous fun s : ℝ => (1 : ℂ) - (s : ℂ) := by fun_prop
  have hKne : ((fun p : ℝ × (Fin r → ℂ) => deningerPeriodCurve p.2 j p.1) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall w₀ 1)).Nonempty :=
    ⟨deningerPeriodCurve w₀ j 0, deningerPeriodCurve_mem_image
      ⟨le_refl 0, zero_le_one⟩ (Metric.mem_closedBall_self zero_le_one)⟩
  have hnorm : Continuous fun x : Fin r → ℂ => ‖fderiv ℂ γ x‖ := by
    have h : Continuous fun A : (Fin r → ℂ) →L[ℂ] X => ‖A‖ := by
      exact continuous_norm (E := (Fin r → ℂ) →L[ℂ] X)
    exact h.comp hcont'
  obtain ⟨p₀, -, hp₀⟩ := IsCompact.exists_isMaxOn (deningerPeriodCurve_image_isCompact w₀ j) hKne
    (f := fun x => ‖fderiv ℂ γ x‖) (Continuous.continuousOn hnorm)
  set C : ℝ := ‖fderiv ℂ γ p₀‖ with hCdef
  have hbound : ∀ t : ℝ, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Metric.ball w₀ 1,
      ‖(1 - (t : ℂ)) • fderiv ℂ γ (deningerPeriodCurve x j t)‖ ≤ C := by
    intro t ht x hx
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    have hpt : ‖fderiv ℂ γ (deningerPeriodCurve x j t)‖ ≤ C :=
      hp₀ (deningerPeriodCurve_mem_image ht01 (Metric.ball_subset_closedBall hx))
    refine le_trans (ContinuousLinearMap.opNorm_smul_le _ _) ?_
    calc ‖(1 : ℂ) - (t : ℂ)‖ * ‖fderiv ℂ γ (deningerPeriodCurve x j t)‖
        ≤ 1 * C := mul_le_mul (deningerWeight_norm_le ht01) hpt
          (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = C := one_mul _
  have htranslate : ∀ (t : ℝ) (x : Fin r → ℂ),
      HasFDerivAt (fun y : Fin r → ℂ => (1 - (t : ℂ)) • γ (deningerPeriodCurve y j t))
        ((1 - (t : ℂ)) • fderiv ℂ γ (deningerPeriodCurve x j t)) x := by
    intro t x
    have hshift : HasFDerivAt (fun y : Fin r → ℂ => deningerPeriodCurve y j t)
        (ContinuousLinearMap.id ℂ (Fin r → ℂ)) x := by
      have h := (hasFDerivAt_id (𝕜 := ℂ) x).add_const
        ((((t : ℂ) * (2 * Real.pi * Complex.I)) •
          (Pi.single j (1 : ℂ) : Fin r → ℂ) : Fin r → ℂ))
      exact h
    have h := ((hdiff (deningerPeriodCurve x j t)).hasFDerivAt).comp x hshift
    rw [ContinuousLinearMap.comp_id] at h
    exact h.const_smul _
  refine _root_.intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (x : Fin r → ℂ) (t : ℝ) => (1 - (t : ℂ)) • γ (deningerPeriodCurve x j t))
    (F' := fun (x : Fin r → ℂ) (t : ℝ) => (1 - (t : ℂ)) • fderiv ℂ γ (deningerPeriodCurve x j t))
    (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall fun x =>
      (hweightcont.smul (hdiff.continuous.comp (hcurvecont x))).aestronglyMeasurable)
    ((hweightcont.smul (hdiff.continuous.comp (hcurvecont w₀))).intervalIntegrable 0 1)
    ((hweightcont.smul (hcont'.comp (hcurvecont w₀))).aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun t _ x _ => htranslate t x)

omit [CompleteSpace X] in
/-- The weighted average is differentiable. -/
theorem deningerWeightHomotopy_differentiable {γ : (Fin r → ℂ) → X} (hdiff : Differentiable ℂ γ)
    (hcont' : Continuous (fderiv ℂ γ)) (j : Fin r) :
    Differentiable ℂ (deningerWeightHomotopy γ j) :=
  fun w => (deningerWeightHomotopy_hasFDerivAt hdiff hcont' j w).differentiableAt

omit [CompleteSpace X] in
/-- The weighted average is continuously differentiable. -/
theorem deningerWeightHomotopy_fderiv_continuous {γ : (Fin r → ℂ) → X}
    (hdiff : Differentiable ℂ γ) (hcont' : Continuous (fderiv ℂ γ)) (j : Fin r) :
    Continuous (fderiv ℂ (deningerWeightHomotopy γ j)) := by
  have hfd : fderiv ℂ (deningerWeightHomotopy γ j) =
      fun w => ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) • fderiv ℂ γ (deningerPeriodCurve w j s) := by
    funext w
    exact (deningerWeightHomotopy_hasFDerivAt hdiff hcont' j w).fderiv
  rw [hfd]
  refine deningerContinuous_parametric_integral ?_
  have hcurve : Continuous fun p : (Fin r → ℂ) × ℝ => deningerPeriodCurve p.1 j p.2 := by
    show Continuous fun p : (Fin r → ℂ) × ℝ =>
      p.1 + ((p.2 : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
    fun_prop
  have hweight : Continuous fun p : (Fin r → ℂ) × ℝ => (1 : ℂ) - ((p.2 : ℝ) : ℂ) := by fun_prop
  exact hweight.smul (hcont'.comp hcurve)

end WeightHomotopy

end RHTower

namespace RHTower

open Complex ContinuousAlternatingMap

section HomotopyFormula

variable {r n : ℕ}

/-- The exterior derivative of the weighted average is the weighted average of the exterior
derivative. -/
theorem deningerWeightHomotopy_extDeriv
    {γ : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ} (hdiff : Differentiable ℂ γ)
    (hcont' : Continuous (fderiv ℂ γ)) (j : Fin r) (w : Fin r → ℂ) :
    extDeriv (deningerWeightHomotopy γ j) w =
      ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) • extDeriv γ (deningerPeriodCurve w j s) := by
  have hcurvecont : Continuous (deningerPeriodCurve w j) := by
    show Continuous fun s : ℝ =>
      w + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
    fun_prop
  have hweightcont : Continuous fun s : ℝ => (1 : ℂ) - (s : ℂ) := by fun_prop
  have hcont : Continuous fun s : ℝ =>
      (1 - (s : ℂ)) • fderiv ℂ γ (deningerPeriodCurve w j s) :=
    hweightcont.smul (hcont'.comp hcurvecont)
  have hcomm : alternatizeUncurryFin
        (∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) • fderiv ℂ γ (deningerPeriodCurve w j s)) =
      ∫ s in (0 : ℝ)..1, (alternatizeUncurryFinCLM ℂ (Fin r → ℂ) ℂ (n := n))
        ((1 - (s : ℂ)) • fderiv ℂ γ (deningerPeriodCurve w j s)) :=
    deningerIntegral_comp_comm (alternatizeUncurryFinCLM ℂ (Fin r → ℂ) ℂ (n := n))
      (fun s => (1 - (s : ℂ)) • fderiv ℂ γ (deningerPeriodCurve w j s)) hcont
  rw [extDeriv, (deningerWeightHomotopy_hasFDerivAt hdiff hcont' j w).fderiv, hcomm]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show (alternatizeUncurryFinCLM ℂ (Fin r → ℂ) ℂ (n := n))
      ((1 - (s : ℂ)) • fderiv ℂ γ (deningerPeriodCurve w j s)) =
    (1 - (s : ℂ)) • extDeriv γ (deningerPeriodCurve w j s)
  rw [map_smul]
  rfl

/-- **The average of a closed form over a period differs from the form by an exact form.**  The
primitive is the weighted average of the contraction against the period direction: the Cartan
formula turns the directional derivative into the exterior derivative of the contraction, and one
integration by parts along the period produces the average. -/
theorem deningerAverageOp_sub_eq_extDeriv
    {β : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ} (hdiff : Differentiable ℂ β)
    (hcont' : Continuous (fderiv ℂ β)) (hclosed : ∀ w : Fin r → ℂ, extDeriv β w = 0) (j : Fin r)
    (w : Fin r → ℂ) :
    extDeriv (deningerWeightHomotopy (fun y => deningerContractCLM
        ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) (β y)) j) w =
      deningerAverageOp β j w - β w := by
  set V : Fin r → ℂ := (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ) with hV
  set γ : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
    fun y => deningerContractCLM V (β y) with hγ
  have hγdiff : Differentiable ℂ γ := by
    intro y
    exact ((deningerContractCLM (n := n) V).differentiableAt).comp y (hdiff y)
  have hγfd : ∀ y : Fin r → ℂ,
      fderiv ℂ γ y = (deningerContractCLM V).comp (fderiv ℂ β y) := by
    intro y
    have h := ((deningerContractCLM (n := n) V).hasFDerivAt).comp y (hdiff y).hasFDerivAt
    exact h.fderiv
  have hγcont : Continuous (fderiv ℂ γ) := by
    have hfun : fderiv ℂ γ = fun y => (deningerContractCLM V).comp (fderiv ℂ β y) := by
      funext y
      exact hγfd y
    rw [hfun]
    exact isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk hcont')
  -- the Cartan formula for a closed form
  have hcartan : ∀ y : Fin r → ℂ, extDeriv γ y = (fderiv ℂ β y) V := by
    intro y
    rw [hγ, deningerExtDeriv_contract (hdiff y) V, deningerCartan_contract]
    rw [show alternatizeUncurryFin (fderiv ℂ β y) =
      (0 : (Fin r → ℂ) [⋀^Fin (n + 1 + 1)]→L[ℂ] ℂ) from hclosed y]
    rw [_root_.map_zero, sub_zero]
  -- the derivative of the form along the period curve
  have hcurvecont : Continuous (deningerPeriodCurve w j) := by
    show Continuous fun s : ℝ =>
      w + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
    fun_prop
  have hderiv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => β (deningerPeriodCurve w j t))
      ((fderiv ℂ β (deningerPeriodCurve w j s)) V) s := by
    intro s
    have hfd := (hdiff (deningerPeriodCurve w j s)).hasFDerivAt
    exact (hfd.restrictScalars ℝ).comp_hasDerivAt s (deningerPeriodCurve_hasDerivAt w j s)
  have hbetacont : Continuous fun s : ℝ => β (deningerPeriodCurve w j s) :=
    hdiff.continuous.comp hcurvecont
  have hdcont : Continuous fun s : ℝ => (fderiv ℂ β (deningerPeriodCurve w j s)) V :=
    (ContinuousLinearMap.apply ℂ ((Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) V).continuous.comp
      (hcont'.comp hcurvecont)
  have hweightcont : Continuous fun s : ℝ => (1 : ℂ) - (s : ℂ) := by fun_prop
  -- integration by parts along the period
  have hweightderiv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (1 : ℂ) - (t : ℂ)) (-1) s := by
    intro s
    exact (deningerRealCast_hasDerivAt s).const_sub 1
  have hprod : ∀ s : ℝ, HasDerivAt
      (fun t : ℝ => (1 - (t : ℂ)) • β (deningerPeriodCurve w j t))
      ((1 - (s : ℂ)) • ((fderiv ℂ β (deningerPeriodCurve w j s)) V) +
        (-1 : ℂ) • β (deningerPeriodCurve w j s)) s :=
    fun s => (hweightderiv s).smul (hderiv s)
  have hprodcont : Continuous fun s : ℝ =>
      (1 - (s : ℂ)) • ((fderiv ℂ β (deningerPeriodCurve w j s)) V) +
        (-1 : ℂ) • β (deningerPeriodCurve w j s) :=
    (hweightcont.smul hdcont).add (hbetacont.const_smul (-1 : ℂ))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hprod s)
    (hprodcont.intervalIntegrable 0 1)
  have hint1 : IntervalIntegrable
      (fun s : ℝ => (1 - (s : ℂ)) • ((fderiv ℂ β (deningerPeriodCurve w j s)) V))
      MeasureTheory.volume 0 1 :=
    (hweightcont.smul hdcont).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable
      (fun s : ℝ => (-1 : ℂ) • β (deningerPeriodCurve w j s)) MeasureTheory.volume 0 1 :=
    (hbetacont.const_smul (-1 : ℂ)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hint1 hint2] at hftc
  have hend : (1 - ((1 : ℝ) : ℂ)) • β (deningerPeriodCurve w j 1) = 0 := by
    have h0 : (1 : ℂ) - ((1 : ℝ) : ℂ) = 0 := by norm_num
    rw [h0]
    ext v
    show (0 : ℂ) • (β (deningerPeriodCurve w j 1) v) =
      (0 : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) v
    rw [show ((0 : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) v) = (0 : ℂ) from rfl, smul_eq_mul,
      zero_mul]
  have hstart : (1 - ((0 : ℝ) : ℂ)) • β (deningerPeriodCurve w j 0) = β w := by
    rw [deningerPeriodCurve_zero]
    have h1 : (1 : ℂ) - ((0 : ℝ) : ℂ) = 1 := by norm_num
    rw [h1]
    ext v
    show (1 : ℂ) • (β w v) = β w v
    rw [smul_eq_mul, one_mul]
  rw [hend, hstart, zero_sub] at hftc
  have hsecond : (∫ s in (0 : ℝ)..1, (-1 : ℂ) • β (deningerPeriodCurve w j s)) =
      -deningerAverageOp β j w := by
    rw [intervalIntegral.integral_smul]
    show (-1 : ℂ) • (deningerAverageOp β j w) = -deningerAverageOp β j w
    ext v
    show (-1 : ℂ) • (deningerAverageOp β j w v) = (-(deningerAverageOp β j w)) v
    rw [show ((-(deningerAverageOp β j w)) v) = -(deningerAverageOp β j w v) from rfl,
      smul_eq_mul, neg_one_mul]
  rw [hsecond] at hftc
  -- assembling the two halves
  rw [deningerWeightHomotopy_extDeriv hγdiff hγcont j w]
  rw [intervalIntegral.integral_congr (g := fun s =>
    (1 - (s : ℂ)) • ((fderiv ℂ β (deningerPeriodCurve w j s)) V))
    (fun s _ => by rw [hcartan (deningerPeriodCurve w j s)])]
  rw [← sub_eq_add_neg] at hftc
  rw [sub_eq_neg_add]
  exact sub_eq_iff_eq_add.mp hftc

end HomotopyFormula

end RHTower
