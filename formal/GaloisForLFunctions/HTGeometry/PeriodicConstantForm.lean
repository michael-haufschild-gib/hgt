import GaloisForLFunctions.HTGeometry.PeriodicHomotopy

/-!
# Constant forms with periodic primitives vanish

A form with constant coefficients on a coordinate space that is the exterior derivative of a
periodic continuously differentiable form is zero.  Contracting against a period direction and
averaging over that period removes the directional derivative from the Cartan formula and lowers the
degree, so the statement follows by induction from the case of a one-form, where the period average
of the derivative of a periodic function vanishes.

* `periodAverage_deriv_eq_zero` : the average of a directional derivative along a period vanishes.
* `constantForm_eq_zero` : the vanishing statement, in every degree.
-/

namespace GaloisForLFunctions.HTGeometry

open ContinuousAlternatingMap

section PeriodAverage

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [SMulCommClass ℝ 𝕜 X] [CompleteSpace X]

omit [SMulCommClass ℝ 𝕜 X] in
/-- **The average of a directional derivative along a period vanishes.** -/
theorem periodAverage_deriv_eq_zero {p : 𝕜} {β : (Fin r → 𝕜) → X} (hdiff : Differentiable 𝕜 β)
    (hcont : Continuous (fderiv 𝕜 β)) (j : Fin r)
    (hper : ∀ w : Fin r → 𝕜, β (w + p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) = β w)
    (w : Fin r → 𝕜) :
    ∫ s in (0 : ℝ)..1,
      (fderiv 𝕜 β (periodCurve p w j s)) (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) = 0 := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => β (periodCurve p w j t))
      ((fderiv 𝕜 β (periodCurve p w j s)) (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))) s := by
    intro s
    have hfd := (hdiff (periodCurve p w j s)).hasFDerivAt
    exact (hfd.restrictScalars ℝ).comp_hasDerivAt s (periodCurve_hasDerivAt p w j s)
  have hintegrand : Continuous fun s : ℝ =>
      (fderiv 𝕜 β (periodCurve p w j s)) (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) :=
    (ContinuousLinearMap.apply 𝕜 X
      (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))).continuous.comp
      (hcont.comp (continuous_periodCurve p w j))
  rw [_root_.intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
    (hintegrand.intervalIntegrable 0 1)]
  rw [periodCurve_zero, periodCurve_one, hper w, sub_self]

end PeriodAverage

section ConstantExact

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ}

/-- **A constant one-form that is the derivative of a periodic function vanishes.**  This is the
base case of the separation of the generators in cohomology: a constant form killed by a periodic
primitive is zero. -/
theorem constant_functional_eq_zero {p : 𝕜} (hp : p ≠ 0) {β : (Fin r → 𝕜) → 𝕜}
    {α : (Fin r → 𝕜) →L[𝕜] 𝕜} (hderiv : ∀ w : Fin r → 𝕜, HasFDerivAt β α w)
    (hper : ∀ (j : Fin r) (w : Fin r → 𝕜),
      β (w + p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) = β w) :
    α = 0 := by
  have hfd : fderiv 𝕜 β = fun _ => α := by
    funext w
    exact (hderiv w).fderiv
  have hdiff : Differentiable 𝕜 β := fun w => (hderiv w).differentiableAt
  have hcont : Continuous (fderiv 𝕜 β) := by
    rw [hfd]
    exact continuous_const
  refine clm_eq_zero_of_single fun j => ?_
  have hzero := periodAverage_deriv_eq_zero hdiff hcont j (hper j) (0 : Fin r → 𝕜)
  rw [hfd] at hzero
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hzero
  have hsmul : α (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) =
      p * α (Pi.single j (1 : 𝕜) : Fin r → 𝕜) := by
    rw [map_smul, smul_eq_mul]
  rw [hsmul] at hzero
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd h hp
  · exact h

end ConstantExact

section ConstantVanishing

variable {𝕜 : Type*} [RCLike 𝕜] {r : ℕ}

/-- **A constant form that is the exterior derivative of a periodic `C^1` form vanishes.** -/
theorem constantForm_eq_zero {p : 𝕜} (hp : p ≠ 0) :
    ∀ (n : ℕ) (α : (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜)
    (β : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜), Differentiable 𝕜 β →
    Continuous (fderiv 𝕜 β) →
    (∀ (l : Fin r) (w : Fin r → 𝕜), β (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = β w) →
    (∀ w : Fin r → 𝕜, extDeriv β w = α) → α = 0 := by
  intro n
  induction n with
  | zero =>
      intro α β hdiff hcont' hper hd
      set b : (Fin r → 𝕜) → 𝕜 := fun w =>
        (ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 (Fin r → 𝕜) 𝕜 (Fin 0)).symm (β w) with hb
      set a : (Fin r → 𝕜) →L[𝕜] 𝕜 :=
        (ContinuousAlternatingMap.ofSubsingleton 𝕜 (Fin r → 𝕜) 𝕜 (0 : Fin 1)).symm α with ha
      have hβb : β = fun w => ContinuousAlternatingMap.constOfIsEmpty 𝕜 (Fin r → 𝕜) (Fin 0)
          (b w) := by
        funext w
        exact ((ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 (Fin r → 𝕜) 𝕜
          (Fin 0)).apply_symm_apply (β w)).symm
      have hbdiff : Differentiable 𝕜 b := by
        intro w
        exact (ContinuousLinearMap.differentiableAt
          ((ContinuousAlternatingMap.constOfIsEmptyLIE 𝕜 (Fin r → 𝕜) 𝕜
            (Fin 0)).symm.toContinuousLinearEquiv.toContinuousLinearMap)).comp w (hdiff w)
      have hbfd : ∀ w : Fin r → 𝕜, fderiv 𝕜 b w = a := by
        intro w
        have hdw := hd w
        rw [hβb, extDeriv_constOfIsEmpty] at hdw
        have := congrArg (ContinuousAlternatingMap.ofSubsingleton 𝕜 (Fin r → 𝕜) 𝕜
          (0 : Fin 1)).symm hdw
        rw [Equiv.symm_apply_apply] at this
        rw [this, ha]
      have hbper : ∀ (l : Fin r) (w : Fin r → 𝕜),
          b (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = b w := by
        intro l w
        rw [hb]
        exact congrArg _ (hper l w)
      have ha0 : a = 0 :=
        constant_functional_eq_zero hp
          (fun w => by rw [← hbfd w]; exact (hbdiff w).hasFDerivAt) hbper
      have hαa : α = ContinuousAlternatingMap.ofSubsingleton 𝕜 (Fin r → 𝕜) 𝕜 (0 : Fin 1) a := by
        rw [ha]
        exact ((ContinuousAlternatingMap.ofSubsingleton 𝕜 (Fin r → 𝕜) 𝕜
          (0 : Fin 1)).apply_symm_apply α).symm
      rw [hαa, ha0]
      ext v
      rfl
  | succ m ih =>
      intro α β hdiff hcont' hper hd
      refine form_eq_zero_of_contract fun j => ?_
      set V : Fin r → 𝕜 := p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜) with hV
      -- the contracted primitive
      set γ : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin m]→L[𝕜] 𝕜 :=
        fun w => contractCLM (𝕜 := 𝕜) V (β w) with hγ
      have hγdiff : Differentiable 𝕜 γ := by
        intro w
        exact ((contractCLM (𝕜 := 𝕜) (n := m) V).differentiableAt).comp w (hdiff w)
      have hγfd : ∀ w : Fin r → 𝕜,
          fderiv 𝕜 γ w = (contractCLM (𝕜 := 𝕜) V).comp (fderiv 𝕜 β w) := by
        intro w
        have h := ((contractCLM (𝕜 := 𝕜) (n := m) V).hasFDerivAt).comp w (hdiff w).hasFDerivAt
        exact h.fderiv
      have hγcont : Continuous (fderiv 𝕜 γ) := by
        have hfun : fderiv 𝕜 γ = fun w => (contractCLM (𝕜 := 𝕜) V).comp (fderiv 𝕜 β w) := by
          funext w
          exact hγfd w
        rw [hfun]
        exact isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk hcont')
      have hγper : ∀ (l : Fin r) (w : Fin r → 𝕜),
          γ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = γ w := by
        intro l w
        rw [hγ]
        exact congrArg _ (hper l w)
      -- the Cartan formula for the contracted primitive
      have hcartan : ∀ w : Fin r → 𝕜,
          extDeriv γ w = (fderiv 𝕜 β w) V - contractCLM (𝕜 := 𝕜) V α := by
        intro w
        rw [hγ, extDeriv_contract (hdiff w) V, cartan_contract]
        rw [show alternatizeUncurryFin (fderiv 𝕜 β w) = α from hd w]
      -- the average of the contracted primitive
      set δ := averageOp p γ j with hδ
      have hδper : ∀ (l : Fin r) (w : Fin r → 𝕜),
          δ (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = δ w :=
        fun l w => averageOp_periodic j (hγper l) w
      have hδdiff : Differentiable 𝕜 δ := averageOp_differentiable hγdiff hγcont j
      have hδcont : Continuous (fderiv 𝕜 δ) := averageOp_fderiv_continuous hγdiff hγcont j
      have hδd : ∀ w : Fin r → 𝕜, extDeriv δ w = -contractCLM (𝕜 := 𝕜) V α := by
        intro w
        rw [hδ, averageOp_extDeriv hγdiff hγcont j w]
        have hint : ∀ s : ℝ, extDeriv γ (periodCurve p w j s) =
            (fderiv 𝕜 β (periodCurve p w j s)) V - contractCLM (𝕜 := 𝕜) V α :=
          fun s => hcartan _
        rw [intervalIntegral.integral_congr (g := fun s =>
          (fderiv 𝕜 β (periodCurve p w j s)) V - contractCLM (𝕜 := 𝕜) V α)
          (fun s _ => hint s)]
        have hf : Continuous fun s : ℝ => (fderiv 𝕜 β (periodCurve p w j s)) V :=
          (ContinuousLinearMap.apply 𝕜 ((Fin r → 𝕜) [⋀^Fin (m + 1)]→L[𝕜] 𝕜) V).continuous.comp
            (hcont'.comp (continuous_periodCurve p w j))
        rw [intervalIntegral.integral_sub (hf.intervalIntegrable 0 1) (intervalIntegrable_const)]
        rw [hV, periodAverage_deriv_eq_zero hdiff hcont' j (hper j) w]
        simp
      have hcontract := ih (-contractCLM (𝕜 := 𝕜) V α) δ hδdiff hδcont hδper hδd
      have hVzero : contractCLM (𝕜 := 𝕜) V α = 0 := neg_eq_zero.1 hcontract
      rw [hV, contractCLM_smul] at hVzero
      have hinv : contractCLM (𝕜 := 𝕜) (Pi.single j (1 : 𝕜) : Fin r → 𝕜) α =
          p⁻¹ • (p • contractCLM (𝕜 := 𝕜) (Pi.single j (1 : 𝕜) : Fin r → 𝕜) α) := by
        rw [smul_smul, inv_mul_cancel₀ hp, one_smul]
      rw [hinv, hVzero]
      ext v
      show p⁻¹ • ((0 : (Fin r → 𝕜) [⋀^Fin (m + 1)]→L[𝕜] 𝕜) v) =
        (0 : (Fin r → 𝕜) [⋀^Fin (m + 1)]→L[𝕜] 𝕜) v
      rw [show ((0 : (Fin r → 𝕜) [⋀^Fin (m + 1)]→L[𝕜] 𝕜) v) = (0 : 𝕜) from rfl, smul_eq_mul,
        mul_zero]

end ConstantVanishing

end GaloisForLFunctions.HTGeometry
