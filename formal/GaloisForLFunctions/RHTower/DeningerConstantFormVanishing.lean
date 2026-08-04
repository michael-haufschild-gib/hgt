import GaloisForLFunctions.RHTower.DeningerContractDeriv
import GaloisForLFunctions.RHTower.DeningerPeriodAverage
import GaloisForLFunctions.RHTower.DeningerAverageOperator

/-!
# Constant forms with periodic primitives vanish

A form with constant coefficients on the covering space that is the exterior derivative of a
periodic continuously differentiable form is zero.  Contracting against a period direction and
averaging over that period removes the directional derivative from the Cartan formula and lowers the
degree, so the statement follows by induction from the case of a one-form, where the period average
of the derivative of a periodic function vanishes.

* `deningerConstantForm_eq_zero` : the vanishing statement, in every degree.
-/

namespace RHTower

open ContinuousAlternatingMap Complex

section ConstantVanishing

variable {r : ℕ}

/-- **A constant form that is the exterior derivative of a periodic `C^1` form vanishes.** -/
theorem deningerConstantForm_eq_zero : ∀ (n : ℕ) (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (β : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ), Differentiable ℂ β →
    Continuous (fderiv ℂ β) →
    (∀ (l : Fin r) (w : Fin r → ℂ),
      β (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = β w) →
    (∀ w : Fin r → ℂ, extDeriv β w = α) → α = 0 := by
  intro n
  induction n with
  | zero =>
      intro α β hdiff hcont' hper hd
      set b : (Fin r → ℂ) → ℂ := fun w =>
        (ContinuousAlternatingMap.constOfIsEmptyLIE ℂ (Fin r → ℂ) ℂ (Fin 0)).symm (β w) with hb
      set a : (Fin r → ℂ) →L[ℂ] ℂ :=
        (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ (0 : Fin 1)).symm α with ha
      have hβb : β = fun w => ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin r → ℂ) (Fin 0)
          (b w) := by
        funext w
        exact ((ContinuousAlternatingMap.constOfIsEmptyLIE ℂ (Fin r → ℂ) ℂ
          (Fin 0)).apply_symm_apply (β w)).symm
      have hbdiff : Differentiable ℂ b := by
        intro w
        exact (ContinuousLinearMap.analyticAt
          ((ContinuousAlternatingMap.constOfIsEmptyLIE ℂ (Fin r → ℂ) ℂ
            (Fin 0)).symm.toContinuousLinearEquiv.toContinuousLinearMap)
          (β w)).differentiableAt.comp w (hdiff w)
      have hbfd : ∀ w : Fin r → ℂ, fderiv ℂ b w = a := by
        intro w
        have hdw := hd w
        rw [hβb, extDeriv_constOfIsEmpty] at hdw
        have := congrArg (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ
          (0 : Fin 1)).symm hdw
        rw [Equiv.symm_apply_apply] at this
        rw [this, ha]
      have hbper : ∀ (l : Fin r) (w : Fin r → ℂ),
          b (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = b w := by
        intro l w
        rw [hb]
        exact congrArg _ (hper l w)
      have ha0 : a = 0 :=
        deningerConstant_functional_eq_zero
          (fun w => by rw [← hbfd w]; exact (hbdiff w).hasFDerivAt) hbper
      have : α = ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ (0 : Fin 1) a := by
        rw [ha]
        exact ((ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ
          (0 : Fin 1)).apply_symm_apply α).symm
      rw [this, ha0]
      ext v
      rfl
  | succ m ih =>
      intro α β hdiff hcont' hper hd
      refine deningerForm_eq_zero_of_contract fun j => ?_
      set X : Fin r → ℂ := (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ) with hX
      -- the contracted primitive
      set γ : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin m]→L[ℂ] ℂ :=
        fun w => deningerContractCLM X (β w) with hγ
      have hγdiff : Differentiable ℂ γ := by
        intro w
        exact ((deningerContractCLM (n := m) X).differentiableAt).comp w (hdiff w)
      have hγfd : ∀ w : Fin r → ℂ,
          fderiv ℂ γ w = (deningerContractCLM X).comp (fderiv ℂ β w) := by
        intro w
        have h := ((deningerContractCLM (n := m) X).hasFDerivAt).comp w (hdiff w).hasFDerivAt
        exact h.fderiv
      have hγcont : Continuous (fderiv ℂ γ) := by
        have hfun : fderiv ℂ γ = fun w => (deningerContractCLM X).comp (fderiv ℂ β w) := by
          funext w
          exact hγfd w
        rw [hfun]
        exact isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk hcont')
      have hγper : ∀ (l : Fin r) (w : Fin r → ℂ),
          γ (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = γ w := by
        intro l w
        rw [hγ]
        exact congrArg _ (hper l w)
      -- the Cartan formula for the contracted primitive
      have hcartan : ∀ w : Fin r → ℂ,
          extDeriv γ w = (fderiv ℂ β w) X - deningerContractCLM X α := by
        intro w
        rw [hγ, deningerExtDeriv_contract (hdiff w) X, deningerCartan_contract]
        rw [show alternatizeUncurryFin (fderiv ℂ β w) = α from hd w]
      -- the average of the contracted primitive
      set δ := deningerAverageOp γ j with hδ
      have hδper : ∀ (l : Fin r) (w : Fin r → ℂ),
          δ (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = δ w :=
        fun l w => deningerAverageOp_periodic j (hγper l) w
      have hδdiff : Differentiable ℂ δ := deningerAverageOp_differentiable hγdiff hγcont j
      have hδcont : Continuous (fderiv ℂ δ) :=
        deningerAverageOp_fderiv_continuous hγdiff hγcont j
      have hδd : ∀ w : Fin r → ℂ, extDeriv δ w = -deningerContractCLM X α := by
        intro w
        rw [hδ, deningerAverageOp_extDeriv hγdiff hγcont j w]
        have hint : ∀ s : ℝ, extDeriv γ (deningerPeriodCurve w j s) =
            (fderiv ℂ β (deningerPeriodCurve w j s)) X - deningerContractCLM X α :=
          fun s => hcartan _
        rw [intervalIntegral.integral_congr (g := fun s =>
          (fderiv ℂ β (deningerPeriodCurve w j s)) X - deningerContractCLM X α)
          (fun s _ => hint s)]
        have hcurvecont : Continuous (deningerPeriodCurve w j) := by
          show Continuous fun s : ℝ =>
            w + ((s : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)
          fun_prop
        have hf : Continuous fun s : ℝ => (fderiv ℂ β (deningerPeriodCurve w j s)) X :=
          (ContinuousLinearMap.apply ℂ ((Fin r → ℂ) [⋀^Fin (m + 1)]→L[ℂ] ℂ) X).continuous.comp
            (hcont'.comp hcurvecont)
        rw [intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
          (intervalIntegrable_const)]
        rw [hX, deningerPeriodAverage_deriv_eq_zero hdiff hcont' j (hper j) w]
        simp
      have hcontract := ih (-deningerContractCLM X α) δ hδdiff hδcont hδper hδd
      have hXzero : deningerContractCLM X α = 0 := by
        have := neg_eq_zero.1 hcontract
        exact this
      -- contraction is linear in the vector
      have hsmul : deningerContractCLM X α =
          (2 * Real.pi * Complex.I) •
            deningerContractCLM (Pi.single j (1 : ℂ) : Fin r → ℂ) α := by
        rw [hX]
        show (deningerContractL (n := m + 1)
          ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ))) α = _
        rw [map_smul]
        rfl
      rw [hsmul] at hXzero
      have htwopi : (2 * Real.pi * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hinv : deningerContractCLM (Pi.single j (1 : ℂ) : Fin r → ℂ) α =
          (2 * Real.pi * Complex.I)⁻¹ • ((2 * Real.pi * Complex.I) •
            deningerContractCLM (Pi.single j (1 : ℂ) : Fin r → ℂ) α) := by
        rw [smul_smul, inv_mul_cancel₀ htwopi, one_smul]
      rw [hinv, hXzero]
      ext v
      show (2 * Real.pi * Complex.I)⁻¹ • ((0 : (Fin r → ℂ) [⋀^Fin (m + 1)]→L[ℂ] ℂ) v) =
        (0 : (Fin r → ℂ) [⋀^Fin (m + 1)]→L[ℂ] ℂ) v
      rw [show ((0 : (Fin r → ℂ) [⋀^Fin (m + 1)]→L[ℂ] ℂ) v) = (0 : ℂ) from rfl, smul_eq_mul,
        mul_zero]

end ConstantVanishing

end RHTower
