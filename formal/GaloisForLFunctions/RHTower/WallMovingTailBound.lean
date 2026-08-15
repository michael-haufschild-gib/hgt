import GaloisForLFunctions.RHTower.WallTailRayComposition

/-!
# The moving tail is bounded by its four terms

Putting the block decomposition together with the frequency measurability of three of its four terms,
the moving part of the propagated tail obeys

`‖moving tail‖²_{L²(ray)} ≤ 16(‖first boundary‖² + ‖second boundary‖² + ‖propagated threshold‖²
                              + ‖remainder‖²)`,

each summand measured on the same ray.  The factor is the only price of the composition: four terms
in the extended norm cost sixteen in the square, and the scalar `−i/2` in front is unimodular up to a
half.

Two small facts do the rest of the work.  The numerical floor grows with the frequency, so the gap
assumed at the threshold holds at every larger frequency and in particular on the whole integration
interval — the decomposition therefore applies at every point of the ray from a single hypothesis at
the threshold.  And the Gamma propagator is continuous along the shifted line, which is what makes
the propagated threshold term measurable.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [Nontrivial X] in
theorem stripPropagator_eq_scalar_smul (E : ℂ → ℂ) (T : X →L[ℂ] X) (z : ℂ) :
    stripPropagator E T z
      = stripScalar E z • NormedSpace.exp ((-(Complex.I / 2) * z) • T) := by
  rw [stripPropagator, stripTransport, smul_smul, stripScalar]

omit [Nontrivial X] in
/-- **The Gamma propagator is continuous along the shifted line.** -/
theorem continuous_stripPropagator_line
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous fun x : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  have hscal : Continuous fun x : ℝ => stripScalar E ((x : ℂ) + (σ : ℂ) * Complex.I) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (hasDerivAt_stripScalar_line hEdiff hE hEne hσ0 hσ1 x).continuousAt
  have hexp : Continuous fun x : ℝ =>
      NormedSpace.exp ((-(Complex.I / 2) * ((x : ℂ) + (σ : ℂ) * Complex.I)) • T) := by
    refine NormedSpace.exp_continuous.comp ?_
    have hlin : Continuous fun x : ℝ => (-(Complex.I / 2) * ((x : ℂ) + (σ : ℂ) * Complex.I)) := by
      fun_prop
    exact hlin.smul continuous_const
  have h : Continuous fun x : ℝ =>
      stripScalar E ((x : ℂ) + (σ : ℂ) * Complex.I)
        • NormedSpace.exp ((-(Complex.I / 2) * ((x : ℂ) + (σ : ℂ) * Complex.I)) • T) :=
    hscal.smul hexp
  refine h.congr fun x => ?_
  rw [stripPropagator_eq_scalar_smul]

omit [Nontrivial X] [CompleteSpace X] in
/-- The floor grows with the frequency. -/
theorem wallFloor_mono {σ Y t : ℝ} (hY : 0 ≤ Y) (hYt : Y ≤ t) :
    wallFloor T σ Y ≤ wallFloor T σ t := by
  have habsY : |Y| = Y := abs_of_nonneg hY
  have habst : |t| = t := abs_of_nonneg (le_trans hY hYt)
  rw [wallFloor, wallFloor, habsY, habst]
  have : Real.log (2 + Y) ≤ Real.log (2 + t) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

set_option maxHeartbeats 1000000 in
/-- **The four ray estimates compose.**  The moving part of the propagated tail is bounded by four
times the sum of the four terms' ray masses. -/
theorem lintegral_sq_movingTail_le
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m Y μ₀ : ℝ} (hg : IntegrableOn g (Icc m (m + 1)))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hY1 : 1 ≤ Y) (hμ : 0 < μ₀)
    (hgapY : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ Y + L) :
    (∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (∫ t in Y..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
          (blockSource g m t))‖ₑ ^ 2)
      ≤ 16 * ((∫⁻ x in Ioi Y, ‖firstBoundary T g σ x‖ₑ ^ 2)
          + (∫⁻ x in Ioi Y, ‖secondBoundary T g m σ x‖ₑ ^ 2)
          + (∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
              (thresholdVector E T g m σ Y)‖ₑ ^ 2)
          + ∫⁻ x in Ioi Y, ‖tailRemainder E T g m σ Y x‖ₑ ^ 2) := by
  have hY0 : (0 : ℝ) ≤ Y := le_trans zero_le_one hY1
  -- the floor propagates to every larger frequency
  have hgapt : ∀ t : ℝ, Y ≤ t → ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ t + L := by
    intro t hYt L hL
    have := hgapY L hL
    have hmono := wallFloor_mono (T := T) (σ := σ) hY0 hYt
    linarith
  have hgapray : ∀ x ∈ Ioi Y, ∀ L ∈ Icc m (m + 1), 0 < wallFloor T σ x + L := by
    intro x hx L hL
    exact lt_of_lt_of_le hμ (hgapt x (le_of_lt hx) L hL)
  -- the pointwise bound
  have hpt : ∀ x ∈ Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      (∫ t in Y..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
        (blockSource g m t))‖ₑ ^ 2
      ≤ 16 * (‖firstBoundary T g σ x‖ₑ ^ 2 + ‖secondBoundary T g m σ x‖ₑ ^ 2
          + ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
              (thresholdVector E T g m σ Y)‖ₑ ^ 2
          + ‖tailRemainder E T g m σ Y x‖ₑ ^ 2) := by
    intro x hx
    have hYx : Y ≤ x := le_of_lt hx
    have hdec := stripPropagator_movingTail_decomposition hEdiff hE hEne hT hσ0 hσ1 hg hYx hY1 hμ
      (fun L hL => hgapt x hYx L hL) hgapY
      (fun L hL t ht => by
        have hty : Y ≤ t := by
          rcases (uIcc_of_le hYx) ▸ ht with ⟨h1, _⟩
          exact h1
        exact lt_of_lt_of_le hμ (hgapt t hty L hL))
    rw [hdec, firstBoundaryBlock_eq_firstBoundary hsupp]
    have hnorm : ‖(-(Complex.I) / 2 : ℂ) • ((Complex.I : ℂ) • firstBoundary T g σ x
        + secondBoundary T g m σ x
        - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (thresholdVector E T g m σ Y)
        - tailRemainder E T g m σ Y x)‖ₑ
        ≤ ‖firstBoundary T g σ x‖ₑ + ‖secondBoundary T g m σ x‖ₑ
          + ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
              (thresholdVector E T g m σ Y)‖ₑ
          + ‖tailRemainder E T g m σ Y x‖ₑ := by
      have hc : ‖(-(Complex.I) / 2 : ℂ)‖ₑ ≤ 1 := by
        rw [← ofReal_norm]
        refine (ENNReal.ofReal_le_one).mpr ?_
        rw [norm_div, norm_neg, Complex.norm_I]
        norm_num
      calc ‖(-(Complex.I) / 2 : ℂ) • _‖ₑ = ‖(-(Complex.I) / 2 : ℂ)‖ₑ * ‖_‖ₑ := by
            rw [enorm_smul]
        _ ≤ 1 * ‖(Complex.I : ℂ) • firstBoundary T g σ x + secondBoundary T g m σ x
              - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                  (thresholdVector E T g m σ Y)
              - tailRemainder E T g m σ Y x‖ₑ := mul_le_mul' hc le_rfl
        _ = ‖(Complex.I : ℂ) • firstBoundary T g σ x + secondBoundary T g m σ x
              - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                  (thresholdVector E T g m σ Y)
              - tailRemainder E T g m σ Y x‖ₑ := one_mul _
        _ ≤ ‖(Complex.I : ℂ) • firstBoundary T g σ x + secondBoundary T g m σ x
              - stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                  (thresholdVector E T g m σ Y)‖ₑ
            + ‖tailRemainder E T g m σ Y x‖ₑ := enorm_sub_le
        _ ≤ (‖(Complex.I : ℂ) • firstBoundary T g σ x + secondBoundary T g m σ x‖ₑ
              + ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                  (thresholdVector E T g m σ Y)‖ₑ)
            + ‖tailRemainder E T g m σ Y x‖ₑ :=
            add_le_add enorm_sub_le le_rfl
        _ ≤ ((‖(Complex.I : ℂ) • firstBoundary T g σ x‖ₑ + ‖secondBoundary T g m σ x‖ₑ)
              + ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                  (thresholdVector E T g m σ Y)‖ₑ)
            + ‖tailRemainder E T g m σ Y x‖ₑ :=
            add_le_add (add_le_add (enorm_add_le _ _) le_rfl) le_rfl
        _ = ‖firstBoundary T g σ x‖ₑ + ‖secondBoundary T g m σ x‖ₑ
            + ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (thresholdVector E T g m σ Y)‖ₑ
            + ‖tailRemainder E T g m σ Y x‖ₑ := by
            have hI : ‖(Complex.I : ℂ)‖ₑ = 1 := by
              rw [← ofReal_norm, Complex.norm_I]
              simp
            rw [enorm_smul, hI, one_mul]
    calc ‖(-(Complex.I) / 2 : ℂ) • _‖ₑ ^ 2
        ≤ (‖firstBoundary T g σ x‖ₑ + ‖secondBoundary T g m σ x‖ₑ
            + ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (thresholdVector E T g m σ Y)‖ₑ
            + ‖tailRemainder E T g m σ Y x‖ₑ) ^ 2 := pow_le_pow_left' hnorm 2
      _ ≤ 16 * (‖firstBoundary T g σ x‖ₑ ^ 2 + ‖secondBoundary T g m σ x‖ₑ ^ 2
            + ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (thresholdVector E T g m σ Y)‖ₑ ^ 2
            + ‖tailRemainder E T g m σ Y x‖ₑ ^ 2) := sq_add_four_le _ _ _ _
  -- the split
  have hA0 : AEStronglyMeasurable (fun x => firstBoundary T g σ x) (volume.restrict (Ioi Y)) := by
    have h := aestronglyMeasurable_firstBoundaryBlock (T := T) (m := m) (Y := Y) hσ0 hσ1
      hg.aestronglyMeasurable hgapray
    refine h.congr ?_
    filter_upwards with x
    exact firstBoundaryBlock_eq_firstBoundary hsupp
  have hB0 : AEStronglyMeasurable (fun x => secondBoundary T g m σ x)
      (volume.restrict (Ioi Y)) :=
    aestronglyMeasurable_secondBoundary (T := T) (Y := Y) hσ0 hσ1 hg.aestronglyMeasurable hgapray
  have hC0 : AEStronglyMeasurable (fun x : ℝ =>
      stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (thresholdVector E T g m σ Y)) (volume.restrict (Ioi Y)) := by
    have hcont := continuous_stripPropagator_line (T := T) hEdiff hE hEne hσ0 hσ1
    exact (hcont.aestronglyMeasurable).apply_continuousLinearMap _
  have hA : AEMeasurable (fun x : ℝ => ‖firstBoundary T g σ x‖ₑ ^ 2)
      (volume.restrict (Ioi Y)) := hA0.enorm.pow_const 2
  have hB : AEMeasurable (fun x : ℝ => ‖secondBoundary T g m σ x‖ₑ ^ 2)
      (volume.restrict (Ioi Y)) := hB0.enorm.pow_const 2
  have hC : AEMeasurable (fun x : ℝ =>
      ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (thresholdVector E T g m σ Y)‖ₑ ^ 2) (volume.restrict (Ioi Y)) := hC0.enorm.pow_const 2
  have hAB : AEMeasurable (fun x : ℝ => ‖firstBoundary T g σ x‖ₑ ^ 2
      + ‖secondBoundary T g m σ x‖ₑ ^ 2) (volume.restrict (Ioi Y)) := hA.add hB
  have hABC : AEMeasurable (fun x : ℝ => ‖firstBoundary T g σ x‖ₑ ^ 2
      + ‖secondBoundary T g m σ x‖ₑ ^ 2
      + ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (thresholdVector E T g m σ Y)‖ₑ ^ 2) (volume.restrict (Ioi Y)) := hAB.add hC
  refine le_trans (setLIntegral_mono' measurableSet_Ioi hpt) ?_
  rw [lintegral_const_mul' _ _ (by simp : (16 : ℝ≥0∞) ≠ ⊤)]
  refine mul_le_mul' le_rfl (le_of_eq ?_)
  rw [lintegral_add_left' hABC, lintegral_add_left' hAB, lintegral_add_left' hA]

end GaloisForLFunctions.RHTower
