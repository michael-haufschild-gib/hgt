import GaloisForLFunctions.RHTower.DirichletPolyPerronMass

/-!
# Perron strip-mass interface discharge

The carrier flank and horizontal masses already contain all four integrability clauses of
`HasPerronStripMassAt`.  This module exposes that construction, then instantiates it for the finite
Dirichlet carrier.  The aggregate strip-mass Prop is therefore no longer an uninhabited producer
interface.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology intervalIntegral Set
open scoped Topology Interval

/-- Flank mass plus horizontal carrier mass constructs every clause of the aggregate strip-mass
producer. -/
theorem hasPerronStripMassAt_of_carrierMassesAt
    {F : ℂ → ℂ} {a : ℕ → ℂ} {c δ A : ℝ} {n M : ℕ}
    (hflank : HasPerronCarrierFlankMassAt F M A)
    (hhorizontal : HasPerronCarrierHorizontalMassAt F c M)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    HasPerronStripMassAt F c n δ M
      (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) * A) := by
  let C : ℝ := 4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ))
  have hDpos : 0 < perronSupportScaleAt n δ := by
    rw [perronSupportScaleAt]
    linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hDpos.le _)
  have hleftPoint : ∀ y : ℝ,
      ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖ ≤
        C * perronCarrierFlankWeight F M y := by
    intro y
    rw [perronContourIntegrand, norm_mul]
    have hE := perronEAt_left_flank_norm_le hn hM hδ0 hδn (y := y)
    calc
      ‖F (↑(-(M : ℝ)) + ↑y * I)‖ *
          ‖perronEAt n δ (↑(-(M : ℝ)) + ↑y * I)‖ ≤
          ‖F (↑(-(M : ℝ)) + ↑y * I)‖ * (C / (1 + y ^ 2)) :=
        mul_le_mul_of_nonneg_left hE (norm_nonneg _)
      _ = C * perronCarrierFlankWeight F M y := by
        unfold perronCarrierFlankWeight
        ring
  have hleftMeas : AEStronglyMeasurable (fun y : ℝ =>
      ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖) :=
    (((hF.mul (perronEAt_differentiable hn hδ0 hδn)).continuous.comp
      (by fun_prop)).norm).aestronglyMeasurable
  have hCint : Integrable (fun y : ℝ => C * perronCarrierFlankWeight F M y) :=
    hflank.1.const_mul C
  have hleftInt : Integrable (fun y : ℝ =>
      ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖) :=
    hCint.mono' hleftMeas (Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hleftPoint y)
  refine ⟨perronContourIntegrand_right_integrable hc0 hsum hF hFeq hn hδ0 hδn,
    hhorizontal.perronHorizontalContourNorm_integrableOn_Ioi hF hc0 hn hδ0 hδn,
    hleftInt, ?_⟩
  calc
    (∫ y : ℝ, ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖) ≤
        ∫ y : ℝ, C * perronCarrierFlankWeight F M y :=
      integral_mono hleftInt hCint hleftPoint
    _ = C * ∫ y : ℝ, perronCarrierFlankWeight F M y := integral_const_mul C _
    _ ≤ C * A := mul_le_mul_of_nonneg_left hflank.2 hC
    _ = 4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) * A := rfl

/-- The finite Dirichlet carrier inhabits the aggregate strip-mass interface with no Prop-valued
inputs. -/
theorem dirichletPoly_hasPerronStripMassAt
    (N : ℕ) {c δ : ℝ} {n M : ℕ}
    (hc : 0 < c) (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    HasPerronStripMassAt (dirichletPoly N) c n δ M
      (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) *
        (dirichletPolyPerronBudget N M * Real.pi)) := by
  exact hasPerronStripMassAt_of_carrierMassesAt
    (dirichletPoly_hasPerronCarrierFlankMassAt N M)
    (dirichletPoly_hasPerronCarrierHorizontalMassAt N M
      (le_trans (neg_nonpos.mpr (Nat.cast_nonneg M)) hc.le))
    hc (dirichletPolyCoeff_lseriesSummable N c) (dirichletPoly_differentiable N)
    (fun s _ => (LSeries_dirichletPolyCoeff N s).symm) hn hM hδ0 hδn

end RHTower
