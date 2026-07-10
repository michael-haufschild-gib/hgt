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

/-- Weighted horizontal carrier mass gives integrability of the actual pair of horizontal Perron
edge norms over all positive heights. -/
theorem HasPerronCarrierHorizontalMassAt.perronHorizontalContourNorm_integrableOn_Ioi
    {F : ℂ → ℂ} {c δ : ℝ} {n M : ℕ}
    (hmass : HasPerronCarrierHorizontalMassAt F c M)
    (hF : Differentiable ℂ F) (hc0 : 0 < c)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    IntegrableOn (fun T : ℝ =>
      ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑T * I)‖ +
      ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(-T) * I)‖)
      (Ioi 0) := by
  let K : ℝ := perronStripKernelEnvelope n M δ c
  let u : ℝ → ℝ := fun T =>
    ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑T * I)‖ +
    ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(-T) * I)‖
  have hMc : -(M : ℝ) ≤ c := by
    have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hK0 : 0 ≤ K := by
    dsimp [K, perronStripKernelEnvelope]
    positivity
  have hGcont : Continuous (perronContourIntegrand F n δ) :=
    (hF.mul (perronEAt_differentiable hn hδ0 hδn)).continuous
  have htopcont : Continuous (fun T : ℝ =>
      ∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑T * I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hGcont.comp (by fun_prop)
  have hbotcont : Continuous (fun T : ℝ =>
      ∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(-T) * I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hGcont.comp (by fun_prop)
  have hucont : Continuous u := htopcont.norm.add hbotcont.norm
  have hhigh : ∀ T : ℝ, 1 < T →
      u T ≤ K * perronCarrierHorizontalWeight F c M T := by
    intro T hT
    have hTabs : 1 ≤ |T| := le_trans hT.le (le_abs_self T)
    have hnegTabs : 1 ≤ |-T| := by simpa using hTabs
    let ftop : ℝ → ℝ := fun x =>
      ‖perronContourIntegrand F n δ (↑x + ↑T * I)‖
    let fbot : ℝ → ℝ := fun x =>
      ‖perronContourIntegrand F n δ (↑x + ↑(-T) * I)‖
    let gtop : ℝ → ℝ := fun x => K * ‖F (↑x + ↑T * I)‖ / (1 + T ^ 2)
    let gbot : ℝ → ℝ := fun x => K * ‖F (↑x + ↑(-T) * I)‖ / (1 + T ^ 2)
    have hftop : IntervalIntegrable ftop volume (-(M : ℝ)) c := by
      exact (hGcont.comp (by fun_prop)).norm.intervalIntegrable _ _
    have hfbot : IntervalIntegrable fbot volume (-(M : ℝ)) c := by
      exact (hGcont.comp (by fun_prop)).norm.intervalIntegrable _ _
    have hgtop : IntervalIntegrable gtop volume (-(M : ℝ)) c := by
      have hgcont : Continuous gtop := by
        dsimp [gtop]
        have hline : Continuous (fun x : ℝ => F (↑x + ↑T * I)) :=
          hF.continuous.comp (by fun_prop)
        exact (continuous_const.mul hline.norm).div_const _
      exact hgcont.intervalIntegrable _ _
    have hgbot : IntervalIntegrable gbot volume (-(M : ℝ)) c := by
      have hgcont : Continuous gbot := by
        dsimp [gbot]
        have hline : Continuous (fun x : ℝ => F (↑x + ↑(-T) * I)) :=
          hF.continuous.comp (by fun_prop)
        exact (continuous_const.mul hline.norm).div_const _
      exact hgcont.intervalIntegrable _ _
    have htopPoint : ∀ x ∈ Icc (-(M : ℝ)) c, ftop x ≤ gtop x := by
      intro x hx
      have hE := perronEAt_strip_high_norm_le hn hδ0 hδn hx.1 hx.2 hTabs
      dsimp [ftop, gtop]
      rw [perronContourIntegrand, norm_mul]
      calc
        ‖F (↑x + ↑T * I)‖ * ‖perronEAt n δ (↑x + ↑T * I)‖ ≤
            ‖F (↑x + ↑T * I)‖ * (K / (1 + T ^ 2)) :=
          mul_le_mul_of_nonneg_left hE (norm_nonneg _)
        _ = K * ‖F (↑x + ↑T * I)‖ / (1 + T ^ 2) := by ring
    have hbotPoint : ∀ x ∈ Icc (-(M : ℝ)) c, fbot x ≤ gbot x := by
      intro x hx
      have hE := perronEAt_strip_high_norm_le hn hδ0 hδn hx.1 hx.2 hnegTabs
      dsimp [fbot, gbot]
      rw [perronContourIntegrand, norm_mul]
      calc
        ‖F (↑x + ↑(-T) * I)‖ * ‖perronEAt n δ (↑x + ↑(-T) * I)‖ ≤
            ‖F (↑x + ↑(-T) * I)‖ * (K / (1 + (-T) ^ 2)) :=
          mul_le_mul_of_nonneg_left hE (norm_nonneg _)
        _ = K * ‖F (↑x + ↑(-T) * I)‖ / (1 + T ^ 2) := by ring
    calc
      u T ≤ (∫ x in (-(M : ℝ))..c, ftop x) +
          ∫ x in (-(M : ℝ))..c, fbot x := by
        dsimp [u, ftop, fbot]
        gcongr <;> exact intervalIntegral.norm_integral_le_integral_norm hMc
      _ ≤ (∫ x in (-(M : ℝ))..c, gtop x) +
          ∫ x in (-(M : ℝ))..c, gbot x := by
        gcongr
        · exact intervalIntegral.integral_mono_on hMc hftop hgtop htopPoint
        · exact intervalIntegral.integral_mono_on hMc hfbot hgbot hbotPoint
      _ = K * perronCarrierHorizontalWeight F c M T := by
        unfold perronCarrierHorizontalWeight
        dsimp [gtop, gbot]
        rw [← intervalIntegral.integral_add hgtop hgbot]
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext x
        ring
  have huHigh : IntegrableOn u (Ioi 1) := by
    have hKmass : IntegrableOn (fun T => K * perronCarrierHorizontalWeight F c M T)
        (Ioi 1) := hmass.const_mul K
    refine hKmass.mono' hucont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [u]; positivity)]
    exact hhigh T hT
  have huLow : IntegrableOn u (Ioc 0 1) := hucont.integrableOn_Ioc
  have huInt : IntegrableOn u (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact huLow.union huHigh
  exact huInt

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
