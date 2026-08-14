import GaloisForLFunctions.RHTower.SmoothAFEZetaDualWeightHeightDerivative

/-!
# Conductor-scale derivative bound for the exact dual weight

The neutral logarithmic slope controls central frequencies, while the global
polynomial derivative envelope controls the complementary Gaussian tail.
Their combination gives an integrable height-independent majorant and an
`O(1/tau)` derivative bound at conductor scale `Y=tau`.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- A quartic polynomial is still integrable against the standard Gaussian. -/
theorem integrable_one_add_abs_pow_four_mul_exp_neg_sq :
    Integrable (fun v : ℝ => (1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
  have hk (k : ℕ) :
      Integrable (fun v : ℝ => |v| ^ k * Real.exp (-(v ^ 2))) := by
    have hraw := integrable_rpow_mul_exp_neg_mul_sq
      (b := (1 : ℝ)) (s := (k : ℝ)) (by norm_num)
        (by have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using hraw.norm
  have h0 : Integrable (fun v : ℝ => Real.exp (-(v ^ 2))) := by
    simpa using hk 0
  have hsum := (((h0.add ((hk 1).const_mul 4)).add ((hk 2).const_mul 6)).add
    ((hk 3).const_mul 4)).add (hk 4)
  refine hsum.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [Pi.add_apply]
  ring

/-- Central neutral variation and the outer Gaussian tail admit one quartic-Gaussian
majorant of total scale `1/tau`. -/
theorem exists_norm_dualHeightDerivativeIntegrand_le_invScale_gaussianQuartic :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y → ∀ v : ℝ,
      ‖smoothAFEZetaDualWeightHeightDerivativeIntegrand tau Y v‖ ≤
        (K / Y) * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
  obtain ⟨D, hD, hglobal⟩ :=
    exists_norm_deriv_smoothAFEZetaChiShiftRatio_le_global
  let C : ℝ := 6 + 2 * Real.pi
  let K : ℝ := 6 * C + 12 * D
  refine ⟨K, by dsimp only [K, C]; positivity, ?_⟩
  intro tau Y htau hY v
  have htau0 : 0 < tau := by linarith
  have habstau : |tau| = tau := abs_of_pos htau0
  have hm := norm_smoothAFEMellinIntegrand_vertical_le hY
    (show (0 : ℝ) < 1 by norm_num) v
  have hm' :
      ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖ ≤
        (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2)) := by
    simpa [Real.rpow_neg_one] using hm
  have hexp1 : Real.exp (1 : ℝ) ≤ 3 := by
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  by_cases hv : 2 * |v| ≤ tau
  · have hder :=
      norm_deriv_smoothAFEZetaChiShiftRatio_neg_right_one_line_le htau hv
    rw [(hasDerivAt_chiShift_eq_heightDerivative tau v).deriv] at hder
    have hratio := norm_smoothAFEZetaChiShiftRatio_neg_right_one_le tau v
    have hscale : (1 + tau) * tau⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ htau0]
      linarith
    have hpowers : (1 + |v|) ^ 2 ≤ (1 + |v|) ^ 4 := by
      have hsq : 1 ≤ (1 + |v|) ^ 2 := by
        nlinarith [abs_nonneg v]
      calc
        (1 + |v|) ^ 2 = (1 + |v|) ^ 2 * 1 := by ring
        _ ≤ (1 + |v|) ^ 2 * (1 + |v|) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg (1 + |v|))
        _ = (1 + |v|) ^ 4 := by ring
    have hinner : ((1 + tau) * tau⁻¹) * (1 + |v|) ^ 2 *
          Real.exp (-(v ^ 2)) ≤
        2 * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
      calc
        ((1 + tau) * tau⁻¹) * (1 + |v|) ^ 2 * Real.exp (-(v ^ 2))
          ≤ 2 * (1 + |v|) ^ 2 * Real.exp (-(v ^ 2)) := by gcongr
        _ ≤ 2 * (1 + |v|) ^ 4 * Real.exp (-(v ^ 2)) := by gcongr
        _ = 2 * ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by ring
    have hKcentral : 6 * C ≤ K := by
      dsimp only [K]
      linarith
    have hcoef : 0 ≤ 3 * C / Y :=
      div_nonneg (mul_nonneg (by norm_num) hC) hY.le
    unfold smoothAFEZetaDualWeightHeightDerivativeIntegrand
    rw [norm_mul]
    calc
      ‖smoothAFEZetaChiShiftHeightDerivative tau v‖ *
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
        ≤ (‖smoothAFEZetaChiShiftRatio (linePt tau)
              (-(↑(1 : ℝ) + ↑v * I))‖ *
              (C * (1 + |v|) / tau)) *
            ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by
          dsimp only [C]
          gcongr
      _ ≤ (((1 + tau) * (1 + |v|)) *
              (C * (1 + |v|) / tau)) *
            ((Y⁻¹ * 3) * Real.exp (-(v ^ 2))) := by
          rw [habstau] at hratio
          gcongr
      _ = (3 * C / Y) * (((1 + tau) * tau⁻¹) *
              (1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by ring
      _ ≤ (6 * C / Y) *
            ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
          rw [show 6 * C / Y = (3 * C / Y) * 2 by ring]
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner hcoef
      _ ≤ (K / Y) *
            ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
          gcongr
  · have htail : tau < 2 * |v| := lt_of_not_ge hv
    have hheight : (1 + tau) ^ 2 ≤ 4 * (1 + |v|) ^ 2 := by
      nlinarith [abs_nonneg v, sq_nonneg (1 + tau), sq_nonneg (1 + |v|)]
    have hder := hglobal tau v
    rw [(hasDerivAt_chiShift_eq_heightDerivative tau v).deriv] at hder
    have hpref : D * (1 + tau) ^ 2 ≤ 4 * D * (1 + |v|) ^ 2 := by
      nlinarith [hD, hheight]
    have hKtail : 12 * D ≤ K := by
      dsimp only [K]
      linarith
    unfold smoothAFEZetaDualWeightHeightDerivativeIntegrand
    rw [norm_mul]
    calc
      ‖smoothAFEZetaChiShiftHeightDerivative tau v‖ *
          ‖smoothAFEMellinIntegrand Y (↑(1 : ℝ) + ↑v * I)‖
        ≤ (D * (1 + tau) ^ 2 * (1 + |v|) ^ 2) *
            ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ 2))) := by
          rw [habstau] at hder
          gcongr
      _ ≤ (D * (1 + tau) ^ 2 * (1 + |v|) ^ 2) *
            ((Y⁻¹ * 3) * Real.exp (-(v ^ 2))) := by gcongr
      _ = (3 * (D * (1 + tau) ^ 2) / Y) *
            ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by ring
      _ ≤ (12 * D / Y) *
            ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
          calc
            (3 * (D * (1 + tau) ^ 2) / Y) *
                ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2)))
              ≤ (3 * (4 * D * (1 + |v|) ^ 2) / Y) *
                ((1 + |v|) ^ 2 * Real.exp (-(v ^ 2))) := by gcongr
            _ = (12 * D / Y) *
                ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by ring
      _ ≤ (K / Y) *
            ((1 + |v|) ^ 4 * Real.exp (-(v ^ 2))) := by
          gcongr

/-- The exact dual-weight height derivative is controlled by reciprocal smoothing scale,
uniformly at every height at least four. -/
theorem exists_norm_deriv_smoothAFEZetaDualWeight_le_invScale :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {tau Y : ℝ}, 4 ≤ tau → 0 < Y →
      ‖deriv (fun u : ℝ => smoothAFEZetaDualWeight u Y) tau‖ ≤ A / Y := by
  obtain ⟨K, hK, hpoint⟩ :=
    exists_norm_dualHeightDerivativeIntegrand_le_invScale_gaussianQuartic
  let q : ℝ → ℝ := fun v => (1 + |v|) ^ 4 * Real.exp (-(v ^ 2))
  let M : ℝ := ∫ v : ℝ, q v
  let a : ℝ := 1 / (2 * Real.pi)
  let A : ℝ := a * K * M
  have hq : Integrable q :=
    integrable_one_add_abs_pow_four_mul_exp_neg_sq
  have hq0 : ∀ v, 0 ≤ q v := fun v => by
    dsimp only [q]
    positivity
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact integral_nonneg hq0
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  refine ⟨A, by dsimp only [A]; positivity, ?_⟩
  intro tau Y htau hY
  have hboundInt : Integrable (fun v : ℝ => (K / Y) * q v) :=
    hq.const_mul (K / Y)
  have hint :
      ‖∫ v : ℝ,
          smoothAFEZetaDualWeightHeightDerivativeIntegrand tau Y v‖ ≤
        ∫ v : ℝ, (K / Y) * q v := by
    apply norm_integral_le_of_norm_le hboundInt
    exact Filter.Eventually.of_forall fun v => hpoint htau hY v
  rw [(hasDerivAt_smoothAFEZetaDualWeight hY tau).deriv]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  calc
    a * ‖∫ v : ℝ,
          smoothAFEZetaDualWeightHeightDerivativeIntegrand tau Y v‖
      ≤ a * ∫ v : ℝ, (K / Y) * q v := by gcongr
    _ = a * ((K / Y) * M) := by
      rw [integral_const_mul]
    _ = A / Y := by
      dsimp only [A]
      ring

/-- Above height four, the exact dual weight is globally Lipschitz in height with
constant proportional to reciprocal smoothing scale.  This is stronger than a
dyadic freezing statement and removes height from the carrier-variation cost. -/
theorem exists_norm_smoothAFEZetaDualWeight_sub_le_invScale_mul_height :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Y tau u : ℝ}, 0 < Y → 4 ≤ tau → 4 ≤ u →
      ‖smoothAFEZetaDualWeight tau Y - smoothAFEZetaDualWeight u Y‖ ≤
        (A / Y) * |tau - u| := by
  obtain ⟨A, hA, hderiv⟩ := exists_norm_deriv_smoothAFEZetaDualWeight_le_invScale
  refine ⟨A, hA, ?_⟩
  intro Y tau u hY htau hu
  let f : ℝ → ℂ := fun y => smoothAFEZetaDualWeight y Y
  let C : ℝ := A / Y
  have hdiff : ∀ y ∈ Set.Ici (4 : ℝ), DifferentiableAt ℝ f y := by
    intro y hy
    exact (hasDerivAt_smoothAFEZetaDualWeight hY y).differentiableAt
  have hbound : ∀ y ∈ Set.Ici (4 : ℝ), ‖deriv f y‖ ≤ C := by
    intro y hy
    exact hderiv hy hY
  have hmvt := (convex_Ici (4 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (show u ∈ Set.Ici (4 : ℝ) from hu)
      (show tau ∈ Set.Ici (4 : ℝ) from htau)
  dsimp only [f, C] at hmvt ⊢
  simpa [Real.norm_eq_abs] using hmvt

/-- Conductor-diagonal specialization of reciprocal-scale height variation. -/
theorem exists_norm_deriv_smoothAFEZetaDualWeight_diagonal_le_inv :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {tau : ℝ}, 4 ≤ tau →
      ‖deriv (fun u : ℝ => smoothAFEZetaDualWeight u tau) tau‖ ≤ A / tau := by
  obtain ⟨A, hA, hbound⟩ := exists_norm_deriv_smoothAFEZetaDualWeight_le_invScale
  exact ⟨A, hA, fun htau => hbound htau (by linarith)⟩

end RHTower
