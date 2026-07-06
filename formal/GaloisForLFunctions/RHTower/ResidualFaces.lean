/-
The residual-face Riemann Hypothesis gate: every analytic estimate of the sign face is a
theorem, and the per-zero certificate is reduced to its irreducible data.

The closed-form calculus supplies, internally: the envelope sup and its reflection
(`archEnvelopeLineBudget`), the derivative-envelope segment budget
(`archDerivSegmentBudget`), the resonance moment (`resonanceMomentClosedFormBudget`), the
completed-carrier line sup (`completedGNLineSupBudget`), the first-moment budget
(`completedGNFirstMomentBudget`), the carrier line slope (`carrierSlopeLineBudget`), the
anchor-generated short-interval mass floor, and the sign bracket.  What remains of the
per-zero certificate — beyond the window geometry — is exactly:
an anchor height where the carrier clears a floor; one scalar comparison between two
explicit formulas; the Jensen sphere data with its quotient and engine inequalities; an
archimedean envelope floor; a completed-carrier sphere sup; the outer cross/EM scalar
budget; and Euler–Maclaurin closeness on window spheres.
-/
import GaloisForLFunctions.RHTower.CarrierMassFloor

open Complex Metric MeasureTheory

namespace RHTower

/-- The winding-floor expression is monotone in the height. -/
theorem winding_floor_expr_mono {α α' : ℝ} (h0 : 0 < α) (hαα' : α ≤ α') :
    (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2 ≤
      (Real.log (α' / (2 * Real.pi)) - (4 / α' ^ 2 + Real.pi / α')) / 2 := by
  have h0' : 0 < α' := lt_of_lt_of_le h0 hαα'
  have hlog : Real.log (α / (2 * Real.pi)) ≤ Real.log (α' / (2 * Real.pi)) :=
    Real.log_le_log (by positivity)
      (div_le_div₀ h0'.le hαα' (by positivity) le_rfl)
  have h4 : 4 / α' ^ 2 ≤ 4 / α ^ 2 :=
    div_le_div₀ (by norm_num) le_rfl (by positivity) (by nlinarith)
  have hπ : Real.pi / α' ≤ Real.pi / α :=
    div_le_div₀ Real.pi_pos.le le_rfl h0 hαα'
  linarith

/-- The closed-form envelope line budget is positive. -/
theorem archEnvelopeLineBudget_pos (B : ℝ) : 0 < archEnvelopeLineBudget B := by
  dsimp [archEnvelopeLineBudget]
  exact mul_pos (by positivity)
    (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
      (Real.Gamma_pos_of_pos (by norm_num)))

/-- The carrier line-slope budget is positive as soon as the depth is at least two and the
envelope budget is positive. -/
theorem carrierSlopeLineBudget_pos {N : ℕ} (hN : 2 ≤ N) {M₀ M₁ : ℝ}
    (hM₀ : 0 < M₀) (hM₁ : 0 ≤ M₁) :
    0 < carrierSlopeLineBudget N M₀ M₁ := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hlogN : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  dsimp [carrierSlopeLineBudget]
  have hfac : 0 < M₁ + M₀ * Real.log N := by nlinarith
  nlinarith

/-- **The residual-face Riemann Hypothesis gate.**  Every analytic estimate of the sign face
is supplied internally by closed-form theorems — envelope sup and reflection, derivative
segment budget, resonance moment, line sup, line slope, the anchor-generated mass floor, and
the sign bracket.  The per-zero certificate retains, beyond the window geometry and
positivity scalars, exactly seven faces:
(R1) an anchor height in the window where the carrier clears the floor `m_J`;
(R2) one scalar inequality between explicit formulas — closed line sup times closed
first-moment budget below the anchor-generated mass floor;
(R3) the Jensen data — carrier sphere sup `M_J`, quotient bound, engine inequality;
(R4) an archimedean envelope floor `a₀` on the expanded window;
(R5) a completed-carrier sphere sup `M_G`;
(R6) the outer cross/EM scalar budget;
(R7) Euler–Maclaurin closeness of the finite carrier on window spheres. -/
theorem riemannHypothesis_of_residual_faces
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (δ : ℝ)
        (T U rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ),
        2 ≤ N ∧
        1 ≤ M ∧
        0 < U ∧
        0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        0 < T - rz ∧
        0 < (Real.log ((T - rz) / (2 * Real.pi)) -
          (4 / (T - rz) ^ 2 + Real.pi / (T - rz))) / 2 ∧
        0 < m_J ∧
        (∃ τ ∈ Set.Icc T (T + U), m_J ≤ ‖gN N (linePt τ)‖) ∧
        (∀ τ ∈ Set.Icc T (T + U),
          completedGNLineSupBudget N (τ + rz) *
              completedGNFirstMomentBudget N (2 * rz)
                (archEnvelopeLineBudget (τ + rz))
                (archDerivSegmentBudget (τ - rz) (τ + rz))
                (resonanceMomentClosedFormBudget (τ - rz) (τ + rz)) <
            (a₀ * m_J / 2) ^ 2 * (2 * min rz (a₀ * m_J /
              (2 * carrierSlopeLineBudget N (archEnvelopeLineBudget (T + U + rz))
                (archDerivSegmentBudget (T - rz) (T + U + rz)))))) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (((max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
              (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)) + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_center_floor_cross_slope_windows
  intro ρ hρ hzero
  obtain ⟨N, M, δ, T, U, rz, r₀, R, P, rJ, RJ, m_J, M_J, M_G, a₀,
    hN2, hM, hU, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad,
    hTrz, hwindT, hmJ0, hanchorEx, hscalar, hMJ, hbound, hjensen_floor, hengine,
    ha₀, ha₀0, hMG, hbudget_outer, hclose⟩ := hwin ρ hρ hzero
  let ε₁ : ℝ := (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
    (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ)
  let Rprime : ℝ := R - rz
  let Rτ : ℝ := max |ρ.im - T| |ρ.im - (T + U)|
  have hR'0 : 0 < Rprime := by
    dsimp [Rprime]
    linarith
  have hR'rz : Rprime + rz ≤ R := by
    dsimp [Rprime]
    linarith
  have hρT : |ρ.im - T| ≤ Rτ := le_max_left _ _
  have hρTU : |ρ.im - (T + U)| ≤ Rτ := le_max_right _ _
  have hρquad' : (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < Rprime ^ 2 := by
    simpa [Rτ, Rprime] using hρquad
  have hR0 : 0 ≤ R := (lt_trans h0 hrR).le
  have hP0 : 0 < P := lt_of_lt_of_le (lt_trans h0 hrR) hRP
  have hMJ0 : 0 < M_J := lt_of_lt_of_le zero_lt_one hMJ
  have hrzJ : rz < rJ := by linarith
  have hRJ0 : 0 < RJ := by linarith [h0, hrR, hRrzJ, hrJR, hrz0]
  have hε₁0 : 0 ≤ ε₁ := by
    have hden0 : 0 < 1 / 2 - RJ := by linarith
    have hpow_nonneg : 0 ≤ (M : ℝ) ^ (-(1 / 2 - RJ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    have hmax_nonneg : 0 ≤ max ‖linePt T‖ ‖linePt (T + U)‖ :=
      le_trans (norm_nonneg (linePt T)) (le_max_left _ _)
    have hlhs_nonneg : 0 ≤ (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
        (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ) := by
      exact div_nonneg (mul_nonneg (add_nonneg hmax_nonneg hRJ0.le) hpow_nonneg) hden0.le
    simpa [ε₁] using hlhs_nonneg
  have hδ0 : 0 ≤ δ := by
    have hτT : T ∈ Set.Icc T (T + U) := ⟨le_rfl, by linarith [hU]⟩
    have hsample : linePt T + (RJ : ℂ) ∈
        sphere (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) RJ := by
      simpa [linePt] using linePt_add_radius_mem_sphere (τ := T) hRJ0.le
    exact le_trans (norm_nonneg (emCarrier M (linePt T + (RJ : ℂ)) -
      gN N (linePt T + (RJ : ℂ)))) (hclose T hτT (linePt T + (RJ : ℂ)) hsample)
  have hεδ : 0 ≤ ε₁ + δ := add_nonneg hε₁0 hδ0
  obtain ⟨τ, hτ, hAnchorLine⟩ := hanchorEx
  have hAnchor : m_J ≤ ‖gN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
    simpa [linePt] using hAnchorLine
  have hwinsub : Set.Icc (τ - rz) (τ + rz) ⊆ Set.Icc (T - rz) (T + U + rz) :=
    Set.Icc_subset_Icc (by linarith [hτ.1]) (by linarith [hτ.2])
  have hτexp : τ ∈ Set.Icc (T - rz) (T + U + rz) :=
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hanchorRe : a₀ * m_J ≤ |(completedGN N (linePt τ)).re| :=
    anchor_re_completedGN_line_of_floors N hmJ0.le (ha₀ τ hτexp) hAnchorLine
  have hcpos : 0 < a₀ * m_J := mul_pos ha₀0 hmJ0
  have hD : 0 < carrierSlopeLineBudget N (archEnvelopeLineBudget (T + U + rz))
      (archDerivSegmentBudget (T - rz) (T + U + rz)) :=
    carrierSlopeLineBudget_pos hN2 (archEnvelopeLineBudget_pos _)
      (archDerivSegmentBudget_nonneg hTrz (by linarith))
  have hτrz0 : 0 < τ - rz := by linarith [hτ.1]
  have hwindτ : 0 < (Real.log ((τ - rz) / (2 * Real.pi)) -
      (4 / (τ - rz) ^ 2 + Real.pi / (τ - rz))) / 2 :=
    lt_of_lt_of_le hwindT
      (winding_floor_expr_mono hTrz (by linarith [hτ.1]))
  have hfirst := abs_integral_re_completedGN_line_le_closedFirstMomentBudget_mono
    N (by omega) hτrz0 (by linarith : τ - rz ≤ τ + rz) hwindτ
    (by linarith : (τ + rz) - (τ - rz) ≤ 2 * rz) le_rfl le_rfl le_rfl
  have hfm : completedGNLineSupBudget N (τ + rz) *
      |∫ u in (τ - rz)..(τ + rz), (completedGN N (linePt u)).re| <
      (a₀ * m_J / 2) ^ 2 * (2 * min rz (a₀ * m_J /
        (2 * carrierSlopeLineBudget N (archEnvelopeLineBudget (T + U + rz))
          (archDerivSegmentBudget (T - rz) (T + U + rz))))) :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hfirst (completedGNLineSupBudget_nonneg N _))
      (hscalar τ hτ)
  obtain ⟨t₁, t₂, ht₁, ht₂, h12, hsign⟩ :=
    exists_completedGN_sign_bracket_of_anchor_slope N hrz0 hcpos hD
      (fun u hu => norm_archFactor_line_le_segment_budget hTrz.le (hwinsub hu))
      (fun u hu => norm_archFactor_reflected_line_le_segment_budget hTrz.le (hwinsub hu))
      (fun u hu => norm_archFactorDeriv_line_le_segmentBudget hTrz (hwinsub hu))
      (fun u hu => by
        rw [norm_archFactorDeriv_reflected_line_eq u]
        exact norm_archFactorDeriv_line_le_segmentBudget hTrz (hwinsub hu))
      hanchorRe
      (fun u hu => abs_re_completedGN_line_le_segment_budget N hτrz0.le hu)
      hfm
  have ht₁0 : 0 < t₁ := by linarith [ht₁.1, hτ.1]
  have hMG_ball := completedGN_norm_le_line_closedBall_of_sphere hRJ0 hRJ12 (hMG τ hτ)
  have hE_ball : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁ := by
    intro z hz
    exact em_remainder_norm_le_window_closedBall_of_endpoint_bound
      (M := M) (T := T) (U := U) (RJ := RJ) (ε₁ := ε₁) hM hRJ12
      (by dsimp [ε₁]; exact le_rfl)
      τ hτ z (by simpa [linePt] using hz)
  have hclose_ball :=
    emCarrier_gN_norm_le_line_closedBall_of_sphere hM hRJ0 hRJ12 (hclose τ hτ)
  have ha₀_ball : ∀ z : ℂ, z.re = 1 / 2 →
      z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz → a₀ ≤ ‖archFactor z‖ := by
    intro z hzre hz
    have him : z.im ∈ Set.Icc (T - rz) (T + U + rz) :=
      im_mem_expanded_window_of_mem_line_center_closedBall hτ hz
    have hzline : z = linePt z.im := eq_linePt_of_re_eq_half hzre
    rw [hzline]
    exact ha₀ z.im him
  obtain ⟨hcross, hfl⟩ :=
    canonical_cross_em_budgets_of_outer_power_floor_max
      (m_J := m_J) (M_J := M_J) (rz := rz) (rJ := rJ) (R := R)
      (P := P) (M_G := M_G) (a₀ := a₀) (r₀ := r₀) (ε₁ := ε₁) (δ := δ)
      hmJ0 hrz0 hMJ0 hrzJ hengine hP0 ha₀0 h0 hR0 hRrzJ (by
        dsimp [ε₁]
        exact hbudget_outer)
  refine ⟨N, M, ε₁, δ, ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I,
    t₁, t₂, rz, r₀, R, Rprime, P, rJ, RJ, m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, ht₁0, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    point_mem_line_center_ball_of_quadratic hR'0
      ((quadratic_target_of_endpoint_abs_im_bounds hρT hρTU hρquad') τ hτ),
    hR'rz, line_center_closedBall_strip hRJ12,
    (fun u hu => line_interval_mem_closedBall_line_center_of_endpoint_bounds
      (T := τ) (U := 0) (by linarith [ht₁.1]) (by linarith [ht₂.2])
      ⟨le_rfl, by linarith⟩ hu),
    (by simpa [linePt] using hsign), hmJ0, hAnchor, hMJ,
    (fun z hz => hbound τ hτ z hz),
    hjensen_floor, hengine, ha₀_ball, ha₀0, hMG_ball, hcross,
    hE_ball, hclose_ball, hfl⟩

end RHTower
