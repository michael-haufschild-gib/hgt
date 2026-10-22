import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFixedActionC5ExactFirstAtomTailReduction

open Set

namespace RHTower

noncomputable section

/-- Physical same-half-line strength envelope for the rational reflection correction. -/
theorem thetaCuspSingleAtomReflectionStrength_lt_physicalEnvelope
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    thetaCuspSingleAtomReflectionLambda
          (thetaCuspSingleAtomReflectionScale 1 u) *
        thetaCuspSingleAtomReflectionDefect t <
      (thetaCuspSingleAtomReflectionScale 1 u - 3) ^ (2 : ℕ) /
        (2 * (thetaCuspSingleAtomReflectionScale 1 u - 3 / 2) ^ (2 : ℕ)) := by
  let Y := Real.exp (2 * u)
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let Z := (Y - 1) ^ (2 : ℕ) / (2 * Y)
  have hu : 0 ≤ u := le_trans ht htu
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hYone : 1 ≤ Y := by
    dsimp only [Y]
    exact Real.one_le_exp (by linarith)
  have hcosh : Real.cosh (2 * t) ≤ Real.cosh (2 * u) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 * t),
      abs_of_nonneg (by linarith : 0 ≤ 2 * u)]
    linarith
  have hcoshZ : Real.cosh (2 * u) - 1 = Z := by
    dsimp only [Z, Y]
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp [hY.ne']
    ring
  have hzle : z ≤ Z := by
    dsimp only [z, thetaCuspSingleAtomReflectionDefect]
    rw [← hcoshZ]
    linarith
  have hAeq : A = Real.pi * Y := by
    dsimp only [A, Y, thetaCuspSingleAtomReflectionScale]
    norm_num
  have hAthree : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale
        (n := 1) (by norm_num) hu
  have hden : 0 < (A - 3 / 2) ^ (2 : ℕ) :=
    sq_pos_of_pos (by linarith)
  have hAZ : 3 * A * Z = 3 * Real.pi * (Y - 1) ^ (2 : ℕ) / 2 := by
    rw [hAeq]
    dsimp only [Z]
    field_simp [hY.ne']
  have hgap : 3 * Real.pi * (Y - 1) ^ (2 : ℕ) < (A - 3) ^ (2 : ℕ) := by
    have hpiGap : 0 < Real.pi - 3 := sub_pos.mpr Real.pi_gt_three
    have hYsq : 1 ≤ Y ^ (2 : ℕ) := by nlinarith [sq_nonneg (Y - 1)]
    have hsecond : 0 < Real.pi * Y ^ (2 : ℕ) - 3 := by
      nlinarith [Real.pi_gt_three]
    have hid :
        (A - 3) ^ (2 : ℕ) - 3 * Real.pi * (Y - 1) ^ (2 : ℕ) =
          (Real.pi - 3) * (Real.pi * Y ^ (2 : ℕ) - 3) := by
      rw [hAeq]
      ring
    have hprod : 0 < (Real.pi - 3) * (Real.pi * Y ^ (2 : ℕ) - 3) :=
      mul_pos hpiGap hsecond
    rw [← hid] at hprod
    linarith
  have hnum : 3 * A * z < (A - 3) ^ (2 : ℕ) / 2 := by
    have hle : 3 * A * z ≤ 3 * A * Z := by
      exact mul_le_mul_of_nonneg_left hzle (by positivity)
    rw [hAZ] at hle
    nlinarith
  unfold thetaCuspSingleAtomReflectionLambda
  calc
    3 * thetaCuspSingleAtomReflectionScale 1 u /
          (thetaCuspSingleAtomReflectionScale 1 u - 3 / 2) ^ (2 : ℕ) *
        thetaCuspSingleAtomReflectionDefect t =
      (3 * thetaCuspSingleAtomReflectionScale 1 u *
        thetaCuspSingleAtomReflectionDefect t) /
          (thetaCuspSingleAtomReflectionScale 1 u - 3 / 2) ^ (2 : ℕ) := by ring
    _ < ((thetaCuspSingleAtomReflectionScale 1 u - 3) ^ (2 : ℕ) / 2) /
          (thetaCuspSingleAtomReflectionScale 1 u - 3 / 2) ^ (2 : ℕ) :=
      div_lt_div_of_pos_right hnum hden
    _ = (thetaCuspSingleAtomReflectionScale 1 u - 3) ^ (2 : ℕ) /
        (2 * (thetaCuspSingleAtomReflectionScale 1 u - 3 / 2) ^ (2 : ℕ)) := by
      rw [div_div]

/-- Möbius-coordinate form of the physical reflection-strength envelope. -/
theorem thetaCuspSingleAtomReflectionOdds_lt_physicalEnvelope
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    thetaCuspSingleAtomReflectionLambda
          (thetaCuspSingleAtomReflectionScale 1 u) /
        thetaCuspSingleAtomReflectionFactor
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t) *
        thetaCuspSingleAtomReflectionDefect t <
      (thetaCuspSingleAtomReflectionScale 1 u - 3) ^ (2 : ℕ) /
        (thetaCuspSingleAtomReflectionScale 1 u ^ (2 : ℕ) - 9 / 2) := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let eta := l * z
  let E := (A - 3) ^ (2 : ℕ) / (2 * (A - 3 / 2) ^ (2 : ℕ))
  have hu : 0 ≤ u := le_trans ht htu
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale
        (n := 1) (by norm_num) hu
  have hetaE : eta < E := by
    simpa only [eta, E, A, z, l] using
      thetaCuspSingleAtomReflectionStrength_lt_physicalEnvelope ht htu
  have hEhalf : E < 1 / 2 := by
    have hden : 0 < 2 * (A - 3 / 2) ^ (2 : ℕ) := by
      exact mul_pos (by norm_num) (sq_pos_of_pos (by linarith))
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos (sub_pos.mpr hA) (by linarith : 0 < 3 * A - 9 / 2)]
  have hetaHalf : eta < 1 / 2 := lt_trans hetaE hEhalf
  have hr : 0 < 1 - eta := by linarith
  have hEr : 0 < 1 - E := by linarith
  have hfrac : eta / (1 - eta) < E / (1 - E) := by
    rw [div_lt_div_iff₀ hr hEr]
    nlinarith
  have hA0 : 0 < A := lt_trans (by norm_num) hA
  have hdenA : 0 < A ^ (2 : ℕ) - 9 / 2 := by
    nlinarith [mul_pos hA0 hA0]
  have hEeq : E / (1 - E) = (A - 3) ^ (2 : ℕ) / (A ^ (2 : ℕ) - 9 / 2) := by
    have hratio (N D : ℝ) (hD : D ≠ 0) (hDN : D - N ≠ 0) :
        (N / D) / (1 - N / D) = N / (D - N) := by
      field_simp [hD, hDN]
    have hD : 2 * (A - 3 / 2) ^ (2 : ℕ) ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (by linarith))
    have hdiff :
        2 * (A - 3 / 2) ^ (2 : ℕ) - (A - 3) ^ (2 : ℕ) = A ^ (2 : ℕ) - 9 / 2 := by ring
    have hDN : 2 * (A - 3 / 2) ^ (2 : ℕ) - (A - 3) ^ (2 : ℕ) ≠ 0 := by
      rw [hdiff]
      exact hdenA.ne'
    dsimp only [E]
    rw [hratio _ _ hD hDN, hdiff]
  dsimp only [eta, l, z] at hfrac
  rw [hEeq] at hfrac
  unfold thetaCuspSingleAtomReflectionFactor
  rw [show thetaCuspSingleAtomReflectionLambda
      (thetaCuspSingleAtomReflectionScale 1 u) /
        (1 - thetaCuspSingleAtomReflectionLambda
          (thetaCuspSingleAtomReflectionScale 1 u) *
            thetaCuspSingleAtomReflectionDefect t) *
        thetaCuspSingleAtomReflectionDefect t =
      (thetaCuspSingleAtomReflectionLambda
        (thetaCuspSingleAtomReflectionScale 1 u) *
          thetaCuspSingleAtomReflectionDefect t) /
        (1 - thetaCuspSingleAtomReflectionLambda
          (thetaCuspSingleAtomReflectionScale 1 u) *
            thetaCuspSingleAtomReflectionDefect t) by ring]
  exact hfrac

/-- Physical envelope for the rational slope correction itself. -/
theorem thetaCuspSingleAtomReflectionSlopeCorrection_lt_physicalEnvelope
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    thetaCuspSingleAtomReflectionLambda
          (thetaCuspSingleAtomReflectionScale 1 u) /
        thetaCuspSingleAtomReflectionFactor
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t) <
      6 * thetaCuspSingleAtomReflectionScale 1 u /
        (thetaCuspSingleAtomReflectionScale 1 u ^ (2 : ℕ) - 9 / 2) := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let eta := l * z
  let E := (A - 3) ^ (2 : ℕ) / (2 * (A - 3 / 2) ^ (2 : ℕ))
  have hu : 0 ≤ u := le_trans ht htu
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale
        (n := 1) (by norm_num) hu
  have hl : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos hA
  have hetaE : eta < E := by
    simpa only [eta, E, A, z, l] using
      thetaCuspSingleAtomReflectionStrength_lt_physicalEnvelope ht htu
  have hEhalf : E < 1 / 2 := by
    have hden : 0 < 2 * (A - 3 / 2) ^ (2 : ℕ) :=
      mul_pos (by norm_num) (sq_pos_of_pos (by linarith))
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos (sub_pos.mpr hA) (by linarith : 0 < 3 * A - 9 / 2)]
  have hr : 0 < 1 - eta := by linarith
  have hEr : 0 < 1 - E := by linarith
  have hfrac : l / (1 - eta) < l / (1 - E) :=
    div_lt_div_of_pos_left hl hEr (by linarith)
  have hA0 : 0 < A := lt_trans (by norm_num) hA
  have hdenA : 0 < A ^ (2 : ℕ) - 9 / 2 := by
    nlinarith [mul_pos hA0 hA0]
  have hidentity : l / (1 - E) = 6 * A / (A ^ (2 : ℕ) - 9 / 2) := by
    let D := 2 * (A - 3 / 2) ^ (2 : ℕ)
    let N := (A - 3) ^ (2 : ℕ)
    have hD : D ≠ 0 := by
      dsimp only [D]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (by linarith))
    have hdiff : D - N = A ^ (2 : ℕ) - 9 / 2 := by
      dsimp only [D, N]
      ring
    have hDN : D - N ≠ 0 := by rw [hdiff]; exact hdenA.ne'
    have hratio (C : ℝ) :
        (C / D) / (1 - N / D) = C / (D - N) := by
      field_simp [hD, hDN]
    have hlform : l = 6 * A / D := by
      dsimp only [l]
      unfold thetaCuspSingleAtomReflectionLambda
      apply (div_eq_div_iff (pow_ne_zero 2 (by linarith)) hD).2
      dsimp only [D]
      ring
    have hEform : E = N / D := by
      dsimp only [E, N, D]
    rw [hlform, hEform, hratio, hdiff]
  rw [hidentity] at hfrac
  dsimp only [eta, l, z] at hfrac
  unfold thetaCuspSingleAtomReflectionFactor
  simpa only [A] using hfrac

private theorem c5PhysicalEnvelopeScaleSlope_pos
    {A : ℝ} (hA : 6 ≤ A) :
    0 < 4 * A -
      (2 * (A + 3 / 2) / (A - 3 / 2)) *
        (6 * A / (A ^ (2 : ℕ) - 9 / 2)) := by
  let D := A ^ (2 : ℕ) - 9 / 2
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hB : 0 < A - 3 / 2 := by linarith
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith [mul_pos hA0 hA0]
  have hpoly : 3 * (A + 3 / 2) < (A - 3 / 2) * D := by
    let b := A - 6
    have hb : 0 ≤ b := by dsimp only [b]; linarith
    have hAeq : A = b + 6 := by dsimp only [b]; ring
    dsimp only [D]
    rw [hAeq]
    ring_nf
    nlinarith [pow_nonneg hb 2, pow_nonneg hb 3]
  have hfrac :
      (2 * (A + 3 / 2) / (A - 3 / 2)) * (6 * A / D) < 4 * A := by
    rw [show (2 * (A + 3 / 2) / (A - 3 / 2)) * (6 * A / D) =
        12 * A * (A + 3 / 2) / ((A - 3 / 2) * D) by
      field_simp [hB.ne', hD.ne']
      ring]
    rw [div_lt_iff₀ (mul_pos hB hD)]
    have hscaled := mul_lt_mul_of_pos_left hpoly
      (mul_pos (by norm_num : (0 : ℝ) < 4) hA0)
    nlinarith
  dsimp only [D] at hfrac
  linarith

private theorem c5PhysicalEnvelopeHighestReserveLossRatio_lt_one
    {A : ℝ} (hA : 6 ≤ A) :
    let D := A ^ (2 : ℕ) - 9 / 2
    let X := 6 * A / D
    let W := (A - 3) ^ (2 : ℕ) / D
    let R := 2 * (A + 3 / 2) / (A - 3 / 2)
    let L₀ := 4 * A - R * X
    R * W * (W + X) / L₀ +
        2 * R * W * (1 + W) * (W + 2 * X) / L₀ +
        3 * W * (W + X) / (2 * A) +
        2 * W ^ (2 : ℕ) * (W + 2 * X) / (2 * A) < 1 := by
  dsimp only
  let D := A ^ (2 : ℕ) - 9 / 2
  let N := (A - 3) ^ (2 : ℕ)
  let X := 6 * A / D
  let W := N / D
  let R := 2 * (A + 3 / 2) / (A - 3 / 2)
  let L₀ := 4 * A - R * X
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hB : 0 < A - 3 / 2 := by linarith
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith [mul_pos hA0 hA0]
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hpolyL : 3 * (A + 3 / 2) < (A - 3 / 2) * D := by
    let b := A - 6
    have hb : 0 ≤ b := by dsimp only [b]; linarith
    have hAeq : A = b + 6 := by dsimp only [b]; ring
    dsimp only [D]
    rw [hAeq]
    ring_nf
    nlinarith [pow_nonneg hb 2, pow_nonneg hb 3]
  have hRX : R * X =
      12 * A * (A + 3 / 2) / ((A - 3 / 2) * D) := by
    dsimp only [R, X]
    field_simp [hB.ne', hD.ne']
    ring
  have hL₀ : 0 < L₀ := by
    have hscaled :
        12 * A * (A + 3 / 2) < 4 * A * ((A - 3 / 2) * D) := by
      have hraw := mul_lt_mul_of_pos_left hpolyL
        (mul_pos (by norm_num : (0 : ℝ) < 4) hA0)
      nlinarith
    have hfrac : R * X < 4 * A := by
      rw [hRX, div_lt_iff₀ (mul_pos hB hD)]
      nlinarith
    dsimp only [L₀]
    linarith
  have hcore₁ :
      2 * (A + 3 / 2) * (8 * N * (N + 6 * A) + 6 * A * D) <
        4 * A * (A - 3 / 2) * D ^ (2 : ℕ) := by
    let b := A - 6
    have hb : 0 ≤ b := by dsimp only [b]; linarith
    have hAeq : A = b + 6 := by dsimp only [b]; ring
    dsimp only [N, D]
    rw [hAeq]
    ring_nf
    nlinarith [pow_nonneg hb 2, pow_nonneg hb 3, pow_nonneg hb 4,
      pow_nonneg hb 5, pow_nonneg hb 6]
  have hterm₁ : R * W * (W + X) / L₀ < 1 / 8 := by
    have hcombined : R * (8 * W * (W + X) + X) < 4 * A := by
      rw [show R * (8 * W * (W + X) + X) =
          (2 * (A + 3 / 2) * (8 * N * (N + 6 * A) + 6 * A * D)) /
            ((A - 3 / 2) * D ^ (2 : ℕ)) by
        dsimp only [R, W, X]
        field_simp [hB.ne', hD.ne']
        ]
      rw [div_lt_iff₀ (mul_pos hB (sq_pos_of_pos hD))]
      simpa only [mul_assoc] using hcore₁
    rw [div_lt_iff₀ hL₀]
    dsimp only [L₀] at hcombined ⊢
    nlinarith
  have hcore₂ :
      12 * (A + 3 / 2) *
          (N * (D + N) * (N + 12 * A) + A * D ^ (2 : ℕ)) <
        4 * A * (A - 3 / 2) * D ^ (3 : ℕ) := by
    let b := A - 6
    have hb : 0 ≤ b := by dsimp only [b]; linarith
    have hAeq : A = b + 6 := by dsimp only [b]; ring
    dsimp only [N, D]
    rw [hAeq]
    ring_nf
    nlinarith [pow_nonneg hb 2, pow_nonneg hb 3, pow_nonneg hb 4,
      pow_nonneg hb 5, pow_nonneg hb 6, pow_nonneg hb 7,
      pow_nonneg hb 8]
  have hterm₂ :
      2 * R * W * (1 + W) * (W + 2 * X) / L₀ < 1 / 3 := by
    have hcombined :
        6 * R * W * (1 + W) * (W + 2 * X) + R * X < 4 * A := by
      rw [show 6 * R * W * (1 + W) * (W + 2 * X) + R * X =
          (12 * (A + 3 / 2) *
            (N * (D + N) * (N + 12 * A) + A * D ^ (2 : ℕ))) /
              ((A - 3 / 2) * D ^ (3 : ℕ)) by
        dsimp only [R, W, X]
        field_simp [hB.ne', hD.ne']
        ring]
      rw [div_lt_iff₀ (mul_pos hB (pow_pos hD 3))]
      simpa only [mul_assoc] using hcore₂
    rw [div_lt_iff₀ hL₀]
    dsimp only [L₀] at hcombined ⊢
    nlinarith
  have hcore₃ : 12 * N * (N + 6 * A) < A * D ^ (2 : ℕ) := by
    let b := A - 6
    have hb : 0 ≤ b := by dsimp only [b]; linarith
    have hAeq : A = b + 6 := by dsimp only [b]; ring
    dsimp only [N, D]
    rw [hAeq]
    ring_nf
    nlinarith [pow_nonneg hb 2, pow_nonneg hb 3, pow_nonneg hb 4,
      pow_nonneg hb 5]
  have hterm₃ : 3 * W * (W + X) / (2 * A) < 1 / 8 := by
    rw [show 3 * W * (W + X) / (2 * A) =
        (3 * N * (N + 6 * A)) / (2 * A * D ^ (2 : ℕ)) by
      dsimp only [W, X]
      field_simp [hD.ne']
      ]
    rw [div_lt_iff₀ (mul_pos (mul_pos (by norm_num) hA0) (sq_pos_of_pos hD))]
    nlinarith
  have hcore₄ : 16 * N ^ (2 : ℕ) * (N + 12 * A) < A * D ^ (3 : ℕ) := by
    let b := A - 6
    have hb : 0 ≤ b := by dsimp only [b]; linarith
    have hAeq : A = b + 6 := by dsimp only [b]; ring
    dsimp only [N, D]
    rw [hAeq]
    ring_nf
    nlinarith [pow_nonneg hb 2, pow_nonneg hb 3, pow_nonneg hb 4,
      pow_nonneg hb 5, pow_nonneg hb 6, pow_nonneg hb 7]
  have hterm₄ : 2 * W ^ (2 : ℕ) * (W + 2 * X) / (2 * A) < 1 / 16 := by
    rw [show 2 * W ^ (2 : ℕ) * (W + 2 * X) / (2 * A) =
        N ^ (2 : ℕ) * (N + 12 * A) / (A * D ^ (3 : ℕ)) by
      dsimp only [W, X]
      field_simp [hD.ne']
      ring]
    rw [div_lt_iff₀ (mul_pos hA0 (pow_pos hD 3))]
    nlinarith
  change R * W * (W + X) / L₀ +
      2 * R * W * (1 + W) * (W + 2 * X) / L₀ +
      3 * W * (W + X) / (2 * A) +
      2 * W ^ (2 : ℕ) * (W + 2 * X) / (2 * A) < 1
  nlinarith

private theorem c5PhysicalEnvelopeSlopeDefect_lt_three
    {A : ℝ} (hA : 6 ≤ A) :
    (A - 3) ^ (2 : ℕ) / (A ^ (2 : ℕ) - 9 / 2) +
        2 * (6 * A / (A ^ (2 : ℕ) - 9 / 2)) < 3 := by
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hD : 0 < A ^ (2 : ℕ) - 9 / 2 := by
    nlinarith [mul_pos hA0 hA0]
  rw [show (A - 3) ^ (2 : ℕ) / (A ^ (2 : ℕ) - 9 / 2) +
      2 * (6 * A / (A ^ (2 : ℕ) - 9 / 2)) =
      ((A - 3) ^ (2 : ℕ) + 12 * A) / (A ^ (2 : ℕ) - 9 / 2) by ring]
  rw [div_lt_iff₀ hD]
  have hprod : 0 ≤ (A - 6) * (2 * A + 6) := by positivity
  nlinarith

/-- Scale-free Gaussian base shape underlying exact first-atom compensation. -/
def c5HyperbolicGaussianBaseShape (t : ℝ) : ℝ :=
  let z := thetaCuspSingleAtomReflectionDefect t
  let e := 2 * Real.sinh (2 * t)
  z * ((25 + 72 * z) * e - t * (140 + 328 * z)) + 20 * t ^ (2 : ℕ) * e

theorem c5HyperbolicGaussianBaseShape_pos {t : ℝ} (ht : 0 < t) :
    0 < c5HyperbolicGaussianBaseShape t := by
  have hcert := c5HyperbolicCertificate_pos (show 0 < 2 * t by linarith)
  unfold c5HyperbolicGaussianBaseShape thetaCuspSingleAtomReflectionDefect
  dsimp only
  unfold c5HyperbolicCertificate at hcert
  convert (show 0 < 2 * c5HyperbolicCertificate (2 * t) by positivity) using 1
  dsimp only [c5HyperbolicCertificate]
  ring

/-- Exact factorization of the first-atom velocity centre numerator. -/
theorem c5SingleAtomVelocityCenterNumerator_eq_factor (A t : ℝ) :
    let z := thetaCuspSingleAtomReflectionDefect t
    let e := 2 * Real.sinh (2 * t)
    let l := thetaCuspSingleAtomReflectionLambda A
    let d := c5SingleAtomScaleLambdaJetOne A
    let r := thetaCuspSingleAtomReflectionFactor A z
    let p := 2 * A + l / r
    let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
    let L := 4 * A + d / r
    let M := 4 * A + d / r ^ (2 : ℕ)
    c5SingleAtomVelocityCenterNumerator A t =
      z * (4 * t * p * (z + 2) * M - p * e * L -
        4 * t * (g * z * (z + 2) + p * (z + 1)) * L) := by
  dsimp only
  let z := thetaCuspSingleAtomReflectionDefect t
  let e := 2 * Real.sinh (2 * t)
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
  let L := 4 * A + d / r
  let M := 4 * A + d / r ^ (2 : ℕ)
  have ha : thetaCuspSingleAtomReflectedActionJetOne A z e = p * e := by
    unfold thetaCuspSingleAtomReflectedActionJetOne
      thetaCuspSingleAtomReflectionSlope
    dsimp only [p, l, r]
  have hb : thetaCuspSingleAtomReflectedActionJetTwo A z =
      4 * (g * z * (z + 2) + p * (z + 1)) := by
    unfold thetaCuspSingleAtomReflectedActionJetTwo
      thetaCuspSingleAtomReflectionSlope
    dsimp only [g, p, l, r]
    ring
  have hs : c5SingleAtomScaleActionJetOne A z = z * L := by
    unfold c5SingleAtomScaleActionJetOne
    dsimp only [L, d, r]
    ring
  have hm : c5SingleAtomScaleMixedJetOne A z e = M * e := by
    unfold c5SingleAtomScaleMixedJetOne
    dsimp only [M, d, r]
  have hesq : e ^ (2 : ℕ) = 4 * z * (z + 2) := by
    dsimp only [e, z]
    exact sq_two_mul_sinh_two t
  unfold c5SingleAtomVelocityCenterNumerator
  dsimp only
  rw [ha, hb, hs, hm]
  rw [show p * e * (t * (M * e)) = t * p * M * e ^ (2 : ℕ) by ring, hesq]
  ring

/-- Exact factorization of the first-atom velocity--slope centre numerator. -/
theorem c5SingleAtomVelocitySlopeCenterNumerator_eq_factor (A t : ℝ) :
    let z := thetaCuspSingleAtomReflectionDefect t
    let e := 2 * Real.sinh (2 * t)
    let l := thetaCuspSingleAtomReflectionLambda A
    let d := c5SingleAtomScaleLambdaJetOne A
    let r := thetaCuspSingleAtomReflectionFactor A z
    let p := 2 * A + l / r
    let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
    let k := l ^ (3 : ℕ) / r ^ (3 : ℕ)
    let L := 4 * A + d / r
    let M := 4 * A + d / r ^ (2 : ℕ)
    let B := g * z * (z + 2) + p * (z + 1)
    let C := 8 * k * z * (z + 2) + 12 * g * (z + 1) + 4 * p
    let N := 2 * l * d / r ^ (3 : ℕ) * z * (z + 2) + M * (z + 1)
    c5SingleAtomVelocitySlopeCenterNumerator A t =
      z * (4 * t * p * (z + 2) * M - p * e * L - 12 * t * B * L) +
        t ^ (2 : ℕ) * e * (4 * p * N - z * C * L) := by
  dsimp only
  let z := thetaCuspSingleAtomReflectionDefect t
  let e := 2 * Real.sinh (2 * t)
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
  let k := l ^ (3 : ℕ) / r ^ (3 : ℕ)
  let L := 4 * A + d / r
  let M := 4 * A + d / r ^ (2 : ℕ)
  let B := g * z * (z + 2) + p * (z + 1)
  let C := 8 * k * z * (z + 2) + 12 * g * (z + 1) + 4 * p
  let N := 2 * l * d / r ^ (3 : ℕ) * z * (z + 2) + M * (z + 1)
  have ha : thetaCuspSingleAtomReflectedActionJetOne A z e = p * e := by
    unfold thetaCuspSingleAtomReflectedActionJetOne
      thetaCuspSingleAtomReflectionSlope
    dsimp only [p, l, r]
  have hb : thetaCuspSingleAtomReflectedActionJetTwo A z = 4 * B := by
    unfold thetaCuspSingleAtomReflectedActionJetTwo
      thetaCuspSingleAtomReflectionSlope
    dsimp only [B, g, p, l, r]
    ring
  have hc : thetaCuspSingleAtomReflectedActionJetThree A z e = e * C := by
    unfold thetaCuspSingleAtomReflectedActionJetThree
      thetaCuspSingleAtomReflectionSlope
    dsimp only [C, k, g, p, l, r]
  have hs : c5SingleAtomScaleActionJetOne A z = z * L := by
    unfold c5SingleAtomScaleActionJetOne
    dsimp only [L, d, r]
    ring
  have hm : c5SingleAtomScaleMixedJetOne A z e = M * e := by
    unfold c5SingleAtomScaleMixedJetOne
    dsimp only [M, d, r]
  have hn : c5SingleAtomScaleMixedJetTwo A z = 4 * N := by
    unfold c5SingleAtomScaleMixedJetTwo
    dsimp only [N, M, l, d, r]
  have hesq : e ^ (2 : ℕ) = 4 * z * (z + 2) := by
    dsimp only [e, z]
    exact sq_two_mul_sinh_two t
  unfold c5SingleAtomVelocitySlopeCenterNumerator
  dsimp only
  rw [ha, hb, hc, hs, hm, hn]
  rw [show p * e * (t * (M * e) + t ^ (2 : ℕ) * (4 * N)) =
      t * p * M * e ^ (2 : ℕ) + 4 * t ^ (2 : ℕ) * p * e * N by ring, hesq]
  ring

/-- Exact rational-hyperbolic normal form of the base compensation margin. -/
theorem c5SingleAtomBaseCompensationMargin_eq_factor (A t : ℝ) :
    let z := thetaCuspSingleAtomReflectionDefect t
    let e := 2 * Real.sinh (2 * t)
    let l := thetaCuspSingleAtomReflectionLambda A
    let d := c5SingleAtomScaleLambdaJetOne A
    let r := thetaCuspSingleAtomReflectionFactor A z
    let p := 2 * A + l / r
    let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
    let k := l ^ (3 : ℕ) / r ^ (3 : ℕ)
    let L := 4 * A + d / r
    let M := 4 * A + d / r ^ (2 : ℕ)
    let B := g * z * (z + 2) + p * (z + 1)
    let C := 8 * k * z * (z + 2) + 12 * g * (z + 1) + 4 * p
    let N := 2 * l * d / r ^ (3 : ℕ) * z * (z + 2) + M * (z + 1)
    c5SingleAtomBaseCompensationMargin A t =
      z * ((25 + 72 * z) * p * e * L -
        4 * t * (25 + 72 * z) * p * M * (z + 2) +
        12 * t * (5 + 24 * z) * B * L) +
      5 * t ^ (2 : ℕ) * e * (4 * p * N - z * C * L) := by
  dsimp only
  unfold c5SingleAtomBaseCompensationMargin
  dsimp only
  rw [c5SingleAtomVelocityCenterNumerator_eq_factor,
    c5SingleAtomVelocitySlopeCenterNumerator_eq_factor]
  ring

/-- The highest-jet reserve is the Gaussian reserve minus four explicit rational losses. -/
theorem c5SingleAtomHighestReserve_eq_gaussian_sub_losses
    (A z : ℝ) :
    let l := thetaCuspSingleAtomReflectionLambda A
    let d := c5SingleAtomScaleLambdaJetOne A
    let r := thetaCuspSingleAtomReflectionFactor A z
    let p := 2 * A + l / r
    let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
    let k := l ^ (3 : ℕ) / r ^ (3 : ℕ)
    let L := 4 * A + d / r
    let M := 4 * A + d / r ^ (2 : ℕ)
    let C := 8 * k * z * (z + 2) + 12 * g * (z + 1) + 4 * p
    let N := 2 * l * d / r ^ (3 : ℕ) * z * (z + 2) + M * (z + 1)
    4 * p * N - z * C * L =
      4 * p * L + 4 * p * (M - L) * (z + 1) +
        8 * p * l * d / r ^ (3 : ℕ) * z * (z + 2) -
        12 * g * z * (z + 1) * L - 8 * k * z ^ (2 : ℕ) * (z + 2) * L := by
  dsimp only
  ring

/-- Highest-jet reserve in the exact first-atom base margin. -/
def c5SingleAtomHighestJetReserve (A z : ℝ) : ℝ :=
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
  let k := l ^ (3 : ℕ) / r ^ (3 : ℕ)
  let L := 4 * A + d / r
  let M := 4 * A + d / r ^ (2 : ℕ)
  let C := 8 * k * z * (z + 2) + 12 * g * (z + 1) + 4 * p
  let N := 2 * l * d / r ^ (3 : ℕ) * z * (z + 2) + M * (z + 1)
  4 * p * N - z * C * L

/-- Dimensionless loss of exact highest-jet reserve relative to its Gaussian carrier. -/
def c5SingleAtomHighestJetLossRatio (A z : ℝ) : ℝ :=
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let L := 4 * A + d / r
  let ρ := 2 * (A + 3 / 2) / (A - 3 / 2)
  let x := l / r
  let w := x * z
  ρ * w * (w + x) / L +
    2 * ρ * w * (1 + w) * (w + 2 * x) / L +
    3 * w * (w + x) / p +
    2 * w ^ (2 : ℕ) * (w + 2 * x) / p

/-- Exact reserve factorization: Gaussian carrier times one minus rational loss ratio. -/
theorem c5SingleAtomHighestJetReserve_eq_factor
    {A z : ℝ} (hA : 3 / 2 < A)
    (hr : thetaCuspSingleAtomReflectionFactor A z ≠ 0)
    (hp : 2 * A + thetaCuspSingleAtomReflectionLambda A /
      thetaCuspSingleAtomReflectionFactor A z ≠ 0)
    (hL : 4 * A + c5SingleAtomScaleLambdaJetOne A /
      thetaCuspSingleAtomReflectionFactor A z ≠ 0) :
    c5SingleAtomHighestJetReserve A z =
      4 * (2 * A + thetaCuspSingleAtomReflectionLambda A /
          thetaCuspSingleAtomReflectionFactor A z) *
        (4 * A + c5SingleAtomScaleLambdaJetOne A /
          thetaCuspSingleAtomReflectionFactor A z) *
        (1 - c5SingleAtomHighestJetLossRatio A z) := by
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
  let k := l ^ (3 : ℕ) / r ^ (3 : ℕ)
  let L := 4 * A + d / r
  let M := 4 * A + d / r ^ (2 : ℕ)
  let C := 8 * k * z * (z + 2) + 12 * g * (z + 1) + 4 * p
  let N := 2 * l * d / r ^ (3 : ℕ) * z * (z + 2) + M * (z + 1)
  let ρ := 2 * (A + 3 / 2) / (A - 3 / 2)
  let x := l / r
  let w := x * z
  have hr' : r ≠ 0 := by simpa only [r] using hr
  have hp' : p ≠ 0 := by simpa only [p, l, r] using hp
  have hL' : L ≠ 0 := by simpa only [L, d, r] using hL
  have hd : d = -ρ * l := by
    dsimp only [d, ρ, l]
    rw [c5SingleAtomScaleLambdaJetOne_eq hA]
    ring
  have hrdef : r = 1 - l * z := by
    dsimp only [r, l]
    unfold thetaCuspSingleAtomReflectionFactor
    rfl
  have hML : M - L = -ρ * x * w := by
    dsimp only [M, L, x, w]
    rw [hd]
    field_simp [hr']
    rw [hrdef]
    ring
  have hld : l * d / r ^ (3 : ℕ) * z = -ρ * x * w * (1 + w) := by
    dsimp only [x, w]
    rw [hd]
    field_simp [hr']
    rw [hrdef]
    ring
  have hg : g * z = x * w := by
    dsimp only [g, x, w]
    ring
  have hk : k * z ^ (2 : ℕ) = x * w ^ (2 : ℕ) := by
    dsimp only [k, x, w]
    ring
  have hsub := c5SingleAtomHighestReserve_eq_gaussian_sub_losses A z
  dsimp only at hsub
  change 4 * p * N - z * C * L =
      4 * p * L + 4 * p * (M - L) * (z + 1) +
        8 * p * l * d / r ^ (3 : ℕ) * z * (z + 2) -
        12 * g * z * (z + 1) * L - 8 * k * z ^ (2 : ℕ) * (z + 2) * L at hsub
  unfold c5SingleAtomHighestJetReserve c5SingleAtomHighestJetLossRatio
  dsimp only
  change 4 * p * N - z * C * L =
    4 * p * L *
      (1 - (ρ * w * (w + x) / L +
        2 * ρ * w * (1 + w) * (w + 2 * x) / L +
        3 * w * (w + x) / p +
        2 * w ^ (2 : ℕ) * (w + 2 * x) / p))
  rw [hsub, hML]
  rw [show 8 * p * l * d / r ^ (3 : ℕ) * z * (z + 2) =
      8 * p * (l * d / r ^ (3 : ℕ) * z) * (z + 2) by ring, hld]
  rw [show 12 * g * z * (z + 1) * L =
      12 * (g * z) * (z + 1) * L by ring, hg]
  rw [show 8 * k * z ^ (2 : ℕ) * (z + 2) * L =
      8 * (k * z ^ (2 : ℕ)) * (z + 2) * L by ring, hk]
  field_simp [hp', hL']
  dsimp only [w]
  ring

/-- Exact rational correction to the Gaussian-carrier base margin. -/
def c5SingleAtomBaseRationalCorrection (A t : ℝ) : ℝ :=
  let z := thetaCuspSingleAtomReflectionDefect t
  let e := 2 * Real.sinh (2 * t)
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let L := 4 * A + d / r
  let ρ := 2 * (A + 3 / 2) / (A - 3 / 2)
  let x := l / r
  let w := x * z
  4 * t * x * w * z * (z + 2) *
      ((25 + 72 * z) * p * ρ + 3 * (5 + 24 * z) * L) -
    20 * t ^ (2 : ℕ) * e * p * L * c5SingleAtomHighestJetLossRatio A z

/-- Exact atom base margin is Gaussian carrier plus one rational correction. -/
theorem c5SingleAtomBaseCompensationMargin_eq_gaussian_add_correction
    {A t : ℝ} (hA : 3 / 2 < A)
    (hr : thetaCuspSingleAtomReflectionFactor A
      (thetaCuspSingleAtomReflectionDefect t) ≠ 0)
    (hp : 2 * A + thetaCuspSingleAtomReflectionLambda A /
      thetaCuspSingleAtomReflectionFactor A
        (thetaCuspSingleAtomReflectionDefect t) ≠ 0)
    (hL : 4 * A + c5SingleAtomScaleLambdaJetOne A /
      thetaCuspSingleAtomReflectionFactor A
        (thetaCuspSingleAtomReflectionDefect t) ≠ 0) :
    c5SingleAtomBaseCompensationMargin A t =
      (2 * A + thetaCuspSingleAtomReflectionLambda A /
          thetaCuspSingleAtomReflectionFactor A
            (thetaCuspSingleAtomReflectionDefect t)) *
        (4 * A + c5SingleAtomScaleLambdaJetOne A /
          thetaCuspSingleAtomReflectionFactor A
            (thetaCuspSingleAtomReflectionDefect t)) *
        c5HyperbolicGaussianBaseShape t +
      c5SingleAtomBaseRationalCorrection A t := by
  let z := thetaCuspSingleAtomReflectionDefect t
  let e := 2 * Real.sinh (2 * t)
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let g := l ^ (2 : ℕ) / r ^ (2 : ℕ)
  let k := l ^ (3 : ℕ) / r ^ (3 : ℕ)
  let L := 4 * A + d / r
  let M := 4 * A + d / r ^ (2 : ℕ)
  let B := g * z * (z + 2) + p * (z + 1)
  let C := 8 * k * z * (z + 2) + 12 * g * (z + 1) + 4 * p
  let N := 2 * l * d / r ^ (3 : ℕ) * z * (z + 2) + M * (z + 1)
  let ρ := 2 * (A + 3 / 2) / (A - 3 / 2)
  let x := l / r
  let w := x * z
  have hr' : r ≠ 0 := by simpa only [r, z] using hr
  have hp' : p ≠ 0 := by simpa only [p, l, r, z] using hp
  have hL' : L ≠ 0 := by simpa only [L, d, r, z] using hL
  have hd : d = -ρ * l := by
    dsimp only [d, ρ, l]
    rw [c5SingleAtomScaleLambdaJetOne_eq hA]
    ring
  have hrdef : r = 1 - l * z := by
    dsimp only [r, l]
    unfold thetaCuspSingleAtomReflectionFactor
    rfl
  have hM : M = L - ρ * x * w := by
    dsimp only [M, L, x, w]
    rw [hd]
    field_simp [hr']
    rw [hrdef]
    ring
  have hg : g * z = x * w := by
    dsimp only [g, x, w]
    ring
  have hB : B = p * (z + 1) + x * w * (z + 2) := by
    dsimp only [B]
    rw [show g * z * (z + 2) = (g * z) * (z + 2) by ring, hg]
    ring
  have hbase := c5SingleAtomBaseCompensationMargin_eq_factor A t
  dsimp only at hbase
  change c5SingleAtomBaseCompensationMargin A t =
      z * ((25 + 72 * z) * p * e * L -
        4 * t * (25 + 72 * z) * p * M * (z + 2) +
        12 * t * (5 + 24 * z) * B * L) +
      5 * t ^ (2 : ℕ) * e * (4 * p * N - z * C * L) at hbase
  have hreserve := c5SingleAtomHighestJetReserve_eq_factor
    hA hr hp hL
  unfold c5SingleAtomHighestJetReserve at hreserve
  dsimp only at hreserve
  change 4 * p * N - z * C * L =
      4 * p * L * (1 - c5SingleAtomHighestJetLossRatio A z) at hreserve
  unfold c5SingleAtomBaseRationalCorrection c5HyperbolicGaussianBaseShape
  dsimp only
  change c5SingleAtomBaseCompensationMargin A t =
      p * L *
          (z * ((25 + 72 * z) * e - t * (140 + 328 * z)) +
            20 * t ^ (2 : ℕ) * e) +
        (4 * t * x * w * z * (z + 2) *
            ((25 + 72 * z) * p * ρ + 3 * (5 + 24 * z) * L) -
          20 * t ^ (2 : ℕ) * e * p * L *
            c5SingleAtomHighestJetLossRatio A z)
  rw [hbase, hreserve, hM, hB]
  ring

/-- Physical same-half-line rational loss stays strictly below the Gaussian reserve. -/
theorem c5SingleAtomHighestJetLossRatio_lt_one_of_sameHalfLine
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    c5SingleAtomHighestJetLossRatio
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t) < 1 := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let L := 4 * A + d / r
  let ρ := 2 * (A + 3 / 2) / (A - 3 / 2)
  let x := l / r
  let w := x * z
  let D := A ^ (2 : ℕ) - 9 / 2
  let X := 6 * A / D
  let W := (A - 3) ^ (2 : ℕ) / D
  let L₀ := 4 * A - ρ * X
  have hA : 6 ≤ A := by simpa only [A] using hscale
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hAthree : 3 < A := lt_of_lt_of_le (by norm_num) hA
  have hz : 0 < z := by
    dsimp only [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have hrhalf : 1 / 2 < r := by
    simpa only [r, A, z] using
      one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine ht.le htu
  have hr : 0 < r := lt_trans (by norm_num) hrhalf
  have hl : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos hAthree
  have hx0 : 0 < x := by dsimp only [x]; positivity
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith [mul_pos hA0 hA0]
  have hX : 0 < X := by dsimp only [X]; positivity
  have hW : 0 < W := by
    dsimp only [W]
    exact div_pos (sq_pos_of_pos (by linarith)) hD
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact div_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hx : x < X := by
    simpa only [x, X, D, A, z, l, r] using
      thetaCuspSingleAtomReflectionSlopeCorrection_lt_physicalEnvelope ht.le htu
  have hw : w < W := by
    simpa only [w, x, W, D, A, z, l, r] using
      thetaCuspSingleAtomReflectionOdds_lt_physicalEnvelope ht.le htu
  have hL₀ : 0 < L₀ := by
    dsimp only [L₀, ρ, X, D]
    exact c5PhysicalEnvelopeScaleSlope_pos hA
  have hd : d = -ρ * l := by
    dsimp only [d, ρ, l]
    rw [c5SingleAtomScaleLambdaJetOne_eq (by linarith)]
    ring
  have hLeq : L = 4 * A - ρ * x := by
    dsimp only [L, x]
    rw [hd]
    ring
  have hL₀L : L₀ < L := by
    have hmul := mul_lt_mul_of_pos_left hx hρ
    dsimp only [L₀]
    rw [hLeq]
    linarith
  have hL : 0 < L := lt_trans hL₀ hL₀L
  have hpbase : 2 * A < p := by
    dsimp only [p, x] at hx0 ⊢
    linarith
  have hp : 0 < p := lt_trans (by positivity) hpbase
  have hsum : w + x < W + X := add_lt_add hw hx
  have hsumTwo : w + 2 * x < W + 2 * X := by linarith
  have hone : 1 + w < 1 + W := by linarith
  have hwsq : w ^ (2 : ℕ) < W ^ (2 : ℕ) := by
    nlinarith [mul_pos (sub_pos.mpr hw) (add_pos hw0 hW)]
  have hnum₁ : ρ * w * (w + x) < ρ * W * (W + X) := by
    calc
      ρ * w * (w + x) < ρ * W * (w + x) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hw hρ)
          (add_pos hw0 hx0)
      _ < ρ * W * (W + X) :=
        mul_lt_mul_of_pos_left hsum (mul_pos hρ hW)
  have hterm₁ : ρ * w * (w + x) / L < ρ * W * (W + X) / L₀ := by
    calc
      ρ * w * (w + x) / L < ρ * W * (W + X) / L :=
        div_lt_div_of_pos_right hnum₁ hL
      _ < ρ * W * (W + X) / L₀ :=
        div_lt_div_of_pos_left
          (mul_pos (mul_pos hρ hW) (add_pos hW hX)) hL₀ hL₀L
  have hnum₂ :
      2 * ρ * w * (1 + w) * (w + 2 * x) <
        2 * ρ * W * (1 + W) * (W + 2 * X) := by
    calc
      2 * ρ * w * (1 + w) * (w + 2 * x) <
          2 * ρ * W * (1 + w) * (w + 2 * x) := by
            gcongr
      _ < 2 * ρ * W * (1 + W) * (w + 2 * x) := by
            gcongr
      _ < 2 * ρ * W * (1 + W) * (W + 2 * X) := by
            gcongr
  have hterm₂ :
      2 * ρ * w * (1 + w) * (w + 2 * x) / L <
        2 * ρ * W * (1 + W) * (W + 2 * X) / L₀ := by
    calc
      2 * ρ * w * (1 + w) * (w + 2 * x) / L <
          2 * ρ * W * (1 + W) * (W + 2 * X) / L :=
        div_lt_div_of_pos_right hnum₂ hL
      _ < 2 * ρ * W * (1 + W) * (W + 2 * X) / L₀ :=
        div_lt_div_of_pos_left (by positivity) hL₀ hL₀L
  have hnum₃ : 3 * w * (w + x) < 3 * W * (W + X) := by
    calc
      3 * w * (w + x) < 3 * W * (w + x) := by gcongr
      _ < 3 * W * (W + X) := by gcongr
  have hterm₃ : 3 * w * (w + x) / p < 3 * W * (W + X) / (2 * A) := by
    calc
      3 * w * (w + x) / p < 3 * W * (W + X) / p :=
        div_lt_div_of_pos_right hnum₃ hp
      _ < 3 * W * (W + X) / (2 * A) :=
        div_lt_div_of_pos_left (by positivity) (by positivity) hpbase
  have hnum₄ : 2 * w ^ (2 : ℕ) * (w + 2 * x) <
      2 * W ^ (2 : ℕ) * (W + 2 * X) := by
    calc
      2 * w ^ (2 : ℕ) * (w + 2 * x) < 2 * W ^ (2 : ℕ) * (w + 2 * x) := by gcongr
      _ < 2 * W ^ (2 : ℕ) * (W + 2 * X) := by gcongr
  have hterm₄ : 2 * w ^ (2 : ℕ) * (w + 2 * x) / p <
      2 * W ^ (2 : ℕ) * (W + 2 * X) / (2 * A) := by
    calc
      2 * w ^ (2 : ℕ) * (w + 2 * x) / p <
          2 * W ^ (2 : ℕ) * (W + 2 * X) / p :=
        div_lt_div_of_pos_right hnum₄ hp
      _ < 2 * W ^ (2 : ℕ) * (W + 2 * X) / (2 * A) :=
        div_lt_div_of_pos_left (by positivity) (by positivity) hpbase
  have henv := c5PhysicalEnvelopeHighestReserveLossRatio_lt_one hA
  dsimp only at henv
  change ρ * W * (W + X) / L₀ +
      2 * ρ * W * (1 + W) * (W + 2 * X) / L₀ +
      3 * W * (W + X) / (2 * A) +
      2 * W ^ (2 : ℕ) * (W + 2 * X) / (2 * A) < 1 at henv
  unfold c5SingleAtomHighestJetLossRatio
  dsimp only
  change ρ * w * (w + x) / L +
      2 * ρ * w * (1 + w) * (w + 2 * x) / L +
      3 * w * (w + x) / p +
      2 * w ^ (2 : ℕ) * (w + 2 * x) / p < 1
  nlinarith

/-- Physical tail keeps the exact centre-scale action slope positive. -/
theorem c5SingleAtomScaleActionSlope_pos_of_sameHalfLine
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    0 < 4 * thetaCuspSingleAtomReflectionScale 1 u +
      c5SingleAtomScaleLambdaJetOne
          (thetaCuspSingleAtomReflectionScale 1 u) /
        thetaCuspSingleAtomReflectionFactor
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t) := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let ρ := 2 * (A + 3 / 2) / (A - 3 / 2)
  let x := l / r
  let D := A ^ (2 : ℕ) - 9 / 2
  let X := 6 * A / D
  have hA : 6 ≤ A := by simpa only [A] using hscale
  have hx : x < X := by
    simpa only [x, X, D, A, z, l, r] using
      thetaCuspSingleAtomReflectionSlopeCorrection_lt_physicalEnvelope ht htu
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact div_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hL₀ : 0 < 4 * A - ρ * X := by
    dsimp only [ρ, X, D]
    exact c5PhysicalEnvelopeScaleSlope_pos hA
  have hd : d = -ρ * l := by
    dsimp only [d, ρ, l]
    rw [c5SingleAtomScaleLambdaJetOne_eq (by linarith)]
    ring
  have hmul := mul_lt_mul_of_pos_left hx hρ
  change 0 < 4 * A + d / r
  rw [hd]
  rw [show 4 * A + -ρ * l / r = 4 * A - ρ * x by
    dsimp only [x]
    ring]
  nlinarith

/-- Reachable tail states satisfy a strict slope--defect cap. -/
theorem c5SingleAtomSlopeCorrection_mul_defect_add_two_lt_three_of_sameHalfLine
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    thetaCuspSingleAtomReflectionLambda
          (thetaCuspSingleAtomReflectionScale 1 u) /
        thetaCuspSingleAtomReflectionFactor
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t) *
        (thetaCuspSingleAtomReflectionDefect t + 2) < 3 := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let x := l / r
  let w := x * z
  let D := A ^ (2 : ℕ) - 9 / 2
  let X := 6 * A / D
  let W := (A - 3) ^ (2 : ℕ) / D
  have hA : 6 ≤ A := by simpa only [A] using hscale
  have hx : x < X := by
    simpa only [x, X, D, A, z, l, r] using
      thetaCuspSingleAtomReflectionSlopeCorrection_lt_physicalEnvelope ht htu
  have hw : w < W := by
    simpa only [w, x, W, D, A, z, l, r] using
      thetaCuspSingleAtomReflectionOdds_lt_physicalEnvelope ht htu
  have henv := c5PhysicalEnvelopeSlopeDefect_lt_three hA
  change x * (z + 2) < 3
  have heq : x * (z + 2) = w + 2 * x := by
    dsimp only [w]
    ring
  rw [heq]
  nlinarith

/-- Positive rational correction exactly compensates the highest-jet reserve loss. -/
theorem c5SingleAtomBaseRationalCorrection_pos_of_sameHalfLine
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    0 < c5SingleAtomBaseRationalCorrection
      (thetaCuspSingleAtomReflectionScale 1 u) t := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let e := 2 * Real.sinh (2 * t)
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let L := 4 * A + d / r
  let ρ := 2 * (A + 3 / 2) / (A - 3 / 2)
  let x := l / r
  let w := x * z
  let S := (25 + 72 * z) * p * ρ + 3 * (5 + 24 * z) * L
  let T := 5 * p * ρ * (z + 1) +
    10 * p * ρ * (1 + w) * (z + 2) +
    15 * L * (z + 1) + 10 * L * w * (z + 2)
  have hA : 6 ≤ A := by simpa only [A] using hscale
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hz : 0 < z := by
    dsimp only [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have he : 0 < e := by dsimp only [e]; positivity
  have hrhalf : 1 / 2 < r := by
    simpa only [r, A, z] using
      one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine ht.le htu
  have hr : 0 < r := lt_trans (by norm_num) hrhalf
  have hl : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos
      (lt_of_lt_of_le (by norm_num) hA)
  have hx : 0 < x := by dsimp only [x]; positivity
  have hw : 0 < w := by dsimp only [w]; positivity
  have hp : 0 < p := by dsimp only [p]; positivity
  have hL : 0 < L := by
    dsimp only [L, A, z, d, r]
    exact c5SingleAtomScaleActionSlope_pos_of_sameHalfLine ht.le htu hscale
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    exact div_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hcap : x * (z + 2) < 3 := by
    simpa only [x, A, z, l, r] using
      c5SingleAtomSlopeCorrection_mul_defect_add_two_lt_three_of_sameHalfLine
        ht.le htu hscale
  have hwz : w * (z + 2) < 3 * z := by
    have hmul := mul_lt_mul_of_pos_left hcap hz
    dsimp only [w] at hmul ⊢
    nlinarith
  have hbarrier : 0 < 57 * z - 10 * w * (z + 2) := by nlinarith
  have hSTeq : S - T = (p * ρ + L) *
      (57 * z - 10 * w * (z + 2)) := by
    dsimp only [S, T]
    ring
  have hT : 0 < T := by dsimp only [T]; positivity
  have hST : T < S := by
    rw [← sub_pos, hSTeq]
    positivity
  have hS : 0 < S := lt_trans hT hST
  have hefour : 4 * t < e := by
    dsimp only [e]
    have hs := self_lt_sinh (by linarith : 0 < 2 * t)
    linarith
  have hesq : e ^ (2 : ℕ) = 4 * z * (z + 2) := by
    dsimp only [e, z]
    exact sq_two_mul_sinh_two t
  have hfirst : t * e * T < e ^ (2 : ℕ) / 4 * T := by
    have hmulPos : 0 < e * T / 4 :=
      div_pos (mul_pos he hT) (by norm_num)
    have hmul := mul_lt_mul_of_pos_right hefour hmulPos
    have hleft : 4 * t * (e * T / 4) = t * e * T := by ring
    have hright : e * (e * T / 4) = e ^ (2 : ℕ) / 4 * T := by ring
    rw [hleft, hright] at hmul
    exact hmul
  have hsecond : e ^ (2 : ℕ) / 4 * T < e ^ (2 : ℕ) / 4 * S :=
    mul_lt_mul_of_pos_left hST (by positivity)
  have hmain : 0 < z * (z + 2) * S - t * e * T := by
    have hchain := lt_trans hfirst hsecond
    rw [hesq] at hchain
    nlinarith
  have hfactor :
      c5SingleAtomBaseRationalCorrection A t =
        4 * t * x * w * (z * (z + 2) * S - t * e * T) := by
    unfold c5SingleAtomBaseRationalCorrection
      c5SingleAtomHighestJetLossRatio
    dsimp only
    change
      4 * t * x * w * z * (z + 2) * S -
          20 * t ^ (2 : ℕ) * e * p * L *
            (ρ * w * (w + x) / L +
              2 * ρ * w * (1 + w) * (w + 2 * x) / L +
              3 * w * (w + x) / p +
              2 * w ^ (2 : ℕ) * (w + 2 * x) / p) =
        4 * t * x * w * (z * (z + 2) * S - t * e * T)
    field_simp [hp.ne', hL.ne']
    dsimp only [T, w]
    ring
  rw [hfactor]
  positivity

/-- The exact first atom retains strictly positive highest-jet reserve on the physical tail. -/
theorem c5SingleAtomHighestJetReserve_pos_of_sameHalfLine
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    0 < c5SingleAtomHighestJetReserve
      (thetaCuspSingleAtomReflectionScale 1 u)
      (thetaCuspSingleAtomReflectionDefect t) := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let L := 4 * A + d / r
  have hrhalf : 1 / 2 < r := by
    simpa only [r, A, z] using
      one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine ht.le htu
  have hr : 0 < r := lt_trans (by norm_num) hrhalf
  have hl : 0 < l := by
    dsimp only [l]
    exact thetaCuspSingleAtomReflectionLambda_pos
      (lt_of_lt_of_le (by norm_num) hscale)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hL : 0 < L := by
    -- This is the positive factor used in the proved centre-transport factorization.
    have hA : 6 ≤ A := by simpa only [A] using hscale
    let ρ := 2 * (A + 3 / 2) / (A - 3 / 2)
    let x := l / r
    let D := A ^ (2 : ℕ) - 9 / 2
    let X := 6 * A / D
    have hx : x < X := by
      simpa only [x, X, D, A, z, l, r] using
        thetaCuspSingleAtomReflectionSlopeCorrection_lt_physicalEnvelope ht.le htu
    have hρ : 0 < ρ := by
      dsimp only [ρ]
      exact div_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    have hL₀ : 0 < 4 * A - ρ * X := by
      dsimp only [ρ, X, D]
      exact c5PhysicalEnvelopeScaleSlope_pos hA
    have hd : d = -ρ * l := by
      dsimp only [d, ρ, l]
      rw [c5SingleAtomScaleLambdaJetOne_eq (by linarith)]
      ring
    have hmul := mul_lt_mul_of_pos_left hx hρ
    dsimp only [L]
    rw [hd]
    rw [show 4 * A + -ρ * l / r = 4 * A - ρ * x by
      dsimp only [x]
      ring]
    nlinarith
  rw [c5SingleAtomHighestJetReserve_eq_factor
    (by linarith : 3 / 2 < A) hr.ne' hp.ne' hL.ne']
  have hloss := c5SingleAtomHighestJetLossRatio_lt_one_of_sameHalfLine
    ht htu hscale
  dsimp only [A, z] at hloss ⊢
  exact mul_pos (mul_pos (mul_pos (by norm_num) hp) hL) (sub_pos.mpr hloss)

/-- Exact rational-hyperbolic base margin is positive throughout physical tail. -/
theorem c5SingleAtomBaseCompensationMargin_pos_of_sameHalfLine
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    0 < c5SingleAtomBaseCompensationMargin
      (thetaCuspSingleAtomReflectionScale 1 u) t := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let l := thetaCuspSingleAtomReflectionLambda A
  let d := c5SingleAtomScaleLambdaJetOne A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let p := 2 * A + l / r
  let L := 4 * A + d / r
  have hA : 6 ≤ A := by simpa only [A] using hscale
  have hrhalf : 1 / 2 < r := by
    simpa only [r, A, z] using
      one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine ht.le htu
  have hr : 0 < r := lt_trans (by norm_num) hrhalf
  have hl : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos
      (lt_of_lt_of_le (by norm_num) hA)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hL : 0 < L := by
    dsimp only [L, A, z, d, r]
    exact c5SingleAtomScaleActionSlope_pos_of_sameHalfLine ht.le htu hscale
  rw [c5SingleAtomBaseCompensationMargin_eq_gaussian_add_correction
    (by linarith : 3 / 2 < A) hr.ne' hp.ne' hL.ne']
  have hshape := c5HyperbolicGaussianBaseShape_pos ht
  have hcorrection :=
    c5SingleAtomBaseRationalCorrection_pos_of_sameHalfLine ht htu hscale
  dsimp only [A] at hcorrection ⊢
  exact add_pos (mul_pos (mul_pos hp hL) hshape) hcorrection

/-- Exact first reflected theta atom has strict direct-C5 compensation on physical tail. -/
theorem c5SingleAtomCompensationMargin_pos_of_sameHalfLine
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    0 < c5SingleAtomCompensationMargin
      (thetaCuspSingleAtomReflectionScale 1 u) t := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let r := thetaCuspSingleAtomReflectionFactor A z
  have hA : 3 < A :=
    lt_of_lt_of_le (by norm_num) (show 6 ≤ A by simpa only [A] using hscale)
  have hr : 0 < r := by
    have hrhalf : 1 / 2 < r := by
      simpa only [r, A, z] using
        one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine ht.le htu
    linarith
  have hH : c5SingleAtomVelocityCenterNumerator A t < 0 := by
    simpa only [A] using
      c5SingleAtomVelocityCenterNumerator_neg_of_sameHalfLine ht htu hscale
  have hbase : 0 < c5SingleAtomBaseCompensationMargin A t := by
    simpa only [A] using
      c5SingleAtomBaseCompensationMargin_pos_of_sameHalfLine ht htu hscale
  exact c5SingleAtomCompensationMargin_pos_of_base hA ht
    (by simpa only [r, z] using hr) hH hbase

end

end RHTower
