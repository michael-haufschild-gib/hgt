import GaloisForLFunctions.RHTower.Sieve.InghamMovingRightEdgePowerSaving
import GaloisForLFunctions.RHTower.Sieve.InghamRightGaussianTranslatedMoment

noncomputable section

open Complex Set MeasureTheory intervalIntegral

namespace RHTower.Sieve

private def movingRightPoint (delta t : ℝ) : ℂ :=
  ((1 + delta : ℝ) : ℂ) + (t : ℂ) * I

private def movingRightRawDensity (delta : ℝ) (X : ℕ) (t : ℝ) : ℝ :=
  ‖riemannZeta (movingRightPoint delta t) *
      inghamMollifier X (movingRightPoint delta t) - 1‖ ^ (2 : ℝ)

private theorem continuous_movingRightPoint (delta : ℝ) :
    Continuous (movingRightPoint delta) := by
  unfold movingRightPoint
  fun_prop

private theorem movingRightPoint_ne_one
    {delta : ℝ} (hdelta : 0 < delta) (t : ℝ) :
    movingRightPoint delta t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [movingRightPoint, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, mul_one, sub_zero, add_zero, one_re] at hre
  linarith

private theorem continuous_movingRightRawDensity
    {delta : ℝ} (hdelta : 0 < delta) (X : ℕ) :
    Continuous (movingRightRawDensity delta X) := by
  have hzeta : Continuous fun t : ℝ => riemannZeta (movingRightPoint delta t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (differentiableAt_riemannZeta
      (movingRightPoint_ne_one hdelta t)).continuousAt.comp'
      (continuous_movingRightPoint delta).continuousAt
  have hmoll : Continuous fun t : ℝ =>
      inghamMollifier X (movingRightPoint delta t) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (analyticAt_inghamMollifier X (movingRightPoint delta t)).continuousAt.comp'
      (continuous_movingRightPoint delta).continuousAt
  exact (((hzeta.mul hmoll).sub continuous_const).norm).rpow_const
    (fun _ => Or.inr (by norm_num))

private theorem movingRight_setIntegral_Icc_eq_intervalIntegral
    {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Icc a b, g t) = ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem translated_movingRightRawDensity_integral_le
    {delta : ℝ} (hdelta : 0 < delta)
    (X N : ℕ) (tau : ℝ) (hcover : |tau| + (X : ℝ) ≤ N) :
    (∫ t in Icc (-(X : ℝ)) (X : ℝ),
      movingRightRawDensity delta X (tau + t)) ≤
        ∫ t in Icc (-(N : ℝ)) (N : ℝ),
          movingRightRawDensity delta X t := by
  have hshift :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        movingRightRawDensity delta X (tau + t)) =
        ∫ t in Icc (-(X : ℝ) + tau) ((X : ℝ) + tau),
          movingRightRawDensity delta X t := by
    rw [movingRight_setIntegral_Icc_eq_intervalIntegral (by
        have hX0 : (0 : ℝ) ≤ X := by positivity
        linarith),
      movingRight_setIntegral_Icc_eq_intervalIntegral (by linarith)]
    calc
      (∫ t in -(X : ℝ)..(X : ℝ),
          movingRightRawDensity delta X (tau + t)) =
          ∫ t in -(X : ℝ)..(X : ℝ),
            movingRightRawDensity delta X (t + tau) := by
        apply intervalIntegral.integral_congr
        intro t _
        change movingRightRawDensity delta X (tau + t) =
          movingRightRawDensity delta X (t + tau)
        rw [add_comm]
      _ = _ := intervalIntegral.integral_comp_add_right _ _
  rw [hshift]
  exact MeasureTheory.setIntegral_mono_set
    (continuous_movingRightRawDensity hdelta X).integrableOn_Icc
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall fun u hu => by
      constructor
      · linarith [hu.1, neg_le_abs tau]
      · linarith [hu.2, le_abs_self tau])

private theorem movingRight_shift_eq
    {delta : ℝ} {z : ℂ} (hz : z.re = 1 + delta) (t : ℝ) :
    z + (t : ℂ) * I = movingRightPoint delta (z.im + t) := by
  apply Complex.ext
  · simp [movingRightPoint, hz]
  · simp [movingRightPoint]

private theorem continuous_movingRight_shift_poleCleared
    (X : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    {z : ℂ} (hz : z.re = 1 + delta) :
    Continuous fun t : ℝ =>
      inghamGabrielPoleClearedError X 1 (X : ℝ) (z + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hpoint0 : z + (t : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_re] at hre
    rw [hz] at hre
    linarith
  have hpath : ContinuousAt (fun u : ℝ => z + (u : ℂ) * I) t := by fun_prop
  change ContinuousAt
    (inghamGabrielPoleClearedError X 1 (X : ℝ) ∘
      fun u : ℝ => z + (u : ℂ) * I) t
  exact ContinuousAt.comp_of_eq
    (analyticAt_inghamGabrielPoleClearedError X 1 (X : ℝ) hpoint0).continuousAt
    hpath rfl

private theorem movingRight_max_sub_le_abs_add
    (X : ℕ) (tau t : ℝ) (ht : t ∈ Icc (-(X : ℝ)) (X : ℝ)) :
    max 0 (|tau| - (X : ℝ)) ≤ |tau + t| := by
  have htAbs : |t| ≤ (X : ℝ) := (abs_le).2 ht
  have htri : |tau| ≤ |tau + t| + |t| := by
    calc
      |tau| = |(tau + t) + (-t)| := by ring_nf
      _ ≤ |tau + t| + |-t| := abs_add_le _ _
      _ = |tau + t| + |t| := by rw [abs_neg]
  apply max_le (abs_nonneg _)
  linarith

private theorem poleCleared_movingRight_shift_rpow_le
    (X : ℕ) {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {z : ℂ} (hz : z.re = 1 + delta) (hX : 4 ≤ X)
    {t : ℝ} (ht : t ∈ Icc (-(X : ℝ)) (X : ℝ)) :
    ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
        (z + (t : ℂ) * I)‖ ^ (2 : ℝ) ≤
      Real.exp 8 *
        Real.exp (-2 *
          (max 0 (|z.im| - (X : ℝ)) / (X : ℝ)) ^ 2) *
        movingRightRawDensity delta X (z.im + t) := by
  let d : ℝ := max 0 (|z.im| - (X : ℝ))
  let y : ℝ := z.im + t
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX4 : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hpoint : z + (t : ℂ) * I = movingRightPoint delta y := by
    dsimp only [y]
    exact movingRight_shift_eq hz t
  have hraw := norm_inghamGabrielPoleClearedError_le_raw X 1 (X : ℝ)
    (z := z + (t : ℂ) * I)
    (by simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, hz]; linarith)
    (by rw [hpoint]; exact movingRightPoint_ne_one hdelta y)
  have hgauss := norm_inghamGabrielGaussian_vertical
    1 (X : ℝ) (1 + delta) y hXpos.ne'
  have hgaussPoint :
      ‖Complex.exp ((1 : ℂ) * (((z + (t : ℂ) * I) / (X : ℂ)) ^ 2))‖ =
        Real.exp ((1 + delta) ^ 2 / (X : ℝ) ^ 2) *
          Real.exp (-y ^ 2 / (X : ℝ) ^ 2) := by
    rw [hpoint]
    simpa [movingRightPoint] using hgauss
  have habscissa :
      Real.exp ((1 + delta) ^ 2 / (X : ℝ) ^ 2) ≤ Real.exp 4 := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (sq_pos_of_pos hXpos)]
    nlinarith [sq_nonneg ((X : ℝ) - 4), sq_nonneg (1 - delta)]
  have hdist : d ^ 2 ≤ y ^ 2 := by
    have hd := movingRight_max_sub_le_abs_add X z.im t ht
    have hd0 : 0 ≤ d := by dsimp only [d]; exact le_max_left _ _
    have habs0 : 0 ≤ |y| := abs_nonneg _
    have hprod : 0 ≤ (|y| - d) * (|y| + d) :=
      mul_nonneg (sub_nonneg.mpr (by simpa only [y] using hd))
        (add_nonneg habs0 hd0)
    nlinarith [sq_abs y]
  have hdecay : Real.exp (-y ^ 2 / (X : ℝ) ^ 2) ≤
      Real.exp (-d ^ 2 / (X : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg hdist) (sq_nonneg _)
  have hgaussBound :
      ‖Complex.exp ((1 : ℂ) * (((z + (t : ℂ) * I) / (X : ℂ)) ^ 2))‖ ≤
        Real.exp 4 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2) := by
    rw [hgaussPoint]
    exact mul_le_mul habscissa hdecay (Real.exp_pos _).le (Real.exp_pos _).le
  have hfield :
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ) (z + (t : ℂ) * I)‖ ≤
        (Real.exp 4 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) *
          ‖riemannZeta (movingRightPoint delta y) *
            inghamMollifier X (movingRightPoint delta y) - 1‖ := by
    calc
      _ ≤ ‖Complex.exp ((1 : ℂ) * (((z + (t : ℂ) * I) / (X : ℂ)) ^ 2))‖ *
            ‖riemannZeta (z + (t : ℂ) * I) *
              inghamMollifier X (z + (t : ℂ) * I) - 1‖ := hraw
      _ ≤ (Real.exp 4 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) *
            ‖riemannZeta (z + (t : ℂ) * I) *
              inghamMollifier X (z + (t : ℂ) * I) - 1‖ :=
        mul_le_mul_of_nonneg_right hgaussBound (norm_nonneg _)
      _ = _ := by rw [hpoint]
  have hrpow := Real.rpow_le_rpow (norm_nonneg _) hfield (by norm_num : (0 : ℝ) ≤ 2)
  have hconst :
      (Real.exp 4 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) ^ (2 : ℝ) =
        Real.exp 8 * Real.exp (-2 * (d / (X : ℝ)) ^ 2) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [Real.mul_rpow (by positivity) (norm_nonneg _), hconst] at hrpow
  simpa only [movingRightRawDensity, d, y] using hrpow

/-- Gaussian translation preserves the moving-right-edge power saving uniformly in the ordinate. -/
theorem exists_inghamGabrielPoleClearedError_movingRight_translatedMoment_le
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X → ∀ z : ℂ,
      z.re = 1 + delta →
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤
        C * (X : ℝ) ^ (-delta) := by
  obtain ⟨A, B, hA, hB, hraw⟩ :=
    exists_integral_Icc_normSq_inghamMollifiedError_movingRightEdge_symmetric_le hdelta
  let K : ℝ := 4 * Real.exp (1 / 2 : ℝ)
  let C : ℝ := Real.exp 8 * (A + B * K)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X hX z hz
  let tau : ℝ := z.im
  let d : ℝ := max 0 (|tau| - (X : ℝ))
  let N : ℕ := Nat.ceil (|tau| + (X : ℝ))
  let E : ℝ := Real.exp (-2 * (d / (X : ℝ)) ^ 2)
  let G : ℝ := Real.exp 8 * E
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hcover : |tau| + (X : ℝ) ≤ (N : ℝ) := by
    dsimp only [N]
    exact Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    exact_mod_cast (show (1 : ℝ) ≤ N by linarith [abs_nonneg tau])
  have hrawN := hraw (X := X) (N := N) (by omega) hN1
  have hrawN' :
      (∫ t in Icc (-(N : ℝ)) (N : ℝ),
        movingRightRawDensity delta X t) ≤
        A * (X : ℝ) ^ (-delta) +
          B * (X : ℝ) ^ (-(1 + delta)) * (N : ℝ) := by
    simpa only [movingRightRawDensity, movingRightPoint,
      Real.rpow_two] using hrawN
  have htranslate :=
    translated_movingRightRawDensity_integral_le hdelta X N tau hcover
  have hrawShift := htranslate.trans hrawN'
  have hfieldCont : Continuous fun t : ℝ =>
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
        (z + (t : ℂ) * I)‖ ^ (2 : ℝ) :=
    (((continuous_movingRight_shift_poleCleared X hdelta hz).norm).rpow_const
      (fun _ => Or.inr (by norm_num)))
  have hrawShiftCont : Continuous fun t : ℝ =>
      movingRightRawDensity delta X (tau + t) :=
    (continuous_movingRightRawDensity hdelta X).comp (by fun_prop)
  have hpointwise : ∀ t ∈ Icc (-(X : ℝ)) (X : ℝ),
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (2 : ℝ) ≤
        G * movingRightRawDensity delta X (tau + t) := by
    intro t ht
    simpa only [G, E, d, tau] using
      poleCleared_movingRight_shift_rpow_le X hdelta hdelta1 hz hX ht
  have hintegral :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (2 : ℝ)) ≤
        G * (∫ t in Icc (-(X : ℝ)) (X : ℝ),
          movingRightRawDensity delta X (tau + t)) := by
    calc
      _ ≤ ∫ t in Icc (-(X : ℝ)) (X : ℝ),
            G * movingRightRawDensity delta X (tau + t) := by
        exact integral_mono_ae hfieldCont.integrableOn_Icc
          ((continuous_const.mul hrawShiftCont).integrableOn_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpointwise)
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hE1 : E ≤ 1 := by
    dsimp only [E]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (d / (X : ℝ))]
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have habsorb := gaussianLinearWindowAbsorption X tau hX
  dsimp only at habsorb
  have hEN : E * (N : ℝ) ≤ K * (X : ℝ) := by
    simpa only [E, d, N, K] using habsorb
  have hpow : (X : ℝ) ^ (-(1 + delta)) * (X : ℝ) =
      (X : ℝ) ^ (-delta) := by
    calc
      (X : ℝ) ^ (-(1 + delta)) * (X : ℝ) =
          (X : ℝ) ^ (-(1 + delta)) * (X : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (X : ℝ) ^ (-(1 + delta) + 1) := by rw [Real.rpow_add hXpos]
      _ = (X : ℝ) ^ (-delta) := by congr 1; ring
  have hfirstE : E * (X : ℝ) ^ (-delta) ≤ (X : ℝ) ^ (-delta) := by
    calc
      E * (X : ℝ) ^ (-delta) ≤ 1 * (X : ℝ) ^ (-delta) :=
        mul_le_mul hE1 le_rfl (Real.rpow_nonneg hXpos.le _) (by norm_num)
      _ = _ := one_mul _
  have hsecondE :
      (X : ℝ) ^ (-(1 + delta)) * (E * (N : ℝ)) ≤
        (X : ℝ) ^ (-(1 + delta)) * (K * (X : ℝ)) :=
    mul_le_mul_of_nonneg_left hEN (Real.rpow_nonneg hXpos.le _)
  calc
    _ ≤ G * (∫ t in Icc (-(X : ℝ)) (X : ℝ),
          movingRightRawDensity delta X (tau + t)) := hintegral
    _ ≤ G * (A * (X : ℝ) ^ (-delta) +
          B * (X : ℝ) ^ (-(1 + delta)) * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hrawShift hG0
    _ = Real.exp 8 *
        (A * (E * (X : ℝ) ^ (-delta)) +
          B * (X : ℝ) ^ (-(1 + delta)) * (E * (N : ℝ))) := by
      dsimp only [G]
      ring
    _ ≤ Real.exp 8 *
        (A * (X : ℝ) ^ (-delta) +
          B * (X : ℝ) ^ (-(1 + delta)) * (K * (X : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact add_le_add
        (mul_le_mul_of_nonneg_left hfirstE hA.le)
        (by
          calc
            B * (X : ℝ) ^ (-(1 + delta)) * (E * (N : ℝ)) =
                B * ((X : ℝ) ^ (-(1 + delta)) * (E * (N : ℝ))) := by ring
            _ ≤ B * ((X : ℝ) ^ (-(1 + delta)) * (K * (X : ℝ))) :=
              mul_le_mul_of_nonneg_left hsecondE hB.le
            _ = B * (X : ℝ) ^ (-(1 + delta)) * (K * (X : ℝ)) := by ring)
    _ = C * (X : ℝ) ^ (-delta) := by
      calc
        Real.exp 8 *
            (A * (X : ℝ) ^ (-delta) +
              B * (X : ℝ) ^ (-(1 + delta)) * (K * (X : ℝ))) =
            Real.exp 8 *
              (A * (X : ℝ) ^ (-delta) +
                B * K * ((X : ℝ) ^ (-(1 + delta)) * (X : ℝ))) := by ring
        _ = Real.exp 8 *
              (A * (X : ℝ) ^ (-delta) +
                B * K * (X : ℝ) ^ (-delta)) := by rw [hpow]
        _ = C * (X : ℝ) ^ (-delta) := by
          dsimp only [C]
          ring

end RHTower.Sieve
