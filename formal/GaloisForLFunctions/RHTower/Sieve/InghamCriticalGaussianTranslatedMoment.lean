import GaloisForLFunctions.RHTower.Sieve.InghamGaussianWindowAbsorption
import GaloisForLFunctions.RHTower.Sieve.InghamGabrielPoleClearedError

noncomputable section

open Complex Set MeasureTheory intervalIntegral

namespace RHTower.Sieve

private def criticalRawErrorDensity (X : ℕ) (t : ℝ) : ℝ :=
  ‖riemannZeta (inghamCriticalPoint t) *
      inghamMollifier X (inghamCriticalPoint t) - 1‖ ^ (4 / 3 : ℝ)

private theorem continuous_criticalRawErrorDensity (X : ℕ) :
    Continuous (criticalRawErrorDensity X) := by
  exact (((continuous_riemannZeta_inghamCriticalPoint.mul
    (continuous_inghamMollifier_critical X)).sub continuous_const).norm).rpow_const
      (fun _ => Or.inr (by norm_num))

private theorem setIntegral_Icc_eq_intervalIntegral
    {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Icc a b, g t) = ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem inghamCriticalErrorFourThirdMoment_eq_intervalIntegral
    (X : ℕ) {a b : ℝ} (hab : a ≤ b) :
    inghamCriticalErrorFourThirdMoment X a b =
      ∫ t in a..b, criticalRawErrorDensity X t := by
  rw [inghamCriticalErrorFourThirdMoment,
    intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rfl

private theorem inghamCriticalErrorFourThirdMoment_mono_set
    (X : ℕ) {a b c d : ℝ} (hsub : Icc a b ⊆ Icc c d) :
    inghamCriticalErrorFourThirdMoment X a b ≤
      inghamCriticalErrorFourThirdMoment X c d := by
  unfold inghamCriticalErrorFourThirdMoment
  exact MeasureTheory.setIntegral_mono_set
    (continuous_criticalRawErrorDensity X).integrableOn_Icc
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall hsub)

private theorem translated_criticalRawErrorDensity_integral_le
    (X N : ℕ) (tau : ℝ) (hcover : |tau| + (X : ℝ) ≤ N) :
    (∫ t in Icc (-(X : ℝ)) (X : ℝ),
      criticalRawErrorDensity X (tau + t)) ≤
        inghamCriticalErrorFourThirdMoment X (-(N : ℝ)) (N : ℝ) := by
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hshift :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        criticalRawErrorDensity X (tau + t)) =
        inghamCriticalErrorFourThirdMoment X
          (-(X : ℝ) + tau) ((X : ℝ) + tau) := by
    rw [setIntegral_Icc_eq_intervalIntegral (by linarith)]
    calc
      (∫ t in -(X : ℝ)..(X : ℝ), criticalRawErrorDensity X (tau + t)) =
          ∫ t in -(X : ℝ)..(X : ℝ), criticalRawErrorDensity X (t + tau) := by
        apply intervalIntegral.integral_congr
        intro t _
        change criticalRawErrorDensity X (tau + t) =
          criticalRawErrorDensity X (t + tau)
        rw [add_comm]
      _ = ∫ t in -(X : ℝ) + tau..(X : ℝ) + tau,
          criticalRawErrorDensity X t :=
        intervalIntegral.integral_comp_add_right _ _
      _ = inghamCriticalErrorFourThirdMoment X
          (-(X : ℝ) + tau) ((X : ℝ) + tau) :=
        (inghamCriticalErrorFourThirdMoment_eq_intervalIntegral X (by linarith)).symm
  rw [hshift]
  apply inghamCriticalErrorFourThirdMoment_mono_set
  intro u hu
  constructor
  · have htau := neg_le_abs tau
    linarith [hu.1]
  · have htau := le_abs_self tau
    linarith [hu.2]

private theorem criticalLine_shift_eq
    {z : ℂ} (hz : z.re = 1 / 2) (t : ℝ) :
    z + (t : ℂ) * I = inghamCriticalPoint (z.im + t) := by
  apply Complex.ext
  · simp [inghamCriticalPoint, hz]
  · simp [inghamCriticalPoint]

private theorem continuous_criticalLine_shift_poleCleared
    (X : ℕ) {z : ℂ} (hz : z.re = 1 / 2) :
    Continuous fun t : ℝ =>
      inghamGabrielPoleClearedError X 1 (X : ℝ) (z + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hpoint0 : z + (t : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [hz] at hre
  have hpath : ContinuousAt (fun u : ℝ => z + (u : ℂ) * I) t := by fun_prop
  change ContinuousAt
    (inghamGabrielPoleClearedError X 1 (X : ℝ) ∘
      fun u : ℝ => z + (u : ℂ) * I) t
  exact ContinuousAt.comp_of_eq
    (analyticAt_inghamGabrielPoleClearedError X 1 (X : ℝ) hpoint0).continuousAt
    hpath rfl

private theorem max_sub_le_abs_add
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

private theorem poleCleared_critical_shift_rpow_le
    (X : ℕ) {z : ℂ} (hz : z.re = 1 / 2) (hX : 4 ≤ X)
    {t : ℝ} (ht : t ∈ Icc (-(X : ℝ)) (X : ℝ)) :
    ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
        (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ) ≤
      Real.exp (4 / 3 : ℝ) *
        Real.exp (-(4 / 3 : ℝ) *
          (max 0 (|z.im| - (X : ℝ)) / (X : ℝ)) ^ 2) *
        criticalRawErrorDensity X (z.im + t) := by
  let d : ℝ := max 0 (|z.im| - (X : ℝ))
  let y : ℝ := z.im + t
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX4 : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hpoint : z + (t : ℂ) * I = inghamCriticalPoint y := by
    dsimp only [y]
    exact criticalLine_shift_eq hz t
  have hraw := norm_inghamGabrielPoleClearedError_le_raw X 1 (X : ℝ)
    (z := z + (t : ℂ) * I) (by simp [hz]) (by
      rw [hpoint]
      exact inghamCriticalPoint_ne_one y)
  have hgauss := norm_inghamGabrielGaussian_vertical
    1 (X : ℝ) (1 / 2 : ℝ) y hXpos.ne'
  have hgaussPoint :
      ‖Complex.exp ((1 : ℂ) *
        (((z + (t : ℂ) * I) / (X : ℂ)) ^ 2))‖ =
        Real.exp ((1 / 2 : ℝ) ^ 2 / (X : ℝ) ^ 2) *
          Real.exp (-y ^ 2 / (X : ℝ) ^ 2) := by
    rw [hpoint]
    simpa [inghamCriticalPoint] using hgauss
  have habscissa : Real.exp ((1 / 2 : ℝ) ^ 2 / (X : ℝ) ^ 2) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    rw [div_le_one (sq_pos_of_pos hXpos)]
    norm_num
    nlinarith [sq_nonneg ((X : ℝ) - 4)]
  have hdist : d ^ 2 ≤ y ^ 2 := by
    have hd := max_sub_le_abs_add X z.im t ht
    have hd0 : 0 ≤ d := by dsimp only [d]; exact le_max_left _ _
    have habs0 : 0 ≤ |y| := abs_nonneg _
    have hprod : 0 ≤ (|y| - d) * (|y| + d) :=
      mul_nonneg (sub_nonneg.mpr (by simpa only [y] using hd))
        (add_nonneg habs0 hd0)
    nlinarith [sq_abs y]
  have hdecay : Real.exp (-y ^ 2 / (X : ℝ) ^ 2) ≤
      Real.exp (-d ^ 2 / (X : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hXsq : 0 < (X : ℝ) ^ 2 := sq_pos_of_pos hXpos
    exact div_le_div_of_nonneg_right (neg_le_neg hdist) hXsq.le
  have hgaussBound :
      ‖Complex.exp ((1 : ℂ) *
        (((z + (t : ℂ) * I) / (X : ℂ)) ^ 2))‖ ≤
        Real.exp 1 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2) := by
    rw [hgaussPoint]
    exact mul_le_mul habscissa hdecay (Real.exp_pos _).le (Real.exp_pos _).le
  have hfield :
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ) (z + (t : ℂ) * I)‖ ≤
        (Real.exp 1 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) *
          ‖riemannZeta (inghamCriticalPoint y) *
            inghamMollifier X (inghamCriticalPoint y) - 1‖ := by
    calc
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ) (z + (t : ℂ) * I)‖ ≤
          ‖Complex.exp ((1 : ℂ) *
            (((z + (t : ℂ) * I) / (X : ℂ)) ^ 2))‖ *
            ‖riemannZeta (z + (t : ℂ) * I) *
              inghamMollifier X (z + (t : ℂ) * I) - 1‖ := hraw
      _ ≤ (Real.exp 1 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) *
            ‖riemannZeta (z + (t : ℂ) * I) *
              inghamMollifier X (z + (t : ℂ) * I) - 1‖ :=
        mul_le_mul_of_nonneg_right hgaussBound (norm_nonneg _)
      _ = (Real.exp 1 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) *
            ‖riemannZeta (inghamCriticalPoint y) *
              inghamMollifier X (inghamCriticalPoint y) - 1‖ := by rw [hpoint]
  have hrpow := Real.rpow_le_rpow (norm_nonneg _) hfield (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have hconst :
      (Real.exp 1 * Real.exp (-d ^ 2 / (X : ℝ) ^ 2)) ^ (4 / 3 : ℝ) =
        Real.exp (4 / 3 : ℝ) *
          Real.exp (-(4 / 3 : ℝ) * (d / (X : ℝ)) ^ 2) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      ← Real.exp_add]
    congr 1
    field_simp
  rw [Real.mul_rpow (by positivity) (norm_nonneg _), hconst] at hrpow
  simpa only [criticalRawErrorDensity, d, y] using hrpow

/-- Uniform translated `4/3` endpoint moment for the actual critical-line Gaussian pole-cleared
mollified error. -/
theorem exists_inghamGabrielPoleClearedError_critical_translatedMoment_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X → ∀ z : ℂ, z.re = 1 / 2 →
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤
        C * (X : ℝ) ^ (251 / 250 : ℝ) := by
  obtain ⟨Craw, hCraw, hraw⟩ :=
    exists_inghamCriticalErrorFourThirdMoment_symmetric_nat_le_routeTBudget
  let K : ℝ := (4 : ℝ) ^ (251 / 250 : ℝ) * Real.exp (3 / 4 : ℝ)
  let C : ℝ := Real.exp (4 / 3 : ℝ) * Craw * K
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X hX z hz
  let tau : ℝ := z.im
  let d : ℝ := max 0 (|tau| - (X : ℝ))
  let N : ℕ := Nat.ceil (|tau| + (X : ℝ))
  let G : ℝ := Real.exp (4 / 3 : ℝ) *
    Real.exp (-(4 / 3 : ℝ) * (d / (X : ℝ)) ^ 2)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hcover : |tau| + (X : ℝ) ≤ (N : ℝ) := by
    dsimp only [N]
    exact Nat.le_ceil _
  have hXN : X ≤ N := by
    exact_mod_cast (show (X : ℝ) ≤ N by linarith [abs_nonneg tau])
  have hrawN := hraw hX hXN
  have htranslate := translated_criticalRawErrorDensity_integral_le X N tau hcover
  have hrawShift :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        criticalRawErrorDensity X (tau + t)) ≤
          Craw * (N : ℝ) ^ (251 / 250 : ℝ) := htranslate.trans hrawN
  have hfieldCont : Continuous fun t : ℝ =>
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
        (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ) :=
    (((continuous_criticalLine_shift_poleCleared X hz).norm).rpow_const
      (fun _ => Or.inr (by norm_num)))
  have hrawShiftCont : Continuous fun t : ℝ =>
      criticalRawErrorDensity X (tau + t) :=
    (continuous_criticalRawErrorDensity X).comp (by fun_prop)
  have hpointwise : ∀ t ∈ Icc (-(X : ℝ)) (X : ℝ),
      ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ) ≤
        G * criticalRawErrorDensity X (tau + t) := by
    intro t ht
    simpa only [G, d, tau] using poleCleared_critical_shift_rpow_le X hz hX ht
  have hintegral :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤
        G * (∫ t in Icc (-(X : ℝ)) (X : ℝ),
          criticalRawErrorDensity X (tau + t)) := by
    calc
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤
          ∫ t in Icc (-(X : ℝ)) (X : ℝ),
            G * criticalRawErrorDensity X (tau + t) := by
        exact integral_mono_ae hfieldCont.integrableOn_Icc
          ((continuous_const.mul hrawShiftCont).integrableOn_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpointwise)
      _ = G * (∫ t in Icc (-(X : ℝ)) (X : ℝ),
          criticalRawErrorDensity X (tau + t)) := by
        rw [MeasureTheory.integral_const_mul]
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have habsorb := gaussianCriticalWindowAbsorption X tau hX
  dsimp only at habsorb
  calc
    (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
          (z + (t : ℂ) * I)‖ ^ (4 / 3 : ℝ)) ≤
        G * (∫ t in Icc (-(X : ℝ)) (X : ℝ),
          criticalRawErrorDensity X (tau + t)) := hintegral
    _ ≤ G * (Craw * (N : ℝ) ^ (251 / 250 : ℝ)) :=
      mul_le_mul_of_nonneg_left hrawShift hG0
    _ = Real.exp (4 / 3 : ℝ) * Craw *
        (Real.exp (-(4 / 3 : ℝ) * (d / (X : ℝ)) ^ 2) *
          (N : ℝ) ^ (251 / 250 : ℝ)) := by
      dsimp only [G]
      ring
    _ ≤ Real.exp (4 / 3 : ℝ) * Craw *
        (K * (X : ℝ) ^ (251 / 250 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [d, N, K] using habsorb
      · exact mul_nonneg (Real.exp_pos _).le hCraw
    _ = C * (X : ℝ) ^ (251 / 250 : ℝ) := by
      dsimp only [C]
      ring

end RHTower.Sieve
