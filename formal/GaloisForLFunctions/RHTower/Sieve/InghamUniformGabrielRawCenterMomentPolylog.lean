import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielCenterMomentPolylog
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLineContinuity

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

theorem continuous_inghamRawError_uniformGabrielCenter
    (sigma : ℝ) (X : ℕ) (hcenter1 : inghamUniformGabrielCenter sigma ≠ 1) :
    Continuous fun t : ℝ =>
      riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
        inghamMollifier X
          ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1 := by
  rw [continuous_iff_continuousAt]
  intro t
  let s : ℂ := (inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    exact hcenter1 hre
  have hpath : ContinuousAt
      (fun u : ℝ => (inghamUniformGabrielCenter sigma : ℂ) + (u : ℂ) * I) t := by
    fun_prop
  have hvalue : ContinuousAt (fun w : ℂ =>
      riemannZeta w * inghamMollifier X w - 1) s :=
    (((analyticAt_riemannZeta_of_ne_one hs1).mul
      (analyticAt_inghamMollifier X s)).sub analyticAt_const).continuousAt
  exact ContinuousAt.comp_of_eq hvalue hpath rfl

private theorem norm_vertical_center_le_ratio_mul_sub_one
    {c t : ℝ} (hc1 : c < 1) :
    ‖(c : ℂ) + (t : ℂ) * I‖ ≤
      (1 + 1 / (1 - c)) * ‖(c : ℂ) + (t : ℂ) * I - 1‖ := by
  let z : ℂ := (c : ℂ) + (t : ℂ) * I
  have hgap : 0 < 1 - c := sub_pos.mpr hc1
  have hnormGap : 1 - c ≤ ‖z - 1‖ := by
    have hre := Complex.abs_re_le_norm (z - 1)
    have habs : |(z - 1).re| = 1 - c := by
      simp [z, abs_of_nonpos (sub_nonpos.mpr hc1.le)]
    simpa only [habs] using hre
  have hone : 1 ≤ (1 / (1 - c)) * ‖z - 1‖ := by
    have hscaled := mul_le_mul_of_nonneg_left hnormGap
      (one_div_nonneg.mpr hgap.le)
    rw [one_div_mul_cancel hgap.ne'] at hscaled
    exact hscaled
  have htriangle : ‖z‖ ≤ ‖z - 1‖ + 1 := by
    have h := norm_add_le (z - 1) (1 : ℂ)
    simpa only [sub_add_cancel, norm_one] using h
  change ‖z‖ ≤ (1 + 1 / (1 - c)) * ‖z - 1‖
  calc
    ‖z‖ ≤ ‖z - 1‖ + 1 := htriangle
    _ ≤ ‖z - 1‖ + (1 / (1 - c)) * ‖z - 1‖ := by linarith
    _ = (1 + 1 / (1 - c)) * ‖z - 1‖ := by ring

private theorem inv_norm_inghamGabrielGaussian_vertical_center_le_exp
    {c kappa T t : ℝ} (hkappa : 0 ≤ kappa) (hT : 0 < T) (ht : |t| ≤ T) :
    (‖Complex.exp ((kappa : ℂ) *
      ((((c : ℂ) + (t : ℂ) * I) / (T : ℂ)) ^ 2))‖)⁻¹ ≤
      Real.exp kappa := by
  rw [norm_inghamGabrielGaussian_vertical kappa T c t hT.ne',
    mul_inv, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htSq : t ^ 2 ≤ T ^ 2 := sq_le_sq.mpr (by
    rw [abs_of_pos hT]
    exact ht)
  have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
  have hquot : kappa * t ^ 2 / T ^ 2 ≤ kappa := by
    apply (div_le_iff₀ hT2).mpr
    exact mul_le_mul_of_nonneg_left htSq hkappa
  have hleft : -(kappa * c ^ 2 / T ^ 2) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg (mul_nonneg hkappa (sq_nonneg c)) hT2.le)
  calc
    -(kappa * c ^ 2 / T ^ 2) + -(-kappa * t ^ 2 / T ^ 2) =
        -(kappa * c ^ 2 / T ^ 2) + kappa * t ^ 2 / T ^ 2 := by ring
    _ ≤ 0 + kappa := add_le_add hleft hquot
    _ = kappa := by ring

theorem norm_inghamRawError_uniformCenter_le_regularized
    (X : ℕ) {c kappa T t : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1)
    (hkappa : 0 ≤ kappa) (hT : 0 < T) (ht : |t| ≤ T) :
    ‖riemannZeta ((c : ℂ) + (t : ℂ) * I) *
        inghamMollifier X ((c : ℂ) + (t : ℂ) * I) - 1‖ ≤
      (1 + 1 / (1 - c)) * Real.exp kappa *
        ‖inghamGabrielPoleClearedError X kappa T
          ((c : ℂ) + (t : ℂ) * I)‖ := by
  let z : ℂ := (c : ℂ) + (t : ℂ) * I
  have hz0 : z ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [z] at hre
    linarith
  have hz1 : z ≠ 1 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [z] at hre
    linarith
  have hzm1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hratio : ‖z‖ / ‖z - 1‖ ≤ 1 + 1 / (1 - c) := by
    apply (div_le_iff₀ (norm_pos_iff.mpr hzm1)).mpr
    simpa only [z] using
      norm_vertical_center_le_ratio_mul_sub_one hc1 (t := t)
  have hginv :
      (‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖)⁻¹ ≤
        Real.exp kappa := by
    simpa only [z] using
      inv_norm_inghamGabrielGaussian_vertical_center_le_exp hkappa hT ht
  have heq := congrArg norm
    (inghamGabrielPoleClearedError_eq_raw X kappa T hz1)
  rw [norm_mul, norm_mul, norm_div] at heq
  have hsolve :
      ‖riemannZeta z * inghamMollifier X z - 1‖ =
        (‖z‖ / ‖z - 1‖) *
          (‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖)⁻¹ *
            ‖inghamGabrielPoleClearedError X kappa T z‖ := by
    rw [heq]
    field_simp [norm_ne_zero_iff.mpr hz0, norm_ne_zero_iff.mpr hzm1,
      norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)]
  change ‖riemannZeta z * inghamMollifier X z - 1‖ ≤
    (1 + 1 / (1 - c)) * Real.exp kappa *
      ‖inghamGabrielPoleClearedError X kappa T z‖
  rw [hsolve]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hratio hginv (inv_nonneg.mpr (norm_nonneg _)) (by positivity))
    (norm_nonneg _)

/-- Raw mollified error inherits the moving center exponent, with only a sigma-dependent constant. -/
theorem exists_inghamRawError_uniformGabrielCenterMoment_le_polylog
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℕ}, 4 ≤ X →
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
          inghamMollifier X
            ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1‖ ^
              inghamUniformGabrielInteriorPower sigma) ≤
        C * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by
  obtain ⟨C0, hC0, hcenter⟩ :=
    exists_inghamGabrielPoleClearedError_uniformCenterMoment_le_polylog
      hsigma0 hsigma1
  have hc0 : 0 < inghamUniformGabrielCenter sigma :=
    lt_of_lt_of_le (by norm_num) (inghamUniformGabrielCenter_ge_half hsigma0)
  have hc1 : inghamUniformGabrielCenter sigma < 1 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter1 : inghamUniformGabrielCenter sigma ≠ 1 := hc1.ne
  let A : ℝ := (1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1
  let C : ℝ := A ^ inghamUniformGabrielInteriorPower sigma * C0
  have hA : 0 ≤ A := by
    dsimp only [A]
    have : 0 < 1 - inghamUniformGabrielCenter sigma := sub_pos.mpr hc1
    positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X hX
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  let raw : ℝ → ℝ := fun t =>
    ‖riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X
        ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1‖ ^
          inghamUniformGabrielInteriorPower sigma
  let field : ℝ → ℝ := fun t =>
    ‖inghamGabrielPoleClearedError X 1 (X : ℝ)
      ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖ ^
        inghamUniformGabrielInteriorPower sigma
  have hrawCont : Continuous raw := by
    dsimp only [raw]
    exact (continuous_inghamRawError_uniformGabrielCenter
      sigma X hcenter1).norm.rpow_const
        (fun _ => Or.inr
          (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1le).le)
  have hfieldCont : Continuous field := by
    dsimp only [field]
    exact (continuous_poleCleared_vertical_of_half_le X
      (z := (inghamUniformGabrielCenter sigma : ℂ))
      (inghamUniformGabrielCenter_ge_half hsigma0)).norm.rpow_const
        (fun _ => Or.inr
          (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1le).le)
  have hpoint : ∀ t ∈ Icc (-(X : ℝ)) (X : ℝ),
      raw t ≤ A ^ inghamUniformGabrielInteriorPower sigma * field t := by
    intro t ht
    have hraw := norm_inghamRawError_uniformCenter_le_regularized X
      hc0 hc1 (kappa := 1) (T := (X : ℝ)) (t := t)
      (by norm_num) hXpos ((abs_le).2 ht)
    have hp := Real.rpow_le_rpow (norm_nonneg _) hraw
      (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1le).le
    rw [Real.mul_rpow (by positivity) (norm_nonneg _)] at hp
    simpa only [raw, field, A] using hp
  have hintegral :
      (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
        A ^ inghamUniformGabrielInteriorPower sigma *
          inghamUniformGabrielCenterMoment sigma
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := by
    calc
      (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
          ∫ t in Icc (-(X : ℝ)) (X : ℝ),
            A ^ inghamUniformGabrielInteriorPower sigma * field t := by
        exact integral_mono_ae hrawCont.integrableOn_Icc
          ((continuous_const.mul hfieldCont).integrableOn_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpoint)
      _ = A ^ inghamUniformGabrielInteriorPower sigma *
          inghamUniformGabrielCenterMoment sigma
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := by
        rw [MeasureTheory.integral_const_mul, inghamUniformGabrielCenterMoment]
  calc
    (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
        A ^ inghamUniformGabrielInteriorPower sigma *
          inghamUniformGabrielCenterMoment sigma
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := hintegral
    _ ≤ A ^ inghamUniformGabrielInteriorPower sigma *
          (C0 * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma)) :=
      mul_le_mul_of_nonneg_left (hcenter hX) (Real.rpow_nonneg hA _)
    _ = C * (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by
      dsimp only [C]
      ring

end

end RHTower.Sieve
