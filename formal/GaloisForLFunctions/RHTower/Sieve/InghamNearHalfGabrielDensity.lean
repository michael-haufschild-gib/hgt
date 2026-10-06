import GaloisForLFunctions.RHTower.Sieve.InghamNearHalfGabrielInterpolation
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorHorizontalTubeCritical
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorDensityExplicit

/-!
# The uniform Ingham–Gabriel zero mass down to the critical line

The moving-Gabriel centre moment (`InghamNearHalfGabrielInterpolation`), the logarithmic detector
moment on the centre line, and the horizontal edges of the critical tube
(`InghamDetectorHorizontalTubeCritical`, segments `[1/2, 4]`) assemble, exactly as in
`InghamUniformDetectorDensityExplicit`, into Littlewood's bound for the zero mass to the right of
the moving centre `c(σ) = σ − (1 − σ)/1000`, now for every `501/1001 ≤ σ < 1`
(`exists_eventually_zetaZeroMass_le_uniformGabrielExplicit`).
-/

namespace RHTower.Sieve.InghamNearHalf

noncomputable section

/-! ### From `InghamUniformGabrielCenterMomentExplicit` -/

section
open Complex MeasureTheory Set

/-- The moving-Gabriel center moment with all dependence on the counting line exposed. The
constant `C` comes only from the critical-line moment and is independent of `sigma`; degeneration
as `sigma → 1` is confined to the explicit moving-right factor. -/
theorem exists_inghamGabrielPoleClearedError_uniformCenterMoment_le_explicit :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {sigma : ℝ}, 501 / 1001 ≤ sigma → sigma < 1 →
      ∀ {X : ℕ}, 4 ≤ X →
        inghamUniformGabrielCenterMoment sigma
          (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) ≤
            C *
              (1 + inghamMovingRightTranslatedExplicitConstant
                ((9 / 100 : ℝ) * (1 - sigma))) *
              (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
              (1 + Real.log (X : ℝ)) ^
                (2 * inghamUniformGabrielCriticalShare sigma) := by
  obtain ⟨CL, hCL, hleft⟩ :=
    exists_inghamGabrielPoleClearedError_critical_translatedMoment_le_polylog
  refine ⟨CL + 1, by positivity, ?_⟩
  intro sigma hsigma0 hsigma1 X hX
  let delta : ℝ := (9 / 100 : ℝ) * (1 - sigma)
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdelta1 : delta ≤ 1 := by
    dsimp only [delta]
    nlinarith
  let CR : ℝ := inghamMovingRightTranslatedExplicitConstant delta
  have hCR : 0 ≤ CR := by
    dsimp only [CR, inghamMovingRightTranslatedExplicitConstant]
    positivity
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  let Log : ℝ := 1 + Real.log (X : ℝ)
  have hLog1 : 1 ≤ Log := by
    dsimp only [Log]
    linarith [Real.log_nonneg hXone]
  have hLog0 : 0 ≤ Log := hLog1.trans' (by norm_num)
  let Left : ℝ := (CL + 1) * (X : ℝ) * Log ^ 2
  let Right : ℝ := (CR + 1) * (X : ℝ) ^ (-delta)
  have hLeft : 0 < Left := by dsimp only [Left]; positivity
  have hRight : 0 < Right := by dsimp only [Right]; positivity
  have hinterp :=
    inghamUniformGabrielCenterMoment_le_shares_of_vertical_continuous
      hsigma0 hsigma1le
      (fun z hz => continuous_poleCleared_vertical_of_half_le X hz)
      (X : ℝ) Left Right hLeft hRight
      (diffContOnCl_inghamUniformGabrielScalarFamily_poleCleared
        hsigma0 hsigma1le X (kappa := 1) (T := (X : ℝ)) hXpos.le)
      (bddAbove_inghamUniformGabrielScalarFamily_poleCleared
        hsigma0 hsigma1le X (kappa := 1) (T := (X : ℝ)) (by norm_num) hXpos)
      (fun z hz => by
        have h := hleft hX z hz
        dsimp only [Left, Log]
        exact h.trans (by
          gcongr
          linarith))
      (fun z hz => by
        have h :=
          inghamGabrielPoleClearedError_movingRight_translatedMoment_le_explicit
            hdelta hdelta1 hX z (by
              dsimp only [delta]
              rw [hz]
              unfold inghamUniformGabrielRightEdge
              ring)
        dsimp only [Right, CR]
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith)
          (Real.rpow_nonneg hXpos.le _)))
  let cs : ℝ := inghamUniformGabrielCriticalShare sigma
  let rs : ℝ := inghamUniformGabrielRightShare sigma
  let E : ℝ := inghamUniformGabrielConservativeExponent sigma
  have hshape :
      Left ^ cs * Right ^ rs =
        ((CL + 1) ^ cs * (CR + 1) ^ rs) *
          (X : ℝ) ^ E * Log ^ (2 * cs) := by
    dsimp only [Left, Right, cs, rs, E]
    rw [Real.mul_rpow (mul_nonneg (by positivity) hXpos.le)
        (pow_nonneg hLog0 2),
      Real.mul_rpow (by positivity) hXpos.le,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hXpos.le _),
      ← Real.rpow_natCast Log 2, ← Real.rpow_mul hLog0,
      ← Real.rpow_mul hXpos.le]
    calc
      ((CL + 1) ^ inghamUniformGabrielCriticalShare sigma *
            (X : ℝ) ^ inghamUniformGabrielCriticalShare sigma *
            Log ^ ((2 : ℝ) * inghamUniformGabrielCriticalShare sigma)) *
          ((CR + 1) ^ inghamUniformGabrielRightShare sigma *
            (X : ℝ) ^
              (-delta * inghamUniformGabrielRightShare sigma)) =
        ((CL + 1) ^ inghamUniformGabrielCriticalShare sigma *
            (CR + 1) ^ inghamUniformGabrielRightShare sigma) *
          ((X : ℝ) ^ inghamUniformGabrielCriticalShare sigma *
            (X : ℝ) ^
              (-delta * inghamUniformGabrielRightShare sigma)) *
          Log ^ ((2 : ℝ) * inghamUniformGabrielCriticalShare sigma) := by ring
      _ = ((CL + 1) ^ inghamUniformGabrielCriticalShare sigma *
            (CR + 1) ^ inghamUniformGabrielRightShare sigma) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          Log ^ (2 * inghamUniformGabrielCriticalShare sigma) := by
        rw [← Real.rpow_add hXpos]
        congr 2
        unfold inghamUniformGabrielConservativeExponent
          inghamUniformGabrielConservativeRightMomentExponent
        dsimp only [delta]
        ring
  have hcs1 : cs ≤ 1 := by
    exact inghamUniformGabrielCriticalShare_le_one hsigma0 hsigma1le
  have hrs1 : rs ≤ 1 := by
    exact inghamUniformGabrielRightShare_le_one hsigma1le
  have hcoeff :
      (CL + 1) ^ cs * (CR + 1) ^ rs ≤ (CL + 1) * (CR + 1) := by
    exact mul_le_mul
      (Real.rpow_le_self_of_one_le (by linarith) hcs1)
      (Real.rpow_le_self_of_one_le (by linarith) hrs1)
      (Real.rpow_nonneg (by positivity) _)
      (by positivity)
  have htail0 : 0 ≤ (X : ℝ) ^ E * Log ^ (2 * cs) :=
    mul_nonneg (Real.rpow_nonneg hXpos.le _) (Real.rpow_nonneg hLog0 _)
  calc
    inghamUniformGabrielCenterMoment sigma
        (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) ≤
      Left ^ cs * Right ^ rs := hinterp
    _ = ((CL + 1) ^ cs * (CR + 1) ^ rs) *
          (X : ℝ) ^ E * Log ^ (2 * cs) := hshape
    _ = ((CL + 1) ^ cs * (CR + 1) ^ rs) *
          ((X : ℝ) ^ E * Log ^ (2 * cs)) := by ring
    _ ≤ ((CL + 1) * (CR + 1)) *
          ((X : ℝ) ^ E * Log ^ (2 * cs)) :=
      mul_le_mul_of_nonneg_right hcoeff htail0
    _ = (CL + 1) * (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by
      dsimp only [CR, delta, E, cs, Log]
      ring

end

/-! ### From `InghamUniformGabrielRawCenterMomentExplicit` -/

section
open Complex MeasureTheory Set

/-- Raw mollified error with a universal leading constant. Pole clearing costs at most the square of
the explicit center-to-pole ratio; all remaining degeneration is the explicit moving-right factor. -/
theorem exists_inghamRawError_uniformGabrielCenterMoment_le_explicit :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {sigma : ℝ}, 501 / 1001 ≤ sigma → sigma < 1 →
      ∀ {X : ℕ}, 4 ≤ X →
      (∫ t in Icc (-(X : ℝ)) (X : ℝ),
        ‖riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
          inghamMollifier X
            ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1‖ ^
              inghamUniformGabrielInteriorPower sigma) ≤
        C *
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
            (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by
  obtain ⟨C0, hC0, hcenter⟩ :=
    exists_inghamGabrielPoleClearedError_uniformCenterMoment_le_explicit
  refine ⟨C0, hC0, ?_⟩
  intro sigma hsigma0 hsigma1 X hX
  have hc0 : 0 < inghamUniformGabrielCenter sigma :=
    lt_of_lt_of_le (by norm_num) (inghamUniformGabrielCenter_ge_half hsigma0)
  have hc1 : inghamUniformGabrielCenter sigma < 1 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter1 : inghamUniformGabrielCenter sigma ≠ 1 := hc1.ne
  let A : ℝ :=
    (1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1
  have hgap : 0 < 1 - inghamUniformGabrielCenter sigma := sub_pos.mpr hc1
  have hA1 : 1 ≤ A := by
    dsimp only [A]
    exact one_le_mul_of_one_le_of_one_le
      (by
        have hinv : 0 ≤ 1 / (1 - inghamUniformGabrielCenter sigma) := by
          positivity
        linarith)
      (Real.one_le_exp (by norm_num))
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA1
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
  have hApow :
      A ^ inghamUniformGabrielInteriorPower sigma ≤ A ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_le hA1
        (inghamUniformGabrielInteriorPower_le_two hsigma1le))
  calc
    (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) ≤
        A ^ inghamUniformGabrielInteriorPower sigma *
          inghamUniformGabrielCenterMoment sigma
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) := hintegral
    _ ≤ A ^ (2 : ℕ) *
          inghamUniformGabrielCenterMoment sigma
            (inghamGabrielPoleClearedError X 1 (X : ℝ)) (X : ℝ) :=
      mul_le_mul_of_nonneg_right hApow
        (inghamUniformGabrielCenterMoment_nonneg _ _ _)
    _ ≤ A ^ (2 : ℕ) *
        (C0 *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma)) :=
      mul_le_mul_of_nonneg_left (hcenter hsigma0 hsigma1 hX) (sq_nonneg A)
    _ = C0 * A ^ (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by ring

end

/-! ### From `InghamUniformDetectorCenterLogMomentExplicit` -/

section
open Complex MeasureTheory Set

/-- Uniform-constant logarithmic detector bound on every vertical subinterval. -/
theorem exists_intervalIntegral_log_norm_inghamClassicalDetector_uniformCenter_le_explicit :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {sigma : ℝ}, 501 / 1001 ≤ sigma → sigma < 1 →
      ∀ {X : ℕ}, 4 ≤ X →
      ∀ {T₁ T₂ : ℝ}, -(X : ℝ) ≤ T₁ → T₁ ≤ T₂ → T₂ ≤ (X : ℝ) →
        (∫ t in T₁..T₂,
          Real.log ‖1 -
            (riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
              inghamMollifier X
                ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1) ^ 2‖) ≤
          C *
            ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
              (2 : ℕ) *
            (1 + inghamMovingRightTranslatedExplicitConstant
              ((9 / 100 : ℝ) * (1 - sigma))) *
            (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) := by
  obtain ⟨C0, hC0, hraw⟩ :=
    exists_inghamRawError_uniformGabrielCenterMoment_le_explicit
  refine ⟨2 * C0, by positivity, ?_⟩
  intro sigma hsigma0 hsigma1 X hX T₁ T₂ hlow hT hhigh
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hcenter1 : inghamUniformGabrielCenter sigma ≠ 1 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  let raw : ℝ → ℝ := fun t =>
    ‖riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X
        ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1‖ ^
          inghamUniformGabrielInteriorPower sigma
  let detector : ℝ → ℂ := fun t =>
    1 - (riemannZeta ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) *
      inghamMollifier X
        ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I) - 1) ^ 2
  have hrawCont : Continuous raw := by
    dsimp only [raw]
    exact (continuous_inghamRawError_uniformGabrielCenter
      sigma X hcenter1).norm.rpow_const
        (fun _ => Or.inr
          (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1le).le)
  have hlogInt : IntervalIntegrable (fun t => Real.log ‖detector t‖) volume T₁ T₂ := by
    have hmer : MeromorphicOn detector (uIcc T₁ T₂) := by
      intro t _
      exact (analyticOnNhd_inghamClassicalDetector_uniformCenter
        sigma X hcenter1 t (mem_univ t)).meromorphicAt
    exact hmer.intervalIntegrable_log_norm
  have hmajorInt : IntervalIntegrable (fun t => 2 * raw t) volume T₁ T₂ :=
    (continuous_const.mul hrawCont).intervalIntegrable _ _
  have hpoint : ∀ t ∈ Icc T₁ T₂,
      Real.log ‖detector t‖ ≤ 2 * raw t := by
    intro t _
    exact log_norm_one_sub_sq_le_two_mul_norm_rpow _
      (le_trans (by norm_num : (1 : ℝ) ≤ 4 / 3)
        (four_thirds_le_inghamUniformGabrielInteriorPower hsigma0 hsigma1le))
      (inghamUniformGabrielInteriorPower_le_two hsigma1le)
  have hlogMajor :
      (∫ t in T₁..T₂, Real.log ‖detector t‖) ≤
        ∫ t in T₁..T₂, 2 * raw t :=
    intervalIntegral.integral_mono_on hT hlogInt hmajorInt hpoint
  have hrawFullInt : IntervalIntegrable raw volume (-(X : ℝ)) (X : ℝ) :=
    hrawCont.intervalIntegrable _ _
  have hrawMono :
      (∫ t in T₁..T₂, raw t) ≤ ∫ t in (-(X : ℝ))..(X : ℝ), raw t := by
    exact intervalIntegral.integral_mono_interval hlow hT hhigh
      (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)
      hrawFullInt
  have hrawFullEq :
      (∫ t in (-(X : ℝ))..(X : ℝ), raw t) =
        ∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t := by
    have hXX : -(X : ℝ) ≤ (X : ℝ) := neg_le_self (Nat.cast_nonneg X)
    rw [intervalIntegral.integral_of_le hXX,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  calc
    (∫ t in T₁..T₂, Real.log ‖detector t‖) ≤
        ∫ t in T₁..T₂, 2 * raw t := hlogMajor
    _ = 2 * (∫ t in T₁..T₂, raw t) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ 2 * (∫ t in (-(X : ℝ))..(X : ℝ), raw t) :=
      mul_le_mul_of_nonneg_left hrawMono (by norm_num)
    _ = 2 * (∫ t in Icc (-(X : ℝ)) (X : ℝ), raw t) := by rw [hrawFullEq]
    _ ≤ 2 *
        (C0 *
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
            (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma)) :=
      mul_le_mul_of_nonneg_left (hraw hsigma0 hsigma1 hX) (by norm_num)
    _ = (2 * C0) *
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
            (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by ring

end

/-! ### From `InghamUniformDetectorHorizontalBoundaryGlobal` -/

section
open Complex Filter Metric Set ArithmeticFunction Finset

/-- A single horizontal-boundary constant works for every moving center. The old pointwise proof
only depends on the center through a width `W = 4 - c`, and `0 ≤ W ≤ 4` on the whole parameter
range. -/
theorem exists_inghamClassicalHorizontalBoundary_global_polylog :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {sigma : ℝ}, 501 / 1001 ≤ sigma → sigma ≤ 1 →
      ∀ {X : ℕ}, 10 ≤ X →
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
      ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
        (∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
          inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
        (∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
          inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
        inghamClassicalHorizontalBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂ ≤
          K * (1 + Real.log X) ^ (2 : ℕ) := by
  obtain ⟨K0, hK0, hselected⟩ :=
    exists_inghamDetector_two_horizontal_edges_critical_polylog
  let B : ℝ := K0 + 2
  let K : ℝ := 32 * B
  have hB : 0 ≤ B := by dsimp only [B]; linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro sigma hsigma0 hsigma1 X hX
  have hcenter699 : (1 / 2 : ℝ) ≤ inghamUniformGabrielCenter sigma := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter4 : inghamUniformGabrielCenter sigma ≤ 4 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  obtain ⟨T₁, hT₁, T₂, hT₂, hbottom, htop⟩ := hselected hX
  let u : ℝ := 1 + Real.log X
  let W : ℝ := 4 - inghamUniformGabrielCenter sigma
  have hW : 0 ≤ W := by dsimp only [W]; linarith
  have hW4 : W ≤ 4 := by
    dsimp only [W]
    unfold inghamUniformGabrielCenter
    nlinarith
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hu1 : 1 ≤ u := by
    dsimp only [u]
    linarith [Real.log_nonneg hX1]
  have huSq0 : 0 ≤ u ^ (2 : ℕ) := sq_nonneg u
  have huSq1 : 1 ≤ u ^ (2 : ℕ) := by nlinarith
  have hT₁abs : 1 ≤ |T₁| := by
    rw [abs_of_nonpos (by linarith [hT₁.2, hXR])]
    linarith [hT₁.2]
  have hT₂abs : 1 ≤ |T₂| := by
    rw [abs_of_nonneg (by linarith [hT₂.1, hXR])]
    linarith [hT₂.1]
  have hclassical₁ : ∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
      ‖logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₁ : ℂ) * I)‖ ≤
        B * u ^ (2 : ℕ) := by
    intro x hx
    have hx' : x ∈ Icc (1 / 2 : ℝ) 4 :=
      ⟨hcenter699.trans hx.1, hx.2⟩
    obtain ⟨hH, hdet⟩ := hbottom x hx'
    let s : ℂ := (x : ℂ) + (T₁ : ℂ) * I
    have hsIm : |s.im| = |T₁| := by simp [s]
    have hs1 : s ≠ 1 := by
      intro hs
      have himEq := congrArg Complex.im hs
      have hTzero : T₁ = 0 := by simpa [s] using himEq
      rw [hTzero, abs_zero] at hT₁abs
      linarith
    have htransfer := norm_logDeriv_inghamClassicalDetector_le
      X hs1 (by simpa only [s] using hH) (by rw [hsIm]; exact hT₁abs)
    have hdet' : ‖logDeriv (inghamDetector X) s‖ ≤ K0 * u ^ (2 : ℕ) := by
      simpa only [s, u] using hdet
    calc
      ‖logDeriv (inghamClassicalDetector X) s‖ ≤
          ‖logDeriv (inghamDetector X) s‖ + 2 := htransfer
      _ ≤ K0 * u ^ (2 : ℕ) + 2 := add_le_add hdet' (le_refl 2)
      _ ≤ B * u ^ (2 : ℕ) := by dsimp only [B]; nlinarith
  have hclassical₂ : ∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
      ‖logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₂ : ℂ) * I)‖ ≤
        B * u ^ (2 : ℕ) := by
    intro x hx
    have hx' : x ∈ Icc (1 / 2 : ℝ) 4 :=
      ⟨hcenter699.trans hx.1, hx.2⟩
    obtain ⟨hH, hdet⟩ := htop x hx'
    let s : ℂ := (x : ℂ) + (T₂ : ℂ) * I
    have hsIm : |s.im| = |T₂| := by simp [s]
    have hs1 : s ≠ 1 := by
      intro hs
      have himEq := congrArg Complex.im hs
      have hTzero : T₂ = 0 := by simpa [s] using himEq
      rw [hTzero, abs_zero] at hT₂abs
      linarith
    have htransfer := norm_logDeriv_inghamClassicalDetector_le
      X hs1 (by simpa only [s] using hH) (by rw [hsIm]; exact hT₂abs)
    have hdet' : ‖logDeriv (inghamDetector X) s‖ ≤ K0 * u ^ (2 : ℕ) := by
      simpa only [s, u] using hdet
    calc
      ‖logDeriv (inghamClassicalDetector X) s‖ ≤
          ‖logDeriv (inghamDetector X) s‖ + 2 := htransfer
      _ ≤ K0 * u ^ (2 : ℕ) + 2 := add_le_add hdet' (le_refl 2)
      _ ≤ B * u ^ (2 : ℕ) := by dsimp only [B]; nlinarith
  let M : ℝ := W * (B * u ^ (2 : ℕ))
  have hpoint₁ : ∀ x ∈ Set.uIoc (inghamUniformGabrielCenter sigma) 4,
      ‖(x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₁ : ℂ) * I)).im‖ ≤ M := by
    intro x hx
    rw [uIoc_of_le hcenter4] at hx
    have hxIcc : x ∈ Icc (inghamUniformGabrielCenter sigma) 4 := ⟨hx.1.le, hx.2⟩
    have himle := Complex.abs_im_le_norm
      (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₁ : ℂ) * I))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxIcc.1)]
    calc
      (x - inghamUniformGabrielCenter sigma) *
          |(logDeriv (inghamClassicalDetector X)
            ((x : ℂ) + (T₁ : ℂ) * I)).im| ≤
          (x - inghamUniformGabrielCenter sigma) *
            ‖logDeriv (inghamClassicalDetector X)
              ((x : ℂ) + (T₁ : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_left himle (sub_nonneg.mpr hxIcc.1)
      _ ≤ W * (B * u ^ (2 : ℕ)) := by
        apply mul_le_mul (by dsimp only [W]; linarith [hxIcc.2])
          (hclassical₁ x hxIcc) (norm_nonneg _) hW
      _ = M := rfl
  have hpoint₂ : ∀ x ∈ Set.uIoc (inghamUniformGabrielCenter sigma) 4,
      ‖(x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₂ : ℂ) * I)).im‖ ≤ M := by
    intro x hx
    rw [uIoc_of_le hcenter4] at hx
    have hxIcc : x ∈ Icc (inghamUniformGabrielCenter sigma) 4 := ⟨hx.1.le, hx.2⟩
    have himle := Complex.abs_im_le_norm
      (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₂ : ℂ) * I))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxIcc.1)]
    calc
      (x - inghamUniformGabrielCenter sigma) *
          |(logDeriv (inghamClassicalDetector X)
            ((x : ℂ) + (T₂ : ℂ) * I)).im| ≤
          (x - inghamUniformGabrielCenter sigma) *
            ‖logDeriv (inghamClassicalDetector X)
              ((x : ℂ) + (T₂ : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_left himle (sub_nonneg.mpr hxIcc.1)
      _ ≤ W * (B * u ^ (2 : ℕ)) := by
        apply mul_le_mul (by dsimp only [W]; linarith [hxIcc.2])
          (hclassical₂ x hxIcc) (norm_nonneg _) hW
      _ = M := rfl
  have hint₁ : ‖∫ x in (inghamUniformGabrielCenter sigma)..4,
      (x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₁ : ℂ) * I)).im‖ ≤ M * W := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint₁
    rw [abs_of_nonneg hW] at h
    simpa only [W] using h
  have hint₂ : ‖∫ x in (inghamUniformGabrielCenter sigma)..4,
      (x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₂ : ℂ) * I)).im‖ ≤ M * W := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint₂
    rw [abs_of_nonneg hW] at h
    simpa only [W] using h
  have hzero₁ : ∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
      inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    exact (hbottom x ⟨hcenter699.trans hx.1, hx.2⟩).1
  have hzero₂ : ∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
      inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    exact (htop x ⟨hcenter699.trans hx.1, hx.2⟩).1
  refine ⟨T₁, hT₁, T₂, hT₂, hzero₁, hzero₂, ?_⟩
  dsimp only [inghamClassicalHorizontalBoundary]
  let I₁ : ℝ := ∫ x in (inghamUniformGabrielCenter sigma)..4,
      (x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₁ : ℂ) * I)).im
  let I₂ : ℝ := ∫ x in (inghamUniformGabrielCenter sigma)..4,
      (x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₂ : ℂ) * I)).im
  change I₁ - I₂ ≤ K * u ^ (2 : ℕ)
  have hdiff : I₁ - I₂ ≤ ‖I₁ - I₂‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have htri : ‖I₁ - I₂‖ ≤ ‖I₁‖ + ‖I₂‖ := norm_sub_le _ _
  have hI₁ : ‖I₁‖ ≤ M * W := by simpa only [I₁] using hint₁
  have hI₂ : ‖I₂‖ ≤ M * W := by simpa only [I₂] using hint₂
  have hWsq : W ^ (2 : ℕ) ≤ 16 := by
    nlinarith [mul_self_le_mul_self hW hW4]
  calc
    I₁ - I₂ ≤ ‖I₁ - I₂‖ := hdiff
    _ ≤ ‖I₁‖ + ‖I₂‖ := htri
    _ ≤ M * W + M * W := add_le_add hI₁ hI₂
    _ = 2 * W ^ (2 : ℕ) * B * u ^ (2 : ℕ) := by dsimp only [M]; ring
    _ ≤ 2 * 16 * B * u ^ (2 : ℕ) := by gcongr
    _ = K * u ^ (2 : ℕ) := by dsimp only [K]; ring

end

/-! ### From `InghamUniformDetectorDensityExplicit` -/

section
open Complex Filter Metric Set ArithmeticFunction Finset

/-- Weighted zeta-zero mass with one universal leading constant. All counting-line degeneration is
visible in the squared pole-recovery factor and explicit moving-right factor. -/
theorem exists_eventually_zetaZeroMass_le_uniformGabrielExplicit :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ X : ℕ in Filter.atTop,
      ∀ {sigma : ℝ}, 501 / 1001 ≤ sigma → sigma < 1 →
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
        ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamUniformGabrielCenter sigma : ℂ) + (T₁ : ℂ) * I)
                  ((4 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamUniformGabrielCenter sigma)) ≤
            K * (1 +
                ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
                    (2 : ℕ) *
                  (1 + inghamMovingRightTranslatedExplicitConstant
                    ((9 / 100 : ℝ) * (1 - sigma))) *
                  (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
                  (1 + Real.log (X : ℝ)) ^
                    (2 * inghamUniformGabrielCriticalShare sigma) +
                (1 + Real.log (X : ℝ)) ^ 2) := by
  obtain ⟨Kₕ, hKₕ, hhorizontal⟩ :=
    exists_inghamClassicalHorizontalBoundary_global_polylog
  obtain ⟨C, hC, hcenter⟩ :=
    exists_intervalIntegral_log_norm_inghamClassicalDetector_uniformCenter_le_explicit
  let K : ℝ := C + Kₕ + 2 + 4 * Real.pi
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_inghamDetector_ne_zero_on_rightEdge
      (beta := 4) (by norm_num), eventually_ge_atTop (10 : ℕ)] with X hright hX
  intro sigma hsigma0 hsigma1
  have hsigma1le : sigma ≤ 1 := hsigma1.le
  have hcenter699 : (1 / 2 : ℝ) ≤ inghamUniformGabrielCenter sigma := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter0 : 0 ≤ inghamUniformGabrielCenter sigma := by
    linarith
  have hcenter4 : inghamUniformGabrielCenter sigma ≤ 4 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter4lt : inghamUniformGabrielCenter sigma < 4 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter1 : inghamUniformGabrielCenter sigma < 1 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  let P : ℝ := 4 * Real.pi * (1 - inghamUniformGabrielCenter sigma)
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hPmax : P ≤ 4 * Real.pi := by
    dsimp only [P]
    calc
      4 * Real.pi * (1 - inghamUniformGabrielCenter sigma) ≤
          4 * Real.pi * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * Real.pi := by ring
  obtain ⟨T₁, hT₁, T₂, hT₂, hzero₁, hzero₂, hhorizontalX⟩ :=
    hhorizontal hsigma0 hsigma1le hX
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hT₁neg : T₁ < 0 := by linarith [hT₁.2]
  have hT₂pos : 0 < T₂ := by linarith [hT₂.1]
  have hT : T₁ < T₂ := hT₁neg.trans hT₂pos
  have hbot : ∀ x ∈ Set.uIcc (inghamUniformGabrielCenter sigma) 4,
      inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hcenter4] at hx
    exact hzero₁ x hx
  have htop : ∀ x ∈ Set.uIcc (inghamUniformGabrielCenter sigma) 4,
      inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hcenter4] at hx
    exact hzero₂ x hx
  have hright' : ∀ t ∈ Set.uIcc T₁ T₂,
      inghamDetector X ((4 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t _
    exact hright t
  have hmass0 := two_pi_mul_zetaZeroMass_le_inghamLittlewoodBoundary X
    (c := inghamUniformGabrielCenter sigma) (d := 4) (T₁ := T₁) (T₂ := T₂)
    hcenter4lt hT hbot htop hright'
  have hgauge := inghamLittlewoodBoundary_eq_classical_add_poleCharge X
    (c := inghamUniformGabrielCenter sigma) (d := 4) (T₁ := T₁) (T₂ := T₂)
    hcenter1 (by norm_num)
    hT₁neg hT₂pos hbot htop hright'
  rw [hgauge] at hmass0
  have hboundary := inghamClassicalLittlewoodBoundary_four_le
    (show 1 ≤ X by omega) (c := inghamUniformGabrielCenter sigma) (T₁ := T₁) (T₂ := T₂)
    hcenter4 hT.le
  have hleft := hcenter hsigma0 hsigma1 (show 4 ≤ X by omega)
    (le_of_lt hT₁.1) hT.le (by linarith [hT₂.2])
  have hleft' :
      (∫ t in T₁..T₂,
        Real.log ‖inghamClassicalDetector X
          ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖) ≤
        C *
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
            (2 : ℕ) *
          (1 + inghamMovingRightTranslatedExplicitConstant
            ((9 / 100 : ℝ) * (1 - sigma))) *
          (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
          (1 + Real.log (X : ℝ)) ^
            (2 * inghamUniformGabrielCriticalShare sigma) := by
    simpa only [inghamClassicalDetector] using hleft
  have hlen : T₂ - T₁ ≤ 2 * (X : ℝ) := by
    linarith [hT₁.1, hT₂.2]
  have hverticalFixed := farRightFour_verticalLoss_le_one
    (show 4 ≤ X by omega) hT.le hlen
  have hinner0 : 0 ≤ (T₂ - T₁) *
      (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)) := by
    positivity
  have hfirst0 : 0 ≤ (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) := by
    have : 0 ≤ T₂ - T₁ := by linarith
    positivity
  have hvertical :
      (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
        (4 - inghamUniformGabrielCenter sigma) * ((T₂ - T₁) *
          (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) ≤ 2 := by
    have hwidth : 4 - inghamUniformGabrielCenter sigma ≤ 2 * (4 - inghamFixedGabrielSigma) := by
      unfold inghamFixedGabrielSigma
      linarith
    calc
      _ ≤ 2 * ((T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
          (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
            (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)))) := by
        have := mul_le_mul_of_nonneg_right hwidth hinner0
        nlinarith
      _ ≤ 2 * 1 := by linarith [hverticalFixed]
      _ = 2 := by ring
  have hdecomp :
      2 * Real.pi *
            (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                ((inghamUniformGabrielCenter sigma : ℂ) + (T₁ : ℂ) * I)
                ((4 : ℂ) + (T₂ : ℂ) * I),
              ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                (w.re - inghamUniformGabrielCenter sigma)) ≤
          (∫ t in T₁..T₂,
            Real.log ‖inghamClassicalDetector X
              ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖) +
          ((T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
            (4 - inghamUniformGabrielCenter sigma) * ((T₂ - T₁) *
              (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)))) +
          inghamClassicalHorizontalBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂ + P := by
    calc
      _ ≤ inghamClassicalLittlewoodBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂ +
          4 * Real.pi * (1 - inghamUniformGabrielCenter sigma) := hmass0
      _ ≤ ((∫ t in T₁..T₂,
              Real.log ‖inghamClassicalDetector X
                ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖) +
            (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
            (4 - inghamUniformGabrielCenter sigma) * ((T₂ - T₁) *
              (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) +
            inghamClassicalHorizontalBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂) +
          4 * Real.pi * (1 - inghamUniformGabrielCenter sigma) :=
        add_le_add hboundary (le_refl _)
      _ = _ := by dsimp only [P]; ring
  let Q : ℝ :=
    ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
        (2 : ℕ) *
      (1 + inghamMovingRightTranslatedExplicitConstant
        ((9 / 100 : ℝ) * (1 - sigma)))
  let A : ℝ := Q *
    (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
    (1 + Real.log (X : ℝ)) ^ (2 * inghamUniformGabrielCriticalShare sigma)
  let B : ℝ := (1 + Real.log (X : ℝ)) ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A, Q, inghamMovingRightTranslatedExplicitConstant]
    positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hCK : C ≤ K := by dsimp only [K]; linarith [Real.pi_pos]
  have hHK : Kₕ ≤ K := by dsimp only [K]; linarith [Real.pi_pos]
  have hPK : 2 + P ≤ K := by dsimp only [K]; linarith
  refine ⟨T₁, hT₁, T₂, hT₂, hdecomp.trans ?_⟩
  calc
    (∫ t in T₁..T₂,
          Real.log ‖inghamClassicalDetector X
            ((inghamUniformGabrielCenter sigma : ℂ) + (t : ℂ) * I)‖) +
        ((T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
          (4 - inghamUniformGabrielCenter sigma) * ((T₂ - T₁) *
            (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)))) +
        inghamClassicalHorizontalBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂ + P ≤
      C * A + 2 + Kₕ * B + P := by
        dsimp only [A, Q, B]
        linarith
    _ = C * A + (2 + P) + Kₕ * B := by ring
    _ ≤ K * A + K + K * B :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hCK hA) hPK)
        (mul_le_mul_of_nonneg_right hHK hB)
    _ = K * (1 + A + B) := by ring
    _ = K * (1 +
          ((1 + 1 / (1 - inghamUniformGabrielCenter sigma)) * Real.exp 1) ^
              (2 : ℕ) *
            (1 + inghamMovingRightTranslatedExplicitConstant
              ((9 / 100 : ℝ) * (1 - sigma))) *
            (X : ℝ) ^ inghamUniformGabrielConservativeExponent sigma *
            (1 + Real.log (X : ℝ)) ^
              (2 * inghamUniformGabrielCriticalShare sigma) +
          (1 + Real.log (X : ℝ)) ^ 2) := by rfl

end


end

end RHTower.Sieve.InghamNearHalf
