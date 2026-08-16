import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfArithmeticWeld
import GaloisForLFunctions.RHTower.RectangleCauchyFormulaOn

/-!
# Route T: exact polar residue on the synchronized negative-half contour

This module evaluates the pole current on the same selected finite rectangle used by the
coefficient-faithful von Mangoldt contour. Cauchy's formula gives the exact residue `2 * π * I`.
The left edge vanishes by the negative-half power of the normalized Mellin kernel, while the two
horizontal edges gain an additional reciprocal-height factor. Hence the selected right polar edge
converges unconditionally to the residue.
-/

open Complex Filter Set Topology MeasureTheory intervalIntegral

namespace RHTower.Sieve

noncomputable section

def routeTNormalizedPoleMellinBoundary
    (N H c d T : ℝ) : ℂ :=
  I • (∫ y : ℝ in (-T)..T,
        (((d : ℂ) + (y : ℂ) * I) - 1)⁻¹ *
          routeTNormalizedSmoothWindowMellin N H
            ((d : ℂ) + (y : ℂ) * I))
    - I • (∫ y : ℝ in (-T)..T,
        (((c : ℂ) + (y : ℂ) * I) - 1)⁻¹ *
          routeTNormalizedSmoothWindowMellin N H
            ((c : ℂ) + (y : ℂ) * I))
    - ((∫ x : ℝ in c..d,
        ((((x : ℂ) + ((T : ℝ) : ℂ) * I) - 1)⁻¹ *
          routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + ((T : ℝ) : ℂ) * I)))
      - ∫ x : ℝ in c..d,
        ((((x : ℂ) + ((-T : ℝ) : ℂ) * I) - 1)⁻¹ *
          routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + ((-T : ℝ) : ℂ) * I)))

theorem routeTNormalizedPoleMellinBoundary_eq_residue
    {N H c d T : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hc : c < 1) (hd : 1 < d) (hT : 0 < T) :
    routeTNormalizedPoleMellinBoundary N H c d T = 2 * Real.pi * I := by
  have hcauchy := RHTower.rectIntegral_cauchyFormula_analyticOnNhd
    (g := routeTNormalizedSmoothWindowMellin N H)
    (U := Set.univ) (p := 1)
    (z₁ := (c : ℂ) + ((-T : ℝ) : ℂ) * I)
    (z₂ := (d : ℂ) + ((T : ℝ) : ℂ) * I)
    (fun _ _ => Set.mem_univ _)
    (analyticOnNhd_routeTNormalizedSmoothWindowMellin_univ hN hH)
    (by simpa using hc) (by simpa using hd)
    (by simp; linarith) (by simp; linarith)
  rw [routeTNormalizedSmoothWindowMellin_one hN.le hH] at hcauchy
  simp [rectIntegral, routeTNormalizedPoleMellinBoundary,
    smul_eq_mul, mul_comm] at hcauchy ⊢
  linear_combination hcauchy

def inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge (X : ℕ) : ℂ :=
  ∫ t in (-inghamRouteTBufferedNegativeHalfHeight X)..
      inghamRouteTBufferedNegativeHalfHeight X,
    (((-1 / 2 : ℂ) + (t : ℂ) * I) - 1)⁻¹ *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((-1 / 2 : ℂ) + (t : ℂ) * I)

def inghamRouteTBufferedNegativeHalfPoleTopEdge (X : ℕ) : ℂ :=
  ∫ x : ℝ in (-1 / 2)..2,
    (((x : ℂ) + (inghamRouteTBufferedNegativeHalfHeight X : ℂ) * I) - 1)⁻¹ *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((x : ℂ) + (inghamRouteTBufferedNegativeHalfHeight X : ℂ) * I)

def inghamRouteTBufferedNegativeHalfPoleBottomEdge (X : ℕ) : ℂ :=
  ∫ x : ℝ in (-1 / 2)..2,
    (((x : ℂ) + ((-inghamRouteTBufferedNegativeHalfHeight X : ℝ) : ℂ) * I) - 1)⁻¹ *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((x : ℂ) + ((-inghamRouteTBufferedNegativeHalfHeight X : ℝ) : ℂ) * I)

theorem routeTBufferedNegativeHalfPoleBoundary_eq_residue
    {X : ℕ} (hX : 12 ≤ X) :
    I • inghamRouteTBufferedSelectedTwoPoleEdge X -
        I • inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge X -
        (inghamRouteTBufferedNegativeHalfPoleTopEdge X -
          inghamRouteTBufferedNegativeHalfPoleBottomEdge X) =
      2 * Real.pi * I := by
  have hspec := inghamRouteTBufferedNegativeHalfHeight_spec hX
  have hres := routeTNormalizedPoleMellinBoundary_eq_residue
    (N := inghamRouteTMellinPhysicalCenter X)
    (H := inghamRouteTMellinBufferedPhysicalWidth X)
    (c := -1 / 2) (d := 2)
    (T := inghamRouteTBufferedNegativeHalfHeight X)
    (inghamRouteTMellinPhysicalCenter_pos (show 1 ≤ X by omega))
    (inghamRouteTMellinBufferedPhysicalWidth_pos (show 1 ≤ X by omega))
    (by norm_num) (by norm_num)
    (by
      have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
      linarith [hspec.1.1])
  simpa [routeTNormalizedPoleMellinBoundary,
    inghamRouteTBufferedSelectedTwoPoleEdge,
    inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge,
    inghamRouteTBufferedNegativeHalfPoleTopEdge,
    inghamRouteTBufferedNegativeHalfPoleBottomEdge] using hres

theorem norm_inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge_le
    {X : ℕ} (hX : 12 ≤ X) :
    ‖inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge X‖ ≤
      2 * (X : ℝ) *
        inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ)) := by
  let T : ℝ := inghamRouteTBufferedNegativeHalfHeight X
  let N : ℝ := inghamRouteTMellinPhysicalCenter X
  let H : ℝ := inghamRouteTMellinBufferedPhysicalWidth X
  have hX1 : 1 ≤ X := by omega
  have hN : 0 < N := inghamRouteTMellinPhysicalCenter_pos hX1
  have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  have hspec := inghamRouteTBufferedNegativeHalfHeight_spec hX
  have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
  have hTpos : 0 < T := by dsimp only [T]; linarith [hspec.1.1]
  have hTX : T ≤ (X : ℝ) := by dsimp only [T]; linarith [hspec.1.2]
  have hpoint : ∀ t ∈ uIoc (-T) T,
      ‖(((-1 / 2 : ℂ) + (t : ℂ) * I) - 1)⁻¹ *
        routeTNormalizedSmoothWindowMellin N H
          ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        N ^ (-(3 / 2 : ℝ)) := by
    intro t ht
    have hden : (1 : ℝ) ≤ ‖(((-1 / 2 : ℂ) + (t : ℂ) * I) - 1)‖ := by
      calc
        (1 : ℝ) ≤ |Complex.re (((-1 / 2 : ℂ) + (t : ℂ) * I) - 1)| := by norm_num
        _ ≤ ‖(((-1 / 2 : ℂ) + (t : ℂ) * I) - 1)‖ :=
          Complex.abs_re_le_norm _
    have hinv : ‖(((-1 / 2 : ℂ) + (t : ℂ) * I) - 1)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (by linarith : 0 <
        ‖(((-1 / 2 : ℂ) + (t : ℂ) * I) - 1)‖)).2 hden
    have hk := norm_routeTNormalizedSmoothWindowMellin_le_left_rpow
      hN hH (s := (-1 / 2 : ℂ) + (t : ℂ) * I) (by norm_num)
    norm_num at hk
    rw [norm_mul]
    norm_num at hk ⊢
    rw [norm_inv] at hinv
    norm_num at hinv
    exact (mul_le_mul hinv hk (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge]
  change ‖∫ t in (-T)..T, _‖ ≤ _
  calc
    ‖∫ t in (-T)..T,
        (((-1 / 2 : ℂ) + (t : ℂ) * I) - 1)⁻¹ *
          routeTNormalizedSmoothWindowMellin N H
            ((-1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        N ^ (-(3 / 2 : ℝ)) * |T - -T| := hint
    _ = 2 * T * N ^ (-(3 / 2 : ℝ)) := by
      rw [abs_of_pos (by linarith : 0 < T - -T)]
      ring
    _ ≤ 2 * (X : ℝ) * N ^ (-(3 / 2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hN.le _)
    _ = _ := rfl

theorem tendsto_inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge_zero :
    Tendsto inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge atTop (nhds 0) := by
  have hcore : Tendsto (fun X : ℕ => (X : ℝ) ^ (-(1201 / 299 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1201 / 299)).comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun X : ℕ =>
      2 * (X : ℝ) ^ (-(1201 / 299 : ℝ))) atTop (nhds 0) := by
    simpa using hcore.const_mul 2
  have hnorm : Tendsto (fun X : ℕ =>
      ‖inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge X‖)
      atTop (nhds 0) := by
    refine squeeze_zero' (by filter_upwards with X; exact norm_nonneg _) ?_ hupper
    filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
    have hb := norm_inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge_le hX
    calc
      ‖inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge X‖ ≤
          2 * (X : ℝ) *
            inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ)) := hb
      _ = 2 * (X : ℝ) ^ (-(1201 / 299 : ℝ)) := by
        rw [← routeT_negative_half_compact_scale_eq (show 1 ≤ X by omega)]
        ring
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

theorem exists_routeT_negativeHalf_two_pole_horizontal_integrals_decay_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {X : ℕ}, 12 ≤ X →
      ‖inghamRouteTBufferedNegativeHalfPoleTopEdge X‖ ≤
          5 / (X : ℝ) *
            (B * (X : ℝ) ^ (-(196 / 299 : ℝ))) ∧
      ‖inghamRouteTBufferedNegativeHalfPoleBottomEdge X‖ ≤
          5 / (X : ℝ) *
            (B * (X : ℝ) ^ (-(196 / 299 : ℝ))) := by
  obtain ⟨C, hC, hkernel⟩ :=
    exists_bound_routeTNormalizedSmoothWindowMellin_horizontal
  let B : ℝ := C * 3 ^ (4001 : ℝ) * 2 ^ (4000 : ℝ)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro X hX
  let T : ℝ := inghamRouteTBufferedNegativeHalfHeight X
  let N : ℝ := inghamRouteTMellinPhysicalCenter X
  let H : ℝ := inghamRouteTMellinBufferedPhysicalWidth X
  have hX1 : 1 ≤ X := by omega
  have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by positivity
  have hN1 : 1 ≤ N := inghamRouteTMellinPhysicalCenter_one_le hX1
  have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  have hHN : H ≤ N := inghamRouteTMellinBufferedPhysicalWidth_le_center hX1
  have hspec := inghamRouteTBufferedNegativeHalfHeight_spec hX
  have hTI : T ∈ Ioo ((X : ℝ) - 3) ((X : ℝ) - 2) := hspec.1
  have hTpos : 0 < T := by linarith [hTI.1]
  have hT9 : 9 ≤ T := by linarith [hTI.1]
  have hhalfpos : 0 < (X : ℝ) / 2 := by positivity
  have hhalfT : (X : ℝ) / 2 ≤ T := by linarith [hTI.1]
  have hscale := routeT_negative_half_horizontal_kernel_scale_le hC hX hTI
  have hedge (eps : ℝ) (heps : eps = -1 ∨ eps = 1) :
      ‖∫ x : ℝ in (-1 / 2)..2,
        (((x : ℂ) + ((eps * T : ℝ) : ℂ) * I) - 1)⁻¹ *
          routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + ((eps * T : ℝ) : ℂ) * I)‖ ≤
        5 / (X : ℝ) *
          (B * (X : ℝ) ^ (-(196 / 299 : ℝ))) := by
    have hepsabs : |eps * T| = T := by
      rcases heps with rfl | rfl <;> simp [abs_of_pos hTpos]
    have ht9 : 9 ≤ |eps * T| := by rw [hepsabs]; exact hT9
    have hpoint : ∀ x ∈ uIoc (-1 / 2 : ℝ) 2,
        ‖(((x : ℂ) + ((eps * T : ℝ) : ℂ) * I) - 1)⁻¹ *
          routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + ((eps * T : ℝ) : ℂ) * I)‖ ≤
          2 / (X : ℝ) *
            (B * (X : ℝ) ^ (-(196 / 299 : ℝ))) := by
      intro x hx
      have hxI : x ∈ Icc (-1 / 2 : ℝ) 2 := by
        rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] at hx
        exact ⟨hx.1.le, hx.2⟩
      have hkraw := hkernel N H (eps * T) x hN1 hH hHN ht9 hxI
      rw [hepsabs] at hkraw
      have hk : ‖routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + ((eps * T : ℝ) : ℂ) * I)‖ ≤
          B * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
        exact hkraw.trans (by simpa only [B, N, H] using hscale)
      let s : ℂ := (x : ℂ) + ((eps * T : ℝ) : ℂ) * I
      have hden : T ≤ ‖s - 1‖ := by
        have him := Complex.abs_im_le_norm (s - 1)
        have hsIm : (s - 1).im = eps * T := by simp [s]
        rw [hsIm, hepsabs] at him
        exact him
      have hinv : ‖(s - 1)⁻¹‖ ≤ 2 / (X : ℝ) := by
        rw [norm_inv]
        calc
          ‖s - 1‖⁻¹ ≤ T⁻¹ := inv_anti₀ hTpos hden
          _ ≤ ((X : ℝ) / 2)⁻¹ := inv_anti₀ hhalfpos hhalfT
          _ = 2 / (X : ℝ) := by field_simp
      change ‖(s - 1)⁻¹ * routeTNormalizedSmoothWindowMellin N H s‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul hinv hk (norm_nonneg _)
        (by positivity : 0 ≤ 2 / (X : ℝ))
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    calc
      ‖∫ x : ℝ in (-1 / 2)..2,
        (((x : ℂ) + ((eps * T : ℝ) : ℂ) * I) - 1)⁻¹ *
          routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + ((eps * T : ℝ) : ℂ) * I)‖ ≤
          (2 / (X : ℝ) *
            (B * (X : ℝ) ^ (-(196 / 299 : ℝ)))) * |2 - (-1 / 2)| := hint
      _ = 5 / (X : ℝ) *
          (B * (X : ℝ) ^ (-(196 / 299 : ℝ))) := by
        norm_num
        ring
  constructor
  · have htop := hedge 1 (Or.inr rfl)
    simpa [inghamRouteTBufferedNegativeHalfPoleTopEdge, T, N, H] using htop
  · have hbot := hedge (-1) (Or.inl rfl)
    simpa [inghamRouteTBufferedNegativeHalfPoleBottomEdge, T, N, H] using hbot

theorem tendsto_inghamRouteTBufferedNegativeHalfPoleTopEdge_zero :
    Tendsto inghamRouteTBufferedNegativeHalfPoleTopEdge atTop (nhds 0) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_routeT_negativeHalf_two_pole_horizontal_integrals_decay_bound
  have hinv : Tendsto (fun X : ℕ => ((X : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun X : ℕ =>
      (X : ℝ) ^ (-(196 / 299 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 196 / 299)).comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun X : ℕ =>
      5 / (X : ℝ) * (B * (X : ℝ) ^ (-(196 / 299 : ℝ))))
      atTop (nhds 0) := by
    convert (hinv.const_mul 5).mul (hpow.const_mul B) using 1 <;> simp [div_eq_mul_inv]
  have hnorm : Tendsto (fun X : ℕ =>
      ‖inghamRouteTBufferedNegativeHalfPoleTopEdge X‖) atTop (nhds 0) := by
    refine squeeze_zero' (by filter_upwards with X; exact norm_nonneg _) ?_ hupper
    filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
    exact (hbound hX).1
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

theorem tendsto_inghamRouteTBufferedNegativeHalfPoleBottomEdge_zero :
    Tendsto inghamRouteTBufferedNegativeHalfPoleBottomEdge atTop (nhds 0) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_routeT_negativeHalf_two_pole_horizontal_integrals_decay_bound
  have hinv : Tendsto (fun X : ℕ => ((X : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun X : ℕ =>
      (X : ℝ) ^ (-(196 / 299 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 196 / 299)).comp
      tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun X : ℕ =>
      5 / (X : ℝ) * (B * (X : ℝ) ^ (-(196 / 299 : ℝ))))
      atTop (nhds 0) := by
    convert (hinv.const_mul 5).mul (hpow.const_mul B) using 1 <;> simp [div_eq_mul_inv]
  have hnorm : Tendsto (fun X : ℕ =>
      ‖inghamRouteTBufferedNegativeHalfPoleBottomEdge X‖) atTop (nhds 0) := by
    refine squeeze_zero' (by filter_upwards with X; exact norm_nonneg _) ?_ hupper
    filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
    exact (hbound hX).2
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

theorem routeTBufferedNegativeHalfPoleRight_sub_residue_eq_errors
    {X : ℕ} (hX : 12 ≤ X) :
    I • inghamRouteTBufferedSelectedTwoPoleEdge X - 2 * Real.pi * I =
      I • inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge X +
        inghamRouteTBufferedNegativeHalfPoleTopEdge X -
        inghamRouteTBufferedNegativeHalfPoleBottomEdge X := by
  have hboundary := routeTBufferedNegativeHalfPoleBoundary_eq_residue hX
  linear_combination hboundary

theorem tendsto_inghamRouteTBufferedSelectedTwoPoleEdge_residue :
    Tendsto (fun X : ℕ => I • inghamRouteTBufferedSelectedTwoPoleEdge X)
      atTop (nhds (2 * Real.pi * I)) := by
  have hleft : Tendsto (fun X : ℕ =>
      I • inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge X)
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (I : ℂ)) atTop (nhds I)).smul
        tendsto_inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge_zero
  have herrors : Tendsto (fun X : ℕ =>
      I • inghamRouteTBufferedSelectedNegativeHalfPoleLeftEdge X +
        inghamRouteTBufferedNegativeHalfPoleTopEdge X -
        inghamRouteTBufferedNegativeHalfPoleBottomEdge X)
      atTop (nhds 0) := by
    convert (hleft.add
      tendsto_inghamRouteTBufferedNegativeHalfPoleTopEdge_zero).sub
        tendsto_inghamRouteTBufferedNegativeHalfPoleBottomEdge_zero using 1 <;> simp
  have hdiff : Tendsto (fun X : ℕ =>
      I • inghamRouteTBufferedSelectedTwoPoleEdge X - 2 * Real.pi * I)
      atTop (nhds 0) := by
    exact Tendsto.congr' (by
      filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
      exact (routeTBufferedNegativeHalfPoleRight_sub_residue_eq_errors hX).symm) herrors
  convert hdiff.add_const (2 * Real.pi * I) using 1 <;> simp

end

end RHTower.Sieve
