import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfHorizontal
import GaloisForLFunctions.HTGeometry.WindowRpowIntegral

/-!
# Route T: decay of the synchronized negative-half contour edges

Arbitrary-order Mellin integration by parts at order `4000` combines with the selected
polylogarithmic zeta logarithmic-derivative bound. The exact scheduled power margin is
`X^(-196/299)`. A canonical symmetric height then makes both horizontal edges and the selected
`Re s = -1/2` edge tend to zero while preserving the exact residue identity.
-/

open Complex Filter Metric Set Finset Topology MeasureTheory Asymptotics intervalIntegral

namespace RHTower.Sieve

noncomputable section

theorem exists_bound_routeTNormalizedSmoothWindowMellin_horizontal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N H t x : ℝ,
      1 ≤ N → 0 < H → H ≤ N → 9 ≤ |t| →
      x ∈ Icc (-1 / 2 : ℝ) 2 →
      ‖routeTNormalizedSmoothWindowMellin N H
          ((x : ℂ) + (t : ℂ) * I)‖ ≤
        C * (3 * N) ^ (4001 : ℝ) / H ^ 4000 / |t| ^ 4000 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_bound_routeTNormalizedSmoothWindowMellin_line 4000
  refine ⟨C, hC, ?_⟩
  intro N H t x hN hH hHN ht hx
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have htpos : 0 < |t| := by linarith
  have hraw := hbound x N H t hNpos hH hHN (by norm_num)
    (by norm_num at hx ⊢; linarith [hx.1])
    htpos
  have hbase : 1 ≤ 3 * N := by nlinarith
  have hexp : x + (4000 : ℝ) - 1 ≤ 4001 := by linarith [hx.2]
  have hpow : (3 * N) ^ (x + (4000 : ℝ) - 1) ≤
      (3 * N) ^ (4001 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hnum : C * (3 * N) ^ (x + (4000 : ℝ) - 1) / H ^ 4000 ≤
      C * (3 * N) ^ (4001 : ℝ) / H ^ 4000 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hC) (by positivity)
  rw [le_div_iff₀ (pow_pos htpos 4000)]
  simpa only [mul_comm] using hraw.trans hnum

theorem routeT_negative_half_horizontal_exact_scale
    {C : ℝ} {X : ℕ} (hX : 1 ≤ X) :
    C * (3 * inghamRouteTMellinPhysicalCenter X) ^ (4001 : ℝ) /
          inghamRouteTMellinBufferedPhysicalWidth X ^ 4000 /
            (((X : ℝ) / 2) ^ 4000) =
      (C * 3 ^ (4001 : ℝ) * 2 ^ (4000 : ℝ)) *
        (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
  have hx : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  let a : ℝ := inghamRouteTPhysicalScaleExponent
  let b : ℝ := inghamRouteTMellinBufferedFrequencyExponent
  have hN : inghamRouteTMellinPhysicalCenter X = (X : ℝ) ^ a := rfl
  have hH : inghamRouteTMellinBufferedPhysicalWidth X = (X : ℝ) ^ (a - b) := by
    rw [inghamRouteTMellinBufferedPhysicalWidth, hN]
    change (X : ℝ) ^ a / (X : ℝ) ^ b = _
    rw [Real.rpow_sub hx]
  rw [hN, hH]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Real.rpow_nonneg hx.le a)]
  rw [← Real.rpow_mul hx.le a (4001 : ℝ),
    ← Real.rpow_mul_natCast hx.le (a - b) 4000,
    ← Real.rpow_natCast]
  rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ X) (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num only [Nat.cast_ofNat]
  rw [mul_div_assoc C
    (3 ^ (4001 : ℝ) * (X : ℝ) ^ (a * 4001))
    ((X : ℝ) ^ ((a - b) * 4000))]
  have hfirst :
      3 ^ (4001 : ℝ) * (X : ℝ) ^ (a * 4001) /
          (X : ℝ) ^ ((a - b) * 4000) =
        3 ^ (4001 : ℝ) *
          (X : ℝ) ^ (a * 4001 - (a - b) * 4000) := by
    rw [mul_div_assoc, ← Real.rpow_sub hx]
  rw [hfirst, div_div_eq_mul_div]
  rw [show C * (3 ^ (4001 : ℝ) *
        (X : ℝ) ^ (a * 4001 - (a - b) * 4000)) * 2 ^ (4000 : ℝ) /
          (X : ℝ) ^ (4000 : ℝ) =
      (C * 3 ^ (4001 : ℝ) * 2 ^ (4000 : ℝ)) *
        ((X : ℝ) ^ (a * 4001 - (a - b) * 4000) /
          (X : ℝ) ^ (4000 : ℝ)) by ring,
    ← Real.rpow_sub hx]
  congr 1
  dsimp only [a, b]
  unfold inghamRouteTPhysicalScaleExponent inghamRouteTMellinBufferedFrequencyExponent
  norm_num

theorem routeT_negative_half_horizontal_kernel_scale_le
    {C T : ℝ} {X : ℕ} (hC : 0 ≤ C) (hX : 12 ≤ X)
    (hT : T ∈ Ioo ((X : ℝ) - 3) ((X : ℝ) - 2)) :
    C * (3 * inghamRouteTMellinPhysicalCenter X) ^ (4001 : ℝ) /
          inghamRouteTMellinBufferedPhysicalWidth X ^ 4000 / T ^ 4000 ≤
      (C * 3 ^ (4001 : ℝ) * 2 ^ (4000 : ℝ)) *
        (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
  have hX1 : 1 ≤ X := by omega
  have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
  have hTpos : 0 < T := by linarith [hT.1]
  have hhalfpos : 0 < (X : ℝ) / 2 := by positivity
  have hhalfT : (X : ℝ) / 2 ≤ T := by linarith [hT.1]
  have hpowT : ((X : ℝ) / 2) ^ 4000 ≤ T ^ 4000 :=
    pow_le_pow_left₀ hhalfpos.le hhalfT 4000
  have hNpos := inghamRouteTMellinPhysicalCenter_pos hX1
  have hHpos := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  have hpre : 0 ≤
      C * (3 * inghamRouteTMellinPhysicalCenter X) ^ (4001 : ℝ) /
        inghamRouteTMellinBufferedPhysicalWidth X ^ 4000 := by
    exact div_nonneg
      (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
      (pow_nonneg hHpos.le _)
  calc
    C * (3 * inghamRouteTMellinPhysicalCenter X) ^ (4001 : ℝ) /
          inghamRouteTMellinBufferedPhysicalWidth X ^ 4000 / T ^ 4000 ≤
        C * (3 * inghamRouteTMellinPhysicalCenter X) ^ (4001 : ℝ) /
          inghamRouteTMellinBufferedPhysicalWidth X ^ 4000 /
            (((X : ℝ) / 2) ^ 4000) :=
      div_le_div_of_nonneg_left hpre (pow_pos hhalfpos 4000) hpowT
    _ = (C * 3 ^ (4001 : ℝ) * 2 ^ (4000 : ℝ)) *
          (X : ℝ) ^ (-(196 / 299 : ℝ)) :=
      routeT_negative_half_horizontal_exact_scale hX1

theorem exists_routeT_negativeHalf_two_horizontal_integrals_decay_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {X : ℕ}, 12 ≤ X →
      ∃ T ∈ Ioo ((X : ℝ) - 3) ((X : ℝ) - 2),
        (∀ x ∈ Icc (-1 / 2 : ℝ) 2,
          zetaResidueUnit ((x : ℂ) + (T : ℂ) * I) ≠ 0) ∧
        (∀ x ∈ Icc (-1 / 2 : ℝ) 2,
          zetaResidueUnit ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) ∧
        ‖∫ x : ℝ in (-1 / 2)..2,
            zetaLogDerivReg ((x : ℂ) + (T : ℂ) * I) *
              routeTNormalizedSmoothWindowMellin
                (inghamRouteTMellinPhysicalCenter X)
                (inghamRouteTMellinBufferedPhysicalWidth X)
                ((x : ℂ) + (T : ℂ) * I)‖ ≤
          A * (1 + Real.log X) ^ 2 *
            (X : ℝ) ^ (-(196 / 299 : ℝ)) ∧
        ‖∫ x : ℝ in (-1 / 2)..2,
            zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * I) *
              routeTNormalizedSmoothWindowMellin
                (inghamRouteTMellinPhysicalCenter X)
                (inghamRouteTMellinBufferedPhysicalWidth X)
                ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
          A * (1 + Real.log X) ^ 2 *
            (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
  obtain ⟨C, hC, hkernel⟩ :=
    exists_bound_routeTNormalizedSmoothWindowMellin_horizontal
  obtain ⟨K, hK, hselected⟩ :=
    exists_routeT_negativeHalf_two_horizontal_edges_polylog
  let B : ℝ := C * 3 ^ (4001 : ℝ) * 2 ^ (4000 : ℝ)
  let A : ℝ := (5 / 2 : ℝ) * K * B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro X hX
  obtain ⟨T, hT, htop, hbot⟩ := hselected hX
  have hX1 : 1 ≤ X := by omega
  have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
  have hTpos : 0 < T := by linarith [hT.1]
  have hTabs : |T| = T := abs_of_pos hTpos
  have hT9 : 9 ≤ |T| := by rw [hTabs]; linarith [hT.1]
  let N : ℝ := inghamRouteTMellinPhysicalCenter X
  let H : ℝ := inghamRouteTMellinBufferedPhysicalWidth X
  have hN1 : 1 ≤ N := inghamRouteTMellinPhysicalCenter_one_le hX1
  have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  have hHN : H ≤ N := inghamRouteTMellinBufferedPhysicalWidth_le_center hX1
  have hscale := routeT_negative_half_horizontal_kernel_scale_le hC hX hT
  let U : ℝ := A * (1 + Real.log X) ^ 2 *
    (X : ℝ) ^ (-(196 / 299 : ℝ))
  let P : ℝ := K * (1 + Real.log X) ^ 2 *
    (B * (X : ℝ) ^ (-(196 / 299 : ℝ)))
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hpointTop : ∀ x ∈ uIoc (-1 / 2 : ℝ) 2,
      ‖zetaLogDerivReg ((x : ℂ) + (T : ℂ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((x : ℂ) + (T : ℂ) * I)‖ ≤ P := by
    intro x hx
    have hxI : x ∈ Icc (-1 / 2 : ℝ) 2 := by
      rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] at hx
      exact ⟨hx.1.le, hx.2⟩
    have hz := (htop x hxI).2
    have hk0 := hkernel N H T x hN1 hH hHN hT9 hxI
    have hk : ‖routeTNormalizedSmoothWindowMellin N H
        ((x : ℂ) + (T : ℂ) * I)‖ ≤
        B * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
      have hk1 : ‖routeTNormalizedSmoothWindowMellin N H
          ((x : ℂ) + (T : ℂ) * I)‖ ≤
          C * (3 * N) ^ (4001 : ℝ) / H ^ 4000 / T ^ 4000 := by
        simpa only [hTabs] using hk0
      have hk2 : C * (3 * N) ^ (4001 : ℝ) / H ^ 4000 / T ^ 4000 ≤
          B * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
        simpa only [B, N, H] using hscale
      exact hk1.trans hk2
    rw [norm_mul]
    exact mul_le_mul hz hk (norm_nonneg _) (by positivity)
  have hpointBot : ∀ x ∈ uIoc (-1 / 2 : ℝ) 2,
      ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ P := by
    intro x hx
    have hxI : x ∈ Icc (-1 / 2 : ℝ) 2 := by
      rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] at hx
      exact ⟨hx.1.le, hx.2⟩
    have hz := (hbot x hxI).2
    have hk0 := hkernel N H (-T) x hN1 hH hHN (by simpa using hT9) hxI
    have hk : ‖routeTNormalizedSmoothWindowMellin N H
        ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
        B * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
      have hk1 : ‖routeTNormalizedSmoothWindowMellin N H
          ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
          C * (3 * N) ^ (4001 : ℝ) / H ^ 4000 / T ^ 4000 := by
        simpa only [abs_neg, hTabs] using hk0
      have hk2 : C * (3 * N) ^ (4001 : ℝ) / H ^ 4000 / T ^ 4000 ≤
          B * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
        simpa only [B, N, H] using hscale
      exact hk1.trans hk2
    rw [norm_mul]
    exact mul_le_mul hz hk (norm_nonneg _) (by positivity)
  have hIntTop := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ =>
      zetaLogDerivReg ((x : ℂ) + (T : ℂ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((x : ℂ) + (T : ℂ) * I))
    (C := P) hpointTop
  have hIntBot := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ =>
      zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * I) *
        routeTNormalizedSmoothWindowMellin N H
          ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
    (C := P) hpointBot
  refine ⟨T, hT, fun x hx => (htop x hx).1, fun x hx => (hbot x hx).1, ?_, ?_⟩
  · change ‖∫ x in (-1 / 2)..2,
        zetaLogDerivReg ((x : ℂ) + (T : ℂ) * I) *
          routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + (T : ℂ) * I)‖ ≤ U
    calc
      _ ≤ P * |2 - (-1 / 2 : ℝ)| := hIntTop
      _ = U := by dsimp only [P, U, A, B]; norm_num; ring
  · change ‖∫ x in (-1 / 2)..2,
        zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * I) *
          routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ U
    calc
      _ ≤ P * |2 - (-1 / 2 : ℝ)| := hIntBot
      _ = U := by dsimp only [P, U, A, B]; norm_num; ring

theorem tendsto_routeT_negativeHalf_horizontal_decay_envelope_zero
    (A : ℝ) :
    Tendsto (fun X : ℕ =>
      A * (1 + Real.log X) ^ 2 *
        (X : ℝ) ^ (-(196 / 299 : ℝ))) atTop (nhds 0) := by
  let a : ℝ := 196 / 299
  have ha : 0 < a := by dsimp only [a]; norm_num
  have h0 : Tendsto (fun x : ℝ => (1 : ℝ) / x ^ a) atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop ha)
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x ^ a) atTop (nhds 0) :=
    HTGeometry.tendsto_logPow_div_rpow ha 2
  have hdiv : Tendsto (fun x : ℝ => (1 + Real.log x) ^ 2 / x ^ a)
      atTop (nhds 0) := by
    have hsum := h0.add ((h1.const_mul 2).add h2)
    convert hsum using 1
    · funext x
      ring
    · simp
  have hnat := hdiv.comp tendsto_natCast_atTop_atTop
  have hcore : Tendsto (fun X : ℕ =>
      (1 + Real.log X) ^ 2 * (X : ℝ) ^ (-a)) atTop (nhds 0) := by
    refine hnat.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hx : (0 : ℝ) ≤ X := by positivity
    change (1 + Real.log (X : ℝ)) ^ 2 / (X : ℝ) ^ a =
      (1 + Real.log (X : ℝ)) ^ 2 * (X : ℝ) ^ (-a)
    rw [Real.rpow_neg hx, div_eq_mul_inv]
  have hscaled := hcore.const_mul A
  convert hscaled using 1
  · funext X
    dsimp only [a]
    ring
  · simp

noncomputable def inghamRouteTNegativeHalfHorizontalDecayConstant : ℝ :=
  Classical.choose exists_routeT_negativeHalf_two_horizontal_integrals_decay_bound

theorem inghamRouteTNegativeHalfHorizontalDecayConstant_nonneg :
    0 ≤ inghamRouteTNegativeHalfHorizontalDecayConstant :=
  (Classical.choose_spec
    exists_routeT_negativeHalf_two_horizontal_integrals_decay_bound).1

noncomputable def inghamRouteTBufferedNegativeHalfHeight (X : ℕ) : ℝ :=
  if hX : 12 ≤ X then
    Classical.choose ((Classical.choose_spec
      exists_routeT_negativeHalf_two_horizontal_integrals_decay_bound).2 hX)
  else 1

def inghamRouteTBufferedNegativeHalfTopEdge (X : ℕ) : ℂ :=
  ∫ x : ℝ in (-1 / 2)..2,
    zetaLogDerivReg
        ((x : ℂ) + (inghamRouteTBufferedNegativeHalfHeight X : ℂ) * I) *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((x : ℂ) + (inghamRouteTBufferedNegativeHalfHeight X : ℂ) * I)

def inghamRouteTBufferedNegativeHalfBottomEdge (X : ℕ) : ℂ :=
  ∫ x : ℝ in (-1 / 2)..2,
    zetaLogDerivReg
        ((x : ℂ) + ((-inghamRouteTBufferedNegativeHalfHeight X : ℝ) : ℂ) * I) *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((x : ℂ) + ((-inghamRouteTBufferedNegativeHalfHeight X : ℝ) : ℂ) * I)

theorem inghamRouteTBufferedNegativeHalfHeight_spec
    {X : ℕ} (hX : 12 ≤ X) :
    inghamRouteTBufferedNegativeHalfHeight X ∈
        Ioo ((X : ℝ) - 3) ((X : ℝ) - 2) ∧
      (∀ x ∈ Icc (-1 / 2 : ℝ) 2,
        zetaResidueUnit
          ((x : ℂ) + (inghamRouteTBufferedNegativeHalfHeight X : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Icc (-1 / 2 : ℝ) 2,
        zetaResidueUnit
          ((x : ℂ) + ((-inghamRouteTBufferedNegativeHalfHeight X : ℝ) : ℂ) * I) ≠ 0) ∧
      ‖inghamRouteTBufferedNegativeHalfTopEdge X‖ ≤
        inghamRouteTNegativeHalfHorizontalDecayConstant *
          (1 + Real.log X) ^ 2 * (X : ℝ) ^ (-(196 / 299 : ℝ)) ∧
      ‖inghamRouteTBufferedNegativeHalfBottomEdge X‖ ≤
        inghamRouteTNegativeHalfHorizontalDecayConstant *
          (1 + Real.log X) ^ 2 * (X : ℝ) ^ (-(196 / 299 : ℝ)) := by
  rw [inghamRouteTBufferedNegativeHalfHeight, dif_pos hX]
  simpa [inghamRouteTNegativeHalfHorizontalDecayConstant,
    inghamRouteTBufferedNegativeHalfHeight, hX,
    inghamRouteTBufferedNegativeHalfTopEdge,
    inghamRouteTBufferedNegativeHalfBottomEdge] using
    Classical.choose_spec ((Classical.choose_spec
      exists_routeT_negativeHalf_two_horizontal_integrals_decay_bound).2 hX)

theorem tendsto_inghamRouteTBufferedNegativeHalfTopEdge_zero :
    Tendsto inghamRouteTBufferedNegativeHalfTopEdge atTop (nhds 0) := by
  have hupper := tendsto_routeT_negativeHalf_horizontal_decay_envelope_zero
    inghamRouteTNegativeHalfHorizontalDecayConstant
  have hnorm : Tendsto (fun X : ℕ =>
      ‖inghamRouteTBufferedNegativeHalfTopEdge X‖) atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards with X
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
      exact (inghamRouteTBufferedNegativeHalfHeight_spec hX).2.2.2.1
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

theorem tendsto_inghamRouteTBufferedNegativeHalfBottomEdge_zero :
    Tendsto inghamRouteTBufferedNegativeHalfBottomEdge atTop (nhds 0) := by
  have hupper := tendsto_routeT_negativeHalf_horizontal_decay_envelope_zero
    inghamRouteTNegativeHalfHorizontalDecayConstant
  have hnorm : Tendsto (fun X : ℕ =>
      ‖inghamRouteTBufferedNegativeHalfBottomEdge X‖) atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards with X
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
      exact (inghamRouteTBufferedNegativeHalfHeight_spec hX).2.2.2.2
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

theorem routeTBufferedNegativeHalfBoundary_eq_neg_zeroPacket
    {X : ℕ} (hX : 12 ≤ X) :
    routeTNormalizedZetaRegularMellinBoundary
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (-1 / 2) 2
        (inghamRouteTBufferedNegativeHalfHeight X) =
      -routeTNormalizedZetaRegularMellinZeroPacket
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X) (-1 / 2) 2
        (inghamRouteTBufferedNegativeHalfHeight X) := by
  have hspec := inghamRouteTBufferedNegativeHalfHeight_spec hX
  have hX1 : 1 ≤ X := by omega
  exact routeTNormalizedZetaRegularMellinBoundary_eq_neg_zeroPacket_univ
    (inghamRouteTMellinPhysicalCenter_pos hX1)
    (inghamRouteTMellinBufferedPhysicalWidth_pos hX1)
    (by norm_num) (by linarith [hspec.1.1, show (12 : ℝ) ≤ X by exact_mod_cast hX])
    (by simpa [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] using hspec.2.2.1)
    (by simpa [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] using hspec.2.1)
    (fun y _ => zetaResidueUnit_ne_zero_two y)
    (fun y _ => by simpa using zetaResidueUnit_ne_zero_negative_half y)

def inghamRouteTBufferedSelectedNegativeHalfLeftEdge (X : ℕ) : ℂ :=
  ∫ t in (-inghamRouteTBufferedNegativeHalfHeight X)..
      inghamRouteTBufferedNegativeHalfHeight X,
    zetaLogDerivReg ((-1 / 2 : ℂ) + (t : ℂ) * I) *
      routeTNormalizedSmoothWindowMellin
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        ((-1 / 2 : ℂ) + (t : ℂ) * I)

theorem tendsto_inghamRouteTBufferedSelectedNegativeHalfLeftEdge_zero :
    Tendsto inghamRouteTBufferedSelectedNegativeHalfLeftEdge atTop (nhds 0) := by
  obtain ⟨A, B, hA, hB, hedge⟩ :=
    exists_bound_routeT_zetaLogDerivReg_negative_half_edge
  have hcoreLow : Tendsto (fun X : ℕ => (X : ℝ) ^ (-(1201 / 299 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1201 / 299)).comp
      tendsto_natCast_atTop_atTop
  have hcoreHigh : Tendsto (fun X : ℕ => (X : ℝ) ^ (-(1549 / 74750 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1549 / 74750)).comp
      tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun X : ℕ =>
      (2 * A) * (X : ℝ) ^ (-(1201 / 299 : ℝ)) +
        (2 * B * 3 ^ (5 / 2 : ℝ)) *
          (X : ℝ) ^ (-(1549 / 74750 : ℝ))) atTop (nhds 0) := by
    convert (hcoreLow.const_mul (2 * A)).add
      (hcoreHigh.const_mul (2 * B * 3 ^ (5 / 2 : ℝ))) using 1 <;> simp
  have hupper : Tendsto (fun X : ℕ =>
      2 * (X : ℝ) *
        (A * inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ)) +
          B * (3 * inghamRouteTMellinPhysicalCenter X) ^ (5 / 2 : ℝ) /
            inghamRouteTMellinBufferedPhysicalWidth X ^ 4)) atTop (nhds 0) := by
    refine hscaled.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    have hlo := routeT_negative_half_compact_scale_eq hX
    have hhi := routeT_negative_half_high_scale_eq hX
    symm
    calc
      2 * (X : ℝ) *
          (A * inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ)) +
            B * (3 * inghamRouteTMellinPhysicalCenter X) ^ (5 / 2 : ℝ) /
              inghamRouteTMellinBufferedPhysicalWidth X ^ 4) =
          2 * A * ((X : ℝ) *
            inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ))) +
          2 * B * ((X : ℝ) *
            (3 * inghamRouteTMellinPhysicalCenter X) ^ (5 / 2 : ℝ) /
              inghamRouteTMellinBufferedPhysicalWidth X ^ 4) := by ring
      _ = 2 * A * (X : ℝ) ^ (-(1201 / 299 : ℝ)) +
          2 * B * (3 ^ (5 / 2 : ℝ) *
            (X : ℝ) ^ (-(1549 / 74750 : ℝ))) := by rw [hlo, hhi]
      _ = (2 * A) * (X : ℝ) ^ (-(1201 / 299 : ℝ)) +
          (2 * B * 3 ^ (5 / 2 : ℝ)) *
            (X : ℝ) ^ (-(1549 / 74750 : ℝ)) := by ring
  have hnorm : Tendsto (fun X : ℕ =>
      ‖inghamRouteTBufferedSelectedNegativeHalfLeftEdge X‖) atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards with X
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (12 : ℕ)] with X hX
      have hspec := inghamRouteTBufferedNegativeHalfHeight_spec hX
      have hX1 : 1 ≤ X := by omega
      have hT9 : (9 : ℝ) ≤ inghamRouteTBufferedNegativeHalfHeight X := by
        have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
        linarith [hspec.1.1]
      have hTX : inghamRouteTBufferedNegativeHalfHeight X ≤ (X : ℝ) := by
        linarith [hspec.1.2]
      let E : ℝ :=
        A * inghamRouteTMellinPhysicalCenter X ^ (-(3 / 2 : ℝ)) +
          B * (3 * inghamRouteTMellinPhysicalCenter X) ^ (5 / 2 : ℝ) /
            inghamRouteTMellinBufferedPhysicalWidth X ^ 4
      have hE : 0 ≤ E := by
        dsimp only [E]
        exact add_nonneg
          (mul_nonneg hA (Real.rpow_nonneg
            (inghamRouteTMellinPhysicalCenter_pos hX1).le _))
          (div_nonneg
            (mul_nonneg hB (Real.rpow_nonneg
              (mul_nonneg (by norm_num)
                (inghamRouteTMellinPhysicalCenter_pos hX1).le) _))
            (pow_nonneg (inghamRouteTMellinBufferedPhysicalWidth_pos hX1).le _))
      have hraw := hedge
        (inghamRouteTMellinPhysicalCenter X)
        (inghamRouteTMellinBufferedPhysicalWidth X)
        (inghamRouteTBufferedNegativeHalfHeight X)
        (inghamRouteTMellinPhysicalCenter_pos hX1)
        (inghamRouteTMellinBufferedPhysicalWidth_pos hX1)
        (inghamRouteTMellinBufferedPhysicalWidth_le_center hX1) hT9
      calc
        ‖inghamRouteTBufferedSelectedNegativeHalfLeftEdge X‖ ≤
            2 * inghamRouteTBufferedNegativeHalfHeight X * E := by
          simpa only [inghamRouteTBufferedSelectedNegativeHalfLeftEdge, E] using hraw
        _ ≤ 2 * (X : ℝ) * E := by gcongr
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

end

end RHTower.Sieve
