import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIWideRealFinsetCount
import GaloisForLFunctions.RHTower.Sieve.RealSeparatedSetMeasure

/-!
# Wide-smoothed Case-II measure bound for one harmonic prime block
-/

namespace RHTower.Sieve

noncomputable section

open Filter MeasureTheory Set

/-- Frequencies in the narrowed physical band where one harmonic prime block exceeds the complete
wide-smoothed reverse-Abel threshold. -/
def menonHarmonicPrimeBlockWideExceptionalSet
    (a X Y : ℕ) (H B T V : ℝ) : Set ℝ :=
  Set.Icc (T + V) (2 * T - V) ∩
    {x : ℝ |
      (((B + menonWideIntervalTransitionEnvelope X H) +
            primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
          ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) (-x / (2 * Real.pi))‖}

/-- The literal exceptional-frequency set for one harmonic prime block satisfies the explicit
wide-smoothed paper-scale Case-II measure bound. -/
theorem exists_absolute_eventually_volume_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X Y cells : ℕ} {T0 t H B sigma V Δ T : ℝ},
        1 ≤ X → a < Y → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ) →
        0 < H → (Y : ℝ) + H ≤ (X : ℝ) →
        1 < sigma → 0 ≤ B → 0 ≤ V → 1 ≤ Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        1 ≤ T → Δ / 2 ≤ T →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 X H sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        (Real.log (a : ℝ)) ^ (-8 : ℝ) < Q →
        let D : ℕ :=
          3 * (Nat.log 2 X + 1) ^ 3 * (Nat.log 2 L + 1) ^ 3
        let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope X) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * W ^ 2 *
              (1 + Real.log (W * (X : ℝ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        (volume (menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V)).toReal ≤
          4 * Δ * (((((cells * D * 12 : ℕ) : ℝ)) * Hmax) / Vexp ^ 2 + 1) := by
  obtain ⟨C0, hC0, hcount⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide_realFinset
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hcount] with a haCount
  intro L X Y cells T0 t H B sigma V Δ T hX haY hXL hT0 hscale ha hL hcut
    hH hYX hsigma hB hV hΔ hcells hgrid hT hΔT h2T
  dsimp only
  intro hQ
  let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 X H sigma
  let Q : ℝ :=
    (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
        (Real.pi - 2 * Real.arctan V)) /
      ((cells : ℝ) * Δ * C)
  let D : ℕ :=
    3 * (Nat.log 2 X + 1) ^ 3 * (Nat.log 2 L + 1) ^ 3
  let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
  let Vexp : ℝ :=
    min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
        (5120 * maynardLongPolylogEnvelope X) * (Q / ((D : ℝ) * 8))
  let Hmax : ℝ :=
    (12 * W ^ 2 *
        (1 + Real.log (W * (X : ℝ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
      (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
  let R : ℝ := (((cells * D * 12 : ℕ) : ℝ)) * Hmax
  have haReal : (1 : ℝ) < (a : ℝ) := by
    calc
      (1 : ℝ) < 64 ^ (8 : ℕ) := by norm_num
      _ ≤ (a : ℝ) := ha
  have hQpos : 0 < Q :=
    (Real.rpow_pos_of_pos (Real.log_pos haReal) _).trans
      (by simpa only [Q, C] using hQ)
  have hVexp : 0 < Vexp := by
    dsimp only [Vexp]
    have hDpos : 0 < (D : ℝ) := by
      dsimp only [D]
      positivity
    have hgain : 0 < (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) := by
      positivity
    have henv : 0 < maynardLongPolylogEnvelope X :=
      lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
    have hTpos : 0 < T := zero_lt_one.trans_le hT
    exact mul_pos (div_pos (lt_min hTpos hgain) (mul_pos (by norm_num) henv))
      (div_pos hQpos (mul_pos hDpos (by norm_num)))
  have hR : 0 ≤ R := by
    have hempty := haCount (E := (∅ : Finset ℝ)) hX haY hXL hT0 hscale ha hL hcut
      hH hYX hsigma hB hV hΔ hcells hgrid (by simp) hT hΔT (by simp) h2T
      (by simpa only [Q, C] using hQ) (by simp)
    simpa only [Finset.card_empty, Nat.cast_zero, zero_mul, D, W, Vexp, Hmax, R]
      using hempty
  have hmeasure := volume_toReal_le_of_separated_finset_mul_sq_le
    (S := menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V)
    (δ := 2 * Δ) (v := Vexp) (R := R) (by positivity) hVexp hR
      (by
        intro E hES hsep
        have hbandE : ∀ x ∈ E, T + V ≤ x ∧ x ≤ 2 * T - V := by
          intro x hx
          exact (hES (by exact_mod_cast hx)).1
        have hlargeE : ∀ x ∈ E,
            (((B + menonWideIntervalTransitionEnvelope X H) +
                  primePowerDefectIoc a Y) /
                Real.log ((a + 1 : ℕ) : ℝ)) /
                  ((a + 1 : ℕ) : ℝ) <
              ‖harmonicPrimeBlockPoly (primesRange a Y)
                (-x / (2 * Real.pi))‖ := by
          intro x hx
          exact (hES (by exact_mod_cast hx)).2
        have hfinite := haCount (E := E) hX haY hXL hT0 hscale ha hL hcut hH hYX
          hsigma hB hV hΔ hcells hgrid hsep hT hΔT hbandE h2T
          (by simpa only [Q, C] using hQ) hlargeE
        simpa only [D, W, Vexp, Hmax, R] using hfinite)
  have hmeasure' :
      (volume (menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V)).toReal ≤
        4 * Δ * (R / Vexp ^ 2 + 1) := by
    calc
      (volume (menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V)).toReal ≤
          2 * (2 * Δ) * (R / Vexp ^ 2 + 1) := hmeasure
      _ = 4 * Δ * (R / Vexp ^ 2 + 1) := by ring
  simpa only [D, W, Vexp, Hmax, R, Q, C] using hmeasure'

end

end RHTower.Sieve
