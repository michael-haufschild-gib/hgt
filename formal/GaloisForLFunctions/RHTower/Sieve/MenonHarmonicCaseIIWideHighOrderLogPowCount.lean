import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIWideLargeValueCount
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIHighOrderAbsorptionSchedule
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIWideMeasure
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeBlockSymmetry
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFrequencyMoment

/-!
# High-order wide-smoothed Case-II count

Order one hundred in Menon's medium-Möbius estimate leaves the explicit `(log a)^(-80)` reserve
needed by the growing final-range grid. Wide smoothing changes only the already-internal kernel and
transition envelopes.
-/

namespace RHTower.Sieve

noncomputable section

open Filter MeasureTheory Set

/-- Wide-smoothed harmonic-prime large values satisfy the explicit Case-II count whenever the
selected threshold dominates `(log a)^(-80)`. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide_highOrder_logPow :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X Y cells : ℕ} {T0 t H B sigma V Δ T : ℝ}
          {S : Finset ℕ} {w : ℕ → ℝ},
        1 ≤ X → a < Y → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        L ≤ X → (X : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) →
        0 < H → (Y : ℝ) + H ≤ (X : ℝ) →
        1 < sigma → 0 ≤ B → 0 ≤ V → 1 ≤ Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        (∀ r : ℕ, -(2 * Real.pi * w r) + 2 * Δ ≤ -(2 * Real.pi * w (r + 1))) →
        1 ≤ T → Δ / 2 ≤ T →
        (∀ r ∈ S, T + V ≤ -(2 * Real.pi * w r) ∧
          -(2 * Real.pi * w r) ≤ 2 * T - V) →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 X H sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        (Real.log (a : ℝ)) ^ (-80 : ℝ) < Q →
        (∀ r ∈ S,
          (((B + menonWideIntervalTransitionEnvelope X H) +
                primePowerDefectIoc a Y) /
              Real.log ((a + 1 : ℕ) : ℝ)) /
                ((a + 1 : ℕ) : ℝ) <
            ‖harmonicPrimeBlockPoly (primesRange a Y) (w r)‖) →
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
        (S.card : ℝ) * Vexp ^ 2 ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  obtain ⟨C0, hC0, hcount⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide 100
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hcount,
    eventually_menonHeathBrownCaseIIAbsorptionEnvelope_hundred_lt_logPow_of_polynomial_support]
      with a haCount haAbsorb
  intro L X Y cells T0 t H B sigma V Δ T S w hX haY hXL hT0 hscale ha hL hLX hXa
    hH hYX hsigma hB hV hΔ hcells hgrid hbaseGap hT hΔT hbaseBand h2T
  dsimp only
  intro hQ hlarge
  have haReal : (1 : ℝ) < (a : ℝ) := by
    calc
      (1 : ℝ) < 64 ^ (8 : ℕ) := by norm_num
      _ ≤ (a : ℝ) := ha
  have hlogPow : 0 < (Real.log (a : ℝ)) ^ (-80 : ℝ) :=
    Real.rpow_pos_of_pos (Real.log_pos haReal) _
  exact haCount hX haY hXL hT0 hscale ha hL hH hYX hsigma hB hV hΔ hcells hgrid
    hbaseGap hT hΔT hbaseBand h2T (hlogPow.trans hQ) (by norm_num)
      ((haAbsorb hL hX hLX hXa).trans hQ) hlarge

/-- Literal finite separated sets inherit the order-one-hundred Case-II cardinality bound. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide_highOrder_realFinset :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X Y cells : ℕ} {T0 t H B sigma V Δ T : ℝ}
          {E : Finset ℝ},
        1 ≤ X → a < Y → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        L ≤ X → (X : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) →
        0 < H → (Y : ℝ) + H ≤ (X : ℝ) →
        1 < sigma → 0 ≤ B → 0 ≤ V → 1 ≤ Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        (∀ x ∈ E, ∀ y ∈ E, x ≠ y → 2 * Δ ≤ |x - y|) →
        1 ≤ T → Δ / 2 ≤ T →
        (∀ x ∈ E, T + V ≤ x ∧ x ≤ 2 * T - V) →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 X H sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        (Real.log (a : ℝ)) ^ (-80 : ℝ) < Q →
        (∀ x ∈ E,
          (((B + menonWideIntervalTransitionEnvelope X H) +
                primePowerDefectIoc a Y) /
              Real.log ((a + 1 : ℕ) : ℝ)) /
                ((a + 1 : ℕ) : ℝ) <
            ‖harmonicPrimeBlockPoly (primesRange a Y)
              (-x / (2 * Real.pi))‖) →
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
        (E.card : ℝ) * Vexp ^ 2 ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  obtain ⟨C0, hC0, hcount⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide_highOrder_logPow
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hcount] with a haCount
  intro L X Y cells T0 t H B sigma V Δ T E hX haY hXL hT0 hscale ha hL hLX hXa
    hH hYX hsigma hB hV hΔ hcells hgrid hsep hT hΔT hband h2T
  dsimp only
  intro hQ hlarge
  have htwoDelta : 0 < 2 * Δ := by positivity
  let P := matomakiTeravainenFiniteSeparatedOrdinates E (2 * Δ) htwoDelta hsep
  let tau : ℕ → ℝ := RHTower.cglFiniteSeparatedOrdinatesTimeline P
  let w : ℕ → ℝ := fun r => -(tau r) / (2 * Real.pi)
  have hphase : ∀ r : ℕ, -(2 * Real.pi * w r) = tau r := by
    intro r
    dsimp only [w]
    field_simp [Real.pi_ne_zero]
  have hgap : ∀ r : ℕ, -(2 * Real.pi * w r) + 2 * Δ ≤
      -(2 * Real.pi * w (r + 1)) := by
    intro r
    rw [hphase r, hphase (r + 1)]
    exact RHTower.cglFiniteSeparatedOrdinatesTimeline_step P r
  have hactiveBand : ∀ r ∈ Finset.range E.card,
      T + V ≤ -(2 * Real.pi * w r) ∧ -(2 * Real.pi * w r) ≤ 2 * T - V := by
    intro r hr
    rw [hphase r]
    exact hband _ (matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
      E (2 * Δ) htwoDelta hsep (Finset.mem_range.mp hr))
  have hactiveLarge : ∀ r ∈ Finset.range E.card,
      (((B + menonWideIntervalTransitionEnvelope X H) +
            primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
            ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) (w r)‖ := by
    intro r hr
    have hmem := matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
      E (2 * Δ) htwoDelta hsep (Finset.mem_range.mp hr)
    simpa only [w, tau] using hlarge _ hmem
  simpa only [Finset.card_range] using
    haCount hX haY hXL hT0 hscale ha hL hLX hXa hH hYX hsigma hB hV hΔ hcells hgrid
      hgap hT hΔT hactiveBand h2T hQ hactiveLarge

/-- One physical frequency band inherits the order-one-hundred Case-II measure bound. -/
theorem exists_absolute_eventually_volume_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_highOrder_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X Y cells : ℕ} {T0 t H B sigma V Δ T : ℝ},
        1 ≤ X → a < Y → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        L ≤ X → (X : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) →
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
        (Real.log (a : ℝ)) ^ (-80 : ℝ) < Q →
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
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide_highOrder_realFinset
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hcount] with a haCount
  intro L X Y cells T0 t H B sigma V Δ T hX haY hXL hT0 hscale ha hL hLX hXa
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
    have hempty := haCount (E := (∅ : Finset ℝ)) hX haY hXL hT0 hscale ha hL hLX hXa
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
        have hfinite := haCount (E := E) hX haY hXL hT0 hscale ha hL hLX hXa hH hYX
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

/-- Both Gallagher-frequency pullbacks of the high-order physical Case-II exceptional band. -/
def menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet
    (a X Y : ℕ) (H B T V : ℝ) : Set ℝ :=
  (fun w : ℝ => -(2 * Real.pi) * w) ⁻¹'
      menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V ∪
    (fun w : ℝ => (2 * Real.pi) * w) ⁻¹'
      menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V

/-- The two Gallagher-frequency signs cost exactly two copies of the `(2π)⁻¹` Jacobian. -/
theorem volume_real_menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet_le
    (a X Y : ℕ) (H B T V : ℝ) :
    volume.real
        (menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet a X Y H B T V) ≤
      2 * (2 * Real.pi)⁻¹ *
        volume.real (menonHarmonicPrimeBlockWideExceptionalSet a X Y H B T V) := by
  rw [menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet]
  refine (measureReal_union_le _ _).trans ?_
  rw [volume_real_preimage_neg_mul_left (by positivity : 0 < 2 * Real.pi),
    volume_real_preimage_mul_left (by positivity : 0 < 2 * Real.pi)]
  ring_nf
  exact le_rfl

/-- A large value in the negative Gallagher half belongs to the high-order two-sided set. -/
theorem mem_menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet_of_neg
    {a X Y : ℕ} {H B T V w : ℝ}
    (hband : T + V ≤ -(2 * Real.pi) * w ∧ -(2 * Real.pi) * w ≤ 2 * T - V)
    (hlarge :
      (((B + menonWideIntervalTransitionEnvelope X H) + primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
          ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) w‖) :
    w ∈ menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet a X Y H B T V := by
  refine Set.mem_union_left _ ?_
  exact ⟨hband, by simpa [Real.pi_ne_zero] using hlarge⟩

/-- The positive Gallagher half follows from exact conjugation symmetry. -/
theorem mem_menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet_of_pos
    {a X Y : ℕ} {H B T V w : ℝ}
    (hband : T + V ≤ (2 * Real.pi) * w ∧ (2 * Real.pi) * w ≤ 2 * T - V)
    (hlarge :
      (((B + menonWideIntervalTransitionEnvelope X H) + primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
          ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) w‖) :
    w ∈ menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet a X Y H B T V := by
  refine Set.mem_union_right _ ?_
  refine ⟨hband, ?_⟩
  have harg : -((2 * Real.pi) * w) / (2 * Real.pi) = -w := by
    field_simp [Real.pi_ne_zero]
  change
    (((B + menonWideIntervalTransitionEnvelope X H) + primePowerDefectIoc a Y) /
        Real.log ((a + 1 : ℕ) : ℝ)) /
        ((a + 1 : ℕ) : ℝ) <
      ‖harmonicPrimeBlockPoly (primesRange a Y)
        (-((2 * Real.pi) * w) / (2 * Real.pi))‖
  rw [harg, norm_harmonicPrimeBlockPoly_neg]
  exact hlarge

/-- Full order-one-hundred Case-II measure theorem on both Gallagher-frequency halves. -/
theorem exists_absolute_eventually_volume_real_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_highOrder_twoSided_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X Y cells : ℕ} {T0 t H B sigma V Δ T : ℝ},
        1 ≤ X → a < Y → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        L ≤ X → (X : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) →
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
        (Real.log (a : ℝ)) ^ (-80 : ℝ) < Q →
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
        volume.real
            (menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet a X Y H B T V) ≤
          2 * (2 * Real.pi)⁻¹ *
            (4 * Δ * (((((cells * D * 12 : ℕ) : ℝ)) * Hmax) / Vexp ^ 2 + 1)) := by
  obtain ⟨C0, hC0, hmain⟩ :=
    exists_absolute_eventually_volume_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_highOrder_le
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hmain] with a ha
  intro L X Y cells T0 t H B sigma V Δ T hX haY hXL hT0 hscale ha64 hL hLX hXa
    hH hYX hsigma hB hV hΔ hcells hgrid hT hΔT h2T
  dsimp only
  intro hQ
  have hphysical := ha hX haY hXL hT0 hscale ha64 hL hLX hXa hH hYX hsigma hB hV
    hΔ hcells hgrid hT hΔT h2T hQ
  have hpull :=
    volume_real_menonHarmonicPrimeBlockWideHighOrderGallagherExceptionalSet_le
      a X Y H B T V
  exact hpull.trans (mul_le_mul_of_nonneg_left hphysical (by positivity))

end

end RHTower.Sieve
