import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIFrequencyRange

/-!
# Generic pointwise Case-II control for a narrow harmonic prime block

The scheduled final-range theorem is a specialization of a statement depending only on the
literal endpoints `a < Y ≤ 2a`.  This module exposes that underlying statement.  The proof uses a
singleton separated family in the order-four-hundred Case-II estimate and then inserts the
canonical smoothing and threshold budgets.
-/

namespace RHTower.Sieve

open Filter Finset

noncomputable section

set_option maxHeartbeats 800000 in
/-- Canonical Case-II cardinal estimate for an arbitrary sufficiently late narrow prime block. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_canonical_realFinset :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {Y : ℕ} {T : ℝ} {E : Finset ℝ},
        a < Y → Y ≤ 2 * a →
        1 ≤ T → (menonHarmonicCaseIICells a : ℝ) / 4 ≤ T →
        (∀ u ∈ E, ∀ v ∈ E, u ≠ v → 2 ≤ |u - v|) →
        (∀ u ∈ E,
          T + (menonHarmonicCaseIICells a : ℝ) / 2 ≤ u ∧
            u ≤ 2 * T - (menonHarmonicCaseIICells a : ℝ) / 2) →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let cells := menonHarmonicCaseIICells a
        let H := menonHarmonicCaseIISmoothingWidth a
        let sigma := menonHarmonicCaseIISigma Y
        let B := menonHarmonicCaseIIBudget C0 a Y
        let Q := 2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)
        (∀ u ∈ E,
          (((B + menonWideIntervalTransitionEnvelope (4 * Y) H) +
                primePowerDefectIoc a Y) /
              Real.log ((a + 1 : ℕ) : ℝ)) /
                ((a + 1 : ℕ) : ℝ) <
            ‖harmonicPrimeBlockPoly (primesRange a Y)
              (-u / (2 * Real.pi))‖) →
        let D : ℕ :=
          3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope (4 * Y)) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        (E.card : ℝ) * Vexp ^ 2 ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  obtain ⟨C0, hC0, hcase⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_orderFourHundred_narrow_smoothing_realFinset
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hcase, eventually_ge_atTop (256 : ℕ)] with a hcaseA ha256
  intro Y T E haY hYa hT hcellsT hsep hband h2T
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let sigma := menonHarmonicCaseIISigma Y
  let B := menonHarmonicCaseIIBudget C0 a Y
  have ha1 : 1 < a := by omega
  have hH : 0 < H := menonHarmonicCaseIISmoothingWidth_pos ha1
  have hlogOne : 1 ≤ Real.log (a : ℝ) := by
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    have hlog := Real.log_le_log (Real.exp_pos 1) (hexpThree.le.trans haThree)
    simpa using hlog
  have hHle : H ≤ 3 * (Y : ℝ) := by
    simp only [H, menonHarmonicCaseIISmoothingWidth]
    have hden : 1 ≤ (Real.log (a : ℝ)) ^ (20 : ℕ) := one_le_pow₀ hlogOne
    have hdiv : (a : ℝ) / (Real.log (a : ℝ)) ^ (20 : ℕ) ≤ (a : ℝ) :=
      div_le_self (Nat.cast_nonneg a) hden
    have haYR : (a : ℝ) ≤ (Y : ℝ) := by exact_mod_cast haY.le
    linarith
  have hsigma : 1 < sigma := menonHarmonicCaseIISigma_gt_one (show 0 < Y by omega)
  have hB : 0 ≤ B := menonHarmonicCaseIIBudget_nonneg hC0 ha1 (show 0 < Y by omega)
  have hcells : 0 < cells := menonHarmonicCaseIICells_pos ha1
  have hQeq := menonHarmonicCaseII_quotient_eq
    (C0 := C0) (a := a) (Y := Y) hC0 ha1 (show 0 < Y by omega)
  have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha1)
  have hQlt : (Real.log (a : ℝ)) ^ (-300 : ℝ) <
      2 * (Real.log (a : ℝ)) ^ (-300 : ℝ) := by
    have := Real.rpow_pos_of_pos hlog (-300 : ℝ)
    linarith
  dsimp only
  intro hlarge
  have hbound := hcaseA (Y := Y) (cells := cells) (H := H) (B := B)
    (sigma := sigma) (T := T) (E := E)
    haY hYa hH hHle hsigma hB hcells hT (by simpa only [cells] using hcellsT)
    (by simpa only [cells] using hsep) (by simpa only [cells] using hband)
    h2T (by rw [hQeq]; exact hQlt)
    (by simpa only [H, B] using hlarge)
  rw [hQeq] at hbound
  simpa only [cells, H, sigma, B] using hbound

set_option maxHeartbeats 800000 in
/-- A singleton violation of the canonical Case-II threshold contradicts the strict cardinal
budget, uniformly for every sufficiently late narrow block. -/
theorem exists_absolute_eventually_norm_harmonicPrimeBlock_le_threshold_of_caseII :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {Y : ℕ} {T u : ℝ},
        a < Y → Y ≤ 2 * a →
        1 ≤ T → (menonHarmonicCaseIICells a : ℝ) / 4 ≤ T →
        T + (menonHarmonicCaseIICells a : ℝ) / 2 ≤ u →
        u ≤ 2 * T - (menonHarmonicCaseIICells a : ℝ) / 2 →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        menonHarmonicCaseIIMeasureNumeratorConstant *
            menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ) *
            (Real.log (a : ℝ)) ^ (1855 : ℕ) * (T + 1) <
          (min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26)) ^ 2 →
        ‖harmonicPrimeBlockPoly (primesRange a Y)
              (-u / (2 * Real.pi))‖ ≤
          (((menonHarmonicCaseIIBudget C0 a Y +
                menonWideIntervalTransitionEnvelope (4 * Y)
                  (menonHarmonicCaseIISmoothingWidth a)) +
              primePowerDefectIoc a Y) /
            Real.log ((a + 1 : ℕ) : ℝ)) /
              ((a + 1 : ℕ) : ℝ) := by
  obtain ⟨C0, hC0, hscheduled⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_canonical_realFinset
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hscheduled, eventually_ge_atTop (256 : ℕ)] with a hsched ha256
  intro Y T u haY hYa hT hcellsT hbandLo hbandHi h2T hcross
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let sigma := menonHarmonicCaseIISigma Y
  let B := menonHarmonicCaseIIBudget C0 a Y
  let Q := 2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)
  let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
  by_contra hnot
  have hlarge :
      (((B + menonWideIntervalTransitionEnvelope (4 * Y) H) +
            primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
            ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) (-u / (2 * Real.pi))‖ :=
    lt_of_not_ge hnot
  have hcount := hsched (Y := Y) (T := T) (E := {u}) haY hYa hT hcellsT
    (by
      intro v hv z hz hvz
      simp only [Finset.mem_singleton] at hv hz
      exact absurd (hv.trans hz.symm) hvz)
    (by
      intro v hv
      simp only [Finset.mem_singleton] at hv
      subst v
      exact ⟨hbandLo, hbandHi⟩)
    h2T
    (by
      intro v hv
      simp only [Finset.mem_singleton] at hv
      subst v
      simpa only [H, B] using hlarge)
  have hcount0 := hcount
  dsimp only at hcount0
  have ha : 1 < a := by omega
  have hlog : 1 ≤ Real.log (a : ℝ) := by
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    have hlog' := Real.log_le_log (Real.exp_pos 1) (hexpThree.le.trans haThree)
    simpa using hlog'
  have hfactor := menonHarmonicCaseII_VexpFactor_lower ha256 hlog haY hYa
  let M : ℝ := min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26)
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hM0 : 0 ≤ M := le_min hT0 (by positivity)
  have hvLower :
      M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ)) ≤
        M / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
          ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
            (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
                (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8)) := by
    have hm := mul_le_mul_of_nonneg_left hfactor hM0
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hm
  have hden0 : 0 < menonHarmonicCaseIICoreDenominatorConstant *
      (Real.log (a : ℝ)) ^ (307 : ℕ) := by
    rw [menonHarmonicCaseIICoreDenominatorConstant]
    positivity
  have hvLower0 : 0 ≤
      M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ)) := div_nonneg hM0 hden0.le
  have hsqLower :
      (M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ))) ^ 2 ≤
        (M / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
          ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
            (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
                (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8))) ^ 2 :=
    pow_le_pow_left₀ hvLower0 hvLower 2
  have hcountAmp :
      (M / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
          ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
            (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
                (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8))) ^ 2 ≤
      (((cells : ℝ) * (D : ℝ) * 12) *
        ((12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log
                (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma)))) := by
    simpa only [Finset.card_singleton, Nat.cast_one, one_mul, Nat.cast_mul,
      Nat.cast_ofNat, cells, H, sigma, B, Q, D, M] using hcount0
  have hcount' :
      (M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ))) ^ 2 ≤
      (((cells : ℝ) * (D : ℝ) * 12) *
        ((12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log
                (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma)))) :=
    hsqLower.trans hcountAmp
  have hstrict := menonHarmonicCaseII_countNumerator_lt_scaledAmplitude ha256 hlog
    haY hYa hT (M := M) (by simpa only [M] using hcross)
  have hstrict' :
      (((cells : ℝ) * (D : ℝ) * 12) *
        ((12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log
                (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma)))) <
        (M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ))) ^ 2 := by
    simpa only [cells, D, sigma] using hstrict
  exact (not_lt_of_ge hcount') hstrict'

private theorem norm_harmonicPrimeBlockPoly_eq_neg_abs_generic (B : Finset ℕ) (w : ℝ) :
    ‖harmonicPrimeBlockPoly B w‖ = ‖harmonicPrimeBlockPoly B (-|w|)‖ := by
  rcases le_total w 0 with hw | hw
  · simp only [abs_of_nonpos hw, neg_neg]
  · rw [abs_of_nonneg hw]
    exact (norm_harmonicPrimeBlockPoly_neg B w).symm

set_option maxHeartbeats 800000 in
/-- Uniform logarithmic Case-II pointwise bound for every sufficiently late narrow prime block. -/
theorem exists_absolute_eventually_norm_harmonicPrimeBlock_le_logPow_of_caseII_range :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {Y : ℕ}, a < Y → Y ≤ 2 * a →
        ∀ w : ℝ,
        menonHarmonicCaseIIFrequencyFloor a ≤ 2 * Real.pi * |w| →
        2 * Real.pi * |w| ≤ menonHarmonicCaseIIFrequencyCeiling a →
        ‖harmonicPrimeBlockPoly (primesRange a Y) w‖ ≤
          menonHarmonicCaseIIThresholdConstant C0 /
            (Real.log (a : ℝ)) ^ (20 : ℕ) := by
  obtain ⟨C0, hC0, hcaseII⟩ :=
    exists_absolute_eventually_norm_harmonicPrimeBlock_le_threshold_of_caseII
  have hthreshold := eventually_menonHarmonicCaseII_threshold_le C0 hC0
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hcaseII, hthreshold, eventually_ge_atTop (256 : ℕ)] with
      a hcase hthresholdA ha256
  intro Y haY hYa w hfloor hceiling
  let u : ℝ := 2 * Real.pi * |w|
  have ha1 : 1 ≤ a := by omega
  have hlog : 1 ≤ Real.log (a : ℝ) := by
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    have hlog' := Real.log_le_log (Real.exp_pos 1) (hexpThree.le.trans haThree)
    simpa using hlog'
  have hgeometry := menonHarmonicCaseII_scalar_geometry ha1 hlog
    (u := u) (by simpa only [u] using hfloor) (by simpa only [u] using hceiling)
  rcases hgeometry with ⟨hT, hcellsT, hbandLo, hbandHi, h2T, hcross⟩
  let T : ℝ := 2 * u / 3
  have hblock := hcase (Y := Y) (T := T) (u := u) haY hYa
    (by simpa only [T] using hT)
    (by simpa only [T] using hcellsT)
    (by simpa only [T] using hbandLo)
    (by simpa only [T] using hbandHi)
    (by simpa only [T] using h2T)
    (by simpa only [T, menonHarmonicCaseIICrossConstant] using hcross)
  have hsmall := hblock.trans (hthresholdA haY hYa)
  have hfreq : -u / (2 * Real.pi) = -|w| := by
    dsimp only [u]
    field_simp
  rw [hfreq] at hsmall
  rw [norm_harmonicPrimeBlockPoly_eq_neg_abs_generic]
  exact hsmall

end

end RHTower.Sieve
