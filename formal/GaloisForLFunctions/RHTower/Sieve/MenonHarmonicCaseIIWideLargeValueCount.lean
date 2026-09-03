import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownWideVariableUpperAggregate
import GaloisForLFunctions.RHTower.Sieve.MenonPrimeTwistRangeReverseAbel

/-!
# Wide-smoothed Case-II count for harmonic prime blocks

Reverse Abel selects a variable sharp endpoint.  One common transition envelope dominates both
wide smoothing errors for every endpoint, so the existing finite Case-II label and receiver remain
uniform.
-/

namespace RHTower.Sieve

noncomputable section

open Filter

/-- Uniform cost of the two common-width transition windows below cutoff `X`. -/
def menonWideIntervalTransitionEnvelope (X : ℕ) (H : ℝ) : ℝ :=
  2 * (H + 1) * Real.log (X : ℝ)

/-- The two endpoint errors of every subinterval below `X` are bounded by the common transition
envelope. -/
theorem menonWideInterval_transition_le_envelope
    {X a b : ℕ} {H : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hH : 0 < H) (hsupport : (b : ℝ) + H ≤ (X : ℝ)) :
    (H + 1) * Real.log ((b : ℝ) + H) +
        (H + 1) * Real.log ((a : ℝ) + H) ≤
      menonWideIntervalTransitionEnvelope X H := by
  have haPos : (0 : ℝ) < (a : ℝ) + H := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hbPos : (0 : ℝ) < (b : ℝ) + H := by
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have haX : (a : ℝ) + H ≤ (X : ℝ) := by
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have hlogA : Real.log ((a : ℝ) + H) ≤ Real.log (X : ℝ) :=
    Real.log_le_log haPos haX
  have hlogB : Real.log ((b : ℝ) + H) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hbPos hsupport
  have hcoef : 0 ≤ H + 1 := by linarith
  have hA := mul_le_mul_of_nonneg_left hlogA hcoef
  have hB := mul_le_mul_of_nonneg_left hlogB hcoef
  dsimp only [menonWideIntervalTransitionEnvelope]
  linarith

/-- Large values of one actual harmonic prime block satisfy the explicit wide-smoothed Case-II
cardinality bound.  Reverse Abel and every endpoint-dependent transition are internal. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide
    (A : ℝ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X Y cells : ℕ} {T0 t H B sigma V Δ T : ℝ}
          {S : Finset ℕ} {w : ℕ → ℝ},
        1 ≤ X → a < Y → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
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
        0 < Q →
        0 ≤ A →
        menonHeathBrownCaseIIAbsorptionEnvelope A L X a < Q →
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
  obtain ⟨C0, hC0, haggregate⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHeathBrownCaseII_variableUpper_wide A
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [haggregate] with a haAggregate
  intro L X Y cells T0 t H B sigma V Δ T S w hX haY hXL hT0 hscale ha hL
    hH hYX hsigma hB hV hΔ hcells hgrid hbaseGap hT hΔT hbaseBand h2T
  dsimp only
  intro hQ hA habsorb hlarge
  have haOne : 1 ≤ a := by
    have haReal : (1 : ℝ) ≤ (a : ℝ) := (by norm_num : (1 : ℝ) ≤ 64 ^ 8).trans ha
    exact_mod_cast haReal
  have hXlog : 0 ≤ Real.log (X : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hX)
  have htransition : 0 ≤ menonWideIntervalTransitionEnvelope X H := by
    dsimp only [menonWideIntervalTransitionEnvelope]
    positivity
  have hrawNonneg : 0 ≤ B + menonWideIntervalTransitionEnvelope X H :=
    add_nonneg hB htransition
  have hprefix : ∀ r : ℕ, r ∈ S →
      ∃ m ∈ Finset.Ioc a Y,
        B + menonWideIntervalTransitionEnvelope X H <
          ‖∑ n ∈ Finset.Ioc a m,
            vonMangoldtTwist (-(2 * Real.pi * w r)) n‖ := by
    intro r hr
    exact exists_norm_vonMangoldtTwist_Ioc_gt_of_harmonicPrimeBlockPoly_gt
      haOne haY (fun p => mem_primesRange) (w r) hrawNonneg (hlarge r hr)
  choose selectedUpper hupper hupperLarge using hprefix
  let upper : ℕ → ℕ := fun r => if hr : r ∈ S then selectedUpper r hr else a
  let tau : ℕ → ℝ := fun r => -(2 * Real.pi * w r)
  have hupperLo : ∀ r ∈ S, a ≤ upper r := by
    intro r hr
    simpa only [upper, dif_pos hr] using (Finset.mem_Ioc.mp (hupper r hr)).1.le
  have hupperHi : ∀ r ∈ S, upper r ≤ Y := by
    intro r hr
    simpa only [upper, dif_pos hr] using (Finset.mem_Ioc.mp (hupper r hr)).2
  have hsharp : ∀ r ∈ S, B +
      ((H + 1) * Real.log (((upper r : ℕ) : ℝ) + H) +
        (H + 1) * Real.log ((a : ℝ) + H)) <
      ‖∑ n ∈ Finset.Ioc a (upper r), vonMangoldtTwist (tau r) n‖ := by
    intro r hr
    have hsupportR : (((upper r : ℕ) : ℝ) + H) ≤ (X : ℝ) := by
      have hupperY : upper r ≤ Y := hupperHi r hr
      have hupperYR : ((upper r : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hupperY
      linarith
    have herror := menonWideInterval_transition_le_envelope haOne (hupperLo r hr)
      hH hsupportR
    have hraw := hupperLarge r hr
    have hBE : B +
        ((H + 1) * Real.log (((upper r : ℕ) : ℝ) + H) +
          (H + 1) * Real.log ((a : ℝ) + H)) ≤
        B + menonWideIntervalTransitionEnvelope X H := by
      linarith
    simpa only [upper, dif_pos hr, tau] using hBE.trans_lt hraw
  obtain ⟨_, _, _, hbound⟩ :=
    haAggregate hX hXL hT0 hscale ha hL hH hYX hsigma hV hΔ hcells hgrid
      hupperLo hupperHi (by simpa only [tau] using hbaseGap) hT hΔT
      (by simpa only [tau] using hbaseBand) h2T (by simpa using hQ) hA habsorb hsharp
  exact hbound

end

end RHTower.Sieve
