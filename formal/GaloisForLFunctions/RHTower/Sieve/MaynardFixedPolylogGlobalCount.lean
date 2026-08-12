import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogAmplitudeFibre
import GaloisForLFunctions.RHTower.Sieve.MaynardLabelAbsorption

/-!
# Global high-amplitude count with moving endpoint

All selected-label fibres are summed before spending the moving Route-T reserve.  Thus one and the
same fixed-polylog absorption pays coefficient energy and complete degree-60 label multiplicity,
leaving Maynard's first-alternative exponent with no residual color factor.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

def maynardFixedPolylogGlobalConstant : ℝ :=
  (2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant) *
    maynardLabelPolylogConstant

theorem maynardFixedPolylogGlobalConstant_pos :
    0 < maynardFixedPolylogGlobalConstant := by
  dsimp only [maynardFixedPolylogGlobalConstant, maynardLabelPolylogConstant]
  positivity [maynardRaisedWidthConstant_one_le]

/-- **Global moving-endpoint first alternative.**  Given the literal selected coloring, every
high-amplitude ordinate below the Route-T boundary obeys the complete Maynard cardinal target.
Energy, raising, labels, and their fixed polylogarithms are all discharged internally. -/
theorem eventually_card_le_maynard_first_alternative_of_high_amplitude_coloring (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {t e mu c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L → (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * t) →
      1 / 2 ≤ c → 99 / 100 ≤ alpha →
      alpha ≤ 1 - routeTEndpointGlobalDeficit A T →
      4 / 3 ≤ mu → mu ≤ 19 / 9 → t = mu / 120 → e = alpha - c →
      0 < delta →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      ∀ (color : ℕ → HeathBrownSelectionLabel L X 60),
      (∀ r ∈ S,
        IsHeathBrownEligibleSelection L X 60
          (T0 := T) (t := t) (e := e)
          ((c : ℂ) + (lam r : ℝ) * Complex.I) (color r)) →
      (S.card : ℝ) ≤
        maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha)) := by
  let C0 : ℝ := 2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant
  let CG : ℝ := maynardFixedPolylogGlobalConstant
  filter_upwards [eventually_isMaynardFixedAmplitudeEnergyScaleReady,
    eventually_maynardFixedPolylogTotalCost_absorbed
      A CG maynardFixedPolylogGlobalConstant_pos 120,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hready habsorb hlogT
  intro L X K t e mu c alpha delta hX hL hXscale hLscale hc
    halpha_lo halpha_hi hmu_lo hmu_hi ht he hdelta S hS lam hgap hdiam color hcolor
  have hTpos : 0 < T := by linarith [hready.1]
  have hHFpos : 0 < maynardHarmonicFactor K delta :=
    maynardHarmonicFactor_pos K hdelta
  have hlabel := heathBrownSelectionLabel_sixty_polylog_bound
    hTpos hlogT hmu_hi ht hX hL hXscale hLscale
  let nlabels : ℝ := Fintype.card (HeathBrownSelectionLabel L X 60)
  have hnlabelsPos : 0 < nlabels := by
    dsimp only [nlabels]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (nonempty_heathBrownSelectionLabel L X 60 (by norm_num))
  have hlabel' : nlabels ≤
      maynardLabelPolylogConstant * (Real.log T) ^ 120 := by
    simpa only [nlabels, maynardLabelPolylogConstant] using hlabel
  have hgap0 : 0 ≤ 1 - alpha := by
    have hd := routeTEndpointGlobalDeficit_pos A (T := T) (by linarith [hready.1])
    linarith
  have htarget0 : 0 ≤ maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha)) :=
    mul_nonneg hHFpos.le (Real.rpow_nonneg hTpos.le _)
  have hfibre : ∀ label : HeathBrownSelectionLabel L X 60,
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
        maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha)) := by
    intro label
    let Sf : Finset ℕ := S.filter fun r => color r = label
    by_cases hSf : Sf.Nonempty
    · have hSfS : Sf ⊆ S := Finset.filter_subset _ _
      have hSfRange : Sf ⊆ Finset.range K := hSfS.trans hS
      have hSfDiam : ∀ r ∈ Sf, ∀ s ∈ Sf, |lam s - lam r| ≤ T := by
        intro r hr s hs
        exact hdiam r (hSfS hr) s (hSfS hs)
      have hSfSelection : ∀ r ∈ Sf,
          IsHeathBrownEligibleSelection L X 60
            (T0 := T) (t := t) (e := e)
            ((c : ℂ) + (lam r : ℝ) * Complex.I) label := by
        intro r hr
        have hrS := hSfS hr
        have hrcolor : color r = label := (Finset.mem_filter.mp hr).2
        simpa only [hrcolor] using hcolor r hrS
      obtain ⟨ell, hell, hell51, hYlo, hYhi, hHuxley⟩ :=
        huxley_maynardEligibleSelection_fibre_at_high_amplitude
          L X K hready (by linarith) halpha_lo hmu_lo hmu_hi ht he
          label Sf hSf hSfRange lam hdelta hgap hSfDiam hSfSelection
      let N : ℕ :=
        (groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell
      let p : ℕ :=
        2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
          (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)
      let PL : ℝ :=
        (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ p
      have hN : 1 ≤ N := by
        dsimp only [N]
        exact Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
      have hNscale : (N : ℝ) ≤ T ^ (1367 / 2160 : ℝ) := by
        simpa only [N] using hYhi
      have hp : p ≤ maynardFixedPolylogExponentBound := by
        dsimp only [p]
        exact heathBrownSelected_fixedPolylogExponent_le label hell51
      have htotal := habsorb N hN hNscale p hp
      have hreserveSlope := maynard_fixedPolylog_huxley_reserve_of_endpoint_deficit
        hmu_lo (routeTEndpointGlobalDeficit_pos A (T := T)
          (by linarith [hready.1])).le halpha_hi
      have hreservePow := Real.rpow_le_rpow_of_exponent_le hready.1.le hreserveSlope
      have htotalReserve :
          CG * (Real.log T) ^ 120 * PL ≤
            T ^ ((mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha)) := by
        have htotal' : CG * (Real.log T) ^ 120 * PL ≤
            T ^ ((73 / 1080 : ℝ) * routeTEndpointGlobalDeficit A T) := by
          simpa only [PL] using htotal
        exact htotal'.trans hreservePow
      have hC00 : 0 ≤ C0 := by
        dsimp only [C0]
        exact mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg _))
          (le_trans (by norm_num) maynardRaisedWidthConstant_one_le)
      have hPL0 : 0 ≤ PL := by
        dsimp only [PL]
        exact pow_nonneg (by
          have hwidthN : 1 ≤ maynardRaisedWidthConstant * (N : ℝ) :=
            one_le_mul_of_one_le_of_one_le maynardRaisedWidthConstant_one_le
              (by exact_mod_cast hN)
          linarith [Real.log_nonneg hwidthN]) p
      have hcoeff : nlabels * C0 * PL ≤
          T ^ ((mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha)) := by
        calc
          nlabels * C0 * PL ≤
              (maynardLabelPolylogConstant * (Real.log T) ^ 120) * C0 * PL :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hlabel' hC00) hPL0
          _ = CG * (Real.log T) ^ 120 * PL := by
            dsimp only [CG, C0, maynardFixedPolylogGlobalConstant]
            ring
          _ ≤ T ^ ((mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha)) := htotalReserve
      have hcount := card_le_of_huxley_at_amplitude_with_fixed_polylog
        hready.1 hc (by linarith) hdelta label Sf ell hell hell51 hYlo hYhi hHuxley
      have hpow0 : 0 ≤ T ^ ((1367 / 2160 : ℝ) * (2 - 2 * alpha)) :=
        Real.rpow_nonneg hTpos.le _
      calc
        nlabels * (((Sf.card : ℕ) : ℝ)) ≤
            nlabels * (C0 * maynardHarmonicFactor K delta * PL *
              T ^ ((1367 / 2160 : ℝ) * (2 - 2 * alpha))) := by
          apply mul_le_mul_of_nonneg_left
          · simpa only [C0, PL, N, p] using hcount
          · exact hnlabelsPos.le
        _ = maynardHarmonicFactor K delta *
            ((nlabels * C0 * PL) *
              T ^ ((1367 / 2160 : ℝ) * (2 - 2 * alpha))) := by ring
        _ ≤ maynardHarmonicFactor K delta *
            (T ^ ((mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha)) *
              T ^ ((1367 / 2160 : ℝ) * (2 - 2 * alpha))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hcoeff hpow0) hHFpos.le
        _ = maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha)) := by
          rw [← Real.rpow_add hTpos]
          congr 2
          ring
    · have hzero : Sf.card = 0 := Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hSf)
      rw [hzero]
      norm_num
      exact htarget0
  have hcardCast : (S.card : ℝ) =
      ∑ label : HeathBrownSelectionLabel L X 60,
        (((S.filter fun r => color r = label).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  have hsum : nlabels * (S.card : ℝ) ≤
      nlabels * (maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha))) := by
    rw [hcardCast, mul_sum]
    calc
      ∑ label : HeathBrownSelectionLabel L X 60,
          nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
          ∑ _label : HeathBrownSelectionLabel L X 60,
            (maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha))) :=
        Finset.sum_le_sum fun label _ => hfibre label
      _ = nlabels * (maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum

end RHTower.Sieve
