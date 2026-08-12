import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogEndpointAbsorption
import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeEnergyScalar
import GaloisForLFunctions.RHTower.Sieve.MaynardArbitraryEnergy

/-!
# Literal high-amplitude fibres with fixed-polylog counting

A single fixed auxiliary energy exponent is used only to establish the Huxley square-scale gate
throughout `alpha ≥ 99/100`.  The subsequent count uses the exact fixed-divisor polylogarithm, so
no auxiliary power loss enters the moving endpoint reserve.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Fixed high-amplitude energy gate.  Its constant is independent of endpoint deficit. -/
def IsMaynardFixedAmplitudeEnergyScaleReady (T : ℝ) : Prop :=
  1 < T ∧
    2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant (1 / 100) *
      maynardEnergyEnvelopeConstant ≤ T ^ (9 / 320 : ℝ)

theorem eventually_isMaynardFixedAmplitudeEnergyScaleReady :
    ∀ᶠ T : ℝ in atTop, IsMaynardFixedAmplitudeEnergyScaleReady T := by
  have hpow : Tendsto (fun T : ℝ => T ^ (9 / 320 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hpow.eventually_ge_atTop
      (2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant (1 / 100) *
        maynardEnergyEnvelopeConstant)] with T hT hconst
  exact ⟨hT, hconst⟩

/-- Fixed-energy square-scale closure for every Route-T high-amplitude cell. -/
theorem heathBrownSelectedRaisedEnergy_scale_at_high_amplitude
    (L X : ℕ) (label : HeathBrownSelectionLabel L X 60)
    {T alpha : ℝ} (hready : IsMaynardFixedAmplitudeEnergyScaleReady T)
    (halpha : 99 / 100 ≤ alpha)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (hYlo : T ^ (9 / 16 : ℝ) ≤
      ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ)) :
    2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) ^ 2 *
        heathBrownSelectedRaisedEnergy label ell *
        (1 + 256 * (Real.sqrt T +
          8 * Real.sqrt
            ((((groupedDyadicUpper
              (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ≤
      ((((groupedDyadicLower
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) ^ (2 * alpha) := by
  have hrho : (0 : ℝ) < 1 / 100 := by norm_num
  have henergy := sum_normSq_convPow_heathBrownGrouped_le_arbitrary_subcritical
    hrho (card_heathBrownSelectedFactor_sixty_le label) ell hell hell51
      L X (heathBrownSelectedKind label) (heathBrownSelectedExponent label)
  have hexp : (9 / 16 : ℝ) * (1 / 20) = 9 / 320 := by norm_num
  have hscale := maynard_huxley_energy_scale_at_amplitude
    (groupedDyadicLower (heathBrownSelectedExponent label))
    (Fintype.card (HeathBrownSelectedFactor label)) ell
    hready.1 (maynardVariableUniformEnergyConstant_pos (1 / 100)).le
    (heathBrownSelectedRaisedEnergy_nonneg label ell)
    (card_heathBrownSelectedFactor_sixty_le label) hell hell51 hYlo henergy
    (gamma := 1 / 20) (rho := 1 / 100) (alpha := alpha)
    (by norm_num) (by linarith) (by simpa only [hexp] using hready.2)
  simpa only [groupedDyadicUpper_eq_lower_mul_twoPow] using hscale

/-- A literal selected Perron fibre in the high-amplitude band satisfies the raised Huxley
inequality with independent abscissa `c` and amplitude `alpha`. -/
theorem huxley_maynardEligibleSelection_fibre_at_high_amplitude
    (L X K : ℕ) {T t e mu c alpha delta : ℝ}
    (hready : IsMaynardFixedAmplitudeEnergyScaleReady T)
    (hc : 0 ≤ c) (halpha : 99 / 100 ≤ alpha)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (he : e = alpha - c)
    (label : HeathBrownSelectionLabel L X 60)
    (S : Finset ℕ) (hSne : S.Nonempty) (hS : S ⊆ Finset.range K)
    (lam : ℕ → ℝ) (hdelta : 0 < delta)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T)
    (hselection : ∀ r ∈ S,
      IsHeathBrownEligibleSelection L X 60
        (T0 := T) (t := t) (e := e)
        ((c : ℂ) + (lam r : ℝ) * Complex.I) label) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 51 ∧
      T ^ (9 / 16 : ℝ) ≤
        ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) ∧
      (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
        T ^ (1367 / 2160 : ℝ) ∧
      (S.card : ℝ) *
          (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
            (alpha - c)) ^ 2) ≤
        2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) *
          ∑ r : Fin (Fintype.card (HeathBrownSelectedFactor label) * ell + 1),
            ((((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-c)) ^ 2 *
              heathBrownSelectedRaisedEnergy label ell *
              (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                  2 ^ (r : ℕ) : ℕ) : ℝ)) +
                (12 * Real.pi *
                  ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                    2 ^ (r : ℕ) : ℕ) : ℝ)) / delta) *
                  ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))) := by
  apply huxley_maynardEligibleSelection_fibre_at_amplitude
    L X 60 K hready.1 hc hmu_lo hmu_hi ht he label S hSne hS
      lam hdelta hgap hdiam hselection
  intro ell hell hell51 hYlo
  exact heathBrownSelectedRaisedEnergy_scale_at_high_amplitude
    L X label hready halpha ell hell hell51 hYlo

/-- **Moving-endpoint selected-fibre count.**  Every nonempty literal Perron fibre below the
Route-T endpoint boundary satisfies Maynard's first-alternative target, uniformly as that boundary
tends to one. -/
theorem eventually_card_le_maynard_first_alternative_of_selected_fibre (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {t e mu c alpha delta : ℝ},
      1 / 2 ≤ c → 99 / 100 ≤ alpha → alpha ≤ 1 - routeTEndpointGlobalDeficit A T →
      4 / 3 ≤ mu → mu ≤ 19 / 9 → t = mu / 120 → e = alpha - c →
      0 < delta →
      ∀ (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ),
      S.Nonempty → S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S,
        IsHeathBrownEligibleSelection L X 60
          (T0 := T) (t := t) (e := e)
          ((c : ℂ) + (lam r : ℝ) * Complex.I) label) →
      (S.card : ℝ) ≤
        maynardHarmonicFactor K delta * T ^ (mu * (1 - alpha)) := by
  filter_upwards [eventually_isMaynardFixedAmplitudeEnergyScaleReady,
    eventually_maynard_fixedPolylog_fibre_reserve A] with T hready hreserve
  intro L X K t e mu c alpha delta hc halpha_lo halpha_hi
    hmu_lo hmu_hi ht he hdelta label S hSne hS lam hgap hdiam hselection
  obtain ⟨ell, hell, hell51, hYlo, hYhi, hHuxley⟩ :=
    huxley_maynardEligibleSelection_fibre_at_high_amplitude
      L X K hready (by linarith) halpha_lo hmu_lo hmu_hi ht he
      label S hSne hS lam hdelta hgap hdiam hselection
  have hcost := hreserve label ell hell hell51 hYhi mu alpha hmu_lo halpha_hi
  have halpha_one : alpha ≤ 1 := by
    have hd := routeTEndpointGlobalDeficit_pos A (T := T)
      (by linarith [hready.1])
    linarith
  exact card_le_maynard_first_alternative_of_huxley_at_amplitude_with_fixed_polylog
    hready.1 hc halpha_one hdelta label S ell hell hell51 hYlo hYhi hHuxley hcost

end RHTower.Sieve
