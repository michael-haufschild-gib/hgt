import GaloisForLFunctions.RHTower.Sieve.MaynardEnergyEnvelope
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectionFibreHuxley

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

def IsMaynardEnergyScaleReady (T : ℝ) : Prop :=
  1 < T ∧
    2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant *
        maynardEnergyEnvelopeConstant ≤ T ^ (31 / 640 : ℝ)

theorem eventually_isMaynardEnergyScaleReady :
    ∀ᶠ T : ℝ in Filter.atTop, IsMaynardEnergyScaleReady T := by
  simpa [IsMaynardEnergyScaleReady] using
    eventually_maynard_huxley_energy_scalar_ready maynardUniformEnergyConstant

theorem card_heathBrownSelectedFactor_sixty_le
    {L X : ℕ} (label : HeathBrownSelectionLabel L X 60) :
    Fintype.card (HeathBrownSelectedFactor label) ≤ 120 := by
  have hm : label.1.m < 60 := label.1.1.isLt
  simpa [HeathBrownSelectedFactor] using
    (card_selected_heathBrown_group_le_120 hm (u := label.2))

theorem heathBrownSelectedRaisedEnergy_scale_of_ready
    (L X : ℕ) (label : HeathBrownSelectionLabel L X 60)
    {T : ℝ} (hready : IsMaynardEnergyScaleReady T)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (hYlo : T ^ (9 / 16 : ℝ) ≤
      ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ)) :
    2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) ^ 2 *
        heathBrownSelectedRaisedEnergy label ell *
        (1 + 256 * (Real.sqrt T +
          8 * Real.sqrt
            ((((groupedDyadicUpper (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ≤
      ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) ^ 2 := by
  have henergy := sum_normSq_convPow_heathBrownGrouped_le_subcritical
    (card_heathBrownSelectedFactor_sixty_le label) ell hell hell51
      L X (heathBrownSelectedKind label) (heathBrownSelectedExponent label)
  have hscale := maynard_huxley_energy_scale_of_subcritical_energy
    (groupedDyadicLower (heathBrownSelectedExponent label))
    (Fintype.card (HeathBrownSelectedFactor label)) ell hready.1
      maynardUniformEnergyConstant_pos.le
      (heathBrownSelectedRaisedEnergy_nonneg label ell)
      (card_heathBrownSelectedFactor_sixty_le label) hell hell51 hYlo henergy hready.2
  rw [← groupedDyadicUpper_eq_lower_mul_twoPow
    (heathBrownSelectedExponent label)] at hscale
  exact hscale

theorem huxley_maynardEligibleSelection_fibre_ready
    (L X K : ℕ) {T0 t e mu sigma delta : ℝ}
    (hready : IsMaynardEnergyScaleReady T0) (hsigma : 0 ≤ sigma)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (he : e = 1 - sigma)
    (label : HeathBrownSelectionLabel L X 60)
    (S : Finset ℕ) (hSne : S.Nonempty) (hS : S ⊆ Finset.range K)
    (lam : ℕ → ℝ) (hdelta : 0 < delta)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T0)
    (hselection : ∀ r ∈ S,
      IsHeathBrownEligibleSelection L X 60
        (T0 := T0) (t := t) (e := e)
        ((sigma : ℂ) + (lam r : ℝ) * Complex.I) label) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 51 ∧
      T0 ^ (9 / 16 : ℝ) ≤
        ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) ∧
      (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
        T0 ^ (1367 / 2160 : ℝ) ∧
      (S.card : ℝ) *
          (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
            (1 - sigma)) ^ 2) ≤
        2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) *
          ∑ r : Fin (Fintype.card (HeathBrownSelectedFactor label) * ell + 1),
            ((((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-sigma)) ^ 2 *
              heathBrownSelectedRaisedEnergy label ell *
              (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                  2 ^ (r : ℕ) : ℕ) : ℝ)) +
                (12 * Real.pi *
                  ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                    2 ^ (r : ℕ) : ℕ) : ℝ)) / delta) *
                  ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))) := by
  apply huxley_maynardEligibleSelection_fibre_canonical
    L X 60 K hready.1 hsigma hmu_lo hmu_hi ht he label S hSne hS
      lam hdelta hgap hdiam hselection
  intro ell hell hell51 hYlo
  exact heathBrownSelectedRaisedEnergy_scale_of_ready
    L X label hready ell hell hell51 hYlo

end RHTower.Sieve
