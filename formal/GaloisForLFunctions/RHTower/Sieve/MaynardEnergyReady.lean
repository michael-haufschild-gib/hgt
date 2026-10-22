import GaloisForLFunctions.RHTower.Sieve.MaynardEnergyEnvelope
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectionFibreHuxley

/-!
# Energy-ready heights and the Huxley estimate on a selection fibre

This module defines the scalar readiness predicate `IsMaynardEnergyScaleReady T`, namely `1 < T`
and `2 · 6121^2 · C_E · C_env ≤ T^{31/640}`, and shows it holds for all large `T`. At such a
height, the raised coefficient energy `E_ℓ` of a degree-60 selected factor group (at most `120`
factors) satisfies the scale inequality required by the canonical Huxley estimate, so on any color
fibre of well-spaced ordinates the number of points obeys an explicit Huxley-type large-values
bound.

## Main results

- `IsMaynardEnergyScaleReady`: the energy scale predicate.
- `eventually_isMaynardEnergyScaleReady`: it holds for all sufficiently large `T`.
- `heathBrownSelectedRaisedEnergy_scale_of_ready`: for `1 ≤ ℓ ≤ 51` and `T^{9/16} ≤ Y^ℓ` (`Y` the
  grouped lower edge), `2 (|u| ℓ + 1)^2 E_ℓ (1 + 256 (√T + 8 √(Y_up^ℓ))) ≤ (Y^ℓ)^2`.
- `huxley_maynardEligibleSelection_fibre_ready`: for a fibre `S` of `δ`-spaced ordinates of
  diameter `≤ T0` sharing one eligible selection label, some `ℓ ∈ [1, 51]` has
  `T0^{9/16} ≤ Y^ℓ ≤ T0^{1367/2160}` and an explicit bound on `|S| (Y^ℓ)^{2(1-σ)}` by the raised
  energy times `Y^ℓ 2^r + 12π Y^ℓ 2^r / δ · ∑_{i<K} 1/(i+1)`, summed over dyadic shifts.

## Hypotheses

`eventually_isMaynardEnergyScaleReady` is unconditional. The other results are conditional on the
Prop-valued premise `IsMaynardEnergyScaleReady T` (explicit scalar inequalities that hold for all
large `T`). The fibre estimate also assumes `σ ≥ 0`, `4/3 ≤ μ ≤ 19/9`, `t = μ/120`, `e = 1 - σ`,
a nonempty `S ⊆ {0, …, K-1}`, spacing `λ_i + δ ≤ λ_{i+1}` with `δ > 0`, diameter `≤ T0`, and that
every ordinate in `S` is an eligible selection for the given label.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Energy scale readiness: `1 < T` and `2 · 6121^2 · maynardUniformEnergyConstant ·
maynardEnergyEnvelopeConstant ≤ T^{31/640}`. -/
def IsMaynardEnergyScaleReady (T : ℝ) : Prop :=
  1 < T ∧
    2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant *
        maynardEnergyEnvelopeConstant ≤ T ^ (31 / 640 : ℝ)

/-- Energy scale readiness holds for all sufficiently large real `T`. -/
theorem eventually_isMaynardEnergyScaleReady :
    ∀ᶠ T : ℝ in Filter.atTop, IsMaynardEnergyScaleReady T := by
  simpa [IsMaynardEnergyScaleReady] using
    eventually_maynard_huxley_energy_scalar_ready maynardUniformEnergyConstant

/-- A selected factor group in a degree-60 Heath-Brown box has at most `120` factors. -/
theorem card_heathBrownSelectedFactor_sixty_le
    {L X : ℕ} (label : HeathBrownSelectionLabel L X 60) :
    Fintype.card (HeathBrownSelectedFactor label) ≤ 120 := by
  have hm : label.1.m < 60 := label.1.1.isLt
  simpa [HeathBrownSelectedFactor] using
    (card_selected_heathBrown_group_le_120 hm (u := label.2))

/-- Energy scale inequality at a ready height: assuming `IsMaynardEnergyScaleReady T`,
`1 ≤ ℓ ≤ 51` and `T^{9/16} ≤ Y^ℓ`, the raised energy satisfies
`2 (|u| ℓ + 1)^2 E_ℓ (1 + 256 (√T + 8 √(Y_up^ℓ))) ≤ (Y^ℓ)^2`. -/
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

/-- Huxley estimate on one selection fibre. Assuming `IsMaynardEnergyScaleReady T0`, the scale
ranges, `δ`-spaced ordinates of diameter `≤ T0` that are all eligible selections for one label,
some raise `ℓ ∈ [1, 51]` with `T0^{9/16} ≤ Y^ℓ ≤ T0^{1367/2160}` bounds `|S| (Y^ℓ)^{2(1-σ)}`. -/
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
