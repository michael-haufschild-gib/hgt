import GaloisForLFunctions.RHTower.Sieve.MaynardReadyColoring
import GaloisForLFunctions.RHTower.Sieve.MaynardEnergyReady

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

def IsMaynardRouteTScaleReady (T : ℝ) : Prop :=
  IsMaynardLongScaleReady T ∧ IsMaynardEnergyScaleReady T

theorem eventually_isMaynardRouteTScaleReady :
    ∀ᶠ T : ℝ in Filter.atTop, IsMaynardRouteTScaleReady T := by
  filter_upwards [eventually_isMaynardLongScaleReady,
    eventually_isMaynardEnergyScaleReady] with T hlong henergy
  exact ⟨hlong, henergy⟩

def IsMaynardSelectionFibreHuxleyConclusion
    {L X K : ℕ} {T0 sigma delta : ℝ}
    (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ) : Prop :=
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
                ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)))

/-- **Route-T ready-scale capstone through Huxley.**  One canonical degree-`60` cutoff colors
every large ordinate.  Every nonempty color fibre then satisfies the fully explicit weighted
Huxley estimate, with no long-factor, cutoff, raising, energy, or absorption hypothesis. -/
theorem exists_canonical_sixty_coloring_with_huxley_fibres_of_ready_scale
    {X K : ℕ} {T0 t mu sigma V delta : ℝ}
    (hready : IsMaynardRouteTScaleReady T0)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 0 ≤ sigma) (hV : 0 < V) (hdelta : 0 < delta)
    (S : Finset ℕ) (hS : S ⊆ Finset.range K) (lam : ℕ → ℝ)
    (hband : ∀ r ∈ S, T0 ≤ lam r ∧ lam r ≤ 2 * T0)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T0)
    (haggregate : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      ∀ r ∈ S, V ≤ ‖heathBrownEligibleDyadicAggregate L X 60 T0 t
        ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖)
    (hreserve : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      ∀ c : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T0 t c →
          heathBrownEligibleBoxCost L X 60 *
            (groupedDyadicLower
              (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤ V) :
    ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧ (L : ℝ) ≤ T0 ^ (2 * t) ∧
      ∃ color : ℕ → HeathBrownSelectionLabel L X 60,
        (∀ r ∈ S, IsHeathBrownEligibleSelection L X 60
          (T0 := T0) (t := t) (e := 1 - sigma)
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I) (color r)) ∧
        ∀ label : HeathBrownSelectionLabel L X 60,
          (S.filter fun r => color r = label).Nonempty →
            IsMaynardSelectionFibreHuxleyConclusion
              (K := K) (T0 := T0) (sigma := sigma) (delta := delta)
              label (S.filter fun r => color r = label) := by
  obtain ⟨L, hL, hXL, hcut, color, hcolor⟩ :=
    exists_canonical_sixty_eligibleSelection_coloring_of_ready_scale
      hready.1 hmu_lo hmu_hi ht hX hXscale hsigma hV S lam hband
        haggregate hreserve
  refine ⟨L, hL, hXL, hcut, color, hcolor, ?_⟩
  intro label hfibre
  let Sfibre : Finset ℕ := S.filter fun r => color r = label
  have hfibreS : Sfibre ⊆ S := Finset.filter_subset _ _
  have hfibreRange : Sfibre ⊆ Finset.range K := hfibreS.trans hS
  have hfibreSelection : ∀ r ∈ Sfibre,
      IsHeathBrownEligibleSelection L X 60
        (T0 := T0) (t := t) (e := 1 - sigma)
        ((sigma : ℂ) + (lam r : ℝ) * Complex.I) label := by
    intro r hr
    have hrS : r ∈ S := hfibreS hr
    have hrcolor : color r = label := (Finset.mem_filter.mp hr).2
    simpa [hrcolor] using hcolor r hrS
  have hfibreDiam : ∀ r ∈ Sfibre, ∀ s ∈ Sfibre,
      |lam s - lam r| ≤ T0 := by
    intro r hr s hs
    exact hdiam r (hfibreS hr) s (hfibreS hs)
  exact huxley_maynardEligibleSelection_fibre_ready
    L X K hready.2 hsigma hmu_lo hmu_hi ht rfl label Sfibre hfibre
      hfibreRange lam hdelta hgap hfibreDiam hfibreSelection

end RHTower.Sieve
