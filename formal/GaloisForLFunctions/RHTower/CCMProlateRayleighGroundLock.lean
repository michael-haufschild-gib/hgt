import Mathlib

/-!
# CCM prolate Rayleigh--ground lock

The constrained-prolate seed in the Connes--Consani--Moscovici outlook is a variational trial
vector for the actual restricted Weil form.  Once its Rayleigh energy tends to zero, asking that
its excess above the true restricted-Weil floor also tend to zero is not a preliminary
ground-state approximation theorem: it is equivalent to the Riemann hypothesis.

This module isolates exactly the source-specific inputs needed for that classification.  The floor
is antitone because multiplicative apertures are nested; it lies below the seed energy by
Rayleigh--Ritz; nonnegativity of every sampled cofinal floor is the Weil criterion.  Under false RH,
one negative floor therefore persists at every later aperture and forces a uniform positive
seed--ground energy separation.

No determinant convergence, real-zero approximation, simple-ground-state hypothesis, numerical
input, or RH assumption occurs in the interface or proofs.
-/

open Filter

namespace RHTower

noncomputable section

/-- Source-typed variational data for a cofinal CCM restricted-Weil/prolate family.

`floor n` is the true restricted-Weil spectral floor at stage `n`; `seedEnergy n` is the Rayleigh
value of the normalized constrained-prolate seed at the same stage.  The final field is the exact
cofinal Weil criterion, not a positivity premise. -/
structure CCMProlateRayleighGroundData where
  floor : ℕ → ℝ
  seedEnergy : ℕ → ℝ
  floor_antitone : Antitone floor
  floor_le_seedEnergy : ∀ n, floor n ≤ seedEnergy n
  seedEnergy_tendsto_zero : Tendsto seedEnergy atTop (nhds 0)
  riemannHypothesis_iff_floor_nonneg :
    RiemannHypothesis ↔ ∀ n, 0 ≤ floor n

/-- Rayleigh excess of the explicit prolate seed above the true restricted-Weil ground energy. -/
def CCMProlateRayleighGroundData.rayleighExcess
    (D : CCMProlateRayleighGroundData) (n : ℕ) : ℝ :=
  D.seedEnergy n - D.floor n

/-- Rayleigh--Ritz makes the prolate seed excess nonnegative at every aperture. -/
theorem CCMProlateRayleighGroundData.rayleighExcess_nonneg
    (D : CCMProlateRayleighGroundData) (n : ℕ) :
    0 ≤ D.rayleighExcess n := by
  exact sub_nonneg.mpr (D.floor_le_seedEnergy n)

/-- Under RH, the true floor is nonnegative, so prolate seed energy squeezes its Rayleigh excess
to zero. -/
theorem CCMProlateRayleighGroundData.rayleighExcess_tendsto_zero_of_riemannHypothesis
    (D : CCMProlateRayleighGroundData) (hRH : RiemannHypothesis) :
    Tendsto D.rayleighExcess atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall D.rayleighExcess_nonneg
  · filter_upwards with n
    dsimp only [CCMProlateRayleighGroundData.rayleighExcess]
    exact sub_le_self _ ((D.riemannHypothesis_iff_floor_nonneg.mp hRH) n)
  · exact D.seedEnergy_tendsto_zero

/-- **Persistent false-RH separation.** If RH fails, one negative restricted-Weil floor survives
at every larger aperture.  Since the prolate seed energy tends to zero, its excess over the true
ground energy is eventually bounded below by one fixed positive constant. -/
theorem CCMProlateRayleighGroundData.eventually_rayleighExcess_ge_of_not_riemannHypothesis
    (D : CCMProlateRayleighGroundData) (hnot : ¬ RiemannHypothesis) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ n in atTop, delta ≤ D.rayleighExcess n := by
  have hnotFloor : ¬ ∀ n, 0 ≤ D.floor n := by
    exact fun h => hnot (D.riemannHypothesis_iff_floor_nonneg.mpr h)
  obtain ⟨n0, hn0⟩ := Classical.not_forall.mp hnotFloor
  have hfloorNeg : D.floor n0 < 0 := not_le.mp hn0
  let delta : ℝ := -D.floor n0 / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  have hseed : ∀ᶠ n in atTop, D.floor n0 / 2 < D.seedEnergy n :=
    D.seedEnergy_tendsto_zero.eventually
      (eventually_gt_nhds (by linarith : D.floor n0 / 2 < 0))
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [hseed, eventually_ge_atTop n0] with n hseedn hn
  have hfloor : D.floor n ≤ D.floor n0 := D.floor_antitone hn
  dsimp only [CCMProlateRayleighGroundData.rayleighExcess, delta]
  linarith

/-- **Route O Rayleigh--ground lock.** For every genuine cofinal restricted-Weil/prolate family
whose seed Rayleigh energy tends to zero, vanishing seed--ground Rayleigh excess is exactly RH.

The reverse implication uses no determinant or zero-transfer theorem: the persistent false-RH
separation above directly contradicts convergence of the excess to zero. -/
theorem CCMProlateRayleighGroundData.riemannHypothesis_iff_rayleighExcess_tendsto_zero
    (D : CCMProlateRayleighGroundData) :
    RiemannHypothesis ↔ Tendsto D.rayleighExcess atTop (nhds 0) := by
  constructor
  · exact D.rayleighExcess_tendsto_zero_of_riemannHypothesis
  · intro hexcess
    by_contra hnot
    obtain ⟨delta, hdelta, hbound⟩ :=
      D.eventually_rayleighExcess_ge_of_not_riemannHypothesis hnot
    have hsmall : ∀ᶠ n in atTop, D.rayleighExcess n < delta :=
      hexcess.eventually (eventually_lt_nhds hdelta)
    obtain ⟨n, hlower, hupper⟩ := (hbound.and hsmall).exists
    exact (not_lt_of_ge hlower) hupper

end

end RHTower
