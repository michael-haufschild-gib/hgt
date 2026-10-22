import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonPotentialUniqueness

/-!
# A source with no Duhamel term vanishes identically

A continuous source whose Duhamel term vanishes for every observation time vanishes at the origin —
that is what the differentiation argument gives directly, and it is all the autonomous inverse
problem needs. This file upgrades it to vanishing everywhere.

The upgrade is algebraic, not analytic. Translating the source by `r` changes the Duhamel term by

`∫₀ʳ (sin((r+y-σ)⟨D⟩)/⟨D⟩) g(σ) dσ`,

and the addition law for the half-order propagator splits that off-diagonal piece into
`cos(y⟨D⟩)` applied to the sine Duhamel term at `r` plus `sin(y⟨D⟩)/⟨D⟩` applied to the cosine one.
Both of those vanish — the first by hypothesis, the second because it is the derivative of the first.
So the translated source again has a vanishing Duhamel term, and the statement at the origin applies
to it.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The cosine Duhamel term of a source whose sine Duhamel term vanishes identically. -/
theorem intervalIntegral_kgCosOp_eq_zero_of_kgSinFreqOp_eq_zero
    {g : ℝ → Lp ℂ 2 (volume : Measure E)} (hg : Continuous g)
    (hzero : ∀ x : ℝ, (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (g s)) = 0) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, kgCosOp (t - s) (g s)) = 0 := by
  have hD := hasDerivAt_intervalIntegral_kgSinFreqOp hg t
  have hfun : (fun r : ℝ => ∫ s in (0 : ℝ)..r, kgSinFreqOp (r - s) (g s))
      = fun _ : ℝ => (0 : Lp ℂ 2 (volume : Measure E)) := funext hzero
  rw [hfun] at hD
  exact hD.unique (hasDerivAt_const t 0)

/-- **The off-diagonal Duhamel term splits.** The part of the Duhamel term at time `r+y` that comes
from the source before time `r` is determined by the two Duhamel terms at time `r`. -/
theorem intervalIntegral_kgSinFreqOp_shift {g : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hg : Continuous g) (r y : ℝ) :
    (∫ σ in (0 : ℝ)..r, kgSinFreqOp (r + y - σ) (g σ))
      = kgCosOp y (∫ σ in (0 : ℝ)..r, kgSinFreqOp (r - σ) (g σ))
        + kgSinFreqOp y (∫ σ in (0 : ℝ)..r, kgCosOp (r - σ) (g σ)) := by
  have hJ1 : Continuous fun σ : ℝ => kgSinFreqOp (r - σ) (g σ) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hg
  have hJ2 : Continuous fun σ : ℝ => kgCosOp (r - σ) (g σ) :=
    continuous_kgCosOp_comp (continuous_const.sub continuous_id) hg
  have hI1 : IntervalIntegrable
      (fun σ : ℝ => kgCosOp y (kgSinFreqOp (r - σ) (g σ))) volume 0 r :=
    (continuous_kgCosOp_comp continuous_const hJ1).intervalIntegrable 0 r
  have hI2 : IntervalIntegrable
      (fun σ : ℝ => kgSinFreqOp y (kgCosOp (r - σ) (g σ))) volume 0 r :=
    (continuous_kgSinFreqOp_comp continuous_const hJ2).intervalIntegrable 0 r
  have hpt : ∀ σ ∈ Set.uIcc (0 : ℝ) r, kgSinFreqOp (r + y - σ) (g σ)
      = kgCosOp y (kgSinFreqOp (r - σ) (g σ)) + kgSinFreqOp y (kgCosOp (r - σ) (g σ)) := by
    intro σ _
    have hsum : r + y - σ = y + (r - σ) := by ring
    rw [hsum, kgSinFreqOp_add]
    rfl
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_add hI1 hI2,
    ContinuousLinearMap.intervalIntegral_comp_comm _ (hJ1.intervalIntegrable 0 r),
    ContinuousLinearMap.intervalIntegral_comp_comm _ (hJ2.intervalIntegrable 0 r)]

/-- **A continuous source whose Duhamel term vanishes identically is zero.** -/
theorem eq_zero_of_intervalIntegral_kgSinFreqOp_eq_zero'
    {g : ℝ → Lp ℂ 2 (volume : Measure E)} (hg : Continuous g)
    (hzero : ∀ x : ℝ, (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (g s)) = 0) :
    ∀ r : ℝ, g r = 0 := by
  intro r
  have hcos := intervalIntegral_kgCosOp_eq_zero_of_kgSinFreqOp_eq_zero hg hzero
  have hshift : Continuous fun s : ℝ => g (r + s) := hg.comp (continuous_const.add continuous_id)
  have hkey : ∀ y : ℝ, (∫ s in (0 : ℝ)..y, kgSinFreqOp (y - s) (g (r + s))) = 0 := by
    intro y
    have hF : Continuous fun σ : ℝ => kgSinFreqOp (r + y - σ) (g σ) :=
      continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hg
    have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) y, kgSinFreqOp (y - s) (g (r + s))
        = (fun σ : ℝ => kgSinFreqOp (r + y - σ) (g σ)) (r + s) := by
      intro s _
      show kgSinFreqOp (y - s) (g (r + s)) = kgSinFreqOp (r + y - (r + s)) (g (r + s))
      congr 2
      ring
    have hshiftInt : (∫ s in (0 : ℝ)..y, kgSinFreqOp (y - s) (g (r + s)))
        = ∫ σ in r..(r + y), kgSinFreqOp (r + y - σ) (g σ) := by
      rw [intervalIntegral.integral_congr hpt]
      have h := intervalIntegral.integral_comp_add_left
        (a := (0 : ℝ)) (b := y) (f := fun σ : ℝ => kgSinFreqOp (r + y - σ) (g σ)) r
      rw [add_zero] at h
      exact h
    have hsplit : (∫ σ in r..(r + y), kgSinFreqOp (r + y - σ) (g σ))
        = (∫ σ in (0 : ℝ)..(r + y), kgSinFreqOp (r + y - σ) (g σ))
          - ∫ σ in (0 : ℝ)..r, kgSinFreqOp (r + y - σ) (g σ) :=
      (intervalIntegral.integral_interval_sub_left (hF.intervalIntegrable 0 (r + y))
        (hF.intervalIntegrable 0 r)).symm
    rw [hshiftInt, hsplit, hzero (r + y), intervalIntegral_kgSinFreqOp_shift hg r y,
      hzero r, hcos r, map_zero, map_zero]
    simp
  have hg0 := eq_zero_of_intervalIntegral_kgSinFreqOp_eq_zero hshift hkey
  simpa using hg0

end GaloisForLFunctions.HTGeometry
