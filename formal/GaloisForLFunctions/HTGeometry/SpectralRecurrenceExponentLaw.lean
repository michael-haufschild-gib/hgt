import GaloisForLFunctions.HTGeometry.SortedSpectrumGapExtremality
import GaloisForLFunctions.HTGeometry.FirstHitExponentLaw

/-!
# The recurrence exponent of a generic Hermitian coefficient family

Extremality of the gap maps says almost every parameter of a simple-spectrum chart is not very well
approximable; the first-hit exponent law turns that into an exact logarithmic exponent for the first
return of the spectral phases to the integer lattice.  The exponent is the number of independent
phases: `n` for the anchored gaps, and one fewer for the gap ratios, because one gap is spent as the
clock.

## Main results

* `ae_not_vwa_of_volume_eq_zero` — the almost-everywhere form of a null very-well-approximable set.
* `ae_tendsto_log_firstHit_sortedGap` — **the discrete recurrence exponent**.
* `ae_tendsto_log_firstHit_sortedGapRatio` — **the winding recurrence exponent**.
-/

open Filter Topology MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D n : ℕ} {P : Fin N → Matrix (Fin D) (Fin D) ℂ}

theorem ae_not_vwa_of_volume_eq_zero {U : Set (Fin N → ℝ)} {F : (Fin N → ℝ) → Fin n → ℝ}
    (h : volume {x ∈ U | KleinbockMargulis.VWA fun k => F x k} = 0) :
    ∀ᵐ x, x ∈ U → ¬ KleinbockMargulis.VWA fun k => F x k := by
  have hae : ∀ᵐ x, x ∉ {x ∈ U | KleinbockMargulis.VWA fun k => F x k} := by
    rw [ae_iff]
    simpa using h
  filter_upwards [hae] with x hx hxU hvwa
  exact hx ⟨hxU, hvwa⟩

/-- **The discrete recurrence exponent of a generic local Hamiltonian.**  Almost every parameter of
a preconnected open piece of the simple-spectrum locus has first-hit exponent exactly `n` for the
rescaled anchored gaps. -/
theorem ae_tendsto_log_firstHit_sortedGap [NeZero N] (hn : 0 < n) (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesAffineRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) {scale : ℝ} (hscale : scale ≠ 0)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    ∀ᵐ x, x ∈ U →
      Tendsto
        (fun r : ℝ =>
          Real.log (firstHit (anchoredGapMap scale (sortedEnsembleSpectrum hP x) anchor ι) r)
            / Real.log (1 / r))
        (𝓝[>] (0 : ℝ)) (𝓝 (n : ℝ)) := by
  filter_upwards [ae_not_vwa_of_volume_eq_zero
    (theoremA_sortedGap hn hP hS hι hanchor hscale hU hUc hUne hUsimple)] with x hx hxU
  exact tendsto_log_firstHit_div_log hn (hx hxU)

/-- **The winding recurrence exponent of a generic local Hamiltonian.** -/
theorem ae_tendsto_log_firstHit_sortedGapRatio [NeZero N] (hn : 0 < n)
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock) (hac : anchor ≠ clock)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUsimple : U ⊆ simpleEnsembleLocus hP) :
    ∀ᵐ x, x ∈ U →
      Tendsto
        (fun r : ℝ =>
          Real.log
            (firstHit (anchoredGapRatioMap (sortedEnsembleSpectrum hP x) anchor clock ι) r)
            / Real.log (1 / r))
        (𝓝[>] (0 : ℝ)) (𝓝 (n : ℝ)) := by
  filter_upwards [ae_not_vwa_of_volume_eq_zero
    (theoremA_sortedGapRatio hn hP hS hι hanchor hclock hac hU hUc hUne hUsimple)] with x hx hxU
  exact tendsto_log_firstHit_div_log hn (hx hxU)

end

end GaloisForLFunctions.HTGeometry
