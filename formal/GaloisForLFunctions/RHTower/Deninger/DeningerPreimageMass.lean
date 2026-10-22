import GaloisForLFunctions.RHTower.Deninger.DeningerAbelMajorant

/-!
# The canonical Möbius preimage has finite mass on the ray

The Abel identity presents the preimage as a limit of partial sums whose norms are uniformly
bounded by the majorant, so the preimage itself is bounded by the majorant pointwise.  Since the
majorant has finite total mass, so does the preimage:

`∫_0^∞ |f_h(x)| dx < ∞`.

No integrability of `f_h` is assumed anywhere — the estimate is proved in `ℝ≥0∞`, where the
comparison needs nothing but the pointwise bound.

* `deningerMobiusPreimage_enorm_le` : the preimage is bounded by the majorant.
* `deningerMobiusPreimage_mass_lt_top` : **the preimage has finite mass on the ray.**
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal Filter Topology

noncomputable section

/-- **The preimage is bounded by the majorant.**  The Abel partial sums are uniformly bounded by
the majorant, and the enorm is continuous. -/
theorem deningerMobiusPreimage_enorm_le {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) {x : ℝ}
    (hx : 0 < x) :
    ‖deningerMobiusPreimage h x‖ₑ ≤ deningerAbelMajorant h x := by
  have habel := deningerMobius_abel hh hx
  have hcont : Tendsto (fun n : ℕ => ‖∑ i ∈ Finset.range n,
      (deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)) *
        ((Sieve.mertensM i : ℝ) : ℂ)‖ₑ) atTop
      (𝓝 ‖-deningerMobiusPreimage h x‖ₑ) :=
    ((continuous_enorm.tendsto _).comp habel)
  have hbound : ∀ n : ℕ, ‖∑ i ∈ Finset.range n,
      (deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)) *
        ((Sieve.mertensM i : ℝ) : ℂ)‖ₑ ≤ deningerAbelMajorant h x := by
    intro n
    refine le_trans (enorm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range n,
        ‖(deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)) *
          ((Sieve.mertensM i : ℝ) : ℂ)‖ₑ
          = ENNReal.ofReal |Sieve.mertensM i| *
            ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ := by
      intro i _
      rw [enorm_mul, mul_comm]
      congr 1
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    rw [Finset.sum_congr rfl hterm]
    exact ENNReal.sum_le_tsum _
  have hle := le_of_tendsto hcont (Eventually.of_forall hbound)
  rwa [enorm_neg] at hle

/-- **The canonical Möbius preimage has finite mass on the positive ray.**  This is the `L¹` half
of the all-moment domain: the unconditional Möbius saving, Abel summation and the dilation-window
exchange combine to a finite bound. -/
theorem deningerMobiusPreimage_mass_lt_top {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    (∫⁻ x in Set.Ioi (0 : ℝ), ‖deningerMobiusPreimage h x‖ₑ) < ⊤ := by
  refine lt_of_le_of_lt ?_ (deningerAbelMajorant_mass_lt_top hh)
  refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
  exact deningerMobiusPreimage_enorm_le hh hx

end

end RHTower
