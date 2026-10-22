import GaloisForLFunctions.RHTower.Deninger.DeningerMajorantIntegrable
import GaloisForLFunctions.RHTower.Deninger.DeningerDilationIntegral
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusHarmonicZero

/-!
# The canonical Möbius preimage has zero mass

Integrating the Abel representation term by term — the dominating function is the majorant, whose
integrability is already proved — turns the mass of the preimage into the harmonic limit times the
mass of the pullback.  The harmonic limit is zero, so

`∫_0^∞ f_h(x) dx = 0`.

* `deningerLogPull_measurable` : the pullback is measurable.
* `deningerMobiusPreimage_mass_eq_zero` : **the preimage has zero mass.**
-/

namespace RHTower

open MeasureTheory SchwartzMap Filter Topology

noncomputable section

/-- The pullback is measurable. -/
theorem deningerLogPull_measurable (h : 𝓢(ℝ, ℂ)) : Measurable (deningerLogPull h) :=
  h.continuous.measurable.comp Real.measurable_log

/-- The Abel partial sums, as functions of the dilation. -/
def deningerAbelPartial (h : 𝓢(ℝ, ℂ)) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range N,
    (deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)) *
      ((Sieve.mertensM i : ℝ) : ℂ)

theorem deningerAbelPartial_measurable (h : 𝓢(ℝ, ℂ)) (N : ℕ) :
    Measurable (deningerAbelPartial h N) := by
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.mul ?_ measurable_const
  exact ((deningerLogPull_measurable h).comp (measurable_id.const_mul _)).sub
    ((deningerLogPull_measurable h).comp (measurable_id.const_mul _))

/-- The partial sums are dominated by the majorant. -/
theorem deningerAbelPartial_enorm_le (h : 𝓢(ℝ, ℂ)) (N : ℕ) (x : ℝ) :
    ‖deningerAbelPartial h N x‖ₑ ≤ deningerAbelMajorant h x := by
  refine le_trans (enorm_sum_le _ _) ?_
  have hterm : ∀ i ∈ Finset.range N,
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

/-- The partial-sum integral is the partial harmonic sum times the mass of the pullback. -/
theorem deningerAbelPartial_integral {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (N : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), deningerAbelPartial h N x)
      = ∑ i ∈ Finset.range N,
        ((Sieve.mertensM i : ℝ) : ℂ) *
          ((-(1 / ((i : ℝ) * ((i : ℝ) + 1)))) • deningerPullMass h) := by
  simp only [deningerAbelPartial]
  have hint : ∀ i ∈ Finset.range N,
      IntegrableOn (fun x : ℝ =>
        (deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)) *
          ((Sieve.mertensM i : ℝ) : ℂ)) (Set.Ioi 0) := by
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have hz : ((Sieve.mertensM 0 : ℝ) : ℂ) = 0 := by
        rw [Sieve.mertensM]
        simp
      simp only [hz, mul_zero]
      exact integrableOn_zero
    · have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
      exact Integrable.mul_const
        ((deningerLogPull_dilation_integrable hh h1).sub
          (deningerLogPull_dilation_integrable hh hir)) _
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have hz : Sieve.mertensM 0 = 0 := by
      rw [Sieve.mertensM]
      simp
    rw [hz]
    simp
  · rw [deningerAbelDifference_integral hh hi]
    ring

end

end RHTower

/-! ## The zero-mass theorem -/

namespace RHTower

noncomputable section

open MeasureTheory SchwartzMap Filter Topology

/-- The partial sums are dominated by the real majorant. -/
theorem deningerAbelPartial_norm_le {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (N : ℕ) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖deningerAbelPartial h N x‖ ≤ deningerAbelMajorantReal h x := by
  filter_upwards [deningerAbelMajorant_lt_top_ae hh] with x hx
  have hle := deningerAbelPartial_enorm_le h N x
  rw [← ofReal_norm] at hle
  rw [deningerAbelMajorantReal]
  exact (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hx)).mp hle

/-- **The canonical Möbius preimage has zero mass on the ray.**  Integrating the Abel
representation term by term turns the mass into the harmonic limit times the mass of the pullback,
and the harmonic limit is zero. -/
theorem deningerMobiusPreimage_mass_eq_zero {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) :
    (∫ x in Set.Ioi (0 : ℝ), deningerMobiusPreimage h x) = 0 := by
  have hlim : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Tendsto (fun N : ℕ => deningerAbelPartial h N x) atTop
        (𝓝 (-deningerMobiusPreimage h x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact deningerMobius_abel hh hx
  have hdct := tendsto_integral_of_dominated_convergence
    (bound := deningerAbelMajorantReal h)
    (F := fun N : ℕ => deningerAbelPartial h N)
    (f := fun x => -deningerMobiusPreimage h x)
    (fun N => (deningerAbelPartial_measurable h N).aestronglyMeasurable)
    (deningerAbelMajorantReal_integrable hh)
    (deningerAbelPartial_norm_le hh) hlim
  have hvalue : ∀ N : ℕ, (∫ x in Set.Ioi (0 : ℝ), deningerAbelPartial h N x)
      = (((-(∑ i ∈ Finset.range N,
          Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1)))) : ℝ) : ℂ) * deningerPullMass h := by
    intro N
    rw [deningerAbelPartial_integral hh]
    have hterm : ∀ i ∈ Finset.range N,
        ((Sieve.mertensM i : ℝ) : ℂ) *
          ((-(1 / ((i : ℝ) * ((i : ℝ) + 1)))) • deningerPullMass h)
          = ((-(Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1))) : ℝ) : ℂ) *
            deningerPullMass h := by
      intro i _
      rw [Complex.real_smul]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    congr 1
    push_cast
    exact Finset.sum_neg_distrib (s := Finset.range N)
      (f := fun i : ℕ => ((Sieve.mertensM i : ℝ) : ℂ) / ((i : ℂ) * ((i : ℂ) + 1)))
  have hpartial : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range N, Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1))) atTop
      (𝓝 deningerHarmonicLimit) :=
    deningerMertensHarmonic_summable.hasSum.tendsto_sum_nat
  have hzero : Tendsto (fun N : ℕ => (∫ x in Set.Ioi (0 : ℝ), deningerAbelPartial h N x))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun N : ℕ =>
        (((-(∑ i ∈ Finset.range N,
          Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1)))) : ℝ) : ℂ) * deningerPullMass h)
        atTop (𝓝 (((-deningerHarmonicLimit : ℝ) : ℂ) * deningerPullMass h)) := by
      exact ((Complex.continuous_ofReal.tendsto _).comp hpartial.neg).mul tendsto_const_nhds
    rw [deningerHarmonicLimit_eq_zero] at hc
    simp only [neg_zero, Complex.ofReal_zero, zero_mul] at hc
    exact hc.congr fun N => (hvalue N).symm
  have huniq := tendsto_nhds_unique hzero hdct
  have hneg : (∫ x in Set.Ioi (0 : ℝ), -deningerMobiusPreimage h x)
      = -∫ x in Set.Ioi (0 : ℝ), deningerMobiusPreimage h x := integral_neg _
  rw [hneg] at huniq
  linear_combination huniq

end

end RHTower
