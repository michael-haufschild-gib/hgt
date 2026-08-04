import GaloisForLFunctions.HTGeometry.ObservationFidelity

/-!
# Resolved Hellinger selector removal

An observation parameter `θ` may choose its own target `selector θ`.  A local Hellinger-affinity
lower bound on a shortcut event, together with one positive reciprocal certificate uniform over
all targets in each `θ`-fibre, bounds the probability of that event.  The selector remains inside
the parameter fibre throughout; no targetwise union bound and no interchange of supremum with
parameter expectation occurs.
-/

open Real MeasureTheory Set

namespace HTGeometry

noncomputable section

/-- Weighted arithmetic--geometric mean in the exact form used by the Hellinger certificate. -/
theorem two_mul_sqrt_mul_le_weighted_sum
    {p q f : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hf : 0 < f) :
    2 * Real.sqrt (p * q) ≤ f * p + q / f := by
  have hfp : 0 ≤ f * p := mul_nonneg hf.le hp
  have hqf : 0 ≤ q / f := div_nonneg hq hf.le
  have hprod : (f * p) * (q / f) = p * q := by
    field_simp [hf.ne']
  have hsq := two_mul_le_add_sq (Real.sqrt (f * p)) (Real.sqrt (q / f))
  rw [Real.sq_sqrt hfp, Real.sq_sqrt hqf] at hsq
  have hsqrt : Real.sqrt (f * p) * Real.sqrt (q / f) = Real.sqrt (p * q) := by
    rw [← Real.sqrt_mul hfp, hprod]
  calc
    2 * Real.sqrt (p * q) =
        2 * (Real.sqrt (f * p) * Real.sqrt (q / f)) := by rw [hsqrt]
    _ = 2 * Real.sqrt (f * p) * Real.sqrt (q / f) := by ring
    _ ≤ f * p + q / f := hsq

/-- The Hellinger affinity of two nonnegative densities is bounded by the sum of the two
reciprocal certificate costs. -/
theorem two_mul_hellingerIntegral_le_weighted_integrals
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p q f : Ω → ℝ}
    (hp : ∀ᵐ ω ∂μ, 0 ≤ p ω)
    (hq : ∀ᵐ ω ∂μ, 0 ≤ q ω)
    (hf : ∀ᵐ ω ∂μ, 0 < f ω)
    (hhell : Integrable (fun ω => Real.sqrt (p ω * q ω)) μ)
    (hhead : Integrable (fun ω => f ω * p ω) μ)
    (htail : Integrable (fun ω => q ω / f ω) μ) :
    2 * ∫ ω, Real.sqrt (p ω * q ω) ∂μ ≤
      (∫ ω, f ω * p ω ∂μ) + ∫ ω, q ω / f ω ∂μ := by
  have hpoint : ∀ᵐ ω ∂μ,
      2 * Real.sqrt (p ω * q ω) ≤ f ω * p ω + q ω / f ω := by
    filter_upwards [hp, hq, hf] with ω hpω hqω hfω
    exact two_mul_sqrt_mul_le_weighted_sum hpω hqω hfω
  have hmono := integral_mono_ae (hhell.const_mul 2) (hhead.add htail) hpoint
  rw [integral_const_mul] at hmono
  calc
    2 * ∫ ω, Real.sqrt (p ω * q ω) ∂μ
        ≤ ∫ ω, (fun ω => f ω * p ω) ω + (fun ω => q ω / f ω) ω ∂μ := by
          simpa only [Pi.add_apply] using hmono
    _ = (∫ ω, f ω * p ω ∂μ) + ∫ ω, q ω / f ω ∂μ :=
      integral_add hhead htail

/-- Abstract resolved selector law.  If the selected target has affinity at least `α` on `A`, and
every target is controlled by the same nonnegative fibre costs, then the probability of `A` is at
most the mean total cost divided by `2α`. -/
theorem resolvedHellinger_selector_event_measure_le
    {Θ C : Type*} [MeasurableSpace Θ] {η : Measure Θ} [IsProbabilityMeasure η]
    {A : Set Θ} (hA : MeasurableSet A) {α : ℝ} (hα : 0 < α)
    (affinity : Θ → C → ℝ) (selector : Θ → C) (head tail : Θ → ℝ)
    (hhead : Integrable head η) (htail : Integrable tail η)
    (hhead_nonneg : ∀ θ, 0 ≤ head θ) (htail_nonneg : ∀ θ, 0 ≤ tail θ)
    (hlocal : ∀ θ ∈ A, α ≤ affinity θ (selector θ))
    (hdual : ∀ θ c, 2 * affinity θ c ≤ head θ + tail θ) :
    η.real A ≤ ((∫ θ, head θ ∂η) + ∫ θ, tail θ ∂η) / (2 * α) := by
  have hpoint : ∀ θ ∈ A, 2 * α ≤ head θ + tail θ := by
    intro θ hθ
    exact le_trans (mul_le_mul_of_nonneg_left (hlocal θ hθ) (by positivity))
      (hdual θ (selector θ))
  have hconst : Integrable (fun _ : Θ => 2 * α) η := integrable_const _
  have hsum : Integrable (fun θ => head θ + tail θ) η := hhead.add htail
  have hmono : ∫ θ in A, 2 * α ∂η ≤ ∫ θ in A, (head θ + tail θ) ∂η :=
    setIntegral_mono_on hconst.integrableOn hsum.integrableOn hA hpoint
  have hset_le : ∫ θ in A, (head θ + tail θ) ∂η ≤
      ∫ θ, (head θ + tail θ) ∂η := by
    exact setIntegral_le_integral hsum
      (ae_of_all _ fun θ => add_nonneg (hhead_nonneg θ) (htail_nonneg θ))
  have hmain : 2 * α * η.real A ≤
      (∫ θ, head θ ∂η) + ∫ θ, tail θ ∂η := by
    calc
      2 * α * η.real A = ∫ θ in A, 2 * α ∂η := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ θ in A, (head θ + tail θ) ∂η := hmono
      _ ≤ ∫ θ, (head θ + tail θ) ∂η := hset_le
      _ = (∫ θ, head θ ∂η) + ∫ θ, tail θ ∂η := integral_add hhead htail
  apply (le_div_iff₀ (mul_pos (by positivity) hα)).2
  simpa [mul_comm] using hmain

/-- **Resolved Hellinger selector-removal law.**  For arbitrary parameter and observation spaces,
an adaptive target selector cannot beat one positive certificate whose reciprocal tail bound is
uniform over every target in the same parameter fibre. -/
theorem resolvedHellinger_selectorRemoval
    {Θ Ω C : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    {η : Measure Θ} [IsProbabilityMeasure η] {μ : Measure Ω}
    {A : Set Θ} (hA : MeasurableSet A) {α : ℝ} (hα : 0 < α)
    (p : Θ → Ω → ℝ) (q : Θ → C → Ω → ℝ) (f : Θ → Ω → ℝ)
    (selector : Θ → C) (tail : Θ → ℝ)
    (hp : ∀ θ, ∀ᵐ ω ∂μ, 0 ≤ p θ ω)
    (hq : ∀ θ c, ∀ᵐ ω ∂μ, 0 ≤ q θ c ω)
    (hf : ∀ θ, ∀ᵐ ω ∂μ, 0 < f θ ω)
    (hhell : ∀ θ c, Integrable (fun ω => Real.sqrt (p θ ω * q θ c ω)) μ)
    (hhead : ∀ θ, Integrable (fun ω => f θ ω * p θ ω) μ)
    (htail : ∀ θ c, Integrable (fun ω => q θ c ω / f θ ω) μ)
    (hheadTheta : Integrable (fun θ => ∫ ω, f θ ω * p θ ω ∂μ) η)
    (htailTheta : Integrable tail η)
    (htailBound : ∀ θ c, (∫ ω, q θ c ω / f θ ω ∂μ) ≤ tail θ)
    (hlocal : ∀ θ ∈ A,
      α ≤ ∫ ω, Real.sqrt (p θ ω * q θ (selector θ) ω) ∂μ) :
    η.real A ≤
      ((∫ θ, ∫ ω, f θ ω * p θ ω ∂μ ∂η) + ∫ θ, tail θ ∂η) / (2 * α) := by
  let affinity : Θ → C → ℝ := fun θ c =>
    ∫ ω, Real.sqrt (p θ ω * q θ c ω) ∂μ
  let head : Θ → ℝ := fun θ => ∫ ω, f θ ω * p θ ω ∂μ
  have hhead_nonneg : ∀ θ, 0 ≤ head θ := by
    intro θ
    apply integral_nonneg_of_ae
    filter_upwards [hf θ, hp θ] with ω hfω hpω
    exact mul_nonneg hfω.le hpω
  have htail_nonneg : ∀ θ, 0 ≤ tail θ := by
    intro θ
    apply le_trans ?_ (htailBound θ (selector θ))
    apply integral_nonneg_of_ae
    filter_upwards [hq θ (selector θ), hf θ] with ω hqω hfω
    exact div_nonneg hqω hfω.le
  have hdual : ∀ θ c, 2 * affinity θ c ≤ head θ + tail θ := by
    intro θ c
    have hamgm := two_mul_hellingerIntegral_le_weighted_integrals
      (hp θ) (hq θ c) (hf θ) (hhell θ c) (hhead θ) (htail θ c)
    exact le_trans hamgm (add_le_add_right (htailBound θ c) _)
  exact resolvedHellinger_selector_event_measure_le hA hα affinity selector head tail
    hheadTheta htailTheta hhead_nonneg htail_nonneg hlocal hdual

end

end HTGeometry
