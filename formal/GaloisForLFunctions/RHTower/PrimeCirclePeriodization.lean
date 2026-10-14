import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Blindness at the powers of a prime is equidistribution on the prime circle

For a frequency `ℓ > 0` (typically `ℓ = log p`) let `phase ℓ t = t ℓ mod 2π`.  A finite measure `μ`
on `ℝ` whose characteristic function vanishes at every `j ℓ`, `j ≥ 1`, pushes forward to a
multiple of Haar measure on the circle `ℝ / 2πℤ` (`map_phase_eq_of_blind`), and conversely
(`blind_of_map_phase_eq`).  For `ℓ = log p` the condition is blindness of the spectral measure at
every power `p^j`.  Consequently every continuous zero-mean function of the phase integrates to
zero against such a measure (`integral_periodic_eq_of_blind`).

**Periodization certificates** (`integral_nonneg_of_periodization`).  If a symbol `S` dominates a
finite sum `Σ_i P_i(t ℓ_i mod 2π)` of continuous zero-mean circle functions, then `∫ S dμ ≥ 0` for
every finite measure `μ` blind at all multiples of every `ℓ_i`.  For a Weil symbol this produces
weights supported on the powers of finitely many primes.

**Null measures saturate certificates** (`ae_eq_of_periodization_of_integral_eq_zero`).  If a blind
measure has `∫ S dμ = 0`, every periodization certificate is an equality `μ`-almost everywhere.  A
null blind test whose spectral measure has full support therefore excludes certificates with slack
anywhere on the line.
-/

open MeasureTheory Complex Real

namespace RHTower.PrimeCirclePeriodization

noncomputable section

instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- The phase `t ℓ mod 2π`. -/
def phase (ℓ t : ℝ) : AddCircle (2 * π) := ((t * ℓ : ℝ) : AddCircle (2 * π))

theorem continuous_phase (ℓ : ℝ) : Continuous (phase ℓ) :=
  (AddCircle.continuous_mk' (2 * π)).comp (continuous_id.mul continuous_const)

theorem measurable_phase (ℓ : ℝ) : Measurable (phase ℓ) := (continuous_phase ℓ).measurable

theorem fourier_phase (ℓ t : ℝ) (n : ℤ) :
    fourier n (phase ℓ t) = cexp ((((n : ℝ) * ℓ : ℝ) : ℂ) * t * I) := by
  rw [phase, fourier_coe_apply]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

theorem integral_fourier_haar (n : ℤ) :
    (∫ z, fourier n z ∂(AddCircle.haarAddCircle (T := 2 * π))) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 2 * π) n) 0
  simpa [fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using h

theorem integral_fourier_map_phase (μ : Measure ℝ) [IsFiniteMeasure μ] (ℓ : ℝ) (n : ℤ) :
    (∫ z, fourier n z ∂(μ.map (phase ℓ))) = charFun μ ((n : ℝ) * ℓ) := by
  rw [integral_map (measurable_phase ℓ).aemeasurable
    (map_continuous (fourier n)).aestronglyMeasurable, charFun_apply_real]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => fourier_phase ℓ t n)

/-- **Blindness at all multiples of `ℓ` is equidistribution of the phase.** -/
theorem map_phase_eq_of_blind (μ : Measure ℝ) [IsFiniteMeasure μ] (ℓ : ℝ)
    (hblind : ∀ j : ℕ, 1 ≤ j → charFun μ ((j : ℝ) * ℓ) = 0) :
    μ.map (phase ℓ) = μ Set.univ • AddCircle.haarAddCircle := by
  haveI : IsFiniteMeasure (μ Set.univ • AddCircle.haarAddCircle (T := 2 * π)) :=
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul, measure_univ (μ := AddCircle.haarAddCircle), mul_one]
      exact measure_lt_top μ _⟩
  apply GaloisForLFunctions.HTGeometry.addCircle_measure_eq_of_fourier_integral_eq
  intro n
  rw [integral_fourier_map_phase, integral_smul_measure, integral_fourier_haar]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨n.natAbs, by omega⟩
    have hj1 : 1 ≤ j := by omega
    have hcast : ((n : ℤ) : ℝ) * ℓ = -((j : ℝ) * ℓ) := by rw [hj]; push_cast; ring
    rw [hcast, charFun_neg, hblind j hj1, map_zero, if_neg hn.ne]
    simp
  · simp [charFun_zero, measureReal_def]
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, n = (j : ℤ) := ⟨n.natAbs, by omega⟩
    have hj1 : 1 ≤ j := by omega
    have hcast : ((n : ℤ) : ℝ) * ℓ = (j : ℝ) * ℓ := by rw [hj]; push_cast; ring
    rw [hcast, hblind j hj1, if_neg hn.ne']
    simp

/-- Conversely, equidistribution of the phase gives blindness at all multiples of `ℓ`. -/
theorem blind_of_map_phase_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (ℓ : ℝ)
    (h : μ.map (phase ℓ) = μ Set.univ • AddCircle.haarAddCircle) (j : ℕ) (hj : 1 ≤ j) :
    charFun μ ((j : ℝ) * ℓ) = 0 := by
  have := integral_fourier_map_phase μ ℓ (j : ℤ)
  rw [h, integral_smul_measure, integral_fourier_haar, if_neg (by omega)] at this
  simpa using this.symm

/-- Every continuous function of the phase integrates against a blind measure to its circle
mean. -/
theorem integral_periodic_eq_of_blind (μ : Measure ℝ) [IsFiniteMeasure μ] (ℓ : ℝ)
    (hblind : ∀ j : ℕ, 1 ≤ j → charFun μ ((j : ℝ) * ℓ) = 0) {P : AddCircle (2 * π) → ℝ}
    (hP : Continuous P) :
    (∫ t, P (phase ℓ t) ∂μ) = μ.real Set.univ * ∫ z, P z ∂AddCircle.haarAddCircle := by
  rw [← integral_map (measurable_phase ℓ).aemeasurable hP.aestronglyMeasurable,
    map_phase_eq_of_blind μ ℓ hblind, integral_smul_measure, smul_eq_mul, measureReal_def]

theorem integrable_periodic (μ : Measure ℝ) [IsFiniteMeasure μ] (ℓ : ℝ)
    {P : AddCircle (2 * π) → ℝ} (hP : Continuous P) : Integrable (fun t => P (phase ℓ t)) μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hP.continuousOn
  exact Integrable.of_bound (hP.comp (continuous_phase ℓ)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun t => hC _ (Set.mem_univ _))

/-- **Periodization certificates.**  If `S ≥ Σ_i P_i(phase ℓ_i)` with continuous zero-mean circle
functions `P_i`, then `∫ S dμ ≥ 0` for every finite measure `μ` blind at all multiples of every
`ℓ_i`. -/
theorem integral_nonneg_of_periodization {μ : Measure ℝ} [IsFiniteMeasure μ] {ι : Type*}
    (F : Finset ι) (ℓ : ι → ℝ) (P : ι → AddCircle (2 * π) → ℝ) (hP : ∀ i ∈ F, Continuous (P i))
    (hmean : ∀ i ∈ F, ∫ z, P i z ∂AddCircle.haarAddCircle = 0)
    (hblind : ∀ i ∈ F, ∀ j : ℕ, 1 ≤ j → charFun μ ((j : ℝ) * ℓ i) = 0) {S : ℝ → ℝ}
    (hS : Integrable S μ) (hcert : ∀ t, ∑ i ∈ F, P i (phase (ℓ i) t) ≤ S t) :
    0 ≤ ∫ t, S t ∂μ := by
  have hsum : ∫ t, ∑ i ∈ F, P i (phase (ℓ i) t) ∂μ = 0 := by
    rw [integral_finsetSum _ fun i hi => integrable_periodic μ (ℓ i) (hP i hi)]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [integral_periodic_eq_of_blind μ (ℓ i) (hblind i hi) (hP i hi), hmean i hi, mul_zero]
  have hint : Integrable (fun t => ∑ i ∈ F, P i (phase (ℓ i) t)) μ :=
    integrable_finsetSum _ fun i hi => integrable_periodic μ (ℓ i) (hP i hi)
  rw [← hsum]
  exact integral_mono hint hS hcert

/-- **Null measures saturate certificates.**  If moreover `∫ S dμ = 0`, the certificate is an
equality `μ`-almost everywhere. -/
theorem ae_eq_of_periodization_of_integral_eq_zero {μ : Measure ℝ} [IsFiniteMeasure μ]
    {ι : Type*} (F : Finset ι) (ℓ : ι → ℝ) (P : ι → AddCircle (2 * π) → ℝ)
    (hP : ∀ i ∈ F, Continuous (P i))
    (hmean : ∀ i ∈ F, ∫ z, P i z ∂AddCircle.haarAddCircle = 0)
    (hblind : ∀ i ∈ F, ∀ j : ℕ, 1 ≤ j → charFun μ ((j : ℝ) * ℓ i) = 0) {S : ℝ → ℝ}
    (hS : Integrable S μ) (hcert : ∀ t, ∑ i ∈ F, P i (phase (ℓ i) t) ≤ S t)
    (hzero : ∫ t, S t ∂μ = 0) :
    ∀ᵐ t ∂μ, S t = ∑ i ∈ F, P i (phase (ℓ i) t) := by
  have hint : Integrable (fun t => ∑ i ∈ F, P i (phase (ℓ i) t)) μ :=
    integrable_finsetSum _ fun i hi => integrable_periodic μ (ℓ i) (hP i hi)
  have hsum : ∫ t, ∑ i ∈ F, P i (phase (ℓ i) t) ∂μ = 0 := by
    rw [integral_finsetSum _ fun i hi => integrable_periodic μ (ℓ i) (hP i hi)]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [integral_periodic_eq_of_blind μ (ℓ i) (hblind i hi) (hP i hi), hmean i hi, mul_zero]
  have hdiff : ∫ t, (S t - ∑ i ∈ F, P i (phase (ℓ i) t)) ∂μ = 0 := by
    rw [integral_sub hS hint, hzero, hsum, sub_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun t => sub_nonneg.mpr (hcert t))
    (hS.sub hint)).mp hdiff
  filter_upwards [hae] with t ht
  exact sub_eq_zero.mp ht

end

end RHTower.PrimeCirclePeriodization
