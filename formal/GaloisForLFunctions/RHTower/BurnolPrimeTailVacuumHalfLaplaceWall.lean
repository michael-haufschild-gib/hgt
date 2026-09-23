import GaloisForLFunctions.RHTower.PrimeVacuumFlatRemainder
import GaloisForLFunctions.RHTower.BurnolPrimeTailFoldedModeWittBridge

/-!
# The prime-vacuum wall of the folded half-Laplace port

The literal all-prime co-Poisson current carries a universal boundary
resonance.  Its logarithmic half-density has a nonzero `1 / L` tail after
the fixed half-rate Burnol weight, so it cannot be an admissible strict-strip
folded mode.  This is an unconditional obstruction, independent of divisor
selection.

The positive survivor is the canonical continuous-prime-vacuum subtraction.
Its residual half-port has an `exp (-c sqrt L)` envelope.  Thus any
coefficient-faithful HJ Stokes transport must be built from the renormalized
remainder (and retain two boundary readings), never from the raw current.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The literal all-prime current is excluded from the strict folded half-Laplace
port by its non-integrable boundary resonance. -/
theorem not_integrableOn_routeRFoldedHalfLaplaceIntegrand_logHalfDensity_primeTailCurrent
    {z : ℂ} (hz : 1 < z.re) :
    ¬ IntegrableOn
      (routeRFoldedHalfLaplaceIntegrand (logHalfDensity (primeTailCurrent z))) (Ioi 0) := by
  intro hint
  have hzne : z - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero.mp h] at hz
    norm_num at hz
  have hnormz : 0 < ‖z - 1‖ := norm_pos_iff.mpr hzne
  have hraw : Tendsto
      (fun L : ℝ => routeRFoldedHalfLaplaceIntegrand
        (logHalfDensity (primeTailCurrent z)) L * ((z - 1) * (L : ℂ)))
      atTop (𝓝 1) := by
    convert tendsto_logHalfDensity_primeTailCurrent hz using 1
    funext L
    have hexp : Complex.exp (-((1 / 2 : ℂ) * (L : ℂ))) =
        (Real.exp (-L / 2) : ℂ) := by
      rw [show -((1 / 2 : ℂ) * (L : ℂ)) = ((-L / 2 : ℝ) : ℂ) from by
        push_cast
        ring,
        Complex.ofReal_exp]
    simp only [routeRFoldedHalfLaplaceIntegrand, logHalfDensity]
    rw [hexp]
    ring
  have hrawnorm : Tendsto (fun L : ℝ => ‖routeRFoldedHalfLaplaceIntegrand
      (logHalfDensity (primeTailCurrent z)) L * ((z - 1) * (L : ℂ))‖)
      atTop (𝓝 1) := by
    simpa using hraw.norm
  have hlarge : ∀ᶠ L : ℝ in atTop,
      (1 / 2 : ℝ) ≤ ‖routeRFoldedHalfLaplaceIntegrand
        (logHalfDensity (primeTailCurrent z)) L * ((z - 1) * (L : ℂ))‖ :=
    Tendsto.eventually_const_le (by norm_num : (1 / 2 : ℝ) < 1) hrawnorm
  obtain ⟨L₀, hL₀⟩ := (eventually_atTop.1 hlarge)
  have hL₀pos : 0 < max 1 L₀ :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hintTail : IntegrableOn
      (routeRFoldedHalfLaplaceIntegrand (logHalfDensity (primeTailCurrent z)))
      (Ioi (max 1 L₀)) := hint.mono_set (Ioi_subset_Ioi hL₀pos.le)
  have hminor : IntegrableOn (fun L : ℝ =>
      (1 / (2 * ‖z - 1‖)) * L⁻¹) (Ioi (max 1 L₀)) := by
    refine MeasureTheory.Integrable.mono' hintTail.norm ?_ ?_
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
      have hLpos : 0 < L := lt_of_lt_of_le hL₀pos (le_of_lt hL)
      have hbound := hL₀ L (le_trans (le_max_right _ _) hL.le)
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hLpos.le] at hbound
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa only [norm_norm] using (show
        (1 / (2 * ‖z - 1‖)) * L⁻¹ ≤ ‖routeRFoldedHalfLaplaceIntegrand
          (logHalfDensity (primeTailCurrent z)) L‖ by
          have hden : 0 < 2 * ‖z - 1‖ * L := by positivity
          calc
            (1 / (2 * ‖z - 1‖)) * L⁻¹ = 1 / (2 * ‖z - 1‖ * L) := by
              field_simp
            _ ≤ ‖routeRFoldedHalfLaplaceIntegrand
                (logHalfDensity (primeTailCurrent z)) L‖ :=
              (div_le_iff₀ hden).mpr (by nlinarith [hbound]))
  have hinv : IntegrableOn (fun L : ℝ => L⁻¹) (Ioi (max 1 L₀)) := by
    have hscaled := hminor.const_mul (2 * ‖z - 1‖)
    apply Integrable.congr hscaled
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with L _
    field_simp
  exact not_integrableOn_Ioi_inv hinv

/-- The vacuum-normalized prime remainder has a strictly decaying half-port
envelope.  This is the usable source tail left by the resonance obstruction. -/
theorem exists_norm_routeRFoldedHalfLaplaceIntegrand_logHalfDensity_primeRemainderCurrent_bound
    {z : ℂ} (hz : 1 < z.re) :
    ∃ K c : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ᶠ L : ℝ in atTop,
      ‖routeRFoldedHalfLaplaceIntegrand
        (logHalfDensity (primeRemainderCurrent z)) L‖ ≤
        K * Real.exp (-c * Real.sqrt L) := by
  obtain ⟨K, c, hc, hK, hbound⟩ :=
    exists_norm_logHalfDensity_primeRemainderCurrent_bound hz
  refine ⟨K, c, hc, hK, ?_⟩
  filter_upwards [hbound] with L hL
  rw [routeRFoldedHalfLaplaceIntegrand, norm_mul, Complex.norm_exp]
  have hreal : (-((1 / 2 : ℂ) * (L : ℂ))).re = -L / 2 := by
    norm_num
    ring
  rw [hreal]
  have hstep := mul_le_mul_of_nonneg_left hL (Real.exp_pos (-L / 2)).le
  refine hstep.trans ?_
  calc
    Real.exp (-L / 2) * (K * Real.exp (L / 2 - c * Real.sqrt L)) =
        K * (Real.exp (-L / 2) * Real.exp (L / 2 - c * Real.sqrt L)) := by ring
    _ = K * Real.exp (-c * Real.sqrt L) := by
      rw [← Real.exp_add]
      apply congrArg (fun x : ℝ => K * Real.exp x)
      ring
    _ ≤ K * Real.exp (-c * Real.sqrt L) := le_rfl

end RHTower
