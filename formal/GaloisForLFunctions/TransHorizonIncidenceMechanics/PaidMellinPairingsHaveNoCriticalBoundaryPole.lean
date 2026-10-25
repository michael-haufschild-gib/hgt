import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries

/-!
# Paid Mellin pairings have no critical boundary pole

Pronic Cauchy–Schwarz bounds the complex Mellin pairing at every height.
Multiplication by the distance to the critical boundary forces its radial
limit to zero, excluding a simple pole there.
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

/-- Generic paid prefix energy bounds the complex Mellin pairing at every height. -/
theorem norm_complexMellinPairing_le_of_energy {E : ℝ} {f : ℕ → ℝ}
    (hf0 : f 0 = 0)
    (hE : ∀ T, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖complexMellinPairing f s‖ ≤
      (‖s‖ / s.re) * (Real.sqrt E *
        Real.sqrt (2 * s.re ^ 2 * (1 + 1 / (2 * s.re - 1)))) := by
  have hs0 : 0 < s.re := by linarith only [hs]
  have hfactor : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs0.le
  have habs := summable_mul_mellinCell_of_energy hs (f := fun n => |f n|)
    (by simp only [hf0, abs_zero]) (fun T => by simpa only [sq_abs] using hE T)
  have hmajor (n : ℕ) : ‖(f n : ℂ) * complexMellinCell s n‖ ≤
      (‖s‖ / s.re) * (|f n| * mellinCell s.re n) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hf0, Complex.ofReal_zero, zero_mul, norm_zero, abs_zero, mul_zero, le_refl]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |f n| * ((‖s‖ / s.re) * mellinCell s.re n) :=
          mul_le_mul_of_nonneg_left (norm_cmellinCell_le hs0 hn) (abs_nonneg _)
        _ = _ := by ring
  have hcomplex : Summable (fun n => (f n : ℂ) * complexMellinCell s n) :=
    (habs.mul_left (‖s‖ / s.re)).of_norm_bounded hmajor
  have hreal := abs_tsum_mul_mellinCell_le hs (f := fun n => |f n|)
    (by simp only [hf0, abs_zero]) habs (fun T => by simpa only [sq_abs] using hE T)
  calc
    _ ≤ ∑' n, ‖(f n : ℂ) * complexMellinCell s n‖ := norm_tsum_le_tsum_norm hcomplex.norm
    _ ≤ ∑' n, (‖s‖ / s.re) * (|f n| * mellinCell s.re n) :=
      Summable.tsum_le_tsum hmajor hcomplex.norm (habs.mul_left _)
    _ = (‖s‖ / s.re) * ∑' n, |f n| * mellinCell s.re n := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hreal) hfactor

end GaloisForLFunctions.TransHorizonIncidenceMechanics

#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.norm_complexMellinPairing_le_of_energy
end
end


section
noncomputable section
set_option autoImplicit false
open Finset Filter Topology Complex

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

/-- One power of distance to the critical boundary dominates the paid Mellin growth. -/
theorem norm_mul_complexMellinPairing_sq_le {E : ℝ} {f : ℕ → ℝ}
    (hf0 : f 0 = 0)
    (hE : ∀ T, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E)
    {s₀ : ℂ} (hs₀ : s₀.re = 1 / 2) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) * complexMellinPairing f (s₀ + u)‖ ^ 2 ≤
      ‖s₀ + (u : ℂ)‖ ^ 2 * E * (2 * u ^ 2 + u) := by
  have hEnonneg : 0 ≤ E := by simpa using hE 0
  have hs : 1 / 2 < (s₀ + (u : ℂ)).re := by
    rw [add_re, ofReal_re, hs₀]
    linarith only [hu]
  have hspos : 0 < (s₀ + (u : ℂ)).re := by linarith only [hs]
  have htwo : 2 * (s₀ + (u : ℂ)).re - 1 = 2 * u := by
    rw [add_re, ofReal_re, hs₀]
    ring
  have hrad : 0 ≤ 2 * (s₀ + (u : ℂ)).re ^ 2 *
      (1 + 1 / (2 * (s₀ + (u : ℂ)).re - 1)) := by rw [htwo]; positivity
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_complexMellinPairing_le_of_energy hf0 hE hs) 2
  simp only [mul_pow, div_pow, Real.sq_sqrt hEnonneg, Real.sq_sqrt hrad] at h
  have heq : ‖s₀ + (u : ℂ)‖ ^ 2 / (s₀ + (u : ℂ)).re ^ 2 *
      (E * (2 * (s₀ + (u : ℂ)).re ^ 2 *
        (1 + 1 / (2 * (s₀ + (u : ℂ)).re - 1)))) =
      ‖s₀ + (u : ℂ)‖ ^ 2 * E * (2 + 1 / u) := by
    rw [htwo]
    field_simp [hspos.ne', hu.ne']
  rw [heq] at h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, mul_pow]
  calc
    _ ≤ u ^ 2 * (‖s₀ + (u : ℂ)‖ ^ 2 * E * (2 + 1 / u)) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by field_simp [hu.ne']

/-- A paid receiver cannot carry a simple Mellin pole on the critical boundary. -/
theorem mul_complexMellinPairing_tendsto_zero_at_boundary {E : ℝ} {f : ℕ → ℝ}
    (hf0 : f 0 = 0)
    (hE : ∀ T, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E)
    {s₀ : ℂ} (hs₀ : s₀.re = 1 / 2) :
    Tendsto (fun u : ℝ => (u : ℂ) * complexMellinPairing f (s₀ + u))
      (𝓝[>] 0) (𝓝 0) := by
  have hbound : Tendsto (fun u : ℝ => ‖s₀ + (u : ℂ)‖ ^ 2 * E * (2 * u ^ 2 + u))
      (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun u : ℝ => ‖s₀ + (u : ℂ)‖ ^ 2 * E * (2 * u ^ 2 + u)) := by
      fun_prop
    have hc0 : ContinuousAt (fun u : ℝ => ‖s₀ + (u : ℂ)‖ ^ 2 * E * (2 * u ^ 2 + u)) 0 :=
      hcont.continuousAt
    have ht := hc0.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    simpa only [ofReal_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
      using ht
  have hsq : Tendsto (fun u : ℝ =>
      ‖(u : ℂ) * complexMellinPairing f (s₀ + u)‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun u => sq_nonneg _) ?_ hbound
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact norm_mul_complexMellinPairing_sq_le hf0 hE hs₀ hu
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun u : ℝ =>
    Real.sqrt (‖(u : ℂ) * complexMellinPairing f (s₀ + u)‖ ^ 2))
    (𝓝[>] 0) (𝓝 (Real.sqrt 0)) at hnorm
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hnorm
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

end GaloisForLFunctions.TransHorizonIncidenceMechanics

#print axioms GaloisForLFunctions.TransHorizonIncidenceMechanics.mul_complexMellinPairing_tendsto_zero_at_boundary
end
end
