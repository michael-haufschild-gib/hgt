import GaloisForLFunctions.SelbergClass.Primon.KestenRelativeEntropy

/-!
# Quadratic entropy convergence of the prime spectral laws

The exact logarithmic averages bound prime-to-semicircle relative entropy
by `p⁻²`. The reverse divergence is at most `p⁻²/(1+p⁻¹)`. Both directed
divergences therefore tend to zero as primes escape finite sets.
-/

open MeasureTheory InformationTheory Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Prime-to-semicircle relative entropy is bounded by the inverse prime square. -/
theorem kestenSemicircleEntropyValue_le_inverse_square (p : Nat.Primes) :
    kestenSemicircleEntropyValue p ≤ ((p : ℝ)⁻¹) ^ 2 := by
  have h := (kesten_evenPhaseLog_bounds p (primeSquareRootDiskParameter p)).1
  rw [integral_kesten_evenPhaseLog, cavityDiskCoordinate_prime_sqrt_square] at h
  have he : (p : ℝ)⁻¹ / (p : ℝ) = ((p : ℝ)⁻¹) ^ 2 := by
    simp only [div_eq_mul_inv, pow_two]
  rw [he] at h
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (p : ℝ)⁻¹ by positivity)
  unfold kestenSemicircleEntropyValue
  nlinarith only [h, hl]

/-- The reverse entropy has a slightly stronger inverse-square bound. -/
theorem semicircleKestenEntropyValue_le_inverse_square_div (p : Nat.Primes) :
    semicircleKestenEntropyValue p ≤ ((p : ℝ)⁻¹) ^ 2 / (1 + (p : ℝ)⁻¹) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hx : (0 : ℝ) < 1 + (p : ℝ)⁻¹ := by positivity
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hl
  unfold semicircleKestenEntropyValue
  calc
    (p : ℝ)⁻¹ - Real.log (1 + (p : ℝ)⁻¹) ≤
        (p : ℝ)⁻¹ + ((1 + (p : ℝ)⁻¹)⁻¹ - 1) := by linarith only [hl]
    _ = ((p : ℝ)⁻¹) ^ 2 / (1 + (p : ℝ)⁻¹) := by
      field_simp [hp, hx.ne']
      ring

/-- The real prime-to-semicircle entropy tends to zero with an explicit quadratic bound. -/
theorem tendsto_kestenSemicircleEntropyValue :
    Tendsto kestenSemicircleEntropyValue cofinite (𝓝 0) := by
  have hi : Tendsto (fun p : Nat.Primes => (p : ℝ)⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_primeReal_cofinite_atTop
  apply squeeze_zero' (Eventually.of_forall kestenSemicircleEntropyValue_nonneg)
    (Eventually.of_forall kestenSemicircleEntropyValue_le_inverse_square)
  have h := hi.pow 2
  change Tendsto (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) cofinite (𝓝 ((0 : ℝ) ^ 2)) at h
  simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0)] using h

/-- The reverse real entropy also tends to zero at a quadratic rate. -/
theorem tendsto_semicircleKestenEntropyValue :
    Tendsto semicircleKestenEntropyValue cofinite (𝓝 0) := by
  have hi : Tendsto (fun p : Nat.Primes => (p : ℝ)⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_primeReal_cofinite_atTop
  have hd := ((tendsto_const_nhds (x := (1 : ℝ))).add hi)
  have h := (hi.pow 2).div hd (by norm_num : (1 : ℝ) + 0 ≠ 0)
  change Tendsto (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2 / (1 + (p : ℝ)⁻¹))
    cofinite (𝓝 ((0 : ℝ) ^ 2 / (1 + 0))) at h
  apply squeeze_zero' (Eventually.of_forall semicircleKestenEntropyValue_nonneg)
    (Eventually.of_forall semicircleKestenEntropyValue_le_inverse_square_div)
  simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), zero_div] using h

/-- The actual extended-real prime-to-semicircle divergences tend to zero. -/
theorem tendsto_klDiv_kesten_semicircle :
    Tendsto (fun p : Nat.Primes =>
      klDiv (kestenSpectralLaw p : Measure ℝ) (semicircleSpectralLaw : Measure ℝ))
      cofinite (𝓝 0) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    tendsto_kestenSemicircleEntropyValue
  change Tendsto (fun p => ENNReal.ofReal (kestenSemicircleEntropyValue p)) cofinite
    (𝓝 (ENNReal.ofReal 0)) at h
  simpa only [← klDiv_kesten_semicircle, ENNReal.ofReal_zero] using h

/-- The reverse extended-real semicircle-to-prime divergences also tend to zero. -/
theorem tendsto_klDiv_semicircle_kesten :
    Tendsto (fun p : Nat.Primes =>
      klDiv (semicircleSpectralLaw : Measure ℝ) (kestenSpectralLaw p : Measure ℝ))
      cofinite (𝓝 0) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    tendsto_semicircleKestenEntropyValue
  change Tendsto (fun p => ENNReal.ofReal (semicircleKestenEntropyValue p)) cofinite
    (𝓝 (ENNReal.ofReal 0)) at h
  simpa only [← klDiv_semicircle_kesten, ENNReal.ofReal_zero] using h

end
end GaloisForLFunctions.SelbergClass.Primon
