import GaloisForLFunctions.SelbergClass.Primon.CharacterMoments

/-!
# Arithmetic averaging of the charged local factor

The second-kind Chebyshev expansion of the charged-boson factor converges
absolutely throughout the disk. Its Kesten–McKay character moments remove
all odd degrees and turn the even degrees into a geometric series.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The charged local partition factor at a parameterized interior fugacity. -/
def phaseLocalFactor (s t : ℝ) : ℝ :=
  (1 - 2 * cavityDiskCoordinate s * Real.cos (Real.pi * t) +
    cavityDiskCoordinate s ^ 2)⁻¹

private theorem cavityChebyshevCoordinate_phase (t : ℝ) :
    cavityChebyshevCoordinate (-Real.cos (Real.pi * t)) (Real.sin (Real.pi * t)) =
      Real.cos (Real.pi * t) := by
  rw [cavityChebyshevCoordinate, neg_sq, Real.cos_sq_add_sin_sq, Real.sqrt_one]
  ring

/-- The character bound is uniform in the phase, including the two endpoints. -/
theorem abs_phaseCharacter_le (n : ℕ) (t : ℝ) :
    |phaseCharacter n t| ≤ (n : ℝ) + 1 := by
  have h := quadraticResponseCoeff_cavity_bound
    (-Real.cos (Real.pi * t)) (Real.sin (Real.pi * t)) n
  simpa only [cavityChebyshevCoordinate_phase, quadraticResponseCoeff_eq_chebyshev,
    phaseCharacter] using h

/-- The cavity response expansion is exactly the charged-primon character expansion. -/
theorem hasSum_phaseCharacter (s t : ℝ) :
    HasSum (fun n => phaseCharacter n t * cavityDiskCoordinate s ^ n)
      (phaseLocalFactor s t) := by
  have h := hasSum_quadraticCavityResponse
    (-Real.cos (Real.pi * t)) (Real.sin (Real.pi * t)) s
  simp only [cavityChebyshevCoordinate_phase, quadraticResponseCoeff_eq_chebyshev] at h
  have he : (1 - 2 * Real.cos (Real.pi * t) * cavityDiskCoordinate s +
      cavityDiskCoordinate s ^ 2)⁻¹ = phaseLocalFactor s t := by
    unfold phaseLocalFactor
    congr 1
    ring
  rw [he] at h
  exact h

private theorem summable_characterMajorant (s : ℝ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * |cavityDiskCoordinate s| ^ n) := by
  have hr : ‖(|cavityDiskCoordinate s| : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs] using abs_cavityDiskCoordinate_lt_one s
  simpa only [pow_one, add_mul, one_mul, Pi.add_apply] using
    (summable_pow_mul_geometric_of_norm_lt_one 1 hr).add
      (summable_geometric_of_norm_lt_one hr)

/-- Uniform character control justifies averaging the entire local series. -/
theorem hasSum_integral_phaseCharacter (p : Nat.Primes) (s : ℝ) :
    HasSum (fun n => phaseCharacterAverage p n * cavityDiskCoordinate s ^ n)
      (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * phaseLocalFactor s t) := by
  have h := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun n t => kestenMcKayDensity p t *
      (phaseCharacter n t * cavityDiskCoordinate s ^ n))
    (f := fun t => kestenMcKayDensity p t * phaseLocalFactor s t)
    (fun n t => kestenMcKayDensity p t *
      (((n : ℝ) + 1) * |cavityDiskCoordinate s| ^ n))
    (fun n => ((continuous_kestenMcKayDensity p).mul
      ((continuous_phaseCharacter n).mul continuous_const)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
        abs_of_nonneg (kestenMcKayDensity_nonneg p t)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (abs_phaseCharacter_le n t) (by positivity))
        (kestenMcKayDensity_nonneg p t))
    (Filter.Eventually.of_forall fun t => (summable_characterMajorant s).mul_left _)
    (by
      simp_rw [tsum_mul_left]
      exact ((continuous_kestenMcKayDensity p).mul continuous_const).continuousOn.integrableOn_Icc.mono_set
        Ioo_subset_Icc_self)
    (Filter.Eventually.of_forall fun t => (hasSum_phaseCharacter s t).mul_left _)
  have he : (fun n => ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      (phaseCharacter n t * cavityDiskCoordinate s ^ n)) =
      fun n => phaseCharacterAverage p n * cavityDiskCoordinate s ^ n := by
    funext n
    simp only [← mul_assoc, integral_mul_const, phaseCharacterAverage]
  rwa [he] at h

private theorem square_div_prime_bounds (p : Nat.Primes) (s : ℝ) :
    0 ≤ cavityDiskCoordinate s ^ 2 / (p : ℝ) ∧
      cavityDiskCoordinate s ^ 2 / (p : ℝ) < 1 := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hr : cavityDiskCoordinate s ^ 2 < 1 := by
    have h := pow_lt_one₀ (abs_nonneg (cavityDiskCoordinate s))
      (abs_cavityDiskCoordinate_lt_one s) (by omega : (2 : ℕ) ≠ 0)
    simpa only [sq_abs] using h
  exact ⟨div_nonneg (sq_nonneg _) (by linarith),
    (div_lt_one (by linarith)).mpr (hr.trans hp)⟩

/-- Kesten–McKay averaging of the charged-boson factor is a single geometric factor. -/
theorem integral_kesten_local_factor (p : Nat.Primes) (s : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * phaseLocalFactor s t) =
      (1 - cavityDiskCoordinate s ^ 2 / (p : ℝ))⁻¹ := by
  have hq := square_div_prime_bounds p s
  have hgeo := hasSum_geometric_of_norm_lt_one (by
    rw [Real.norm_eq_abs, abs_of_nonneg hq.1]
    exact hq.2)
  have he : HasSum (fun n => phaseCharacterAverage p (2 * n) *
      cavityDiskCoordinate s ^ (2 * n))
      (1 - cavityDiskCoordinate s ^ 2 / (p : ℝ))⁻¹ := by
    have heq : (fun n => phaseCharacterAverage p (2 * n) *
        cavityDiskCoordinate s ^ (2 * n)) =
        fun n => (cavityDiskCoordinate s ^ 2 / (p : ℝ)) ^ n := by
      funext n
      rw [phaseCharacterAverage_even, div_pow, pow_mul, inv_pow]
      ring
    rw [heq]
    exact hgeo
  have ho : HasSum (fun n => phaseCharacterAverage p (2 * n + 1) *
      cavityDiskCoordinate s ^ (2 * n + 1)) 0 := by
    simp only [phaseCharacterAverage_odd, zero_mul]
    exact hasSum_zero
  have hs : HasSum (fun n => phaseCharacterAverage p n * cavityDiskCoordinate s ^ n)
      ((1 - cavityDiskCoordinate s ^ 2 / (p : ℝ))⁻¹ + 0) := he.even_add_odd ho
  simp only [add_zero] at hs
  exact (hasSum_integral_phaseCharacter p s).unique hs

/-- The arithmetic mean is at least one throughout the disk. -/
theorem one_le_integral_kesten_local_factor (p : Nat.Primes) (s : ℝ) :
    1 ≤ ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * phaseLocalFactor s t := by
  rw [integral_kesten_local_factor]
  have hq := square_div_prime_bounds p s
  rw [← one_div]
  exact (le_div_iff₀ (by linarith)).mpr (by linarith)

end
end GaloisForLFunctions.SelbergClass.Primon
