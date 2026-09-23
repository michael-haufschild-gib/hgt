import GaloisForLFunctions.RHTower.SelbergMaassFullGradient

/-!
# Source Fourier energy on the centered modular strip

Actual gradient covariance gives a unit-period trace gradient. Finite integral
summation proves its exact equality with the period-normalized component
energies. The existing original-source first-frequency theorem therefore
bounds centered unit-strip energy by its actual trace mass, with the precise
congruence period retained.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassStripSlice
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassFullGradient
  SelbergMaassMean SelbergMaassFlux
noncomputable section

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The actual full trace gradient is continuous on every positive-height horizontal slice. -/
theorem gradient_slice_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => gradientDensity N f (point x y)) := by
  apply continuous_finsetSum Finset.univ
  intro q _
  have hq := (quotientForm N f q).2.2.1.1
  exact (Complex.continuous_normSq.comp
    (slice_continuous (directional_contDiffOn hq (m := 1) le_rfl (1 : ℂ)).continuousOn hy)).add
      (Complex.continuous_normSq.comp
        (slice_continuous (directional_contDiffOn hq (m := 1) le_rfl Complex.I).continuousOn hy))

/-- Modular translation gives period one to the actual total gradient. -/
theorem gradient_slice_periodic {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x : ℝ => gradientDensity N f (point x y)) 1 := by
  intro x
  let z : ℍ := ⟨point x y, by simpa [point] using hy⟩
  let w : ℍ := ⟨point (x + 1) y, by simpa [point] using hy⟩
  have hz : T • z = w := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_T_smul]
    simp only [UpperHalfPlane.coe_vadd, z, w, point]
    push_cast
    ring
  have h := hyperbolicGradient_invariant N f T z
  rw [hz] at h
  have hi : z.im = y := by simp [z, point, UpperHalfPlane.im]
  have hj : w.im = y := by simp [w, point, UpperHalfPlane.im]
  unfold hyperbolicGradient at h
  rw [hi, hj] at h
  exact mul_left_cancel₀ (pow_ne_zero 2 hy.ne') h

/-- Unit-strip energy is the sum of the original period-normalized source energies. -/
theorem gradient_integral_eq_sum {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, gradientDensity N f (point x y)) =
      ∑ q : Deck N, gradientEnergy N (quotientForm N f q) y := by
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun x => gradientDensity N f (point x y)) volume a b :=
    (gradient_slice_continuous N f hy).intervalIntegrable
  have hper := (gradient_slice_periodic N f hy).intervalIntegral_add_zsmul_eq
    ((N + 1 : ℕ) : ℤ) 0 hint
  have hscale : (∫ x in (0 : ℝ)..(N + 1 : ℕ), gradientDensity N f (point x y)) =
      ((N + 1 : ℕ) : ℝ) * ∫ x in (0 : ℝ)..1, gradientDensity N f (point x y) := by
    simpa only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] using hper
  have hq (q : Deck N) : gradientEnergy N (quotientForm N f q) y =
      ((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
        Complex.normSq (dir 1 ((quotientForm N f q).1.1 ∘ ofComplex) (point x y)) +
        Complex.normSq (dir Complex.I ((quotientForm N f q).1.1 ∘ ofComplex) (point x y)) := by
    have hs := (quotientForm N f q).2.2.1.1
    have h1 := (directional_contDiffOn hs (m := 1) le_rfl (1 : ℂ)).continuousOn
    have hI := (directional_contDiffOn hs (m := 1) le_rfl Complex.I).continuousOn
    rw [gradientEnergy, pairing_self _ h1 hy, pairing_self _ hI hy]
    congr 1
    have hsum := intervalIntegral.integral_add (a := (0 : ℝ)) (b := (N + 1 : ℕ)) (μ := volume)
      ((Complex.continuous_normSq.comp (slice_continuous h1 hy)).intervalIntegrable _ _)
      ((Complex.continuous_normSq.comp (slice_continuous hI hy)).intervalIntegrable _ _)
    simpa only [Function.comp_def, dir, directional,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ))] using hsum.symm
  simp_rw [hq]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum]
  · change _ = ((N + 1 : ℕ) : ℝ)⁻¹ *
      ∫ x in (0 : ℝ)..(N + 1 : ℕ), gradientDensity N f (point x y)
    rw [hscale]
    field_simp
  · intro q _
    have hs := (quotientForm N f q).2.2.1.1
    exact ((Complex.continuous_normSq.comp
      (slice_continuous (directional_contDiffOn hs (m := 1) le_rfl (1 : ℂ)).continuousOn hy)).add
      (Complex.continuous_normSq.comp
        (slice_continuous (directional_contDiffOn hs (m := 1) le_rfl Complex.I).continuousOn hy))).intervalIntegrable _ _

/-- The literal source Fourier gap controls the complete centered unit-strip energy. -/
theorem centered_energy_ge_mass (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : 0 < y) :
    (2 * Real.pi / (N + 1 : ℕ)) ^ (2 : ℕ) *
        (∫ x in (-(1 / 2 : ℝ))..(1 / 2), density N f (ofComplex (point x y))) ≤
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), gradientDensity N f (point x y) := by
  have hD := (density_slice_periodic N f hy).intervalIntegral_add_eq (-(1 / 2)) 0
  have hG := (gradient_slice_periodic N f hy).intervalIntegral_add_eq (-(1 / 2)) 0
  norm_num at hD hG
  rw [hD, hG, density_integral_eq_sum_mass N f hy, gradient_integral_eq_sum N f hy,
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun q _ => gradientEnergy_ge_first_frequency N lam (quotientForm N f q) hy)

end
end GaloisForLFunctions.RHTower.SelbergMaassStripSlice
