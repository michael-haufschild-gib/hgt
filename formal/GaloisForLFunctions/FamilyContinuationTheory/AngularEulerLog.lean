import GaloisForLFunctions.FamilyContinuationTheory.AngularRayFamily
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.LogarithmicInputs

/-! # Euler logarithms for actual angular L-functions

Multiplicative angular ideal coefficients connect primitive and original-modulus
continuations to the same absolutely convergent Euler logarithm.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
namespace GaloisForLFunctions.FamilyContinuationTheory
open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein HeckeFamily
open IsDedekindDomain
local notation "O" => Eisenstein.O

/-- Multiplication by the sextic infinity type preserves multiplicativity and zero extension. -/
def angularIdealTwist (a : Ideal O →*₀ ℂ) (k : ℕ) : Ideal O →*₀ ℂ where
  toFun I := a I * idealPsiSix I ^ k
  map_zero' := by rw [map_zero, zero_mul]
  map_one' := by rw [map_one, idealPsiSix_one, one_pow, one_mul]
  map_mul' I J := by simp only [map_mul, idealPsiSix_mul, mul_pow]; ring

theorem angularIdealTwist_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (k : ℕ) (I : Ideal O) : ‖angularIdealTwist a k I‖ ≤ 1 := by
  change ‖a I * idealPsiSix I ^ k‖ ≤ 1
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (ha I) (pow_nonneg (norm_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) (norm_idealPsiSix_le_one I))

private def angularPrimeEquiv : HeckeIdealSeries.PrimeIdeal ≃ HeightOneSpectrum O where
  toFun P := ⟨P.val, Ideal.isPrime_of_prime P.property, P.property.ne_zero⟩
  invFun v := ⟨v.asIdeal, Ideal.prime_of_isPrime v.ne_bot v.isPrime⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The ideal-series Euler product in height-one-spectrum notation. -/
theorem angularIdealTwist_series_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (k : ℕ) {w : ℂ} (hw : 1 < w.re) :
    IdealEuler.series (angularIdealTwist a k) w =
      ∏' v : HeightOneSpectrum O,
        (1 - idealPsiSix v.asIdeal ^ k * a v.asIdeal *
          (primeNorm v : ℂ) ^ (-w))⁻¹ := by
  rw [IdealEuler.series_euler _ (angularIdealTwist_norm_le a ha k) w hw]
  calc
    _ = ∏' P : HeckeIdealSeries.PrimeIdeal,
        (1 - idealPsiSix (angularPrimeEquiv P).asIdeal ^ k * a (angularPrimeEquiv P).asIdeal *
          (primeNorm (angularPrimeEquiv P) : ℂ) ^ (-w))⁻¹ := by
      apply tprod_congr
      intro P
      change (1 - (a P.val * idealPsiSix P.val ^ k) * fullIdealWeight w P.val)⁻¹ = _
      simp only [fullIdealWeight, P.property.ne_zero, if_false]
      congr 2
      change a P.val * idealPsiSix P.val ^ k * (Ideal.absNorm P.val : ℂ) ^ (-w) = _
      change _ = idealPsiSix P.val ^ k * a P.val * (Ideal.absNorm P.val : ℂ) ^ (-w)
      ring
    _ = _ := angularPrimeEquiv.tprod_eq (fun v : HeightOneSpectrum O =>
      (1 - idealPsiSix v.asIdeal ^ k * a v.asIdeal * (primeNorm v : ℂ) ^ (-w))⁻¹)

/-- Primitive angular continuation agrees with its multiplicative ideal series. -/
theorem grossenLFunction_eq_angularIdealSeries (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) {w : ℂ} (hw : 1 < w.re) :
    grossenLFunction 𝔪 ψ k w = IdealEuler.series
      (angularIdealTwist (primitiveIdealValue 𝔪 ψ) k) w := by
  rw [grossenLFunction_eq_eulerProduct 𝔪 ψ hk hw,
    angularIdealTwist_series_euler _ (norm_primitiveIdealValue_le_one 𝔪 ψ) k hw]
  rfl

private def angularEmptyPrimeEquiv : HeightOneSpectrum O ≃
    {v : HeightOneSpectrum O // v ∉ (∅ : Finset (HeightOneSpectrum O))} where
  toFun v := ⟨v, Finset.notMem_empty v⟩
  invFun v := v.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- At the original modulus the series has exactly the finite row coefficients. -/
theorem angularRowLFunction_eq_idealSeries (χ : Character) {k : ℕ} (hk : 1 ≤ k)
    {w : ℂ} (hw : 1 < w.re) :
    angularRowLFunction χ k ∅ w = IdealEuler.series (angularIdealTwist (idealCoeff χ) k) w := by
  rw [angularRowLFunction_eq_eulerProduct χ hk ∅ hw,
    angularIdealTwist_series_euler _ (idealCoeff_norm_le_one χ) k hw]
  exact (angularEmptyPrimeEquiv.tprod_eq _).symm

/-- A bounded analytic logarithm on the absolute-convergence disk for every primitive
angular L-function, with a constant independent of both characters and infinity type. -/
theorem grossenLFunction_inner_log (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    let E := HeckeEulerLog.eulerLog (angularIdealTwist (primitiveIdealValue 𝔪 ψ) k)
    DifferentiableOn ℂ E (Metric.ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      Set.EqOn (Complex.exp ∘ E) (grossenLFunction 𝔪 ψ k)
        (Metric.ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ w ∈ Metric.closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖E w‖ ≤ HeckeEulerLog.eulerLogBound :=
  HeckeEulerLog.continued_inner_disk _
    (angularIdealTwist_norm_le _ (norm_primitiveIdealValue_le_one 𝔪 ψ) k)
    (grossenLFunction 𝔪 ψ k) (fun _ hw => grossenLFunction_eq_angularIdealSeries 𝔪 ψ hk hw) t

/-- The same inner-disk logarithm applies to every finite row character. -/
theorem angularRowLFunction_inner_log (χ : Character) {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    let E := HeckeEulerLog.eulerLog (angularIdealTwist (idealCoeff χ) k)
    DifferentiableOn ℂ E (Metric.ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      Set.EqOn (Complex.exp ∘ E) (angularRowLFunction χ k ∅)
        (Metric.ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ w ∈ Metric.closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖E w‖ ≤ HeckeEulerLog.eulerLogBound :=
  HeckeEulerLog.continued_inner_disk _
    (angularIdealTwist_norm_le _ (idealCoeff_norm_le_one χ) k)
    (angularRowLFunction χ k ∅) (fun _ hw => angularRowLFunction_eq_idealSeries χ hk hw) t

end GaloisForLFunctions.FamilyContinuationTheory
