import GaloisForLFunctions.HTGeometry.BoundedRelationLogMagnitudeHypertranscendence
import GaloisForLFunctions.HTGeometry.PolynomialTorsionLanguageDefectLimit

/-!
# Entire polynomial-magnitude torsion-language series

This leaf packages the coefficient-profile ADE exclusion as the literal entire series from the
paper card.  It also supplies the deterministic unit-norm torsion-language phase existence
corollary, so no analytic carrier or phase-existence hypothesis remains outside the theorem.
-/

namespace GaloisForLFunctions

open Filter PowerSeries
open scoped Topology

noncomputable section

/-- The exact polynomial log-magnitude profile `B n^β`. -/
def polynomialTorsionLanguageProfile (B β : ℝ) (n : ℕ) : ℝ :=
  B * (n : ℝ) ^ β

/-- Polynomial log-magnitude growth with exponent above one is superlinear. -/
theorem tendsto_polynomialTorsionLanguageProfile_div_natCast_atTop
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β) :
    Tendsto
      (fun n => polynomialTorsionLanguageProfile B β n / (n : ℝ))
      atTop atTop := by
  have hlead : Tendsto (fun n : ℕ => B * (n : ℝ) ^ (β - 1)) atTop atTop :=
    ((tendsto_rpow_atTop (sub_pos.mpr hβ)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop hB
  refine hlead.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  rw [polynomialTorsionLanguageProfile,
    Real.rpow_sub_one hnpos.ne' β]
  ring

/-- The literal scalar entire-series carrier with coefficients
`exp (-B n^β) u_n`. -/
def polynomialTorsionLanguageFunction (B β : ℝ) (u : ℕ → ℂ) : ℂ → ℂ :=
  boundedRelationExponentialFunction
    (polynomialTorsionLanguageProfile B β) u

/-- The analytic carrier is the card's ordinary scalar power-series sum. -/
theorem polynomialTorsionLanguageFunction_eq_tsum
    (B β : ℝ) (u : ℕ → ℂ) (z : ℂ) :
    polynomialTorsionLanguageFunction B β u z =
      ∑' n : ℕ,
        ((Real.exp (-(B * (n : ℝ) ^ β)) : ℝ) : ℂ) * u n * z ^ n := by
  rw [polynomialTorsionLanguageFunction,
    boundedRelationExponentialFunction_eq_tsum]
  apply tsum_congr
  intro n
  rw [boundedRelationExponentialCoeff,
    polynomialTorsionLanguageProfile]
  rw [Complex.ofReal_exp]
  push_cast
  ring

/-- The polynomial-magnitude carrier is entire. -/
theorem contDiff_polynomialTorsionLanguageFunction
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β)
    {u : ℕ → ℂ} (huNorm : ∀ n, ‖u n‖ = 1) :
    ContDiff ℂ (⊤ : ℕ∞) (polynomialTorsionLanguageFunction B β u) := by
  exact contDiff_boundedRelationExponentialFunction
    (tendsto_polynomialTorsionLanguageProfile_div_natCast_atTop hB hβ)
    huNorm

/-- The entire carrier has exactly the prescribed Taylor coefficients. -/
theorem taylorPS_polynomialTorsionLanguageFunction
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β)
    {u : ℕ → ℂ} (huNorm : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (polynomialTorsionLanguageFunction B β u)) =
      ((Real.exp (-(B * (n : ℝ) ^ β)) : ℝ) : ℂ) * u n := by
  rw [polynomialTorsionLanguageFunction,
    taylorPS_boundedRelationExponentialFunction
      (tendsto_polynomialTorsionLanguageProfile_div_natCast_atTop hB hβ)
      huNorm]
  rw [boundedRelationExponentialCoeff,
    polynomialTorsionLanguageProfile]
  rw [Complex.ofReal_exp]
  push_cast
  ring

/-- **Literal polynomial TLU theorem.**  Every unit-norm torsion-language-universal phase makes
the entire series with coefficients `exp (-B n^β) u_n` hypertranscendental when `β > 2`. -/
theorem hypertranscendental_polynomialTorsionLanguageFunction
    {B β : ℝ} (hB : 0 < B) (hβ : 2 < β)
    {u : ℕ → ℂ} (huNorm : ∀ n, ‖u n‖ = 1)
    (hu : TorsionLanguageUniversal u) :
    Hypertranscendental (polynomialTorsionLanguageFunction B β u) := by
  apply hypertranscendental_of_polynomial_torsionLanguageUniversal
    (contDiff_polynomialTorsionLanguageFunction hB (by linarith) huNorm)
    hβ hB
    (taylorPS_polynomialTorsionLanguageFunction hB (by linarith) huNorm)
    huNorm hu

/-- **Deterministic existence corollary.**  For every `B > 0` and `β > 2`, the explicit
unit-filled universal torsion phase produces the card's entire hypertranscendental series. -/
theorem exists_unitTorsionPhase_polynomialMagnitude_hypertranscendental
    {B β : ℝ} (hB : 0 < B) (hβ : 2 < β) :
    ∃ u : ℕ → ℂ,
      TorsionLanguageUniversal u ∧
      (∀ n, ‖u n‖ = 1) ∧
      (∀ n, ∃ m : ℕ, 0 < m ∧ u n ^ m = 1) ∧
      ContDiff ℂ (⊤ : ℕ∞) (polynomialTorsionLanguageFunction B β u) ∧
      Hypertranscendental (polynomialTorsionLanguageFunction B β u) := by
  refine ⟨universalUnitTorsionPhase,
    universalUnitTorsionPhase_torsionLanguageUniversal,
    universalUnitTorsionPhase_norm,
    universalUnitTorsionPhase_isTorsion,
    contDiff_polynomialTorsionLanguageFunction hB (by linarith)
      universalUnitTorsionPhase_norm, ?_⟩
  exact hypertranscendental_polynomialTorsionLanguageFunction hB hβ
    universalUnitTorsionPhase_norm
    universalUnitTorsionPhase_torsionLanguageUniversal

end


end GaloisForLFunctions
