import GaloisForLFunctions.RHTower.PrimeArchBernsteinNarrowSectorDissipationMaster
import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation
import GaloisForLFunctions.RHTower.PrimeArchCofinalHausdorffDiagonalRH

/-!
# Abel susceptibility of the prime--archimedean Bernstein source

The positive endpoint purity has a canonical Abel transform

`sum_n purity(n) * t^n`.

The narrow-sector divisor estimate gives an unconditional open interval of convergence.  The
whole open unit interval is available exactly under RH.  Failure of RH supplies a source-attained
exponential mode, hence a parameter strictly inside the unit interval at which the Abel series
diverges.  The same module records the finite source-positive chamber already supplied by the
scaled Hausdorff rectangle.
-/

open Complex Filter Topology
open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

/-- The endpoint purity has finite Abel susceptibility at parameter `t`. -/
def PrimeArchEndpointBernsteinAbelSusceptibilityFinite (t : ℝ) : Prop :=
  Summable (fun n : ℕ => primeArchEndpointBernsteinPurity n * t ^ n)

/-- RH puts the positive endpoint susceptibility in the full open unit interval. -/
theorem primeArchEndpointBernsteinAbelSusceptibilityFinite_of_riemannHypothesis
    (hRH : RiemannHypothesis) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    PrimeArchEndpointBernsteinAbelSusceptibilityFinite t := by
  have hgeo : Summable (fun n : ℕ => t ^ n) :=
    summable_geometric_of_lt_one ht0 ht1
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (bernsteinCoefficientPurity_nonneg _ n) (pow_nonneg ht0 n))
    (fun n => ?_) (hgeo.mul_left (normalizedPrimeArchMoment 0 ^ 2))
  exact mul_le_mul_of_nonneg_right
    (primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis hRH n)
    (pow_nonneg ht0 n)

/-- The narrow-sector divisor estimate gives an unconditional Abel chamber. -/
theorem primeArchEndpointBernsteinAbelSusceptibilityFinite_of_sector_contraction
    {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : xiSectorConfinedBernsteinAmplitudeBase ^ 2 * t < 1) :
    PrimeArchEndpointBernsteinAbelSusceptibilityFinite t := by
  let q := xiSectorConfinedBernsteinAmplitudeBase ^ 2 * t
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    exact mul_nonneg (sq_nonneg _) ht0
  have hgeo : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq0 ht1
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (bernsteinCoefficientPurity_nonneg _ n) (pow_nonneg ht0 n))
    (fun n => ?_) (hgeo.mul_left (xiReciprocalSquareAbsoluteMass ^ 2))
  calc
    primeArchEndpointBernsteinPurity n * t ^ n ≤
        (xiReciprocalSquareAbsoluteMass *
          xiSectorConfinedBernsteinAmplitudeBase ^ n) ^ 2 * t ^ n :=
      mul_le_mul_of_nonneg_right
        (primeArchEndpointBernsteinPurity_le_sectorConfined n) (pow_nonneg ht0 n)
    _ = xiReciprocalSquareAbsoluteMass ^ 2 * q ^ n := by
      dsimp only [q]
      simp only [mul_pow]
      ring

/-- In rational form, the unconditional susceptibility chamber reaches
`t < 250000 / 251001`. -/
theorem primeArchEndpointBernsteinAbelSusceptibilityFinite_below_narrowSectorRadius
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 250000 / 251001) :
    PrimeArchEndpointBernsteinAbelSusceptibilityFinite t := by
  apply primeArchEndpointBernsteinAbelSusceptibilityFinite_of_sector_contraction ht0
  rw [xiSectorConfinedBernsteinAmplitudeBase_sq_eq]
  norm_num at ht1 ⊢
  linarith

/-- Failure of RH is witnessed by divergence at a positive parameter strictly inside the unit
interval.  The parameter is selected from the source-attained lower exponential envelope. -/
theorem exists_nonfinite_primeArchEndpointBernsteinAbelSusceptibility_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ¬ PrimeArchEndpointBernsteinAbelSusceptibilityFinite t := by
  obtain ⟨ρ, η, hρ, hη, hlower⟩ :=
    exists_eventually_exponential_lower_envelope_primeArchEndpointBernsteinPurity_of_not_rh hRH
  have hρpos : 0 < ρ := lt_trans (by norm_num) hρ
  let t : ℝ := (1 + 1 / ρ) / 2
  have hinvpos : 0 < 1 / ρ := one_div_pos.mpr hρpos
  have hinvlt : 1 / ρ < 1 := (div_lt_one hρpos).2 hρ
  have ht0 : 0 < t := by
    dsimp only [t]
    positivity
  have ht1 : t < 1 := by
    dsimp only [t]
    linarith
  have hρt : 1 < ρ * t := by
    have heq : ρ * t = (ρ + 1) / 2 := by
      dsimp only [t]
      field_simp
    rw [heq]
    linarith
  refine ⟨t, ht0, ht1, ?_⟩
  intro hsum
  have hbound : ∀ᶠ n : ℕ in atTop,
      η * (ρ * t) ^ n / (n + 1 : ℝ) ≤
        primeArchEndpointBernsteinPurity n * t ^ n := by
    filter_upwards [hlower] with n hn
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
    calc
      η * (ρ * t) ^ n = (η * ρ ^ n) * t ^ n := by
        rw [mul_pow]
        ring
      _ ≤ ((n + 1 : ℝ) * primeArchEndpointBernsteinPurity n) * t ^ n :=
        mul_le_mul_of_nonneg_right hn (pow_nonneg ht0.le n)
      _ = (primeArchEndpointBernsteinPurity n * t ^ n) * (n + 1 : ℝ) := by ring
  have hdiv : Tendsto
      (fun n : ℕ => primeArchEndpointBernsteinPurity n * t ^ n) atTop atTop :=
    tendsto_atTop_mono' atTop hbound
      (tendsto_const_mul_pow_div_nat_add_one_atTop hρt hη)
  have hone : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ primeArchEndpointBernsteinPurity n * t ^ n :=
    (hdiv.eventually_gt_atTop 1).mono fun _ h => h.le
  have hcontra : (1 : ℝ) ≤ 0 := ge_of_tendsto hsum.tendsto_atTop_zero hone
  linarith

/-- **Abel susceptibility RH law.** The source-defined positive susceptibility is finite at
every parameter of the open unit interval exactly when RH holds. -/
theorem riemannHypothesis_iff_primeArchEndpointBernsteinAbelSusceptibilityFinite :
    RiemannHypothesis ↔
      ∀ t : ℝ, 0 ≤ t → t < 1 →
        PrimeArchEndpointBernsteinAbelSusceptibilityFinite t := by
  constructor
  · intro hRH t ht0 ht1
    exact primeArchEndpointBernsteinAbelSusceptibilityFinite_of_riemannHypothesis
      hRH ht0 ht1
  · intro h
    by_contra hRH
    obtain ⟨t, ht0, ht1, ht⟩ :=
      exists_nonfinite_primeArchEndpointBernsteinAbelSusceptibility_of_not_rh hRH
    exact ht (h t ht0.le ht1)

/-- The unconditional scaled-Hausdorff rectangle makes every endpoint Bernstein coefficient of
degree at most thirteen nonnegative. -/
theorem primeArchEndpointBernsteinCoefficient_nonnegative_of_degree_le_thirteen
    (n i : ℕ) (hn : n ≤ 13) :
    0 ≤ bernsteinCoefficient
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n i := by
  apply momentFunctional_bernsteinPolynomial_nonnegative_of_scaledHausdorffDiagonal
    primeArchEndpointHausdorffRadius_pos
  intro k hk
  exact scaledPrimeArchEndpointHausdorffDifference_rectangle_nonnegative
    k (n - k) (by omega) (by omega)

/-- Consequently the canonical endpoint Bernstein system has exactly zero negative mass through
defect degree twelve. -/
theorem primeArchEndpointHausdorffBernsteinNegativeMass_eq_zero_of_degree_le_twelve
    (N : ℕ) (hN : N ≤ 12) :
    hausdorffBernsteinNegativeMass
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) N = 0 := by
  rw [hausdorffBernsteinNegativeMass]
  apply Finset.sum_eq_zero
  intro i hi
  apply negPart_eq_zero.mpr
  exact primeArchEndpointBernsteinCoefficient_nonnegative_of_degree_le_thirteen
    (N + 1) i (by omega)

/-- **Finite-to-cofinal Abel selection master theorem.**  The actual completed Xi source is
unconditionally positive through thirteen Bernstein degrees and has finite positive Abel
susceptibility throughout the explicit narrow-sector chamber.  RH is exactly the assertion that
this finite source-selected chamber extends to every point of the open unit interval. -/
theorem primeArchEndpointBernsteinAbelSelectionMaster :
    (∀ n i : ℕ, n ≤ 13 →
      0 ≤ bernsteinCoefficient
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n i) ∧
    (∀ N : ℕ, N ≤ 12 →
      hausdorffBernsteinNegativeMass
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) N = 0) ∧
    (∀ t : ℝ, 0 ≤ t → t < 250000 / 251001 →
      PrimeArchEndpointBernsteinAbelSusceptibilityFinite t) ∧
    (RiemannHypothesis ↔
      ∀ t : ℝ, 0 ≤ t → t < 1 →
        PrimeArchEndpointBernsteinAbelSusceptibilityFinite t) := by
  exact ⟨
    fun n i hn =>
      primeArchEndpointBernsteinCoefficient_nonnegative_of_degree_le_thirteen n i hn,
    fun N hN =>
      primeArchEndpointHausdorffBernsteinNegativeMass_eq_zero_of_degree_le_twelve N hN,
    fun t ht0 ht1 =>
      primeArchEndpointBernsteinAbelSusceptibilityFinite_below_narrowSectorRadius ht0 ht1,
    riemannHypothesis_iff_primeArchEndpointBernsteinAbelSusceptibilityFinite⟩

end

end RHTower
