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

/-- The exact open Abel radius of the endpoint purity susceptibility. -/
def PrimeArchEndpointBernsteinAbelCriticalRadius (R : ℝ) : Prop :=
  0 < R ∧
    (∀ t : ℝ, 0 ≤ t → t < R →
      PrimeArchEndpointBernsteinAbelSusceptibilityFinite t) ∧
    (∀ t : ℝ, R < t →
      ¬ PrimeArchEndpointBernsteinAbelSusceptibilityFinite t)

private lemma not_summable_of_tendsto_atTop
    {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) : ¬ Summable f := by
  intro hsum
  have hone : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ f n :=
    (hf.eventually_gt_atTop 1).mono fun _ h => h.le
  have hcontra : (1 : ℝ) ≤ 0 := ge_of_tendsto hsum.tendsto_atTop_zero hone
  linarith

/-- Under RH the exact Abel radius is one. -/
theorem primeArchEndpointBernsteinAbelCriticalRadius_one_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchEndpointBernsteinAbelCriticalRadius 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro t ht0 ht1
    exact primeArchEndpointBernsteinAbelSusceptibilityFinite_of_riemannHypothesis
      hRH ht0 ht1
  · intro t ht
    have ht0 : 0 ≤ t := (zero_lt_one.trans ht).le
    have hbound : ∀ n : ℕ,
        normalizedPrimeArchMoment 0 ^ 2 * t ^ n / (n + 1 : ℝ) ≤
          primeArchEndpointBernsteinPurity n * t ^ n := by
      intro n
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
      calc
        normalizedPrimeArchMoment 0 ^ 2 * t ^ n ≤
            ((n + 1 : ℝ) * primeArchEndpointBernsteinPurity n) * t ^ n :=
          mul_le_mul_of_nonneg_right
            (mass_sq_le_card_mul_primeArchEndpointBernsteinPurity n)
            (pow_nonneg ht0 n)
        _ = (primeArchEndpointBernsteinPurity n * t ^ n) * (n + 1 : ℝ) := by ring
    have hdiv : Tendsto
        (fun n : ℕ => primeArchEndpointBernsteinPurity n * t ^ n) atTop atTop :=
      tendsto_atTop_mono' atTop (Eventually.of_forall hbound)
        (tendsto_const_mul_pow_div_nat_add_one_atTop ht
          (sq_pos_of_pos normalizedPrimeArchMoment_zero_pos))
    exact not_summable_of_tendsto_atTop hdiv

/-- Under failure of RH the Abel radius is the reciprocal square of a genuinely attained maximal
endpoint atom amplitude. -/
theorem exists_attained_primeArchEndpointBernsteinAbelCriticalRadius_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ B : ℝ,
      PrimeArchEndpointBernsteinAttainedExactThreshold B ∧
      PrimeArchEndpointBernsteinAbelCriticalRadius (1 / B ^ 2) := by
  obtain ⟨B, η, hB, hBsector, hη, hattained, hmax, hupper,
      hlower, habove, hbelow⟩ :=
    exists_primeArchEndpointBernstein_exactExponentialThreshold_of_not_rh hRH
  have hBpos : 0 < B := lt_trans zero_lt_one hB
  have hBsqpos : 0 < B ^ 2 := sq_pos_of_pos hBpos
  have hthreshold : PrimeArchEndpointBernsteinAttainedExactThreshold B :=
    ⟨hB, hBsector, hattained, hmax,
      ⟨hBsqpos, habove, hbelow⟩⟩
  refine ⟨B, hthreshold, one_div_pos.mpr hBsqpos, ?_, ?_⟩
  · intro t ht0 htR
    let q : ℝ := B ^ 2 * t
    have hq0 : 0 ≤ q := by
      dsimp only [q]
      exact mul_nonneg hBsqpos.le ht0
    have hq1 : q < 1 := by
      dsimp only [q]
      have := (lt_div_iff₀ hBsqpos).mp htR
      nlinarith
    have hgeo : Summable (fun n : ℕ => q ^ n) :=
      summable_geometric_of_lt_one hq0 hq1
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (bernsteinCoefficientPurity_nonneg _ n) (pow_nonneg ht0 n))
      (fun n => ?_) (hgeo.mul_left (xiReciprocalSquareAbsoluteMass ^ 2))
    calc
      primeArchEndpointBernsteinPurity n * t ^ n ≤
          (xiReciprocalSquareAbsoluteMass * B ^ n) ^ 2 * t ^ n :=
        mul_le_mul_of_nonneg_right (hupper n) (pow_nonneg ht0 n)
      _ = xiReciprocalSquareAbsoluteMass ^ 2 * q ^ n := by
        dsimp only [q]
        simp only [mul_pow]
        ring
  · intro t hRt
    have htpos : 0 < t := lt_trans (one_div_pos.mpr hBsqpos) hRt
    have hinvB : 1 / t < B ^ 2 := by
      apply (div_lt_iff₀ htpos).2
      have := (div_lt_iff₀ hBsqpos).mp hRt
      nlinarith
    have hdiv0 := hbelow (1 / t) (one_div_pos.mpr htpos) hinvB
    have hdiv : Tendsto
        (fun n : ℕ => primeArchEndpointBernsteinPurity n * t ^ n) atTop atTop := by
      convert hdiv0 using 1
      funext n
      rw [one_div, inv_pow, div_inv_eq_mul]
    exact not_summable_of_tendsto_atTop hdiv

/-- The open Abel critical radius is unique. -/
theorem primeArchEndpointBernsteinAbelCriticalRadius_unique
    {R S : ℝ}
    (hR : PrimeArchEndpointBernsteinAbelCriticalRadius R)
    (hS : PrimeArchEndpointBernsteinAbelCriticalRadius S) : R = S := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hRS | hSR
  · let t : ℝ := (R + S) / 2
    have ht0 : 0 ≤ t := by
      dsimp only [t]
      linarith [hR.1, hS.1]
    have hRt : R < t := by
      dsimp only [t]
      linarith
    have htS : t < S := by
      dsimp only [t]
      linarith
    exact (hR.2.2 t hRt) (hS.2.1 t ht0 htS)
  · let t : ℝ := (S + R) / 2
    have ht0 : 0 ≤ t := by
      dsimp only [t]
      linarith [hR.1, hS.1]
    have hSt : S < t := by
      dsimp only [t]
      linarith
    have htR : t < R := by
      dsimp only [t]
      linarith
    exact (hS.2.2 t hSt) (hR.2.1 t ht0 htR)

/-- The unique Abel radius lies in the explicit narrow collar and equals one exactly under RH. -/
theorem existsUnique_primeArchEndpointBernsteinAbelCriticalRadius :
    ∃! R : ℝ,
      250000 / 251001 < R ∧ R ≤ 1 ∧
      PrimeArchEndpointBernsteinAbelCriticalRadius R ∧
      (RiemannHypothesis ↔ R = 1) := by
  by_cases hRH : RiemannHypothesis
  · have hR :=
      primeArchEndpointBernsteinAbelCriticalRadius_one_of_riemannHypothesis hRH
    refine ⟨1, ⟨by norm_num, le_rfl, hR, ⟨fun _ => rfl, fun _ => hRH⟩⟩, ?_⟩
    intro S hS
    exact primeArchEndpointBernsteinAbelCriticalRadius_unique hS.2.2.1 hR
  · obtain ⟨B, hB, hR⟩ :=
      exists_attained_primeArchEndpointBernsteinAbelCriticalRadius_of_not_rh hRH
    have hBpos : 0 < B := lt_trans zero_lt_one hB.1
    have hBsqpos : 0 < B ^ 2 := sq_pos_of_pos hBpos
    have hBsector' : B < (501 / 500 : ℝ) := by
      simpa only [xiSectorConfinedBernsteinAmplitudeBase] using hB.2.1
    have hBsqsector : B ^ 2 < (501 / 500 : ℝ) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hBsector')
        (add_pos hBpos (by norm_num : (0 : ℝ) < 501 / 500))]
    have hRlower : (250000 / 251001 : ℝ) < 1 / B ^ 2 := by
      apply (lt_div_iff₀ hBsqpos).2
      norm_num at hBsqsector ⊢
      linarith
    have hRlt : 1 / B ^ 2 < (1 : ℝ) :=
      (div_lt_one hBsqpos).2 (by nlinarith [hB.1])
    refine ⟨1 / B ^ 2, ⟨hRlower, hRlt.le, hR, ?_⟩, ?_⟩
    · constructor
      · exact fun h => (hRH h).elim
      · intro hEq
        linarith
    · intro S hS
      exact primeArchEndpointBernsteinAbelCriticalRadius_unique hS.2.2.1 hR

/-- The exact susceptibility radius and the exact purity/dissipation exponent are reciprocal. -/
theorem primeArchEndpointBernsteinAbelRadius_mul_exactExponent_eq_one
    {R E : ℝ}
    (hR : PrimeArchEndpointBernsteinAbelCriticalRadius R)
    (hE : PrimeArchEndpointBernsteinExactExponentialExponent E) :
    R * E = 1 := by
  by_cases hRH : RiemannHypothesis
  · have hR1 :=
      primeArchEndpointBernsteinAbelCriticalRadius_one_of_riemannHypothesis hRH
    have hE1 := primeArchEndpointBernsteinExactExponentialExponent_one_of_rh hRH
    rw [primeArchEndpointBernsteinAbelCriticalRadius_unique hR hR1,
      primeArchEndpointBernsteinExactExponentialExponent_unique hE hE1]
    norm_num
  · obtain ⟨B, hB, hRB⟩ :=
      exists_attained_primeArchEndpointBernsteinAbelCriticalRadius_of_not_rh hRH
    have hEB : PrimeArchEndpointBernsteinExactExponentialExponent (B ^ 2) := hB.2.2.2.2
    rw [primeArchEndpointBernsteinAbelCriticalRadius_unique hR hRB,
      primeArchEndpointBernsteinExactExponentialExponent_unique hE hEB]
    have hBne : B ≠ 0 := (lt_trans zero_lt_one hB.1).ne'
    field_simp [hBne]

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
susceptibility throughout the explicit narrow-sector chamber.  It has a unique exact Abel radius
strictly beyond that chamber and at most one; RH is exactly the assertion that this radius reaches
the endpoint, equivalently that susceptibility is finite on the whole open unit interval. -/
theorem primeArchEndpointBernsteinAbelSelectionMaster :
    (∀ n i : ℕ, n ≤ 13 →
      0 ≤ bernsteinCoefficient
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n i) ∧
    (∀ N : ℕ, N ≤ 12 →
      hausdorffBernsteinNegativeMass
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) N = 0) ∧
    (∀ t : ℝ, 0 ≤ t → t < 250000 / 251001 →
      PrimeArchEndpointBernsteinAbelSusceptibilityFinite t) ∧
    (∃! R : ℝ,
      250000 / 251001 < R ∧ R ≤ 1 ∧
      PrimeArchEndpointBernsteinAbelCriticalRadius R ∧
      (RiemannHypothesis ↔ R = 1)) ∧
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
    existsUnique_primeArchEndpointBernsteinAbelCriticalRadius,
    riemannHypothesis_iff_primeArchEndpointBernsteinAbelSusceptibilityFinite⟩

end

end RHTower
