import GaloisForLFunctions.RHTower.PrimeArchBernsteinAbelSusceptibility

/-!
# Closed Abel boundary and root growth of the endpoint Bernstein purity

The earlier Abel-radius API separated convergence below the critical radius from divergence
strictly above it.  The source envelopes also force harmonic divergence at the radius itself.
Thus the convergence set on the nonnegative real axis is exactly the half-open interval `[0,R)`.

The exact exponential-threshold predicate likewise determines the ordinary real nth-root limit.
This file proves that implication abstractly for every nonnegative real sequence, then specializes
it to the completed prime--archimedean Bernstein purity.
-/

open Complex Filter Topology
open scoped BigOperators Polynomial
open Polynomial

namespace RHTower

noncomputable section

private lemma rpow_inv_natCast_pow_eq
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    (a ^ n) ^ ((n : ℝ)⁻¹) = a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  rw [show (n : ℝ) * (n : ℝ)⁻¹ = 1 by
    exact mul_inv_cancel₀ (by exact_mod_cast hn.ne')]
  exact Real.rpow_one a

/-- A positive exact exponential threshold is the ordinary real nth-root limit.  This is the
abstract root-limit theorem behind the endpoint-purity specialization below. -/
theorem tendsto_rpow_inv_natCast_of_exactExponentialExponentAtNatInfinity
    {f : ℕ → ℝ} {E : ℝ} (hf : ∀ n, 0 ≤ f n)
    (hE : ExactExponentialExponentAtNatInfinity f E) :
    Tendsto (fun n : ℕ => (f n) ^ ((n : ℝ)⁻¹)) atTop (nhds E) := by
  apply tendsto_order.2
  constructor
  · intro a haE
    let c : ℝ := (max a 0 + E) / 2
    have hmaxE : max a 0 < E := (max_lt_iff.mpr ⟨haE, hE.1⟩)
    have hc0 : 0 < c := by
      dsimp only [c]
      have hmax0 : 0 ≤ max a 0 := le_max_right _ _
      linarith
    have hac : a < c := by
      dsimp only [c]
      have hamax : a ≤ max a 0 := le_max_left _ _
      linarith
    have hcE : c < E := by
      dsimp only [c]
      linarith
    have hbelow := hE.2.2 c hc0 hcE
    have hlarge : ∀ᶠ n : ℕ in atTop, 1 < f n / c ^ n :=
      hbelow.eventually_gt_atTop 1
    filter_upwards [hlarge, eventually_ge_atTop 1] with n hn hnone
    have hcn : 0 < c ^ n := pow_pos hc0 n
    have hpow : c ^ n < f n := by
      simpa only [one_mul] using (lt_div_iff₀ hcn).mp hn
    have hinv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hnone)
    calc
      a < c := hac
      _ = (c ^ n) ^ ((n : ℝ)⁻¹) :=
        (rpow_inv_natCast_pow_eq hc0 hnone).symm
      _ < (f n) ^ ((n : ℝ)⁻¹) :=
        Real.rpow_lt_rpow (pow_nonneg hc0.le n) hpow hinv
  · intro b hEb
    have hb0 : 0 < b := hE.1.trans hEb
    have habove := hE.2.1 b hEb
    have hsmall : ∀ᶠ n : ℕ in atTop, f n / b ^ n < 1 :=
      habove.eventually_lt_const zero_lt_one
    filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hnone
    have hbn : 0 < b ^ n := pow_pos hb0 n
    have hpow : f n < b ^ n := (div_lt_one hbn).mp hn
    have hinv : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hnone)
    calc
      (f n) ^ ((n : ℝ)⁻¹) < (b ^ n) ^ ((n : ℝ)⁻¹) :=
        Real.rpow_lt_rpow (hf n) hpow hinv
      _ = b := rpow_inv_natCast_pow_eq hb0 hnone

/-- The exact endpoint-purity exponent is its real nth-root limit. -/
theorem tendsto_primeArchEndpointBernsteinPurity_rpow_inv_natCast
    {E : ℝ} (hE : PrimeArchEndpointBernsteinExactExponentialExponent E) :
    Tendsto
      (fun n : ℕ => primeArchEndpointBernsteinPurity n ^ ((n : ℝ)⁻¹))
      atTop (nhds E) := by
  exact tendsto_rpow_inv_natCast_of_exactExponentialExponentAtNatInfinity
    (fun n => bernsteinCoefficientPurity_nonneg _ n) hE

private lemma not_summable_const_div_nat_add_one {c : ℝ} (hc : 0 < c) :
    ¬ Summable (fun n : ℕ => c / (n + 1 : ℝ)) := by
  intro h
  have hscaled : Summable
      (fun n : ℕ => (1 / c) * (c / (n + 1 : ℝ))) := h.mul_left (1 / c)
  have hone : Summable (fun n : ℕ => 1 / (n + 1 : ℝ)) :=
    hscaled.congr fun n => by
      field_simp [hc.ne']
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
  simpa only [Nat.cast_add, Nat.cast_one] using hone

private lemma not_summable_at_reciprocal_boundary
    {f : ℕ → ℝ} {E η : ℝ}
    (hE : 0 < E) (hη : 0 < η)
    (hlower : ∀ᶠ n : ℕ in atTop, η * E ^ n ≤ (n + 1 : ℝ) * f n) :
    ¬ Summable (fun n : ℕ => f n * (1 / E) ^ n) := by
  intro hsum
  have hharm : Summable (fun n : ℕ => η / (n + 1 : ℝ)) := by
    apply Summable.of_norm_bounded_eventually_nat hsum
    filter_upwards [hlower] with n hn
    have hEinvnonneg : 0 ≤ (1 / E) ^ n :=
      pow_nonneg (one_div_nonneg.mpr hE.le) n
    rw [Real.norm_of_nonneg (div_nonneg hη.le (by positivity))]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
    calc
      η ≤ ((n + 1 : ℝ) * f n) / E ^ n := by
        rwa [le_div_iff₀ (pow_pos hE n)]
      _ = (n + 1 : ℝ) * (f n * (1 / E) ^ n) := by
        rw [one_div, inv_pow]
        field_simp [hE.ne']
      _ = (f n * (1 / E) ^ n) * (n + 1 : ℝ) := by ring
  exact not_summable_const_div_nat_add_one hη hharm

/-- The exact Abel radius is a divergence boundary, not only an open transition. -/
theorem not_primeArchEndpointBernsteinAbelSusceptibilityFinite_at_criticalRadius
    {R : ℝ} (hR : PrimeArchEndpointBernsteinAbelCriticalRadius R) :
    ¬ PrimeArchEndpointBernsteinAbelSusceptibilityFinite R := by
  by_cases hRH : RiemannHypothesis
  · have hRone :=
      primeArchEndpointBernsteinAbelCriticalRadius_one_of_riemannHypothesis hRH
    have hReq : R = 1 :=
      primeArchEndpointBernsteinAbelCriticalRadius_unique hR hRone
    rw [hReq]
    simp only [PrimeArchEndpointBernsteinAbelSusceptibilityFinite, one_pow, mul_one]
    intro hsum
    have hharm : Summable
        (fun n : ℕ => normalizedPrimeArchMoment 0 ^ 2 / (n + 1 : ℝ)) := by
      apply Summable.of_norm_bounded hsum
      intro n
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
        (by simpa [mul_comm] using
          mass_sq_le_card_mul_primeArchEndpointBernsteinPurity n)
    exact not_summable_const_div_nat_add_one
      (sq_pos_of_pos normalizedPrimeArchMoment_zero_pos) hharm
  · obtain ⟨B, η, hB, _hBsector, hη, _hattained, _hmax, _hupper,
        hlower, habove, hbelow⟩ :=
      exists_primeArchEndpointBernstein_exactExponentialThreshold_of_not_rh hRH
    have hBpos : 0 < B := lt_trans zero_lt_one hB
    have hE : PrimeArchEndpointBernsteinExactExponentialExponent (B ^ 2) :=
      ⟨sq_pos_of_pos hBpos, habove, hbelow⟩
    have hmul := primeArchEndpointBernsteinAbelRadius_mul_exactExponent_eq_one hR hE
    have hReq : R = 1 / B ^ 2 :=
      (eq_div_iff (sq_pos_of_pos hBpos).ne').2 (by simpa [mul_comm] using hmul)
    rw [hReq]
    exact not_summable_at_reciprocal_boundary
      (E := B ^ 2) (by positivity) hη hlower

/-- On the nonnegative real axis the Abel convergence set is exactly `[0,R)`. -/
theorem primeArchEndpointBernsteinAbelSusceptibilityFinite_iff_lt_criticalRadius
    {R t : ℝ} (hR : PrimeArchEndpointBernsteinAbelCriticalRadius R) (ht : 0 ≤ t) :
    PrimeArchEndpointBernsteinAbelSusceptibilityFinite t ↔ t < R := by
  constructor
  · intro hfinite
    rcases lt_trichotomy t R with hlt | heq | hgt
    · exact hlt
    · subst t
      exact (not_primeArchEndpointBernsteinAbelSusceptibilityFinite_at_criticalRadius hR
        hfinite).elim
    · exact (hR.2.2 t hgt hfinite).elim
  · exact hR.2.1 t ht

end

end RHTower
