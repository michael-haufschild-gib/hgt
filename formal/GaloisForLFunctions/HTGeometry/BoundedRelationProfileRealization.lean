import GaloisForLFunctions.HTGeometry.PrivatePrimeApproximation
import GaloisForLFunctions.HTGeometry.BoundedRelationLogMagnitudeHypertranscendence

/-!
# Arbitrary private-prime profile realization

This leaf completes the constructive surface of the bounded-relation log-magnitude theorem.
Every prescribed positive superlinear real profile has an arbitrarily close positive rational
realization with private denominator primes.  The resulting exponential series is entire,
full-support, and hypertranscendental for every algebraic unit-modulus phase sequence.

The polynomial specialization uses `B * ((n : ℝ) + 1) ^ β`, rather than the paper card's literal
`B * (n : ℝ) ^ β`: the latter vanishes at `n = 0` and therefore does not satisfy the positivity
hypothesis of the arbitrary-profile theorem.
-/

open Filter PowerSeries

namespace GaloisForLFunctions

noncomputable section

/-- A positive rational realization of `g` within `ε`, equipped with strictly increasing private
denominator primes, superlinear growth, and the resulting bounded-relation confinement. -/
def IsPrivatePrimeSuperlinearApproximation
    (g ε : ℕ → ℝ) (b : ℕ → ℚ) (p : ℕ → ℕ) : Prop :=
  (∀ n, (p n).Prime) ∧
    StrictMono p ∧
    (∀ n, 0 < (b n : ℝ)) ∧
    (∀ n, |(b n : ℝ) - g n| < ε n) ∧
    Tendsto (fun n => (b n : ℝ) / (n : ℝ)) atTop atTop ∧
    (∀ n, 1 < padicNorm (p n) (b n)) ∧
    (∀ n m, m ≠ n → padicNorm (p n) (b m) ≤ 1) ∧
    BoundedRelationConfinement (fun n => (b n : ℝ))

/-- Every prescribed positive superlinear real profile has an arbitrarily close positive rational
realization with strictly increasing private denominator primes. -/
theorem exists_privatePrime_superlinear_profile_realization
    (g ε : ℕ → ℝ) (hgpos : ∀ n, 0 < g n) (hε : ∀ n, 0 < ε n)
    (hgrowth : Tendsto (fun n => g n / (n : ℝ)) atTop atTop) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      IsPrivatePrimeSuperlinearApproximation g ε b p := by
  obtain ⟨b, p, hp, hpmono, hbpos, hclose, hself, hother⟩ :=
    exists_privatePrime_rational_approximation g ε hgpos hε
  have hpTop : Tendsto p atTop atTop := hpmono.tendsto_atTop
  have hcloseε : ∀ n, |(b n : ℝ) - g n| < ε n := by
    intro n
    exact (hclose n).trans_le (min_le_left _ _)
  have hcloseOne : ∀ n, |(b n : ℝ) - g n| < 1 := by
    intro n
    exact (hclose n).trans_le (min_le_right _ _)
  have hbgrowth : Tendsto (fun n => (b n : ℝ) / (n : ℝ)) atTop atTop :=
    tendsto_div_natCast_atTop_of_abs_sub_lt_one hgrowth hcloseOne
  have hconf : BoundedRelationConfinement (fun n => (b n : ℝ)) :=
    boundedRelationConfinement_of_privatePrime hp hpTop hself hother
  exact ⟨b, p, hp, hpmono, hbpos, hcloseε, hbgrowth, hself, hother, hconf⟩

/-- Every algebraic unit-phase series built from a private-prime superlinear approximation is
entire, has full Taylor support, and is hypertranscendental. -/
theorem IsPrivatePrimeSuperlinearApproximation.entire_fullSupport_hypertranscendental
    {g ε : ℕ → ℝ} {b : ℕ → ℚ} {p : ℕ → ℕ}
    (h : IsPrivatePrimeSuperlinearApproximation g ε b p)
    {u : ℕ → ℂ} (huAlg : ∀ n, IsAlgebraic ℚ (u n)) (huNorm : ∀ n, ‖u n‖ = 1) :
    ContDiff ℂ (⊤ : ℕ∞)
        (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) ∧
      (∀ n, PowerSeries.coeff n
        (taylorPS (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u)) ≠ 0) ∧
      Hypertranscendental
        (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) := by
  rcases h with ⟨_hp, _hpmono, hbpos, _hclose, hgrowth,
    _hself, _hother, hconf⟩
  have hbAlg : ∀ n, IsAlgebraic ℚ ((b n : ℚ) : ℝ) := by
    intro n
    exact isAlgebraic_rat ℚ (b n)
  exact ⟨contDiff_boundedRelationExponentialFunction hgrowth huNorm,
    taylorPS_boundedRelationExponentialFunction_coeff_ne_zero hgrowth huNorm,
    hypertranscendental_boundedRelationExponentialFunction
      hbpos hgrowth hbAlg hconf huAlg huNorm⟩

/-- Capstone form of arbitrary-profile realization: one private-prime rational approximation works
for every algebraic unit-modulus phase sequence. -/
theorem exists_privatePrime_superlinear_profile_entire_fullSupport_hypertranscendental
    (g ε : ℕ → ℝ) (hgpos : ∀ n, 0 < g n) (hε : ∀ n, 0 < ε n)
    (hgrowth : Tendsto (fun n => g n / (n : ℝ)) atTop atTop) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      IsPrivatePrimeSuperlinearApproximation g ε b p ∧
      ∀ u : ℕ → ℂ,
        (∀ n, IsAlgebraic ℚ (u n)) →
        (∀ n, ‖u n‖ = 1) →
        ContDiff ℂ (⊤ : ℕ∞)
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) ∧
          (∀ n, PowerSeries.coeff n
            (taylorPS (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u)) ≠ 0) ∧
          Hypertranscendental
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) := by
  obtain ⟨b, p, hprofile⟩ :=
    exists_privatePrime_superlinear_profile_realization g ε hgpos hε hgrowth
  refine ⟨b, p, hprofile, ?_⟩
  intro u huAlg huNorm
  exact hprofile.entire_fullSupport_hypertranscendental huAlg huNorm

/-- The everywhere-positive shifted polynomial profile.  The shift is essential at index zero:
`B * (0 : ℝ) ^ β = 0`, whereas the realization theorem requires a positive prescribed profile. -/
def boundedRelationShiftedPolynomialProfile (B β : ℝ) (n : ℕ) : ℝ :=
  B * ((n : ℝ) + 1) ^ β

/-- A shifted polynomial profile with positive scale and exponent above one is superlinear. -/
theorem tendsto_boundedRelationShiftedPolynomialProfile_div_natCast_atTop
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β) :
    Tendsto (fun n => boundedRelationShiftedPolynomialProfile B β n / (n : ℝ))
      atTop atTop := by
  have hlead : Tendsto (fun n : ℕ => B * (n : ℝ) ^ (β - 1)) atTop atTop :=
    ((tendsto_rpow_atTop (sub_pos.mpr hβ)).comp tendsto_natCast_atTop_atTop).const_mul_atTop hB
  refine tendsto_atTop_mono' atTop ?_ hlead
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hbase : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hpow : (n : ℝ) ^ β ≤ ((n : ℝ) + 1) ^ β :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hbase (by linarith)
  rw [boundedRelationShiftedPolynomialProfile, Real.rpow_sub_one hnpos.ne' β]
  calc
    B * ((n : ℝ) ^ β / (n : ℝ)) =
        (B * (n : ℝ) ^ β) / (n : ℝ) := by ring
    _ ≤ (B * ((n : ℝ) + 1) ^ β) / (n : ℝ) :=
      (div_le_div_iff_of_pos_right hnpos).2
        (mul_le_mul_of_nonneg_left hpow hB.le)

/-- Positive shifted polynomial profiles admit exponentially close private-prime rational
realizations whose algebraic unit-phase series are entire, full-support, and hypertranscendental. -/
theorem exists_privatePrime_shiftedPolynomial_profile_entire_fullSupport_hypertranscendental
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      IsPrivatePrimeSuperlinearApproximation
        (boundedRelationShiftedPolynomialProfile B β)
        (fun n => Real.exp (-(n : ℝ))) b p ∧
      ∀ u : ℕ → ℂ,
        (∀ n, IsAlgebraic ℚ (u n)) →
        (∀ n, ‖u n‖ = 1) →
        ContDiff ℂ (⊤ : ℕ∞)
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) ∧
          (∀ n, PowerSeries.coeff n
            (taylorPS (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u)) ≠ 0) ∧
          Hypertranscendental
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) u) := by
  apply exists_privatePrime_superlinear_profile_entire_fullSupport_hypertranscendental
  · intro n
    exact mul_pos hB (Real.rpow_pos_of_pos (by positivity) β)
  · intro n
    exact Real.exp_pos _
  · exact tendsto_boundedRelationShiftedPolynomialProfile_div_natCast_atTop hB hβ

/-- The shifted polynomial specialization has a deterministic all-positive coefficient fiber:
take every algebraic phase equal to one. -/
theorem exists_privatePrime_shiftedPolynomial_positive_entire_fullSupport_hypertranscendental
    {B β : ℝ} (hB : 0 < B) (hβ : 1 < β) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      IsPrivatePrimeSuperlinearApproximation
        (boundedRelationShiftedPolynomialProfile B β)
        (fun n => Real.exp (-(n : ℝ))) b p ∧
      ContDiff ℂ (⊤ : ℕ∞)
          (boundedRelationExponentialFunction (fun n => (b n : ℝ)) (fun _ => 1)) ∧
        (∀ n, PowerSeries.coeff n
          (taylorPS (boundedRelationExponentialFunction
            (fun n => (b n : ℝ)) (fun _ => 1))) ≠ 0) ∧
        Hypertranscendental
          (boundedRelationExponentialFunction (fun n => (b n : ℝ)) (fun _ => 1)) := by
  obtain ⟨b, p, hprofile, hall⟩ :=
    exists_privatePrime_shiftedPolynomial_profile_entire_fullSupport_hypertranscendental hB hβ
  refine ⟨b, p, hprofile, ?_⟩
  exact hall (fun _ => 1) (by intro n; exact isAlgebraic_one) (by intro n; simp)

end

end GaloisForLFunctions
