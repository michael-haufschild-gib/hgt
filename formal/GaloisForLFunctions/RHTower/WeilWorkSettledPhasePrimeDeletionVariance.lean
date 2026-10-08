import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeVariance

/-!
# Finite prime deletion deviations share one variance budget

Distinct prime coprimality masks are orthogonal after centering. The result
controls their joint normalized deviations using the actual source variance.
-/

open Complex Filter Finset
open scoped Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

theorem coprimeDensity_prime {p : ℕ} (hp : p.Prime) :
    coprimeDensity p = 1 - (p : ℝ)⁻¹ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [coprimeDensity_eq_totient_div, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp

theorem coprimeDensity_mul_of_coprime {Q R : ℕ} (hQ : Q ≠ 0) (hR : R ≠ 0)
    (hQR : Q.Coprime R) :
    coprimeDensity (Q * R) = coprimeDensity Q * coprimeDensity R := by
  haveI : NeZero Q := ⟨hQ⟩
  haveI : NeZero R := ⟨hR⟩
  rw [coprimeDensity_eq_totient_div, coprimeDensity_eq_totient_div,
    coprimeDensity_eq_totient_div, Nat.totient_mul hQR, Nat.cast_mul, Nat.cast_mul]
  ring

private theorem coprimeDensity_prime_square {p : ℕ} (hp : p.Prime) :
    coprimeDensity (p * p) = 1 - (p : ℝ)⁻¹ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have ht : (p * p).totient = p * (p - 1) := by
    simpa [pow_two] using Nat.totient_prime_pow_succ hp 1
  rw [coprimeDensity_eq_totient_div, ht, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  field_simp

theorem coprimeDensity_prime_covariance {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    coprimeDensity (p * q) - coprimeDensity p * coprimeDensity q =
      if p = q then ((p : ℝ) - 1) / (p : ℝ) ^ 2 else 0 := by
  by_cases he : p = q
  · subst q
    rw [if_pos rfl, coprimeDensity_prime_square hp, coprimeDensity_prime hp]
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    field_simp
    ring
  · rw [if_neg he, coprimeDensity_mul_of_coprime hp.ne_zero hq.ne_zero
      ((Nat.coprime_primes hp hq).mpr he), sub_self]

theorem coprimeCovariance_primes_diagonal (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (c : ℕ → ℝ) :
    (∑ p ∈ S, ∑ q ∈ S, c p * c q *
      (coprimeDensity (p * q) - coprimeDensity p * coprimeDensity q)) =
      ∑ p ∈ S, c p ^ 2 * (((p : ℝ) - 1) / (p : ℝ) ^ 2) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_eq_single p]
  · rw [coprimeDensity_prime_covariance (hS p hp) (hS p hp), if_pos rfl]
    ring
  · intro q hq hqp
    rw [coprimeDensity_prime_covariance (hS p hp) (hS q hq), if_neg (Ne.symm hqp), mul_zero]
  · exact fun h => (h hp).elim

/-- A simultaneous finite Bessel bound for actual prime deletion endpoints. -/
theorem exists_forward_prime_deletion_variance {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ (V : ℝ) (r : ℕ → ℝ), 0 ≤ V ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N,
        ‖sourceCoeff lam n - sourceCompletion hW 1‖ ^ 2 / n) / Real.log N)
        atTop (𝓝 V) ∧
      (∀ Q : ℕ, Q ≠ 0 → 0 < r Q ∧
        Tendsto (fun s : ℝ => LSeries (coprimePart Q (sourceCoeff lam)) (s : ℂ) /
          LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (r Q : ℂ))) ∧
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        ‖sourceCompletion hW 1‖ ^ 2 *
          (∑ p ∈ S, (p : ℝ) ^ 2 / ((p : ℝ) - 1) *
            (r p - (1 - (p : ℝ)⁻¹)) ^ 2) ≤ V := by
  obtain ⟨V, r, hV0, hV, hr, hcov⟩ := exists_forward_coprime_covariance hW
  refine ⟨V, r, hV0, hV, hr, ?_⟩
  intro S hS
  let w : ℕ → ℝ := fun p => (p : ℝ) ^ 2 / ((p : ℝ) - 1)
  let d : ℕ → ℝ := fun p => r p - (1 - (p : ℝ)⁻¹)
  let T : ℝ := ∑ p ∈ S, w p * d p ^ 2
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun p hp =>
    mul_nonneg (div_nonneg (sq_nonneg _) (by
      have : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
      linarith)) (sq_nonneg _)
  have hb := hcov S (fun p hp => (hS p hp).ne_zero) (fun p => w p * d p)
  rw [coprimeCovariance_primes_diagonal S hS] at hb
  have hlin : (∑ p ∈ S, w p * d p * (r p - coprimeDensity p)) = T := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [coprimeDensity_prime (hS p hp)]
    change w p * d p * d p = w p * d p ^ 2
    ring
  have hquad : (∑ p ∈ S, (w p * d p) ^ 2 * (((p : ℝ) - 1) / (p : ℝ) ^ 2)) = T := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hS p hp).ne_zero
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast (hS p hp).one_lt
      linarith
    dsimp [w]
    field_simp
  rw [hlin, hquad] at hb
  change ‖sourceCompletion hW 1‖ ^ 2 * T ≤ V
  by_cases hT : T = 0
  · simpa only [hT, mul_zero] using hV0
  have hTp : 0 < T := lt_of_le_of_ne hT0 (Ne.symm hT)
  apply (mul_le_mul_iff_of_pos_right hTp).mp
  nlinarith only [hb]

end RHTower.WeilSingularArithmetic
