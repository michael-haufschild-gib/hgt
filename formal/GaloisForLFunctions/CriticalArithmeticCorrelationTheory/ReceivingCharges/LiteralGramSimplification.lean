import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralThreeRange
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.HarmonicPrimeTails

/-!
# Separated costs in the literal three-range bound

Reciprocal-square source tails and terminal harmonic width separate the
finite bound into short rows, prime tails, own towers and covariance.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- A subinterval of the horizon has harmonic mass at most twice its logarithm. -/
theorem harmonic_subinterval_le_two_log {A Z N : ℕ}
    (hA : 1 ≤ A) (hZN : Z ≤ N) (hlog : 1 ≤ Real.log N) :
    (∑ n ∈ Icc A Z, 1 / (n : ℝ)) ≤ 2 * Real.log N := by
  have hsub : Icc A Z ⊆ Icc 1 N := fun n hn =>
    mem_Icc.mpr ⟨hA.trans (mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hZN⟩
  have h := (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)).trans
    (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N)
  linarith only [h, hlog]

/-- The middle prime mass separates into the reciprocal-square tail and the proper-power tail. -/
theorem literal_middle_prime_mass_le {c : ℝ} {N n Q R : ℕ} {P : Finset ℕ}
    (hR : 1 ≤ R) (hQ : 1 ≤ Q) (hRP : ∀ p ∈ P, R < p)
    (hH : Q ^ 2 ≤ literalMultiplierLower c N n) :
    (∑ p ∈ P, (1027 * literalMultiplierWidth c ^ 2 / (p : ℝ) ^ 2 +
      576 * literalMultiplierWidth c * (literalMultiplierLower c N n : ℝ) ^ (-(7 / 16 : ℝ)) / p)) ≤
      1027 * literalMultiplierWidth c ^ 2 / R +
        576 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ)) *
          (Q : ℝ) ^ (-(7 / 8 : ℝ)) := by
  have htail := literalMultiplierLower_proper_power_tail hQ hH
  have hsum := finite_reciprocal_square_tail_le hR hRP
  have hS : 0 ≤ ∑ p ∈ P, 1 / (p : ℝ) := sum_nonneg fun p _ => by positivity
  have hW := literalMultiplierWidth_nonneg c
  calc
    _ = 1027 * literalMultiplierWidth c ^ 2 * (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
        576 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ)) *
          (literalMultiplierLower c N n : ℝ) ^ (-(7 / 16 : ℝ)) := by
      rw [mul_sum, mul_sum, sum_mul, ← sum_add_distrib]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ _ := add_le_add
      ((mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring))
      (mul_le_mul_of_nonneg_left htail (by positivity))

/-- All middle rows share a single source bound, with no loss from their number. -/
theorem literal_middle_harmonic_mass_le {c : ℝ} (hc : 0 < c)
    {N A Z Q R : ℕ} {P : Finset ℕ} (hA : 1 ≤ A) (hZN : Z ≤ N)
    (hlog : 1 ≤ Real.log N) (hR : 1 ≤ R) (hQ : 1 ≤ Q)
    (hRP : ∀ p ∈ P, R < p) (hH : Q ^ 2 ≤ literalMultiplierLower c N Z) :
    (∑ n ∈ Icc A Z, (∑ p ∈ P,
      (1027 * literalMultiplierWidth c ^ 2 / (p : ℝ) ^ 2 +
        576 * literalMultiplierWidth c * (literalMultiplierLower c N n : ℝ) ^ (-(7 / 16 : ℝ)) / p)) /
          (n : ℝ)) ≤
      (1027 * literalMultiplierWidth c ^ 2 / R +
        576 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ)) *
          (Q : ℝ) ^ (-(7 / 8 : ℝ))) * (2 * Real.log N) := by
  let C := 1027 * literalMultiplierWidth c ^ 2 / R +
    576 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ)) * (Q : ℝ) ^ (-(7 / 8 : ℝ))
  have hW := literalMultiplierWidth_nonneg c
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  calc
    _ ≤ C * ∑ n ∈ Icc A Z, 1 / (n : ℝ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      have hHn := hH.trans (literalMultiplierLower_antitone hc
        (hA.trans (mem_Icc.mp hn).1) (mem_Icc.mp hn).2)
      exact (div_le_div_of_nonneg_right
        (literal_middle_prime_mass_le hR hQ hRP hHn) (Nat.cast_nonneg n)).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_subinterval_le_two_log hA hZN hlog) hC

/-- A terminal prime block costs at most twice the reciprocal-prime mass. -/
theorem terminal_prime_mass_le {P : Finset ℕ} (hp : ∀ p ∈ P, 1 ≤ p) :
    (∑ p ∈ P, (1 / (p : ℝ) ^ 2 + 1 / (p : ℝ))) ≤
      2 * ∑ p ∈ P, 1 / (p : ℝ) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hpP
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp p hpP
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp1
  have hsq : (p : ℝ) ≤ (p : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hp1) hp0.le]
  have h := one_div_le_one_div_of_le hp0 hsq
  linarith only [h]

/-- Terminal rows pay only their exact logarithmic width. -/
theorem literal_terminal_harmonic_mass_le {J N : ℕ} {D : ℝ} {P : Finset ℕ}
    (hJ : 1 ≤ J) (hJN : J ≤ N) (hDJ : (N : ℝ) ≤ D * J)
    (hp : ∀ p ∈ P, 1 ≤ p) :
    (∑ n ∈ Icc (J + 1) N, (∑ p ∈ P, (1 / (p : ℝ) ^ 2 + 1 / (p : ℝ))) / (n : ℝ)) ≤
      2 * (∑ p ∈ P, 1 / (p : ℝ)) * Real.log D := by
  have hS : 0 ≤ ∑ p ∈ P, 1 / (p : ℝ) := sum_nonneg fun p _ => by positivity
  calc
    _ ≤ (2 * ∑ p ∈ P, 1 / (p : ℝ)) * ∑ n ∈ Icc (J + 1) N, 1 / (n : ℝ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro n _
      exact (div_le_div_of_nonneg_right (terminal_prime_mass_le hp)
        (Nat.cast_nonneg n)).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left (terminal_harmonic_mass_le hJ hJN hDJ) (by positivity)

/-- Later interval starts decrease the full covariance remainder. -/
theorem literalGramError_antitone_start (φ : ℝ → ℝ) (c : ℝ) (N M : ℕ)
    (P : Finset ℕ) (V K : ℝ) (hK : 0 ≤ K) {A T : ℕ} (hA : 1 ≤ A) (hAT : A ≤ T) :
    literalGramError φ c N P M T V K ≤ literalGramError φ c N P M A V K := by
  have hmass : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  unfold literalGramError
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact div_le_div_of_nonneg_left (by positivity) hA0 (by exact_mod_cast hAT)

#print axioms literal_middle_harmonic_mass_le
#print axioms literal_terminal_harmonic_mass_le
#print axioms literalGramError_antitone_start

/-- The explicit three-range bound separates into short rows, two prime tails, own towers and covariance. -/
theorem literalThreeRangeBound_le {φ : ℝ → ℝ} (hmass : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N M R A J Q : ℕ} {P : Finset ℕ} {s V K D : ℝ}
    (hK : 0 ≤ K) (hA : 1 ≤ A) (hAJ : A ≤ J) (hJN : J ≤ N)
    (hlog : 1 ≤ Real.log N) (hR : 1 ≤ R) (hQ : 1 ≤ Q)
    (hRP : ∀ p ∈ P, R < p) (hH : Q ^ 2 ≤ literalMultiplierLower c N J)
    (hDJ : (N : ℝ) ≤ D * J) :
    literalThreeRangeBound φ c N M R A J P s V K ≤
      literalShortRowBound c N A P s V ^ 2 * (1 + Real.log A) / Real.log N +
      64 * (linearPrimeStrip c : ℝ) ^ 2 * s ^ 2 * V ^ 2 *
        (1027 * literalMultiplierWidth c ^ 2 / R +
          576 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ)) * (Q : ℝ) ^ (-(7 / 8 : ℝ))) +
      64 * (linearPrimeStrip c : ℝ) ^ 2 * s ^ 2 * V ^ 2 * literalMultiplierWidth c ^ 2 *
        (∑ p ∈ P, 1 / (p : ℝ)) * Real.log D / Real.log N +
      256 * (linearPrimeStrip c : ℝ) ^ 2 * V ^ 2 *
        (s * ∑ p ∈ P, Real.log p / (p : ℝ)) ^ 2 / (R : ℝ) ^ 2 +
      16 * (s / (∫ u, φ u ^ 2)) ^ 2 * literalGramError φ c N P M A V K / Real.log N := by
  let B : ℝ := linearPrimeStrip c
  let m : ℝ := ∫ u, φ u ^ 2
  let L : ℝ := Real.log N
  let W : ℝ := literalMultiplierWidth c
  let S : ℝ := ∑ p ∈ P, 1 / (p : ℝ)
  let C : ℝ := 1027 * W ^ 2 / R + 576 * W * S * (Q : ℝ) ^ (-(7 / 8 : ℝ))
  let E : ℝ := literalGramError φ c N P M A V K
  let T : ℝ := literalPrimeTowerBound φ c R P V
  let H₁ : ℝ := ∑ n ∈ Icc A J, 1 / (n : ℝ)
  let H₂ : ℝ := ∑ n ∈ Icc (J + 1) N, 1 / (n : ℝ)
  let X : ℝ := literalShortRowBound c N A P s V ^ 2 * (1 + Real.log A)
  have hL : 0 < L := zero_lt_one.trans_le hlog
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hmid : literalMiddleGramBound φ c N P M A J V K ≤
      B ^ 2 * (2 * m) ^ 2 * V ^ 2 * (C * (2 * L)) + E := by
    exact add_le_add (mul_le_mul_of_nonneg_left
      (literal_middle_harmonic_mass_le hc hA hJN hlog hR hQ hRP hH) (by positivity)) le_rfl
  have hterm : literalTerminalGramBound φ c N P M (J + 1) N V K ≤
      B ^ 2 * (2 * m) ^ 2 * V ^ 2 * W ^ 2 * (2 * S * Real.log D) + E := by
    exact add_le_add (mul_le_mul_of_nonneg_left
      (literal_terminal_harmonic_mass_le (hA.trans hAJ) hJN hDJ
        (fun p hp => hR.trans (hRP p hp).le)) (by positivity))
      (literalGramError_antitone_start φ c N M P V K hK hA (hAJ.trans (Nat.le_succ J)))
  have hHsum : H₁ + H₂ ≤ 2 * L := by
    have he := sum_Ioc_consecutive (fun n => 1 / (n : ℝ))
      ((Nat.sub_le A 1).trans hAJ) hJN
    simp only [← Icc_add_one_left_eq_Ioc, Nat.sub_add_cancel hA] at he
    exact he.trans_le (harmonic_subinterval_le_two_log hA le_rfl hlog)
  have hsplit : literalThreeRangeBound φ c N M R A J P s V K =
      X / L + (8 * (s / m) ^ 2 / L) *
        (literalMiddleGramBound φ c N P M A J V K +
          literalTerminalGramBound φ c N P M (J + 1) N V K + T ^ 2 * (H₁ + H₂)) := by
    dsimp only [literalThreeRangeBound, X, L, m, T, H₁, H₂]
    ring
  rw [hsplit]
  calc
    _ ≤ X / L + (8 * (s / m) ^ 2 / L) *
        ((B ^ 2 * (2 * m) ^ 2 * V ^ 2 * (C * (2 * L)) + E) +
          (B ^ 2 * (2 * m) ^ 2 * V ^ 2 * W ^ 2 * (2 * S * Real.log D) + E) +
          T ^ 2 * (2 * L)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hmid hterm) (mul_le_mul_of_nonneg_left hHsum (sq_nonneg T)))
        (by positivity))
    _ = _ := by
      dsimp only [B, m, L, W, S, C, E, T, X, literalPrimeTowerBound]
      field_simp [hmass.ne', hL.ne', hR0.ne']
      ring

#print axioms literalThreeRangeBound_le

/-- The short-row square splits into reciprocal-prime mass and the complete proper-power remainder. -/
theorem literalShortRowBound_sq_le (c : ℝ) (N A : ℕ) (P : Finset ℕ) (s V : ℝ) :
    literalShortRowBound c N A P s V ^ 2 ≤
      32 * (linearPrimeStrip c : ℝ) ^ 2 * s ^ 2 * V ^ 2 *
        (1027 ^ 2 * literalMultiplierWidth c ^ 2 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 +
          576 ^ 2 * (P.card : ℝ) ^ 2 *
            (literalMultiplierLower c N A : ℝ) ^ (-(7 / 8 : ℝ))) := by
  let x : ℝ := 1027 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ))
  let y : ℝ := 576 * (P.card : ℝ) *
    (literalMultiplierLower c N A : ℝ) ^ (-(7 / 16 : ℝ))
  have hxy : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    nlinarith only [sq_nonneg (x - y)]
  have hpower : ((literalMultiplierLower c N A : ℝ) ^ (-(7 / 16 : ℝ))) ^ (2 : ℕ) =
      (literalMultiplierLower c N A : ℝ) ^ (-(7 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  calc
    _ = (4 * (linearPrimeStrip c : ℝ) * |s| * V) ^ 2 * (x + y) ^ 2 := by
      rw [literalShortRowBound, mul_pow]
    _ ≤ (4 * (linearPrimeStrip c : ℝ) * |s| * V) ^ 2 * (2 * (x ^ 2 + y ^ 2)) :=
      mul_le_mul_of_nonneg_left hxy (sq_nonneg _)
    _ = _ := by
      dsimp only [x, y]
      simp only [mul_pow, sq_abs, hpower]
      ring

#print axioms literalShortRowBound_sq_le

/-- All five costs in the finite three-range estimate are explicit scalar quantities. -/
theorem literalThreeRangeBound_explicit_le {φ : ℝ → ℝ} (hmass : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {N M R A J Q : ℕ} {P : Finset ℕ} {s V K D : ℝ}
    (hK : 0 ≤ K) (hA : 1 ≤ A) (hAJ : A ≤ J) (hJN : J ≤ N)
    (hlog : 1 ≤ Real.log N) (hR : 1 ≤ R) (hQ : 1 ≤ Q)
    (hRP : ∀ p ∈ P, R < p) (hH : Q ^ 2 ≤ literalMultiplierLower c N J)
    (hDJ : (N : ℝ) ≤ D * J) :
    literalThreeRangeBound φ c N M R A J P s V K ≤
      (32 * (linearPrimeStrip c : ℝ) ^ 2 * s ^ 2 * V ^ 2 *
        (1027 ^ 2 * literalMultiplierWidth c ^ 2 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 +
          576 ^ 2 * (P.card : ℝ) ^ 2 *
            (literalMultiplierLower c N A : ℝ) ^ (-(7 / 8 : ℝ)))) *
        (1 + Real.log A) / Real.log N +
      64 * (linearPrimeStrip c : ℝ) ^ 2 * s ^ 2 * V ^ 2 *
        (1027 * literalMultiplierWidth c ^ 2 / R +
          576 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ)) * (Q : ℝ) ^ (-(7 / 8 : ℝ))) +
      64 * (linearPrimeStrip c : ℝ) ^ 2 * s ^ 2 * V ^ 2 * literalMultiplierWidth c ^ 2 *
        (∑ p ∈ P, 1 / (p : ℝ)) * Real.log D / Real.log N +
      256 * (linearPrimeStrip c : ℝ) ^ 2 * V ^ 2 *
        (s * ∑ p ∈ P, Real.log p / (p : ℝ)) ^ 2 / (R : ℝ) ^ 2 +
      (64 * (M : ℝ) * V ^ 2 *
        (2 * (2 * ∫ u, φ u ^ 2) ^ 2 + 2 * (2 * ∫ u, φ u ^ 2) * K) /
          (∫ u, φ u ^ 2) ^ 2) *
        (s ^ 2 * (P.card : ℝ) ^ 2 * (linearPrimeStrip c : ℝ) ^ 2 *
          (Real.log (N + linearPrimeStrip c : ℕ) + mertensWindowConstant + 1) ^ 2) /
            ((A : ℝ) * Real.log N) := by
  have hL : 0 < Real.log N := zero_lt_one.trans_le hlog
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hcov :
      16 * (s / (∫ u, φ u ^ 2)) ^ 2 * literalGramError φ c N P M A V K / Real.log N =
      (64 * (M : ℝ) * V ^ 2 *
        (2 * (2 * ∫ u, φ u ^ 2) ^ 2 + 2 * (2 * ∫ u, φ u ^ 2) * K) /
          (∫ u, φ u ^ 2) ^ 2) *
        (s ^ 2 * (P.card : ℝ) ^ 2 * (linearPrimeStrip c : ℝ) ^ 2 *
          (Real.log (N + linearPrimeStrip c : ℕ) + mertensWindowConstant + 1) ^ 2) /
            ((A : ℝ) * Real.log N) := by
    unfold literalGramError
    field_simp [hmass.ne', hA0.ne', hL.ne']
    ring
  rw [← hcov]
  have hs := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (literalShortRowBound_sq_le c N A P s V)
      (add_nonneg zero_le_one (Real.log_natCast_nonneg A))) hL.le
  exact (literalThreeRangeBound_le hmass hc hK hA hAJ hJN hlog hR hQ hRP hH hDJ).trans
    (add_le_add (add_le_add (add_le_add (add_le_add hs le_rfl) le_rfl) le_rfl) le_rfl)

#print axioms literalThreeRangeBound_explicit_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
