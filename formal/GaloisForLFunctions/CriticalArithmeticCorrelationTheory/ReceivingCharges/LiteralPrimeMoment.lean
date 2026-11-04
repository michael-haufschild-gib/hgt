import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralPrimeRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralUnitGram

/-!
# Harmonic moments of complete literal prime rows

The exact normalized coefficient retains both signed unit rows and both
own-prime tower corrections. Their square bounds sum over each long interval.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset
open GaloisForLFunctions
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence
  CriticalScaleArithmeticRigidity ArithmeticCouplingTheory

/-- The normalized coefficient retains both periodic unit rows and both own-prime-tower corrections. -/
theorem literal_prime_coefficient_split {P : Finset ℕ} {G : ℕ → ℝ} {M n : ℕ}
    (hM : 0 < M) (hG : Function.Periodic G M) (hp : ∀ p ∈ P, p.Prime)
    (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (hBP : ∀ p ∈ P, linearPrimeStrip c < p) (hn : linearPrimeStrip c ≤ n) (s : ℝ) :
    logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N
      (fun j => G j * incidencePacket P (fun _ => s) j) n =
    (s / (∫ u, φ u ^ 2)) *
      (literalUnitPrimeRow true φ c N P M G n + literalUnitPrimeRow false φ c N P M G n -
        literalTowerRow P (N + linearPrimeStrip c) (linearPrimeStrip c) G (fun k h => k * n + h)
          (fun k h => positiveLiteralUpwardKernel φ c N k h n) -
        literalTowerRow P (N + linearPrimeStrip c) (linearPrimeStrip c) G (fun k h => k * n - h)
          (fun k h => negativeLiteralUpwardKernel φ c N k h n)) := by
  rw [logarithmicUpwardProfileCoefficient_eq_rows,
    positive_literal_prime_row_split hG hp hBP,
    negative_literal_prime_row_split hM hG hp hBP hn]
  change _ = (s / (∫ u, φ u ^ 2)) *
    (unitMangoldtKernelRow P (N + linearPrimeStrip c) (linearPrimeStrip c) M (fun p h => p - h)
      (fun _ k h r => G (k * r + h)) (positiveLiteralUpwardKernel φ c N) n +
    unitMangoldtKernelRow P (N + linearPrimeStrip c) (linearPrimeStrip c) M (fun _ h => h)
      (fun _ k h => negativePeriodicProfile G M k h) (negativeLiteralUpwardKernel φ c N) n -
    literalTowerRow P (N + linearPrimeStrip c) (linearPrimeStrip c) G (fun k h => k * n + h)
      (fun k h => positiveLiteralUpwardKernel φ c N k h n) -
    literalTowerRow P (N + linearPrimeStrip c) (linearPrimeStrip c) G (fun k h => k * n - h)
      (fun k h => negativeLiteralUpwardKernel φ c N k h n))
  ring

/-- Squaring the complete literal row costs two unit-row squares and the explicit tower mass. -/
theorem literal_prime_coefficient_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {P : Finset ℕ} {G : ℕ → ℝ} {M R n : ℕ}
    (hM : 0 < M) (hG : Function.Periodic G M) (hR : 1 ≤ R)
    (hp : ∀ p ∈ P, p.Prime) (hRP : ∀ p ∈ P, R < p)
    (c : ℝ) (N : ℕ) (hBP : ∀ p ∈ P, linearPrimeStrip c < p)
    (hn : 1 ≤ n) (hBn : 2 * linearPrimeStrip c ≤ n)
    (s : ℝ) {V : ℝ} (hV : 0 ≤ V) (hGV : ∀ j, |G j| ≤ V) :
    logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N
      (fun j => G j * incidencePacket P (fun _ => s) j) n ^ 2 ≤
    4 * (s / (∫ u, φ u ^ 2)) ^ 2 *
      (literalUnitPrimeRow true φ c N P M G n ^ 2 + literalUnitPrimeRow false φ c N P M G n ^ 2 +
        2 * ((2 * (linearPrimeStrip c : ℝ) * (2 * ∫ u, φ u ^ 2) * V / R) *
          ∑ p ∈ P, Real.log p / (p : ℝ)) ^ 2) := by
  have hU : 0 ≤ 2 * ∫ u, φ u ^ 2 :=
    mul_nonneg zero_le_two (integral_nonneg fun u => sq_nonneg (φ u))
  have hamp (k : ℕ) (hk : k ∈ Icc 1 (N + linearPrimeStrip c))
      (h : ℕ) (hh : h ∈ Icc 1 (linearPrimeStrip c)) :
      |positiveLiteralUpwardKernel φ c N k h n| ≤ 2 * ∫ u, φ u ^ 2 ∧
        |negativeLiteralUpwardKernel φ c N k h n| ≤ 2 * ∫ u, φ u ^ 2 := by
    have hnkn : n ≤ k * n := by
      simpa only [one_mul] using Nat.mul_le_mul_right n (mem_Icc.mp hk).1
    exact abs_literalUpwardKernels_le hφ hsupp c N (mem_Icc.mp hk).1 hn
      ((Nat.mul_le_mul_left 2 (mem_Icc.mp hh).2).trans (hBn.trans hnkn))
  have hplus := abs_literalTowerRow_le hR hp hRP G (fun k h => k * n + h)
    (fun k h => positiveLiteralUpwardKernel φ c N k h n) hU hV hGV
    (fun k hk h hh => (hamp k hk h hh).1)
  have hminus := abs_literalTowerRow_le hR hp hRP G (fun k h => k * n - h)
    (fun k h => negativeLiteralUpwardKernel φ c N k h n) hU hV hGV
    (fun k hk h hh => (hamp k hk h hh).2)
  have hplus2 := pow_le_pow_left₀ (abs_nonneg _) hplus 2
  have hminus2 := pow_le_pow_left₀ (abs_nonneg _) hminus 2
  rw [sq_abs] at hplus2 hminus2
  have hfour (a b d e T : ℝ) (hd : d ^ 2 ≤ T ^ 2) (he : e ^ 2 ≤ T ^ 2) :
      (a + b - d - e) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + 2 * T ^ 2) := by
    nlinarith only [hd, he, sq_nonneg (a - b), sq_nonneg (a + d), sq_nonneg (a + e),
      sq_nonneg (b + d), sq_nonneg (b + e), sq_nonneg (d - e)]
  rw [literal_prime_coefficient_split hM hG hp φ c N hBP (by omega) s, mul_pow]
  exact (mul_le_mul_of_nonneg_left (hfour _ _ _ _ _ hplus2 hminus2)
    (sq_nonneg (s / (∫ u, φ u ^ 2)))).trans_eq (by ring)

#print axioms literal_prime_coefficient_split
#print axioms literal_prime_coefficient_sq_le

/-- Summing the exact long-row split preserves both signed unit Gram moments and the tower charge. -/
theorem literal_prime_long_moment_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {P : Finset ℕ} {G : ℕ → ℝ} {M R A Z : ℕ}
    (hM : 0 < M) (hG : Function.Periodic G M) (hR : 1 ≤ R)
    (hp : ∀ p ∈ P, p.Prime) (hRP : ∀ p ∈ P, R < p)
    (c : ℝ) (N : ℕ) (hBP : ∀ p ∈ P, linearPrimeStrip c < p)
    (hA : 1 ≤ A) (hBA : 2 * linearPrimeStrip c ≤ A)
    (s : ℝ) {V : ℝ} (hV : 0 ≤ V) (hGV : ∀ j, |G j| ≤ V) :
    (∑ n ∈ Icc A Z, logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N
      (fun j => G j * incidencePacket P (fun _ => s) j) n ^ 2 / (n : ℝ)) ≤
    4 * (s / (∫ u, φ u ^ 2)) ^ 2 *
      ((∑ n ∈ Icc A Z, literalUnitPrimeRow true φ c N P M G n ^ 2 / (n : ℝ)) +
        (∑ n ∈ Icc A Z, literalUnitPrimeRow false φ c N P M G n ^ 2 / (n : ℝ)) +
        2 * ((2 * (linearPrimeStrip c : ℝ) * (2 * ∫ u, φ u ^ 2) * V / R) *
          ∑ p ∈ P, Real.log p / (p : ℝ)) ^ 2 * (∑ n ∈ Icc A Z, 1 / (n : ℝ))) := by
  have hsum := sum_le_sum (s := Icc A Z) fun n hn =>
    div_le_div_of_nonneg_right
      (literal_prime_coefficient_sq_le hφ hsupp hM hG hR hp hRP c N hBP
        (hA.trans (mem_Icc.mp hn).1) (hBA.trans (mem_Icc.mp hn).1) s hV hGV)
      (Nat.cast_nonneg n)
  refine hsum.trans_eq ?_
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  ring

#print axioms literal_prime_long_moment_le

/-- Actual long-row moments combine prime covariance and own-prime towers, for both receiving ranges. -/
theorem exists_literal_prime_long_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) :
    ∃ p₀ : ℕ, ∃ K : ℝ, 8 ≤ p₀ ∧ 0 ≤ K ∧
      ∀ (c : ℝ), 0 < c → ∀ (N M R A Z : ℕ), p₀ ≤ R → linearPrimeStrip c ≤ R →
      1 ≤ A → A ≤ Z → Z ≤ N → 0 < M →
      c / N ≤ 1 → linearPrimeStrip c ≤ N → 2 * linearPrimeStrip c ≤ A →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, R < p) → (∀ p ∈ P, M.Coprime p) →
      ∀ (G : ℕ → ℝ) (s V : ℝ), Function.Periodic G M → 0 ≤ V → (∀ j, |G j| ≤ V) →
      ((∀ p ∈ P, p ^ 2 ≤ literalMultiplierLower c N Z) →
        (∑ n ∈ Icc A Z, logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N
          (fun j => G j * incidencePacket P (fun _ => s) j) n ^ 2 / (n : ℝ)) ≤
        8 * (s / (∫ u, φ u ^ 2)) ^ 2 *
          (literalMiddleGramBound φ c N P M A Z V K +
            ((2 * (linearPrimeStrip c : ℝ) * (2 * ∫ u, φ u ^ 2) * V / R) *
              ∑ p ∈ P, Real.log p / (p : ℝ)) ^ 2 * (∑ n ∈ Icc A Z, 1 / (n : ℝ)))) ∧
      ((∑ n ∈ Icc A Z, logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N
          (fun j => G j * incidencePacket P (fun _ => s) j) n ^ 2 / (n : ℝ)) ≤
        8 * (s / (∫ u, φ u ^ 2)) ^ 2 *
          (literalTerminalGramBound φ c N P M A Z V K +
            ((2 * (linearPrimeStrip c : ℝ) * (2 * ∫ u, φ u ^ 2) * V / R) *
              ∑ p ∈ P, Real.log p / (p : ℝ)) ^ 2 * (∑ n ∈ Icc A Z, 1 / (n : ℝ)))) := by
  obtain ⟨p₀, K, hp₀, hK, hGram⟩ := exists_literal_unit_prime_Gram_bounds hφ hsupp hφ0
  refine ⟨p₀, K, hp₀, hK, ?_⟩
  intro c hc N M R A Z hpR hBR hA hAZ hZN hM hwidth hB hBA P hp hRP hMp G s V hG hV hGV
  have hR : 1 ≤ R := by omega
  have hBP : ∀ p ∈ P, linearPrimeStrip c < p := fun p hp => hBR.trans_lt (hRP p hp)
  have hpp : ∀ p ∈ P, p₀ ≤ p := fun p hp => hpR.trans (hRP p hp).le
  have hg := hGram c hc N M A Z hA hAZ hZN hM hwidth hB hBA P hp hpp hMp hBP G V hV hGV
  have hl := literal_prime_long_moment_le hφ hsupp hM hG hR hp hRP c N hBP hA hBA s hV hGV
  have hclose (C : ℝ)
      (hplus : (∑ n ∈ Icc A Z, literalUnitPrimeRow true φ c N P M G n ^ 2 / (n : ℝ)) ≤ C)
      (hminus : (∑ n ∈ Icc A Z, literalUnitPrimeRow false φ c N P M G n ^ 2 / (n : ℝ)) ≤ C) :
      (∑ n ∈ Icc A Z, logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N
        (fun j => G j * incidencePacket P (fun _ => s) j) n ^ 2 / (n : ℝ)) ≤
        8 * (s / (∫ u, φ u ^ 2)) ^ 2 *
          (C + ((2 * (linearPrimeStrip c : ℝ) * (2 * ∫ u, φ u ^ 2) * V / R) *
            ∑ p ∈ P, Real.log p / (p : ℝ)) ^ 2 * (∑ n ∈ Icc A Z, 1 / (n : ℝ))) := by
    refine hl.trans ((mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hplus hminus) (le_refl _)) (by positivity)).trans_eq ?_)
    ring
  exact ⟨fun hpH => hclose _ (hg.1 hpH true) (hg.1 hpH false),
    hclose _ (hg.2 true) (hg.2 false)⟩

#print axioms exists_literal_prime_long_bounds

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
