import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.MangoldtKernelGram
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralMultiplierGeometry
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PeriodicProfiles
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.AffineIncidences

/-!
# Covariance bounds for the actual signed unit kernels

The literal kernels satisfy the amplitude, support and variation inputs
of the finite prime Gram estimate for both receiving ranges.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open GaloisForLFunctions.BezoutValuationIncidence

/-- The sign selects one of the two original finite offset kernels. -/
def signedLiteralKernel (positive : Bool) (φ : ℝ → ℝ) (c : ℝ) (N k h n : ℕ) : ℝ :=
  if positive then positiveLiteralUpwardKernel φ c N k h n else negativeLiteralUpwardKernel φ c N k h n

def signedLiteralTarget (positive : Bool) (p h : ℕ) : ℕ :=
  if positive then p - h else h

def signedLiteralSample (positive : Bool) (G : ℕ → ℝ) (M k h r : ℕ) : ℝ :=
  if positive then G (k * r + h) else negativePeriodicProfile G M k h r

/-- The literal prime-band unit row for either offset sign. -/
def literalUnitPrimeRow (positive : Bool) (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (P : Finset ℕ) (M : ℕ) (G : ℕ → ℝ) (n : ℕ) : ℝ :=
  unitMangoldtKernelRow P (N + linearPrimeStrip c) (linearPrimeStrip c) M
    (signedLiteralTarget positive) (fun _ => signedLiteralSample positive G M)
    (signedLiteralKernel positive φ c N) n

/-- The exact finite covariance error for the actual literal kernels. -/
def literalGramError (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (P : Finset ℕ)
    (M A : ℕ) (V K : ℝ) : ℝ :=
  (4 * (M : ℝ) * V ^ 2 *
    (2 * (2 * ∫ u, φ u ^ 2) ^ 2 + 2 * (2 * ∫ u, φ u ^ 2) * K) / A) *
      ((P.card : ℝ) * linearPrimeStrip c *
        (Real.log (N + linearPrimeStrip c : ℕ) + mertensWindowConstant + 1)) ^ 2

def literalMiddleGramBound (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (P : Finset ℕ)
    (M A Z : ℕ) (V K : ℝ) : ℝ :=
  (linearPrimeStrip c : ℝ) ^ 2 * (2 * ∫ u, φ u ^ 2) ^ 2 * V ^ 2 *
    (∑ n ∈ Icc A Z, (∑ p ∈ P,
      (1027 * literalMultiplierWidth c ^ 2 / (p : ℝ) ^ 2 +
        576 * literalMultiplierWidth c * (literalMultiplierLower c N n : ℝ) ^ (-(7 / 16 : ℝ)) / p)) /
          (n : ℝ)) + literalGramError φ c N P M A V K

def literalTerminalGramBound (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (P : Finset ℕ)
    (M A Z : ℕ) (V K : ℝ) : ℝ :=
  (linearPrimeStrip c : ℝ) ^ 2 * (2 * ∫ u, φ u ^ 2) ^ 2 * V ^ 2 * literalMultiplierWidth c ^ 2 *
    (∑ n ∈ Icc A Z, (∑ p ∈ P, (1 / (p : ℝ) ^ 2 + 1 / (p : ℝ))) / (n : ℝ)) +
      literalGramError φ c N P M A V K

/-- Both actual signs satisfy the middle and terminal Gram bounds with no extra kernel hypothesis. -/
theorem exists_literal_unit_prime_Gram_bounds {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) :
    ∃ p₀ : ℕ, ∃ K : ℝ, 8 ≤ p₀ ∧ 0 ≤ K ∧
      ∀ (c : ℝ), 0 < c → ∀ (N M A Z : ℕ), 1 ≤ A → A ≤ Z → Z ≤ N → 0 < M →
      c / N ≤ 1 → linearPrimeStrip c ≤ N → 2 * linearPrimeStrip c ≤ A →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p₀ ≤ p) →
      (∀ p ∈ P, M.Coprime p) → (∀ p ∈ P, linearPrimeStrip c < p) →
      ∀ (G : ℕ → ℝ) (V : ℝ), 0 ≤ V → (∀ j, |G j| ≤ V) →
      ((∀ p ∈ P, p ^ 2 ≤ literalMultiplierLower c N Z) → ∀ positive : Bool,
        (∑ n ∈ Icc A Z, literalUnitPrimeRow positive φ c N P M G n ^ 2 / (n : ℝ)) ≤
          literalMiddleGramBound φ c N P M A Z V K) ∧
      (∀ positive : Bool,
        (∑ n ∈ Icc A Z, literalUnitPrimeRow positive φ c N P M G n ^ 2 / (n : ℝ)) ≤
          literalTerminalGramBound φ c N P M A Z V K) := by
  obtain ⟨p₀, hp₀, hmiddle⟩ := exists_unit_mangoldt_kernel_Gram_le
  obtain ⟨K, hK, hvariation⟩ := exists_literalUpwardKernels_variation hφ hsupp
  refine ⟨p₀, K, hp₀, hK, ?_⟩
  intro c hc N M A Z hA hAZ hZN hM hwidth hB hBA P hp hpp hMp hBP G V hV hG
  have hN : 1 ≤ N := (hA.trans hAZ).trans hZN
  have hU : 0 ≤ 2 * ∫ u, φ u ^ 2 :=
    mul_nonneg zero_le_two (integral_nonneg fun u => sq_nonneg (φ u))
  have hW := literalMultiplierWidth_nonneg c
  have htarget (positive : Bool) (p : ℕ) (hpP : p ∈ P) (h : ℕ)
      (hh : h ∈ Icc 1 (linearPrimeStrip c)) : p.Coprime (signedLiteralTarget positive p h) := by
    have hhp := (mem_Icc.mp hh).2.trans_lt (hBP p hpP)
    cases positive
    · exact prime_negative_offset_unit (hp p hpP) (mem_Icc.mp hh).1 hhp
    · exact prime_positive_offset_unit (hp p hpP) (mem_Icc.mp hh).1 hhp
  have hsample (positive : Bool) (p : ℕ) (_hp : p ∈ P) (k : ℕ)
      (_hk : k ∈ Icc 1 (N + linearPrimeStrip c)) (h : ℕ)
      (_hh : h ∈ Icc 1 (linearPrimeStrip c)) (r : ℕ) (_hr : r ∈ range M) :
      |signedLiteralSample positive G M k h r| ≤ V := by
    cases positive <;> exact hG _
  have hnonneg (positive : Bool) (k : ℕ) (_hk : k ∈ Icc 1 (N + linearPrimeStrip c))
      (h : ℕ) (_hh : h ∈ Icc 1 (linearPrimeStrip c)) (n : ℕ) (_hn : n ∈ Icc A Z) :
      0 ≤ signedLiteralKernel positive φ c N k h n := by
    cases positive
    · exact (literalUpwardKernels_nonneg hφ0 c N k h n).2
    · exact (literalUpwardKernels_nonneg hφ0 c N k h n).1
  have hamp (positive : Bool) (k : ℕ) (hk : k ∈ Icc 1 (N + linearPrimeStrip c))
      (h : ℕ) (hh : h ∈ Icc 1 (linearPrimeStrip c)) (n : ℕ) (hn : n ∈ Icc A Z) :
      |signedLiteralKernel positive φ c N k h n| ≤ 2 * ∫ u, φ u ^ 2 := by
    have hn1 : 1 ≤ n := hA.trans (mem_Icc.mp hn).1
    have hnkn : n ≤ k * n := by
      simpa only [one_mul] using Nat.mul_le_mul_right n (mem_Icc.mp hk).1
    have haway : 2 * h ≤ k * n :=
      (Nat.mul_le_mul_left 2 (mem_Icc.mp hh).2).trans (hBA.trans ((mem_Icc.mp hn).1.trans hnkn))
    cases positive
    · exact (abs_literalUpwardKernels_le hφ hsupp c N (mem_Icc.mp hk).1 hn1 haway).2
    · exact (abs_literalUpwardKernels_le hφ hsupp c N (mem_Icc.mp hk).1 hn1 haway).1
  have hvar (positive : Bool) (k : ℕ) (hk : k ∈ Icc 1 (N + linearPrimeStrip c))
      (h : ℕ) (hh : h ∈ Icc 1 (linearPrimeStrip c)) :
      discreteVariation (signedLiteralKernel positive φ c N k h) A Z ≤ K := by
    have haway := (Nat.mul_le_mul_left 2 (mem_Icc.mp hh).2).trans hBA
    have hv := hvariation (N := N) hc hA hAZ (mem_Icc.mp hk).1 haway
    cases positive
    · exact hv.2
    · exact hv.1
  have hH (n : ℕ) (hn : n ∈ Icc A Z) : 1 ≤ literalMultiplierLower c N n :=
    literalMultiplierLower_pos hc hN (hA.trans (mem_Icc.mp hn).1)
  have hs (positive : Bool) (k : ℕ) (hk : k ∈ Icc 1 (N + linearPrimeStrip c))
      (h : ℕ) (hh : h ∈ Icc 1 (linearPrimeStrip c)) (n : ℕ) (hn : n ∈ Icc A Z) :
      signedLiteralKernel positive φ c N k h n ≠ 0 →
        k ∈ Icc (literalMultiplierLower c N n) (literalMultiplierUpper c N n) := by
    cases positive
    · exact negativeLiteralUpwardKernel_support hφ hsupp hc hN (mem_Icc.mp hk).1
        (mem_Icc.mp hh).1 (hA.trans (mem_Icc.mp hn).1) hwidth
    · exact positiveLiteralUpwardKernel_support hφ hsupp hc hN (mem_Icc.mp hk).1
        (mem_Icc.mp hh).1 (hA.trans (mem_Icc.mp hn).1) hwidth
  have hw (n : ℕ) (hn : n ∈ Icc A Z) :
      literalMultiplierLower c N n ≤ literalMultiplierUpper c N n →
      Real.log (literalMultiplierUpper c N n) - Real.log (literalMultiplierLower c N n) +
        mertensWindowConstant + 1 ≤ literalMultiplierWidth c :=
    literalMultiplierWidth_bounds hc hN (hA.trans (mem_Icc.mp hn).1) hB
  constructor
  · intro hpH positive
    have hpH' (n : ℕ) (hn : n ∈ Icc A Z) (p : ℕ) (hpP : p ∈ P) :
        p ^ 2 ≤ literalMultiplierLower c N n :=
      (hpH p hpP).trans (literalMultiplierLower_antitone hc
        (hA.trans (mem_Icc.mp hn).1) (mem_Icc.mp hn).2)
    exact hmiddle P (N + linearPrimeStrip c) (linearPrimeStrip c) M A Z
      (signedLiteralTarget positive) (fun _ => signedLiteralSample positive G M)
      (signedLiteralKernel positive φ c N) (literalMultiplierLower c N)
      (literalMultiplierUpper c N) (2 * ∫ u, φ u ^ 2) K V (literalMultiplierWidth c)
      hA hAZ hM hU hK hV hW hp hpp hMp (htarget positive) (hsample positive)
      (hnonneg positive) (hamp positive) (hvar positive) hH hpH' (hs positive) hw
  · intro positive
    exact unit_mangoldt_terminal_Gram_le P (N + linearPrimeStrip c) (linearPrimeStrip c) M A Z
      (signedLiteralTarget positive) (fun _ => signedLiteralSample positive G M)
      (signedLiteralKernel positive φ c N) (literalMultiplierLower c N)
      (literalMultiplierUpper c N) (2 * ∫ u, φ u ^ 2) K V (literalMultiplierWidth c)
      hA hAZ hM hU hK hV hW hp hMp (hsample positive)
      (hnonneg positive) (hamp positive) (hvar positive) hH (hs positive) hw

#print axioms exists_literal_unit_prime_Gram_bounds

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
