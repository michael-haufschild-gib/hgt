import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralPrimeMoment
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralShortRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.UpwardProfileNorms
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.SuccPred

/-!
# Three receiving ranges for the literal upward norm

Short, middle and terminal rows partition the full physical harmonic
square. Every covariance error and own-prime tower remains explicit.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset
open GaloisForLFunctions
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence
  CriticalScaleArithmeticRigidity ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory

/-- Uniform coefficient bound for all receiving rows below `A`. -/
def literalShortRowBound (c : ℝ) (N A : ℕ) (P : Finset ℕ) (s V : ℝ) : ℝ :=
  4 * (linearPrimeStrip c : ℝ) * |s| * V *
    (1027 * literalMultiplierWidth c * (∑ p ∈ P, 1 / (p : ℝ)) +
      576 * (P.card : ℝ) * (literalMultiplierLower c N A : ℝ) ^ (-(7 / 16 : ℝ)))

/-- Uniform own-prime-tower mass of either signed row. -/
def literalPrimeTowerBound (φ : ℝ → ℝ) (c : ℝ) (R : ℕ) (P : Finset ℕ) (V : ℝ) : ℝ :=
  (2 * (linearPrimeStrip c : ℝ) * (2 * ∫ u, φ u ^ 2) * V / R) *
    ∑ p ∈ P, Real.log p / (p : ℝ)

/-- The three exact receiving ranges, including covariance errors and own-prime towers. -/
def literalThreeRangeBound (φ : ℝ → ℝ) (c : ℝ) (N M R A J : ℕ)
    (P : Finset ℕ) (s V K : ℝ) : ℝ :=
  (literalShortRowBound c N A P s V ^ 2 * (1 + Real.log A) +
    8 * (s / (∫ u, φ u ^ 2)) ^ 2 *
      (literalMiddleGramBound φ c N P M A J V K +
        literalPrimeTowerBound φ c R P V ^ 2 * (∑ n ∈ Icc A J, 1 / (n : ℝ))) +
    8 * (s / (∫ u, φ u ^ 2)) ^ 2 *
      (literalTerminalGramBound φ c N P M (J + 1) N V K +
        literalPrimeTowerBound φ c R P V ^ 2 * (∑ n ∈ Icc (J + 1) N, 1 / (n : ℝ)))) / Real.log N

/-- The literal physical upward vector satisfies the full three-range estimate for every periodic prime band. -/
theorem exists_literal_upward_three_range_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ0 : ∀ u, 0 ≤ φ u) (hmass : 0 < ∫ u, φ u ^ 2) :
    ∃ p₀ : ℕ, ∃ K : ℝ, 8 ≤ p₀ ∧ 0 ≤ K ∧
      ∀ (c : ℝ), 0 < c → ∀ (N M R A J : ℕ), p₀ ≤ R → linearPrimeStrip c ≤ R →
      2 ≤ A → A ≤ J → J < N → 0 < M → 0 < Real.log N →
      c / N ≤ 1 → linearPrimeStrip c ≤ N → 2 * linearPrimeStrip c ≤ A →
      2 * c * Real.exp 1 * linearPrimeStrip c ≤ N →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, R < p) → (∀ p ∈ P, M.Coprime p) →
      (∀ p ∈ P, p ^ 2 ≤ literalMultiplierLower c N J) →
      ∀ (G : ℕ → ℝ) (s V : ℝ), Function.Periodic G M → 0 ≤ V → (∀ j, |G j| ≤ V) →
      ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ •
        packetVector (fun j => G j * incidencePacket P (fun _ => s) j) N)‖ ^ 2 ≤
        literalThreeRangeBound φ c N M R A J P s V K := by
  obtain ⟨pS, hpS, hshort⟩ := exists_literal_prime_short_row_bound
  obtain ⟨pL, K, hpL, hK, hlong⟩ := exists_literal_prime_long_bounds hφ hsupp hφ0
  refine ⟨max pS pL, K, hpS.trans (le_max_left _ _), hK, ?_⟩
  intro c hc N M R A J hpR hBR hA hAJ hJN hM hlog hwidth hB hBA hsep P hp hRP hMp hpH G s V hG hV hGV
  have hpSR : pS ≤ R := (le_max_left _ _).trans hpR
  have hpLR : pL ≤ R := (le_max_right _ _).trans hpR
  have hN : 1 ≤ N := by omega
  have hA1 : 1 ≤ A := by omega
  have hBP : ∀ p ∈ P, linearPrimeStrip c < p := fun p hp => hBR.trans_lt (hRP p hp)
  have hsmall (n : ℕ) (hn : n ∈ Icc 1 (A - 1)) :
      |logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N
        (fun j => G j * incidencePacket P (fun _ => s) j) n| ≤
        literalShortRowBound c N A P s V := by
    have hn1 := (mem_Icc.mp hn).1
    have hnA : n ≤ A := (mem_Icc.mp hn).2.trans (Nat.sub_le A 1)
    have hnN : n ≤ N := (hnA.trans hAJ).trans hJN.le
    have hpHn : ∀ p ∈ P, p ^ 2 ≤ literalMultiplierLower c N n := fun p hpP =>
      (hpH p hpP).trans (literalMultiplierLower_antitone hc hn1 (hnA.trans hAJ))
    have h := hshort φ hφ hsupp hmass c hc N n (mem_Icc.mpr ⟨hn1, hnN⟩)
      hwidth hB hsep P hp (fun p hpP => hpSR.trans (hRP p hpP).le) hBP hpHn G s V hV hGV
    have hHA : (0 : ℝ) < literalMultiplierLower c N A := by
      exact_mod_cast literalMultiplierLower_pos hc hN hA1
    have hmono : (literalMultiplierLower c N A : ℝ) ≤ literalMultiplierLower c N n := by
      exact_mod_cast literalMultiplierLower_antitone hc hn1 hnA
    have htail := Real.rpow_le_rpow_of_nonpos hHA hmono (by norm_num : -(7 / 16 : ℝ) ≤ 0)
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left htail (by positivity))) (by positivity))
  have hsmallSum :
      (∑ n ∈ Icc 1 (A - 1), logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N
        (fun j => G j * incidencePacket P (fun _ => s) j) n ^ 2 / (n : ℝ)) ≤
        literalShortRowBound c N A P s V ^ 2 * (1 + Real.log A) := by
    have hHarmonic : (∑ n ∈ Icc 1 (A - 1), 1 / (n : ℝ)) ≤ 1 + Real.log A := by
      refine (sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)).trans
        (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log A)
      intro n hn
      exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans (Nat.sub_le A 1)⟩
    calc
      _ ≤ literalShortRowBound c N A P s V ^ 2 * ∑ n ∈ Icc 1 (A - 1), 1 / (n : ℝ) := by
        rw [mul_sum]
        apply sum_le_sum
        intro n hn
        have hsquare := pow_le_pow_left₀ (abs_nonneg _) (hsmall n hn) 2
        rw [sq_abs] at hsquare
        exact (div_le_div_of_nonneg_right hsquare (Nat.cast_nonneg n)).trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left hHarmonic (sq_nonneg _)
  have hmiddle := (hlong c hc N M R A J hpLR hBR hA1 hAJ hJN.le hM hwidth hB hBA
    P hp hRP hMp G s V hG hV hGV).1 hpH
  have hterminal := (hlong c hc N M R (J + 1) N hpLR hBR (by omega) (by omega) le_rfl hM
    hwidth hB (hBA.trans (hAJ.trans (Nat.le_succ J))) P hp hRP hMp G s V hG hV hGV).2
  have hpartition (f : ℕ → ℝ) :
      (∑ n ∈ Icc 1 N, f n) =
        (∑ n ∈ Icc 1 (A - 1), f n) + (∑ n ∈ Icc A J, f n) + (∑ n ∈ Icc (J + 1) N, f n) := by
    have h₁ := sum_Ioc_consecutive f (Nat.zero_le (A - 1)) ((Nat.sub_le A 1).trans hAJ)
    have h₂ := sum_Ioc_consecutive f (Nat.zero_le J) hJN.le
    simp only [← Icc_add_one_left_eq_Ioc, Nat.zero_add, Nat.sub_add_cancel hA1] at h₁ h₂
    rw [← h₂, ← h₁]
  rw [upwardPrimeVector_physical_packet_norm_sq hsupp hc hwidth]
  unfold literalThreeRangeBound
  apply div_le_div_of_nonneg_right _ hlog.le
  rw [hpartition]
  exact add_le_add (add_le_add hsmallSum hmiddle) hterminal

#print axioms exists_literal_upward_three_range_bound

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
