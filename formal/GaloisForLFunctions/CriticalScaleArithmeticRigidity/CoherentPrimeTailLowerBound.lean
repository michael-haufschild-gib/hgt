import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeCoherenceCalculus
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.HarmonicPoleCentering
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AnnularRamanujanFamiliesHaveTwoSidedFrames

/-!
# A source-preserving lower bound for coherent prime tails

Primes above the complementary row quotient contribute complete positive
towers. Their nondivisibility sum is an exact conductor packet with a
coherent constant coefficient. Annular sampling retains that coefficient
with the sharp quadratic conductor loss.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  SuccessorShellArithmetic SignedArithmeticHodgeTheory ArithmeticElectrostatics
  ArithmeticEffectivityTheory

/-- The constant coefficient of the high-prime nondivisibility source. -/
def highPrimePoleMass (P Q : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 Q).filter Nat.Prime, if P < p then Real.log p / (p : ℝ) else 0

/-- Exact conductor coefficients of the high-prime source, including its constant row. -/
def highPrimeSourceCoefficients (P Q : ℕ) : ℕ → ℝ :=
  addConstantConductor
    (primeIncidenceCoefficients (fun p => if P < p then -Real.log p / ((p : ℝ) - 1) else 0))
    (highPrimePoleMass P Q)

/-- No source replacement is needed: the high-prime tail is a literal conductor packet. -/
theorem highPrimeCoherentSource_packet_eq {Q : ℕ} (hQ : 1 ≤ Q) (P n : ℕ) :
    normalizedConductorPacket Q (highPrimeSourceCoefficients P Q) n =
      highPrimeCoherentSource P Q n := by
  rw [highPrimeSourceCoefficients, normalizedConductorPacket_addConstantConductor hQ,
    primeIncidencePacket_eq, highPrimePoleMass, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  have hp0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hpm : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hp1).ne'
  by_cases hP : P < p
  · simp only [if_pos hP]
    by_cases hn : p ∣ n <;> simp only [hn, if_true, if_false]
    all_goals field_simp [hp0, hpm] <;> ring
  · simp only [if_neg hP, zero_mul, zero_add]

theorem highPrimeSourceCoefficients_one (P Q : ℕ) :
    highPrimeSourceCoefficients P Q 1 = highPrimePoleMass P Q := by
  simp only [highPrimeSourceCoefficients, addConstantConductor, if_pos rfl,
    primeIncidenceCoefficients, primeOnly, Nat.not_prime_one, if_false, zero_add]

/-- The coherent constant row gives a lower bound for the full coefficient mass. -/
theorem highPrimePoleMass_sq_le_mass {Q : ℕ} (hQ : 1 ≤ Q) (P : ℕ) :
    highPrimePoleMass P Q ^ 2 ≤ ∑ m ∈ Icc 1 Q, highPrimeSourceCoefficients P Q m ^ 2 := by
  have h := single_le_sum (f := fun m => highPrimeSourceCoefficients P Q m ^ 2)
    (fun m _ => sq_nonneg _) (mem_Icc.mpr ⟨le_rfl, hQ⟩)
  rwa [highPrimeSourceCoefficients_one] at h

/-- Annular sampling preserves the coherent source with an explicit first-weight loss. -/
theorem highPrimeCoherentSource_annular_lower {Q : ℕ} (hQ : 2 ≤ Q) (P A K : ℕ) :
    ((∑ n ∈ Icc (A + 1) (A + K), 1 / (n : ℝ)) -
      ((Q : ℝ) * ((Q : ℝ) - 1)) / ((A : ℝ) + 1)) * highPrimePoleMass P Q ^ 2 ≤
        ∑ n ∈ Icc (A + 1) (A + K), highPrimeCoherentSource P Q n ^ 2 / (n : ℝ) := by
  let c := highPrimeSourceCoefficients P Q
  let H : ℝ := ∑ n ∈ Icc (A + 1) (A + K), 1 / (n : ℝ)
  let D : ℝ := ((Q : ℝ) * ((Q : ℝ) - 1)) / ((A : ℝ) + 1)
  let M : ℝ := ∑ m ∈ Icc 1 Q, c m ^ 2
  have h := abs_ramanujanPoleProfile_annular_gram_discrepancy_le hQ c A K
  have heq (n : ℕ) : (∑ m ∈ Icc 1 Q, c m * ramanujanPoleProfile m n) ^ 2 =
      highPrimeCoherentSource P Q n ^ 2 / (n : ℝ) := by
    simp only [ramanujanPoleProfile, ← mul_div_assoc, ← sum_div]
    change (normalizedConductorPacket Q c n / Real.sqrt n) ^ 2 = _
    rw [highPrimeCoherentSource_packet_eq (by omega : 1 ≤ Q), div_pow,
      Real.sq_sqrt (Nat.cast_nonneg n)]
  simp only [heq] at h
  have hl := (abs_le.mp h).1
  change -(D * M) ≤ _ - H * M at hl
  have hm : highPrimePoleMass P Q ^ 2 ≤ M :=
    highPrimePoleMass_sq_le_mass (by omega : 1 ≤ Q) P
  change (H - D) * highPrimePoleMass P Q ^ 2 ≤ _
  by_cases hc : 0 ≤ H - D
  · have hmul := mul_le_mul_of_nonneg_left hm hc
    nlinarith only [hl, hmul]
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hc)) (sq_nonneg _)).trans
      (sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))

/-- Beyond `N/P`, the literal coherent tail dominates every prime tower above `P`. -/
theorem highPrimeSource_le_row_tail {P N n : ℕ} (hP : 0 < P)
    (hn : N / P < n) (Q : ℕ) :
    highPrimeCoherentSource P Q n ≤
      completedPrimeDilationTail Q (primeOnly primePoleWitness) (N / n) n := by
  have hn0 : 0 < n := by omega
  have hN := (Nat.div_lt_iff_lt_mul hP).mp hn
  have hy : N / n < P := (Nat.div_lt_iff_lt_mul hn0).mpr (by simpa only [Nat.mul_comm] using hN)
  exact highPrimeCoherentSource_le_completedTail hy.le Q n

/-- The exact coherent complementary tail has an annular lower bound with the
constant source coefficient retained and no unproved distribution hypothesis. -/
theorem coherentPrimeTail_annular_lower {P Q : ℕ} (hP : 0 < P) (hQ : 2 ≤ Q) (N : ℕ) :
    ((∑ n ∈ Icc (N / P + 1) N, 1 / (n : ℝ)) -
      ((Q : ℝ) * ((Q : ℝ) - 1)) / (((N / P : ℕ) : ℝ) + 1)) * highPrimePoleMass P Q ^ 2 ≤
        ∑ n ∈ Icc 1 N,
          completedPrimeDilationTail Q (primeOnly primePoleWitness) (N / n) n ^ 2 / (n : ℝ) := by
  have hA : N / P ≤ N := Nat.div_le_self N P
  have hframe := highPrimeCoherentSource_annular_lower hQ P (N / P) (N - N / P)
  rw [Nat.add_sub_of_le hA] at hframe
  refine hframe.trans ((sum_le_sum fun n hn => ?_).trans ?_)
  · have hnA : N / P < n := by have := (mem_Icc.mp hn).1; omega
    have hsource := highPrimeSource_le_row_tail hP hnA Q
    have hpos := highPrimeCoherentSource_nonneg P Q n
    have hprod := mul_nonneg (sub_nonneg.mpr hsource)
      (add_nonneg (hpos.trans hsource) hpos)
    exact div_le_div_of_nonneg_right (by nlinarith only [hprod]) (Nat.cast_nonneg n)
  · apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hn).1; omega, (mem_Icc.mp hn).2⟩
    · intro n _ _
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

/-- The scalar row cannot cancel a tail square larger than its proved logarithmic cost. -/
theorem exists_primeResidual_sq_lower_of_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ Q N : ℕ, 2 ≤ Q → 2 ≤ N → ∀ a : ℕ → ℝ,
      (1 / 2 : ℝ) *
          (∑ n ∈ Icc 1 N, completedPrimeDilationTail Q a (N / n) n ^ 2 / (n : ℝ)) -
        C * (1 + Real.log Q) * (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
          ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2 := by
  obtain ⟨C, hC, hscalar⟩ := exists_scalarPrimeResidual_packet_sq_le
  refine ⟨C, hC, ?_⟩
  intro Q N hQ hN a
  let r : ℕ → ℝ := fun n => mertensSum (N / n) + Real.log n -
    (Real.log N - Real.eulerMascheroniConstant)
  let F := normalizedConductorPacket Q a
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs : (∑ n ∈ Icc 1 N, r n ^ 2 * F n ^ 2 / (n : ℝ)) / Real.log N ≤
      C * (1 + Real.log Q) / Real.log N * (∑ m ∈ Icc 1 Q, a m ^ 2) := by
    simpa only [r, F, normalizedConductorPacket] using hscalar Q N hQ hN a
  have hs0 : (∑ n ∈ Icc 1 N, r n ^ 2 * F n ^ 2 / (n : ℝ)) ≤
      C * (1 + Real.log Q) * (∑ m ∈ Icc 1 Q, a m ^ 2) := by
    calc
      _ = ((∑ n ∈ Icc 1 N, r n ^ 2 * F n ^ 2 / (n : ℝ)) / Real.log N) * Real.log N :=
        (div_mul_cancel₀ _ hlog.ne').symm
      _ ≤ (C * (1 + Real.log Q) / Real.log N *
          (∑ m ∈ Icc 1 Q, a m ^ 2)) * Real.log N := mul_le_mul_of_nonneg_right hs hlog.le
      _ = _ := by field_simp
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) :
      (1 / 2 : ℝ) * (completedPrimeDilationTail Q a (N / n) n ^ 2 / (n : ℝ)) -
        r n ^ 2 * F n ^ 2 / (n : ℝ) ≤
          (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2 := by
    rw [primeResidual_packet_eq_scalar_sub_tail a hn, mul_pow, poleVector, div_pow,
      one_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_one_div]
    have hsq : completedPrimeDilationTail Q a (N / n) n ^ 2 / 2 - r n ^ 2 * F n ^ 2 ≤
        (r n * F n - completedPrimeDilationTail Q a (N / n) n) ^ 2 := by
      nlinarith only [sq_nonneg (r n * F n - completedPrimeDilationTail Q a (N / n) n / 2)]
    exact (show _ = (completedPrimeDilationTail Q a (N / n) n ^ 2 / 2 -
      r n ^ 2 * F n ^ 2) / (n : ℝ) by ring).trans_le
        (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg n))
  have hsum := sum_le_sum hrow
  rw [sum_sub_distrib, ← mul_sum] at hsum
  linarith only [hsum, hs0]

/-- A completely explicit coherent source survives the scalar correction, with only
the independently proved scalar coefficient cost subtracted. -/
theorem exists_coherentPrimeResidual_annular_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ P Q N : ℕ, 0 < P → 2 ≤ Q → 2 ≤ N →
      (1 / 2 : ℝ) *
        ((∑ n ∈ Icc (N / P + 1) N, 1 / (n : ℝ)) -
          ((Q : ℝ) * ((Q : ℝ) - 1)) / (((N / P : ℕ) : ℝ) + 1)) * highPrimePoleMass P Q ^ 2 -
        C * (1 + Real.log Q) * (∑ m ∈ Icc 1 Q, primeOnly primePoleWitness m ^ 2) ≤
          ∑ n ∈ Icc 1 N,
            (∑ m ∈ Icc 1 Q, primeOnly primePoleWitness m * ramanujanPrimeResidual m N n) ^ 2 := by
  obtain ⟨C, hC, hres⟩ := exists_primeResidual_sq_lower_of_tail
  refine ⟨C, hC, ?_⟩
  intro P Q N hP hQ hN
  have hr := hres Q N hQ hN (primeOnly primePoleWitness)
  have ht := coherentPrimeTail_annular_lower hP hQ N
  linarith only [hr, ht]

#print axioms highPrimeCoherentSource_packet_eq
#print axioms highPrimeCoherentSource_annular_lower
#print axioms coherentPrimeTail_annular_lower
#print axioms exists_primeResidual_sq_lower_of_tail
#print axioms exists_coherentPrimeResidual_annular_lower

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
