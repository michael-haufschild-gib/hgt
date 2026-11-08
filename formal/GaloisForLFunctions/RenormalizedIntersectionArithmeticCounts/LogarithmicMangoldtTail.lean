import GaloisForLFunctions.RHTower.Sieve.PrimeLogPowerTail
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments

/-!
# The logarithmic Mangoldt tail

Prime-density logarithmic summability and the finite proper-prime-power mass
give convergence of the full Mangoldt tail at every logarithmic exponent
strictly greater than one. This supplies the forward divisor row estimate.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

/-- The positive logarithmic conductor, including the harmless zero coordinate. -/
def logConductor (n : ℕ) : ℝ := 1+Real.log n

theorem one_le_logConductor (n : ℕ) : 1 ≤ logConductor n := by
  rcases n with _|n
  · simp [logConductor]
  · have h := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n) :
        (1:ℝ) ≤ ((n+1:ℕ):ℝ))
    dsimp only [logConductor]
    linarith only [h]

/-- Proper prime powers have finite Mangoldt mass at reciprocal conductor weight. -/
theorem summable_nonprime_mangoldt_reciprocal :
    Summable (fun n : ℕ => if n.Prime then (0:ℝ) else Λ n/(n:ℝ)) := by
  have hn (n : ℕ) : 0 ≤ (if n.Prime then (0:ℝ) else Λ n/(n:ℝ)) := by
    split_ifs
    · exact le_rfl
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  apply summable_of_sum_le hn (c := 72)
  intro S
  have hb := RHTower.sum_nonprime_vonMangoldt_rpow_le
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (S.sup id)
  norm_num only [show (-(1/2+(1/2:ℝ))) = -1 by norm_num,
    Real.rpow_neg_one,div_eq_mul_inv] at hb
  have hsub : S ⊆ insert 0 (Icc 1 (S.sup id)) := by
    intro n hnS
    by_cases hz : n=0
    · exact mem_insert.mpr (Or.inl hz)
    · exact mem_insert_of_mem (mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hz,Finset.le_sup (f := id) hnS⟩)
  calc (∑ n∈S,if n.Prime then (0:ℝ) else Λ n/(n:ℝ)) ≤
        ∑ n∈insert 0 (Icc 1 (S.sup id)),if n.Prime then (0:ℝ) else Λ n/(n:ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hn n)
       _ = ∑ n∈(Icc 1 (S.sup id)).filter (fun n => ¬n.Prime),Λ n/(n:ℝ) := by
        rw [sum_insert (by simp : 0∉Icc 1 (S.sup id))]
        simp only [Nat.not_prime_zero,ite_false,Nat.cast_zero,div_zero,zero_add,sum_filter]
        apply sum_congr rfl
        intro n _
        by_cases hp : n.Prime <;> simp only [hp,not_true_eq_false,not_false_eq_true,ite_false,ite_true]
       _ ≤ 72 := by simpa only [div_eq_mul_inv] using hb

/-- The Mangoldt logarithmic tail converges throughout its full prime-density range. -/
theorem summable_mangoldt_logConductor (a : ℝ) (ha : 1 < a) :
    Summable (fun n : ℕ => Λ n/((n:ℝ)*(logConductor n)^a)) := by
  have hp := RHTower.Sieve.summable_primes_one_div_mul_log_rpow
    (by linarith only [ha] : 0 < a-1)
  have hprime : Summable (fun p : Nat.Primes => Λ (p:ℕ)/((p:ℝ)*(logConductor p)^a)) := by
    apply hp.of_nonneg_of_le
    · intro p
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith [one_le_logConductor p]) _))
    · intro p
      have hp0 : (0:ℝ) < p := by exact_mod_cast p.property.pos
      have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast p.property.one_lt)
      have hpow : (Real.log p)^a ≤ (logConductor p)^a :=
        Real.rpow_le_rpow hl.le (by dsimp only [logConductor]; linarith only) (by linarith only [ha])
      have he : (Real.log p)^a=Real.log p*(Real.log p)^(a-1) := by
        calc (Real.log p)^a=(Real.log p)^((1:ℝ)+(a-1)) := by congr 1; ring
             _ = _ := by rw [Real.rpow_add hl,Real.rpow_one]
      rw [ArithmeticFunction.vonMangoldt_apply_prime p.property]
      calc Real.log p/((p:ℝ)*(logConductor p)^a) ≤ Real.log p/((p:ℝ)*(Real.log p)^a) :=
          div_le_div_of_nonneg_left hl.le (mul_pos hp0 (Real.rpow_pos_of_pos hl _))
            (mul_le_mul_of_nonneg_left hpow hp0.le)
           _ = 1/((p:ℝ)*(Real.log p)^(a-1)) := by
            rw [he]
            field_simp [hp0.ne',hl.ne',(Real.rpow_pos_of_pos hl (a-1)).ne']
  have hpi : Summable (fun n : ℕ => if n.Prime then Λ n/((n:ℝ)*(logConductor n)^a) else 0) := by
    have hz (n : ℕ) (hn : n∉Set.range (fun p : Nat.Primes => (p:ℕ))) :
        (if n.Prime then Λ n/((n:ℝ)*(logConductor n)^a) else 0)=0 := by
      have hp : ¬n.Prime := fun hp => hn ⟨⟨n,hp⟩,rfl⟩
      exact if_neg hp
    apply (Subtype.val_injective.summable_iff hz).mp
    exact hprime.congr fun p => by simp only [p.property,ite_true,Function.comp_apply]
  have hn : Summable (fun n : ℕ => if n.Prime then (0:ℝ) else Λ n/((n:ℝ)*(logConductor n)^a)) := by
    apply summable_nonprime_mangoldt_reciprocal.of_nonneg_of_le
    · intro n
      split_ifs
      · exact le_rfl
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith [one_le_logConductor n]) _))
    · intro n
      split_ifs
      · exact le_rfl
      · rw [div_mul_eq_div_div]
        exact div_le_self (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
          (Real.one_le_rpow (one_le_logConductor n) (by linarith only [ha]))
  exact (hpi.add hn).congr fun n => by split_ifs <;> simp only [add_zero,zero_add]

#print axioms summable_nonprime_mangoldt_reciprocal
#print axioms summable_mangoldt_logConductor
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
