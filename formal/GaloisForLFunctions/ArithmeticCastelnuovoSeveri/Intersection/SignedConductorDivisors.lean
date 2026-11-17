import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.ConductorGraphContacts

/-!
# The prime pairing from vertical orders of signed graph divisors

For each base conductor, restrict a divisor supported on its proper multiples
to a thickening of the base graph. Two effective orders record the two signs.
Their logarithmic difference retains the mixed terms of arbitrary integer
divisors. The graph equations determine every local multiplicity.
-/

noncomputable section

open Finset Polynomial Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem graph_ne_on_proper_multiple {i t : ℕ} (hi : i ≠ 0) (ht : 1 < t) :
    conductorContact i (i*t) ≠ 0 := by
  apply Int.natAbs_ne_zero.mpr
  apply mt content_eq_zero_iff.mp
  apply sub_ne_zero.mpr
  apply conductorContact_graph_ne hi (Nat.mul_ne_zero hi (by omega))
  exact (lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hi) ht).ne

/-- Vertical order of a positive base divisor against prescribed thickenings of
all proper multiples up to ratio B. -/
def divisorRowOrder (i B h : ℕ) (b : ℕ → ℕ) : ℕ :=
  verticalIntersection {i} (((Icc 1 B).erase 1).image (i * ·)) (fun _ => h) b

private theorem rowOrder_eq (i B h : ℕ) (hi : 0 < i) (b : ℕ → ℕ) :
    divisorRowOrder i B h b =
      ∏ t ∈ (Icc 1 B).erase 1, conductorContact i (i*t) ^ (h * b (i*t)) := by
  rw [divisorRowOrder, verticalIntersection_eq, prod_singleton, prod_image]
  exact fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hi he

private theorem proper_ratio {t B : ℕ} (ht : t ∈ (Icc 1 B).erase 1) : 1 < t := by
  obtain ⟨hne, hm⟩ := mem_erase.mp ht
  have := (mem_Icc.mp hm).1
  omega

private theorem rowOrder_pos (i B h : ℕ) (hi : 0 < i) (b : ℕ → ℕ) :
    0 < divisorRowOrder i B h b := by
  rw [rowOrder_eq i B h hi]
  exact prod_pos fun _ ht => pow_pos (Nat.pos_of_ne_zero
    (graph_ne_on_proper_multiple hi.ne' (proper_ratio ht))) _

private theorem log_rowOrder (i B h : ℕ) (hi : 0 < i) (b : ℕ → ℕ) :
    Real.log (divisorRowOrder i B h b : ℝ) =
      ∑ t ∈ Icc 1 B, (h : ℝ) * b (i*t) * Λ t := by
  rw [rowOrder_eq i B h hi, Nat.cast_prod, Real.log_prod]
  · calc _ = ∑ t ∈ (Icc 1 B).erase 1, (h : ℝ) * b (i*t) * Λ t := by
           apply sum_congr rfl
           intro t ht
           rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul,
             log_conductorContact_mul hi.ne' (Nat.ne_zero_of_lt (proper_ratio ht))]
         _ = _ := by
           by_cases hb : 1 ∈ Icc 1 B
           · rw [sum_erase_eq_sub hb, ArithmeticFunction.vonMangoldt_apply_one, mul_zero, sub_zero]
           · rw [erase_eq_of_notMem hb]
  · intro t ht
    exact_mod_cast pow_ne_zero _ (graph_ne_on_proper_multiple hi.ne' (proper_ratio ht))

/-- The product of the effective vertical orders with the indicated orientation.
Changing the sign of the second divisor exchanges the two orientations. -/
def signedDivisorOrder (A X B : ℕ) (u v : ℕ → ℤ) : ℕ :=
  ∏ i ∈ Icc A X, divisorRowOrder i B (u i).natAbs
    (fun j => ((u i).sign * v j).toNat)

/-- Difference of log orders for the same and the opposite sign. -/
def signedDivisorHeight (A X B : ℕ) (u v : ℕ → ℤ) : ℝ :=
  Real.log (signedDivisorOrder A X B u v : ℝ) -
    Real.log (signedDivisorOrder A X B u (-v) : ℝ)

private theorem log_signedDivisorOrder {A : ℕ} (hA : 0 < A) (X B : ℕ) (u v : ℕ → ℤ) :
    Real.log (signedDivisorOrder A X B u v : ℝ) =
      ∑ i ∈ Icc A X, ∑ t ∈ Icc 1 B,
        ((u i).natAbs : ℝ) * (((u i).sign * v (i*t)).toNat : ℝ) * Λ t := by
  rw [signedDivisorOrder, Nat.cast_prod, Real.log_prod]
  · exact sum_congr rfl fun i hi => log_rowOrder _ _ _ (hA.trans_le (mem_Icc.mp hi).1) _
  · intro i hi
    exact_mod_cast (rowOrder_pos _ _ _ (hA.trans_le (mem_Icc.mp hi).1) _).ne'

/-- Every signed multiplicity occurs with its original sign and every prime
power with unit local length, even when its prime divides the base. -/
theorem signedDivisorHeight_eq {A : ℕ} (hA : 0 < A) (X B : ℕ) (u v : ℕ → ℤ) :
    signedDivisorHeight A X B u v =
      ∑ i ∈ Icc A X, ∑ t ∈ Icc 1 B, (u i : ℝ) * v (i*t) * Λ t := by
  rw [signedDivisorHeight, log_signedDivisorOrder hA, log_signedDivisorOrder hA, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun t _ => ?_
  simp only [Pi.neg_apply, mul_neg, ← sub_mul, ← mul_sub]
  have hv := Int.toNat_sub_toNat_neg ((u i).sign * v (i*t))
  have hu := Int.sign_mul_natAbs (u i)
  have hv' : ((((u i).sign * v (i*t)).toNat : ℝ) - ((-((u i).sign * v (i*t))).toNat : ℝ)) =
      ((u i).sign : ℝ) * v (i*t) := by exact_mod_cast hv
  have hu' : ((u i).sign : ℝ) * (u i).natAbs = u i := by
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hu
  rw [hv', ← mul_assoc, mul_comm _ ((u i).sign : ℝ), hu']

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
