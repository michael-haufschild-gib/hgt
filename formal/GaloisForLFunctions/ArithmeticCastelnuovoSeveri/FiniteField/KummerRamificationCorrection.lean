import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.KummerExponentGCD

/-!
# The ramification gcd equals the point-count correction

The trace intersection and signed-family correction add to the gcd of the
Kummer degree and the branch multiplicity. The identity follows from the
parity of the reduced exponent and holds for every constructed prime-power
family.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The trace intersection is governed by the parity of the reduced auxiliary period. -/
theorem kummerTraceIntersectionNumber_parity (p s k : ℕ) :
    kummerTraceIntersectionNumber p s k =
      if Even (k / Nat.gcd (s + 1) k) then p ^ Nat.gcd (s + 1) k
      else if p = 2 then 0 else 1 := by
  unfold kummerTraceIntersectionNumber
  simp only [gcd_double_left_eq_iff (s + 1) k (Nat.succ_pos s)]
  by_cases he : Even (k / Nat.gcd (s + 1) k) <;> simp only [he, not_true_eq_false,
    not_false_eq_true, if_true, if_false]

/-- Expressing the base size as a prime power cancels the common field-degree factor. -/
theorem kummerTraceIntersectionNumber_primePower (p d n r : ℕ) :
    kummerTraceIntersectionNumber p (kummerSquareIndex d n) ((d + 1) * (r + 1)) =
      if Even ((r + 1) / Nat.gcd (n + 1) (r + 1)) then
        (p ^ (d + 1)) ^ Nat.gcd (n + 1) (r + 1)
      else if p = 2 then 0 else 1 := by
  rw [kummerTraceIntersectionNumber_parity, kummerSquareIndex_succ,
    Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ (Nat.succ_pos d), pow_mul]

variable (p : ℕ) [Fact p.Prime]

/-- The excluded trace count plus the signed correction is exactly the branch-multiplicity gcd. -/
theorem kummer_ramification_correction (d n r : ℕ) :
    Nat.gcd ((p ^ (d + 1)) ^ (n + 1) + 1) (kummerExponent (p ^ (d + 1)) (r + 1)) =
      kummerTraceIntersectionNumber p (kummerSquareIndex d n) ((d + 1) * (r + 1)) +
        (if p = 2 ∨ Even (r + 1) then 1 else 0) := by
  rw [kummerExponent_gcd, kummerTraceIntersectionNumber_primePower]
  by_cases hr : Even ((r + 1) / Nat.gcd (n + 1) (r + 1))
  · rw [if_pos hr, if_pos hr]
    have he : Even (r + 1) := by
      have hm := hr.mul_left (Nat.gcd (n + 1) (r + 1))
      rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_right (n + 1) (r + 1))] at hm
    rw [if_pos (Or.inr he)]
  · rw [if_neg hr, if_neg hr]
    by_cases hp : p = 2
    · have hq : ¬Odd (p ^ (d + 1)) := by
        have he : Even (p ^ (d + 1)) :=
          Nat.even_pow.mpr ⟨(Fact.out : p.Prime).even_iff.mpr hp, Nat.succ_ne_zero d⟩
        exact fun ho => (Nat.not_even_iff_odd.mpr ho) he
      rw [if_neg (fun h => hq h.1), if_pos hp, if_pos (Or.inl hp)]
    · have hq : Odd (p ^ (d + 1)) := ((Fact.out : p.Prime).odd_of_ne_two hp).pow
      simp only [hp, hq, true_and, false_or, if_false]
      split_ifs <;> rfl

/-- The excluded trace intersection cannot exceed the full trace-one fiber. -/
theorem kummerTraceIntersectionNumber_le (s k : ℕ) :
    kummerTraceIntersectionNumber p s k ≤ p ^ (s + 1) := by
  let f : SquareTraceIntersection p s k →
      {u : SquareConstantField p s | u ^ p ^ (s + 1) + u = 1} :=
    fun u => ⟨u.val, u.property.1⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun u : {u : SquareConstantField p s | u ^ p ^ (s + 1) + u = 1} => u.val) h
  have hc := Nat.card_le_card_of_injective f hf
  rw [squareTraceIntersection_card, squareFieldTrace_one_card] at hc
  exact hc

private theorem ordinate_count_identity (q Q t : ℕ) (e : Prop) [Decidable e]
    (hq : 1 ≤ q) (hQ : q ≤ Q) (ht : t ≤ Q) :
    (q - 1) * (Q - t) + (if e then Q - q else Q - 1) =
      q * Q - 1 - (q - 1) * (t + if e then 1 else 0) := by
  have hq' := Nat.sub_add_cancel hq
  have ht' := Nat.sub_add_cancel ht
  by_cases he : e
  · rw [if_pos he, if_pos he]
    have hb : (q - 1) * (Q - t) + (Q - q) + (1 + (q - 1) * (t + 1)) = q * Q := by
      calc
        _ = (q - 1) * ((Q - t) + t) + (Q - q) + ((q - 1) + 1) := by ring
        _ = (q - 1) * Q + ((Q - q) + q) := by rw [ht', hq', add_assoc]
        _ = ((q - 1) + 1) * Q := by rw [Nat.sub_add_cancel hQ]; ring
        _ = q * Q := by rw [hq']
    rw [Nat.sub_sub, ← hb, Nat.add_sub_cancel]
  · rw [if_neg he, if_neg he]
    have hb : (q - 1) * (Q - t) + (Q - 1) + (1 + (q - 1) * (t + 0)) = q * Q := by
      calc
        _ = (q - 1) * ((Q - t) + t) + ((Q - 1) + 1) := by ring
        _ = ((q - 1) + 1) * Q := by rw [ht', Nat.sub_add_cancel (hq.trans hQ)]; ring
        _ = q * Q := by rw [hq']
    rw [Nat.sub_sub, ← hb, Nat.add_sub_cancel]

/-- The two constructions supply exactly the gcd-predicted number of distinct ordinates. -/
theorem kummerOrdinateParameters_primePower_card (d n r : ℕ) :
    Nat.card (KummerOrdinateParameters p (kummerSquareIndex d n) d r) =
      p ^ (d + 1) * p ^ (kummerSquareIndex d n + 1) - 1 -
      (p ^ (d + 1) - 1) *
        Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
          (kummerExponent (p ^ (d + 1)) (r + 1)) := by
  have hQ : p ^ (d + 1) ≤ p ^ (kummerSquareIndex d n + 1) := by
    rw [kummerSquareIndex_succ]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos n))
  have he := ordinate_count_identity (p ^ (d + 1)) (p ^ (kummerSquareIndex d n + 1))
    (kummerTraceIntersectionNumber p (kummerSquareIndex d n) ((d + 1) * (r + 1)))
    (p = 2 ∨ Even (r + 1)) (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos) hQ
    (kummerTraceIntersectionNumber_le p _ _)
  have hδ := kummer_ramification_correction p d n r
  rw [← pow_mul, ← kummerSquareIndex_succ] at hδ
  have hd : d + 1 ∣ kummerSquareIndex d n + 1 := by
    rw [kummerSquareIndex_succ]
    exact dvd_mul_right _ _
  rw [KummerOrdinateParameters, Nat.card_sum, Nat.card_prod,
    kummerTraceScalars_card_of_dvd p _ d hd, kummerTraceParameters_card,
    kummerSignedParameters_card p _ d r hd, he, ← hδ]

/-- The affine lower bound depends only on the base size, extension size, and ramification gcd. -/
theorem normalizedKummer_primePower_affine_card_lower_bound_gcd (d n r : ℕ) :
    (p ^ (d + 1) * p ^ (kummerSquareIndex d n + 1) - 1 -
      (p ^ (d + 1) - 1) *
        Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
          (kummerExponent (p ^ (d + 1)) (r + 1))) *
      (p ^ (kummerSquareIndex d n + 1) + 1) ≤
        Nat.card (NormalizedKummerAffinePoints p (kummerSquareIndex d n) d r) := by
  rw [← kummerOrdinateParameters_primePower_card]
  simpa only [KummerOrdinateParameters, Nat.card_sum, Nat.card_prod] using
    normalizedKummer_affine_card_lower_bound p (kummerSquareIndex d n) d r

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
