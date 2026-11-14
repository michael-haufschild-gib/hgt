import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFiniteRationalPrimes

/-!
# Rational places in the normalization charts

The complete finite-prime classification and the unique prime at infinity
give the exact count. Natural-number subtraction bounds put this count
in the form `Q² + 1 + (q-1)Q(N-δ)` without a genus or point-bound input.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

/-- Rational finite normalization primes together with the actual prime fiber at infinity. -/
def normalizedKummerRationalChartPlaces : Type :=
  {P // P ∈ normalizedKummerRationalPrimes p d n r} ⊕
    {P : Ideal (SquareKummerInfinityNormalization p (kummerSquareIndex d n)
        ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
        (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))) //
      P.IsPrime ∧ P.LiesOver (Ideal.span {(X : (SquareConstantField p (kummerSquareIndex d n))[X])})}

/-- The two normalization charts have the exact rational place count before arithmetic simplification. -/
theorem normalizedKummerRationalChartPlaces_card :
    Nat.card (normalizedKummerRationalChartPlaces p d n r) =
      (p ^ (d + 1) * p ^ (kummerSquareIndex d n + 1) - 1 -
        (p ^ (d + 1) - 1) * Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
          (kummerExponent (p ^ (d + 1)) (r + 1))) * (p ^ (kummerSquareIndex d n + 1) + 1) +
      (p ^ (d + 1) - 1) * Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
        (kummerExponent (p ^ (d + 1)) (r + 1)) + 2 := by
  classical
  let I := {P : Ideal (SquareKummerInfinityNormalization p (kummerSquareIndex d n)
        ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
        (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))) //
      P.IsPrime ∧ P.LiesOver (Ideal.span {(X : (SquareConstantField p (kummerSquareIndex d n))[X])})}
  obtain ⟨P, hP, huniq⟩ := squareKummerInfinity_unique p (kummerSquareIndex d n)
    ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1)) d (r + 1)
  letI : Unique I := { default := ⟨P, hP⟩, uniq := fun Q => Subtype.ext (huniq Q.val Q.property) }
  have hI : Nat.card I = 1 := Nat.card_unique
  change Nat.card (_ ⊕ I) = _
  rw [Nat.card_sum, Nat.card_eq_finsetCard, normalizedKummerRationalPrimes_card,
    kummerOrdinateParameters_primePower_card, hI]

/-- The rational place count of the two normalization charts has the maximal-curve form. -/
theorem normalizedKummerRationalChartPlaces_card_closed :
    Nat.card (normalizedKummerRationalChartPlaces p d n r) =
      (p ^ (kummerSquareIndex d n + 1)) ^ 2 + 1 +
        (p ^ (d + 1) - 1) * p ^ (kummerSquareIndex d n + 1) *
          (p ^ (kummerSquareIndex d n + 1) + 1 -
            Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
              (kummerExponent (p ^ (d + 1)) (r + 1))) := by
  rw [normalizedKummerRationalChartPlaces_card]
  let q := p ^ (d + 1)
  let Q := p ^ (kummerSquareIndex d n + 1)
  let δ := Nat.gcd (Q + 1) (kummerExponent q (r + 1))
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hqQ : q ≤ Q := by
    dsimp only [q, Q]
    rw [kummerSquareIndex_succ]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos n))
  have hδ : δ ≤ Q + 1 := Nat.le_of_dvd (Nat.succ_pos _) (Nat.gcd_dvd_left _ _)
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hbound : (q - 1) * δ + 1 ≤ q * Q := by
    have hmul := Nat.mul_le_mul_left (q - 1) hδ
    nlinarith only [hmul, hqsub, hqQ, congrArg (fun x : ℕ => x * Q) hqsub]
  have hfirst : q * Q - 1 + 1 = q * Q := Nat.sub_add_cancel (by nlinarith only [hbound])
  have hsecond : q * Q - 1 - (q - 1) * δ + (q - 1) * δ = q * Q - 1 :=
    Nat.sub_add_cancel (by omega)
  have hlast : Q + 1 - δ + δ = Q + 1 := Nat.sub_add_cancel hδ
  change (q * Q - 1 - (q - 1) * δ) * (Q + 1) + (q - 1) * δ + 2 =
    Q ^ 2 + 1 + (q - 1) * Q * (Q + 1 - δ)
  nlinarith only [congrArg (fun x : ℕ => x * (Q + 1)) hsecond,
    congrArg (fun x : ℕ => x * (Q + 1)) hfirst,
    congrArg (fun x : ℕ => (q - 1) * Q * x) hlast,
    congrArg (fun x : ℕ => x * Q) hqsub, congrArg (fun x : ℕ => x * Q ^ 2) hqsub]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
