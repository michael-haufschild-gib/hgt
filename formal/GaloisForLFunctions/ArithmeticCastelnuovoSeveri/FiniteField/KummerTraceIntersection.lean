import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterFields
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.InvolutiveTraceFibers

/-!
# Exact trace-intersection counts

The auxiliary fixed field has either trivial or nontrivial middle Frobenius.
The trace-one intersection therefore has size zero or one in the trivial
case, according to characteristic, and `p^gcd(m,k)` in the nontrivial case.
Subtracting this intersection gives the exact number of trace parameters.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticHarmonicAnalysis
open scoped Classical

/-- Removing one predicate from a finite subtype subtracts the intersection count. -/
theorem card_subtype_and_not {K : Type*} [Finite K] (P Q : K → Prop) :
    Nat.card {x : K // P x ∧ ¬Q x} = Nat.card {x : K // P x} - Nat.card {x : K // P x ∧ Q x} := by
  letI := Fintype.ofFinite {x : K // P x}
  let e (T : K → Prop) : {x : {x : K // P x} // T x.val} ≃ {x : K // P x ∧ T x} :=
    Equiv.subtypeSubtypeEquivSubtypeInter P T
  have hc : Nat.card {x : {x : K // P x} // ¬Q x.val} =
      Nat.card {x : K // P x} - Nat.card {x : {x : K // P x} // Q x.val} := by
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_subtype_compl (fun x : {x : K // P x} => Q x.val)
  rw [Nat.card_congr (e (fun x => ¬Q x)), Nat.card_congr (e Q)] at hc
  exact hc

variable (p : ℕ) [Fact p.Prime]

/-- The actual trace-one intersection with an auxiliary fixed field. -/
abbrev SquareTraceIntersection (s k : ℕ) :=
  {u : SquareConstantField p s // u ^ p ^ (s + 1) + u = 1 ∧ u ^ p ^ k = u}

/-- The ambient intersection is the trace-one fiber of the restricted involution. -/
def squareTraceIntersectionEquiv (s k : ℕ) :
    SquareTraceIntersection p s k ≃
      {x : KummerAuxiliaryField p s k // kummerAuxiliaryFrobenius p s k x + x = 1} where
  toFun u := ⟨⟨u.val, u.property.2⟩, Subtype.ext u.property.1⟩
  invFun x := ⟨x.val.val, congrArg Subtype.val x.property, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A formula for the excluded trace parameters, involving only characteristic and gcds. -/
def kummerTraceIntersectionNumber (s k : ℕ) : ℕ :=
  if Nat.gcd (2 * (s + 1)) k = Nat.gcd (s + 1) k then
    if p = 2 then 0 else 1
  else p ^ Nat.gcd (s + 1) k

/-- The trace-one intersection has the predicted cardinality in every characteristic. -/
theorem squareTraceIntersection_card (s k : ℕ) :
    Nat.card (SquareTraceIntersection p s k) = kummerTraceIntersectionNumber p s k := by
  rw [Nat.card_congr (squareTraceIntersectionEquiv p s k)]
  unfold kummerTraceIntersectionNumber
  by_cases h : Nat.gcd (2 * (s + 1)) k = Nat.gcd (s + 1) k
  · rw [if_pos h, kummerAuxiliaryFrobenius_eq_id p s k h]
    change Nat.card {x : KummerAuxiliaryField p s k // x + x = 1} = _
    rw [identity_trace_one_card]
    have h2 : (2 : KummerAuxiliaryField p s k) = 0 ↔ p = 2 :=
      (CharP.cast_eq_zero_iff (KummerAuxiliaryField p s k) p 2).trans
        ((Nat.prime_two.dvd_iff_eq (Fact.out : p.Prime).ne_one).trans eq_comm)
    simp only [h2]
  · rw [if_neg h, involution_trace_one_card (kummerAuxiliaryFrobenius p s k)
      (kummerAuxiliaryFrobenius_involutive p s k) (kummerAuxiliaryFrobenius_nontrivial p s k h),
      kummerAuxiliaryFixed_card]

/-- The trace construction uses exactly `Q` minus the explicitly evaluated intersection. -/
theorem kummerTraceParameters_card (s d r : ℕ) :
    Nat.card (KummerTraceParameters p s d r) =
      p ^ (s + 1) - kummerTraceIntersectionNumber p s ((d + 1) * (r + 1)) := by
  change Nat.card {u : SquareConstantField p s //
    u ^ p ^ (s + 1) + u = 1 ∧ ¬u ^ (p ^ (d + 1)) ^ (r + 1) = u} = _
  rw [card_subtype_and_not]
  erw [squareFieldTrace_one_card]
  congr 1
  have hc := squareTraceIntersection_card p s ((d + 1) * (r + 1))
  simpa only [SquareTraceIntersection, pow_mul p] using hc

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
