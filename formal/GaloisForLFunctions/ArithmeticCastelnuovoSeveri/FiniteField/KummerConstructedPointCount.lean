import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerSignedPointFamily

/-!
# Counting the constructed affine points

The trace and signed-Frobenius constructions inject into distinct ordinates
of the literal Kummer equation. Counting their norm fibers gives an explicit
lower bound for its affine solution set. The same trace-fiber count gives
exactly `Q³` affine points on the Hermitian equation.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Injectively indexed fibers of constant size give a lower bound for a relation's solution set. -/
theorem card_relation_lower_bound {I Y Z : Type*} [Finite I] [Finite Y] [Finite Z]
    (P : Y → Z → Prop) (f : I → Y) (hf : Function.Injective f) (n : ℕ)
    (hn : ∀ i, Nat.card {z : Z | P (f i) z} = n) :
    Nat.card I * n ≤ Nat.card {t : Y × Z // P t.1 t.2} := by
  classical
  letI := Fintype.ofFinite I
  let g : (Σ i : I, {z : Z | P (f i) z}) → {t : Y × Z // P t.1 t.2} :=
    fun x => ⟨(f x.1, x.2.val), x.2.property⟩
  have hg : Function.Injective g := by
    rintro ⟨i, ⟨z, hz⟩⟩ ⟨j, ⟨w, hw⟩⟩ h
    have hval := congrArg Subtype.val h
    have hij := hf (congrArg Prod.fst hval)
    have hzw := congrArg Prod.snd hval
    change i = j at hij
    change z = w at hzw
    subst j
    subst w
    rfl
  have hle := Nat.card_le_card_of_injective g hg
  rw [Nat.card_sigma, Finset.sum_const_nat (fun i _ => hn i), Finset.card_univ,
    ← Nat.card_eq_fintype_card] at hle
  exact hle

variable (p : ℕ) [Fact p.Prime]

/-- Parameters for the disjoint union of the two rational-ordinate constructions. -/
abbrev KummerOrdinateParameters (s d r : ℕ) :=
  (KummerTraceScalars p s d × KummerTraceParameters p s d r) ⊕ KummerSignedParameters p s d r

/-- Both constructions as a single map to the affine base line. -/
def kummerConstructedOrdinate (s d r : ℕ) : KummerOrdinateParameters p s d r → SquareConstantField p s :=
  Sum.elim (fun x => kummerTraceFamilyPoint p s d r x.1 x.2) Subtype.val

/-- No two parameters, even from different constructions, give the same ordinate. -/
theorem kummerConstructedOrdinate_injective (s d r : ℕ) :
    Function.Injective (kummerConstructedOrdinate p s d r) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (kummerTraceFamilyPoint_injective p s d r h)
    | inr y =>
      exact ((Set.disjoint_left.mp (kummerTrace_signed_disjoint p s d r))
        ⟨x, rfl⟩ ⟨y, h.symm⟩).elim
  | inr x =>
    cases y with
    | inl y =>
      exact ((Set.disjoint_left.mp (kummerTrace_signed_disjoint p s d r))
        ⟨y, rfl⟩ ⟨x, h⟩).elim
    | inr y => exact congrArg Sum.inr (Subtype.ext h)

/-- Actual ordered pairs satisfying the normalized affine Kummer equation. -/
abbrev NormalizedKummerAffinePoints (s d r : ℕ) :=
  {t : SquareConstantField p s × SquareConstantField p s //
    t.2 ^ (p ^ (s + 1) + 1) = (normalizedKummerBranch p s d r).eval t.1}

/-- The two disjoint families give a certified lower bound for actual affine solutions. -/
theorem normalizedKummer_affine_card_lower_bound (s d r : ℕ) :
    (Nat.card (KummerTraceScalars p s d) * Nat.card (KummerTraceParameters p s d r) +
      Nat.card (KummerSignedParameters p s d r)) * (p ^ (s + 1) + 1) ≤
        Nat.card (NormalizedKummerAffinePoints p s d r) := by
  have h := card_relation_lower_bound
    (fun y z : SquareConstantField p s => z ^ (p ^ (s + 1) + 1) =
      (normalizedKummerBranch p s d r).eval y)
    (kummerConstructedOrdinate p s d r) (kummerConstructedOrdinate_injective p s d r)
    (p ^ (s + 1) + 1) (fun i => by
      cases i with
      | inl x => exact kummerTraceFamilyPoint_fiber_card p s d r x.1 x.2
      | inr x => exact kummerSignedParameter_fiber_card p s d r x)
  simpa only [KummerOrdinateParameters, NormalizedKummerAffinePoints,
    Nat.card_sum, Nat.card_prod] using h

/-- The literal affine Hermitian equation over the square finite field. -/
abbrev HermitianAffinePoints (s : ℕ) :=
  {t : SquareConstantField p s × SquareConstantField p s //
    t.2 ^ p ^ (s + 1) + t.2 = t.1 ^ (p ^ (s + 1) + 1)}

/-- Grouping the affine Hermitian solutions by their first coordinate. -/
def hermitianAffineFiberEquiv (s : ℕ) :
    HermitianAffinePoints p s ≃
      Σ x : SquareConstantField p s,
        {y : SquareConstantField p s | y ^ p ^ (s + 1) + y = x ^ (p ^ (s + 1) + 1)} where
  toFun t := ⟨t.val.1, t.val.2, t.property⟩
  invFun t := ⟨(t.1, t.2.val), t.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Hermitian affine equation has exactly `Q³` rational solutions. -/
theorem hermitianAffinePoints_card (s : ℕ) :
    Nat.card (HermitianAffinePoints p s) = (p ^ (s + 1)) ^ 3 := by
  letI := Fintype.ofFinite (SquareConstantField p s)
  have hf (x : SquareConstantField p s) :
      Nat.card {y : SquareConstantField p s |
        y ^ p ^ (s + 1) + y = x ^ (p ^ (s + 1) + 1)} = p ^ (s + 1) :=
    squareFieldTrace_fiber_card_of_fixed p s _ (squareConstantField_norm_fixed p s x)
  rw [Nat.card_congr (hermitianAffineFiberEquiv p s), Nat.card_sigma,
    Finset.sum_const_nat (fun x _ => hf x), Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [squareConstantField_card]
  have hpow : p ^ (2 * (s + 1)) = (p ^ (s + 1)) ^ 2 := by
    rw [Nat.mul_comm 2 (s + 1), pow_mul]
  rw [hpow]
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
