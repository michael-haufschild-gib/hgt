import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalResidue


/-!
# Rational normalization primes have soluble coordinates

Surjectivity from constants to a prime quotient makes the coordinate
residue a constant. The contracted prime is the corresponding linear
ideal. Reducing the integral radical equation supplies a constant root;
the nonzero linear contraction also proves that the prime has height one.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain

/-- A prime with only constant residues lies above a rational point of the polynomial line. -/
theorem prime_liesOver_linear_of_residue_surjective
    {K B : Type*} [Field K] [CommRing B] [Algebra K B] [Algebra K[X] B]
    [IsScalarTower K K[X] B] (P : Ideal B) [hP : P.IsPrime]
    (hsurj : Function.Surjective (algebraMap K (B ⧸ P))) :
    ∃ a : K, P.LiesOver (Ideal.span {X - C a}) := by
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk P (algebraMap K[X] B X))
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
  have hmax : (Ideal.span {X - C a}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hJ : P.under K[X] ≠ ⊤ := by
    intro h
    have hm : (1 : K[X]) ∈ P.under K[X] := by rw [h]; trivial
    change algebraMap K[X] B 1 ∈ P at hm
    rw [map_one] at hm
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr hm)
  refine ⟨a, (Ideal.liesOver_iff P (Ideal.span {X - C a})).mpr (hmax.eq_of_le hJ ?_)⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change algebraMap K[X] B (X - C a) ∈ P
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_sub, ← ha]
  have hC : Ideal.Quotient.mk P (algebraMap K[X] B (C a)) = algebraMap K (B ⧸ P) a :=
    (IsScalarTower.algebraMap_apply K K[X] (B ⧸ P) a).symm
  rw [hC, sub_self]

/-- A rational prime of the normalization lies above a soluble affine coordinate. -/
theorem squareKummer_rationalPrime_coordinate
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (P : Ideal (SquareKummerNormalization p s c b R)) [hP : P.IsPrime]
    (hsurj : Function.Surjective (algebraMap (SquareConstantField p s)
      (SquareKummerNormalization p s c b R ⧸ P))) :
    ∃ a β : SquareConstantField p s, P.LiesOver (Ideal.span {X - C a}) ∧
      β ^ (p ^ (s + 1) + 1) = (kummerBranch c b R).eval a := by
  obtain ⟨a, ha⟩ := prime_liesOver_linear_of_residue_surjective P hsurj
  letI := ha
  obtain ⟨β, hβ⟩ := hsurj (Ideal.Quotient.mk P (squareKummerIntegralRoot p s c b R))
  refine ⟨a, β, ha, (algebraMap (SquareConstantField p s)
    (SquareKummerNormalization p s c b R ⧸ P)).injective ?_⟩
  rw [map_pow, hβ, ← map_pow, squareKummerIntegralRoot_pow,
    linearPrime_quotient_polynomial a P]

/-- A normalization prime with constant residue field is nonzero. -/
theorem squareKummer_rationalPrime_ne_bot
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (P : Ideal (SquareKummerNormalization p s c b R)) [P.IsPrime]
    (hsurj : Function.Surjective (algebraMap (SquareConstantField p s)
      (SquareKummerNormalization p s c b R ⧸ P))) : P ≠ ⊥ := by
  obtain ⟨a, _, hover, _⟩ := squareKummer_rationalPrime_coordinate p s c b R P hsurj
  letI := hover
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
  exact Ideal.ne_bot_of_liesOver_of_ne_bot
    (show (Ideal.span {X - C a}) ≠ ⊥ from v.ne_bot) P

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
