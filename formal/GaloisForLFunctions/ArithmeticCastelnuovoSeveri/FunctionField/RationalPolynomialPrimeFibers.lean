import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalPrimeCoordinate
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDistinguishedPlaceCount

/-!
# Rational normalization primes as rational-coordinate fibers

A prime quotient consisting of constants gives a unique coordinate in
the constant field. Grouping primes by this coordinate identifies all
rational primes with the disjoint sum of the rational parts of the
linear fibers. The same primes are exactly the rational height-one
normalization places.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (K B : Type*) [Field K] [CommRing B] [IsDedekindDomain B]
    [Algebra K B] [Algebra K[X] B] [IsScalarTower K K[X] B]
    [Module.IsTorsionFree K[X] B]

/-- Actual prime ideals whose quotient is exhausted by constants. -/
def RationalPolynomialPrimes :=
  {P : Ideal B // P.IsPrime ∧ Function.Surjective (algebraMap K (B ⧸ P))}

/-- The rational part of the full normalization fiber above one constant coordinate. -/
abbrev RationalPolynomialPrimeFiber (x : K) :=
  {P : {P : Ideal B // P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {X - C x}) B} //
    Function.Surjective (algebraMap K (B ⧸ P.val))}

/-- Every constant-residue prime has positive height because its linear base contraction is nonzero. -/
theorem rationalPolynomialPrime_ne_bot (P : RationalPolynomialPrimes K B) : P.val ≠ ⊥ := by
  letI := P.property.1
  obtain ⟨x, hx⟩ := prime_liesOver_linear_of_residue_surjective P.val P.property.2
  letI := hx
  exact Ideal.ne_bot_of_liesOver_of_ne_bot
    (show (Ideal.span {X - C x}) ≠ ⊥ from
      (GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)).ne_bot) P.val

/-- Forgetting the coordinate turns a rational fiber prime into an actual rational normalization prime. -/
def rationalPolynomialPrimeFiberToPrime
    (z : (x : K) × RationalPolynomialPrimeFiber K B x) : RationalPolynomialPrimes K B := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C z.1)
  letI : (Ideal.span {X - C z.1}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C z.1}) ≠ ⊥ := v.ne_bot
  have hp := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp z.2.val.property
  exact ⟨z.2.val.val, hp.1, z.2.property⟩

omit [IsScalarTower K K[X] B] in
private theorem fiberToPrime_injective : Function.Injective (rationalPolynomialPrimeFiberToPrime K B) := by
  intro z w h
  rcases z with ⟨x, P⟩
  rcases w with ⟨y, Q⟩
  have hPQ : P.val.val = Q.val.val := congrArg Subtype.val h
  let vx := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  let vy := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C y)
  letI : (Ideal.span {X - C x}).IsMaximal := vx.isPrime.isMaximal vx.ne_bot
  letI : (Ideal.span {X - C y}).IsMaximal := vy.isPrime.isMaximal vy.ne_bot
  have hx0 : (Ideal.span {X - C x}) ≠ ⊥ := vx.ne_bot
  have hy0 : (Ideal.span {X - C y}) ≠ ⊥ := vy.ne_bot
  have hPx := ((IsDedekindDomain.mem_primesOverFinset_iff hx0 B).mp P.val.property).2
  have hQy := ((IsDedekindDomain.mem_primesOverFinset_iff hy0 B).mp Q.val.property).2
  have hPy : P.val.val.LiesOver (Ideal.span {X - C y}) := hPQ.symm ▸ hQy
  letI := hPx
  letI := hPy
  have hxy := linearPlace_liesOver_unique P.val.val x y
  cases hxy
  exact congrArg (Sigma.mk x) (Subtype.ext (Subtype.ext hPQ))

private theorem fiberToPrime_surjective : Function.Surjective (rationalPolynomialPrimeFiberToPrime K B) := by
  intro P
  letI := P.property.1
  obtain ⟨x, hx⟩ := prime_liesOver_linear_of_residue_surjective P.val P.property.2
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  letI : (Ideal.span {X - C x}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C x}) ≠ ⊥ := v.ne_bot
  have hm := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mpr ⟨P.property.1, hx⟩
  exact ⟨⟨x, ⟨⟨P.val, hm⟩, P.property.2⟩⟩, Subtype.ext rfl⟩

/-- Rational normalization primes are the disjoint union of the rational parts of all linear fibers. -/
def rationalPolynomialPrimeFiberEquiv :
    ((x : K) × RationalPolynomialPrimeFiber K B x) ≃ RationalPolynomialPrimes K B :=
  Equiv.ofBijective (rationalPolynomialPrimeFiberToPrime K B)
    ⟨fiberToPrime_injective K B, fiberToPrime_surjective K B⟩

/-- A finite constant field leaves only finitely many rational normalization primes. -/
instance rationalPolynomialPrimes_finite [Finite K] : Finite (RationalPolynomialPrimes K B) :=
  Finite.of_equiv ((x : K) × RationalPolynomialPrimeFiber K B x)
    (rationalPolynomialPrimeFiberEquiv K B)

/-- The rational prime count is the sum of the rational linear-fiber counts. -/
theorem rationalPolynomialPrimes_card [Fintype K] :
    Nat.card (RationalPolynomialPrimes K B) = ∑ x : K, Nat.card (RationalPolynomialPrimeFiber K B x) := by
  rw [← Nat.card_congr (rationalPolynomialPrimeFiberEquiv K B), Nat.card_sigma]

/-- Rational prime ideals and rational height-one normalization places are equivalent. -/
def rationalPolynomialPrimeHeightOneEquiv :
    RationalPolynomialPrimes K B ≃
      {w : HeightOneSpectrum B // Function.Surjective (algebraMap K (B ⧸ w.asIdeal))} where
  toFun P := ⟨⟨P.val, P.property.1, rationalPolynomialPrime_ne_bot K B P⟩, P.property.2⟩
  invFun w := ⟨w.val.asIdeal, w.val.isPrime, w.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (HeightOneSpectrum.ext rfl)

/-- If every prime of a linear fiber has constant residue, its rational part is the entire fiber. -/
def rationalPolynomialPrimeFiberEquivAll (x : K)
    (hall : ∀ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {X - C x}) B,
      Function.Surjective (algebraMap K (B ⧸ P))) :
    RationalPolynomialPrimeFiber K B x ≃
      {P : Ideal B // P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {X - C x}) B} :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun P => ⟨⟨P, hall P.val P.property⟩, rfl⟩⟩

omit [IsScalarTower K K[X] B] [Module.IsTorsionFree K[X] B] in
/-- A wholly rational linear fiber has the cardinality of the full normalization prime set. -/
theorem rationalPolynomialPrimeFiber_card_of_all (x : K)
    (hall : ∀ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {X - C x}) B,
      Function.Surjective (algebraMap K (B ⧸ P))) :
    Nat.card (RationalPolynomialPrimeFiber K B x) =
      (IsDedekindDomain.primesOverFinset (Ideal.span {X - C x}) B).card := by
  rw [Nat.card_congr (rationalPolynomialPrimeFiberEquivAll K B x hall), Nat.card_eq_finsetCard]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

