import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalConstantPlaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalChartCount

/-!
# Exact intrinsic rational-place count

The explicit finite prime set and a singleton at infinity are equivalent
to all proper constant-field valuation rings with constant residue field.
This transfers the exact chart count to an intrinsic count of places.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)

/-- Intrinsic rational places of the normalized prime-power Kummer function field. -/
abbrev NormalizedKummerRationalPlaces :=
  RationalConstantFieldPlaces (SquareConstantField p (kummerSquareIndex d n))
    (NormalizedKummerField p (kummerSquareIndex d n) d r)

/-- A prime in the explicit rational prime set is an actual height-one normalization place. -/
def normalizedKummerRationalPrimeHeightOne
    (P : {P // P ∈ normalizedKummerRationalPrimes p d n r}) :
    HeightOneSpectrum (NormalizedKummerNormalization p (kummerSquareIndex d n) d r) := by
  have hp := (mem_normalizedKummerRationalPrimes_iff p d n r P.val).mp P.property
  letI := hp.1
  exact ⟨P.val, hp.1, squareKummer_rationalPrime_ne_bot p (kummerSquareIndex d n) _ _ _ P.val hp.2⟩

/-- The intrinsic rational place associated with an explicitly counted finite normalization prime. -/
def normalizedKummerRationalPrimeToPlace
    (P : {P // P ∈ normalizedKummerRationalPrimes p d n r}) :
    NormalizedKummerRationalPlaces p d n r :=
  squareKummerRationalFinitePlace p (kummerSquareIndex d n)
    ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1)) d (r + 1)
    (normalizedKummerRationalPrimeHeightOne p d n r P)
    (((mem_normalizedKummerRationalPrimes_iff p d n r P.val).mp P.property).2)

/-- Distinct counted normalization primes remain distinct as intrinsic places. -/
theorem normalizedKummerRationalPrimeToPlace_injective :
    Function.Injective (normalizedKummerRationalPrimeToPlace p d n r) := by
  intro P Q h
  have hw := squareKummerFiniteConstantPlace_injective p (kummerSquareIndex d n)
    ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1)) d (r + 1)
    (congrArg Subtype.val h)
  exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal hw)

/-- Enumerating intrinsic rational places by finite rational primes and the unique infinity place. -/
def normalizedKummerRationalPlaceMap :
    ({P // P ∈ normalizedKummerRationalPrimes p d n r} ⊕ PUnit.{1}) →
      NormalizedKummerRationalPlaces p d n r :=
  Sum.elim (normalizedKummerRationalPrimeToPlace p d n r)
    (fun _ => squareKummerRationalInfinityPlace p (kummerSquareIndex d n)
      ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1)) d (r + 1))

/-- The explicit enumeration contains no repeated intrinsic place. -/
theorem normalizedKummerRationalPlaceMap_injective :
    Function.Injective (normalizedKummerRationalPlaceMap p d n r) := by
  intro x y h
  cases x with
  | inl P =>
    cases y with
    | inl Q => exact congrArg Sum.inl (normalizedKummerRationalPrimeToPlace_injective p d n r h)
    | inr u =>
      exact (squareKummerFiniteConstantPlace_ne_infinity p (kummerSquareIndex d n) _ d (r + 1)
        (normalizedKummerRationalPrimeHeightOne p d n r P) (congrArg Subtype.val h)).elim
  | inr u =>
    cases y with
    | inl Q =>
      exact (squareKummerFiniteConstantPlace_ne_infinity p (kummerSquareIndex d n) _ d (r + 1)
        (normalizedKummerRationalPrimeHeightOne p d n r Q) (congrArg Subtype.val h.symm)).elim
    | inr v => exact congrArg Sum.inr (Subsingleton.elim u v)

/-- Every intrinsic rational place occurs in the explicit enumeration. -/
theorem normalizedKummerRationalPlaceMap_surjective :
    Function.Surjective (normalizedKummerRationalPlaceMap p d n r) := by
  intro W
  rcases squareKummer_rationalPlace_cases p (kummerSquareIndex d n)
    ((kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1)) d (r + 1) W with
    ⟨w, hw, hW⟩ | hW
  · have hP := (mem_normalizedKummerRationalPrimes_iff p d n r w.asIdeal).mpr ⟨w.isPrime, hw⟩
    let P : {P // P ∈ normalizedKummerRationalPrimes p d n r} := ⟨w.asIdeal, hP⟩
    have he : normalizedKummerRationalPrimeHeightOne p d n r P = w := HeightOneSpectrum.ext rfl
    refine ⟨Sum.inl P, ?_⟩
    apply Subtype.ext
    change squareKummerFiniteConstantPlace p (kummerSquareIndex d n) _ d (r + 1)
      (normalizedKummerRationalPrimeHeightOne p d n r P) = W.val
    rw [he]
    exact congrArg Subtype.val hW
  · exact ⟨Sum.inr PUnit.unit, hW⟩

/-- The finite normalization primes and infinity classify the intrinsic rational places exactly. -/
def normalizedKummerRationalPlaceEquiv :
    ({P // P ∈ normalizedKummerRationalPrimes p d n r} ⊕ PUnit.{1}) ≃
      NormalizedKummerRationalPlaces p d n r :=
  Equiv.ofBijective (normalizedKummerRationalPlaceMap p d n r)
    ⟨normalizedKummerRationalPlaceMap_injective p d n r,
      normalizedKummerRationalPlaceMap_surjective p d n r⟩

/-- The intrinsic rational place count equals the count in the two normalization charts. -/
theorem normalizedKummerRationalPlaces_card_eq_charts :
    Nat.card (NormalizedKummerRationalPlaces p d n r) =
      Nat.card (normalizedKummerRationalChartPlaces p d n r) := by
  rw [← Nat.card_congr (normalizedKummerRationalPlaceEquiv p d n r), Nat.card_sum,
    Nat.card_eq_finsetCard, Nat.card_unique, normalizedKummerRationalPrimes_card,
    kummerOrdinateParameters_primePower_card, normalizedKummerRationalChartPlaces_card]

/-- The exact intrinsic rational place count, obtained from actual valuation rings and their residue fields. -/
theorem normalizedKummerRationalPlaces_card :
    Nat.card (NormalizedKummerRationalPlaces p d n r) =
      (p ^ (kummerSquareIndex d n + 1)) ^ 2 + 1 +
        (p ^ (d + 1) - 1) * p ^ (kummerSquareIndex d n + 1) *
          (p ^ (kummerSquareIndex d n + 1) + 1 -
            Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
              (kummerExponent (p ^ (d + 1)) (r + 1))) := by
  rw [normalizedKummerRationalPlaces_card_eq_charts, normalizedKummerRationalChartPlaces_card_closed]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
