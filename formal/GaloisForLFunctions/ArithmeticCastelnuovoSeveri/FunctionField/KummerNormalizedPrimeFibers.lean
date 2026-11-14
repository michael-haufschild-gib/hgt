import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerUnramifiedSplitting
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDistinguishedPlaceCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerOrdinateReconstruction

/-!
# Normalization primes over the constructed Kummer ordinates

Each trace or signed-Frobenius ordinate has a nonzero soluble norm fiber.
Complete splitting gives `Q+1` rational normalization primes above it.
Injectivity of the ordinate parametrization makes these prime fibers
disjoint and turns their union into an exact finite count.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s d r : ℕ)

/-- The function field of the normalized trace-constant Kummer equation. -/
abbrev NormalizedKummerField := SquareKummerField p s
  ((kummerTraceConstant p s)⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
  (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))

/-- The integral closure of the affine coordinate ring in the normalized Kummer field. -/
abbrev NormalizedKummerNormalization := SquareKummerNormalization p s
  ((kummerTraceConstant p s)⁻¹ ^ kummerExponent (p ^ (d + 1)) (r + 1))
  (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) (r + 1))

/-- The actual normalization prime fiber above one constructed ordinate. -/
def kummerConstructedPrimeFiber (i : KummerOrdinateParameters p s d r) :
    Finset (Ideal (NormalizedKummerNormalization p s d r)) :=
  IsDedekindDomain.primesOverFinset (Ideal.span {X - C (kummerConstructedOrdinate p s d r i)})
    (NormalizedKummerNormalization p s d r)

/-- Every constructed ordinate splits into exactly `Q+1` normalization primes. -/
theorem kummerConstructedPrimeFiber_card (i : KummerOrdinateParameters p s d r) :
    (kummerConstructedPrimeFiber p s d r i).card = p ^ (s + 1) + 1 := by
  obtain ⟨β, hβ⟩ := (squareConstantField_exists_norm_iff p s _).mpr
    (kummerConstructedOrdinate_branch_fixed p s d r i)
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.succ_ne_zero _)] at hβ
    exact kummerConstructedOrdinate_branch_ne_zero p s d r i hβ.symm
  exact squareKummer_unramified_split_primes_card p s _ _ _
    (kummerConstructedOrdinate p s d r i) β hβ0 hβ

/-- All constructed nonzero fibers form a finite set of actual normalization primes. -/
def kummerConstructedPrimes : Finset (Ideal (NormalizedKummerNormalization p s d r)) := by
  classical
  letI : Fintype (KummerOrdinateParameters p s d r) := Fintype.ofFinite _
  exact Finset.univ.biUnion (kummerConstructedPrimeFiber p s d r)

/-- Distinct ordinate parameters give disjoint normalization fibers. -/
theorem kummerConstructedPrimeFiber_disjoint (i j : KummerOrdinateParameters p s d r) (h : i ≠ j) :
    Disjoint (kummerConstructedPrimeFiber p s d r i) (kummerConstructedPrimeFiber p s d r j) :=
  squareKummer_linearPrimeFibers_disjoint p s _ _ _ _ _
    (fun hij => h (kummerConstructedOrdinate_injective p s d r hij))

/-- Counting constructed normalization primes multiplies the ordinate count by `Q+1`. -/
theorem kummerConstructedPrimes_card :
    (kummerConstructedPrimes p s d r).card =
      Nat.card (KummerOrdinateParameters p s d r) * (p ^ (s + 1) + 1) := by
  classical
  letI : Fintype (KummerOrdinateParameters p s d r) := Fintype.ofFinite _
  unfold kummerConstructedPrimes
  rw [Finset.card_biUnion]
  · simp only [kummerConstructedPrimeFiber_card, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.cast_id, Nat.card_eq_fintype_card]
  · intro i _ j _ hij
    exact kummerConstructedPrimeFiber_disjoint p s d r i j hij

/-- Membership in the constructed prime set is exactly lying above one of its ordinates. -/
theorem mem_kummerConstructedPrimes_iff (P : Ideal (NormalizedKummerNormalization p s d r)) :
    P ∈ kummerConstructedPrimes p s d r ↔ P.IsPrime ∧
      ∃ i : KummerOrdinateParameters p s d r,
        P.LiesOver (Ideal.span {X - C (kummerConstructedOrdinate p s d r i)}) := by
  classical
  letI : Fintype (KummerOrdinateParameters p s d r) := Fintype.ofFinite _
  unfold kummerConstructedPrimes
  constructor
  · intro hP
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hP
    let v := GaloisForLFunctions.HTGeometry.polyPlace
      (irreducible_X_sub_C (kummerConstructedOrdinate p s d r i))
    letI : (Ideal.span {X - C (kummerConstructedOrdinate p s d r i)}).IsMaximal :=
      v.isPrime.isMaximal v.ne_bot
    obtain ⟨hp, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff
      (show (Ideal.span {X - C (kummerConstructedOrdinate p s d r i)}) ≠ ⊥ from v.ne_bot) _).mp hi
    exact ⟨hp, i, hover⟩
  · rintro ⟨hp, i, hover⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    let v := GaloisForLFunctions.HTGeometry.polyPlace
      (irreducible_X_sub_C (kummerConstructedOrdinate p s d r i))
    letI : (Ideal.span {X - C (kummerConstructedOrdinate p s d r i)}).IsMaximal :=
      v.isPrime.isMaximal v.ne_bot
    exact (IsDedekindDomain.mem_primesOverFinset_iff
      (show (Ideal.span {X - C (kummerConstructedOrdinate p s d r i)}) ≠ ⊥ from v.ne_bot) _).mpr ⟨hp, hover⟩

/-- Every constructed normalization prime has only constant residues. -/
theorem kummerConstructedPrimes_rational (P : Ideal (NormalizedKummerNormalization p s d r))
    (hP : P ∈ kummerConstructedPrimes p s d r) :
    Function.Surjective (algebraMap (SquareConstantField p s) (NormalizedKummerNormalization p s d r ⧸ P)) := by
  obtain ⟨hp, i, hover⟩ := (mem_kummerConstructedPrimes_iff p s d r P).mp hP
  letI := hp
  letI := hover
  let v := GaloisForLFunctions.HTGeometry.polyPlace
    (irreducible_X_sub_C (kummerConstructedOrdinate p s d r i))
  let w : HeightOneSpectrum (NormalizedKummerNormalization p s d r) := ⟨P, hp,
    Ideal.ne_bot_of_liesOver_of_ne_bot
      (show (Ideal.span {X - C (kummerConstructedOrdinate p s d r i)}) ≠ ⊥ from v.ne_bot) P⟩
  apply squareKummer_rational_residue_surjective p s _ _ _ (kummerConstructedOrdinate p s d r i) w
  exact (squareKummer_nonzero_fiber_rational_iff_fixed p s _ _ _ _
    (kummerConstructedOrdinate_branch_ne_zero p s d r i) w).mpr
      (kummerConstructedOrdinate_branch_fixed p s d r i)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
