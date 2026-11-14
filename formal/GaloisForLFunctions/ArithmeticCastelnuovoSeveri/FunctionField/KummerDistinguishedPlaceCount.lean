import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerBranchSplitting
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityPlace

/-!
# Distinguished places of the prime-power Kummer family

The nonzero auxiliary-field fibers are disjoint and each contains
`gcd(Q+1,R)` actual normalization primes. Adding the unique origin
prime and the unique prime in the infinity chart gives
`2+(q-1) gcd(Q+1,R)` places above the auxiliary projective line.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis

/-- Distinct scalar coordinates define distinct linear polynomial ideals. -/
theorem polynomial_linearIdeal_injective {K : Type*} [Field K] :
    Function.Injective (fun a : K => Ideal.span {X - C a}) := by
  intro a b hab
  change Ideal.span {X - C a} = Ideal.span {X - C b} at hab
  have hm : X - C b ∈ Ideal.span {X - C a} := by
    rw [hab]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hm
  have hroot : (X - C b).eval a = 0 := by
    rw [hg, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  simpa only [eval_sub, eval_X, eval_C, sub_eq_zero] using hroot

/-- An ideal in an extension cannot lie above two different rational base points. -/
theorem linearPlace_liesOver_unique {K B : Type*} [Field K] [CommRing B] [Algebra K[X] B]
    (P : Ideal B) (a b : K)
    [P.LiesOver (Ideal.span {X - C a})] [P.LiesOver (Ideal.span {X - C b})] : a = b := by
  apply polynomial_linearIdeal_injective
  exact ((Ideal.liesOver_iff P (Ideal.span {X - C a})).mp inferInstance).trans
    ((Ideal.liesOver_iff P (Ideal.span {X - C b})).mp inferInstance).symm

/-- Prime fibers over distinct rational coordinates are disjoint in the normalization. -/
theorem squareKummer_linearPrimeFibers_disjoint
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (a a' : SquareConstantField p s) (haa' : a ≠ a') :
    Disjoint (IsDedekindDomain.primesOverFinset (Ideal.span {X - C a})
      (SquareKummerNormalization p s c b R))
      (IsDedekindDomain.primesOverFinset (Ideal.span {X - C a'})
        (SquareKummerNormalization p s c b R)) := by
  classical
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
  let v' := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a')
  letI : (Ideal.span {X - C a}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : (Ideal.span {X - C a'}).IsMaximal := v'.isPrime.isMaximal v'.ne_bot
  apply Finset.disjoint_left.mpr
  intro P hP hP'
  obtain ⟨_, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff
    (show (Ideal.span {X - C a}) ≠ ⊥ from v.ne_bot) _).mp hP
  obtain ⟨_, hover'⟩ := (IsDedekindDomain.mem_primesOverFinset_iff
    (show (Ideal.span {X - C a'}) ≠ ⊥ from v'.ne_bot) _).mp hP'
  letI := hover
  letI := hover'
  exact haa' (linearPlace_liesOver_unique P a a')

variable (p : ℕ) [Fact p.Prime] (d n R : ℕ)
    (η : (SquareConstantField p (kummerSquareIndex d n))ˣ)

/-- The nonzero auxiliary field has `q-1` elements for the prime-power family. -/
theorem kummerAuxiliaryUnits_card :
    Nat.card (KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1))ˣ = p ^ (d + 1) - 1 := by
  rw [Nat.card_units, kummerAuxiliaryField_card, kummerSquareIndex_succ,
    Nat.gcd_eq_right (show d + 1 ∣ 2 * ((d + 1) * (n + 1)) from ⟨2 * (n + 1), by ring⟩)]

/-- The actual normalization primes over all nonzero auxiliary-field coordinates. -/
def squareKummerNonzeroBranchPrimes :
    Finset (Ideal (SquareKummerNormalization p (kummerSquareIndex d n)
      ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R)) := by
  classical
  letI : Fintype (KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1))ˣ := Fintype.ofFinite _
  exact Finset.univ.biUnion fun a : (KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1))ˣ =>
    IsDedekindDomain.primesOverFinset
    (Ideal.span {X - C ((a : KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1)) :
      SquareConstantField p (kummerSquareIndex d n))})
    (SquareKummerNormalization p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R)

/-- Nonzero auxiliary-field fibers contain exactly `(q-1) gcd(Q+1,R)` distinct normalization primes. -/
theorem squareKummerNonzeroBranchPrimes_card :
    (squareKummerNonzeroBranchPrimes p d n R η).card =
      (p ^ (d + 1) - 1) * Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1) R := by
  classical
  letI : Fintype (KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1))ˣ := Fintype.ofFinite _
  unfold squareKummerNonzeroBranchPrimes
  rw [Finset.card_biUnion]
  · simp only [squareKummer_primePowerBranch_primes_card, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.cast_id, ← Nat.card_eq_fintype_card, kummerAuxiliaryUnits_card]
  · intro a _ a' _ haa'
    apply squareKummer_linearPrimeFibers_disjoint
    intro h
    exact haa' (Units.ext (Subtype.ext h))

/-- The origin prime is distinct from every prime above a nonzero auxiliary-field coordinate. -/
theorem squareKummerOrigin_notMem_nonzeroBranchPrimes :
    squareKummerOriginIdeal p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R ∉
      squareKummerNonzeroBranchPrimes p d n R η := by
  classical
  intro h
  unfold squareKummerNonzeroBranchPrimes at h
  obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp h
  let α : SquareConstantField p (kummerSquareIndex d n) := a
  let P := squareKummerOriginIdeal p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C α)
  letI : (Ideal.span {X - C α}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  obtain ⟨_, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff
    (show (Ideal.span {X - C α}) ≠ ⊥ from v.ne_bot) _).mp ha
  letI := hover
  letI : P.LiesOver (Ideal.span {X - C (0 : SquareConstantField p (kummerSquareIndex d n))}) := by
    simpa only [map_zero, sub_zero] using
      (squareKummerOriginIdeal_liesOver p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R)
  exact Units.ne_zero a (Subtype.ext (linearPlace_liesOver_unique P 0 α).symm)

/-- The actual finite normalization primes above the auxiliary-field coordinates. -/
def squareKummerFiniteBranchPrimes :
    Finset (Ideal (SquareKummerNormalization p (kummerSquareIndex d n)
      ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R)) := by
  classical
  exact insert (squareKummerOriginIdeal p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R)
    (squareKummerNonzeroBranchPrimes p d n R η)

/-- Finite auxiliary-field fibers contain exactly `1+(q-1) gcd(Q+1,R)` normalization primes. -/
theorem squareKummerFiniteBranchPrimes_card :
    (squareKummerFiniteBranchPrimes p d n R η).card =
      (p ^ (d + 1) - 1) * Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1) R + 1 := by
  classical
  rw [squareKummerFiniteBranchPrimes,
    Finset.card_insert_of_notMem (squareKummerOrigin_notMem_nonzeroBranchPrimes p d n R η),
    squareKummerNonzeroBranchPrimes_card]

/-- The finite auxiliary-field fibers together with the actual prime fiber at infinity. -/
def primePowerKummerDistinguishedPlaces (r : ℕ) : Type :=
  {P // P ∈ squareKummerFiniteBranchPrimes p d n (kummerExponent (p ^ (d + 1)) (r + 1)) η} ⊕
    {P : Ideal (SquareKummerInfinityNormalization p (kummerSquareIndex d n)
        ((η⁻¹) ^ kummerExponent (p ^ (d + 1)) (r + 1)) (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) (r + 1))) //
      P.IsPrime ∧ P.LiesOver (Ideal.span {(X : (SquareConstantField p (kummerSquareIndex d n))[X])})}

/-- The two actual normalization charts contribute `2+(q-1) gcd(Q+1,R)` distinguished places. -/
theorem primePowerKummerDistinguishedPlaces_card (r : ℕ) :
    Nat.card (primePowerKummerDistinguishedPlaces p d n η r) =
      2 + (p ^ (d + 1) - 1) * Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1)
        (kummerExponent (p ^ (d + 1)) (r + 1)) := by
  classical
  let I := {P : Ideal (SquareKummerInfinityNormalization p (kummerSquareIndex d n)
        ((η⁻¹) ^ kummerExponent (p ^ (d + 1)) (r + 1)) (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) (r + 1))) //
      P.IsPrime ∧ P.LiesOver (Ideal.span {(X : (SquareConstantField p (kummerSquareIndex d n))[X])})}
  obtain ⟨P, hP, huniq⟩ := squareKummerInfinity_unique p (kummerSquareIndex d n)
    ((η⁻¹) ^ kummerExponent (p ^ (d + 1)) (r + 1)) d (r + 1)
  letI : Unique I := { default := ⟨P, hP⟩, uniq := fun Q => Subtype.ext (huniq Q.val Q.property) }
  have hI : Nat.card I = 1 := Nat.card_unique
  change Nat.card (_ ⊕ I) = _
  rw [Nat.card_sum, Nat.card_eq_finsetCard, squareKummerFiniteBranchPrimes_card, hI]
  omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
