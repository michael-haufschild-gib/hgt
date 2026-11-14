import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDistinguishedPlaceCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalResidue

/-!
# Rationality and membership of distinguished finite primes

The explicit distinguished set consists exactly of normalization primes
above auxiliary-field coordinates. The origin is totally ramified with
residue degree one; every nonzero auxiliary-field fiber has constant residues.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (d n R : ℕ)
    (η : (SquareConstantField p (kummerSquareIndex d n))ˣ)

/-- The finite distinguished primes are exactly those above auxiliary-field coordinates. -/
theorem mem_squareKummerFiniteBranchPrimes_iff
    (P : Ideal (SquareKummerNormalization p (kummerSquareIndex d n)
      ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R)) :
    P ∈ squareKummerFiniteBranchPrimes p d n R η ↔ P.IsPrime ∧
      ∃ a : KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1),
        P.LiesOver (Ideal.span {X - C (a : SquareConstantField p (kummerSquareIndex d n))}) := by
  classical
  let K := SquareConstantField p (kummerSquareIndex d n)
  let A := KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1)
  letI : Fintype Aˣ := Fintype.ofFinite _
  let B := SquareKummerNormalization p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R
  rw [squareKummerFiniteBranchPrimes, Finset.mem_insert]
  constructor
  · rintro (rfl | hP)
    · refine ⟨inferInstance, 0, ?_⟩
      simpa only [ZeroMemClass.coe_zero, map_zero, sub_zero] using
        (squareKummerOriginIdeal_liesOver p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R)
    · unfold squareKummerNonzeroBranchPrimes at hP
      obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hP
      let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (a : K))
      letI : (Ideal.span {X - C (a : K)}).IsMaximal := v.isPrime.isMaximal v.ne_bot
      obtain ⟨hp, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff
        (show (Ideal.span {X - C (a : K)}) ≠ ⊥ from v.ne_bot) B).mp ha
      exact ⟨hp, a, hover⟩
  · rintro ⟨hp, a, hover⟩
    letI := hp
    letI := hover
    by_cases ha : a = 0
    · left
      have hzero : P.LiesOver (Ideal.span {(X : K[X])}) := by
        simpa only [ha, ZeroMemClass.coe_zero, map_zero, sub_zero] using hover
      obtain ⟨P₀, _, huniq⟩ := squareKummer_origin_unique p (kummerSquareIndex d n)
        ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R
      exact (huniq P ⟨hp, hzero⟩).trans (huniq _ ⟨inferInstance, inferInstance⟩).symm
    · right
      unfold squareKummerNonzeroBranchPrimes
      apply Finset.mem_biUnion.mpr
      refine ⟨Units.mk0 a ha, Finset.mem_univ _, ?_⟩
      let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (a : K))
      letI : (Ideal.span {X - C (a : K)}).IsMaximal := v.isPrime.isMaximal v.ne_bot
      exact (IsDedekindDomain.mem_primesOverFinset_iff
        (show (Ideal.span {X - C (a : K)}) ≠ ⊥ from v.ne_bot) B).mpr ⟨hp, hover⟩

/-- Every finite distinguished prime has residue field equal to the constants. -/
theorem squareKummerFiniteBranchPrimes_rational
    (P : Ideal (SquareKummerNormalization p (kummerSquareIndex d n)
      ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R))
    (hP : P ∈ squareKummerFiniteBranchPrimes p d n R η) :
    Function.Surjective (algebraMap (SquareConstantField p (kummerSquareIndex d n))
      (SquareKummerNormalization p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R ⧸ P)) := by
  obtain ⟨hp, a, hover⟩ := (mem_squareKummerFiniteBranchPrimes_iff p d n R η P).mp hP
  letI := hp
  letI := hover
  let K := SquareConstantField p (kummerSquareIndex d n)
  let B := SquareKummerNormalization p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (a : K))
  let w : HeightOneSpectrum B := ⟨P, hp,
    Ideal.ne_bot_of_liesOver_of_ne_bot (show (Ideal.span {X - C (a : K)}) ≠ ⊥ from v.ne_bot) P⟩
  apply squareKummer_rational_residue_surjective p (kummerSquareIndex d n)
    ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R (a : K) w
  by_cases ha : a = 0
  · have hover0 : P.LiesOver (Ideal.span {(X : K[X])}) := by
      simpa only [ha, ZeroMemClass.coe_zero, map_zero, sub_zero] using hover
    letI := hover0
    simpa only [ha, ZeroMemClass.coe_zero, map_zero, sub_zero] using
      (squareKummer_origin_inertia p (kummerSquareIndex d n) ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R P)
  · let u := Units.mk0 a ha
    letI : w.asIdeal.LiesOver (Ideal.span {X - C
        ((u : KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1)) : K)}) := hover
    exact squareKummer_primePowerBranch_inertia p d n R η u w

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
