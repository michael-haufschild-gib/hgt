import GaloisForLFunctions.RHTower.DeningerQ8ActualTwoAdicNormSelector
import GaloisForLFunctions.RHTower.DeningerQ8ActualBiquadraticOddRamification
import GaloisForLFunctions.HTGeometry.UnramifiedAwayFromDerivative

/-!
# Exact finite ramification support of the literal Q8 field

The top quadratic generator `z` has integral minimal polynomial
`X² - δ`, whose derivative is `2z`.  The different therefore puts every
relative ramified prime in the support of `2z`.  The literal source identity

`((u+2)(35+12v))((3-u)(47-12v)) = 1025 = 5²·41`

then restricts the rational support to `2`, `5`, and `41`.  Combining this
with exact discriminant support of the maximal abelian subfield proves the
same support inclusion for the full top field over `ℚ`.
-/

set_option maxHeartbeats 1600000

namespace RHTower

open scoped NumberField
open Polynomial

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
local instance : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective

noncomputable local instance : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_firstQuadratic_irreducible.ne_zero).basis
noncomputable local instance : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero).basis
noncomputable local instance : FiniteDimensional ℚ K2 :=
  FiniteDimensional.trans ℚ K1 K2
noncomputable local instance : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance : NumberField K2 := NumberField.mk
noncomputable local instance : NumberField K3 := NumberField.mk

theorem q8LiteralTwoAdic_branchFactor_mul_conjugate :
    ((q8LiteralTwoAdicU + 2) * (35 + 12 * q8LiteralTwoAdicV)) *
        ((3 - q8LiteralTwoAdicU) * (47 - 12 * q8LiteralTwoAdicV)) = 1025 := by
  have hu : (q8LiteralTwoAdicU + 2) * (3 - q8LiteralTwoAdicU) = 5 := by
    calc
      (q8LiteralTwoAdicU + 2) * (3 - q8LiteralTwoAdicU) =
          6 + q8LiteralTwoAdicU - q8LiteralTwoAdicU ^ 2 := by ring
      _ = 5 := by rw [q8LiteralTwoAdicU_sq]; ring
  have hv : (35 + 12 * q8LiteralTwoAdicV) *
      (47 - 12 * q8LiteralTwoAdicV) = 205 := by
    calc
      (35 + 12 * q8LiteralTwoAdicV) * (47 - 12 * q8LiteralTwoAdicV) =
          1645 + 144 * q8LiteralTwoAdicV - 144 * q8LiteralTwoAdicV ^ 2 := by ring
      _ = 205 := by rw [q8LiteralTwoAdicV_sq]; ring
  calc
    ((q8LiteralTwoAdicU + 2) * (35 + 12 * q8LiteralTwoAdicV)) *
        ((3 - q8LiteralTwoAdicU) * (47 - 12 * q8LiteralTwoAdicV)) =
      ((q8LiteralTwoAdicU + 2) * (3 - q8LiteralTwoAdicU)) *
        ((35 + 12 * q8LiteralTwoAdicV) * (47 - 12 * q8LiteralTwoAdicV)) := by ring
    _ = 1025 := by rw [hu, hv]; norm_num

theorem q8Literal_prime_dvd_1025_of_two_mul_topRoot_mem
    (p : ℕ) (P : Ideal (𝓞 K3)) [P.IsPrime]
    (hPover : P.LiesOver (Ideal.span {(p : ℤ)}))
    (h2 : (2 : 𝓞 K3) ∉ P)
    (hderiv : (2 : 𝓞 K3) * q8LiteralTwoAdicZ ∈ P) :
    p ∣ 1025 := by
  have hz : q8LiteralTwoAdicZ ∈ P := by
    exact ((inferInstance : P.IsPrime).mem_or_mem hderiv).resolve_left h2
  have hzsq : q8LiteralTwoAdicZ ^ 2 ∈ P := P.pow_mem_of_mem hz 2 (by norm_num)
  rw [q8LiteralTwoAdicZ_sq] at hzsq
  have hb : (q8LiteralTwoAdicU + 2) * (35 + 12 * q8LiteralTwoAdicV) ∈ P := by
    have hzsq' : (2 : 𝓞 K3) *
        ((q8LiteralTwoAdicU + 2) * (35 + 12 * q8LiteralTwoAdicV)) ∈ P := by
      simpa [mul_assoc] using hzsq
    exact ((inferInstance : P.IsPrime).mem_or_mem hzsq').resolve_left h2
  have h1025top : (1025 : 𝓞 K3) ∈ P := by
    rw [← q8LiteralTwoAdic_branchFactor_mul_conjugate]
    exact P.mul_mem_right _ hb
  have h1025base : (1025 : ℤ) ∈ Ideal.span {(p : ℤ)} := by
    letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover
    exact (Ideal.mem_of_liesOver (P := P) (Ideal.span {(p : ℤ)}) (1025 : ℤ)).mpr h1025top
  rw [Ideal.mem_span_singleton] at h1025base
  exact_mod_cast h1025base

theorem q8Literal_prime_eq_two_or_five_or_fortyOne_of_two_mul_topRoot_mem
    (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K3)) [P.IsPrime]
    (hPover : P.LiesOver (Ideal.span {(p : ℤ)}))
    (hderiv : (2 : 𝓞 K3) * q8LiteralTwoAdicZ ∈ P) :
    p = 2 ∨ p = 5 ∨ p = 41 := by
  by_cases h2 : (2 : 𝓞 K3) ∈ P
  · have h2base : (2 : ℤ) ∈ Ideal.span {(p : ℤ)} := by
      letI : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover
      exact (Ideal.mem_of_liesOver (P := P) (Ideal.span {(p : ℤ)}) (2 : ℤ)).mpr h2
    rw [Ideal.mem_span_singleton] at h2base
    have hp2 : p ∣ 2 := by exact_mod_cast h2base
    exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left hp.ne_one)
  · have hpd : p ∣ 1025 :=
      q8Literal_prime_dvd_1025_of_two_mul_topRoot_mem p P hPover h2 hderiv
    have hfactor : (1025 : ℕ) = 5 ^ 2 * 41 := by norm_num
    rw [hfactor] at hpd
    rcases (hp.dvd_mul).mp hpd with h5 | h41
    · right; left
      obtain ⟨k, hk, hpk⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp h5
      interval_cases k
      · norm_num at hpk
        exact (hp.ne_one hpk).elim
      · simpa using hpk
      · norm_num at hpk
        subst p
        norm_num at hp
    · right; right
      exact (Nat.dvd_prime (by norm_num : Nat.Prime 41)).mp h41 |>.resolve_left hp.ne_one

noncomputable def q8LiteralTopMinpolyCandidate : (𝓞 K2)[X] :=
  Polynomial.X ^ 2 - Polynomial.C q8BiquadTwoAdicRadicand

theorem q8LiteralTopMinpolyCandidate_monic : q8LiteralTopMinpolyCandidate.Monic := by
  exact Polynomial.monic_X_pow_sub_C q8BiquadTwoAdicRadicand (by norm_num : 2 ≠ 0)

theorem q8LiteralTopMinpolyCandidate_map :
    q8LiteralTopMinpolyCandidate.map (algebraMap (𝓞 K2) K2) =
      deningerQ8RootNumberNegOneThirdQuadraticPolynomial := by
  simp [q8LiteralTopMinpolyCandidate,
    deningerQ8RootNumberNegOneThirdQuadraticPolynomial,
    q8BiquadTwoAdicRadicand_eq_topRadicand]

theorem q8LiteralTopMinpolyCandidate_irreducible :
    Irreducible q8LiteralTopMinpolyCandidate := by
  apply q8LiteralTopMinpolyCandidate_monic.irreducible_of_irreducible_map
    (algebraMap (𝓞 K2) K2)
  rw [q8LiteralTopMinpolyCandidate_map]
  exact deningerQ8RootNumberNegOne_thirdQuadratic_irreducible

theorem q8BiquadTwoAdicU_map_top :
    algebraMap (𝓞 K2) (𝓞 K3) q8BiquadTwoAdicU = q8LiteralTwoAdicU := by
  apply Subtype.ext
  change algebraMap K2 K3 (algebraMap K1 K2 q8BiquadU) = q8LiteralTwoAdicUField
  simp [q8BiquadU, q8LiteralTwoAdicUField,
    deningerQ8RootNumberNegOneTopX]
  congr 1

theorem q8BiquadTwoAdicV_map_top :
    algebraMap (𝓞 K2) (𝓞 K3) q8BiquadTwoAdicV = q8LiteralTwoAdicV := by
  apply Subtype.ext
  change algebraMap K2 K3 q8BiquadV = q8LiteralTwoAdicVField
  simp [q8BiquadV, q8LiteralTwoAdicVField,
    deningerQ8RootNumberNegOneTopY]
  rw [map_ofNat]

theorem q8LiteralTopMinpolyCandidate_aeval :
    Polynomial.aeval q8LiteralTwoAdicZ q8LiteralTopMinpolyCandidate = 0 := by
  rw [show Polynomial.aeval q8LiteralTwoAdicZ q8LiteralTopMinpolyCandidate =
      q8LiteralTwoAdicZ ^ 2 -
        algebraMap (𝓞 K2) (𝓞 K3) q8BiquadTwoAdicRadicand by
      simp [q8LiteralTopMinpolyCandidate]]
  rw [q8LiteralTwoAdicZ_sq]
  simp only [q8BiquadTwoAdicRadicand, map_mul, map_add, map_ofNat,
    q8BiquadTwoAdicU_map_top, q8BiquadTwoAdicV_map_top]
  ring

theorem q8LiteralTopMinpolyCandidate_derivative :
    Polynomial.derivative q8LiteralTopMinpolyCandidate =
      Polynomial.C (2 : 𝓞 K2) * Polynomial.X := by
  simp [q8LiteralTopMinpolyCandidate, one_add_one_eq_two]

theorem q8LiteralTwoAdicZ_minpoly :
    minpoly (𝓞 K2) q8LiteralTwoAdicZ = q8LiteralTopMinpolyCandidate := by
  apply Polynomial.map_injective (algebraMap (𝓞 K2) K2)
    (IsFractionRing.injective (𝓞 K2) K2)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions K2 K3
    (Algebra.IsIntegral.isIntegral q8LiteralTwoAdicZ)]
  rw [q8LiteralTopMinpolyCandidate_map]
  symm
  exact minpoly.eq_of_irreducible_of_monic
    deningerQ8RootNumberNegOne_thirdQuadratic_irreducible
    (by
      change deningerQ8RootNumberNegOneThirdQuadraticPolynomial.eval₂
        (algebraMap K2 K3) deningerQ8RootNumberNegOneTopRoot = 0
      exact AdjoinRoot.eval₂_root
        deningerQ8RootNumberNegOneThirdQuadraticPolynomial)
    (by
      simpa [deningerQ8RootNumberNegOneThirdQuadraticPolynomial] using
        (Polynomial.monic_X_pow_sub_C
          deningerQ8RootNumberNegOneTopRadicand (by norm_num : 2 ≠ 0)))

theorem q8LiteralTwoAdicZ_aeval_derivative_minpoly :
    Polynomial.aeval q8LiteralTwoAdicZ
      (Polynomial.derivative (minpoly (𝓞 K2) q8LiteralTwoAdicZ)) =
        2 * q8LiteralTwoAdicZ := by
  rw [q8LiteralTwoAdicZ_minpoly]
  rw [q8LiteralTopMinpolyCandidate_derivative]
  simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
  rw [map_ofNat]

theorem q8LiteralTwoAdicZ_generates_top_fraction_field :
    Algebra.adjoin K2
      ({algebraMap (𝓞 K3) K3 q8LiteralTwoAdicZ} : Set K3) = ⊤ := by
  change Algebra.adjoin K2
      ({deningerQ8RootNumberNegOneTopRoot} : Set K3) = ⊤
  exact AdjoinRoot.adjoinRoot_eq_top

theorem q8Literal_two_mul_topRoot_mem_of_relative_ramified
    (P : Ideal (𝓞 K3)) [P.IsPrime]
    (hP : ¬ Algebra.IsUnramifiedAt (𝓞 K2) P) :
    (2 : 𝓞 K3) * q8LiteralTwoAdicZ ∈ P := by
  have hdvd : P ∣ differentIdeal (𝓞 K2) (𝓞 K3) :=
    dvd_differentIdeal_iff.mpr hP
  have hdiff : Polynomial.aeval q8LiteralTwoAdicZ
      (Polynomial.derivative (minpoly (𝓞 K2) q8LiteralTwoAdicZ)) ∈
        differentIdeal (𝓞 K2) (𝓞 K3) :=
    aeval_derivative_mem_differentIdeal (𝓞 K2) K2 K3
      q8LiteralTwoAdicZ q8LiteralTwoAdicZ_generates_top_fraction_field
  have hmem := (Ideal.dvd_iff_le.mp hdvd) hdiff
  rwa [q8LiteralTwoAdicZ_aeval_derivative_minpoly] at hmem

theorem q8Literal_relative_ramified_prime_support
    (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K3)) [P.IsPrime]
    (hPover : P.LiesOver (Ideal.span {(p : ℤ)}))
    (hP : ¬ Algebra.IsUnramifiedAt (𝓞 K2) P) :
    p = 2 ∨ p = 5 ∨ p = 41 := by
  exact q8Literal_prime_eq_two_or_five_or_fortyOne_of_two_mul_topRoot_mem
    p hp P hPover (q8Literal_two_mul_topRoot_mem_of_relative_ramified P hP)

/-- Every rational prime ramified in the literal Q8 top field is `2`, `5`, or `41`. -/
theorem q8Literal_absolute_ramified_prime_support
    (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K3)) [P.IsPrime]
    (hPover : P.LiesOver (Ideal.span {(p : ℤ)}))
    (hP : ¬ Algebra.IsUnramifiedAt ℤ P) :
    p = 2 ∨ p = 5 ∨ p = 41 := by
  by_contra hsupp
  push Not at hsupp
  let p0 : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hpInt : Prime (p : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  haveI hp0Prime : p0.IsPrime := by
    dsimp [p0]
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact hpInt
  letI hPover0 : P.LiesOver p0 := hPover
  have hpIntNe : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp0bot : p0 ≠ ⊥ := by simpa [p0] using hpIntNe
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0bot P
  let Q : Ideal (𝓞 K2) := P.under (𝓞 K2)
  have hQbot : Q ≠ ⊥ := Ideal.under_ne_bot (𝓞 K2) hPbot
  haveI hQPrime : Q.IsPrime := Ideal.IsPrime.under (𝓞 K2) P
  haveI hQMax : Q.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hQbot hQPrime
  haveI hQover : Q.LiesOver p0 := by
    dsimp [Q]
    exact Ideal.under_liesOver_of_liesOver (𝓞 K2) P p0
  have hbase : Algebra.IsUnramifiedAt ℤ Q := by
    have hnotdvd : ¬ (p : ℤ) ∣ NumberField.discr K2 := by
      intro hdvd
      rcases (q8Biquad_prime_dvd_discr_iff p hp).mp hdvd with h5 | h41
      · exact hsupp.2.1 h5
      · exact hsupp.2.2 h41
    exact (NumberField.not_dvd_discr_iff_forall_liesOver K2 (𝓞 K2) hpInt).mp
      hnotdvd Q hQMax hQover
  have hrelative : Algebra.IsUnramifiedAt (𝓞 K2) P := by
    by_contra hram
    rcases q8Literal_relative_ramified_prime_support p hp P hPover hram with
      h2 | h5 | h41
    · exact hsupp.1 h2
    · exact hsupp.2.1 h5
    · exact hsupp.2.2 h41
  letI : P.LiesOver Q := Ideal.over_under P
  letI : Algebra.IsUnramifiedAt ℤ Q := hbase
  letI : Algebra.IsUnramifiedAt (𝓞 K2) P := hrelative
  exact hP (Algebra.IsUnramifiedAt.comp Q P)

end

end RHTower
