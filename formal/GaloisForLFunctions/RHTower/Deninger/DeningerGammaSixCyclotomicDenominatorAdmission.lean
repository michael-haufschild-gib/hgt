import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittFiniteEvaluationBridge
import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixCriticalEdgeCofaceRigidity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# Gamma-six cyclotomic denominator admission and parity wall

For the honest complementary Gamma-six pair

`x_m = 6^m / (1 + 6^m)`, `y_m = 1 / (1 + 6^m)`,

this module proves the complete denominator-place classification.

* The generalized Fermat subsequence `1 + 6^(2^n)` is pairwise coprime.  Least prime factors
  therefore give an explicit injection from `ℕ` into honest denominator places, proving their
  infinitude without a primitive-divisor theorem.
* At every denominator prime, both rational entries have valuation `-e`, their ratio has valuation
  zero, its p-adic logarithm vanishes, and the literal tame symbol is one.
* Forward and reciprocal common-pole reductions are the same nonzero element `[-1] - [1]`.
  The corresponding order-two cyclotomic element is nonzero, evaluates to `-2`, embeds into the
  published complexified rational-Witt presentation, and is fixed by arithmetic Frobenius.
* The cofinal even layer is in `ℓ¹ ∩ ℓ²`; its two-slot Köthe refinement is nuclear.  The actual
  oriented normal pair has sharp mixed admission exactly on `|delta| < 1`, while its odd reader
  vanishes exactly at `delta = 0`.
* Every additive transport factoring through common-pole reduction annihilates the resolved odd
  denominator class.  Thus this nonzero finite layer cannot supply the missing signed Route-L
  differential.

All results are unconditional.  No Xi-zero location, RH premise, positivity premise, numerical
computation, or fitted coefficient map is used.
-/

open scoped BigOperators

namespace RHTower

def gammaSixFermatDenominator (n : ℕ) : ℕ := 6 ^ (2 ^ n) + 1

lemma gammaSixFermatDenominator_odd (n : ℕ) : Odd (gammaSixFermatDenominator n) := by
  rw [gammaSixFermatDenominator]
  exact (even_iff_two_dvd.mpr (dvd_pow (by norm_num : 2 ∣ 6)
    (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0)))).add_one

lemma gammaSixFermatDenominator_coprime {i j : ℕ} (hij : i < j) :
    Nat.Coprime (gammaSixFermatDenominator i) (gammaSixFermatDenominator j) := by
  by_contra hnot
  obtain ⟨p, hp, hpi, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  letI : Fact p.Prime := ⟨hp⟩
  have hiNeg : (6 : ZMod p) ^ (2 ^ i) = -1 := by
    rw [← add_eq_zero_iff_eq_neg]
    simpa [gammaSixFermatDenominator] using
      ((ZMod.natCast_eq_zero_iff (gammaSixFermatDenominator i) p).mpr hpi)
  have hjNeg : (6 : ZMod p) ^ (2 ^ j) = -1 := by
    rw [← add_eq_zero_iff_eq_neg]
    simpa [gammaSixFermatDenominator] using
      ((ZMod.natCast_eq_zero_iff (gammaSixFermatDenominator j) p).mpr hpj)
  have hdiff : j - i ≠ 0 := Nat.sub_ne_zero_of_lt hij
  have hpowEven : Even (2 ^ (j - i)) := Even.pow_of_ne_zero even_two hdiff
  have hexp : 2 ^ j = 2 ^ i * 2 ^ (j - i) := by
    rw [← pow_add, Nat.add_sub_of_le hij.le]
  have hjPos : (6 : ZMod p) ^ (2 ^ j) = 1 := by
    rw [hexp, pow_mul, hiNeg, hpowEven.neg_one_pow]
  have honeNeg : (1 : ZMod p) = -1 := hjPos.symm.trans hjNeg
  have htwoZero : (2 : ZMod p) = 0 := by
    linear_combination honeNeg
  have hpTwo : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwoZero
  have hpEq : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hpTwo |>.resolve_left hp.ne_one
  have hEven : Even (gammaSixFermatDenominator i) := by
    rw [even_iff_two_dvd]
    simpa [hpEq] using hpi
  exact (Nat.not_even_iff_odd.mpr (gammaSixFermatDenominator_odd i)) hEven

def gammaSixDenominatorPrime (n : ℕ) : Nat.Primes :=
  ⟨Nat.minFac (gammaSixFermatDenominator n),
    Nat.minFac_prime (by
      have hgt : 1 < gammaSixFermatDenominator n := by
        rw [gammaSixFermatDenominator]
        have : 0 < 6 ^ (2 ^ n) := pow_pos (by norm_num) _
        omega
      omega)⟩

lemma gammaSixDenominatorPrime_dvd (n : ℕ) :
    (gammaSixDenominatorPrime n : ℕ) ∣ gammaSixFermatDenominator n :=
  Nat.minFac_dvd _

lemma gammaSixDenominatorPrime_injective : Function.Injective gammaSixDenominatorPrime := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcop := gammaSixFermatDenominator_coprime hlt
    have hdvdI := gammaSixDenominatorPrime_dvd i
    have hdvdJ : (gammaSixDenominatorPrime i : ℕ) ∣ gammaSixFermatDenominator j := by
      simpa [hij] using gammaSixDenominatorPrime_dvd j
    exact Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨gammaSixDenominatorPrime i, (gammaSixDenominatorPrime i).2, hdvdI, hdvdJ⟩ hcop
  · have hcop := gammaSixFermatDenominator_coprime hgt
    have hdvdJ := gammaSixDenominatorPrime_dvd j
    have hdvdI : (gammaSixDenominatorPrime j : ℕ) ∣ gammaSixFermatDenominator i := by
      simpa [hij] using gammaSixDenominatorPrime_dvd i
    exact Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨gammaSixDenominatorPrime j, (gammaSixDenominatorPrime j).2, hdvdJ, hdvdI⟩ hcop

def gammaSixX (m : ℕ) : ℚ := ((6 ^ m : ℕ) : ℚ) / ((1 + 6 ^ m : ℕ) : ℚ)
def gammaSixY (m : ℕ) : ℚ := 1 / ((1 + 6 ^ m : ℕ) : ℚ)

lemma gammaSixDenominator_coprime_six {m : ℕ} (hm : 0 < m) :
    Nat.Coprime (1 + 6 ^ m) 6 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [pow_succ]
  rw [mul_comm (6 ^ k) 6]
  exact (Nat.coprime_add_mul_left_left 1 6 (6 ^ k)).mpr (by simp)

lemma padicValRat_gammaSixX_eq_neg {p m : ℕ} [Fact p.Prime]
    (hm : 0 < m) (hp : p ∣ 1 + 6 ^ m) :
    padicValRat p (gammaSixX m) = -(padicValNat p (1 + 6 ^ m) : ℤ) := by
  have h6 : ¬ p ∣ 6 := by
    intro hp6
    have hcop := gammaSixDenominator_coprime_six hm
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, Fact.out, hp, hp6⟩ hcop
  have hpow : ¬ p ∣ 6 ^ m := fun h => h6 ((Fact.out : Nat.Prime p).dvd_of_dvd_pow h)
  rw [gammaSixX, padicValRat.div]
  · rw [padicValRat.of_nat, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hpow]
    norm_num
  · positivity
  · positivity

lemma padicValRat_gammaSixY_eq_neg {p m : ℕ} [Fact p.Prime]
    (_hp : p ∣ 1 + 6 ^ m) :
    padicValRat p (gammaSixY m) = -(padicValNat p (1 + 6 ^ m) : ℤ) := by
  rw [gammaSixY, padicValRat.div]
  · rw [padicValRat.one, padicValRat.of_nat]
    norm_num
  · norm_num
  · positivity

lemma gammaSixX_div_Y (m : ℕ) : gammaSixX m / gammaSixY m = 6 ^ m := by
  rw [gammaSixX, gammaSixY]
  field_simp
  norm_cast

lemma padicValRat_gammaSixX_div_Y_eq_zero {p m : ℕ} [Fact p.Prime]
    (hm : 0 < m) (hp : p ∣ 1 + 6 ^ m) :
    padicValRat p (gammaSixX m / gammaSixY m) = 0 := by
  have h6 : ¬ p ∣ 6 := by
    intro hp6
    exact Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, Fact.out, hp, hp6⟩ (gammaSixDenominator_coprime_six hm)
  have hval : padicValRat p (6 : ℚ) = 0 := by
    change padicValRat p ((6 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h6]
    norm_num
  rw [gammaSixX_div_Y, padicValRat.pow, hval, mul_zero]

lemma padicNorm_gammaSixX_div_Y_eq_one {p m : ℕ} [Fact p.Prime]
    (hm : 0 < m) (hp : p ∣ 1 + 6 ^ m) :
    padicNorm p (gammaSixX m / gammaSixY m) = 1 := by
  have hne : gammaSixX m / gammaSixY m ≠ 0 := by
    rw [gammaSixX_div_Y]
    positivity
  rw [padicNorm.eq_zpow_of_nonzero hne,
    padicValRat_gammaSixX_div_Y_eq_zero hm hp]
  norm_num

theorem gammaSix_denominatorKummerLog_eq_zero {p m : ℕ} [Fact p.Prime]
    (hm : 0 < m) (hp : p ∣ 1 + 6 ^ m) :
    Real.log (((padicNorm p (gammaSixX m / gammaSixY m) : ℚ) : ℝ)) = 0 := by
  rw [padicNorm_gammaSixX_div_Y_eq_one hm hp]
  norm_num

noncomputable section

lemma gammaSixDenominatorPrime_not_dvd_six (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) : ¬(p : ℕ) ∣ 6 := by
  intro hp6
  exact Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p, p.2, hp, hp6⟩ (gammaSixDenominator_coprime_six hm)

lemma gammaSixDenominatorPrime_ne_two (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) : (p : ℕ) ≠ 2 := by
  intro h
  apply gammaSixDenominatorPrime_not_dvd_six p m hm hp
  rw [h]
  norm_num

lemma gammaSixDenominatorPrime_ne_three (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) : (p : ℕ) ≠ 3 := by
  intro h
  apply gammaSixDenominatorPrime_not_dvd_six p m hm hp
  rw [h]
  norm_num

theorem gammaSix_denominatorExactValuations (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    let e := padicValNat (p : ℕ) (1 + 6 ^ m)
    0 < e ∧
      padicValRat (p : ℕ) (gammaSixX m) = -(e : ℤ) ∧
      padicValRat (p : ℕ) (gammaSixY m) = -(e : ℤ) ∧
      padicValRat (p : ℕ) (gammaSixX m / gammaSixY m) = 0 := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  dsimp
  exact ⟨one_le_padicValNat_of_dvd (by positivity) hp,
    padicValRat_gammaSixX_eq_neg hm hp,
    padicValRat_gammaSixY_eq_neg hp,
    padicValRat_gammaSixX_div_Y_eq_zero hm hp⟩

def gammaSixDenominatorSixUnit (p : Nat.Primes) (m : ℕ) (hm : 0 < m)
    (hp : (p : ℕ) ∣ 1 + 6 ^ m) : (ZMod (p : ℕ))ˣ :=
  ZMod.unitOfCoprime 6
    ((gammaSixDenominator_coprime_six hm).symm.of_dvd_right hp)

lemma gammaSixDenominatorSixUnit_val (p : Nat.Primes) (m : ℕ) (hm : 0 < m)
    (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    ((gammaSixDenominatorSixUnit p m hm hp : (ZMod (p : ℕ))ˣ) : ZMod (p : ℕ)) = 6 := by
  simp [gammaSixDenominatorSixUnit, ZMod.unitOfCoprime]

lemma gammaSixDenominatorSixUnit_pow_val (p : Nat.Primes) (m : ℕ) (hm : 0 < m)
    (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    (((gammaSixDenominatorSixUnit p m hm hp ^ m : (ZMod (p : ℕ))ˣ) : ZMod (p : ℕ))) = -1 := by
  rw [Units.val_pow_eq_pow_val, gammaSixDenominatorSixUnit_val]
  rw [← add_eq_zero_iff_eq_neg]
  simpa [add_comm] using ((ZMod.natCast_eq_zero_iff (1 + 6 ^ m) (p : ℕ)).mpr hp)

abbrev GammaSixDenominatorResidueAlgebra (p : Nat.Primes) :=
  MonoidAlgebra ℂ (ZMod (p : ℕ))ˣ

def gammaSixForwardCommonPoleResidue (p : Nat.Primes) (m : ℕ) (hm : 0 < m)
    (hp : (p : ℕ) ∣ 1 + 6 ^ m) : GammaSixDenominatorResidueAlgebra p :=
  MonoidAlgebra.single (gammaSixDenominatorSixUnit p m hm hp ^ m) 1 -
    MonoidAlgebra.single 1 1

def gammaSixReciprocalCommonPoleResidue (p : Nat.Primes) (m : ℕ) (hm : 0 < m)
    (hp : (p : ℕ) ∣ 1 + 6 ^ m) : GammaSixDenominatorResidueAlgebra p :=
  MonoidAlgebra.single ((gammaSixDenominatorSixUnit p m hm hp ^ m)⁻¹) 1 -
    MonoidAlgebra.single 1 1

def gammaSixDenominatorEpsilon (p : Nat.Primes) (m : ℕ) (hm : 0 < m)
    (hp : (p : ℕ) ∣ 1 + 6 ^ m) : GammaSixDenominatorResidueAlgebra p :=
  MonoidAlgebra.single (gammaSixDenominatorSixUnit p m hm hp ^ m) 1 -
    MonoidAlgebra.single 1 1

theorem gammaSix_forward_commonPoleResidue_eq_epsilon (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    gammaSixForwardCommonPoleResidue p m hm hp = gammaSixDenominatorEpsilon p m hm hp := rfl

theorem gammaSix_reciprocal_commonPoleResidue_eq_epsilon (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    gammaSixReciprocalCommonPoleResidue p m hm hp = gammaSixDenominatorEpsilon p m hm hp := by
  rw [gammaSixReciprocalCommonPoleResidue, gammaSixDenominatorEpsilon,
    show (gammaSixDenominatorSixUnit p m hm hp ^ m)⁻¹ =
        gammaSixDenominatorSixUnit p m hm hp ^ m by
      ext
      rw [Units.val_inv_eq_inv_val, gammaSixDenominatorSixUnit_pow_val,
        ]
      simp]

theorem gammaSix_denominator_orientationCollapse (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    gammaSixForwardCommonPoleResidue p m hm hp -
      gammaSixReciprocalCommonPoleResidue p m hm hp = 0 := by
  rw [gammaSix_forward_commonPoleResidue_eq_epsilon,
    gammaSix_reciprocal_commonPoleResidue_eq_epsilon, sub_self]

theorem gammaSixDenominatorEpsilon_ne_zero (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    gammaSixDenominatorEpsilon p m hm hp ≠ 0 := by
  intro hzero
  have hp2 : (p : ℕ) ≠ 2 := by
    intro h
    have h2six : (2 : ℕ) ∣ 6 := by norm_num
    exact Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨2, Nat.prime_two, by simpa [h] using hp, h2six⟩
      (gammaSixDenominator_coprime_six hm)
  have hminus : gammaSixDenominatorSixUnit p m hm hp ^ m ≠ 1 := by
    intro h
    have hv := congrArg Units.val h
    rw [gammaSixDenominatorSixUnit_pow_val] at hv
    simp only [Units.val_one] at hv
    have htwoZero : (2 : ZMod (p : ℕ)) = 0 := by
      calc
        (2 : ZMod (p : ℕ)) = 1 - (-1) := by ring
        _ = 0 := by rw [hv]; ring
    have hpdiv : (p : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (p : ℕ)).mp htwoZero
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hpdiv |>.resolve_left p.2.ne_one)
  have hcoeff := congrArg
    (fun w : GammaSixDenominatorResidueAlgebra p =>
      w.coeff (gammaSixDenominatorSixUnit p m hm hp ^ m)) hzero
  simp [gammaSixDenominatorEpsilon, hminus] at hcoeff

def gammaSixDenominatorResidueFrobenius (p : Nat.Primes) :
    GammaSixDenominatorResidueAlgebra p →ₐ[ℂ] GammaSixDenominatorResidueAlgebra p :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (powMonoidHom (p : ℕ))

@[simp] theorem gammaSixDenominatorResidueFrobenius_single (p : Nat.Primes)
    (u : (ZMod (p : ℕ))ˣ) (c : ℂ) :
    gammaSixDenominatorResidueFrobenius p (MonoidAlgebra.single u c) =
      MonoidAlgebra.single (u ^ (p : ℕ)) c := by
  simp [gammaSixDenominatorResidueFrobenius,
    MonoidAlgebra.mapDomainAlgHom, MonoidAlgebra.mapDomain_single]

theorem gammaSixDenominatorResidueFrobenius_fixed (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    gammaSixDenominatorResidueFrobenius p (gammaSixDenominatorEpsilon p m hm hp) =
      gammaSixDenominatorEpsilon p m hm hp := by
  simp only [gammaSixDenominatorEpsilon, map_sub,
    gammaSixDenominatorResidueFrobenius_single, one_pow]
  congr 2
  ext
  exact ZMod.pow_card _

def gammaSixParityWittResidue : DeningerFiniteCyclotomicWittAlgebra 2 :=
  AddMonoidAlgebra.single (1 : ZMod 2) 1 - AddMonoidAlgebra.single 0 1

theorem gammaSixParityWittResidue_ne_zero : gammaSixParityWittResidue ≠ 0 := by
  intro h
  have hc := congrArg
    (fun w : DeningerFiniteCyclotomicWittAlgebra 2 => w.coeff (1 : ZMod 2)) h
  norm_num [gammaSixParityWittResidue] at hc

theorem gammaSixParityWittResidue_frobenius_fixed (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    deningerFiniteCyclotomicWittFrobenius (p : ℕ) 2
      ((p.2.coprime_iff_not_dvd).mpr (by
        intro hdvd
        exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left p.2.ne_one)))
        gammaSixParityWittResidue =
        gammaSixParityWittResidue := by
  have hodd := p.2.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  have hpval : ((p : ℕ) : ZMod 2) = 1 := by
    rw [hk, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self]
    simp
  simp only [gammaSixParityWittResidue, map_sub,
    deningerFiniteCyclotomicWittFrobenius_single]
  congr 2
  · change (1 : ZMod 2) * ((p : ℕ) : ZMod 2) = 1
    rw [hpval, mul_one]
  · change (0 : ZMod 2) * ((p : ℕ) : ZMod 2) = 0
    simp

def gammaSixParityFrobeniusStage (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    DeningerFiniteFrobeniusStage (p : ℕ) where
  modulus := 2
  modulus_ne_zero := by norm_num
  coprime := (p.2.coprime_iff_not_dvd).mpr (by
    intro hdvd
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left p.2.ne_one))

def gammaSixPrimeRationalWittParityResidue (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    DeningerPrimeComplexifiedRationalWittPresentation p :=
  deningerPrimeFiniteCyclotomicWittInclusion p (gammaSixParityFrobeniusStage p hp2)
    gammaSixParityWittResidue

theorem gammaSixPrimeRationalWittParityResidue_ne_zero (p : Nat.Primes)
    (hp2 : (p : ℕ) ≠ 2) : gammaSixPrimeRationalWittParityResidue p hp2 ≠ 0 := by
  exact (deningerPrimeFiniteCyclotomicWittInclusion_injective p
    (gammaSixParityFrobeniusStage p hp2)).ne gammaSixParityWittResidue_ne_zero

theorem gammaSixPrimeRationalWittParityResidue_frobenius_fixed (p : Nat.Primes)
    (hp2 : (p : ℕ) ≠ 2) :
    deningerPrimeComplexifiedRationalWittFrobenius p
        (gammaSixPrimeRationalWittParityResidue p hp2) =
      gammaSixPrimeRationalWittParityResidue p hp2 := by
  rw [gammaSixPrimeRationalWittParityResidue,
    deningerPrimeFiniteCyclotomicWittInclusion_frobenius]
  change deningerPrimeFiniteCyclotomicWittInclusion p (gammaSixParityFrobeniusStage p hp2)
      (deningerFiniteCyclotomicWittFrobenius (p : ℕ) 2
        (gammaSixParityFrobeniusStage p hp2).coprime gammaSixParityWittResidue) = _
  rw [gammaSixParityWittResidue_frobenius_fixed p hp2]

theorem gammaSixParityWittResidue_evaluation :
    deningerFiniteCyclotomicWittEvaluation 2 (1 : (ZMod 2)ˣ)
      gammaSixParityWittResidue = -2 := by
  rw [gammaSixParityWittResidue, map_sub,
    deningerFiniteCyclotomicWittEvaluation_single,
    deningerFiniteCyclotomicWittEvaluation_single]
  simp only [deningerFiniteUnitEvaluation, Units.val_one, mul_one,
    AddChar.map_zero_eq_one, one_mul]
  rw [show (1 : ZMod 2) = (1 : ℤ) by norm_num, ZMod.stdAddChar_coe]
  rw [show (2 * Real.pi * Complex.I * (1 : ℤ) / (2 : ℕ) : ℂ) =
      Real.pi * Complex.I by push_cast; ring]
  rw [Complex.exp_pi_mul_I]
  norm_num [deningerFiniteUnitEvaluation]

noncomputable def gammaSixResidueMinusOneRoot (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    (ZMod (p : ℕ))ˣ :=
  (IsPrimitiveRoot.neg_one (R := ZMod (p : ℕ)) (p : ℕ) hp2).isUnit
    (by norm_num : (2 : ℕ) ≠ 0) |>.unit

lemma gammaSixResidueMinusOneRoot_spec (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    IsPrimitiveRoot (gammaSixResidueMinusOneRoot p hp2) 2 := by
  change IsPrimitiveRoot
    ((IsPrimitiveRoot.neg_one (R := ZMod (p : ℕ)) (p : ℕ) hp2).isUnit
      (by norm_num : (2 : ℕ) ≠ 0) |>.unit) 2
  exact IsPrimitiveRoot.isUnit_unit (M := ZMod (p : ℕ)) (by norm_num : (2 : ℕ) ≠ 0)
    (IsPrimitiveRoot.neg_one (R := ZMod (p : ℕ)) (p : ℕ) hp2)

lemma gammaSixResidueMinusOneRoot_val (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    ((gammaSixResidueMinusOneRoot p hp2 : (ZMod (p : ℕ))ˣ) : ZMod (p : ℕ)) = -1 := by
  rw [gammaSixResidueMinusOneRoot]
  exact ((IsPrimitiveRoot.neg_one (R := ZMod (p : ℕ)) (p : ℕ) hp2).isUnit
    (by norm_num : (2 : ℕ) ≠ 0)).unit_spec

noncomputable def gammaSixParityResidueEmbedding (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    Multiplicative (ZMod 2) →* (ZMod (p : ℕ))ˣ :=
  let e : Multiplicative (ZMod 2) ≃*
      Subgroup.zpowers (gammaSixResidueMinusOneRoot p hp2) :=
    (gammaSixResidueMinusOneRoot_spec p hp2).zmodEquivZPowers.toMultiplicative
  (Subgroup.zpowers (gammaSixResidueMinusOneRoot p hp2)).subtype.comp e.toMonoidHom

lemma gammaSixParityResidueEmbedding_one (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    gammaSixParityResidueEmbedding p hp2 (Multiplicative.ofAdd (1 : ZMod 2)) = gammaSixResidueMinusOneRoot p hp2 := by
  change ((Subgroup.zpowers (gammaSixResidueMinusOneRoot p hp2)).subtype)
    (((gammaSixResidueMinusOneRoot_spec p hp2).zmodEquivZPowers.toMultiplicative)
      (Multiplicative.ofAdd (1 : ZMod 2))) = _
  change (((gammaSixResidueMinusOneRoot_spec p hp2).zmodEquivZPowers (1 : ZMod 2)).toMul :
    (ZMod (p : ℕ))ˣ) = gammaSixResidueMinusOneRoot p hp2
  have h := (gammaSixResidueMinusOneRoot_spec p hp2).zmodEquivZPowers_apply_coe_nat 1
  have hv := congrArg
    (fun z : Additive (Subgroup.zpowers (gammaSixResidueMinusOneRoot p hp2)) =>
      (z.toMul : (ZMod (p : ℕ))ˣ)) h
  simpa using hv

lemma gammaSixParityResidueEmbedding_zero (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    gammaSixParityResidueEmbedding p hp2 (Multiplicative.ofAdd (0 : ZMod 2)) = 1 := by
  exact map_one (gammaSixParityResidueEmbedding p hp2)

noncomputable def gammaSixParityResidueInclusion (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    DeningerFiniteCyclotomicWittAlgebra 2 →ₐ[ℂ]
      GammaSixDenominatorResidueAlgebra p where
  toFun x := MonoidAlgebra.mapDomainAlgHom ℂ ℂ (gammaSixParityResidueEmbedding p hp2)
    ((AddMonoidAlgebra.toMultiplicative ℂ (ZMod 2)) x)
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul]
    exact map_mul (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (gammaSixParityResidueEmbedding p hp2)) _ _
  map_zero' := by simp
  map_add' x y := by
    rw [map_add]
    exact map_add (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (gammaSixParityResidueEmbedding p hp2)) _ _
  commutes' c := by simp [AddMonoidAlgebra.toMultiplicative]

@[simp] lemma gammaSixParityResidueInclusion_single (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2)
    (j : ZMod 2) (c : ℂ) :
    gammaSixParityResidueInclusion p hp2 (AddMonoidAlgebra.single j c) =
      MonoidAlgebra.single (gammaSixParityResidueEmbedding p hp2 (Multiplicative.ofAdd j)) c := by
  simp [gammaSixParityResidueInclusion, AddMonoidAlgebra.toMultiplicative]

theorem gammaSixParityResidueInclusion_maps_epsilon (p : Nat.Primes) (m : ℕ) (hm : 0 < m)
    (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    gammaSixParityResidueInclusion p (gammaSixDenominatorPrime_ne_two p m hm hp)
        gammaSixParityWittResidue = gammaSixDenominatorEpsilon p m hm hp := by
  rw [gammaSixParityWittResidue, map_sub, gammaSixParityResidueInclusion_single,
    gammaSixParityResidueInclusion_single, gammaSixDenominatorEpsilon,
    gammaSixParityResidueEmbedding_one, gammaSixParityResidueEmbedding_zero]
  congr 2
  apply Units.ext
  rw [gammaSixResidueMinusOneRoot_val, gammaSixDenominatorSixUnit_pow_val]

def gammaSixDenominatorTameSymbol (p : Nat.Primes) (m e : ℕ) (hm : 0 < m)
    (hp : (p : ℕ) ∣ 1 + 6 ^ m) : ZMod (p : ℕ) :=
  (-1) ^ (e * e) *
    (((gammaSixDenominatorSixUnit p m hm hp : (ZMod (p : ℕ))ˣ) : ZMod (p : ℕ))⁻¹) ^ (m * e)

theorem gammaSixDenominatorTameSymbol_eq_one (p : Nat.Primes) (m e : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    gammaSixDenominatorTameSymbol p m e hm hp = 1 := by
  have hpow :
      (((gammaSixDenominatorSixUnit p m hm hp : (ZMod (p : ℕ))ˣ) :
          ZMod (p : ℕ)) ^ m) = -1 := by
    rw [← Units.val_pow_eq_pow_val]
    exact gammaSixDenominatorSixUnit_pow_val p m hm hp
  rw [gammaSixDenominatorTameSymbol, pow_mul _ m e, inv_pow, hpow]
  simp only [inv_neg, inv_one]
  rw [← pow_add]
  exact (show Even (e * e + e) by
    simpa [mul_add] using Nat.even_mul_succ_self e).neg_one_pow

theorem gammaSix_denominatorExactTameKummer (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    gammaSixDenominatorTameSymbol p m (padicValNat (p : ℕ) (1 + 6 ^ m)) hm hp = 1 ∧
      Real.log (((padicNorm (p : ℕ) (gammaSixX m / gammaSixY m) : ℚ) : ℝ)) = 0 := by
  letI : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact ⟨gammaSixDenominatorTameSymbol_eq_one p m _ hm hp,
    gammaSix_denominatorKummerLog_eq_zero hm hp⟩

theorem gammaSix_denominatorRationalWittSurvivor (p : Nat.Primes) (m : ℕ)
    (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m) :
    gammaSixPrimeRationalWittParityResidue p
        (gammaSixDenominatorPrime_ne_two p m hm hp) ≠ 0 ∧
      deningerPrimeComplexifiedRationalWittFrobenius p
          (gammaSixPrimeRationalWittParityResidue p
            (gammaSixDenominatorPrime_ne_two p m hm hp)) =
        gammaSixPrimeRationalWittParityResidue p
          (gammaSixDenominatorPrime_ne_two p m hm hp) ∧
      deningerFiniteCyclotomicWittEvaluation 2 (1 : (ZMod 2)ˣ)
        gammaSixParityWittResidue = -2 := by
  exact ⟨gammaSixPrimeRationalWittParityResidue_ne_zero p _,
    gammaSixPrimeRationalWittParityResidue_frobenius_fixed p _,
    gammaSixParityWittResidue_evaluation⟩

end

open Complex Real
open scoped BigOperators

noncomputable section

def gammaSixDenominatorPlaceSet : Set Nat.Primes :=
  {p | ∃ m : ℕ, 0 < m ∧ (p : ℕ) ∣ 1 + 6 ^ m}

theorem gammaSixDenominatorPrime_mem (n : ℕ) :
    gammaSixDenominatorPrime n ∈ gammaSixDenominatorPlaceSet := by
  refine ⟨2 ^ n, pow_pos (by norm_num) _, ?_⟩
  simpa [gammaSixFermatDenominator, add_comm] using gammaSixDenominatorPrime_dvd n

theorem gammaSixDenominatorPlaceSet_infinite : gammaSixDenominatorPlaceSet.Infinite := by
  apply (Set.infinite_range_of_injective gammaSixDenominatorPrime_injective).mono
  rintro p ⟨n, rfl⟩
  exact gammaSixDenominatorPrime_mem n

lemma gammaSixCofinalExponent_ge (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

def gammaSixEvenDenominatorCoefficient (n : ℕ) : ℝ := (1 / 6 : ℝ) ^ (2 ^ n)

lemma gammaSixEvenDenominatorCoefficient_nonneg (n : ℕ) :
    0 ≤ gammaSixEvenDenominatorCoefficient n := by
  exact pow_nonneg (by norm_num) _

lemma gammaSixEvenDenominatorCoefficient_le_geometric (n : ℕ) :
    gammaSixEvenDenominatorCoefficient n ≤ (1 / 6 : ℝ) ^ (n + 1) := by
  exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 6)
    (by norm_num : (1 / 6 : ℝ) ≤ 1) (gammaSixCofinalExponent_ge n)

theorem summable_gammaSixEvenDenominatorCoefficient :
    Summable gammaSixEvenDenominatorCoefficient := by
  have hgeom : Summable (fun n : ℕ => (1 / 6 : ℝ) ^ (n + 1)) := by
    rw [summable_nat_add_iff 1]
    exact summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 6 : ℝ)‖ < 1)
  exact Summable.of_nonneg_of_le gammaSixEvenDenominatorCoefficient_nonneg
    gammaSixEvenDenominatorCoefficient_le_geometric hgeom

theorem summable_sq_gammaSixEvenDenominatorCoefficient :
    Summable (fun n => gammaSixEvenDenominatorCoefficient n ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    summable_gammaSixEvenDenominatorCoefficient
  have hzero := gammaSixEvenDenominatorCoefficient_nonneg n
  have hone : gammaSixEvenDenominatorCoefficient n ≤ 1 := by
    rw [gammaSixEvenDenominatorCoefficient]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

/-- The actual cofinal parity layer, separated into its rational-Witt packet and scalar
tensor-square coefficient.  Injectivity of `place` makes different entries different prime
summands. -/
structure GammaSixEvenDenominatorPacket where
  place : Nat.Primes
  witt : DeningerFiniteCyclotomicWittAlgebra 2
  coefficient : ℝ

def gammaSixEvenDenominatorPacket (n : ℕ) : GammaSixEvenDenominatorPacket where
  place := gammaSixDenominatorPrime n
  witt := gammaSixParityWittResidue
  coefficient := gammaSixEvenDenominatorCoefficient n

theorem gammaSixEvenDenominatorPacket_place_injective :
    Function.Injective (fun n => (gammaSixEvenDenominatorPacket n).place) :=
  gammaSixDenominatorPrime_injective

theorem gammaSixEvenDenominatorPacket_witt_ne_zero (n : ℕ) :
    (gammaSixEvenDenominatorPacket n).witt ≠ 0 := gammaSixParityWittResidue_ne_zero

theorem gammaSixEvenDenominatorPacket_mixed_admission :
    Summable (fun n => |(gammaSixEvenDenominatorPacket n).coefficient|) ∧
      Summable (fun n => |(gammaSixEvenDenominatorPacket n).coefficient| ^ 2) := by
  constructor
  · simpa [gammaSixEvenDenominatorPacket, abs_of_nonneg,
      gammaSixEvenDenominatorCoefficient_nonneg] using
      summable_gammaSixEvenDenominatorCoefficient
  · simpa [gammaSixEvenDenominatorPacket, abs_of_nonneg,
      gammaSixEvenDenominatorCoefficient_nonneg] using
      summable_sq_gammaSixEvenDenominatorCoefficient

def gammaSixMixedKotheData : DeningerKotheData (Bool × ℕ) where
  w k i := deningerGammaSixCriticalKotheData.w k i.2
  pos k i := deningerGammaSixCriticalKotheData.pos k i.2
  mono k i := deningerGammaSixCriticalKotheData.mono k i.2

theorem gammaSixMixedKotheData_isNuclear : gammaSixMixedKotheData.IsNuclear := by
  intro k
  obtain ⟨m, hkm, hsum⟩ := deningerGammaSixCriticalKotheData_isNuclear k
  refine ⟨m, hkm, ?_⟩
  rw [summable_prod_of_nonneg (fun i => by
    exact div_nonneg (gammaSixMixedKotheData.pos k i).le
      (gammaSixMixedKotheData.pos m i).le)]
  constructor
  · intro b
    simpa [gammaSixMixedKotheData] using hsum
  · exact Summable.of_finite

abbrev GammaSixMixedKothe := DeningerKotheCarrier ℂ gammaSixMixedKotheData

theorem gammaSixMixedKothe_isNuclearSpace :
    DeningerIsNuclearSpace (deningerKotheSeminorm (𝕜 := ℂ) gammaSixMixedKotheData) :=
  deningerKothe_isNuclearSpace gammaSixMixedKotheData gammaSixMixedKotheData_isNuclear

theorem gammaSixMixedKothe_mem_iff (c : Bool × ℕ → ℂ) :
    c ∈ GammaSixMixedKothe ↔
      ∀ b : Bool, DeningerGammaSixCriticalEdgeMem (fun m => c (b, m)) := by
  constructor
  · intro hc b
    rw [← deningerGammaSixCriticalKothe_mem_iff]
    intro k
    have hall := (summable_prod_of_nonneg (fun i : Bool × ℕ =>
      mul_nonneg (gammaSixMixedKotheData.pos k i).le (norm_nonneg _))).mp (hc k)
    simpa [gammaSixMixedKotheData] using hall.1 b
  · intro hc k
    rw [summable_prod_of_nonneg (fun i : Bool × ℕ =>
      mul_nonneg (gammaSixMixedKotheData.pos k i).le (norm_nonneg _))]
    constructor
    · intro b
      have hb : (fun m => c (b, m)) ∈ DeningerGammaSixCriticalKothe :=
        (deningerGammaSixCriticalKothe_mem_iff _).mpr (hc b)
      simpa [gammaSixMixedKotheData] using hb k
    · exact Summable.of_finite

def gammaSixMixedHorizontalEvaluation (delta : ℝ) (c : Bool × ℕ → ℂ) :
    Bool × ℕ → ℂ
  | (true, m) => (((6 : ℝ) ^ (delta * (m + 1 : ℝ)) : ℝ) : ℂ) * c (true, m)
  | (false, m) => (((6 : ℝ) ^ (-delta * (m + 1 : ℝ)) : ℝ) : ℂ) * c (false, m)

lemma gammaSixMixedHorizontalEvaluation_norm_le {delta : ℝ} {k : ℕ}
    (hdk : |delta| ≤ deningerGammaSixKotheExponent k)
    (c : Bool × ℕ → ℂ) (i : Bool × ℕ) :
    ‖gammaSixMixedHorizontalEvaluation delta c i‖ ≤
      gammaSixMixedKotheData.w k i * ‖c i‖ := by
  rcases i with ⟨b, m⟩
  cases b
  · rw [gammaSixMixedHorizontalEvaluation, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6)
          (-delta * (m + 1 : ℝ)))]
    change (6 : ℝ) ^ (-delta * (m + 1 : ℝ)) * ‖c (false, m)‖ ≤
      (6 : ℝ) ^ (deningerGammaSixKotheExponent k * (m + 1 : ℝ)) * ‖c (false, m)‖
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6)
    have hneg : -delta ≤ |delta| := neg_le_abs delta
    exact mul_le_mul_of_nonneg_right (hneg.trans hdk) (by positivity)
  · rw [gammaSixMixedHorizontalEvaluation, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6)
          (delta * (m + 1 : ℝ)))]
    change (6 : ℝ) ^ (delta * (m + 1 : ℝ)) * ‖c (true, m)‖ ≤
      (6 : ℝ) ^ (deningerGammaSixKotheExponent k * (m + 1 : ℝ)) * ‖c (true, m)‖
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6)
    have hpos : delta ≤ |delta| := le_abs_self delta
    exact mul_le_mul_of_nonneg_right (hpos.trans hdk) (by positivity)

theorem gammaSixMixedHorizontalEvaluation_summable_and_bound {delta : ℝ} {k : ℕ}
    (hdk : |delta| ≤ deningerGammaSixKotheExponent k) (c : GammaSixMixedKothe) :
    Summable (fun i => ‖gammaSixMixedHorizontalEvaluation delta c i‖) ∧
      ∑' i, ‖gammaSixMixedHorizontalEvaluation delta c i‖ ≤
        deningerKotheSeminorm gammaSixMixedKotheData k c := by
  have hdom := gammaSixMixedHorizontalEvaluation_norm_le hdk (c : Bool × ℕ → ℂ)
  have hsum := (c.2 k).of_nonneg_of_le (fun i => norm_nonneg _) hdom
  exact ⟨hsum, Summable.tsum_le_tsum hdom hsum (c.2 k)⟩

theorem gammaSixMixedHorizontalEvaluation_continuityGrade {delta : ℝ} (hdelta : |delta| < 1)
    (c : GammaSixMixedKothe) :
    ∃ k : ℕ,
      Summable (fun i => ‖gammaSixMixedHorizontalEvaluation delta c i‖) ∧
      ∑' i, ‖gammaSixMixedHorizontalEvaluation delta c i‖ ≤
        deningerKotheSeminorm gammaSixMixedKotheData k c := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hdelta)
  have hinv : 1 / (n + 2 : ℝ) < 1 - |delta| := by
    calc
      1 / (n + 2 : ℝ) ≤ 1 / (n + 1 : ℝ) := by
        apply one_div_le_one_div_of_le (by positivity)
        norm_num
      _ < 1 - |delta| := hn
  have hgrade : |delta| ≤ deningerGammaSixKotheExponent n := by
    rw [deningerGammaSixKotheExponent]
    linarith
  exact ⟨n, gammaSixMixedHorizontalEvaluation_summable_and_bound hgrade c⟩

def gammaSixMixedEvaluatedPair (delta : ℝ) : Bool × ℕ → ℂ
  | (true, m) => deningerGammaSixForwardEvaluatedEdge delta m
  | (false, m) => -deningerGammaSixReflectedEvaluatedEdge delta m

lemma summable_norm_gammaSixForwardEvaluatedEdge_iff (delta : ℝ) :
    Summable (fun m => ‖deningerGammaSixForwardEvaluatedEdge delta m‖) ↔ delta < 1 := by
  have h := summable_deningerGammaSixCriticalWeight_forwardEdge_iff 0 delta
  simpa [deningerGammaSixCriticalWeight] using h

lemma summable_norm_gammaSixReflectedEvaluatedEdge_iff (delta : ℝ) :
    Summable (fun m => ‖deningerGammaSixReflectedEvaluatedEdge delta m‖) ↔ -1 < delta := by
  change Summable (fun m => ‖deningerGammaSixForwardEvaluatedEdge (-delta) m‖) ↔ -1 < delta
  rw [summable_norm_gammaSixForwardEvaluatedEdge_iff]
  constructor <;> intro h <;> linarith

lemma summable_sq_norm_gammaSixForwardEvaluatedEdge_iff (delta : ℝ) :
    Summable (fun m => ‖deningerGammaSixForwardEvaluatedEdge delta m‖ ^ 2) ↔ delta < 1 := by
  simp_rw [deningerGammaSixForwardEvaluatedEdge_norm]
  have heq : (fun m : ℕ => (((6 : ℝ) ^ (-1 + delta)) ^ (m + 1)) ^ 2) =
      fun m : ℕ => (((6 : ℝ) ^ (-1 + delta)) ^ 2) ^ (m + 1) := by
    funext m
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [heq]
  rw [summable_nat_add_iff 1, summable_geometric_iff_norm_lt_one,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ((6 : ℝ) ^ (-1 + delta)) ^ 2),
    sq_lt_one_iff₀ (by positivity : 0 ≤ (6 : ℝ) ^ (-1 + delta)),
    Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 6)]
  norm_num

lemma summable_sq_norm_gammaSixReflectedEvaluatedEdge_iff (delta : ℝ) :
    Summable (fun m => ‖deningerGammaSixReflectedEvaluatedEdge delta m‖ ^ 2) ↔ -1 < delta := by
  change Summable (fun m => ‖deningerGammaSixForwardEvaluatedEdge (-delta) m‖ ^ 2) ↔ -1 < delta
  rw [summable_sq_norm_gammaSixForwardEvaluatedEdge_iff]
  constructor <;> intro h <;> linarith

def GammaSixMixedL1L2Admission (c : Bool × ℕ → ℂ) : Prop :=
  Summable (fun i => ‖c i‖) ∧ Summable (fun i => ‖c i‖ ^ 2)

theorem gammaSixMixedEvaluatedPair_admission_iff (delta : ℝ) :
    GammaSixMixedL1L2Admission (gammaSixMixedEvaluatedPair delta) ↔ |delta| < 1 := by
  have hnorm_nonneg : 0 ≤ fun i : Bool × ℕ => ‖gammaSixMixedEvaluatedPair delta i‖ :=
    fun _ => norm_nonneg _
  have hsq_nonneg : 0 ≤ fun i : Bool × ℕ => ‖gammaSixMixedEvaluatedPair delta i‖ ^ 2 :=
    fun _ => sq_nonneg _
  rw [GammaSixMixedL1L2Admission,
    summable_prod_of_nonneg hnorm_nonneg,
    summable_prod_of_nonneg hsq_nonneg]
  simp only [Bool.forall_bool, gammaSixMixedEvaluatedPair, norm_neg]
  rw [summable_norm_gammaSixForwardEvaluatedEdge_iff,
    summable_norm_gammaSixReflectedEvaluatedEdge_iff,
    summable_sq_norm_gammaSixForwardEvaluatedEdge_iff,
    summable_sq_norm_gammaSixReflectedEvaluatedEdge_iff]
  simp only [and_self, Summable.of_finite, and_true]
  rw [abs_lt]

def gammaSixMixedReflection (c : Bool × ℕ → ℂ) : Bool × ℕ → ℂ
  | (true, m) => -c (false, m)
  | (false, m) => -c (true, m)

theorem gammaSixMixedReflection_evaluatedPair (delta : ℝ) :
    gammaSixMixedReflection (gammaSixMixedEvaluatedPair delta) =
      gammaSixMixedEvaluatedPair (-delta) := by
  funext i
  rcases i with ⟨b, m⟩
  cases b <;> simp [gammaSixMixedReflection, gammaSixMixedEvaluatedPair,
    deningerGammaSixReflectedEvaluatedEdge]

def gammaSixMixedOddRead (c : Bool × ℕ → ℂ) (m : ℕ) : ℂ :=
  c (true, m) + c (false, m)

theorem gammaSixMixedOddRead_evaluatedPair (delta : ℝ) (m : ℕ) :
    gammaSixMixedOddRead (gammaSixMixedEvaluatedPair delta) m =
      (((6 : ℝ) ^ (-1 + delta)) ^ (m + 1) -
        ((6 : ℝ) ^ (-1 - delta)) ^ (m + 1) : ℝ) := by
  simp [gammaSixMixedOddRead, gammaSixMixedEvaluatedPair,
    deningerGammaSixForwardEvaluatedEdge, deningerGammaSixReflectedEvaluatedEdge]
  congr 2

theorem gammaSixMixedOddRead_evaluatedPair_eq_zero_iff (delta : ℝ) :
    gammaSixMixedOddRead (gammaSixMixedEvaluatedPair delta) = 0 ↔ delta = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    rw [gammaSixMixedOddRead_evaluatedPair] at h0
    simp only [zero_add, pow_one, Pi.zero_apply, Complex.ofReal_eq_zero, sub_eq_zero] at h0
    have hexp := (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 6)).injective h0
    linarith
  · rintro rfl
    funext m
    rw [gammaSixMixedOddRead_evaluatedPair]
    norm_num

theorem gammaSixCommonPole_factor_odd_zero {V : Type*} [AddCommGroup V]
    (p : Nat.Primes) (m : ℕ) (hm : 0 < m) (hp : (p : ℕ) ∣ 1 + 6 ^ m)
    (F : GammaSixDenominatorResidueAlgebra p →+ V) :
    F (gammaSixForwardCommonPoleResidue p m hm hp) -
      F (gammaSixReciprocalCommonPoleResidue p m hm hp) = 0 := by
  rw [gammaSix_forward_commonPoleResidue_eq_epsilon,
    gammaSix_reciprocal_commonPoleResidue_eq_epsilon, sub_self]

/-- Dependency-closed Gamma-six cyclotomic-denominator admission.  This packages the infinite
honest denominator support, cofinal nonzero Witt survivor, Frobenius invariance, mixed
`ℓ¹ ∩ ℓ²` admission, nuclear two-orientation carrier, sharp open-strip admission, and exact
critical-line zero locus.  It contains no Xi-zero or RH premise. -/
theorem gammaSixCyclotomicDenominatorAdmission_closed :
    gammaSixDenominatorPlaceSet.Infinite ∧
    Function.Injective gammaSixDenominatorPrime ∧
    (∀ n, gammaSixDenominatorPrime n ∈ gammaSixDenominatorPlaceSet) ∧
    gammaSixParityWittResidue ≠ 0 ∧
    deningerFiniteCyclotomicWittEvaluation 2 (1 : (ZMod 2)ˣ)
      gammaSixParityWittResidue = -2 ∧
    Summable gammaSixEvenDenominatorCoefficient ∧
    Summable (fun n => gammaSixEvenDenominatorCoefficient n ^ 2) ∧
    gammaSixMixedKotheData.IsNuclear ∧
    (∀ (p : Nat.Primes) (m : ℕ) (hm : 0 < m)
        (hp : (p : ℕ) ∣ 1 + 6 ^ m),
      gammaSixDenominatorTameSymbol p m (padicValNat (p : ℕ) (1 + 6 ^ m)) hm hp = 1 ∧
      Real.log (((padicNorm (p : ℕ) (gammaSixX m / gammaSixY m) : ℚ) : ℝ)) = 0 ∧
      gammaSixForwardCommonPoleResidue p m hm hp -
        gammaSixReciprocalCommonPoleResidue p m hm hp = 0 ∧
      gammaSixParityResidueInclusion p
          (gammaSixDenominatorPrime_ne_two p m hm hp) gammaSixParityWittResidue =
        gammaSixDenominatorEpsilon p m hm hp ∧
      gammaSixPrimeRationalWittParityResidue p
        (gammaSixDenominatorPrime_ne_two p m hm hp) ≠ 0) ∧
    (∀ delta : ℝ,
      GammaSixMixedL1L2Admission (gammaSixMixedEvaluatedPair delta) ↔ |delta| < 1) ∧
    (∀ delta : ℝ,
      gammaSixMixedOddRead (gammaSixMixedEvaluatedPair delta) = 0 ↔ delta = 0) := by
  exact ⟨gammaSixDenominatorPlaceSet_infinite,
    gammaSixDenominatorPrime_injective,
    gammaSixDenominatorPrime_mem,
    gammaSixParityWittResidue_ne_zero,
    gammaSixParityWittResidue_evaluation,
    summable_gammaSixEvenDenominatorCoefficient,
    summable_sq_gammaSixEvenDenominatorCoefficient,
    gammaSixMixedKotheData_isNuclear,
    fun p m hm hp => ⟨(gammaSix_denominatorExactTameKummer p m hm hp).1,
      (gammaSix_denominatorExactTameKummer p m hm hp).2,
      gammaSix_denominator_orientationCollapse p m hm hp,
      gammaSixParityResidueInclusion_maps_epsilon p m hm hp,
      (gammaSix_denominatorRationalWittSurvivor p m hm hp).1⟩,
    gammaSixMixedEvaluatedPair_admission_iff,
    gammaSixMixedOddRead_evaluatedPair_eq_zero_iff⟩

end
end RHTower
