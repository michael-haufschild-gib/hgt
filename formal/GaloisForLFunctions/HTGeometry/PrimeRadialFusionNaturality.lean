import GaloisForLFunctions.HTGeometry.PrimeRadialFusionFieldCorrespondence
import Mathlib.NumberTheory.ArithmeticFunction.LFunction

/-!
# Naturality of prime-radial fusion

Raywise Cauchy fusion is not an unrelated second multiplication.  On the augmentation ideal of
arithmetic functions it is exactly Dirichlet convolution followed by projection back to positive
prime powers.  The same proof also gives the intrinsic commutative, associative, bilinear laws of
the external fusion operation.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Set

noncomputable section

set_option maxHeartbeats 1200000

/-- Projection of an arithmetic function onto its positive-prime-power coordinates. -/
def positivePrimePowerProjection
    (A : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  arithmeticFunctionOfPrimePowerProfile (primePowerCoordinateProfile A)

@[simp]
theorem primePowerCoordinateProfile_positivePrimePowerProjection
    (A : ArithmeticFunction ℂ) (x : PrimePowerClockIndex) :
    primePowerCoordinateProfile (positivePrimePowerProjection A) x =
      primePowerCoordinateProfile A x := by
  exact primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile _ x

/-- The positive-prime-power projection is the identity precisely on sources already supported
there. -/
theorem positivePrimePowerProjection_eq_self
    (A : ArithmeticFunction ℂ)
    (hA : PrimeProfileSupportedOnPositivePrimePowers A) :
    positivePrimePowerProjection A = A := by
  ext n
  by_cases hpow : IsPrimePow n
  · let x : PrimePowerClockIndex := Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
    have hx := congrArg Subtype.val
      (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
    have hnrep : n = (x.1 : Nat) ^ (x.2 + 1) := by
      simpa only [x, Nat.Primes.coe_prodNatEquiv_apply] using! hx.symm
    calc
      positivePrimePowerProjection A n =
          primePowerCoordinateProfile (positivePrimePowerProjection A) x := by
            simpa only [primePowerCoordinateProfile,
              Nat.Primes.coe_prodNatEquiv_apply] using
                congrArg (fun m : Nat => positivePrimePowerProjection A m) hx.symm
      _ = primePowerCoordinateProfile A x :=
        primePowerCoordinateProfile_positivePrimePowerProjection A x
      _ = A n := by
        simpa only [primePowerCoordinateProfile,
          Nat.Primes.coe_prodNatEquiv_apply] using
            congrArg (fun m : Nat => A m) hx
  · have hn : A n = 0 := by
      by_contra hne
      obtain ⟨p, e, hne'⟩ := hA hne
      apply hpow
      rw [hne']
      exact (Nat.Primes.prodNatEquiv (p, e)).property
    simp [positivePrimePowerProjection, arithmeticFunctionOfPrimePowerProfile, hpow, hn]

/-- Divisor pairs of a prime power are exactly the pairs of complementary powers of that prime. -/
theorem divisorsAntidiagonal_prime_pow
    (p : Nat.Primes) (n : Nat) :
    ((p : Nat) ^ n).divisorsAntidiagonal =
      (Finset.HasAntidiagonal.antidiagonal n).map
        (.prodMap ⟨fun k => (p : Nat) ^ k, Nat.pow_right_injective p.2.one_lt⟩
          ⟨fun k => (p : Nat) ^ k, Nat.pow_right_injective p.2.one_lt⟩) := by
  apply Finset.Subset.antisymm
  · intro ab hab
    obtain ⟨hmul, _hne⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow p.2).mp ⟨ab.2, hmul.symm⟩
    have hsplit : (p : Nat) ^ i * (p : Nat) ^ (n - i) = (p : Nat) ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' hi]
    have hb : ab.2 = (p : Nat) ^ (n - i) := by
      have hcancel : (p : Nat) ^ i * ab.2 =
          (p : Nat) ^ i * (p : Nat) ^ (n - i) := by
        rw [hsplit, ← hai]
        exact hmul
      exact Nat.eq_of_mul_eq_mul_left (pow_pos p.2.pos i) hcancel
    apply Finset.mem_map.mpr
    refine ⟨(i, n - i),
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_sub_of_le hi), ?_⟩
    exact Prod.ext hai.symm hb.symm
  · exact Nat.antidiagonal_map_subset_divisorsAntidiagonal_pow p.2.one_lt n

/-- If an arithmetic function has zero augmentation, its ray-series coefficient at every depth,
including depth zero, is its value on the corresponding prime power. -/
theorem primeRadialRaySeries_coeff_eq_of_apply_one_eq_zero
    (A : ArithmeticFunction ℂ) (p : Nat.Primes) (hA : A 1 = 0) (n : Nat) :
    PowerSeries.coeff n (primeRadialRaySeries A p) = A ((p : Nat) ^ n) := by
  cases n with
  | zero => simpa [primeRadialRaySeries] using hA.symm
  | succ n => simp [primeRadialRaySeries]

/-- On each prime ray, the Cauchy product of zero-augmentation ray series is the restriction of
Dirichlet convolution to that ray. -/
theorem primeRadialRaySeries_mul_coeff_eq_dirichletConvolution
    (A B : ArithmeticFunction ℂ) (p : Nat.Primes)
    (hA : A 1 = 0) (hB : B 1 = 0) (n : Nat) :
    PowerSeries.coeff n
        (primeRadialRaySeries A p * primeRadialRaySeries B p) =
      (A * B) ((p : Nat) ^ n) := by
  rw [PowerSeries.coeff_mul, ArithmeticFunction.mul_apply,
    divisorsAntidiagonal_prime_pow]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro ij hij
  change PowerSeries.coeff ij.1 (primeRadialRaySeries A p) *
      PowerSeries.coeff ij.2 (primeRadialRaySeries B p) =
    A ((p : Nat) ^ ij.1) * B ((p : Nat) ^ ij.2)
  rw [primeRadialRaySeries_coeff_eq_of_apply_one_eq_zero A p hA,
    primeRadialRaySeries_coeff_eq_of_apply_one_eq_zero B p hB]

/-- Support on positive prime powers forces zero augmentation. -/
theorem apply_one_eq_zero_of_supportedOnPositivePrimePowers
    (A : ArithmeticFunction ℂ)
    (hA : PrimeProfileSupportedOnPositivePrimePowers A) :
    A 1 = 0 := by
  by_contra hne
  obtain ⟨p, e, hp⟩ := hA hne
  have hone : (p : Nat) ^ (e + 1) = 1 := hp.symm
  obtain hpone | hezero := Nat.pow_eq_one.mp hone
  · exact p.2.ne_one hpone
  · omega

/-- **Dirichlet-projection fusion law.**  On positive-prime-power sources, raywise Cauchy fusion
is exactly Dirichlet convolution followed by the canonical positive-prime-power projection. -/
theorem primeRadialFusion_eq_positivePrimePowerProjection_mul
    (A B : ArithmeticFunction ℂ)
    (hA : PrimeProfileSupportedOnPositivePrimePowers A)
    (hB : PrimeProfileSupportedOnPositivePrimePowers B) :
    primeRadialFusion A B = positivePrimePowerProjection (A * B) := by
  unfold primeRadialFusion positivePrimePowerProjection
  apply congrArg arithmeticFunctionOfPrimePowerProfile
  funext x
  exact primeRadialRaySeries_mul_coeff_eq_dirichletConvolution A B x.1
    (apply_one_eq_zero_of_supportedOnPositivePrimePowers A hA)
    (apply_one_eq_zero_of_supportedOnPositivePrimePowers B hB) (x.2 + 1)

/-- The ray series of a fusion is the product of the two input ray series. -/
@[simp]
theorem primeRadialRaySeries_fusion
    (A B : ArithmeticFunction ℂ) (p : Nat.Primes) :
    primeRadialRaySeries (primeRadialFusion A B) p =
      primeRadialRaySeries A p * primeRadialRaySeries B p := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [primeRadialRaySeries]
  | succ n =>
      unfold primeRadialRaySeries
      rw [PowerSeries.coeff_mk]
      simp only [Nat.succ_ne_zero, if_false]
      change (primeRadialFusion A B) ((p : Nat) ^ (n + 1)) =
        PowerSeries.coeff (n + 1)
          (primeRadialRaySeries A p * primeRadialRaySeries B p)
      exact primePowerCoordinateProfile_primeRadialFusion A B (p, n)

@[simp]
theorem primeRadialRaySeries_add
    (A B : ArithmeticFunction ℂ) (p : Nat.Primes) :
    primeRadialRaySeries (A + B) p =
      primeRadialRaySeries A p + primeRadialRaySeries B p := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [primeRadialRaySeries]

@[simp]
theorem primeRadialRaySeries_smul
    (z : ℂ) (A : ArithmeticFunction ℂ) (p : Nat.Primes) :
    primeRadialRaySeries (z • A) p = z • primeRadialRaySeries A p := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [primeRadialRaySeries]

theorem primeRadialFusion_add_left
    (A B C : ArithmeticFunction ℂ) :
    primeRadialFusion (A + B) C =
      primeRadialFusion A C + primeRadialFusion B C := by
  unfold primeRadialFusion
  rw [← arithmeticFunctionOfPrimePowerProfile.map_add]
  apply congrArg arithmeticFunctionOfPrimePowerProfile
  funext x
  rw [primeRadialRaySeries_add, add_mul, map_add]
  rfl

theorem primeRadialFusion_smul_left
    (z : ℂ) (A B : ArithmeticFunction ℂ) :
    primeRadialFusion (z • A) B = z • primeRadialFusion A B := by
  unfold primeRadialFusion
  rw [← arithmeticFunctionOfPrimePowerProfile.map_smul]
  apply congrArg arithmeticFunctionOfPrimePowerProfile
  funext x
  rw [primeRadialRaySeries_smul, smul_mul_assoc, map_smul]
  rfl

theorem primeRadialFusion_comm
    (A B : ArithmeticFunction ℂ) :
    primeRadialFusion A B = primeRadialFusion B A := by
  unfold primeRadialFusion
  apply congrArg arithmeticFunctionOfPrimePowerProfile
  funext x
  rw [mul_comm]

theorem primeRadialFusion_assoc
    (A B C : ArithmeticFunction ℂ) :
    primeRadialFusion (primeRadialFusion A B) C =
      primeRadialFusion A (primeRadialFusion B C) := by
  change arithmeticFunctionOfPrimePowerProfile
      (fun x => PowerSeries.coeff (x.2 + 1)
        (primeRadialRaySeries (primeRadialFusion A B) x.1 *
          primeRadialRaySeries C x.1)) =
    arithmeticFunctionOfPrimePowerProfile
      (fun x => PowerSeries.coeff (x.2 + 1)
        (primeRadialRaySeries A x.1 *
          primeRadialRaySeries (primeRadialFusion B C) x.1))
  apply congrArg arithmeticFunctionOfPrimePowerProfile
  funext x
  rw [primeRadialRaySeries_fusion, primeRadialRaySeries_fusion, mul_assoc]

end

end GaloisForLFunctions.HTGeometry
