import GaloisForLFunctions.HTGeometry.PaperPrimeConstantProjection

/-!
# The literal Möbius Euler factor under the native prime flow

The p-free coefficient is an actual element of the full prime constant ring.
The arithmetic derivative, Euler factor and formal transported factor below
are identities in the native convolution algebra, before any analytic handoff.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The prime derivative of Möbius is minus its literal p-free restriction. -/
theorem paperMoebius_prime_derivative_eq_projection (p : Nat.Primes) :
    primeArithmeticDerivation (p : ℕ) p.property
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) =
      -(paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) := by
  have hconstant : primeArithmeticDerivation (p : ℕ) p.property
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) ∈ paperPrimeConstants p :=
    paperMoebius_prime_iterate_two p
  ext n
  rw [ArithmeticFunction.neg_apply, paperPrimeConstantProjection_apply]
  by_cases hn : (p : ℕ) ∣ n
  · rw [if_pos hn, neg_zero]
    exact (paperPrimeConstants_mem_iff p _).mp hconstant n hn
  · rw [if_neg hn]
    have hcop := (p.property.coprime_iff_not_dvd.mpr hn).symm
    have hmul := (ArithmeticFunction.isMultiplicative_moebius.intCast
      (R := ℂ)).map_mul_of_coprime hcop
    have h := paperPrimeArithmetic_iterate_apply p
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) n 1
    simpa [Nat.factorization_eq_zero_of_not_dvd hn, hmul,
      ArithmeticFunction.intCoe_apply, ArithmeticFunction.moebius_apply_prime p.property]
      using h

/-- The p-free Möbius and zeta coefficients are inverse in the ambient convolution algebra. -/
theorem paperMoebius_zeta_prime_constants_inverse (p : Nat.Primes) :
    (paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) *
      (paperPrimeConstantProjection p
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) = 1 :=
  congrArg Subtype.val (paperPrimeConstantProjection_moebius_mul_zeta p)

/-- The native Möbius function has its literal one-prime Euler factor. -/
theorem paperMoebius_prime_euler_factor (p : Nat.Primes) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ) =
      (1 - paperPrimeCoordinate p) *
        (paperPrimeConstantProjection p
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) := by
  let a := paperPrimeConstantProjection p
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)
  let g := (ArithmeticFunction.moebius : ArithmeticFunction ℂ) -
    (1 - paperPrimeCoordinate p) * (a : ArithmeticFunction ℂ)
  have ha : primeArithmeticDerivation (p : ℕ) p.property
      (a : ArithmeticFunction ℂ) = 0 := a.property
  have hx : primeArithmeticDerivation (p : ℕ) p.property (paperPrimeCoordinate p) = 1 := by
    simp [primeArithmeticDerivation_apply, paperPrimeCoordinate_primeDeriv]
  have hone : primeArithmeticDerivation (p : ℕ) p.property 1 = 0 := by simp
  have hg : g ∈ paperPrimeConstants p := by
    change primeArithmeticDerivation (p : ℕ) p.property g = 0
    dsimp only [g]
    rw [map_sub, Derivation.leibniz, ha, map_sub, hone, hx,
      paperMoebius_prime_derivative_eq_projection]
    change -(a : ArithmeticFunction ℂ) - ((1 - paperPrimeCoordinate p) * 0 +
      (a : ArithmeticFunction ℂ) * (0 - 1)) = 0
    ring
  have hfix := paperPrimeConstantProjection_constant p ⟨g, hg⟩
  have hzero : paperPrimeConstantProjection p g = 0 := by
    dsimp only [g]
    rw [map_sub, map_mul, map_sub, map_one, paperPrimeConstantProjection_coordinate,
      paperPrimeConstantProjection_constant]
    apply Subtype.ext
    change (a : ArithmeticFunction ℂ) - (1 - 0) * (a : ArithmeticFunction ℂ) = 0
    ring
  exact sub_eq_zero.mp (congrArg Subtype.val (hfix.symm.trans hzero))

/-- Removing the Euler factor from zeta gives the literal p-free zeta coefficient. -/
theorem paperZeta_prime_euler_factor (p : Nat.Primes) :
    (1 - paperPrimeCoordinate p) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) =
        (paperPrimeConstantProjection p
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f *
      (paperPrimeConstantProjection p
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [paperMoebius_prime_euler_factor p] at h
  have he : ((1 - paperPrimeCoordinate p) *
      (paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) *
      (paperPrimeConstantProjection p
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) =
      ((1 - paperPrimeCoordinate p) * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) *
        ((paperPrimeConstantProjection p
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) *
        (paperPrimeConstantProjection p
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ)) := by ring
  rw [he, paperMoebius_zeta_prime_constants_inverse, mul_one, one_mul] at h
  exact h

/-- The formal Möbius orbit changes only the one-prime Euler factor. -/
theorem paperMoebius_formal_prime_euler_factor (p : Nat.Primes) :
    paperArithmeticPrimeFormalFlow p (ArithmeticFunction.moebius : ArithmeticFunction ℂ) =
      (PowerSeries.C (1 - paperPrimeCoordinate p) - PowerSeries.X) *
        PowerSeries.C (paperPrimeConstantProjection p
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) := by
  have hC := congrArg (PowerSeries.C (R := ArithmeticFunction ℂ))
    (paperMoebius_prime_euler_factor p)
  rw [map_mul] at hC
  rw [paperMoebius_formal_prime_orbit, paperMoebius_prime_derivative_eq_projection, map_neg]
  rw [hC]
  ring

/-- Zeta's formal orbit has the reciprocal transported Euler factor. -/
theorem paperZeta_formal_prime_euler_factor (p : Nat.Primes) :
    (PowerSeries.C (1 - paperPrimeCoordinate p) - PowerSeries.X) *
      paperArithmeticPrimeFormalFlow p (ArithmeticFunction.zeta : ArithmeticFunction ℂ) =
        PowerSeries.C (paperPrimeConstantProjection p
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) := by
  have h := congrArg (fun f : PowerSeries (ArithmeticFunction ℂ) => f *
      PowerSeries.C (paperPrimeConstantProjection p
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ))
    (paperMoebius_zeta_formal_prime_inverse p)
  rw [paperMoebius_formal_prime_euler_factor p] at h
  have he : ((PowerSeries.C (1 - paperPrimeCoordinate p) - PowerSeries.X) *
      PowerSeries.C (paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) *
      paperArithmeticPrimeFormalFlow p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) *
      PowerSeries.C (paperPrimeConstantProjection p
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) =
      ((PowerSeries.C (1 - paperPrimeCoordinate p) - PowerSeries.X) *
        paperArithmeticPrimeFormalFlow p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) *
      (PowerSeries.C (paperPrimeConstantProjection p
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) *
        PowerSeries.C (paperPrimeConstantProjection p
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ)) := by ring
  rw [he, ← map_mul, paperMoebius_zeta_prime_constants_inverse, map_one, mul_one, one_mul] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
