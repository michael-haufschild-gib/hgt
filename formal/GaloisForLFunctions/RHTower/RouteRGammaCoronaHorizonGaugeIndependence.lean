import GaloisForLFunctions.RHTower.RouteRDegreeSixGammaCoronaLocalGlobalFracture

/-!
# Route R Gamma-corona horizon gauge independence

The singular-corona globalization criterion does not depend on the arbitrary
`Encodable` normalization of the existing packet horizon.  For every nonzero
corona direction, the global action agrees with any finite source-local action
exactly when the same Gamma/Cartier port vanishes.

An intrinsic replacement is constructed directly from ordered prime labels:
the coefficient at `(p,q)` is `1/(p*q)`.  Its square summability, full support,
survival outside the finite arithmetic core, and invariance under orientation
swap are unconditional.  The original globalization statement is then proved
equivalent to globalization on this arithmetic horizon.

This removes horizon choice from the open Route R producer burden.  It does
not assume or prove port vanishing, centered-rate vanishing, critical-line
placement, same-fibre norm, source-dagger, or RH.
-/

open Complex Function Set Topology
open scoped ENNReal

namespace RHTower

noncomputable section

noncomputable local instance :
    DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

private def routeRCrossPrimePacketIndexOfPrime (p : Nat.Primes) :
    DeningerCalderonWittCrossPrimePacketIndex :=
  if hp : p = ⟨2, Nat.prime_two⟩ then
    ⟨(p, ⟨3, Nat.prime_three⟩), by
      intro h
      have hval := congrArg (fun r : Nat.Primes => r.1) h
      simp [hp] at hval⟩
  else
    ⟨(p, ⟨2, Nat.prime_two⟩), hp⟩

private theorem routeRCrossPrimePacketIndexOfPrime_first (p : Nat.Primes) :
    (routeRCrossPrimePacketIndexOfPrime p).1.1 = p := by
  rw [routeRCrossPrimePacketIndexOfPrime]
  split <;> rfl

private theorem routeRCrossPrimePacketIndexOfPrime_injective :
    Function.Injective routeRCrossPrimePacketIndexOfPrime := by
  intro p q h
  have hval := congrArg
    (fun i : DeningerCalderonWittCrossPrimePacketIndex => i.1.1) h
  simpa [routeRCrossPrimePacketIndexOfPrime_first] using hval

noncomputable local instance :
    Infinite DeningerCalderonWittCrossPrimePacketIndex :=
  Infinite.of_injective routeRCrossPrimePacketIndexOfPrime
    routeRCrossPrimePacketIndexOfPrime_injective

def routeRTwoThreeGammaSingularCoronaLiftAt
    (rho : XiDivisorSupport)
    (h : DeningerCalderonWittCrossPrimeSingularCorona) :
    DeningerCalderonWittCrossPrimeSingularCorona :=
  ccmRationalAdelicPrimeXiCartierCoefficient rho • h

theorem routeRTwoThreeGammaSingularCoronaLiftAt_ne_zero
    (rho : XiDivisorSupport)
    {h : DeningerCalderonWittCrossPrimeSingularCorona} (hh : h ≠ 0) :
    routeRTwoThreeGammaSingularCoronaLiftAt rho h ≠ 0 := by
  exact smul_ne_zero
    (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho) hh

theorem routeRTwoThreeGammaSingularCoronaAction_liftAt
    (rho : XiDivisorSupport)
    (h : DeningerCalderonWittCrossPrimeSingularCorona) :
    routeRTwoThreeGammaSingularCoronaAction rho
        (routeRTwoThreeGammaSingularCoronaLiftAt rho h) =
      routeRTwoThreeGammaCartierTransportPort rho • h := by
  rw [routeRTwoThreeGammaSingularCoronaAction,
    routeRTwoThreeGammaSingularCoronaLiftAt,
    LinearMap.smul_apply, LinearMap.id_apply, smul_smul,
    routeRTwoThreeGammaCartierTransportPort_eq]
  rfl

theorem routeRTwoThreeGammaCorona_global_eq_local_at_iff_port_eq_zero
    (rho : XiDivisorSupport)
    (h : DeningerCalderonWittCrossPrimeSingularCorona) (hh : h ≠ 0)
    (z : DeningerCalderonWittCrossPrimePacketHilbert) :
    routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaSingularCoronaLiftAt rho h) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho z) ↔
      routeRTwoThreeGammaCartierTransportPort rho = 0 := by
  rw [deningerCalderonWittCrossPrimeSingularCoronaClass_localPacketAction,
    routeRTwoThreeGammaSingularCoronaAction_liftAt]
  constructor
  · intro hzero
    exact (smul_eq_zero.mp hzero).resolve_right hh
  · intro hzero
    rw [hzero, zero_smul]

def routeRCrossPrimeArithmeticHorizonCoefficient
    (i : DeningerCalderonWittCrossPrimePacketIndex) : ℂ :=
  (((((i.1.1 : ℕ) : ℝ))⁻¹ * ((((i.1.2 : ℕ) : ℝ))⁻¹)) : ℝ)

theorem routeRCrossPrimeArithmeticHorizonCoefficient_ne_zero
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    routeRCrossPrimeArithmeticHorizonCoefficient i ≠ 0 := by
  rw [routeRCrossPrimeArithmeticHorizonCoefficient]
  exact_mod_cast mul_ne_zero
    (inv_ne_zero (by exact_mod_cast i.1.1.2.ne_zero))
    (inv_ne_zero (by exact_mod_cast i.1.2.2.ne_zero))

theorem routeRCrossPrimeArithmeticHorizonCoefficient_norm_sq
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    ‖routeRCrossPrimeArithmeticHorizonCoefficient i‖ ^ 2 =
      (((i.1.1 : ℕ) : ℝ) ^ 2)⁻¹ * (((i.1.2 : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hp : (0 : ℝ) < (i.1.1 : ℕ) := by exact_mod_cast i.1.1.2.pos
  have hq : (0 : ℝ) < (i.1.2 : ℕ) := by exact_mod_cast i.1.2.2.pos
  rw [routeRCrossPrimeArithmeticHorizonCoefficient,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (inv_pos.mpr hp) (inv_pos.mpr hq)),
    mul_pow, inv_pow, inv_pow]

theorem summable_norm_sq_routeRCrossPrimeArithmeticHorizonCoefficient :
    Summable (fun i : DeningerCalderonWittCrossPrimePacketIndex =>
      ‖routeRCrossPrimeArithmeticHorizonCoefficient i‖ ^ 2) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes =>
      (((p : ℕ) : ℝ) ^ 2)⁻¹) := by
    simpa [Function.comp_def] using
      hnat.comp_injective (i := fun p : Nat.Primes => (p : ℕ))
        Subtype.val_injective
  have hprod : Summable (fun pq : Nat.Primes × Nat.Primes =>
      (((pq.1 : ℕ) : ℝ) ^ 2)⁻¹ *
        (((pq.2 : ℕ) : ℝ) ^ 2)⁻¹) := by
    rw [summable_prod_of_nonneg (fun pq => mul_nonneg (by positivity) (by positivity))]
    constructor
    · intro p
      simpa using hprime.mul_left ((((p : ℕ) : ℝ) ^ 2)⁻¹)
    · simpa only [hprime.tsum_mul_left] using
        hprime.mul_right (∑' q : Nat.Primes, (((q : ℕ) : ℝ) ^ 2)⁻¹)
  have hsub := hprod.subtype (fun pq : Nat.Primes × Nat.Primes => pq.1 ≠ pq.2)
  refine (hsub.congr fun i => ?_)
  exact (routeRCrossPrimeArithmeticHorizonCoefficient_norm_sq i).symm

def routeRCrossPrimeArithmeticHorizon :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  ⟨routeRCrossPrimeArithmeticHorizonCoefficient, by
    apply memℓp_gen
    simpa using
      summable_norm_sq_routeRCrossPrimeArithmeticHorizonCoefficient⟩

@[simp]
theorem routeRCrossPrimeArithmeticHorizon_apply
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    routeRCrossPrimeArithmeticHorizon i =
      routeRCrossPrimeArithmeticHorizonCoefficient i :=
  rfl

def routeRCrossPrimePacketSwap
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    DeningerCalderonWittCrossPrimePacketIndex :=
  ⟨(i.1.2, i.1.1), Ne.symm i.2⟩

@[simp]
theorem routeRCrossPrimeArithmeticHorizonCoefficient_swap
    (i : DeningerCalderonWittCrossPrimePacketIndex) :
    routeRCrossPrimeArithmeticHorizonCoefficient
        (routeRCrossPrimePacketSwap i) =
      routeRCrossPrimeArithmeticHorizonCoefficient i := by
  simp [routeRCrossPrimeArithmeticHorizonCoefficient,
    routeRCrossPrimePacketSwap, mul_comm]

theorem routeRCrossPrimeArithmeticHorizon_not_mem_arithmeticCore :
    routeRCrossPrimeArithmeticHorizon ∉
      deningerCalderonWittCrossPrimeArithmeticPacketCore := by
  rintro ⟨x, hx⟩
  let a : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
    deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan.symm x
  have hsource :
      deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert x =
        deningerCalderonWittCrossPrimeAlgebraicPacketToHilbert a := by
    rw [show x =
        deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan a by
      exact
        (deningerCalderonWittCrossPrimeFinsuppEquivAlgebraicSourceSpan
          |>.apply_symm_apply x).symm]
    exact deningerCalderonWittCrossPrimeSourceSpanToPacketHilbert_finsupp a
  rw [hsource] at hx
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset a.support
  have hcoord := congrArg
    (fun z : DeningerCalderonWittCrossPrimePacketHilbert => z i) hx
  rw [deningerCalderonWittCrossPrimeAlgebraicPacketToHilbert_apply,
    Finsupp.notMem_support_iff.mp hi] at hcoord
  exact routeRCrossPrimeArithmeticHorizonCoefficient_ne_zero i hcoord.symm

def routeRCrossPrimeArithmeticSingularCoronaHorizon :
    DeningerCalderonWittCrossPrimeSingularCorona :=
  deningerCalderonWittCrossPrimeSingularCoronaClass
    routeRCrossPrimeArithmeticHorizon

theorem routeRCrossPrimeArithmeticSingularCoronaHorizon_ne_zero :
    routeRCrossPrimeArithmeticSingularCoronaHorizon ≠ 0 := by
  intro hzero
  exact routeRCrossPrimeArithmeticHorizon_not_mem_arithmeticCore
    ((Submodule.Quotient.mk_eq_zero _).1 hzero)

def routeRTwoThreeGammaArithmeticPacketPhysicalLift
    (rho : XiDivisorSupport) :
    DeningerCalderonWittCrossPrimePacketHilbert :=
  ccmRationalAdelicPrimeXiCartierCoefficient rho •
    routeRCrossPrimeArithmeticHorizon

def routeRTwoThreeGammaArithmeticSingularCoronaPhysicalLift
    (rho : XiDivisorSupport) :
    DeningerCalderonWittCrossPrimeSingularCorona :=
  routeRTwoThreeGammaSingularCoronaLiftAt rho
    routeRCrossPrimeArithmeticSingularCoronaHorizon

theorem routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_port_eq_zero
    (rho : XiDivisorSupport) :
    routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaArithmeticSingularCoronaPhysicalLift rho) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaArithmeticPacketPhysicalLift rho)) ↔
      routeRTwoThreeGammaCartierTransportPort rho = 0 := by
  exact routeRTwoThreeGammaCorona_global_eq_local_at_iff_port_eq_zero
    rho routeRCrossPrimeArithmeticSingularCoronaHorizon
      routeRCrossPrimeArithmeticSingularCoronaHorizon_ne_zero
      (routeRTwoThreeGammaArithmeticPacketPhysicalLift rho)

theorem routeRTwoThreeGammaCorona_original_globalization_iff_arithmetic :
    (∀ rho : XiDivisorSupport,
      routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaSingularCoronaPhysicalLift rho) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaPacketPhysicalLift rho))) ↔
    (∀ rho : XiDivisorSupport,
      routeRTwoThreeGammaSingularCoronaAction rho
          (routeRTwoThreeGammaArithmeticSingularCoronaPhysicalLift rho) =
        deningerCalderonWittCrossPrimeSingularCoronaClass
          (routeRTwoThreeGammaLocalPacketAction rho
            (routeRTwoThreeGammaArithmeticPacketPhysicalLift rho))) := by
  constructor
  · intro horiginal rho
    exact
      (routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_port_eq_zero rho).2
        ((routeRTwoThreeGammaCorona_global_eq_local_iff_port_eq_zero rho).1
          (horiginal rho))
  · intro harithmetic rho
    exact
      (routeRTwoThreeGammaCorona_global_eq_local_iff_port_eq_zero rho).2
        ((routeRTwoThreeGammaArithmeticCorona_global_eq_local_iff_port_eq_zero rho).1
          (harithmetic rho))

end

end RHTower
