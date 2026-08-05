import GaloisForLFunctions.RHTower.RouteRCorrectedMultiplierGammaOrientationDescent

/-!
# Prime-log essential cap and singular Stokes flatness

The corrected multiplier cap already carries the Kummer period `-log p`.
Multiplying its period-one Stokes readout by `-2` therefore cancels the
`1 / (2 log p)` attenuation of the physical Hodge-mate coefficient.  The
resulting fixed-orientation port is

`aρ (1 - p⁻¹) (2 - p⁻¹) cρ`,

where `aρ = 2 re ρ - 1` and `cρ` is the nonzero first Xi jet.  Along the
canonical enumeration of the primes it converges to the single essential
scalar `2 aρ cρ`.

Consequently cofinal singular Stokes flatness is exactly nullity of the
explicit cap at every ordinary prime.  This is an unconditional reduction,
not an assertion of flatness: a source proof of the flatness proposition is
the remaining producer.
-/

open Complex Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Nondivisive fixed-orientation singular readout of the explicit cap.  The
Kummer logarithm is already present in the cap landing. -/
def ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  -2 * ccmRationalAdelicPrimeRelativeH1StokesRegulator p
    (ccmRationalAdelicPrimeXiCentralBocksteinCapClass p rho)

/-- Prime-log transport exactly removes the local logarithmic attenuation. -/
theorem two_mul_primeLog_mul_hodgeMateCoefficient
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    2 * Real.log (p : ℝ) *
        ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho =
      primeDepthBVWoldXiCenteredRate rho *
        (1 - (p : ℝ)⁻¹) * (2 - (p : ℝ)⁻¹) := by
  rw [ccmRationalAdelicPrimeXiHodgeMateCoefficient,
    primeDepthBVWoldReesCoronaWeight_adjacent_eq,
    primeDepthBVWoldReesCoronaAdjacentAttenuation]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  field_simp [hlog]

/-- Exact coefficient-faithful port formula.  No division by the Xi jet or
by the physical Hodge coefficient is used. -/
theorem ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_eq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort p rho =
      ((primeDepthBVWoldXiCenteredRate rho *
        (1 - (p : ℝ)⁻¹) * (2 - (p : ℝ)⁻¹) : ℝ) : ℂ) *
          ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort,
    ccmRationalAdelicPrimeRelativeH1StokesRegulator_centralBocksteinCapClass,
    ccmRationalAdelicPrimeCorrectedMultiplierXiLanding_eq_signedKummerLanding,
    ccmRationalAdelicPrimeXiSignedKummerLanding_eq]
  have hcoefficient := congrArg (fun x : ℝ => (x : ℂ))
    (two_mul_primeLog_mul_hodgeMateCoefficient p rho)
  calc
    -2 * ((ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℂ) *
        (-(Real.log (p : ℝ) : ℂ) *
          ccmRationalAdelicPrimeXiCartierCoefficient rho)) =
      ((2 * Real.log (p : ℝ) *
        ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℝ) : ℂ) *
          ccmRationalAdelicPrimeXiCartierCoefficient rho := by
            push_cast
            ring
    _ = _ := congrArg (fun z : ℂ => z *
      ccmRationalAdelicPrimeXiCartierCoefficient rho) hcoefficient

/-- The unique constant corona channel left after prime-log transport. -/
def ccmRationalAdelicPrimeXiEssentialCapScalar
    (rho : XiDivisorSupport) : ℂ :=
  ((2 * primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) *
    ccmRationalAdelicPrimeXiCartierCoefficient rho

/-- Every cofinal sequence of ordinary primes sees the same essential cap
scalar. -/
theorem ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_tendsto
    (rho : XiDivisorSupport) (P : ℕ → Nat.Primes)
    (hP : Tendsto (fun n => ((P n : ℕ) : ℝ)) atTop atTop) :
    Tendsto
      (fun n => ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort (P n) rho)
      atTop (nhds (ccmRationalAdelicPrimeXiEssentialCapScalar rho)) := by
  have hq : Tendsto (fun n => (((P n : ℕ) : ℝ))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hP
  have hreal : Tendsto
      (fun n => primeDepthBVWoldXiCenteredRate rho *
        (1 - (((P n : ℕ) : ℝ))⁻¹) *
          (2 - (((P n : ℕ) : ℝ))⁻¹))
      atTop (nhds (2 * primeDepthBVWoldXiCenteredRate rho)) := by
    have ha : Tendsto
        (fun _ : ℕ => primeDepthBVWoldXiCenteredRate rho)
        atTop (nhds (primeDepthBVWoldXiCenteredRate rho)) :=
      tendsto_const_nhds
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (nhds 1) := tendsto_const_nhds
    have h2 : Tendsto (fun _ : ℕ => (2 : ℝ))
        atTop (nhds 2) := tendsto_const_nhds
    simpa [mul_comm] using ((ha.mul (h1.sub hq)).mul (h2.sub hq))
  have hcomplex := hreal.ofReal
  have hmul := hcomplex.mul_const
    (ccmRationalAdelicPrimeXiCartierCoefficient rho)
  convert hmul using 1
  · funext n
    rw [ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_eq]
  · rw [ccmRationalAdelicPrimeXiEssentialCapScalar]

/-- The essential scalar is faithful because the multiplicity-leading Xi jet
is nonzero. -/
theorem ccmRationalAdelicPrimeXiEssentialCapScalar_eq_zero_iff
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiEssentialCapScalar rho = 0 ↔
      primeDepthBVWoldXiCenteredRate rho = 0 := by
  rw [ccmRationalAdelicPrimeXiEssentialCapScalar, mul_eq_zero]
  constructor
  · rintro (h | h)
    · have hr : 2 * primeDepthBVWoldXiCenteredRate rho = 0 := by
        exact_mod_cast h
      exact (mul_eq_zero.mp hr).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
    · exact False.elim
        (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho h)
  · intro h
    left
    exact_mod_cast
      (mul_eq_zero.mpr (Or.inr h) :
        2 * primeDepthBVWoldXiCenteredRate rho = 0)

/-- Canonical increasing enumeration of ordinary primes. -/
def routeRPrimeLogCapPrimeEnumeration (n : ℕ) : Nat.Primes :=
  ⟨Nat.nth Nat.Prime n, Nat.prime_nth_prime n⟩

/-- Canonical prime enumeration is cofinal in the positive real scale. -/
theorem routeRPrimeLogCapPrimeEnumeration_tendsto :
    Tendsto
      (fun n => ((routeRPrimeLogCapPrimeEnumeration n : ℕ) : ℝ))
      atTop atTop := by
  apply Filter.tendsto_atTop_mono
    (f := fun n : ℕ => (n : ℝ))
    (g := fun n : ℕ =>
      ((routeRPrimeLogCapPrimeEnumeration n : ℕ) : ℝ))
  · intro n
    exact_mod_cast (show n ≤ Nat.nth Nat.Prime n by
      exact (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n))
  · exact tendsto_natCast_atTop_atTop

/-- Independent fixed-source-orientation singular Stokes law: the complete
prime-log cap port is cofinally flat.  This proposition mentions neither a
critical-line condition nor pointwise cap nullity. -/
def CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat
    (rho : XiDivisorSupport) : Prop :=
  Tendsto
    (fun n => ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort
      (routeRPrimeLogCapPrimeEnumeration n) rho)
    atTop (nhds 0)

/-- Singular flatness is precisely zero horizontal rate; infinite-rank
transport leaves no additional obstruction channel. -/
theorem ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff
    (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho ↔
      primeDepthBVWoldXiCenteredRate rho = 0 := by
  have hlimit :=
    ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_tendsto rho
      routeRPrimeLogCapPrimeEnumeration
      routeRPrimeLogCapPrimeEnumeration_tendsto
  constructor
  · intro hflat
    have hessential :
        ccmRationalAdelicPrimeXiEssentialCapScalar rho = 0 :=
      tendsto_nhds_unique hlimit hflat
    exact
      (ccmRationalAdelicPrimeXiEssentialCapScalar_eq_zero_iff rho).mp
        hessential
  · intro hzero
    have hessential :=
      (ccmRationalAdelicPrimeXiEssentialCapScalar_eq_zero_iff rho).mpr
        hzero
    rw [hessential] at hlimit
    exact hlimit

/-- A source proof of singular flatness annihilates the explicit cap at every
ordinary prime. -/
theorem ccmRationalAdelicPrimeXiCentralBocksteinCapClass_eq_zero_of_singularStokesFlat
    (rho : XiDivisorSupport)
    (hflat : CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho)
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeXiCentralBocksteinCapClass p rho = 0 := by
  apply
    (ccmRationalAdelicPrimeXiCentralBocksteinCapClass_eq_zero_iff_hodgeMate
      p rho).2
  apply
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half
      p rho).2
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1
    ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).1
      hflat)

/-- Exact all-prime form: cofinal singular flatness and nullity of every
explicit central-Bockstein cap are the same statement. -/
theorem ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff_all_cap_zero
    (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho ↔
      ∀ p : Nat.Primes,
        ccmRationalAdelicPrimeXiCentralBocksteinCapClass p rho = 0 := by
  constructor
  · exact fun h p =>
      ccmRationalAdelicPrimeXiCentralBocksteinCapClass_eq_zero_of_singularStokesFlat
        rho h p
  · intro h
    let p : Nat.Primes := ⟨2, by norm_num⟩
    have hK : ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 :=
      (ccmRationalAdelicPrimeXiCentralBocksteinCapClass_eq_zero_iff_hodgeMate
        p rho).1 (h p)
    have hrate : primeDepthBVWoldXiCenteredRate rho = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2
        ((ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half
          p rho).1 hK)
    exact
      (ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).2
        hrate

/-- Global cofinal fixed-orientation Stokes flatness is the exact remaining
RH-strength source statement. -/
theorem forall_ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff_RH :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_RH
    (⟨2, by norm_num⟩ : Nat.Primes)]
  apply forall_congr'
  intro rho
  exact
    (ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).trans
      ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).trans
        ((ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half
          (⟨2, by norm_num⟩ : Nat.Primes) rho).symm.trans
        (ccmRationalAdelicPrimeXiCorrectedMultiplierGammaOrientationDescent_iff_hodgeMate
          (⟨2, by norm_num⟩ : Nat.Primes) rho).symm))

end

end RHTower
