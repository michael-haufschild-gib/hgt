import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapSingularStokesLaw
import GaloisForLFunctions.RHTower.DeningerRealKummerArakelovBoundary
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# Route R prime-cap Arakelov boundary law

The prime-log essential cap has removed the local Kummer attenuation.  This module puts those
physical cap values on a literal pre-divisor Arakelov source.

For every ordinary prime `p`, normalize the prime divisor by `1 / log p`.  Its finite Kummer trace
is exactly one, so its Arakelov infinity coordinate is exactly minus one, independently of `p`.
The physical finite trace sends this normalized divisor to the explicit Route R prime-log cap.
Consequently, one infinity coefficient annihilates all source Arakelov boundaries only if all
prime caps agree.  Equality at the two source-fixed primes `2` and `3` already forces neutral grade:
their exact attenuation factors are `3/4` and `10/9`, while the Xi Cartier coefficient is nonzero.

This constructs a different, all-prime relative producer interface.  It replaces a same-fibre norm
equality at every prime by one explicit infinity-corrected boundary character.  The final
classification is honest: annihilation of that character is equivalent to neutral grade, and its
global form is equivalent to RH.  The remaining arithmetic theorem is to derive the displayed
boundary annihilation from the pre-divisor singular Cartier comparison; it is not assumed here.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Unit-trace prime divisors and their common infinity face -/

/-- Finite Kummer trace on ordinary-prime divisors. -/
def routeRPrimeFiniteTrace : (Nat.Primes →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun p : Nat.Primes => Real.log (p : ℝ))

/-- Prime divisor normalized to have finite Kummer trace one. -/
def routeRNormalizedPrimeDivisor (p : Nat.Primes) : Nat.Primes →₀ ℝ :=
  Finsupp.single p (Real.log (p : ℝ))⁻¹

/-- Every normalized ordinary-prime divisor has finite trace one. -/
theorem routeRPrimeFiniteTrace_normalizedPrimeDivisor (p : Nat.Primes) :
    routeRPrimeFiniteTrace (routeRNormalizedPrimeDivisor p) = 1 := by
  rw [routeRPrimeFiniteTrace, routeRNormalizedPrimeDivisor,
    Finsupp.linearCombination_single, smul_eq_mul]
  exact inv_mul_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one
    (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.ne_one))

/-- Prime-divisor Arakelov boundary: finite divisor plus the negative finite trace at infinity. -/
def routeRPrimeArakelovBoundary :
    (Nat.Primes →₀ ℝ) →ₗ[ℝ] ((Nat.Primes →₀ ℝ) × ℝ) where
  toFun d := (d, -routeRPrimeFiniteTrace d)
  map_add' d e := by
    apply Prod.ext
    · rfl
    · change -(routeRPrimeFiniteTrace (d + e)) =
        -routeRPrimeFiniteTrace d + -routeRPrimeFiniteTrace e
      rw [map_add]
      abel
  map_smul' c d := by ext <;> simp

/-- Unit-trace normalization gives the same infinity coordinate `-1` at every prime. -/
theorem routeRPrimeArakelovBoundary_normalizedPrimeDivisor (p : Nat.Primes) :
    routeRPrimeArakelovBoundary (routeRNormalizedPrimeDivisor p) =
      (routeRNormalizedPrimeDivisor p, -1) := by
  ext
  · rfl
  · simp [routeRPrimeArakelovBoundary,
      routeRPrimeFiniteTrace_normalizedPrimeDivisor]

/-! ## Physical cap trace and infinity-corrected character -/

/-- Physical finite trace: the Kummer logarithm times the already normalized essential cap port. -/
def routeRPhysicalEssentialCapFiniteTrace (rho : XiDivisorSupport) :
    (Nat.Primes →₀ ℝ) →ₗ[ℝ] ℂ :=
  Finsupp.linearCombination ℝ (fun p : Nat.Primes =>
    Real.log (p : ℝ) • ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort p rho)

/-- Unit-trace prime normalization reads the literal prime-log essential cap. -/
theorem routeRPhysicalEssentialCapFiniteTrace_normalizedPrimeDivisor
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    routeRPhysicalEssentialCapFiniteTrace rho (routeRNormalizedPrimeDivisor p) =
      ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort p rho := by
  rw [routeRPhysicalEssentialCapFiniteTrace, routeRNormalizedPrimeDivisor,
    Finsupp.linearCombination_single, smul_smul]
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.ne_one)
  rw [inv_mul_cancel₀ hlog, one_smul]

/-- Infinity-corrected physical cap character. -/
def routeRPhysicalCapArakelovCharacter (rho : XiDivisorSupport) (A : ℂ) :
    ((Nat.Primes →₀ ℝ) × ℝ) →ₗ[ℝ] ℂ where
  toFun z := routeRPhysicalEssentialCapFiniteTrace rho z.1 + z.2 • A
  map_add' z w := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel
  map_smul' c z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, smul_smul,
      RingHom.id_apply]
    congr 1

/-- Source-native singular boundary law: one infinity coefficient makes the physical cap character
annihilate every prime-divisor Arakelov boundary. -/
def CCMRationalAdelicXiPrimeCapArakelovBoundaryLaw
    (rho : XiDivisorSupport) : Prop :=
  ∃ A : ℂ, (routeRPhysicalCapArakelovCharacter rho A).comp
    routeRPrimeArakelovBoundary = 0

/-- Boundary annihilation makes every normalized prime cap equal to the same infinity coefficient. -/
theorem primeCap_eq_infinity_of_boundaryLaw
    (rho : XiDivisorSupport)
    (A : ℂ)
    (hA : (routeRPhysicalCapArakelovCharacter rho A).comp
      routeRPrimeArakelovBoundary = 0)
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort p rho = A := by
  have hz := LinearMap.congr_fun hA (routeRNormalizedPrimeDivisor p)
  rw [LinearMap.comp_apply, LinearMap.zero_apply,
    routeRPrimeArakelovBoundary_normalizedPrimeDivisor] at hz
  change routeRPhysicalEssentialCapFiniteTrace rho
      (routeRNormalizedPrimeDivisor p) + (-1 : ℝ) • A = 0 at hz
  rw [routeRPhysicalEssentialCapFiniteTrace_normalizedPrimeDivisor] at hz
  have hz' :
      ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort p rho - A = 0 := by
    simpa [sub_eq_add_neg] using hz
  exact sub_eq_zero.mp hz'

/-! ## The two-prime rigidity gate -/

/-- Canonical first ordinary prime. -/
def routeRTwoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- Canonical second ordinary prime. -/
def routeRThreePrime : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- Equality of the normalized cap at the two fixed primes `2` and `3` forces neutral grade. -/
theorem centeredRate_eq_zero_of_two_three_cap_eq
    (rho : XiDivisorSupport)
    (h : ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort routeRTwoPrime rho =
      ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort routeRThreePrime rho) :
    primeDepthBVWoldXiCenteredRate rho = 0 := by
  have hjet := ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho
  have hscaled :
      ((((-(13 : ℝ) / 36) * primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) *
        ccmRationalAdelicPrimeXiCartierCoefficient rho) = 0 := by
    calc
      ((((-(13 : ℝ) / 36) * primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) *
          ccmRationalAdelicPrimeXiCartierCoefficient rho) =
        ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort routeRTwoPrime rho -
          ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort routeRThreePrime rho := by
            rw [ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_eq,
              ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_eq]
            dsimp [routeRTwoPrime, routeRThreePrime]
            norm_num
            push_cast
            ring
      _ = 0 := sub_eq_zero.mpr h
  have hrealCast :
      (((-(13 : ℝ) / 36) * primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_right hjet
  have hreal :
      (-(13 : ℝ) / 36) * primeDepthBVWoldXiCenteredRate rho = 0 := by
    exact_mod_cast hrealCast
  exact (mul_eq_zero.mp hreal).resolve_left (by norm_num)

/-- One all-prime Arakelov boundary law annihilates the Route R centered rate. -/
theorem centeredRate_eq_zero_of_primeCapArakelovBoundaryLaw
    (rho : XiDivisorSupport)
    (h : CCMRationalAdelicXiPrimeCapArakelovBoundaryLaw rho) :
    primeDepthBVWoldXiCenteredRate rho = 0 := by
  rcases h with ⟨A, hA⟩
  apply centeredRate_eq_zero_of_two_three_cap_eq rho
  rw [primeCap_eq_infinity_of_boundaryLaw rho A hA routeRTwoPrime,
    primeCap_eq_infinity_of_boundaryLaw rho A hA routeRThreePrime]

/-! ## Exact logical classification -/

/-- At neutral grade the zero infinity coefficient annihilates every source boundary. -/
theorem primeCapArakelovBoundaryLaw_of_centeredRate_eq_zero
    (rho : XiDivisorSupport)
    (h : primeDepthBVWoldXiCenteredRate rho = 0) :
    CCMRationalAdelicXiPrimeCapArakelovBoundaryLaw rho := by
  refine ⟨0, ?_⟩
  apply LinearMap.ext
  intro d
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  change routeRPhysicalEssentialCapFiniteTrace rho d +
      (-routeRPrimeFiniteTrace d) • (0 : ℂ) = 0
  simp only [smul_zero, add_zero]
  rw [routeRPhysicalEssentialCapFiniteTrace]
  rw [Finsupp.linearCombination_apply]
  simp [ccmRationalAdelicPrimeXiPrimeLogEssentialCapPort_eq, h]

/-- The explicit Arakelov boundary law is exactly neutral grade. -/
theorem primeCapArakelovBoundaryLaw_iff_centeredRate_eq_zero
    (rho : XiDivisorSupport) :
    CCMRationalAdelicXiPrimeCapArakelovBoundaryLaw rho ↔
      primeDepthBVWoldXiCenteredRate rho = 0 :=
  ⟨centeredRate_eq_zero_of_primeCapArakelovBoundaryLaw rho,
    primeCapArakelovBoundaryLaw_of_centeredRate_eq_zero rho⟩

/-- Global all-prime Arakelov cap boundary law. -/
def CCMRationalAdelicXiGlobalPrimeCapArakelovBoundaryLaw : Prop :=
  ∀ rho : XiDivisorSupport, CCMRationalAdelicXiPrimeCapArakelovBoundaryLaw rho

/-- **Route R endpoint.**  Global source-compatible Arakelov boundary annihilation is RH. -/
theorem globalPrimeCapArakelovBoundaryLaw_iff_riemannHypothesis :
    CCMRationalAdelicXiGlobalPrimeCapArakelovBoundaryLaw ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mp
      ((primeCapArakelovBoundaryLaw_iff_centeredRate_eq_zero rho).mp (h rho))
  · intro hRH rho
    apply (primeCapArakelovBoundaryLaw_iff_centeredRate_eq_zero rho).mpr
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
