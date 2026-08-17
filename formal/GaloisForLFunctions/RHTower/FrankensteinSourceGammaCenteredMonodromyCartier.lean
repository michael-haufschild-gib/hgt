import GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationPluckerLanding
import GaloisForLFunctions.RHTower.RouteRRationalCartierPrimeDilationLanding
import GaloisForLFunctions.RHTower.SourceGammaNaturalitySharedGhostProducer
import GaloisForLFunctions.Hurwitz.MonodromyScalar

/-!
# Source/Gamma centered monodromy and rational Cartier descent

The literal theta-cusp atom has half-density spin: its complex logarithmic continuation is
anti-periodic under `2 * pi * I` and periodic under `4 * pi * I`.  Its restriction to the real
axis is exactly the existing physical theta source atom, with its integer label retained.

For an actual Xi divisor, the prime-translation energy extends to the complex logarithmic
character

`E_rho(L) = exp (-(2 Re(rho) - 1) L)`.

Its `2 * pi * I` monodromy is the Hurwitz character of the *actual centered grade*.  Descent is
therefore equivalent to integral grade.  Xi's open critical strip upgrades this to grade zero.
The same descent constructs both the coefficient-faithful rational Cartier landing and the
genuine `(2,3)` source-natural Gamma reporter.

No descent premise is asserted.  The module proves the source spin law, exact monodromy, and the
complete cross-corpus consumer chain.  It also corrects the stale claim that the exact real grade
has no integral-lattice realization: rational Cartier valuation and Hurwitz monodromy provide two.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Literal complex theta source and its spin period -/

/-- Entire complexification of the polynomial-Gaussian theta-cusp seed. -/
private def thetaCuspComplexSeed (z : ℂ) : ℂ :=
  2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * z ^ 4 - 3 * z ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * z ^ 2)

/-- One integer-labelled complex logarithmic theta-cusp source atom. -/
def thetaCuspComplexSourceTerm (z : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (z / 2) * thetaCuspComplexSeed ((n : ℂ) * Complex.exp z)

theorem complex_exp_two_pi_mul_I :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨1, by push_cast; ring⟩

theorem complex_exp_pi_mul_I :
    Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := by
  rw [Complex.exp_pi_mul_I]

/-- The literal theta atom is a half-density spinor on the punctured scale plane. -/
theorem thetaCuspComplexSourceTerm_add_two_pi_I
    (z : ℂ) (n : ℕ) :
    thetaCuspComplexSourceTerm
        (z + 2 * (Real.pi : ℂ) * Complex.I) n =
      -thetaCuspComplexSourceTerm z n := by
  rw [thetaCuspComplexSourceTerm, thetaCuspComplexSourceTerm]
  have hexp : Complex.exp (z + 2 * (Real.pi : ℂ) * Complex.I) =
      Complex.exp z := by
    rw [Complex.exp_add, complex_exp_two_pi_mul_I, mul_one]
  rw [hexp]
  have hhalf :
      Complex.exp ((z + 2 * (Real.pi : ℂ) * Complex.I) / 2) =
        -Complex.exp (z / 2) := by
    rw [show (z + 2 * (Real.pi : ℂ) * Complex.I) / 2 =
        z / 2 + (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_add, complex_exp_pi_mul_I]
    ring
  rw [hhalf]
  ring

/-- The same labelled atom is single-valued on the metaplectic double cover. -/
theorem thetaCuspComplexSourceTerm_add_four_pi_I
    (z : ℂ) (n : ℕ) :
    thetaCuspComplexSourceTerm
        (z + 4 * (Real.pi : ℂ) * Complex.I) n =
      thetaCuspComplexSourceTerm z n := by
  rw [show z + 4 * (Real.pi : ℂ) * Complex.I =
      (z + 2 * (Real.pi : ℂ) * Complex.I) +
        2 * (Real.pi : ℂ) * Complex.I by ring,
    thetaCuspComplexSourceTerm_add_two_pi_I,
    thetaCuspComplexSourceTerm_add_two_pi_I, neg_neg]

private theorem thetaCuspComplexSeed_ofReal (x : ℝ) :
    thetaCuspComplexSeed (x : ℂ) = (thetaCuspSeed x : ℂ) := by
  rw [thetaCuspComplexSeed, thetaCuspSeed]
  have hexponent :
      -(Real.pi : ℂ) * (x : ℂ) ^ 2 =
        ((-Real.pi * x ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexponent, ← Complex.ofReal_exp]
  push_cast
  ring

/-- Complex source is coefficient-faithful to the pre-existing real physical source term. -/
theorem thetaCuspComplexSourceTerm_ofReal (x : ℝ) (n : ℕ) :
    thetaCuspComplexSourceTerm (x : ℂ) n =
      (thetaCuspSourceTerm x n : ℂ) := by
  rw [thetaCuspComplexSourceTerm, thetaCuspSourceTerm]
  have hhalf : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have harg : (n : ℂ) * Complex.exp (x : ℂ) =
      (((n : ℝ) * Real.exp x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
    norm_cast
  rw [hhalf, ← Complex.ofReal_exp, harg, thetaCuspComplexSeed_ofReal]
  norm_cast

/-! ## Exact Xi-grade character and its arithmetic descent -/

/-- Complex logarithmic continuation of the actual centered Xi prime-translation energy. -/
def xiCenteredLogCharacter (rho : XiDivisorSupport) (L : ℂ) : ℂ :=
  Complex.exp (-((primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) * L)

theorem xiCenteredLogCharacter_add (rho : XiDivisorSupport) (L M : ℂ) :
    xiCenteredLogCharacter rho (L + M) =
      xiCenteredLogCharacter rho L * xiCenteredLogCharacter rho M := by
  rw [xiCenteredLogCharacter, xiCenteredLogCharacter, xiCenteredLogCharacter]
  rw [show -((primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) * (L + M) =
      -((primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) * L +
        -((primeDepthBVWoldXiCenteredRate rho : ℝ) : ℂ) * M by ring,
    Complex.exp_add]

/-- A full imaginary log-scale turn carries exactly the Hurwitz monodromy of the centered grade. -/
theorem xiCenteredLogCharacter_add_two_pi_I (rho : XiDivisorSupport) (L : ℂ) :
    xiCenteredLogCharacter rho (L + 2 * (Real.pi : ℂ) * Complex.I) =
      HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ) *
        xiCenteredLogCharacter rho L := by
  rw [xiCenteredLogCharacter_add]
  have hperiod :
      xiCenteredLogCharacter rho (2 * (Real.pi : ℂ) * Complex.I) =
        HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ) := by
    rw [HurwitzOrbit.monoScalar, xiCenteredLogCharacter]
    congr 1
    ring
  rw [hperiod]
  ring

/-- The FE/Schwarz Hurwitz-character quotient cancels height and retains exactly the centered
horizontal grade.  This is the non-equivariant two-orientation carrier required by the producer. -/
theorem hurwitz_feSchwarz_orientationQuotient_eq_centeredRate
    (rho : XiDivisorSupport) :
    HurwitzOrbit.monoScalar (rho : ℂ) /
        HurwitzOrbit.monoScalar (1 - (starRingEnd ℂ) (rho : ℂ)) =
      HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ) := by
  rw [HurwitzOrbit.monoScalar, HurwitzOrbit.monoScalar,
    HurwitzOrbit.monoScalar, div_eq_mul_inv, ← Complex.exp_neg,
    ← Complex.exp_add]
  congr 1
  rw [primeDepthBVWoldXiCenteredRate]
  apply Complex.ext <;> simp
  ring

/-- Source/Gamma target: the actual centered character descends through the complex log cover. -/
def XiCenteredLogCharacterDescends (rho : XiDivisorSupport) : Prop :=
  ∀ L : ℂ,
    xiCenteredLogCharacter rho (L + 2 * (Real.pi : ℂ) * Complex.I) =
      xiCenteredLogCharacter rho L

/-- Hurwitz monodromy embeds the exact real centered grade in the integral lattice. -/
theorem xiCenteredLogCharacterDescends_iff_integer (rho : XiDivisorSupport) :
    XiCenteredLogCharacterDescends rho ↔
      ∃ k : ℤ, primeDepthBVWoldXiCenteredRate rho = (k : ℝ) := by
  constructor
  · intro h
    have hzero := h 0
    rw [xiCenteredLogCharacter_add_two_pi_I] at hzero
    have hchar0 : xiCenteredLogCharacter rho 0 = 1 := by
      simp [xiCenteredLogCharacter]
    rw [hchar0, mul_one] at hzero
    obtain ⟨k, hk⟩ :=
      (HurwitzOrbit.monoScalar_eq_one_iff
        (primeDepthBVWoldXiCenteredRate rho : ℂ)).mp hzero
    refine ⟨k, ?_⟩
    exact_mod_cast hk
  · rintro ⟨k, hk⟩ L
    rw [xiCenteredLogCharacter_add_two_pi_I]
    have hmono :
        HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ) = 1 := by
      apply (HurwitzOrbit.monoScalar_eq_one_iff _).2
      exact ⟨k, by exact_mod_cast hk⟩
    rw [hmono, one_mul]

/-- Triviality of the coefficient-faithful FE/Schwarz orientation quotient is exactly descent of
the centered log character. -/
theorem hurwitz_feSchwarz_orientationQuotient_eq_one_iff_descends
    (rho : XiDivisorSupport) :
    HurwitzOrbit.monoScalar (rho : ℂ) /
        HurwitzOrbit.monoScalar (1 - (starRingEnd ℂ) (rho : ℂ)) = 1 ↔
      XiCenteredLogCharacterDescends rho := by
  rw [hurwitz_feSchwarz_orientationQuotient_eq_centeredRate]
  constructor
  · intro hmono
    obtain ⟨k, hk⟩ :=
      (HurwitzOrbit.monoScalar_eq_one_iff
        (primeDepthBVWoldXiCenteredRate rho : ℂ)).mp hmono
    apply (xiCenteredLogCharacterDescends_iff_integer rho).2
    exact ⟨k, by exact_mod_cast hk⟩
  · intro h
    obtain ⟨k, hk⟩ :=
      (xiCenteredLogCharacterDescends_iff_integer rho).1 h
    apply (HurwitzOrbit.monoScalar_eq_one_iff _).2
    exact ⟨k, by exact_mod_cast hk⟩

/-- Xi's open critical strip turns integral centered monodromy into neutral grade. -/
theorem xiCenteredLogCharacterDescends_iff_centeredRate_eq_zero
    (rho : XiDivisorSupport) :
    XiCenteredLogCharacterDescends rho ↔
      primeDepthBVWoldXiCenteredRate rho = 0 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ :=
      (xiCenteredLogCharacterDescends_iff_integer rho).mp h
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    have hkLower : (-1 : ℝ) < (k : ℝ) := by
      rw [← hk, primeDepthBVWoldXiCenteredRate]
      linarith
    have hkUpper : (k : ℝ) < 1 := by
      rw [← hk, primeDepthBVWoldXiCenteredRate]
      linarith
    have hkZero : k = 0 := by
      have hLowerInt : (-1 : ℤ) < k := by exact_mod_cast hkLower
      have hUpperInt : k < 1 := by exact_mod_cast hkUpper
      omega
    simpa [hkZero] using hk
  · intro h
    apply (xiCenteredLogCharacterDescends_iff_integer rho).2
    exact ⟨0, by simpa using h⟩

/-- On a retained prime log, the complex character is exactly the genuine theta translation
energy, not a divisor-fitted replacement. -/
theorem xiCenteredLogCharacter_at_primeLog_eq_thetaEnergy
    (q : XiZeroCopy) (p : Nat.Primes) :
    xiCenteredLogCharacter q.1 (Real.log (p : ℝ) : ℂ) =
      (HedenmalmThetaSource.frankensteinThetaPrimeTranslationEnergy q p : ℂ) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [HedenmalmThetaSource.frankensteinThetaPrimeTranslationEnergy_eq,
    Real.rpow_def_of_pos hp, xiCenteredLogCharacter]
  have hexponent :
      -((primeDepthBVWoldXiCenteredRate q.1 : ℝ) : ℂ) *
          (Real.log (p : ℝ) : ℂ) =
        ((Real.log (p : ℝ) *
          -primeDepthBVWoldXiCenteredRate q.1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexponent, ← Complex.ofReal_exp]

/-! ## Frankenstein consumer chain -/

/-- Centered monodromy descent and coefficient-faithful rational Cartier landing are the same
pointwise producer. -/
theorem xiCenteredLogCharacterDescends_iff_rationalCartierLanding
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    XiCenteredLogCharacterDescends rho ↔
      CCMRationalAdelicPrimeXiRationalCartierLanding p rho := by
  rw [xiCenteredLogCharacterDescends_iff_centeredRate_eq_zero,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff,
    ccmRationalAdelicPrimeXiRationalCartierLanding_iff_re_eq_half]

/-- The same descent is exactly existence of the genuine source-natural `(2,3)` Gamma reporter. -/
theorem xiCenteredLogCharacterDescends_iff_sourceGammaNaturalReporter
    (rho : XiDivisorSupport) :
    XiCenteredLogCharacterDescends rho ↔
      Nonempty (PrimeGammaTwoThreeSourceNaturalReporter
        (primeDepthBVWoldXiCenteredRate rho)) := by
  rw [xiCenteredLogCharacterDescends_iff_centeredRate_eq_zero,
    primeGammaTwoThreeSourceNaturalReporter_nonempty_iff,
    primeGammaTwoThreeSourceNaturalInverseGhost_iff]

/-- One source-derived centered descent constructs both requested producers while retaining the
divisor and prime labels. -/
theorem xiCenteredLogCharacterDescends_constructs_cartier_and_reporter
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (h : XiCenteredLogCharacterDescends rho) :
    CCMRationalAdelicPrimeXiRationalCartierLanding p rho ∧
      Nonempty (PrimeGammaTwoThreeSourceNaturalReporter
        (primeDepthBVWoldXiCenteredRate rho)) := by
  exact ⟨(xiCenteredLogCharacterDescends_iff_rationalCartierLanding rho p).1 h,
    (xiCenteredLogCharacterDescends_iff_sourceGammaNaturalReporter rho).1 h⟩

end

end RHTower
