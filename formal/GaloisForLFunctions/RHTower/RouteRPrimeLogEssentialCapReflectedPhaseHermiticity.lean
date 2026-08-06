import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapRadialPhasePolarization
import GaloisForLFunctions.RHTower.XiCTaylorSignedPrimePhaseNodeSourceNoGo

/-!
# Two-prime reflected phase rigidity for the Route-R essential cap

Gamma reflection makes the physical half-density characters reciprocal.  Reality of one
reflected trace therefore has two branches: either the character is unitary, or its prime angle
is a sine node.  Reality at two distinct ordinary primes eliminates the second branch by
prime-log independence and nonzero Xi height.  Hence the two scalar reality laws force the fixed
orientation singular Stokes cap to vanish.

This is strictly weaker source-facing data than a same-fibre norm identity: only the imaginary
parts of the reflected physical moments at primes `2` and `3` must vanish.  The theorem below
isolates that finite phase-geometric producer without assuming critical-line placement.
-/

open Complex

namespace RHTower

noncomputable section

/-- The physical character splits into a positive radial gain and the unitary source-height
phase. -/
theorem ccmRationalAdelicPrimeXiPhysicalCharacter_radial_factorization
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) =
      (((p : ℝ) ^ ((1 / 2 : ℝ) - (rho : ℂ).re) : ℝ) : ℂ) *
        ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hbase : (((p : ℝ) : ℂ)) = (p : ℂ) := by push_cast; rfl
  rw [bilateralHalfDensityCharacter,
    ccmRationalAdelicPrimeXiSourcePhaseCharacter,
    bilateralHalfDensityCharacter]
  have hphysical :
      (((1 / 2 : ℝ) : ℂ) - (rho : ℂ)) =
        (((1 / 2 : ℝ) - (rho : ℂ).re : ℝ) : ℂ) +
          (((-(rho : ℂ).im : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  have hsource :
      (((1 / 2 : ℝ) : ℂ) - ccmRationalAdelicPrimeXiSourcePhasePoint rho) =
        (((-(rho : ℂ).im : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [hphysical, Complex.cpow_add _ _ hpC, hsource, ← hbase]
  rw [← Complex.ofReal_cpow hpR]

/-- Vanishing physical imaginary part is exactly the prime-angle sine-node alternative. -/
theorem ccmRationalAdelicPrimeXiPhysicalCharacter_im_eq_zero_iff_phaseNode
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)).im = 0 ↔
      Real.sin ((rho : ℂ).im * Real.log (p : ℝ)) = 0 := by
  rw [ccmRationalAdelicPrimeXiPhysicalCharacter_radial_factorization]
  have hphase := bilateralJetFamily_zpow_on_line
    (by exact_mod_cast p.2.pos) (rho : ℂ).im (1 : ℤ)
  simp only [one_mul, Int.cast_one, zpow_one] at hphase
  have hsourcePhase :
      ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho =
        Complex.exp (-((((rho : ℂ).im * Real.log (p : ℝ) : ℝ) : ℂ)) * I) := by
    simpa [ccmRationalAdelicPrimeXiSourcePhaseCharacter,
      ccmRationalAdelicPrimeXiSourcePhasePoint] using hphase
  rw [hsourcePhase]
  rw [show -((((rho : ℂ).im * Real.log (p : ℝ) : ℝ) : ℂ)) * I =
      (((-((rho : ℂ).im * Real.log (p : ℝ)) : ℝ) : ℂ)) * I by
        simp [mul_comm],
    Complex.exp_mul_I]
  let theta : ℝ := (rho : ℂ).im * Real.log (p : ℝ)
  have htheta : -((rho : ℂ).im * Real.log (p : ℝ)) = -theta := by rfl
  rw [htheta]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.I_re, Complex.I_im, zero_mul, add_zero,
    zero_add, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    Complex.sin_ofReal_im, mul_one]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hrpow : (p : ℝ) ^ ((1 / 2 : ℝ) - (rho : ℂ).re) ≠ 0 :=
    (Real.rpow_pos_of_pos hpR _).ne'
  change (p : ℝ) ^ ((1 / 2 : ℝ) - (rho : ℂ).re) * Real.sin (-theta) = 0 ↔
    Real.sin ((rho : ℂ).im * Real.log (p : ℝ)) = 0
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact False.elim (hrpow h)
    · simpa [theta, Real.sin_neg] using h
  · intro h
    exact Or.inr (by simpa [theta, Real.sin_neg] using h)

/-- A real reciprocal moment is either unitary or lies on the real-axis phase node. -/
theorem norm_eq_one_or_im_eq_zero_of_reciprocalMoment_im_eq_zero
    {z : ℂ} (hz : z ≠ 0) (hreal : (z + z⁻¹).im = 0) :
    ‖z‖ = 1 ∨ z.im = 0 := by
  by_cases him : z.im = 0
  · exact Or.inr him
  · left
    have hnormSq : Complex.normSq z ≠ 0 :=
      (Complex.normSq_pos.mpr hz).ne'
    rw [Complex.add_im, Complex.inv_im] at hreal
    have hfactor : z.im * (Complex.normSq z - 1) = 0 := by
      field_simp [hnormSq] at hreal
      nlinarith
    have hsq : Complex.normSq z = 1 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left him)
    rw [Complex.normSq_eq_norm_sq] at hsq
    nlinarith [norm_nonneg z]

theorem reciprocalMoment_im_eq_zero_of_norm_eq_one
    {z : ℂ} (hnorm : ‖z‖ = 1) :
    (z + z⁻¹).im = 0 := by
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [Complex.add_im, Complex.inv_im, hsq]
  ring

/-- Physical characters in the two Gamma orientations multiply to one, including their phase. -/
theorem ccmRationalAdelicPrimeXiPhysicalCharacter_mul_reflection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) *
      bilateralHalfDensityCharacter (p : ℕ) (xiZeroReflectEquiv rho : ℂ) = 1 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [bilateralHalfDensityCharacter, bilateralHalfDensityCharacter,
    xiZeroReflectEquiv_apply, ← Complex.cpow_add _ _ hpC]
  have hexp :
      (((1 / 2 : ℝ) : ℂ) - (rho : ℂ)) +
          (((1 / 2 : ℝ) : ℂ) - (1 - (rho : ℂ))) = 0 := by
    norm_num
    ring
  rw [hexp, Complex.cpow_zero]

theorem ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    bilateralHalfDensityCharacter (p : ℕ) (xiZeroReflectEquiv rho : ℂ) =
      (bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ))⁻¹ := by
  have hz : bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) ≠ 0 := by
    exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (by exact_mod_cast p.2.ne_zero))
  apply mul_left_cancel₀ hz
  rw [ccmRationalAdelicPrimeXiPhysicalCharacter_mul_reflection,
    mul_inv_cancel₀ hz]

/-- Reflection of a Xi support point reverses the source-height phase point around `1 / 2`. -/
theorem ccmRationalAdelicPrimeXiSourcePhasePoint_reflection
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourcePhasePoint (xiZeroReflectEquiv rho) =
      1 - ccmRationalAdelicPrimeXiSourcePhasePoint rho := by
  apply Complex.ext
  · simp [ccmRationalAdelicPrimeXiSourcePhasePoint, xiZeroReflectEquiv_apply]
    norm_num
  · simp [ccmRationalAdelicPrimeXiSourcePhasePoint, xiZeroReflectEquiv_apply]

/-- Pre-divisor source-height characters are reciprocal in the two Gamma orientations. -/
theorem ccmRationalAdelicPrimeXiSourcePhaseCharacter_mul_reflection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho *
      ccmRationalAdelicPrimeXiSourcePhaseCharacter p (xiZeroReflectEquiv rho) = 1 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [ccmRationalAdelicPrimeXiSourcePhaseCharacter,
    ccmRationalAdelicPrimeXiSourcePhaseCharacter,
    ccmRationalAdelicPrimeXiSourcePhasePoint_reflection,
    bilateralHalfDensityCharacter, bilateralHalfDensityCharacter,
    ← Complex.cpow_add _ _ hpC]
  have hexp :
      (((1 / 2 : ℝ) : ℂ) - ccmRationalAdelicPrimeXiSourcePhasePoint rho) +
          (((1 / 2 : ℝ) : ℂ) -
            (1 - ccmRationalAdelicPrimeXiSourcePhasePoint rho)) = 0 := by
    norm_num
    ring
  rw [hexp, Complex.cpow_zero]

theorem ccmRationalAdelicPrimeXiSourcePhaseCharacter_reflection_eq_inv
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourcePhaseCharacter p (xiZeroReflectEquiv rho) =
      (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho)⁻¹ := by
  apply mul_left_cancel₀
    (ccmRationalAdelicPrimeXiSourcePhaseCharacter_ne_zero p rho)
  rw [ccmRationalAdelicPrimeXiSourcePhaseCharacter_mul_reflection,
    mul_inv_cancel₀ (ccmRationalAdelicPrimeXiSourcePhaseCharacter_ne_zero p rho)]

/-- Pre-divisor half-grade orbit with an independent phase coefficient.  Horizontal modular
grade `t` and phase `u` remain separate until divisor specialization. -/
def ccmRationalAdelicPrimePhaseTwistedHalfGradeSource
    (p : Nat.Primes) (u : ℂ) (t : ℝ) : ℂ :=
  (((p : ℝ) ^ (t / 2) : ℝ) : ℂ) * u

/-- Reflection-minus-identity boundary of the independent phase/grade source. -/
def ccmRationalAdelicPrimePhaseTwistedHalfGradeBoundary
    (p : Nat.Primes) (u : ℂ) (t : ℝ) : ℂ :=
  ccmRationalAdelicPrimePhaseTwistedHalfGradeSource p u (-t) -
    ccmRationalAdelicPrimePhaseTwistedHalfGradeSource p u t

/-- Gamma-reflected physical phase moment at one ordinary prime. -/
def ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) +
    bilateralHalfDensityCharacter (p : ℕ) (xiZeroReflectEquiv rho : ℂ)

/-- Exact source-boundary presentation of the physical reflected imaginary moment.  The source
boundary is formed before fixing horizontal grade; specialization inserts the actual centered Xi
grade only after reflection-minus-identity has been formed. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_im_eq_sourceBoundary
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho).im =
      (ccmRationalAdelicPrimePhaseTwistedHalfGradeBoundary p
        (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho)
        (2 * (rho : ℂ).re - 1)).im := by
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
    ccmRationalAdelicPrimeXiPhysicalCharacter_radial_factorization,
    ccmRationalAdelicPrimeXiPhysicalCharacter_radial_factorization,
    ccmRationalAdelicPrimeXiSourcePhaseCharacter_reflection_eq_inv]
  have hsq : Complex.normSq
      (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho) = 1 := by
    rw [Complex.normSq_eq_norm_sq,
      norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter]
    norm_num
  rw [ccmRationalAdelicPrimePhaseTwistedHalfGradeBoundary,
    ccmRationalAdelicPrimePhaseTwistedHalfGradeSource,
    ccmRationalAdelicPrimePhaseTwistedHalfGradeSource]
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.inv_im, hsq, div_one]
  rw [xiZeroReflectEquiv_apply]
  simp only [Complex.sub_re, Complex.one_re]
  congr 1 <;> ring_nf

/-- Gamma-reflected moment of the unitary pre-divisor source-height phase. -/
def ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho +
    ccmRationalAdelicPrimeXiSourcePhaseCharacter p (xiZeroReflectEquiv rho)

/-- Source reflection is Hermitian before any horizontal physical gain is introduced. -/
theorem ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment_im_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment p rho).im = 0 := by
  rw [ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment,
    ccmRationalAdelicPrimeXiSourcePhaseCharacter_reflection_eq_inv]
  exact reciprocalMoment_im_eq_zero_of_norm_eq_one
    (norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho)

/-- Finite source-facing phase law: reflected physical moments are real at primes `2` and `3`. -/
def CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian
    (rho : XiDivisorSupport) : Prop :=
  (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment
      (⟨2, Nat.prime_two⟩ : Nat.Primes) rho).im = 0 ∧
    (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment
      (⟨3, by norm_num⟩ : Nat.Primes) rho).im = 0

/-- Exact finite landing still required after unconditional source Hermiticity: the imaginary
parts of the two physical reflected moments must equal those of their fixed source moments. -/
def CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding
    (rho : XiDivisorSupport) : Prop :=
  (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment
      (⟨2, Nat.prime_two⟩ : Nat.Primes) rho).im =
      (ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment
        (⟨2, Nat.prime_two⟩ : Nat.Primes) rho).im ∧
    (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment
      (⟨3, by norm_num⟩ : Nat.Primes) rho).im =
      (ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment
        (⟨3, by norm_num⟩ : Nat.Primes) rho).im

theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding_iff_hermitian
    (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding rho ↔
      CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian rho := by
  rw [CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding,
    CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian,
    ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment_im_eq_zero,
    ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment_im_eq_zero]

/-- Two reflected phase traces annihilate the fixed-orientation singular cap.  If neither trace
selects the unitary branch, they would place the nonzero Xi height simultaneously on the sine-node
lattices of `log 2` and `log 3`, contradicting prime-log independence. -/
theorem ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_of_twoPrimeHermitian
    (rho : XiDivisorSupport)
    (h : CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian rho) :
    CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  let p3 : Nat.Primes := ⟨3, by norm_num⟩
  rcases h with ⟨h2, h3⟩
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
    ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv] at h2 h3
  have hc2 := norm_eq_one_or_im_eq_zero_of_reciprocalMoment_im_eq_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) h2
  have hc3 := norm_eq_one_or_im_eq_zero_of_reciprocalMoment_im_eq_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))) h3
  rcases hc2 with hnorm2 | him2
  · have hre := (norm_bilateralHalfDensityCharacter_eq_one_iff (p := 2)
      (by norm_num) (rho : ℂ)).1 hnorm2
    exact (ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).2
      ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2 hre)
  · rcases hc3 with hnorm3 | him3
    · have hre := (norm_bilateralHalfDensityCharacter_eq_one_iff (p := 3)
        (by norm_num) (rho : ℂ)).1 hnorm3
      exact (ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).2
        ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).2 hre)
    · have hsin2 : Real.sin ((rho : ℂ).im * Real.log (2 : ℝ)) = 0 :=
        by
          have hiff :=
            ccmRationalAdelicPrimeXiPhysicalCharacter_im_eq_zero_iff_phaseNode
              p2 rho
          rw [bilateralHalfDensityCharacter] at hiff
          exact hiff.1 him2
      have hsin3 : Real.sin ((rho : ℂ).im * Real.log (3 : ℝ)) = 0 :=
        by
          have hiff :=
            ccmRationalAdelicPrimeXiPhysicalCharacter_im_eq_zero_iff_phaseNode
              p3 rho
          rw [bilateralHalfDensityCharacter] at hiff
          exact hiff.1 him3
      exact False.elim
        ((routeJ_scaledPrimeLog_phaseNodes_incompatible
          (u := (rho : ℂ).im) (p := 2) (q := 3) (a := 1) (b := 1)
          (xi_divisor_support_im_ne_zero rho) Nat.prime_two (by norm_num)
          (by norm_num) (by norm_num) (by norm_num))
          ⟨by simpa using hsin2, by simpa using hsin3⟩)

theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian_of_flat
    (rho : XiDivisorSupport)
    (hflat : CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho) :
    CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian rho := by
  have hre : (rho : ℂ).re = 1 / 2 :=
    (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).1
      ((ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff rho).1 hflat)
  constructor
  · rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
      ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv]
    apply reciprocalMoment_im_eq_zero_of_norm_eq_one
    exact (norm_bilateralHalfDensityCharacter_eq_one_iff (p := 2)
      (by norm_num) (rho : ℂ)).2 hre
  · rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
      ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv]
    apply reciprocalMoment_im_eq_zero_of_norm_eq_one
    exact (norm_bilateralHalfDensityCharacter_eq_one_iff (p := 3)
      (by norm_num) (rho : ℂ)).2 hre

theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian_iff_flat
    (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian rho ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho :=
  ⟨ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_of_twoPrimeHermitian rho,
    ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian_of_flat rho⟩

/-- Exact source-to-physical phase landing is the finite remaining form of singular flatness. -/
theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding_iff_flat
    (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding rho ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho :=
  (ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding_iff_hermitian rho).trans
    (ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian_iff_flat rho)

/-- Single positive phase port measuring failure of reflected physical Hermiticity at the two
independent prime clocks. -/
def ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort
    (rho : XiDivisorSupport) : ℝ :=
  (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment
      (⟨2, Nat.prime_two⟩ : Nat.Primes) rho).im ^ 2 +
    (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment
      (⟨3, by norm_num⟩ : Nat.Primes) rho).im ^ 2

/-- Fixed-grade scalar readout of the two independent pre-divisor phase/grade boundaries. -/
def ccmRationalAdelicPrimeXiTwoPrimePhaseBoundaryPort
    (rho : XiDivisorSupport) : ℝ :=
  (ccmRationalAdelicPrimePhaseTwistedHalfGradeBoundary
      (⟨2, Nat.prime_two⟩ : Nat.Primes)
      (ccmRationalAdelicPrimeXiSourcePhaseCharacter
        (⟨2, Nat.prime_two⟩ : Nat.Primes) rho)
      (2 * (rho : ℂ).re - 1)).im ^ 2 +
    (ccmRationalAdelicPrimePhaseTwistedHalfGradeBoundary
      (⟨3, by norm_num⟩ : Nat.Primes)
      (ccmRationalAdelicPrimeXiSourcePhaseCharacter
        (⟨3, by norm_num⟩ : Nat.Primes) rho)
      (2 * (rho : ℂ).re - 1)).im ^ 2

/-- The positive physical phase port is literally the squared fixed-grade readout of source
reflection boundaries, not merely a zero-locus equivalent. -/
theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_boundaryPort
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort rho =
      ccmRationalAdelicPrimeXiTwoPrimePhaseBoundaryPort rho := by
  rw [ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort,
    ccmRationalAdelicPrimeXiTwoPrimePhaseBoundaryPort,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_im_eq_sourceBoundary,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_im_eq_sourceBoundary]

/-- Corresponding source port.  It is zero before divisor placement because source-height
reflection is unitary. -/
def ccmRationalAdelicPrimeXiTwoPrimeReflectedSourcePhasePort
    (rho : XiDivisorSupport) : ℝ :=
  (ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment
      (⟨2, Nat.prime_two⟩ : Nat.Primes) rho).im ^ 2 +
    (ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment
      (⟨3, by norm_num⟩ : Nat.Primes) rho).im ^ 2

theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_nonneg
    (rho : XiDivisorSupport) :
    0 ≤ ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort rho := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedSourcePhasePort_eq_zero
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiTwoPrimeReflectedSourcePhasePort rho = 0 := by
  rw [ccmRationalAdelicPrimeXiTwoPrimeReflectedSourcePhasePort,
    ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment_im_eq_zero,
    ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment_im_eq_zero]
  norm_num

theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_zero_iff_hermitian
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort rho = 0 ↔
      CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian rho := by
  rw [ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort,
    CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg
      (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment
        (⟨2, Nat.prime_two⟩ : Nat.Primes) rho).im,
      sq_nonneg
        (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment
          (⟨3, by norm_num⟩ : Nat.Primes) rho).im]
  · rintro ⟨h2, h3⟩
    rw [h2, h3]
    norm_num

/-- Vanishing of the explicit positive phase port is exactly singular Stokes flatness. -/
theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_zero_iff_flat
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort rho = 0 ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho :=
  (ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_zero_iff_hermitian
    rho).trans
    (ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian_iff_flat rho)

theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_source_iff_flat
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort rho =
        ccmRationalAdelicPrimeXiTwoPrimeReflectedSourcePhasePort rho ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  rw [ccmRationalAdelicPrimeXiTwoPrimeReflectedSourcePhasePort_eq_zero]
  exact ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_zero_iff_flat rho

theorem ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_pos_iff_not_flat
    (rho : XiDivisorSupport) :
    0 < ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort rho ↔
      ¬ CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  constructor
  · intro hpos hflat
    have hzero :=
      (ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_zero_iff_flat
        rho).2 hflat
    linarith
  · intro hnflat
    rcases lt_or_eq_of_le
        (ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_nonneg rho) with
      hpos | hzero
    · exact hpos
    · exact False.elim (hnflat
        ((ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_zero_iff_flat
          rho).1 hzero.symm))

/-- Global two-prime reflected Hermiticity is equivalent to RH. -/
theorem forall_ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian_iff_RH :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian rho) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff_RH]
  exact forall_congr' ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseHermitian_iff_flat

theorem forall_ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding_iff_RH :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding rho) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff_RH]
  exact forall_congr' ccmRationalAdelicPrimeXiTwoPrimeReflectedPhaseLanding_iff_flat

theorem forall_ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_zero_iff_RH :
    (∀ rho : XiDivisorSupport,
      ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort rho = 0) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff_RH]
  exact forall_congr'
    ccmRationalAdelicPrimeXiTwoPrimeReflectedPhysicalPhasePort_eq_zero_iff_flat

end

end RHTower
