import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapPhaseQuadraturePolarization

/-!
# Fixed-grade phase dagger for the Route-R essential cap

The even and oriented-odd reflection quadratures are the two real coordinates of one intrinsic
dagger defect

`star z - z⁻¹`.

Their positive port is exactly the norm-square of that defect.  The source-height character has
zero dagger defect and acts isometrically on its coefficient line.  The physical character acts
on the same fixed Xi-Cartier coefficient line.  Since that coefficient is nonzero, the canonical
coefficient-faithful comparison intertwines the two scalar actions exactly when both physical
quadratures inherit source Hermiticity.

This identifies the fixed-grade operation which variable-grade boundary exactness would have to
produce.  It does not infer that intertwining from resolved homology: globally that assertion is
equivalent to the Riemann hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

/-- The two reciprocal quadratures are exactly the positive norm-square of failure of the
complex dagger to equal multiplicative inversion. -/
theorem reciprocalPhaseQuadraturePort_eq_normSq_daggerDefect
    {z : ℂ} (hz : z ≠ 0) :
    (z + z⁻¹).im ^ (2 : ℕ) + (I * (z - z⁻¹)).im ^ (2 : ℕ) =
      Complex.normSq (star z - z⁻¹) := by
  rw [reciprocalPhaseQuadraturePort_eq_normSq hz]
  have hN : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  change
    (Complex.normSq z - 1) ^ (2 : ℕ) / Complex.normSq z =
      (star z - z⁻¹).re * (star z - z⁻¹).re +
        (star z - z⁻¹).im * (star z - z⁻¹).im
  simp only [Complex.star_def, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.inv_re, Complex.inv_im]
  field_simp [hN]
  rw [Complex.normSq_apply]
  ring

/-- A unit complex phase has source dagger equal to multiplicative inversion. -/
theorem star_eq_inv_of_norm_eq_one {z : ℂ} (hnorm : ‖z‖ = 1) :
    star z = z⁻¹ := by
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [Complex.inv_def, hsq]
  norm_num

/-- Unitary source-height phase action on one fixed coefficient fibre. -/
def ccmRationalAdelicPrimeXiSourcePhaseAction
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ →ₗ[ℂ] ℂ :=
  ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho • LinearMap.id

/-- Physical half-density phase action on the same fixed coefficient fibre. -/
def ccmRationalAdelicPrimeXiPhysicalPhaseAction
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ →ₗ[ℂ] ℂ :=
  bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) • LinearMap.id

/-- Canonical coefficient-faithful fixed-grade Cartier comparison. -/
def ccmRationalAdelicPrimeXiCartierPhaseComparison
    (rho : XiDivisorSupport) : ℂ →ₗ[ℂ] ℂ :=
  ccmRationalAdelicPrimeXiCartierCoefficient rho • LinearMap.id

/-- Nonzero first Xi jet makes the fixed-grade Cartier comparison injective. -/
theorem ccmRationalAdelicPrimeXiCartierPhaseComparison_injective
    (rho : XiDivisorSupport) :
    Function.Injective (ccmRationalAdelicPrimeXiCartierPhaseComparison rho) := by
  intro x y h
  simp only [ccmRationalAdelicPrimeXiCartierPhaseComparison,
    LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at h
  exact mul_left_cancel₀
    (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho) h

/-- Source phase action is norm-conservative before divisor-grade specialization. -/
theorem ccmRationalAdelicPrimeXiSourcePhaseAction_norm
    (p : Nat.Primes) (rho : XiDivisorSupport) (x : ℂ) :
    ‖ccmRationalAdelicPrimeXiSourcePhaseAction p rho x‖ = ‖x‖ := by
  rw [ccmRationalAdelicPrimeXiSourcePhaseAction, LinearMap.smul_apply,
    LinearMap.id_apply, norm_smul,
    norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter, one_mul]

/-- The source phase point equals physical divisor placement exactly at neutral horizontal
grade. -/
theorem ccmRationalAdelicPrimeXiSourcePhasePoint_eq_physical_iff
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourcePhasePoint rho = (rho : ℂ) ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simpa using hre.symm
  · intro hre
    apply Complex.ext
    · simpa [ccmRationalAdelicPrimeXiSourcePhasePoint] using hre.symm
    · simp [ccmRationalAdelicPrimeXiSourcePhasePoint]

/-- Same-fibre physical dagger defect. -/
def ccmRationalAdelicPrimeXiReflectedPhysicalPhaseDaggerDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  star (bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ)) -
    (bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ))⁻¹

/-- Pre-divisor source dagger defect. -/
def ccmRationalAdelicPrimeXiReflectedSourcePhaseDaggerDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  star (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho) -
    (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho)⁻¹

/-- Source dagger defect vanishes unconditionally. -/
theorem ccmRationalAdelicPrimeXiReflectedSourcePhaseDaggerDefect_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedSourcePhaseDaggerDefect p rho = 0 := by
  rw [ccmRationalAdelicPrimeXiReflectedSourcePhaseDaggerDefect,
    star_eq_inv_of_norm_eq_one
      (norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho), sub_self]

/-- Exact positive identity: physical even/odd quadrature energy is the norm-square of the
fixed same-fibre dagger defect. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_daggerDefectNormSq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort p rho =
      Complex.normSq
        (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseDaggerDefect p rho) := by
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment,
    ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseDaggerDefect]
  exact reciprocalPhaseQuadraturePort_eq_normSq_daggerDefect
    (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (by exact_mod_cast p.2.ne_zero)))

/-- Physical simultaneous Hermiticity is exactly vanishing of the fixed same-fibre dagger
defect. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian_iff_daggerDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian p rho ↔
      ccmRationalAdelicPrimeXiReflectedPhysicalPhaseDaggerDefect p rho = 0 := by
  rw [←
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_zero_iff_hermitian,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadraturePort_eq_daggerDefectNormSq,
    Complex.normSq_eq_zero]

/-- The requested source-to-physical Hermiticity landing is precisely same-fibre dagger
triviality. -/
theorem ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_daggerDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding p rho ↔
      ccmRationalAdelicPrimeXiReflectedPhysicalPhaseDaggerDefect p rho = 0 := by
  rw [CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding,
    ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment_im_eq_zero,
    ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment_im_eq_zero,
    ←
      ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian_iff_daggerDefect]
  rfl

/-- On the retained nonzero Xi coefficient, equality of physical and source phase actions is
exactly neutral horizontal grade. -/
theorem ccmRationalAdelicPrimeXiPhaseActions_cartier_eq_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiPhysicalPhaseAction p rho
        (ccmRationalAdelicPrimeXiCartierCoefficient rho) =
      ccmRationalAdelicPrimeXiSourcePhaseAction p rho
        (ccmRationalAdelicPrimeXiCartierCoefficient rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hc := ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho
    have hchar :
        bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) =
          ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho := by
      apply mul_right_cancel₀ hc
      simpa [ccmRationalAdelicPrimeXiPhysicalPhaseAction,
        ccmRationalAdelicPrimeXiSourcePhaseAction] using h
    have hnorm := congrArg norm hchar
    rw [norm_ccmRationalAdelicPrimeXiSourcePhaseCharacter] at hnorm
    exact
      (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le _).1 hnorm
  · intro hre
    have hpoint :=
      (ccmRationalAdelicPrimeXiSourcePhasePoint_eq_physical_iff rho).2 hre
    simp only [ccmRationalAdelicPrimeXiPhysicalPhaseAction,
      ccmRationalAdelicPrimeXiSourcePhaseAction, LinearMap.smul_apply,
      LinearMap.id_apply]
    rw [ccmRationalAdelicPrimeXiSourcePhaseCharacter, hpoint]

/-- Exact fixed-grade comparison square.  Unlike variable-grade boundary exactness, this compares
source and physical actions on the same coefficient fibre. -/
def CCMRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  (ccmRationalAdelicPrimeXiPhysicalPhaseAction p rho).comp
      (ccmRationalAdelicPrimeXiCartierPhaseComparison rho) =
    (ccmRationalAdelicPrimeXiCartierPhaseComparison rho).comp
      (ccmRationalAdelicPrimeXiSourcePhaseAction p rho)

theorem ccmRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining_iff_actions
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining p rho ↔
      ccmRationalAdelicPrimeXiPhysicalPhaseAction p rho
          (ccmRationalAdelicPrimeXiCartierCoefficient rho) =
        ccmRationalAdelicPrimeXiSourcePhaseAction p rho
          (ccmRationalAdelicPrimeXiCartierCoefficient rho) := by
  constructor
  · intro h
    have h1 := LinearMap.congr_fun h 1
    simp only [LinearMap.comp_apply,
      ccmRationalAdelicPrimeXiPhysicalPhaseAction,
      ccmRationalAdelicPrimeXiSourcePhaseAction,
      ccmRationalAdelicPrimeXiCartierPhaseComparison,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one] at h1
    change
      bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) *
          ccmRationalAdelicPrimeXiCartierCoefficient rho =
        ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho *
          ccmRationalAdelicPrimeXiCartierCoefficient rho
    calc
      _ = ccmRationalAdelicPrimeXiCartierCoefficient rho *
          ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho := h1
      _ = _ := mul_comm _ _
  · intro h
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply,
      ccmRationalAdelicPrimeXiPhysicalPhaseAction,
      ccmRationalAdelicPrimeXiSourcePhaseAction,
      ccmRationalAdelicPrimeXiCartierPhaseComparison,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at h ⊢
    calc
      bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) *
          (ccmRationalAdelicPrimeXiCartierCoefficient rho * x) =
        (bilateralHalfDensityCharacter (p : ℕ) (rho : ℂ) *
          ccmRationalAdelicPrimeXiCartierCoefficient rho) * x := by ring
      _ = (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho *
          ccmRationalAdelicPrimeXiCartierCoefficient rho) * x := by rw [h]
      _ = ccmRationalAdelicPrimeXiCartierCoefficient rho *
          (ccmRationalAdelicPrimeXiSourcePhaseCharacter p rho * x) := by ring

/-- Fixed-grade coefficient-faithful intertwining is exactly simultaneous source-to-physical
Hermiticity of even and oriented-odd quadratures. -/
theorem ccmRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining_iff_landing
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining p rho ↔
      CCMRationalAdelicPrimeXiReflectedPhaseQuadratureLanding p rho := by
  rw [ccmRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining_iff_actions,
    ccmRationalAdelicPrimeXiPhaseActions_cartier_eq_iff_re_eq_half,
    ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_flat,
    ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Under the exact same-fibre comparison square, physical even and oriented-odd quadratures
inherit unconditional source Hermiticity. -/
theorem ccmRationalAdelicPrimeXiPhysicalQuadratures_inherit_sourceHermiticity
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hfixed :
      CCMRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining p rho) :
    (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho).im =
        (ccmRationalAdelicPrimeXiReflectedSourcePhaseMoment p rho).im ∧
      (ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p rho).im =
        (ccmRationalAdelicPrimeXiReflectedSourceOddPhaseMoment p rho).im :=
  (ccmRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining_iff_landing
    p rho).1 hfixed

/-- Global fixed-grade comparison is the exact Route-R endpoint, hence equivalent to RH. -/
theorem forall_ccmRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining_iff_RH
    (p : Nat.Primes) :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining p rho) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_RH p]
  exact forall_congr' fun rho =>
    ccmRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining_iff_landing
      p rho

end

end RHTower
