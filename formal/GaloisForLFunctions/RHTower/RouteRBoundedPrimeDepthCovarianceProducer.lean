import GaloisForLFunctions.RHTower.CCMRationalAdelicCompletedXiFixedCoronaPolarization

/-!
# Route R bounded prime-depth covariance criterion

This module classifies a proposed producer different from first-wall cofinal readers.  A retained rational-adelic
prime class lands in one normed carrier, where prime-depth dilation is isometric and physical
polarization is bounded.  If their commutator on the retained orbit is the explicit completed-Xi
Hodge-mate coefficient times the dilated vector, iteration makes that coefficient grow linearly.
Boundedness makes the same orbit uniformly bounded, so the coefficient is zero.

The converse is also exact: when the coefficient is zero, the Stokes regulator itself, identity
dilation, and zero polarization give a certificate.  Thus existence of this certificate is
equivalent to the desired coefficient vanishing, and its global form is equivalent to RH.  The
bounded-covariance package is therefore a classified criterion, not an independent source producer.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Abstract orbitwise bounded-covariance rigidity -/

private theorem norm_iterate_eq_of_isometry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : E →L[ℂ] E) (hU : ∀ y : E, ‖U y‖ = ‖y‖) :
    ∀ n : ℕ, ∀ y : E, ‖((U : E → E)^[n]) y‖ = ‖y‖ := by
  intro n
  induction n with
  | zero => intro y; rfl
  | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', hU, ih]

private theorem covariance_iterate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H U : E →L[ℂ] E) (k : ℂ) (x : E)
    (hcov : ∀ n : ℕ,
      H (U (((U : E → E)^[n]) x)) -
          U (H (((U : E → E)^[n]) x)) =
        k • U (((U : E → E)^[n]) x)) :
    ∀ n : ℕ,
      H (((U : E → E)^[n]) x) -
          ((U : E → E)^[n]) (H x) =
        (((n : ℕ) : ℂ) * k) • ((U : E → E)^[n]) x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc
        H (U (((U : E → E)^[n]) x)) - U (((U : E → E)^[n]) (H x)) =
            (H (U (((U : E → E)^[n]) x)) -
                U (H (((U : E → E)^[n]) x))) +
              U (H (((U : E → E)^[n]) x) -
                ((U : E → E)^[n]) (H x)) := by
                  rw [map_sub]
                  abel
        _ = k • U (((U : E → E)^[n]) x) +
              U ((((n : ℕ) : ℂ) * k) • ((U : E → E)^[n]) x) := by
                rw [hcov n, ih]
        _ = ((((n + 1 : ℕ) : ℂ) * k) •
              U (((U : E → E)^[n]) x)) := by
                rw [map_smul, ← add_smul]
                simp [Nat.cast_add, add_mul, add_comm]

/-- **Orbitwise bounded-covariance rigidity.**  A bounded operator cannot have a nonzero scalar
commutator with an isometry even when the commutator identity is known only on one nonzero forward
orbit. -/
theorem scalar_eq_zero_of_bounded_covariance_on_isometric_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H U : E →L[ℂ] E) (k : ℂ) (x : E) (hx : x ≠ 0)
    (hU : ∀ y : E, ‖U y‖ = ‖y‖)
    (hcov : ∀ n : ℕ,
      H (U (((U : E → E)^[n]) x)) -
          U (H (((U : E → E)^[n]) x)) =
        k • U (((U : E → E)^[n]) x)) :
    k = 0 := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hbound : ∀ n : ℕ, (n : ℝ) * ‖k‖ ≤ 2 * ‖H‖ := by
    intro n
    have hraw :
        ‖(((n : ℕ) : ℂ) * k) • ((U : E → E)^[n]) x‖ ≤
          (2 * ‖H‖) * ‖x‖ := by
      calc
        ‖(((n : ℕ) : ℂ) * k) • ((U : E → E)^[n]) x‖ =
            ‖H (((U : E → E)^[n]) x) -
              ((U : E → E)^[n]) (H x)‖ := by
                rw [covariance_iterate H U k x hcov n]
        _ ≤ ‖H (((U : E → E)^[n]) x)‖ +
              ‖((U : E → E)^[n]) (H x)‖ := norm_sub_le _ _
        _ ≤ ‖H‖ * ‖((U : E → E)^[n]) x‖ +
              ‖((U : E → E)^[n]) (H x)‖ := by
                exact add_le_add (H.le_opNorm _) le_rfl
        _ = ‖H‖ * ‖x‖ + ‖H x‖ := by
              rw [norm_iterate_eq_of_isometry U hU n x,
                norm_iterate_eq_of_isometry U hU n (H x)]
        _ ≤ ‖H‖ * ‖x‖ + ‖H‖ * ‖x‖ := by
              exact add_le_add le_rfl (H.le_opNorm _)
        _ = (2 * ‖H‖) * ‖x‖ := by rw [two_mul, add_mul]
    have hraw' :
        ((n : ℝ) * ‖k‖) * ‖x‖ ≤ (2 * ‖H‖) * ‖x‖ := by
      rw [norm_smul, norm_mul, Complex.norm_natCast,
        norm_iterate_eq_of_isometry U hU n x] at hraw
      simpa [mul_assoc] using hraw
    exact le_of_mul_le_mul_right hraw' hxnorm
  by_contra hk
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖H‖ / ‖k‖)
  have hstrict : 2 * ‖H‖ < (n : ℝ) * ‖k‖ :=
    (div_lt_iff₀ hkpos).mp hn
  exact (not_lt_of_ge (hbound n)) hstrict

/-! ## Coefficient-faithful rational-adelic producer -/

/-- Source-native Route R producer certificate.  Stokes compatibility pins the atom to the actual
period-one rational-adelic relative class.  The only new physical input is bounded orbitwise
covariance on a carrier where prime-depth dilation is isometric. -/
structure CCMRationalAdelicPrimeXiBoundedCovarianceCertificate
    (p : Nat.Primes) (rho : XiDivisorSupport) : Type 1 where
  E : Type
  [normedAddCommGroup_E : NormedAddCommGroup E]
  [normedSpace_E : NormedSpace ℂ E]
  sourceLanding :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] E
  stokesReadout : E →L[ℂ] ℂ
  stokes_compatible : ∀ z,
    stokesReadout (sourceLanding z) =
      ccmRationalAdelicPrimeRelativeH1StokesRegulator p z
  physicalPolarization : E →L[ℂ] E
  primeDepthDilation : E →L[ℂ] E
  primeDepthDilation_isometry : ∀ y : E,
    ‖primeDepthDilation y‖ = ‖y‖
  orbit_covariance : ∀ n : ℕ,
    physicalPolarization
          (primeDepthDilation
            (((primeDepthDilation : E → E)^[n])
              (sourceLanding (ccmRationalAdelicPrimeRelativeClass p)))) -
        primeDepthDilation
          (physicalPolarization
            (((primeDepthDilation : E → E)^[n])
              (sourceLanding (ccmRationalAdelicPrimeRelativeClass p)))) =
      ((ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℝ) : ℂ) •
        primeDepthDilation
          (((primeDepthDilation : E → E)^[n])
            (sourceLanding (ccmRationalAdelicPrimeRelativeClass p)))

attribute [instance]
  CCMRationalAdelicPrimeXiBoundedCovarianceCertificate.normedAddCommGroup_E
  CCMRationalAdelicPrimeXiBoundedCovarianceCertificate.normedSpace_E

/-- Actual retained period-one source atom in the producer carrier. -/
def CCMRationalAdelicPrimeXiBoundedCovarianceCertificate.sourceAtom
    {p : Nat.Primes} {rho : XiDivisorSupport}
    (cert : CCMRationalAdelicPrimeXiBoundedCovarianceCertificate p rho) : cert.E :=
  cert.sourceLanding (ccmRationalAdelicPrimeRelativeClass p)

/-- Stokes period one makes the landed source atom nonzero; non-erasure is a conclusion, not a
certificate field. -/
theorem CCMRationalAdelicPrimeXiBoundedCovarianceCertificate.sourceAtom_ne_zero
    {p : Nat.Primes} {rho : XiDivisorSupport}
    (cert : CCMRationalAdelicPrimeXiBoundedCovarianceCertificate p rho) :
    cert.sourceAtom ≠ 0 := by
  change cert.sourceLanding (ccmRationalAdelicPrimeRelativeClass p) ≠ 0
  intro hzero
  have hread := cert.stokes_compatible
    (ccmRationalAdelicPrimeRelativeClass p)
  rw [hzero, map_zero,
    ccmRationalAdelicPrimeRelativeH1StokesRegulator_class] at hread
  exact zero_ne_one hread

/-- One source-native bounded covariance certificate annihilates the explicit Route R Hodge-mate
coefficient. -/
theorem CCMRationalAdelicPrimeXiBoundedCovarianceCertificate.hodgeMateCoefficient_eq_zero
    {p : Nat.Primes} {rho : XiDivisorSupport}
    (cert : CCMRationalAdelicPrimeXiBoundedCovarianceCertificate p rho) :
    ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  have hk :
      ((ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℝ) : ℂ) = 0 :=
    scalar_eq_zero_of_bounded_covariance_on_isometric_orbit
      cert.physicalPolarization cert.primeDepthDilation
      ((ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho : ℝ) : ℂ)
      cert.sourceAtom cert.sourceAtom_ne_zero
      cert.primeDepthDilation_isometry cert.orbit_covariance
  exact Complex.ofReal_eq_zero.mp hk

/-- When the Hodge-mate coefficient already vanishes, the period-one Stokes regulator with
identity dilation and zero polarization gives a bounded covariance certificate.  This converse
exposes the exact logical strength of the proposed producer package. -/
theorem nonempty_boundedCovarianceCertificate_of_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hK : ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0) :
    Nonempty (CCMRationalAdelicPrimeXiBoundedCovarianceCertificate p rho) := by
  let sourceLanding :
      (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] ℂ :=
    ccmRationalAdelicPrimeRelativeH1StokesRegulator p
  let stokesReadout : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ
  let physicalPolarization : ℂ →L[ℂ] ℂ := 0
  let primeDepthDilation : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ
  let cert : CCMRationalAdelicPrimeXiBoundedCovarianceCertificate p rho := {
    E := ℂ
    sourceLanding := sourceLanding
    stokesReadout := stokesReadout
    stokes_compatible := by intro z; rfl
    physicalPolarization := physicalPolarization
    primeDepthDilation := primeDepthDilation
    primeDepthDilation_isometry := by intro y; rfl
    orbit_covariance := by
      intro n
      simp [physicalPolarization, primeDepthDilation, hK]
  }
  exact ⟨cert⟩

/-- **Exact classification.**  A bounded prime-depth covariance certificate exists exactly when
the explicit Route R Hodge-mate coefficient vanishes. -/
theorem nonempty_boundedCovarianceCertificate_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    Nonempty (CCMRationalAdelicPrimeXiBoundedCovarianceCertificate p rho) ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  constructor
  · intro hcert
    exact hcert.some.hodgeMateCoefficient_eq_zero
  · exact nonempty_boundedCovarianceCertificate_of_hodgeMateCoefficient_eq_zero p rho

/-- Global source producer: one bounded covariance realization for every actual Xi divisor point. -/
def CCMRationalAdelicPrimeXiGlobalBoundedCovarianceProducer
    (p : Nat.Primes) : Prop :=
  ∀ rho : XiDivisorSupport,
    Nonempty (CCMRationalAdelicPrimeXiBoundedCovarianceCertificate p rho)

/-- A global producer annihilates every explicit Hodge-mate coefficient. -/
theorem forall_hodgeMateCoefficient_eq_zero_of_globalBoundedCovarianceProducer
    (p : Nat.Primes)
    (hsource : CCMRationalAdelicPrimeXiGlobalBoundedCovarianceProducer p) :
    ∀ rho : XiDivisorSupport,
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  intro rho
  exact (hsource rho).some.hodgeMateCoefficient_eq_zero

/-- **Route R endgame.**  Constructing the global bounded covariance producer from pre-divisor
source structure closes the existing unconditional Lean chain to the Riemann hypothesis. -/
theorem riemannHypothesis_of_globalBoundedCovarianceProducer
    (p : Nat.Primes)
    (hsource : CCMRationalAdelicPrimeXiGlobalBoundedCovarianceProducer p) :
    RiemannHypothesis := by
  apply
    (forall_ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_riemannHypothesis p).1
  intro rho
  exact
    (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_hodgeMateCoefficient_eq_zero
      p rho).2
      (forall_hodgeMateCoefficient_eq_zero_of_globalBoundedCovarianceProducer
        p hsource rho)

/-- **Global classification.**  The proposed global bounded covariance producer is exactly RH,
so constructing it cannot serve as an independent pre-divisor source theorem. -/
theorem globalBoundedCovarianceProducer_iff_riemannHypothesis
    (p : Nat.Primes) :
    CCMRationalAdelicPrimeXiGlobalBoundedCovarianceProducer p ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_globalBoundedCovarianceProducer p
  · intro hRH rho
    apply nonempty_boundedCovarianceCertificate_of_hodgeMateCoefficient_eq_zero
    apply
      (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_hodgeMateCoefficient_eq_zero
        p rho).1
    exact
      (forall_ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_riemannHypothesis p).2
        hRH rho

end

end RHTower
