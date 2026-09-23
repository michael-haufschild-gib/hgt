import GaloisForLFunctions.RHTower.HedenmalmGammaSewnRouteRKreinGaugeBridge
import GaloisForLFunctions.RHTower.RouteRDerivedScalarCartierBaseChangeWall

/-!
# Transverse modular cocycle inside the Route N Krein wall

The critically damped marked Route N doublet contains more than the fixed-trace harmonic
obstruction.  Its signed Krein charge `Q_t(p)` recovers the positive transverse modular cocycle
after the literal prime deconvolution

`1 + sign(t) * p * Q_t(p) = p^(-2|t|)`.

The multiplier `p` is forced pointwise away from neutral grade.  It is unbounded, does not
preserve the fixed all-prime `ell^(1 : ℕ)` ideal, and therefore has no diagonal action on the physical
quotient.  Thus the modular half-density lives before fixed-trace completion: recovering it is
exactly a singular Cartier base change, not a bounded Hilbert or quotient operation.

At an actual Xi divisor point, survival of the scalar Cartier atom, noncontractibility of its
derived scalar fibre, summability of the Route N Krein current, and triviality of the recovered
modular cocycle have the same support.  No RH premise occurs.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Positive transverse modular character on an arbitrary positive clock. -/
def routeNGammaSewnTransverseModularClockCocycle
    (t q : ℝ) : ℝ :=
  q ^ (-2 * |t|)

/-- The transverse character is a genuine multiplicative clock cocycle. -/
theorem routeNGammaSewnTransverseModularClockCocycle_mul
    (t : ℝ) {q r : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) :
    routeNGammaSewnTransverseModularClockCocycle t (q * r) =
      routeNGammaSewnTransverseModularClockCocycle t q *
        routeNGammaSewnTransverseModularClockCocycle t r := by
  exact Real.mul_rpow hq hr

/-- Positive transverse modular cocycle recovered from the critically damped Route N doublet. -/
def routeNGammaSewnTransverseModularCocycle
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  routeNGammaSewnTransverseModularClockCocycle t (p : ℝ)

/-- Singular prime deconvolution required to recover the transverse modular cocycle. -/
def routeNGammaSewnModularDeconvolutionSequence : AllPrimeComplexSequence :=
  fun p => (p : ℂ)

/-- The Route N Krein current contains the complete positive modular cocycle. -/
theorem one_add_sign_mul_prime_mul_routeNKrein_eq_modularCocycle
    (t : ℝ) (p : Nat.Primes) :
    1 + Real.sign t * (p : ℝ) *
        routeNGammaSewnCriticalHorizonKreinCharge t p =
      routeNGammaSewnTransverseModularCocycle t p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [routeNGammaSewnCriticalHorizonKreinCharge_eq,
      routeNGammaSewnTransverseModularCocycle,
      routeNGammaSewnTransverseModularClockCocycle,
      Real.sign_of_neg ht, abs_of_neg ht]
    have hcancel : (p : ℝ) ^ t * (p : ℝ) ^ (-t) = 1 := by
      rw [← Real.rpow_add hp0]
      norm_num
    have hsquare : (p : ℝ) ^ t * (p : ℝ) ^ t = (p : ℝ) ^ (2 * t) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    field_simp [hp0.ne']
    calc
      1 + -((p : ℝ) ^ t * ((p : ℝ) ^ (-t) - (p : ℝ) ^ t)) =
          1 - (p : ℝ) ^ t * (p : ℝ) ^ (-t) +
            (p : ℝ) ^ t * (p : ℝ) ^ t := by ring
      _ = (p : ℝ) ^ (2 * t) := by rw [hcancel, hsquare]; ring
      _ = (p : ℝ) ^ (t * 2) := by ring_nf
  · norm_num [routeNGammaSewnCriticalHorizonKreinCharge_eq,
      routeNGammaSewnTransverseModularCocycle,
      routeNGammaSewnTransverseModularClockCocycle]
  · rw [routeNGammaSewnCriticalHorizonKreinCharge_eq,
      routeNGammaSewnTransverseModularCocycle,
      routeNGammaSewnTransverseModularClockCocycle,
      Real.sign_of_pos ht, abs_of_pos ht]
    have hcancel : (p : ℝ) ^ (-t) * (p : ℝ) ^ t = 1 := by
      rw [← Real.rpow_add hp0]
      norm_num
    have hsquare : (p : ℝ) ^ (-t) * (p : ℝ) ^ (-t) = (p : ℝ) ^ (-2 * t) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    field_simp [hp0.ne']
    calc
      1 + (p : ℝ) ^ (-t) * ((p : ℝ) ^ (-t) - (p : ℝ) ^ t) =
          1 + (p : ℝ) ^ (-t) * (p : ℝ) ^ (-t) -
            (p : ℝ) ^ (-t) * (p : ℝ) ^ t := by ring
      _ = (p : ℝ) ^ (-2 * t) := by rw [hcancel, hsquare]; ring
      _ = (p : ℝ) ^ (-(t * 2)) := by ring_nf

/-- The recovered positive cocycle is trivial at one ordinary prime exactly at neutral grade. -/
theorem routeNGammaSewnTransverseModularCocycle_eq_one_iff
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTransverseModularCocycle t p = 1 ↔ t = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  rw [routeNGammaSewnTransverseModularCocycle,
    routeNGammaSewnTransverseModularClockCocycle,
    ← Real.rpow_zero (p : ℝ)]
  constructor
  · intro h
    have hexp : -2 * |t| = 0 :=
      (Real.strictMono_rpow_of_base_gt_one hp1).injective h
    have habs : |t| = 0 := by linarith
    exact abs_eq_zero.mp habs
  · rintro rfl
    norm_num

/-- The critically damped Krein charge is pointwise nonzero away from neutral grade. -/
theorem routeNGammaSewnCriticalHorizonKreinCharge_ne_zero
    {t : ℝ} (ht : t ≠ 0) (p : Nat.Primes) :
    routeNGammaSewnCriticalHorizonKreinCharge t p ≠ 0 := by
  intro hq
  have hr := routeR_eq_fisherGauge_mul_routeNKrein t p
  rw [hq, mul_zero] at hr
  have hdamp : (p : ℝ) ^ (-|t|) ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).ne'
  have hraw :
      primeActivationOccupancyFisherTwist (-t) p -
          primeActivationOccupancyFisherTwist t p ≠ 0 := by
    change primeGammaCofinalBocksteinCoefficient t p ≠ 0
    exact (primeGammaCofinalBocksteinCoefficient_eq_zero_iff t p).not.mpr ht
  exact (mul_ne_zero hdamp hraw) hr

/-- Away from neutral grade, prime deconvolution is the unique real diagonal coefficient that
recovers the modular cocycle from the Route N Krein current. -/
theorem routeNGammaSewn_modularDeconvolution_unique
    {t : ℝ} (ht : t ≠ 0) (p : Nat.Primes) {m : ℝ}
    (hm : 1 + Real.sign t * m *
        routeNGammaSewnCriticalHorizonKreinCharge t p =
      routeNGammaSewnTransverseModularCocycle t p) :
    m = (p : ℝ) := by
  have hcanonical :=
    one_add_sign_mul_prime_mul_routeNKrein_eq_modularCocycle t p
  have hsign : Real.sign t ≠ 0 := fun hs =>
    ht (Real.sign_eq_zero_iff.mp hs)
  have hcharge := routeNGammaSewnCriticalHorizonKreinCharge_ne_zero ht p
  have hproduct : Real.sign t *
        routeNGammaSewnCriticalHorizonKreinCharge t p ≠ 0 :=
    mul_ne_zero hsign hcharge
  apply (mul_right_cancel₀ hproduct)
  nlinarith [hm, hcanonical]

/-- Summable test sequence used to expose failure of prime deconvolution on `ell^(1 : ℕ)`. -/
def routeNGammaSewnModularDeconvolutionKernelWitness : AllPrimeComplexSequence :=
  fun p => Complex.ofReal ((p : ℝ) ^ (-2 : ℝ))

theorem summable_routeNGammaSewnModularDeconvolutionKernelWitness :
    Summable routeNGammaSewnModularDeconvolutionKernelWitness := by
  change Summable (fun p : Nat.Primes => Complex.ofReal ((p : ℝ) ^ (-2 : ℝ)))
  exact Complex.summable_ofReal.mpr
    ((Nat.Primes.summable_rpow).2 (by norm_num))

/-- Prime deconvolution sends a summable order-two witness to the nonsummable prime harmonic
sequence. -/
theorem routeNGammaSewnModularDeconvolution_mul_kernelWitness :
    primeDiagonalMultiplier routeNGammaSewnModularDeconvolutionSequence
        routeNGammaSewnModularDeconvolutionKernelWitness =
      primeHarmonicComplexSequence := by
  funext p
  change (p : ℂ) * Complex.ofReal ((p : ℝ) ^ (-2 : ℝ)) =
    Complex.ofReal ((p : ℝ) ^ (-1 : ℝ))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hmul : (p : ℝ) * (p : ℝ) ^ (-2 : ℝ) =
      (p : ℝ) ^ (-1 : ℝ) := by
    calc
      (p : ℝ) * (p : ℝ) ^ (-2 : ℝ) =
          (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-2 : ℝ) := by
            rw [Real.rpow_one]
      _ = (p : ℝ) ^ ((1 : ℝ) + (-2 : ℝ)) := by
        rw [Real.rpow_add hp0]
      _ = (p : ℝ) ^ (-1 : ℝ) := by norm_num
  exact_mod_cast hmul

/-- Singular prime deconvolution does not preserve the fixed physical `ell^(1 : ℕ)` ideal. -/
theorem routeNGammaSewnModularDeconvolution_not_preservesL1 :
    ¬ PrimeDiagonalPreservesL1 routeNGammaSewnModularDeconvolutionSequence := by
  intro hpreserves
  have hout := hpreserves summable_routeNGammaSewnModularDeconvolutionKernelWitness
  change Summable
    (primeDiagonalMultiplier routeNGammaSewnModularDeconvolutionSequence
      routeNGammaSewnModularDeconvolutionKernelWitness) at hout
  rw [routeNGammaSewnModularDeconvolution_mul_kernelWitness] at hout
  exact not_summable_primeHarmonicComplexSequence hout

/-- Equivalently, prime deconvolution is unbounded. -/
theorem routeNGammaSewnModularDeconvolution_not_isBounded :
    ¬ Bornology.IsBounded
      (Set.range routeNGammaSewnModularDeconvolutionSequence) := by
  rw [← primeDiagonalPreservesL1_iff_isBounded]
  exact routeNGammaSewnModularDeconvolution_not_preservesL1

/-- Therefore the unique modular deconvolution has no diagonal action on the fixed all-prime
quotient by `ell^(1 : ℕ)`. -/
theorem routeNGammaSewnModularDeconvolution_not_hasQuotientMap :
    ¬ HasPrimeDiagonalQuotientMap
      routeNGammaSewnModularDeconvolutionSequence := by
  rw [hasPrimeDiagonalQuotientMap_iff_preservesL1]
  exact routeNGammaSewnModularDeconvolution_not_preservesL1

/-! ## The same singular deconvolution in the Route R gauge -/

/-- Unique Route R coefficient that removes both the bounded Fisher gauge and the harmonic
first-trace factor. -/
def routeRGammaSewnModularDeconvolutionWeight (p : Nat.Primes) : ℝ :=
  (p : ℝ) / routeNGammaSewnFisherGauge p

theorem routeRGammaSewnModularDeconvolutionWeight_eq
    (p : Nat.Primes) :
    routeRGammaSewnModularDeconvolutionWeight p =
      ((p : ℝ) + 1) ^ 2 / (p : ℝ) := by
  rw [routeRGammaSewnModularDeconvolutionWeight,
    routeNGammaSewnFisherGauge,
    primeActivationOccupancyFisherDensity_eq]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp [hp0]

/-- Route R's oriented critical-wall coefficient recovers the identical transverse modular
cocycle after its canonical singular deconvolution. -/
theorem one_add_sign_mul_routeRDeconvolution_mul_routeRWall_eq_modularCocycle
    (t : ℝ) (p : Nat.Primes) :
    1 + Real.sign t * routeRGammaSewnModularDeconvolutionWeight p *
        primeGammaCofinalBocksteinCriticalWallCoefficient t p =
      routeNGammaSewnTransverseModularCocycle t p := by
  rw [routeR_eq_fisherGauge_mul_routeNKrein,
    routeRGammaSewnModularDeconvolutionWeight]
  have hg : routeNGammaSewnFisherGauge p ≠ 0 :=
    (routeNGammaSewnFisherGauge_pos p).ne'
  calc
    1 + Real.sign t *
          ((p : ℝ) / routeNGammaSewnFisherGauge p) *
          (routeNGammaSewnFisherGauge p *
            routeNGammaSewnCriticalHorizonKreinCharge t p) =
        1 + Real.sign t * (p : ℝ) *
          routeNGammaSewnCriticalHorizonKreinCharge t p := by
            field_simp [hg]
    _ = routeNGammaSewnTransverseModularCocycle t p :=
      one_add_sign_mul_prime_mul_routeNKrein_eq_modularCocycle t p

/-- Away from neutral grade, the Route R coefficient above is also forced pointwise. -/
theorem routeRGammaSewn_modularDeconvolution_unique
    {t : ℝ} (ht : t ≠ 0) (p : Nat.Primes) {m : ℝ}
    (hm : 1 + Real.sign t * m *
        primeGammaCofinalBocksteinCriticalWallCoefficient t p =
      routeNGammaSewnTransverseModularCocycle t p) :
    m = routeRGammaSewnModularDeconvolutionWeight p := by
  have hcanonical :=
    one_add_sign_mul_routeRDeconvolution_mul_routeRWall_eq_modularCocycle t p
  have hsign : Real.sign t ≠ 0 := fun hs =>
    ht (Real.sign_eq_zero_iff.mp hs)
  have hwall : primeGammaCofinalBocksteinCriticalWallCoefficient t p ≠ 0 := by
    rw [primeGammaCofinalBocksteinCriticalWallCoefficient]
    exact mul_ne_zero
      (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).ne'
      ((primeGammaCofinalBocksteinCoefficient_eq_zero_iff t p).not.mpr ht)
  have hproduct : Real.sign t *
        primeGammaCofinalBocksteinCriticalWallCoefficient t p ≠ 0 :=
    mul_ne_zero hsign hwall
  apply (mul_right_cancel₀ hproduct)
  nlinarith [hm, hcanonical]

def routeRGammaSewnModularDeconvolutionSequence : AllPrimeComplexSequence :=
  fun p => (routeRGammaSewnModularDeconvolutionWeight p : ℂ)

/-- Multiplying Route R's singular deconvolution by the bounded Fisher gauge gives the literal
prime deconvolution. -/
theorem routeRGammaSewnFisherGauge_mul_modularDeconvolutionSequence :
    primeDiagonalMultiplier routeNGammaSewnFisherGaugeSequence
        routeRGammaSewnModularDeconvolutionSequence =
      routeNGammaSewnModularDeconvolutionSequence := by
  funext p
  change (routeNGammaSewnFisherGauge p : ℂ) *
      (routeRGammaSewnModularDeconvolutionWeight p : ℂ) = (p : ℂ)
  rw [routeRGammaSewnModularDeconvolutionWeight]
  push_cast
  field_simp [(routeNGammaSewnFisherGauge_pos p).ne']

/-- Route R modular recovery cannot preserve the fixed physical `ell^(1 : ℕ)` ideal either. -/
theorem routeRGammaSewnModularDeconvolution_not_preservesL1 :
    ¬ PrimeDiagonalPreservesL1 routeRGammaSewnModularDeconvolutionSequence := by
  intro hrouteR
  apply routeNGammaSewnModularDeconvolution_not_preservesL1
  intro f hf
  have hfirst := hrouteR hf
  have hsecond := routeNGammaSewnFisherGaugeSequence_preservesL1 hfirst
  change Summable
    (primeDiagonalMultiplier routeNGammaSewnFisherGaugeSequence
      (primeDiagonalMultiplier routeRGammaSewnModularDeconvolutionSequence f)) at hsecond
  have hcomp :
      primeDiagonalMultiplier routeNGammaSewnFisherGaugeSequence
          (primeDiagonalMultiplier routeRGammaSewnModularDeconvolutionSequence f) =
        primeDiagonalMultiplier routeNGammaSewnModularDeconvolutionSequence f := by
    funext p
    change routeNGammaSewnFisherGaugeSequence p *
        (routeRGammaSewnModularDeconvolutionSequence p * f p) =
      routeNGammaSewnModularDeconvolutionSequence p * f p
    rw [← mul_assoc]
    have hpoint := congrFun
      routeRGammaSewnFisherGauge_mul_modularDeconvolutionSequence p
    exact congrArg (fun z : ℂ => z * f p) hpoint
  rw [hcomp] at hsecond
  exact hsecond

theorem routeRGammaSewnModularDeconvolution_not_hasQuotientMap :
    ¬ HasPrimeDiagonalQuotientMap
      routeRGammaSewnModularDeconvolutionSequence := by
  rw [hasPrimeDiagonalQuotientMap_iff_preservesL1]
  exact routeRGammaSewnModularDeconvolution_not_preservesL1

/-- Actual centered horizontal grade of one Xi divisor point. -/
def routeNGammaSewnXiCenteredGrade (rho : XiDivisorSupport) : ℝ :=
  2 * (rho : ℂ).re - 1

/-- Route N critical-horizon Krein current on an actual Xi divisor fibre. -/
def routeNGammaSewnXiCriticalHorizonKreinPrimeSequence
    (rho : XiDivisorSupport) : AllPrimeComplexSequence :=
  routeNGammaSewnCriticalHorizonKreinPrimeSequence
    (routeNGammaSewnXiCenteredGrade rho)

/-- The actual Route N Krein current is summable exactly on critical-line support. -/
theorem summable_routeNGammaSewnXiCriticalHorizonKreinPrimeSequence_iff
    (rho : XiDivisorSupport) :
    Summable (routeNGammaSewnXiCriticalHorizonKreinPrimeSequence rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeNGammaSewnXiCriticalHorizonKreinPrimeSequence,
    summable_routeNGammaSewnCriticalHorizonKreinPrimeSequence_iff,
    routeNGammaSewnXiCenteredGrade]
  constructor <;> intro h <;> linarith

/-- **Support-exchange law.**  The ordinary scalar Cartier fibre is contractible exactly when
the physical Route N Krein current fails to be summable. -/
theorem routeRScalarCartier_contractible_iff_not_summable_routeNKrein
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    RouteRScalarCartierSpecializationContractible
        (routeRPrimeXiScalarCartierGain p rho) ↔
      ¬ Summable (routeNGammaSewnXiCriticalHorizonKreinPrimeSequence rho) := by
  rw [routeRPrimeXiScalarCartierSpecializationContractible_iff_re_ne_half,
    summable_routeNGammaSewnXiCriticalHorizonKreinPrimeSequence_iff]

/-- Dually, coefficient-faithful survival of the scalar Cartier atom occurs exactly when the
physical Route N Krein wall disappears into `ell^(1 : ℕ)`. -/
theorem routeRScalarCartier_atomLanding_injective_iff_summable_routeNKrein
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    Function.Injective (routeRPrimeXiScalarCartierAtomLanding p rho) ↔
      Summable (routeNGammaSewnXiCriticalHorizonKreinPrimeSequence rho) := by
  rw [routeRPrimeXiScalarCartierAtomLanding_injective_iff_re_eq_half,
    summable_routeNGammaSewnXiCriticalHorizonKreinPrimeSequence_iff]

/-- Global scalar-Cartier/Route-N support matching is exactly the RH endpoint. -/
theorem riemannHypothesis_iff_all_routeNXiKrein_summable :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        Summable (routeNGammaSewnXiCriticalHorizonKreinPrimeSequence rho) := by
  constructor
  · intro hRH rho
    exact (summable_routeNGammaSewnXiCriticalHorizonKreinPrimeSequence_iff rho).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hzero
    let q : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    exact (summable_routeNGammaSewnXiCriticalHorizonKreinPrimeSequence_iff q).1
      (h q)

end

end RHTower
