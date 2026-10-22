import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyStokesRegulator
import GaloisForLFunctions.RHTower.PrimeFirstTraceEssentialEdgeReflectedIdealGrade

/-!
# Graded variable-ideal comparison to the fixed physical Xi trace quotient

The activation-Fisher carrier at centered grade `t` is reflected by the raw character multiplier
`C_t(a)_p = p^(-2t) a_p`.  A fixed Hilbert carrier does not contain every actual Xi grade.  This
module instead constructs the maximal pullback ideal `J_t = C_t⁻¹(ell¹)`.  The induced comparison
`S/J_t -> S/ell¹` is an isomorphism at every real grade and sends the distinguished resolved
coefficient class at `t` to the fixed physical Fisher class at `-t`.

The construction is unconditional and uses the full complex coefficient line.  In the actual Xi
strip its distinguished coefficient landing is injective exactly for `t <= 0`; the reflected
landing is injective exactly for `0 <= t`.  Simultaneous coefficient faithfulness is therefore
equivalent to `t=0`, and at an Xi divisor copy to the critical-line condition.  No such
faithfulness is assumed here: the final theorem is a classification, not an RH premise.
-/

open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Ambient complex prime sequence module for the essential first-trace quotient. -/
abbrev PrimeTraceSequence := Nat.Primes → ℂ

/-- Fixed physical first-trace ideal. -/
def primeFirstTraceSummableIdeal : Submodule ℂ PrimeTraceSequence where
  carrier := {a | Summable a}
  zero_mem' := summable_zero
  add_mem' ha hb := ha.add hb
  smul_mem' c a ha := by
    change Summable (fun i => c * a i)
    exact ha.const_smul c

/-- Complex coefficient realization of the source activation-Fisher twist. -/
def primeActivationOccupancyFisherComplexTwist
    (t : ℝ) (p : Nat.Primes) : ℂ :=
  primeActivationOccupancyFisherTwist t p

/-- Raw reflected character multiplier on the full prime sequence module. -/
def primeReflectedCharacterMultiplier (t : ℝ) :
    PrimeTraceSequence →ₗ[ℂ] PrimeTraceSequence where
  toFun a p := (↑((p.1 : ℝ) ^ (-2 * t)) : ℂ) * a p
  map_add' a b := by
    funext p
    simp only [Pi.add_apply]
    ring
  map_smul' c a := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem primeReflectedCharacterMultiplier_apply
    (t : ℝ) (a : PrimeTraceSequence) (p : Nat.Primes) :
    primeReflectedCharacterMultiplier t a p =
      (↑((p.1 : ℝ) ^ (-2 * t)) : ℂ) * a p :=
  rfl

/-- The raw character comparison carries grade `t` Fisher coefficients to grade `-t`. -/
theorem primeReflectedCharacterMultiplier_fisher
    (t : ℝ) :
    primeReflectedCharacterMultiplier t
        (primeActivationOccupancyFisherComplexTwist t) =
      primeActivationOccupancyFisherComplexTwist (-t) := by
  funext p
  have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  rw [primeReflectedCharacterMultiplier_apply,
    primeActivationOccupancyFisherComplexTwist,
    primeActivationOccupancyFisherComplexTwist,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist]
  have hpow :
      (p.1 : ℝ) ^ (-2 * t) * (p.1 : ℝ) ^ t =
        (p.1 : ℝ) ^ (-t) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have hreal :
      (p.1 : ℝ) ^ (-2 * t) *
          ((p.1 : ℝ) ^ t * primeActivationOccupancyFisherDensity p) =
        (p.1 : ℝ) ^ (-t) *
          primeActivationOccupancyFisherDensity p := by
    rw [← mul_assoc, hpow]
  exact_mod_cast hreal

/-- Reflection twice is the identity on every prime coefficient. -/
theorem primeReflectedCharacterMultiplier_involution
    (t : ℝ) :
    (primeReflectedCharacterMultiplier (-t)).comp
        (primeReflectedCharacterMultiplier t) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  funext p
  have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  simp only [LinearMap.comp_apply, primeReflectedCharacterMultiplier_apply,
    LinearMap.id_coe, id_eq]
  have hpow :
      (p.1 : ℝ) ^ (-2 * (-t)) * (p.1 : ℝ) ^ (-2 * t) = 1 := by
    rw [← Real.rpow_add hp]
    norm_num
  have hpowC :
      (↑((p.1 : ℝ) ^ (-2 * (-t))) : ℂ) *
          ↑((p.1 : ℝ) ^ (-2 * t)) = 1 := by
    exact_mod_cast hpow
  rw [← mul_assoc]
  rw [hpowC, one_mul]

theorem primeReflectedCharacterMultiplier_bijective (t : ℝ) :
    Function.Bijective (primeReflectedCharacterMultiplier t) := by
  constructor
  · intro a b hab
    have ha : primeReflectedCharacterMultiplier (-t)
        (primeReflectedCharacterMultiplier t a) = a := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        DFunLike.congr_fun (primeReflectedCharacterMultiplier_involution t) a
    have hb : primeReflectedCharacterMultiplier (-t)
        (primeReflectedCharacterMultiplier t b) = b := by
      simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
        DFunLike.congr_fun (primeReflectedCharacterMultiplier_involution t) b
    rw [← ha, ← hb, hab]
  · intro a
    refine ⟨primeReflectedCharacterMultiplier (-t) a, ?_⟩
    have h := DFunLike.congr_fun
      (primeReflectedCharacterMultiplier_involution (-t)) a
    simpa only [neg_neg, LinearMap.comp_apply, LinearMap.id_apply] using h

/-- Maximal grade-dependent source ideal that lands in the fixed physical trace ideal. -/
def primeReflectedCharacterPullbackIdeal (t : ℝ) :
    Submodule ℂ PrimeTraceSequence :=
  primeFirstTraceSummableIdeal.comap
    (primeReflectedCharacterMultiplier t)

/-- Induced comparison from the variable source ideal quotient to the fixed physical quotient. -/
def primeVariableIdealFixedComparison (t : ℝ) :
    PrimeTraceSequence ⧸ primeReflectedCharacterPullbackIdeal t →ₗ[ℂ]
      PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal :=
  (primeReflectedCharacterPullbackIdeal t).mapQ
    primeFirstTraceSummableIdeal
    (primeReflectedCharacterMultiplier t) (by rfl)

theorem primeVariableIdealFixedComparison_bijective (t : ℝ) :
    Function.Bijective (primeVariableIdealFixedComparison t) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, primeVariableIdealFixedComparison,
      Submodule.ker_mapQ]
    simp [primeReflectedCharacterPullbackIdeal]
    rfl
  · intro q
    rcases primeFirstTraceSummableIdeal.mkQ_surjective q with ⟨a, rfl⟩
    rcases (primeReflectedCharacterMultiplier_bijective t).2 a with ⟨b, hb⟩
    refine ⟨Submodule.Quotient.mk b, ?_⟩
    rw [primeVariableIdealFixedComparison, Submodule.mapQ_apply, hb]
    rfl

/-- Raw graded comparison is an isomorphism from its maximal pullback ideal quotient to the fixed
physical trace-ideal quotient at every real grade. -/
def primeVariableIdealFixedComparisonEquiv (t : ℝ) :
    (PrimeTraceSequence ⧸ primeReflectedCharacterPullbackIdeal t) ≃ₗ[ℂ]
      (PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal) :=
  LinearEquiv.ofBijective (primeVariableIdealFixedComparison t)
    (primeVariableIdealFixedComparison_bijective t)

/-- Resolved distinguished coefficient before fixed-ideal specialization. -/
def primeVariableIdealResolvedCoefficientClass (t : ℝ) :
    PrimeTraceSequence ⧸ primeReflectedCharacterPullbackIdeal t :=
  Submodule.Quotient.mk (primeActivationOccupancyFisherComplexTwist t)

/-- Fixed physical Fisher class at one grade. -/
def primeFixedPhysicalFisherClass (t : ℝ) :
    PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal :=
  Submodule.Quotient.mk (primeActivationOccupancyFisherComplexTwist t)

/-- Exact landing of the resolved coefficient in the fixed physical quotient. -/
theorem primeVariableIdealFixedComparison_coefficientClass
    (t : ℝ) :
    primeVariableIdealFixedComparison t
        (primeVariableIdealResolvedCoefficientClass t) =
      primeFixedPhysicalFisherClass (-t) := by
  rw [primeVariableIdealFixedComparison,
    primeVariableIdealResolvedCoefficientClass,
    primeFixedPhysicalFisherClass, Submodule.mapQ_apply,
    primeReflectedCharacterMultiplier_fisher]

/-- Full complex coefficient line of the retained resolved boundary. -/
def primeVariableIdealResolvedCoefficientLanding (t : ℝ) :
    ℂ →ₗ[ℂ]
      PrimeTraceSequence ⧸ primeReflectedCharacterPullbackIdeal t where
  toFun c := c • primeVariableIdealResolvedCoefficientClass t
  map_add' c d := by rw [add_smul]
  map_smul' c d := by
    simp [smul_eq_mul, mul_smul]

private theorem coefficientLanding_injective_iff_class_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V] (v : V) :
    Function.Injective (fun c : ℂ => c • v) ↔ v ≠ 0 := by
  constructor
  · intro h hv
    have h10 := h (show (1 : ℂ) • v = (0 : ℂ) • v by simp [hv])
    norm_num at h10
  · intro hv c d hcd
    have hzero : (c - d) • v = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact hcd
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv)

/-- In the moderate strip, fixed physical coefficient survives exactly on the nonnegative side. -/
theorem primeFixedPhysicalFisherClass_ne_zero_iff
    {t : ℝ} (ht : t < 1) :
    primeFixedPhysicalFisherClass t ≠ 0 ↔ 0 ≤ t := by
  rw [ne_eq, primeFixedPhysicalFisherClass,
    Submodule.Quotient.mk_eq_zero]
  change ¬Summable (primeActivationOccupancyFisherComplexTwist t) ↔ 0 ≤ t
  rw [show Summable (primeActivationOccupancyFisherComplexTwist t) ↔
      Summable (primeActivationOccupancyFisherTwist t) by
    exact Complex.summable_ofReal]
  rw [summable_primeActivationOccupancyFisherTwist_iff_of_lt_one ht]
  exact not_lt

/-- Pullback-ideal coefficient survives exactly when its fixed physical reflected class does. -/
theorem primeVariableIdealResolvedCoefficientClass_ne_zero_iff
    {t : ℝ} (ht : -1 < t) :
    primeVariableIdealResolvedCoefficientClass t ≠ 0 ↔ t ≤ 0 := by
  rw [ne_eq, primeVariableIdealResolvedCoefficientClass,
    Submodule.Quotient.mk_eq_zero]
  change ¬ Summable
      (primeReflectedCharacterMultiplier t
        (primeActivationOccupancyFisherComplexTwist t)) ↔ t ≤ 0
  rw [primeReflectedCharacterMultiplier_fisher,
    show Summable (primeActivationOccupancyFisherComplexTwist (-t)) ↔
        Summable (primeActivationOccupancyFisherTwist (-t)) by
      exact Complex.summable_ofReal,
    summable_primeActivationOccupancyFisherTwist_iff_of_lt_one (by linarith)]
  constructor <;> intro h <;> linarith

/-- Exact one-sided coefficient-faithfulness wall of the oriented comparison. -/
theorem primeVariableIdealResolvedCoefficientLanding_injective_iff
    {t : ℝ} (ht : -1 < t) :
    Function.Injective (primeVariableIdealResolvedCoefficientLanding t) ↔
      t ≤ 0 := by
  change Function.Injective
      (fun c : ℂ => c • primeVariableIdealResolvedCoefficientClass t) ↔
    t ≤ 0
  rw [coefficientLanding_injective_iff_class_ne_zero,
    primeVariableIdealResolvedCoefficientClass_ne_zero_iff ht]

/-- Both Gamma-reflected orientations are coefficient-faithful exactly at neutral grade. -/
theorem reflected_primeVariableIdealResolvedCoefficientLandings_injective_iff
    {t : ℝ} (ht : |t| < 1) :
    (Function.Injective (primeVariableIdealResolvedCoefficientLanding t) ∧
      Function.Injective (primeVariableIdealResolvedCoefficientLanding (-t))) ↔
      t = 0 := by
  rw [primeVariableIdealResolvedCoefficientLanding_injective_iff
      (abs_lt.mp ht).1,
    primeVariableIdealResolvedCoefficientLanding_injective_iff
      (by linarith [(abs_lt.mp ht).2])]
  constructor
  · rintro ⟨h₁, h₂⟩
    linarith
  · rintro rfl
    simp

/-- At an actual Xi divisor copy, simultaneous reflected coefficient faithfulness is precisely
the critical-line condition.  This is an unconditional equivalence, not an assumption that either
landing is faithful. -/
theorem xi_reflected_primeVariableIdealResolvedCoefficientLandings_injective_iff
    (rho : XiDivisorSupport) :
    (Function.Injective
        (primeVariableIdealResolvedCoefficientLanding
          (2 * (rho : ℂ).re - 1)) ∧
      Function.Injective
        (primeVariableIdealResolvedCoefficientLanding
          (-(2 * (rho : ℂ).re - 1)))) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflected_primeVariableIdealResolvedCoefficientLandings_injective_iff
    (xiCenteredPrimeIdealRate_abs_lt_one rho)]
  constructor <;> intro h <;> linarith

/-! ## Source Stokes comparison carrying the retained rational-adelic class -/

/-- Period-normalized comparison from actual rational-adelic relative `H1` to the resolved
variable-ideal coefficient line at one Xi divisor.  Actual leading Xi jet is retained as its
coefficient. -/
def ccmRationalAdelicPrimeXiVariableIdealStokesComparison
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ]
      (PrimeTraceSequence ⧸ primeReflectedCharacterPullbackIdeal
        (2 * (rho : ℂ).re - 1)) where
  toFun x :=
    (ccmRationalAdelicPrimeRelativeH1StokesRegulator p x *
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho)) •
      primeVariableIdealResolvedCoefficientClass
        (2 * (rho : ℂ).re - 1)
  map_add' x y := by
    rw [map_add, add_mul, add_smul]
  map_smul' c x := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    rw [mul_assoc, mul_smul]

/-- Retained source class lands on actual leading Xi jet times resolved Fisher class. -/
theorem ccmRationalAdelicPrimeXiVariableIdealStokesComparison_class
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiVariableIdealStokesComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) =
      iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) •
        primeVariableIdealResolvedCoefficientClass
          (2 * (rho : ℂ).re - 1) := by
  change
    (ccmRationalAdelicPrimeRelativeH1StokesRegulator p
        (ccmRationalAdelicPrimeRelativeClass p) *
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho)) •
      primeVariableIdealResolvedCoefficientClass
        (2 * (rho : ℂ).re - 1) = _
  rw [ccmRationalAdelicPrimeRelativeH1StokesRegulator_class, one_mul]

/-- Reporter square with existing strict resolved chain map: both paths carry exactly the same
prime-localized, multiplicity-leading Xi coefficient. -/
theorem ccmRationalAdelicPrimeXiVariableIdealStokesComparison_resolvedBoundary
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiVariableIdealStokesComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) =
      (primeDepthBVWoldXiResolvedCovariantD0
        (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p)
        rho (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p)).2 •
        primeVariableIdealResolvedCoefficientClass
          (2 * (rho : ℂ).re - 1) := by
  rw [ccmRationalAdelicPrimeXiVariableIdealStokesComparison_class,
    ccmRationalAdelicPrimeRelativeXiComparison_class_landing_snd]

/-- Physical specialization of source Stokes comparison into fixed first-trace quotient. -/
def ccmRationalAdelicPrimeFixedXiStokesComparison
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ]
      (PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal) :=
  (primeVariableIdealFixedComparison (2 * (rho : ℂ).re - 1)).comp
    (ccmRationalAdelicPrimeXiVariableIdealStokesComparison p rho)

/-- Exact physical landing: actual leading Xi coefficient times reflected fixed Fisher class. -/
theorem ccmRationalAdelicPrimeFixedXiStokesComparison_class
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeFixedXiStokesComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) =
      iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) •
        primeFixedPhysicalFisherClass (-(2 * (rho : ℂ).re - 1)) := by
  rw [ccmRationalAdelicPrimeFixedXiStokesComparison, LinearMap.comp_apply,
    ccmRationalAdelicPrimeXiVariableIdealStokesComparison_class,
    map_smul, primeVariableIdealFixedComparison_coefficientClass]

/-- Physical comparison retains source Stokes coefficient exactly on one oriented half-grade.
This is a classification; nonerasure is not assumed. -/
theorem ccmRationalAdelicPrimeFixedXiStokesComparison_class_ne_zero_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeFixedXiStokesComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 ↔
      2 * (rho : ℂ).re - 1 ≤ 0 := by
  rw [ccmRationalAdelicPrimeFixedXiStokesComparison_class,
    smul_ne_zero_iff]
  have hjet : iteratedDeriv (xiSupportMultiplicity rho) XiC
      (xiSpectralPointSupport rho) ≠ 0 :=
    iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho
  rw [and_iff_right hjet]
  rw [primeFixedPhysicalFisherClass_ne_zero_iff
      (by linarith [(abs_lt.mp (xiCenteredPrimeIdealRate_abs_lt_one rho)).1])]
  constructor <;> intro h <;> linarith

/-- Gamma-reflected orientation of the same source Stokes comparison. -/
def ccmRationalAdelicPrimeReflectedXiVariableIdealStokesComparison
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ]
      (PrimeTraceSequence ⧸ primeReflectedCharacterPullbackIdeal
        (-(2 * (rho : ℂ).re - 1))) where
  toFun x :=
    (ccmRationalAdelicPrimeRelativeH1StokesRegulator p x *
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho)) •
      primeVariableIdealResolvedCoefficientClass
        (-(2 * (rho : ℂ).re - 1))
  map_add' x y := by
    rw [map_add, add_mul, add_smul]
  map_smul' c x := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    rw [mul_assoc, mul_smul]

/-- Fixed physical specialization in Gamma-reflected orientation. -/
def ccmRationalAdelicPrimeReflectedFixedXiStokesComparison
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ]
      (PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal) :=
  (primeVariableIdealFixedComparison (-(2 * (rho : ℂ).re - 1))).comp
    (ccmRationalAdelicPrimeReflectedXiVariableIdealStokesComparison p rho)

theorem ccmRationalAdelicPrimeReflectedFixedXiStokesComparison_class
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeReflectedFixedXiStokesComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) =
      iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) •
        primeFixedPhysicalFisherClass (2 * (rho : ℂ).re - 1) := by
  change primeVariableIdealFixedComparison (-(2 * (rho : ℂ).re - 1))
      (((ccmRationalAdelicPrimeRelativeH1StokesRegulator p
        (ccmRationalAdelicPrimeRelativeClass p)) *
          iteratedDeriv (xiSupportMultiplicity rho) XiC
            (xiSpectralPointSupport rho)) •
        primeVariableIdealResolvedCoefficientClass
          (-(2 * (rho : ℂ).re - 1))) = _
  rw [ccmRationalAdelicPrimeRelativeH1StokesRegulator_class, one_mul,
    map_smul, primeVariableIdealFixedComparison_coefficientClass, neg_neg]

theorem ccmRationalAdelicPrimeReflectedFixedXiStokesComparison_class_ne_zero_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeReflectedFixedXiStokesComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 ↔
      0 ≤ 2 * (rho : ℂ).re - 1 := by
  rw [ccmRationalAdelicPrimeReflectedFixedXiStokesComparison_class,
    smul_ne_zero_iff]
  have hjet : iteratedDeriv (xiSupportMultiplicity rho) XiC
      (xiSpectralPointSupport rho) ≠ 0 :=
    iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho
  rw [and_iff_right hjet]
  exact primeFixedPhysicalFisherClass_ne_zero_iff
    (by linarith [(abs_lt.mp (xiCenteredPrimeIdealRate_abs_lt_one rho)).2])

/-- Both source-derived fixed-ideal orientations retain the actual class exactly at one critical
Xi fibre. -/
theorem ccmRationalAdelicPrimeReflectedFixedXiStokesComparisons_class_ne_zero_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeFixedXiStokesComparison p rho
          (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 ∧
      ccmRationalAdelicPrimeReflectedFixedXiStokesComparison p rho
          (ccmRationalAdelicPrimeRelativeClass p) ≠ 0) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [ccmRationalAdelicPrimeFixedXiStokesComparison_class_ne_zero_iff,
    ccmRationalAdelicPrimeReflectedFixedXiStokesComparison_class_ne_zero_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    linarith
  · intro h
    constructor <;> linarith

/-- Global coefficient-faithfulness target for two source Stokes orientations. -/
def CCMRationalAdelicPrimeFixedXiStokesComparisonsCoefficientFaithful : Prop :=
  ∀ p : Nat.Primes, ∀ rho : XiDivisorSupport,
    ccmRationalAdelicPrimeFixedXiStokesComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 ∧
      ccmRationalAdelicPrimeReflectedFixedXiStokesComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) ≠ 0

/-- Exact global frontier: simultaneous source-derived fixed-ideal coefficient faithfulness is RH.
No faithfulness premise is used in constructing either comparison. -/
theorem ccmRationalAdelicPrimeFixedXiStokesComparisonsCoefficientFaithful_iff_riemannHypothesis :
    CCMRationalAdelicPrimeFixedXiStokesComparisonsCoefficientFaithful ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hline : z.re = 1 / 2 :=
      (ccmRationalAdelicPrimeReflectedFixedXiStokesComparisons_class_ne_zero_iff
        p rho).mp (h p rho)
    have hzgt : 1 / 2 < z.re := mem_rightHalf.mp hz
    linarith
  · intro hRH p rho
    exact
      (ccmRationalAdelicPrimeReflectedFixedXiStokesComparisons_class_ne_zero_iff
        p rho).mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)

/-! ## Explicit coefficient-faithful resolved-frame factorization -/

/-- Variable-ideal resolved frame: pullback-ideal coordinate plus an independent complex
coefficient line. -/
abbrev PrimeVariableIdealResolvedFrame (t : ℝ) :=
  primeReflectedCharacterPullbackIdeal t × ℂ

/-- Coefficient reporter retained before physical trace-ideal specialization. -/
def primeVariableIdealResolvedFrameCoefficient (t : ℝ) :
    PrimeVariableIdealResolvedFrame t →ₗ[ℂ] ℂ :=
  LinearMap.snd ℂ _ _

/-- Fixed physical realization of a resolved frame.  Pullback-ideal coordinate vanishes in fixed
quotient; coefficient multiplies reflected Fisher conormal. -/
def primeVariableIdealResolvedFramePhysicalComparison (t : ℝ) :
    PrimeVariableIdealResolvedFrame t →ₗ[ℂ]
      (PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal) where
  toFun x := x.2 • primeFixedPhysicalFisherClass (-t)
  map_add' x y := by rw [Prod.snd_add, add_smul]
  map_smul' c x := by
    simp [smul_eq_mul, smul_smul]

/-- Actual source Stokes class in coefficient-faithful variable-ideal resolved frame. -/
def ccmRationalAdelicPrimeXiResolvedFrameComparison
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ]
      PrimeVariableIdealResolvedFrame (2 * (rho : ℂ).re - 1) where
  toFun x :=
    (0, ccmRationalAdelicPrimeRelativeH1StokesRegulator p x *
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho))
  map_add' x y := by
    ext
    · simp
    · rw [map_add, add_mul, Prod.snd_add]
  map_smul' c x := by
    ext
    · simp
    · simp only [map_smul, smul_eq_mul, RingHom.id_apply, Prod.smul_snd]
      ring

/-- Retained rational-adelic class lands on nonzero actual Xi coefficient before physical
quotienting. -/
theorem ccmRationalAdelicPrimeXiResolvedFrameComparison_class
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiResolvedFrameComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) =
      (0, iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho)) := by
  ext
  · rfl
  · change ccmRationalAdelicPrimeRelativeH1StokesRegulator p
        (ccmRationalAdelicPrimeRelativeClass p) *
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho) = _
    rw [ccmRationalAdelicPrimeRelativeH1StokesRegulator_class, one_mul]

theorem ccmRationalAdelicPrimeXiResolvedFrameComparison_class_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiResolvedFrameComparison p rho
        (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 := by
  rw [ccmRationalAdelicPrimeXiResolvedFrameComparison_class]
  intro h
  have hsnd := congrArg Prod.snd h
  simp only [Prod.snd_zero] at hsnd
  exact iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho hsnd

/-- Resolved-frame coefficient reporter equals reporter of existing strict positive resolved Xi
boundary on retained source class. -/
theorem ccmRationalAdelicPrimeXiResolvedFrameCoefficient_eq_resolvedBoundary
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    primeVariableIdealResolvedFrameCoefficient (2 * (rho : ℂ).re - 1)
        (ccmRationalAdelicPrimeXiResolvedFrameComparison p rho
          (ccmRationalAdelicPrimeRelativeClass p)) =
      (primeDepthBVWoldXiResolvedCovariantD0
        (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p)
        rho (ccmRationalAdelicPrimeRelativeXiCellZero p)
          (ccmRationalAdelicPrimeRelativeXiCellOne p)).2 := by
  rw [ccmRationalAdelicPrimeXiResolvedFrameComparison_class,
    primeVariableIdealResolvedFrameCoefficient,
    LinearMap.snd_apply,
    ccmRationalAdelicPrimeRelativeXiComparison_class_landing_snd]

/-- Previously constructed fixed comparison factors through coefficient-faithful resolved frame. -/
theorem ccmRationalAdelicPrimeFixedXiStokesComparison_factorization
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (primeVariableIdealResolvedFramePhysicalComparison
      (2 * (rho : ℂ).re - 1)).comp
        (ccmRationalAdelicPrimeXiResolvedFrameComparison p rho) =
      ccmRationalAdelicPrimeFixedXiStokesComparison p rho := by
  apply LinearMap.ext
  intro x
  change (ccmRationalAdelicPrimeRelativeH1StokesRegulator p x *
      iteratedDeriv (xiSupportMultiplicity rho) XiC
        (xiSpectralPointSupport rho)) •
      primeFixedPhysicalFisherClass (-(2 * (rho : ℂ).re - 1)) = _
  rw [ccmRationalAdelicPrimeFixedXiStokesComparison,
    LinearMap.comp_apply]
  change _ = primeVariableIdealFixedComparison (2 * (rho : ℂ).re - 1)
      ((ccmRationalAdelicPrimeRelativeH1StokesRegulator p x *
        iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho)) •
        primeVariableIdealResolvedCoefficientClass
          (2 * (rho : ℂ).re - 1))
  rw [map_smul, primeVariableIdealFixedComparison_coefficientClass]

end

end RHTower
