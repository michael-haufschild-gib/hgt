import GaloisForLFunctions.RHTower.RouteRPrimeLogEssentialCapFixedGradePhaseDagger
import GaloisForLFunctions.RHTower.DeningerMeyerAntiReflectedGaussianOddMultiplier
import GaloisForLFunctions.RHTower.CCMRationalAdelicReflectedGaussianCartierComparison

/-!
# Gaussian source Hermiticity for Route R phase quadratures

The physical even and oriented-odd prime quadratures are not merely scalar
repackagings.  They are the normalized zeroth Xi evaluations of two explicit
prime-log Meyer source classes.  The even class is fixed by Paugam reflection;
the oriented-odd class is anti-fixed.  Their pair is therefore fixed by the
corresponding oriented source involution.

The period-one rational-adelic prime class maps coefficient-faithfully to this
mixed source pair.  On the physical divisor, both normalized evaluations obey
the unconditional antiunitary line-conjugation law.  This is the precise
Hermiticity inherited from the source before identifying two divisor fibres.

Fixed-grade evaluation is kept separate.  Equality of each line-conjugate
value with its value in the original fibre is proved equivalent to joint
scalar Hermiticity, singular Stokes flatness, and globally RH.  Thus no
variable-grade boundary equality is silently used as a same-fibre descent.
-/

open Complex
open GaloisForLFunctions

namespace RHTower

noncomputable section

open DeningerMeyerGaussianGreen

/-- Prime half-density character written in the centered exponential chart. -/
theorem ccmRationalAdelicPrimeHalfDensityCharacter_eq_centeredExp
    (p : Nat.Primes) (s : ℂ) :
    bilateralHalfDensityCharacter (p : ℕ) s =
      Complex.exp (-((Real.log (p : ℝ) : ℂ) * (s - 1 / 2))) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
  rw [bilateralHalfDensityCharacter, Complex.cpow_def_of_ne_zero hpC, hlog]
  congr 1
  norm_num
  ring

/-- Reflection-even prime-log Meyer source class. -/
def ccmRationalAdelicPrimeXiGaussianEvenSourceClass
    (p : Nat.Primes) : DeningerMeyerStrongLogCohomology :=
  deningerMeyerReflectedGaussianCountertransportClass (Real.log (p : ℝ))

/-- Oriented reflection-odd prime-log Meyer source class.  The factor `-I`
matches the physical oriented-odd quadrature exactly. -/
def ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass
    (p : Nat.Primes) : DeningerMeyerStrongLogCohomology :=
  (-I) •
    deningerMeyerAntiReflectedGaussianCountertransportClass (Real.log (p : ℝ))

/-- Even source class has positive Paugam parity. -/
theorem ccmRationalAdelicPrimeXiGaussianEvenSourceClass_J_fixed
    (p : Nat.Primes) :
    deningerMeyerStrongLogCohomologyJ
        (ccmRationalAdelicPrimeXiGaussianEvenSourceClass p) =
      ccmRationalAdelicPrimeXiGaussianEvenSourceClass p := by
  exact deningerMeyerReflectedGaussianCountertransportClass_J_fixed _

/-- Oriented-odd source class has negative Paugam parity. -/
theorem ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass_J_antiFixed
    (p : Nat.Primes) :
    deningerMeyerStrongLogCohomologyJ
        (ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass p) =
      -ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass p := by
  rw [ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass, map_smul,
    deningerMeyerAntiReflectedGaussianCountertransportClass_J_antiFixed]
  module

/-- Exact source evaluation of the physical even quadrature.  The Gaussian
horizon grade is explicit and nonzero. -/
theorem ccmRationalAdelicPrimeXiGaussianEvenSourceClass_evaluation
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ : DeningerArithmeticJetIndex rho)
        (ccmRationalAdelicPrimeXiGaussianEvenSourceClass p) =
      ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho *
        reflectedGaussianHorizonGrade
          (ccmRationalAdelicPrimeXiLeadingZeroCopy rho) := by
  rw [ccmRationalAdelicPrimeXiGaussianEvenSourceClass,
    deningerMeyerReflectedGaussianCountertransportClass_evaluation,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
    ccmRationalAdelicPrimeHalfDensityCharacter_eq_centeredExp,
    ccmRationalAdelicPrimeHalfDensityCharacter_eq_centeredExp,
    reflectedGaussianHorizonGrade]
  have hreflect : (xiZeroReflectEquiv rho : ℂ) = 1 - (rho : ℂ) := rfl
  rw [hreflect, deningerMeyerReflectedLogGaussianSource_mellin]
  congr 1
  ring

/-- Exact source evaluation of the physical oriented-odd quadrature. -/
theorem ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass_evaluation
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerMeyerXiSupportJetEvaluationLM rho
        (⟨0, xiSupportMultiplicity_pos rho⟩ : DeningerArithmeticJetIndex rho)
        (ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass p) =
      ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p rho *
        reflectedGaussianHorizonGrade
          (ccmRationalAdelicPrimeXiLeadingZeroCopy rho) := by
  rw [ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass, map_smul,
    deningerMeyerAntiReflectedGaussianCountertransportClass_evaluation,
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment,
    ccmRationalAdelicPrimeHalfDensityCharacter_eq_centeredExp,
    ccmRationalAdelicPrimeHalfDensityCharacter_eq_centeredExp,
    reflectedGaussianHorizonGrade]
  have hreflect : (xiZeroReflectEquiv rho : ℂ) = 1 - (rho : ℂ) := rfl
  rw [hreflect, deningerMeyerReflectedLogGaussianSource_mellin]
  simp only [smul_eq_mul, ccmRationalAdelicPrimeXiLeadingZeroCopy]
  ring

/-- Mixed even/oriented-odd source pair attached to one ordinary prime. -/
def ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair
    (p : Nat.Primes) :
    DeningerMeyerStrongLogCohomology × DeningerMeyerStrongLogCohomology :=
  (ccmRationalAdelicPrimeXiGaussianEvenSourceClass p,
    ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass p)

/-- Both quadrature channels cannot vanish: after nonzero Gaussian
normalization their sum and difference recover a nonzero prime character. -/
theorem ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair_ne_zero
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair p ≠ 0 := by
  intro hzero
  have heven : ccmRationalAdelicPrimeXiGaussianEvenSourceClass p = 0 :=
    congrArg Prod.fst hzero
  have hodd : ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass p = 0 :=
    congrArg Prod.snd hzero
  let q : XiZeroCopy := Classical.choice inferInstance
  have hevenEval := congrArg
    (deningerMeyerXiSupportJetEvaluationLM q.1
      (⟨0, xiSupportMultiplicity_pos q.1⟩ : DeningerArithmeticJetIndex q.1)) heven
  have hoddEval := congrArg
    (deningerMeyerXiSupportJetEvaluationLM q.1
      (⟨0, xiSupportMultiplicity_pos q.1⟩ : DeningerArithmeticJetIndex q.1)) hodd
  rw [ccmRationalAdelicPrimeXiGaussianEvenSourceClass_evaluation, map_zero]
    at hevenEval
  rw [ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass_evaluation, map_zero]
    at hoddEval
  have hgrade : reflectedGaussianHorizonGrade
      (ccmRationalAdelicPrimeXiLeadingZeroCopy q.1) ≠ 0 :=
    reflectedGaussianHorizonGrade_ne_zero _
  have hevenMoment :
      ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p q.1 = 0 :=
    (mul_eq_zero.mp hevenEval).resolve_right hgrade
  have hoddMoment :
      ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p q.1 = 0 :=
    (mul_eq_zero.mp hoddEval).resolve_right hgrade
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
    ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv] at hevenMoment
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment,
    ccmRationalAdelicPrimeXiPhysicalCharacter_reflection_eq_inv] at hoddMoment
  have hsub :
      bilateralHalfDensityCharacter (p : ℕ) (q.1 : ℂ) -
          (bilateralHalfDensityCharacter (p : ℕ) (q.1 : ℂ))⁻¹ = 0 :=
    (mul_eq_zero.mp hoddMoment).resolve_left I_ne_zero
  have hz : bilateralHalfDensityCharacter (p : ℕ) (q.1 : ℂ) = 0 := by
    linear_combination (1 / 2 : ℂ) * hevenMoment + (1 / 2 : ℂ) * hsub
  exact (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (by exact_mod_cast p.2.ne_zero))) hz

/-- Coefficient-faithful rational-adelic period map into the two genuine
Gaussian quadrature source classes. -/
def ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ]
      (DeningerMeyerStrongLogCohomology × DeningerMeyerStrongLogCohomology) :=
  (LinearMap.toSpanSingleton ℂ _
      (ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair p)).comp
    (ccmRationalAdelicPrimeRelativeH1StokesRegulator p)

/-- Retained rational-adelic atom lands on the literal mixed source pair. -/
theorem ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison_class
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison p
        (ccmRationalAdelicPrimeRelativeClass p) =
      ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair p := by
  simp [ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison,
    ccmRationalAdelicPrimeRelativeH1StokesRegulator_class]

/-- Mixed Gaussian comparison loses exactly the kernel of the independent
period-one Stokes regulator. -/
theorem ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison_eq_zero_iff
    (p : Nat.Primes) (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison p x = 0 ↔
      ccmRationalAdelicPrimeRelativeH1StokesRegulator p x = 0 := by
  simp only [ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison,
    LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  constructor
  · intro h
    exact (smul_eq_zero.mp h).resolve_right
      (ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair_ne_zero p)
  · intro h
    rw [h, zero_smul]

/-- Oriented source involution: Paugam reflection on the even channel and
minus Paugam reflection on the oriented-odd channel. -/
def ccmRationalAdelicPrimeXiGaussianQuadratureSourceJ :
    (DeningerMeyerStrongLogCohomology × DeningerMeyerStrongLogCohomology) →ₗ[ℂ]
      (DeningerMeyerStrongLogCohomology × DeningerMeyerStrongLogCohomology) where
  toFun x := (deningerMeyerStrongLogCohomologyJ x.1,
    -deningerMeyerStrongLogCohomologyJ x.2)
  map_add' x y := by
    apply Prod.ext
    · exact map_add _ _ _
    · change -deningerMeyerStrongLogCohomologyJ (x.2 + y.2) =
          -deningerMeyerStrongLogCohomologyJ x.2 +
            -deningerMeyerStrongLogCohomologyJ y.2
      rw [map_add]
      module
  map_smul' c x := by
    apply Prod.ext
    · exact map_smul _ _ _
    · change -deningerMeyerStrongLogCohomologyJ (c • x.2) =
          c • (-deningerMeyerStrongLogCohomologyJ x.2)
      rw [map_smul]
      module

/-- Oriented source involution squares to the identity. -/
theorem ccmRationalAdelicPrimeXiGaussianQuadratureSourceJ_sq
    (x : DeningerMeyerStrongLogCohomology × DeningerMeyerStrongLogCohomology) :
    ccmRationalAdelicPrimeXiGaussianQuadratureSourceJ
        (ccmRationalAdelicPrimeXiGaussianQuadratureSourceJ x) = x := by
  ext <;> simp [ccmRationalAdelicPrimeXiGaussianQuadratureSourceJ]

/-- Mixed prime-log source pair is unconditionally Hermitian for the
oriented source involution. -/
theorem ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair_J_fixed
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeXiGaussianQuadratureSourceJ
        (ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair p) =
      ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair p := by
  ext
  · exact ccmRationalAdelicPrimeXiGaussianEvenSourceClass_J_fixed p
  · simp [ccmRationalAdelicPrimeXiGaussianQuadratureSourceJ,
      ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair,
      ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass_J_antiFixed]

/-- Every coefficient of the rational-adelic comparison inherits the same
unconditional oriented source Hermiticity. -/
theorem ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison_J_fixed
    (p : Nat.Primes) (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    ccmRationalAdelicPrimeXiGaussianQuadratureSourceJ
        (ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison p x) =
      ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison p x := by
  rw [ccmRationalAdelicPrimeXiGaussianQuadratureSourceComparison,
    LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, map_smul,
    ccmRationalAdelicPrimeXiGaussianQuadratureSourcePair_J_fixed]

/-- Physical even quadrature is Hermitian under divisor line conjugation,
without identifying the two divisor fibres. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_lineConj
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p
        (xiZeroLineConjEquiv rho) =
      starRingEnd ℂ
        (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho) := by
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment]
  repeat' rw [ccmRationalAdelicPrimeHalfDensityCharacter_eq_centeredExp]
  have hreflect (q : XiDivisorSupport) :
      (xiZeroReflectEquiv q : ℂ) = 1 - (q : ℂ) := rfl
  rw [hreflect, hreflect]
  simp only [xiZeroLineConjEquiv_apply, map_add, ← Complex.exp_conj,
    map_neg, map_mul, map_sub, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal]
  norm_num
  ring

/-- Physical oriented-odd quadrature obeys the same unconditional
antiunitary line-conjugation law. -/
theorem ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment_lineConj
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p
        (xiZeroLineConjEquiv rho) =
      starRingEnd ℂ
        (ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p rho) := by
  rw [ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment,
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment]
  repeat' rw [ccmRationalAdelicPrimeHalfDensityCharacter_eq_centeredExp]
  have hreflect (q : XiDivisorSupport) :
      (xiZeroReflectEquiv q : ℂ) = 1 - (q : ℂ) := rfl
  rw [hreflect, hreflect]
  simp only [xiZeroLineConjEquiv_apply, map_mul, map_sub,
    ← Complex.exp_conj, map_neg, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal, conj_I]
  norm_num
  ring

/-- **Unconditional physical inheritance theorem.**  Both physical
quadratures inherit antiunitary source Hermiticity on the full divisor before
any fixed-fibre identification. -/
theorem ccmRationalAdelicPrimeXiPhysicalQuadratures_inherit_sourceLineConjHermiticity
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p
          (xiZeroLineConjEquiv rho) =
        starRingEnd ℂ
          (ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho) ∧
      ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p
          (xiZeroLineConjEquiv rho) =
        starRingEnd ℂ
          (ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p rho) :=
  ⟨ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_lineConj p rho,
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment_lineConj p rho⟩

/-- The nonzero Gaussian normalizing grade is itself Hermitian under line
conjugation at the leading divisor copy. -/
theorem ccmRationalAdelicPrimeXiLeadingGaussianGrade_lineConj
    (rho : XiDivisorSupport) :
    reflectedGaussianHorizonGrade
        (ccmRationalAdelicPrimeXiLeadingZeroCopy (xiZeroLineConjEquiv rho)) =
      starRingEnd ℂ (reflectedGaussianHorizonGrade
        (ccmRationalAdelicPrimeXiLeadingZeroCopy rho)) := by
  rw [reflectedGaussianHorizonGrade, reflectedGaussianHorizonGrade,
    deningerMeyerReflectedLogGaussianSource_mellin,
    deningerMeyerReflectedLogGaussianSource_mellin]
  simp only [ccmRationalAdelicPrimeXiLeadingZeroCopy,
    xiZeroLineConjEquiv_apply, ← Complex.exp_conj, map_div₀, map_mul,
    map_pow, map_sub, map_one, map_ofNat, Complex.conj_ofReal]
  congr 1
  ring

/-- Even source evaluation inherits physical line-conjugation Hermiticity. -/
theorem ccmRationalAdelicPrimeXiGaussianEvenSourceClass_evaluation_lineConj
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerMeyerXiSupportJetEvaluationLM (xiZeroLineConjEquiv rho)
        (⟨0, xiSupportMultiplicity_pos (xiZeroLineConjEquiv rho)⟩ :
          DeningerArithmeticJetIndex (xiZeroLineConjEquiv rho))
        (ccmRationalAdelicPrimeXiGaussianEvenSourceClass p) =
      starRingEnd ℂ
        (deningerMeyerXiSupportJetEvaluationLM rho
          (⟨0, xiSupportMultiplicity_pos rho⟩ : DeningerArithmeticJetIndex rho)
          (ccmRationalAdelicPrimeXiGaussianEvenSourceClass p)) := by
  rw [ccmRationalAdelicPrimeXiGaussianEvenSourceClass_evaluation,
    ccmRationalAdelicPrimeXiGaussianEvenSourceClass_evaluation,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_lineConj,
    ccmRationalAdelicPrimeXiLeadingGaussianGrade_lineConj, map_mul]

/-- Oriented-odd source evaluation inherits physical line-conjugation
Hermiticity. -/
theorem
    ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass_evaluation_lineConj
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    deningerMeyerXiSupportJetEvaluationLM (xiZeroLineConjEquiv rho)
        (⟨0, xiSupportMultiplicity_pos (xiZeroLineConjEquiv rho)⟩ :
          DeningerArithmeticJetIndex (xiZeroLineConjEquiv rho))
        (ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass p) =
      starRingEnd ℂ
        (deningerMeyerXiSupportJetEvaluationLM rho
          (⟨0, xiSupportMultiplicity_pos rho⟩ : DeningerArithmeticJetIndex rho)
          (ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass p)) := by
  rw [ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass_evaluation,
    ccmRationalAdelicPrimeXiGaussianOrientedOddSourceClass_evaluation,
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment_lineConj,
    ccmRationalAdelicPrimeXiLeadingGaussianGrade_lineConj, map_mul]

/-- Exact missing fixed-grade operation: descend both antiunitary quadrature
values from the line-conjugate divisor fibre to the original fibre. -/
def CCMRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p
        (xiZeroLineConjEquiv rho) =
      ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment p rho ∧
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p
        (xiZeroLineConjEquiv rho) =
      ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment p rho

/-- Fixed-grade descent is exactly scalar Hermiticity of both quadratures. -/
theorem ccmRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent_iff_hermitian
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent p rho ↔
      CCMRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian p rho := by
  rw [CCMRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent,
    CCMRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseMoment_lineConj,
    ccmRationalAdelicPrimeXiReflectedPhysicalOddPhaseMoment_lineConj]
  constructor
  · rintro ⟨heven, hodd⟩
    exact ⟨Complex.conj_eq_iff_im.mp heven,
      Complex.conj_eq_iff_im.mp hodd⟩
  · rintro ⟨heven, hodd⟩
    exact ⟨Complex.conj_eq_iff_im.mpr heven,
      Complex.conj_eq_iff_im.mpr hodd⟩

/-- Fixed-grade Gaussian descent is the singular Stokes-flatness endpoint. -/
theorem ccmRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent_iff_flat
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent p rho ↔
      CCMRationalAdelicPrimeXiFixedOrientationSingularStokesFlat rho := by
  rw [ccmRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent_iff_hermitian,
    ccmRationalAdelicPrimeXiReflectedPhysicalPhaseQuadratureHermitian_iff_flat]

/-- The new source-native fixed-grade statement agrees exactly with Route R's
fixed Cartier phase square. -/
theorem
    ccmRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent_iff_cartierIntertwining
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent p rho ↔
      CCMRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining p rho := by
  rw [ccmRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent_iff_flat,
    ccmRationalAdelicPrimeXiFixedGradeCartierPhaseIntertwining_iff_landing,
    ccmRationalAdelicPrimeXiReflectedPhaseQuadratureLanding_iff_flat]

/-- Global same-fibre descent of the unconditionally Hermitian physical field
is exactly RH. -/
theorem forall_ccmRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent_iff_RH
    (p : Nat.Primes) :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent p rho) ↔
      RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiFixedOrientationSingularStokesFlat_iff_RH]
  exact forall_congr'
    (ccmRationalAdelicPrimeXiGaussianQuadratureFixedGradeDescent_iff_flat p)

end

end RHTower
