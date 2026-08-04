import GaloisForLFunctions.RHTower.PrimeFirstTraceGradedVariableIdealFixedXiComparison

/-!
# Fixed-trace-ideal Gamma cofinal normalizer frontier

Finite-place Gamma changes are invisible in the fixed first-trace quotient: their difference from
the identity is finitely supported and hence summable.  The full all-prime reflected character is
different.  In the moderate strip it preserves the fixed summable ideal exactly on one half-grade,
and it normalizes that ideal in both directions exactly at neutral grade.

Thus fixed-ideal physical information is created only at the singular cofinal all-prime boundary.
No finite adelic naturality square can prove its non-erasure.  The theorem is unconditional and
does not assert the remaining global source law.
-/

open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The raw all-prime Gamma character preserves the fixed first-trace ideal. -/
def PrimeReflectedCharacterPreservesFixedIdeal (t : ℝ) : Prop :=
  ∀ a : PrimeTraceSequence,
    a ∈ primeFirstTraceSummableIdeal →
      primeReflectedCharacterMultiplier t a ∈ primeFirstTraceSummableIdeal

/-- A nonnegative centered grade damps every prime coefficient and therefore preserves `ell1`. -/
theorem primeReflectedCharacter_preservesFixedIdeal_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    PrimeReflectedCharacterPreservesFixedIdeal t := by
  intro a ha
  change Summable (primeReflectedCharacterMultiplier t a)
  apply Summable.of_norm_bounded ha.norm
  intro p
  rw [primeReflectedCharacterMultiplier_apply, norm_mul]
  have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by
    exact_mod_cast p.2.one_lt.le
  have hpow : (p.1 : ℝ) ^ (-2 * t) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
  have hpow0 : 0 ≤ (p.1 : ℝ) ^ (-2 * t) :=
    (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpow0]
  exact mul_le_of_le_one_left (norm_nonneg _) hpow

/-- In the moderate strip, preservation of the fixed first-trace ideal has the sharp one-sided
Gamma wall. -/
theorem primeReflectedCharacter_preservesFixedIdeal_iff
    {t : ℝ} (ht : |t| < 1) :
    PrimeReflectedCharacterPreservesFixedIdeal t ↔ 0 ≤ t := by
  constructor
  · intro hpres
    by_contra hnot
    have htneg : t < 0 := lt_of_not_ge hnot
    have hsource :
        primeActivationOccupancyFisherComplexTwist t ∈
          primeFirstTraceSummableIdeal := by
      change Summable (primeActivationOccupancyFisherComplexTwist t)
      rw [show Summable (primeActivationOccupancyFisherComplexTwist t) ↔
          Summable (primeActivationOccupancyFisherTwist t) by
        exact Complex.summable_ofReal]
      exact (summable_primeActivationOccupancyFisherTwist_iff_of_lt_one
        (lt_trans htneg (by norm_num))).2 htneg
    have himage := hpres _ hsource
    rw [primeReflectedCharacterMultiplier_fisher] at himage
    have hclass := primeFixedPhysicalFisherClass_ne_zero_iff
      (t := -t) (by linarith [(abs_lt.mp ht).1])
    have hnonzero : primeFixedPhysicalFisherClass (-t) ≠ 0 :=
      hclass.2 (by linarith)
    apply hnonzero
    rw [primeFixedPhysicalFisherClass, Submodule.Quotient.mk_eq_zero]
    exact himage
  · exact primeReflectedCharacter_preservesFixedIdeal_of_nonneg

/-- Reflected preservation has the opposite half-grade wall. -/
theorem reflected_primeReflectedCharacter_preservesFixedIdeal_iff
    {t : ℝ} (ht : |t| < 1) :
    PrimeReflectedCharacterPreservesFixedIdeal (-t) ↔ t ≤ 0 := by
  rw [primeReflectedCharacter_preservesFixedIdeal_iff (by simpa [abs_neg] using ht)]
  constructor <;> intro h <;> linarith

/-- The fixed first-trace ideal is normalized in both Gamma orientations exactly at neutral
grade. -/
theorem reflected_primeReflectedCharacter_normalizesFixedIdeal_iff
    {t : ℝ} (ht : |t| < 1) :
    (PrimeReflectedCharacterPreservesFixedIdeal t ∧
      PrimeReflectedCharacterPreservesFixedIdeal (-t)) ↔ t = 0 := by
  rw [primeReflectedCharacter_preservesFixedIdeal_iff ht,
    reflected_primeReflectedCharacter_preservesFixedIdeal_iff ht]
  constructor
  · rintro ⟨h₁, h₂⟩
    linarith
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

/-- Gamma multiplier restricted to a finite set of ordinary primes. -/
def primeFiniteReflectedCharacterMultiplier
    (K : Finset Nat.Primes) (t : ℝ) :
    PrimeTraceSequence →ₗ[ℂ] PrimeTraceSequence where
  toFun a p := if p ∈ K then
      (↑((p.1 : ℝ) ^ (-2 * t)) : ℂ) * a p
    else a p
  map_add' a b := by
    funext p
    by_cases hp : p ∈ K <;> simp [hp, mul_add]
  map_smul' c a := by
    funext p
    by_cases hp : p ∈ K
    · simp only [hp, if_pos, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [hp]

@[simp]
theorem primeFiniteReflectedCharacterMultiplier_apply
    (K : Finset Nat.Primes) (t : ℝ) (a : PrimeTraceSequence)
    (p : Nat.Primes) :
    primeFiniteReflectedCharacterMultiplier K t a p =
      if p ∈ K then (↑((p.1 : ℝ) ^ (-2 * t)) : ℂ) * a p else a p :=
  rfl

/-- Every finite-place Gamma change differs from the identity by a summable sequence. -/
theorem summable_primeFiniteReflectedCharacterMultiplier_sub
    (K : Finset Nat.Primes) (t : ℝ) (a : PrimeTraceSequence) :
    Summable (primeFiniteReflectedCharacterMultiplier K t a - a) := by
  apply summable_of_hasFiniteSupport
  apply K.finite_toSet.subset
  intro p hp
  by_contra hpK
  apply hp
  have hpK' : p ∉ K := by simpa using hpK
  simp [primeFiniteReflectedCharacterMultiplier_apply, hpK']

/-- Every finite-place Gamma action induces the identity on the fixed physical quotient. -/
theorem primeFiniteReflectedCharacterMultiplier_quotient_eq
    (K : Finset Nat.Primes) (t : ℝ) (a : PrimeTraceSequence) :
    Submodule.Quotient.mk
        (primeFiniteReflectedCharacterMultiplier K t a) =
      (Submodule.Quotient.mk a :
        PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal) := by
  rw [Submodule.Quotient.eq]
  exact summable_primeFiniteReflectedCharacterMultiplier_sub K t a

/-- Finite-prime Fisher truncation. -/
def primeActivationOccupancyFisherFiniteTruncation
    (K : Finset Nat.Primes) (t : ℝ) : PrimeTraceSequence :=
  fun p => if p ∈ K then primeActivationOccupancyFisherComplexTwist t p else 0

theorem summable_primeActivationOccupancyFisherFiniteTruncation
    (K : Finset Nat.Primes) (t : ℝ) :
    Summable (primeActivationOccupancyFisherFiniteTruncation K t) := by
  apply summable_of_hasFiniteSupport
  apply K.finite_toSet.subset
  intro p hp
  by_contra hpK
  apply hp
  have hpK' : p ∉ K := by simpa using hpK
  simp [primeActivationOccupancyFisherFiniteTruncation, hpK']

/-- Every finite-prime Fisher stage is erased in the fixed first-trace quotient. -/
theorem primeActivationOccupancyFisherFiniteTruncation_class_eq_zero
    (K : Finset Nat.Primes) (t : ℝ) :
    (Submodule.Quotient.mk
        (primeActivationOccupancyFisherFiniteTruncation K t) :
      PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact summable_primeActivationOccupancyFisherFiniteTruncation K t

/-- The singular all-prime Gamma Bockstein: reflected Fisher class minus its source class in the
fixed first-trace quotient.  Unlike every finite-prime stage, this class can be nonzero. -/
def primeGammaCofinalBockstein (t : ℝ) :
    PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal :=
  primeFixedPhysicalFisherClass (-t) - primeFixedPhysicalFisherClass t

/-- Every finite-prime approximation to the Gamma Bockstein vanishes in the fixed quotient. -/
theorem primeFiniteGammaBockstein_eq_zero
    (K : Finset Nat.Primes) (t : ℝ) :
    (Submodule.Quotient.mk
          (primeFiniteReflectedCharacterMultiplier K t
            (primeActivationOccupancyFisherComplexTwist t)) :
        PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal) -
      primeFixedPhysicalFisherClass t = 0 := by
  rw [sub_eq_zero, primeFixedPhysicalFisherClass]
  exact primeFiniteReflectedCharacterMultiplier_quotient_eq K t _

/-- The full reflected physical pair is never jointly erased in the moderate strip. -/
theorem primeFixedPhysicalFisher_reflected_pair_ne_zero
    {t : ℝ} (ht : |t| < 1) :
    primeFixedPhysicalFisherClass (-t) ≠ 0 ∨
      primeFixedPhysicalFisherClass t ≠ 0 := by
  rcases le_total t 0 with ht0 | h0t
  · left
    exact (primeFixedPhysicalFisherClass_ne_zero_iff
      (by linarith [(abs_lt.mp ht).1])).2 (by linarith)
  · right
    exact (primeFixedPhysicalFisherClass_ne_zero_iff
      (abs_lt.mp ht).2).2 h0t

/-- Both full reflected physical classes survive exactly at neutral grade. -/
theorem primeFixedPhysicalFisher_reflected_pair_both_ne_zero_iff
    {t : ℝ} (ht : |t| < 1) :
    (primeFixedPhysicalFisherClass (-t) ≠ 0 ∧
      primeFixedPhysicalFisherClass t ≠ 0) ↔ t = 0 := by
  rw [primeFixedPhysicalFisherClass_ne_zero_iff
      (by linarith [(abs_lt.mp ht).1]),
    primeFixedPhysicalFisherClass_ne_zero_iff (abs_lt.mp ht).2]
  constructor
  · rintro ⟨h₁, h₂⟩
    linarith
  · rintro rfl
    simp

/-- Off neutral grade, exactly one physical Gamma orientation is erased. -/
theorem primeFixedPhysicalFisher_reflected_pair_exactly_one_erased
    {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    (primeFixedPhysicalFisherClass (-t) = 0 ∧
        primeFixedPhysicalFisherClass t ≠ 0) ∨
      (primeFixedPhysicalFisherClass (-t) ≠ 0 ∧
        primeFixedPhysicalFisherClass t = 0) := by
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · right
    constructor
    · exact (primeFixedPhysicalFisherClass_ne_zero_iff
        (by linarith [(abs_lt.mp ht).1])).2 (by linarith)
    · apply not_ne_iff.mp
      rw [primeFixedPhysicalFisherClass_ne_zero_iff (abs_lt.mp ht).2]
      linarith
  · left
    constructor
    · apply not_ne_iff.mp
      rw [primeFixedPhysicalFisherClass_ne_zero_iff
        (by linarith [(abs_lt.mp ht).1])]
      linarith
    · exact (primeFixedPhysicalFisherClass_ne_zero_iff
        (abs_lt.mp ht).2).2 htpos.le

/-- The full cofinal Gamma Bockstein detects exactly nonneutral grade.  This is the sharp
discontinuity invisible at every finite-prime stage. -/
theorem primeGammaCofinalBockstein_ne_zero_iff
    {t : ℝ} (ht : |t| < 1) :
    primeGammaCofinalBockstein t ≠ 0 ↔ t ≠ 0 := by
  constructor
  · intro hB ht0
    subst t
    exact hB (by simp [primeGammaCofinalBockstein])
  · intro ht0
    rcases primeFixedPhysicalFisher_reflected_pair_exactly_one_erased ht ht0 with h | h
    · rw [primeGammaCofinalBockstein, h.1, zero_sub]
      exact neg_ne_zero.mpr h.2
    · rw [primeGammaCofinalBockstein, h.2, sub_zero]
      exact h.1

/-- Equivalent zero form of the cofinal Gamma Bockstein classification. -/
theorem primeGammaCofinalBockstein_eq_zero_iff
    {t : ℝ} (ht : |t| < 1) :
    primeGammaCofinalBockstein t = 0 ↔ t = 0 := by
  rw [← not_iff_not]
  simpa using primeGammaCofinalBockstein_ne_zero_iff ht

/-! ## Actual Xi and rational-adelic source consequences -/

/-- At an actual Xi divisor, two-sided normalization of the fixed trace ideal is exactly the
critical-line condition. -/
theorem xi_reflected_primeReflectedCharacter_normalizesFixedIdeal_iff
    (rho : XiDivisorSupport) :
    (PrimeReflectedCharacterPreservesFixedIdeal
        (2 * (rho : ℂ).re - 1) ∧
      PrimeReflectedCharacterPreservesFixedIdeal
        (-(2 * (rho : ℂ).re - 1))) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflected_primeReflectedCharacter_normalizesFixedIdeal_iff
    (xiCenteredPrimeIdealRate_abs_lt_one rho)]
  constructor <;> intro h <;> linarith

/-- The period-one rational-adelic source class always survives in at least one fixed physical
Gamma orientation.  This is the strongest unconditional global non-erasure statement: off the
critical line the other orientation is erased. -/
theorem ccmRationalAdelicPrimeFixedXiStokesComparisons_class_one_orientation_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeFixedXiStokesComparison p rho
          (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 ∨
      ccmRationalAdelicPrimeReflectedFixedXiStokesComparison p rho
          (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 := by
  rcases le_total (2 * (rho : ℂ).re - 1) 0 with h | h
  · exact Or.inl
      ((ccmRationalAdelicPrimeFixedXiStokesComparison_class_ne_zero_iff
        p rho).2 h)
  · exact Or.inr
      ((ccmRationalAdelicPrimeReflectedFixedXiStokesComparison_class_ne_zero_iff
        p rho).2 h)

/-- Away from the critical line, the actual retained source class is erased in exactly one of the
two fixed physical Gamma orientations. -/
theorem ccmRationalAdelicPrimeFixedXiStokesComparisons_class_exactly_one_erased
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    (ccmRationalAdelicPrimeFixedXiStokesComparison p rho
          (ccmRationalAdelicPrimeRelativeClass p) = 0 ∧
        ccmRationalAdelicPrimeReflectedFixedXiStokesComparison p rho
          (ccmRationalAdelicPrimeRelativeClass p) ≠ 0) ∨
      (ccmRationalAdelicPrimeFixedXiStokesComparison p rho
          (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 ∧
        ccmRationalAdelicPrimeReflectedFixedXiStokesComparison p rho
          (ccmRationalAdelicPrimeRelativeClass p) = 0) := by
  have hrate : 2 * (rho : ℂ).re - 1 ≠ 0 := by
    intro h
    apply hoff
    linarith
  rcases lt_or_gt_of_ne hrate with hneg | hpos
  · right
    constructor
    · exact
        (ccmRationalAdelicPrimeFixedXiStokesComparison_class_ne_zero_iff
          p rho).2 hneg.le
    · apply not_ne_iff.mp
      rw [ccmRationalAdelicPrimeReflectedFixedXiStokesComparison_class_ne_zero_iff]
      linarith
  · left
    constructor
    · apply not_ne_iff.mp
      rw [ccmRationalAdelicPrimeFixedXiStokesComparison_class_ne_zero_iff]
      linarith
    · exact
        (ccmRationalAdelicPrimeReflectedFixedXiStokesComparison_class_ne_zero_iff
          p rho).2 hpos.le

/-- Source-derived physical Gamma-orientation Bockstein.  It compares the two actual fixed-fibre
landings of the same retained period-one rational-adelic source class. -/
def ccmRationalAdelicPrimeFixedXiGammaBockstein
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal :=
  ccmRationalAdelicPrimeFixedXiStokesComparison p rho
      (ccmRationalAdelicPrimeRelativeClass p) -
    ccmRationalAdelicPrimeReflectedFixedXiStokesComparison p rho
      (ccmRationalAdelicPrimeRelativeClass p)

/-- Exact source factorization: physical orientation defect is leading Xi jet times the singular
all-prime Gamma Bockstein. -/
theorem ccmRationalAdelicPrimeFixedXiGammaBockstein_eq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeFixedXiGammaBockstein p rho =
      iteratedDeriv (xiSupportMultiplicity rho) XiC
          (xiSpectralPointSupport rho) •
        primeGammaCofinalBockstein (2 * (rho : ℂ).re - 1) := by
  simp [ccmRationalAdelicPrimeFixedXiGammaBockstein,
    ccmRationalAdelicPrimeFixedXiStokesComparison_class,
    ccmRationalAdelicPrimeReflectedFixedXiStokesComparison_class,
    primeGammaCofinalBockstein, smul_sub]

/-- The source-derived physical Gamma Bockstein is nonzero exactly off the critical line. -/
theorem ccmRationalAdelicPrimeFixedXiGammaBockstein_ne_zero_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeFixedXiGammaBockstein p rho ≠ 0 ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  rw [ccmRationalAdelicPrimeFixedXiGammaBockstein_eq, smul_ne_zero_iff]
  have hjet : iteratedDeriv (xiSupportMultiplicity rho) XiC
      (xiSpectralPointSupport rho) ≠ 0 :=
    iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho
  rw [and_iff_right hjet,
    primeGammaCofinalBockstein_ne_zero_iff
      (xiCenteredPrimeIdealRate_abs_lt_one rho)]
  constructor
  · intro hrate hline
    apply hrate
    rw [hline]
    norm_num
  · intro hline hrate
    apply hline
    linarith

/-- Global annihilation target for the explicit source-derived physical Gamma Bockstein. -/
def CCMRationalAdelicPrimeFixedXiGammaBocksteinAnnihilates : Prop :=
  ∀ p : Nat.Primes, ∀ rho : XiDivisorSupport,
    ccmRationalAdelicPrimeFixedXiGammaBockstein p rho = 0

/-- Exact global obstruction: annihilating the explicit source-derived physical Gamma Bockstein
is equivalent to RH.  No annihilation assumption enters construction of the class. -/
theorem ccmRationalAdelicPrimeFixedXiGammaBocksteinAnnihilates_iff_riemannHypothesis :
    CCMRationalAdelicPrimeFixedXiGammaBocksteinAnnihilates ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have hline : z.re = 1 / 2 := by
      by_contra hoff
      exact (ccmRationalAdelicPrimeFixedXiGammaBockstein_ne_zero_iff p rho).2
        hoff (h p rho)
    linarith [mem_rightHalf.mp hz]
  · intro hRH p rho
    apply not_ne_iff.mp
    rw [ccmRationalAdelicPrimeFixedXiGammaBockstein_ne_zero_iff]
    exact not_ne_iff.mpr (xi_divisor_support_re_eq_half_of_rh hRH rho)

/-- Global fixed-ideal Gamma normalization target. -/
def XiPrimeReflectedCharacterNormalizesFixedIdeal : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeReflectedCharacterPreservesFixedIdeal
        (2 * (rho : ℂ).re - 1) ∧
      PrimeReflectedCharacterPreservesFixedIdeal
        (-(2 * (rho : ℂ).re - 1))

/-- Exact global categorical frontier: a same-fibre two-sided Gamma action on the fixed physical
trace ideal is equivalent to RH. -/
theorem xiPrimeReflectedCharacterNormalizesFixedIdeal_iff_riemannHypothesis :
    XiPrimeReflectedCharacterNormalizesFixedIdeal ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hline : z.re = 1 / 2 :=
      (xi_reflected_primeReflectedCharacter_normalizesFixedIdeal_iff rho).1
        (h rho)
    linarith [mem_rightHalf.mp hz]
  · intro hRH rho
    apply (xi_reflected_primeReflectedCharacter_normalizesFixedIdeal_iff rho).2
    exact xi_divisor_support_re_eq_half_of_rh hRH rho

end

end RHTower
