import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge
import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinSchattenWall

/-!
# Schatten spectrum of literal Xi reflection incidence

The canonical horizontal reflection charge has a literal multiplicity-copy incidence carrier.
This module weights every one of its `m_rho^(2 : ℕ)` incidences by the exact cofinal Gamma Bockstein
`q`-mass.  No divisor copy, prime label, or reflection orientation is discarded.

At `q = 2`, this mass is exactly the quadratic source-incidence energy.  At variable order, its
summability wall is unchanged by the positive integral incidence multiplicity.  Consequently the
intersection of all orders `q > 1` detects the critical line for each divisor point and detects RH
globally.

These are unconditional reader theorems.  They expose a sharply typed producer: place the literal
Xi reflection-incidence carrier in every prime Schatten class `S_q`, `q > 1`, by a source theorem.
A single fixed Schatten order cannot replace this all-order landing.
-/

open Complex Set Metric Filter

namespace RHTower

noncomputable section

/-- Coefficient-faithful `q`-mass of one Xi reflection-incidence fibre at prime `p`.
The cardinal factor is literal `m_rho^(2 : ℕ)`, not a synthetic amplification parameter. -/
def xiZeroCopyLineReflectionPrimeIncidenceSchattenMass
    (q : ℝ) (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) *
    primeGammaCofinalBocksteinSchattenMass q
      (primeDepthBVWoldXiCenteredRate rho) p

/-- The order-two Schatten mass is exactly the previously constructed quadratic incidence
energy, prime by prime. -/
theorem xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_two
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 2 rho p =
      xiZeroCopyLineReflectionPrimeIncidenceEnergy rho p := by
  rw [xiZeroCopyLineReflectionPrimeIncidenceSchattenMass,
    primeGammaCofinalBocksteinSchattenMass,
    Real.rpow_two, primeGammaCofinalBocksteinMagnitude, sq_abs,
    xiZeroCopyLineReflectionPrimeIncidenceEnergy_eq,
    sourceZeroHorizontalPrimeCarrierAtSupport,
    card_xiZeroCopyLineReflectionIncidence]
  norm_cast

/-- Every variable-order incidence mass preserves both line-reflection orientations. -/
@[simp] theorem xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_reflection
    (q : ℝ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    xiZeroCopyLineReflectionPrimeIncidenceSchattenMass q
        (xiZeroLineConjEquiv rho) p =
      xiZeroCopyLineReflectionPrimeIncidenceSchattenMass q rho p := by
  rw [xiZeroCopyLineReflectionPrimeIncidenceSchattenMass,
    xiZeroCopyLineReflectionPrimeIncidenceSchattenMass,
    card_xiZeroCopyLineReflectionIncidence,
    card_xiZeroCopyLineReflectionIncidence,
    xi_orderAt_xiZeroLineConjEquiv,
    primeDepthBVWoldXiCenteredRate_reflection,
    primeGammaCofinalBocksteinSchattenMass,
    primeGammaCofinalBocksteinSchattenMass,
    primeGammaCofinalBocksteinMagnitude,
    primeGammaCofinalBocksteinMagnitude]
  simp only [neg_neg, abs_sub_comm]

/-- Sharp fixed-order summability classification after retaining literal divisor multiplicity. -/
theorem summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_iff
    {q : ℝ} (hq : 0 < q) (rho : XiDivisorSupport) :
    Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass q rho) ↔
      primeDepthBVWoldXiCenteredRate rho = 0 ∨
        1 < q * (1 - |primeDepthBVWoldXiCenteredRate rho|) := by
  have hcard : ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
      (xiZeroCopyLineReflectionIncidence_nonempty rho))
  change Summable (fun p : Nat.Primes =>
      ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) *
        primeGammaCofinalBocksteinSchattenMass q
          (primeDepthBVWoldXiCenteredRate rho) p) ↔ _
  rw [summable_mul_left_iff hcard,
    summable_primeGammaCofinalBocksteinSchattenMass_iff hq]

/-- Off line, a fixed order only imposes the open summability window; it does not annihilate the
incidence.  This is the exact fixed-`q` obstruction. -/
theorem summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_iff_of_offLine
    {q : ℝ} (hq : 0 < q) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass q rho) ↔
      1 < q * (1 - |primeDepthBVWoldXiCenteredRate rho|) := by
  rw [summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_iff hq]
  exact or_iff_right
    ((not_congr (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho)).mpr hoff)

/-- **Nuclear endpoint at one order.**  At `q = 1` the open fixed-order window disappears:
coefficient-faithful trace mass is summable exactly on the critical line. -/
theorem summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff
    (rho : XiDivisorSupport) :
    Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_iff (by norm_num),
    ← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  constructor
  · rintro (hzero | hwindow)
    · exact hzero
    · have habs := abs_nonneg (primeDepthBVWoldXiCenteredRate rho)
      norm_num at hwindow
      linarith
  · exact Or.inl

/-- Endpoint incidence nuclearity is exactly annihilation of the singular all-prime Gamma
Bockstein class in the fixed first-trace quotient. -/
theorem summable_reflectionIncidenceSchattenMass_one_iff_cofinalBockstein_eq_zero
    (rho : XiDivisorSupport) :
    Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) ↔
      primeGammaCofinalBockstein (primeDepthBVWoldXiCenteredRate rho) = 0 := by
  rw [summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff,
    primeDepthBVWoldXiCenteredRate,
    primeGammaCofinalBockstein_eq_zero_iff
      (xiCenteredPrimeIdealRate_abs_lt_one rho)]
  constructor <;> intro h <;> linarith

/-- Endpoint incidence nuclearity is equivalently two-sided normalization of the same fixed
first-trace ideal by both retained Gamma orientations. -/
theorem summable_reflectionIncidenceSchattenMass_one_iff_twoSidedFixedIdealNormalization
    (rho : XiDivisorSupport) :
    Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) ↔
      (PrimeReflectedCharacterPreservesFixedIdeal
          (primeDepthBVWoldXiCenteredRate rho) ∧
        PrimeReflectedCharacterPreservesFixedIdeal
          (-primeDepthBVWoldXiCenteredRate rho)) := by
  rw [summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff]
  simpa only [primeDepthBVWoldXiCenteredRate] using
    (xi_reflected_primeReflectedCharacter_normalizesFixedIdeal_iff rho).symm

/-- **Actual-source dictionary.**  For every retained ordinary prime, endpoint nuclearity of the
literal reflection-incidence carrier is exactly vanishing of the rational-adelic fixed-Xi Gamma
Bockstein obtained by comparing the two landings of the same period-one source class. -/
theorem summable_reflectionIncidenceSchattenMass_one_iff_sourceGammaBockstein_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho) ↔
      ccmRationalAdelicPrimeFixedXiGammaBockstein p rho = 0 := by
  rw [summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff]
  have hne := ccmRationalAdelicPrimeFixedXiGammaBockstein_ne_zero_iff p rho
  rw [← not_iff_not] at hne
  simpa only [not_ne_iff] using hne.symm

/-- **Local all-order seam.** Literal incidence belongs to every prime Schatten order above one
exactly when its Xi divisor point lies on the critical line. -/
theorem all_order_summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_iff
    (rho : XiDivisorSupport) :
    (∀ q : ℝ, 1 < q →
      Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass q rho)) ↔
      (rho : ℂ).re = 1 / 2 := by
  have hcard : ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
      (xiZeroCopyLineReflectionIncidence_nonempty rho))
  rw [← primeDepthBVWoldXiCenteredRate_eq_zero_iff,
    ← all_order_summable_primeGammaCofinalBocksteinSchattenMass_iff]
  constructor
  · intro hall q hq
    apply (summable_mul_left_iff hcard).mp
    change Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass q rho)
    exact hall q hq
  · intro hall q hq
    change Summable (fun p : Nat.Primes =>
      ((xiZeroCopyLineReflectionIncidence rho).card : ℝ) *
        primeGammaCofinalBocksteinSchattenMass q
          (primeDepthBVWoldXiCenteredRate rho) p)
    exact (summable_mul_left_iff hcard).mpr (hall q hq)

/-- Global source-admission proposition exposed by the incidence/Schatten splice. -/
def XiReflectionIncidenceAllOrderSourceAdmission : Prop :=
  ∀ rho : XiDivisorSupport, ∀ q : ℝ, 1 < q →
    Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass q rho)

/-- Strongest scalar nuclear producer exposed by the splice: literal incidence trace mass is
summable at the endpoint order one for every Xi divisor point. -/
def XiReflectionIncidenceNuclearSourceAdmission : Prop :=
  ∀ rho : XiDivisorSupport,
    Summable (xiZeroCopyLineReflectionPrimeIncidenceSchattenMass 1 rho)

/-- Global endpoint-order nuclear admission is already exactly RH. -/
theorem riemannHypothesis_iff_xiReflectionIncidenceNuclearSourceAdmission :
    RiemannHypothesis ↔ XiReflectionIncidenceNuclearSourceAdmission := by
  constructor
  · intro hRH rho
    exact
      (summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff rho).2
        (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro hall
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro z hz
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    exact
      (summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_one_iff rho).1
        (hall rho)

/-- **Frankenstein endpoint.** Global all-order source admission of the literal, coefficient-
faithful reflection-incidence carrier is exactly RH. -/
theorem riemannHypothesis_iff_xiReflectionIncidenceAllOrderSourceAdmission :
    RiemannHypothesis ↔ XiReflectionIncidenceAllOrderSourceAdmission := by
  constructor
  · intro hRH rho
    exact
      (all_order_summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_iff rho).2
        (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro hall
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro z hz
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    exact
      (all_order_summable_xiZeroCopyLineReflectionPrimeIncidenceSchattenMass_iff rho).1
        (hall rho)

end

end RHTower
