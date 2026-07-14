import GaloisForLFunctions.RHTower.PrimeArchBernsteinExponentialPhase

/-!
# Subexponential Bernstein negative mass and the prime--polar abscissa

The cancellation-resistant exponential-phase theorem reduces RH to subexponential growth of the
endpoint Bernstein total variation. The exact order-unit identity converts that criterion to one
scalar negative-mass sequence. This file records that source-only obligation and identifies it
with the existing prime--polar absolute-convergence target.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Subexponential growth of the endpoint Bernstein negative mass, in its exact order-unit
normalization. -/
def PrimeArchBernsteinNegativeMassSubexponential : Prop :=
  ∀ r : ℝ, 1 < r →
    Tendsto
      (fun N : ℕ =>
        (normalizedPrimeArchMoment 0 +
          2 * hausdorffBernsteinNegativeMass
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment) N) / r ^ (N + 1))
      atTop (nhds 0)

/-- The exact total-variation identity converts the negative-mass and coefficient-vector
subexponential laws without loss. -/
theorem primeArchBernsteinNegativeMassSubexponential_iff_totalVariation :
    PrimeArchBernsteinNegativeMassSubexponential ↔
      SubexponentialAtNatInfinity primeArchEndpointBernsteinTotalVariation := by
  constructor
  · intro hneg r hr
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [primeArchEndpointBernsteinTotalVariation,
      bernsteinCoefficientL1_eq_mass_add_two_negativeMass,
      radiusNormalizedMoment, pow_zero, div_one] using hneg r hr
  · intro htv r hr
    have hshift := (tendsto_add_atTop_iff_nat 1).mpr (htv r hr)
    simpa only [primeArchEndpointBernsteinTotalVariation,
      bernsteinCoefficientL1_eq_mass_add_two_negativeMass,
      radiusNormalizedMoment, pow_zero, div_one] using hshift

/-- **Subexponential Bernstein negative-mass RH law.** It is enough—and is necessary—to prove
that the endpoint source's total Bernstein negative mass has exponential rate zero. Exact
vanishing, monotone decay, or a positive representing measure are not required. -/
theorem riemannHypothesis_iff_primeArchBernsteinNegativeMassSubexponential :
    RiemannHypothesis ↔ PrimeArchBernsteinNegativeMassSubexponential :=
  riemannHypothesis_iff_primeArchEndpointBernsteinTotalVariation_subexponential.trans
    primeArchBernsteinNegativeMassSubexponential_iff_totalVariation.symm

/-- The source-only subexponential obligation is exactly equivalent to the prime--polar
absolute-convergence abscissa target, for every admissible rectangle. -/
theorem primeArchBernsteinNegativeMassSubexponential_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    PrimeArchBernsteinNegativeMassSubexponential ↔
      LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) :=
  riemannHypothesis_iff_primeArchBernsteinNegativeMassSubexponential.symm.trans
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one hL hN)

/-- The endpoint source has a finite Bernstein-negativity ceiling. No sign or vanishing is
required in this condition. -/
def PrimeArchBernsteinNegativeMassBounded : Prop :=
  ∃ C : ℝ, ∀ N : ℕ,
    hausdorffBernsteinNegativeMass
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment) N ≤ C

/-- A finite ceiling already implies subexponential growth of the endpoint negative-mass
order unit. -/
lemma primeArchBernsteinNegativeMassBounded_implies_subexponential
    (hbounded : PrimeArchBernsteinNegativeMassBounded) :
    PrimeArchBernsteinNegativeMassSubexponential := by
  obtain ⟨C, hC⟩ := hbounded
  intro r hr
  let E : ℕ → ℝ := hausdorffBernsteinNegativeMass
    (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment)
  let K : ℝ := normalizedPrimeArchMoment 0 + 2 * C
  have hKnonneg : 0 ≤ K := by
    have hnum : 0 ≤ normalizedPrimeArchMoment 0 + 2 * E 0 := by
      rw [show normalizedPrimeArchMoment 0 + 2 * E 0 =
          bernsteinCoefficientL1
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment) 1 by
        rw [bernsteinCoefficientL1_eq_mass_add_two_negativeMass]
        simp only [E, radiusNormalizedMoment, pow_zero, div_one]]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hle := hC 0
    dsimp only [K]
    linarith
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hpow : Tendsto (fun n : ℕ => (r⁻¹) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_nonneg.mpr hrpos.le) (inv_lt_one_of_one_lt₀ hr)
  have hupper : Tendsto (fun N : ℕ => K / r ^ (N + 1)) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => K * (r⁻¹) ^ n) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hpow
    have hshift := (tendsto_add_atTop_iff_nat 1).mpr hbase
    simpa only [div_eq_mul_inv, inv_pow] using hshift
  refine squeeze_zero (fun N => ?_) (fun N => ?_) hupper
  · have hnum : 0 ≤ normalizedPrimeArchMoment 0 + 2 * E N := by
      rw [show normalizedPrimeArchMoment 0 + 2 * E N =
          bernsteinCoefficientL1
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment) (N + 1) by
        rw [bernsteinCoefficientL1_eq_mass_add_two_negativeMass]
        simp only [E, radiusNormalizedMoment, pow_zero, div_one]]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact div_nonneg hnum (pow_nonneg hrpos.le _)
  · apply div_le_div_of_nonneg_right _ (pow_nonneg hrpos.le _)
    linarith [hC N]

/-- **Finite-ceiling RH law.** The endpoint Bernstein negative mass may be allowed to stay
positive: any uniform finite ceiling forces RH and hence retroactively forces exact vanishing. -/
theorem riemannHypothesis_iff_primeArchBernsteinNegativeMassBounded :
    RiemannHypothesis ↔ PrimeArchBernsteinNegativeMassBounded := by
  constructor
  · intro hRH
    refine ⟨0, fun N => ?_⟩
    have hcofinal :=
      cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis.mpr hRH
    rw [hausdorffBernsteinNegativeMass_eq_zero_of_cofinalVanishing hcofinal N]
  · intro hbounded
    exact riemannHypothesis_iff_primeArchBernsteinNegativeMassSubexponential.mpr
      (primeArchBernsteinNegativeMassBounded_implies_subexponential hbounded)

/-- It is enough to bound the source defect only on one cofinal sequence of Bernstein degrees. -/
def PrimeArchBernsteinNegativeMassCofinallyBounded : Prop :=
  ∃ (d : ℕ → ℕ) (C : ℝ), Tendsto d atTop atTop ∧
    ∀ j : ℕ,
      hausdorffBernsteinNegativeMass
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) (d j) ≤ C

/-- Cofinal boundedness is equivalent to a global finite ceiling because Bernstein degree
elevation makes the negative mass monotone. -/
theorem primeArchBernsteinNegativeMassCofinallyBounded_iff_bounded :
    PrimeArchBernsteinNegativeMassCofinallyBounded ↔
      PrimeArchBernsteinNegativeMassBounded := by
  constructor
  · rintro ⟨d, C, hd, hC⟩
    refine ⟨C, fun N => ?_⟩
    obtain ⟨j, hj⟩ := eventually_atTop.1 ((tendsto_atTop.1 hd) N)
    exact (hausdorffBernsteinNegativeMass_monotone _ (hj j le_rfl)).trans (hC j)
  · rintro ⟨C, hC⟩
    exact ⟨fun n => n, C, tendsto_id, hC⟩

/-- **Cofinal finite-ceiling RH law.** A uniformly bounded checkpoint at arbitrarily large
degrees is sufficient; the degrees between checkpoints need not be controlled separately. -/
theorem riemannHypothesis_iff_primeArchBernsteinNegativeMassCofinallyBounded :
    RiemannHypothesis ↔ PrimeArchBernsteinNegativeMassCofinallyBounded :=
  riemannHypothesis_iff_primeArchBernsteinNegativeMassBounded.trans
    primeArchBernsteinNegativeMassCofinallyBounded_iff_bounded.symm

/-- The complementary positive phase law: if RH fails, the monotone source defect diverges to
`+∞`; there is no bounded nonzero intermediate phase. -/
theorem tendsto_primeArchBernsteinNegativeMass_atTop_of_not_riemannHypothesis
    (hnot : ¬ RiemannHypothesis) :
    Tendsto
      (hausdorffBernsteinNegativeMass
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment))
      atTop atTop := by
  apply (hausdorffBernsteinNegativeMass_monotone _).tendsto_atTop_atTop
  intro C
  by_contra hnone
  push Not at hnone
  have hbounded : PrimeArchBernsteinNegativeMassBounded :=
    ⟨C, fun N => (hnone N).le⟩
  exact hnot
    (riemannHypothesis_iff_primeArchBernsteinNegativeMassBounded.mpr hbounded)

/-- For every admissible prime--polar rectangle, a finite ceiling on one cofinal Bernstein
sampling is exactly the requested critical absolute-convergence abscissa. -/
theorem primeArchBernsteinNegativeMassCofinallyBounded_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    PrimeArchBernsteinNegativeMassCofinallyBounded ↔
      LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) :=
  riemannHypothesis_iff_primeArchBernsteinNegativeMassCofinallyBounded.symm.trans
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one hL hN)

end


end RHTower
