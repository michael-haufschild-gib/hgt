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

/-- **Exact endpoint phase dichotomy.** False RH is equivalent to divergence of the single
source-defined Bernstein negative-mass sequence to positive infinity. -/
theorem not_riemannHypothesis_iff_tendsto_primeArchBernsteinNegativeMass_atTop :
    ¬ RiemannHypothesis ↔
      Tendsto
        (hausdorffBernsteinNegativeMass
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment))
        atTop atTop := by
  constructor
  · exact tendsto_primeArchBernsteinNegativeMass_atTop_of_not_riemannHypothesis
  · intro hdiv hRH
    obtain ⟨C, hC⟩ :=
      riemannHypothesis_iff_primeArchBernsteinNegativeMassBounded.mp hRH
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 ((tendsto_atTop.1 hdiv) (C + 1))
    linarith [hN N le_rfl, hC N]

/-- **Lowest-quantifier Bernstein endpoint.** RH is exactly failure of the endpoint negative
mass to diverge. No cofinal schedule, convergence rate, zero limit, or ceiling witness remains. -/
theorem riemannHypothesis_iff_not_tendsto_primeArchBernsteinNegativeMass_atTop :
    RiemannHypothesis ↔
      ¬ Tendsto
        (hausdorffBernsteinNegativeMass
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment))
        atTop atTop := by
  rw [← not_riemannHypothesis_iff_tendsto_primeArchBernsteinNegativeMass_atTop]
  tauto

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

open HTGeometry

/-- Aggregate discrepancy between two degree-`N+1` Bernstein value packets. -/
def bernsteinCoefficientL1DiscrepancyAtDefectDegree
    (m a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 2),
    |bernsteinCoefficient m (N + 1) i -
      bernsteinCoefficient a (N + 1) i|

/-- A positive Bernstein comparator bounds the target's entire negative mass by their aggregate
coefficient discrepancy. -/
lemma hausdorffBernsteinNegativeMass_le_l1Discrepancy
    (m a : ℕ → ℝ) (N : ℕ)
    (ha : HausdorffBernsteinNonnegative a) :
    hausdorffBernsteinNegativeMass m N ≤
      bernsteinCoefficientL1DiscrepancyAtDefectDegree m a N := by
  rw [hausdorffBernsteinNegativeMass]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ =>
      (momentFunctional m (bernsteinPolynomial ℝ (N + 1) i))⁻) (N + 2)]
  apply Finset.sum_le_sum
  intro i hi
  have hy : 0 ≤ bernsteinCoefficient a (N + 1) i := ha (N + 1) i
  have h := negPart_le_negPart_add_of_abs_sub_le
    (bernsteinCoefficient m (N + 1) i)
    (bernsteinCoefficient a (N + 1) i)
    |bernsteinCoefficient m (N + 1) i - bernsteinCoefficient a (N + 1) i|
    le_rfl
  rw [negPart_eq_zero.mpr hy, zero_add] at h
  simpa only [bernsteinCoefficient,
    bernsteinCoefficientL1DiscrepancyAtDefectDegree] using h

/-- **Positive-comparator discharge theorem.** Positive finite-system comparators need not
reproduce the source moments. A fixed aggregate Bernstein error bound along one cofinal degree
schedule already proves RH. -/
theorem riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_l1Discrepancy_bounded
    (d : ℕ → ℕ) (a : ℕ → ℕ → ℝ) (C : ℝ)
    (hd : Tendsto d atTop atTop)
    (ha : ∀ j, HausdorffBernsteinNonnegative (a j))
    (herr : ∀ j,
      bernsteinCoefficientL1DiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) (a j) (d j) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_primeArchBernsteinNegativeMassCofinallyBounded.mpr
  refine ⟨d, C, hd, fun j => ?_⟩
  exact (hausdorffBernsteinNegativeMass_le_l1Discrepancy _ _ _ (ha j)).trans
    (herr j)

/-- Every normalized finite Xi thermal truncation is a positive endpoint Hausdorff comparator. -/
lemma hausdorffBernsteinNonnegative_radiusNormalized_xiThermalTruncation (M : ℕ) :
    HausdorffBernsteinNonnegative
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        (xiThermalTruncation M)) := by
  apply hausdorffBernsteinNonnegative_of_momentDifferencesNonnegative
  exact hausdorffMomentDifferencesNonnegative_radiusNormalizedMoment
    primeArchEndpointHausdorffRadius_pos
    (scaledHausdorffMomentDifferencesNonnegative_xiThermalTruncation M)

/-- **Finite thermal discharge theorem.** A uniformly bounded aggregate discrepancy from any
family of explicit finite Xi thermal systems at cofinally large Bernstein degrees proves RH. The
thermal cutoff may vary arbitrarily with the degree. -/
theorem riemannHypothesis_of_cofinal_xiThermalTruncation_bernsteinL1Discrepancy_bounded
    (d M : ℕ → ℕ) (C : ℝ)
    (hd : Tendsto d atTop atTop)
    (herr : ∀ j,
      bernsteinCoefficientL1DiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment)
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          (xiThermalTruncation (M j))) (d j) ≤ C) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_l1Discrepancy_bounded
      d (fun j => radiusNormalizedMoment primeArchEndpointHausdorffRadius
        (xiThermalTruncation (M j))) C hd
      (fun j =>
        hausdorffBernsteinNonnegative_radiusNormalized_xiThermalTruncation (M j))
      herr

/-- Squared Hilbert discrepancy of two degree-`N+1` Bernstein value packets. -/
def bernsteinCoefficientSquareDiscrepancyAtDefectDegree
    (m a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 2),
    (bernsteinCoefficient m (N + 1) i -
      bernsteinCoefficient a (N + 1) i) ^ 2

/-- Cauchy--Schwarz converts the dimension-normalized quadratic discrepancy into the aggregate
`l1` discrepancy needed by the finite-ceiling law. -/
lemma bernsteinCoefficientL1Discrepancy_le_of_card_mul_squareDiscrepancy_le_sq
    {m a : ℕ → ℝ} {N : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (henergy : (N + 2 : ℝ) *
      bernsteinCoefficientSquareDiscrepancyAtDefectDegree m a N ≤ C ^ 2) :
    bernsteinCoefficientL1DiscrepancyAtDefectDegree m a N ≤ C := by
  let s := Finset.range (N + 2)
  let f : ℕ → ℝ := fun i =>
    |bernsteinCoefficient m (N + 1) i - bernsteinCoefficient a (N + 1) i|
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  have hcard : ((s.card : ℕ) : ℝ) = (N + 2 : ℝ) := by simp [s]
  have hsq : (∑ i ∈ s, f i) ^ 2 ≤ C ^ 2 := by
    calc
      (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := hcs
      _ = (N + 2 : ℝ) *
          bernsteinCoefficientSquareDiscrepancyAtDefectDegree m a N := by
        rw [hcard]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp only [f, sq_abs]
      _ ≤ C ^ 2 := henergy
  have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg fun _ _ => abs_nonneg _
  change (∑ i ∈ s, f i) ≤ C
  nlinarith

/-- **Quadratic operator-state discharge theorem.** It is enough to control one squared Hilbert
packet error at the natural inverse-dimension scale along cofinally many degrees. -/
theorem riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_squareDiscrepancy
    (d : ℕ → ℕ) (a : ℕ → ℕ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hd : Tendsto d atTop atTop)
    (ha : ∀ j, HausdorffBernsteinNonnegative (a j))
    (henergy : ∀ j, (d j + 2 : ℝ) *
      bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) (a j) (d j) ≤ C ^ 2) :
    RiemannHypothesis := by
  apply
    riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_l1Discrepancy_bounded
      d a C hd ha
  intro j
  exact bernsteinCoefficientL1Discrepancy_le_of_card_mul_squareDiscrepancy_le_sq
    hC (henergy j)

/-- Concrete quadratic thermal consumer for the explicit finite Xi truncations. -/
theorem riemannHypothesis_of_cofinal_xiThermalTruncation_bernsteinSquareDiscrepancy
    (d M : ℕ → ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hd : Tendsto d atTop atTop)
    (henergy : ∀ j, (d j + 2 : ℝ) *
      bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment)
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          (xiThermalTruncation (M j))) (d j) ≤ C ^ 2) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_squareDiscrepancy
      d (fun j => radiusNormalizedMoment primeArchEndpointHausdorffRadius
        (xiThermalTruncation (M j))) C hC hd
      (fun j =>
        hausdorffBernsteinNonnegative_radiusNormalized_xiThermalTruncation (M j))
      henergy

end


end RHTower
