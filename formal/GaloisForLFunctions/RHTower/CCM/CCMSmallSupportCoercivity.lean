import GaloisForLFunctions.RHTower.CCM.CCMCompactPhysicalConcentration
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilSourceAlignedFiniteBlock

/-!
# Full Weil coercivity on sets of small total measure

At any fixed aperture, the compact Gamma embedding controls physical mass on
every small measurable set. The explicit prime--pole remainder envelope then
gives arbitrarily large physical coercivity on sources supported there, with
half the Gamma form norm retained. Disconnected support and all mixed terms
are included. The measure threshold depends on the ambient aperture.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RHTower

/-- Small total support gives arbitrary physical coercivity for the complete source form. -/
theorem exists_ccmSmallSupport_coercivity (a : SuzukiPositiveAperture) (L : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (s : Set ℝ) (hs : MeasurableSet s),
      volume s ≤ ENNReal.ofReal delta → ∀ u : CCMArchimedeanFormDomain a,
        indicatorCutoff s hs (ccmArchimedeanFormEmbedding a u) =
            ccmArchimedeanFormEmbedding a u →
          L * ‖ccmArchimedeanFormEmbedding a u‖ ^ 2 + (1 / 2 : ℝ) * ‖u‖ ^ 2 ≤
            ccmRestrictedWeilSourceQuadratic a u := by
  let M := ccmRestrictedWeilRemainderEnvelope a
  have hM : 0 ≤ M := ccmRestrictedWeilRemainderEnvelope_nonneg a
  let eta := 1 / (2 * (M + |L| + 1))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hpay : (M + |L|) * eta ≤ (1 / 2 : ℝ) := by
    dsimp only [eta]
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 2 * (M + |L| + 1))]
    nlinarith
  obtain ⟨delta, hdelta, hsmall⟩ := exists_ccmSmallSet_mass_le a eta heta
  refine ⟨delta, hdelta, fun s hs hvol u hsupp => ?_⟩
  have hmass := hsmall s hs hvol u
  rw [hsupp] at hmass
  have hcost : (M + L) * ‖ccmArchimedeanFormEmbedding a u‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
    calc
      _ ≤ (M + |L|) * ‖ccmArchimedeanFormEmbedding a u‖ ^ 2 := by
        gcongr
        exact le_abs_self L
      _ ≤ (M + |L|) * (eta * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmass (add_nonneg hM (abs_nonneg L))
      _ = ((M + |L|) * eta) * ‖u‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpay (sq_nonneg _)
  have hbase := ccmRestrictedWeilForm_sourceRelative_lowerBound a u
  rw [ccmRestrictedWeilForm_self_re_eq_source] at hbase
  change ‖u‖ ^ 2 - M * ‖ccmArchimedeanFormEmbedding a u‖ ^ 2 ≤
    ccmRestrictedWeilSourceQuadratic a u at hbase
  nlinarith

/-- All nonpositive directions are uniformly nonconcentrating in physical space.
The estimate controls mass fractions and does not assume compact support. -/
theorem exists_ccmNonpositive_smallSet_mass_fraction
    (a : SuzukiPositiveAperture) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (s : Set ℝ) (hs : MeasurableSet s),
      volume s ≤ ENNReal.ofReal delta → ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u ≤ 0 →
          ‖indicatorCutoff s hs (ccmArchimedeanFormEmbedding a u)‖ ^ 2 ≤
            epsilon * ‖ccmArchimedeanFormEmbedding a u‖ ^ 2 := by
  let M := ccmRestrictedWeilRemainderEnvelope a
  have hM : 0 ≤ M := ccmRestrictedWeilRemainderEnvelope_nonneg a
  let eta := epsilon / (M + 1)
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hpay : eta * M ≤ epsilon := by
    have heq : eta * (M + 1) = epsilon :=
      div_mul_cancel₀ epsilon (by positivity : M + 1 ≠ 0)
    nlinarith
  obtain ⟨delta, hdelta, hsmall⟩ := exists_ccmSmallSet_mass_le a eta heta
  refine ⟨delta, hdelta, fun s hs hvol u hQ => ?_⟩
  have hbase := ccmRestrictedWeil_sourceMass_lower_of_nonpositive a u
    (by rwa [ccmRestrictedWeilForm_self_re_eq_source])
  change ‖u‖ ^ 2 ≤ M * ‖ccmArchimedeanFormEmbedding a u‖ ^ 2 at hbase
  calc
    _ ≤ eta * ‖u‖ ^ 2 := hsmall s hs hvol u
    _ ≤ eta * (M * ‖ccmArchimedeanFormEmbedding a u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hbase heta.le
    _ = (eta * M) * ‖ccmArchimedeanFormEmbedding a u‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpay (sq_nonneg _)

/-- A nonzero nonpositive direction cannot be supported on an arbitrarily small set. -/
theorem exists_ccmNonpositive_support_measure_floor (a : SuzukiPositiveAperture) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (s : Set ℝ) (hs : MeasurableSet s),
      ∀ u : CCMArchimedeanFormDomain a, u ≠ 0 →
        ccmRestrictedWeilSourceQuadratic a u ≤ 0 →
        indicatorCutoff s hs (ccmArchimedeanFormEmbedding a u) =
          ccmArchimedeanFormEmbedding a u →
        ENNReal.ofReal delta < volume s := by
  obtain ⟨delta, hdelta, hcoercive⟩ := exists_ccmSmallSupport_coercivity a 0
  refine ⟨delta, hdelta, fun s hs u hu hQ hsupp => ?_⟩
  by_contra hvol
  have hbound := hcoercive s hs (le_of_not_gt hvol) u hsupp
  have hnorm : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  nlinarith

end RHTower
