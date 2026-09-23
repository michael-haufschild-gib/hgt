import GaloisForLFunctions.RHTower.CCMActualHeadQuantileGammaChiSquareProducer
import GaloisForLFunctions.RHTower.PrimeSecondMomentDivergence
import GaloisForLFunctions.RHTower.CCMCountableLogChirp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Signed completed-error control on actual Gamma heads

The literal reciprocal-Gamma chi-square envelope cannot close Route O: its diagonal cell cost
already diverges along prime atoms. This module proves that obstruction and isolates the surviving
producer, higher Gamma energy plus the signed completed-error autocorrelation current. The survivor
is exactly the restricted-Weil source quadratic after its scalar Gamma term is removed, and it
converges on canonical finite Gamma--Slepian heads without separating prime and polar channels.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

lemma integral_Ioc_abs_ge_length_sq_div_four
    {a b : ℝ} (hab : a ≤ b) :
    (b - a) ^ 2 / 4 ≤ ∫ x in Ioc a b, |x| := by
  rw [← intervalIntegral.integral_of_le hab]
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    have heq : (∫ x in a..b, |x|) = ∫ x in a..b, x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [abs_of_nonneg]
      rw [uIcc_of_le hab] at hx
      exact ha.trans hx.1
    rw [heq, integral_id]
    nlinarith [sq_nonneg (b - a)]
  · have ha' : a < 0 := lt_of_not_ge ha
    by_cases hb : b ≤ 0
    · have heq : (∫ x in a..b, |x|) = ∫ x in a..b, -x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [abs_of_nonpos]
        rw [uIcc_of_le hab] at hx
        exact hx.2.trans hb
      rw [heq]
      have hid : (∫ x in a..b, -x) = -(∫ x in a..b, x) := by
        exact intervalIntegral.integral_neg
      rw [hid, integral_id]
      nlinarith [sq_nonneg (b - a)]
    · have hb' : 0 < b := lt_of_not_ge hb
      have hleft : (∫ x in a..0, |x|) = -(∫ x in a..0, x) := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro x hx
        rw [abs_of_nonpos]
        rw [uIcc_of_le ha'.le] at hx
        exact hx.2
      have hright : (∫ x in (0 : ℝ)..b, |x|) = ∫ x in (0 : ℝ)..b, x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [abs_of_nonneg]
        rw [uIcc_of_le hb'.le] at hx
        exact hx.1
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (continuous_abs.intervalIntegrable a 0)
        (continuous_abs.intervalIntegrable 0 b),
        hleft, hright, integral_id, integral_id]
      nlinarith [sq_nonneg (a + b)]

lemma criticalMellinAtomWeight_le_two (n : ℕ) :
    criticalMellinAtomWeight n ≤ 2 := by
  rcases n with _ | n
  · simp [criticalMellinAtomWeight]
  · have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hsqrtpos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hnpos
    have hvm := ArithmeticFunction.vonMangoldt_le_log (n := n + 1)
    push_cast at hvm
    rw [criticalMellinAtomWeight_eq_div_sqrt]
    push_cast
    calc
      ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt ((n : ℝ) + 1) ≤
          Real.log ((n : ℝ) + 1) / Real.sqrt ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_right hvm hsqrtpos.le
      _ ≤ 2 := by
        rw [div_le_iff₀ hsqrtpos]
        exact GaloisForLFunctions.RHTower.log_le_two_mul_sqrt hnpos

lemma two_mul_abs_le_ccmGammaHigherBinetDualDensity_abs (r : ℝ) :
    2 * |r| ≤ ccmGammaHigherBinetDualDensity |r| := by
  have hr0 : 0 ≤ |r| := abs_nonneg r
  have hexp : 1 ≤ Real.exp (|r| / 2) := Real.one_le_exp (by positivity)
  have hlin := Real.add_one_le_exp (2 * |r|)
  have hdiff : 2 * |r| ≤ Real.exp (2 * |r|) - 1 := by linarith
  have hdiff0 : 0 ≤ Real.exp (2 * |r|) - 1 :=
    (mul_nonneg (by norm_num) hr0).trans hdiff
  unfold ccmGammaHigherBinetDualDensity
  calc
    2 * |r| ≤ 1 * (Real.exp (2 * |r|) - 1) := by simpa using hdiff
    _ ≤ Real.exp (|r| / 2) * (Real.exp (2 * |r|) - 1) :=
      mul_le_mul_of_nonneg_right hexp hdiff0

lemma criticalMellinAtomWeight_le_two_exp_half_mul_quantileWidth (n : ℕ) :
    criticalMellinAtomWeight n ≤
      2 * Real.exp (ccmOutgoingPrimeQuantileBoundary n / 2) *
        (ccmOutgoingPrimeQuantileBoundary (n + 1) -
          ccmOutgoingPrimeQuantileBoundary n) := by
  let b0 := ccmOutgoingPrimeQuantileBoundary n
  let b1 := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let w := criticalMellinAtomWeight n
  let A := Real.exp (b0 / 2)
  let B := Real.exp (b1 / 2)
  have hb : b0 ≤ b1 := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hgap : 0 ≤ b1 - b0 := sub_nonneg.mpr hb
  have hwB : w ≤ B * (b1 - b0) := by
    have hleft : IntervalIntegrable (fun h : ℝ => Real.exp (h / 2)) volume b0 b1 :=
      (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).intervalIntegrable _ _
    have hright : IntervalIntegrable (fun _ : ℝ => B) volume b0 b1 :=
      continuous_const.intervalIntegrable _ _
    have hmono : (∫ h in b0..b1, Real.exp (h / 2)) ≤ ∫ _ in b0..b1, B := by
      apply intervalIntegral.integral_mono_on hb hleft hright
      intro h hh
      exact Real.exp_le_exp.mpr (by
        linarith [hh.2])
    calc
      w = ∫ h in b0..b1, Real.exp (h / 2) := by
        simpa only [w, b0, b1] using (integral_exp_half_quantileCell_eq_atomWeight n).symm
      _ ≤ ∫ _ in b0..b1, B := hmono
      _ = B * (b1 - b0) := by
        rw [intervalIntegral.integral_const]
        ring
  have hB : B = A + w / 2 := by
    dsimp only [A, B, b0, b1, w]
    rw [exp_half_ccmOutgoingPrimeQuantileBoundary,
      exp_half_ccmOutgoingPrimeQuantileBoundary,
      ccmOutgoingPrimeCumulative_succ]
    ring
  have hA1 : 1 ≤ A := by
    dsimp only [A, b0]
    rw [exp_half_ccmOutgoingPrimeQuantileBoundary]
    have hP := ccmOutgoingPrimeCumulative_nonneg n
    linarith
  have hw2 : w ≤ 2 := criticalMellinAtomWeight_le_two n
  have hB2A : B ≤ 2 * A := by rw [hB]; linarith
  exact hwB.trans (mul_le_mul_of_nonneg_right hB2A hgap)

/-- Self-interaction cost of one literal outgoing quantile cell. -/
def ccmOutgoingQuantileGammaDiagonalCellCost (n : ℕ) : ℝ :=
  ∫ r : ℝ, ccmOutgoingQuantileDisplacementCellDensity n r ^ 2 *
    ccmGammaHigherBinetDualDensity |r|

lemma ccmOutgoingQuantileGammaDiagonalCellCost_eq_interval (n : ℕ) :
    ccmOutgoingQuantileGammaDiagonalCellCost n =
      ∫ r in (ccmOutgoingPrimeQuantileBoundary n - Real.log n)..
          (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n),
        Real.exp ((r + Real.log n) / 2) ^ 2 *
          ccmGammaHigherBinetDualDensity |r| := by
  let S : Set ℝ := Ioc
    (ccmOutgoingPrimeQuantileBoundary n - Real.log n)
    (ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n)
  let F : ℝ → ℝ := fun r =>
    Real.exp ((r + Real.log n) / 2) ^ 2 *
      ccmGammaHigherBinetDualDensity |r|
  have heq : (fun r : ℝ =>
      ccmOutgoingQuantileDisplacementCellDensity n r ^ 2 *
        ccmGammaHigherBinetDualDensity |r|) = S.indicator F := by
    funext r
    by_cases hr : r ∈ S <;>
      simp [ccmOutgoingQuantileDisplacementCellDensity, S, F, hr]
  have hb := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hdisp : ccmOutgoingPrimeQuantileBoundary n - Real.log n ≤
      ccmOutgoingPrimeQuantileBoundary (n + 1) - Real.log n := by linarith
  unfold ccmOutgoingQuantileGammaDiagonalCellCost
  rw [heq, MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hdisp]

theorem criticalMellinAtomWeight_sq_div_eight_le_quantileGammaDiagonalCellCost
    (n : ℕ) :
    criticalMellinAtomWeight n ^ 2 / 8 ≤
      ccmOutgoingQuantileGammaDiagonalCellCost n := by
  let b0 := ccmOutgoingPrimeQuantileBoundary n
  let b1 := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let d0 := b0 - Real.log n
  let d1 := b1 - Real.log n
  let gap := b1 - b0
  let A := Real.exp (b0 / 2)
  let w := criticalMellinAtomWeight n
  have hb : b0 ≤ b1 := ccmOutgoingPrimeQuantileBoundary_mono_step n
  have hd : d0 ≤ d1 := by dsimp only [d0, d1]; linarith
  have hgap0 : 0 ≤ gap := by dsimp only [gap]; linarith
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have hFint : IntervalIntegrable (fun r : ℝ =>
      Real.exp ((r + Real.log n) / 2) ^ 2 *
        ccmGammaHigherBinetDualDensity |r|) volume d0 d1 := by
    exact (by
      unfold ccmGammaHigherBinetDualDensity
      fun_prop : Continuous fun r : ℝ =>
        Real.exp ((r + Real.log n) / 2) ^ 2 *
          ccmGammaHigherBinetDualDensity |r|).intervalIntegrable _ _
  have hGint : IntervalIntegrable (fun r : ℝ => 2 * A ^ 2 * |r|)
      volume d0 d1 := (by fun_prop : Continuous fun r : ℝ => 2 * A ^ 2 * |r|).intervalIntegrable _ _
  have hpoint : ∀ r ∈ Icc d0 d1,
      2 * A ^ 2 * |r| ≤
        Real.exp ((r + Real.log n) / 2) ^ 2 *
          ccmGammaHigherBinetDualDensity |r| := by
    intro r hr
    have hbase : b0 ≤ r + Real.log n := by
      dsimp only [d0] at hr
      linarith [hr.1]
    have hexp : A ≤ Real.exp ((r + Real.log n) / 2) := by
      dsimp only [A]
      exact Real.exp_le_exp.mpr (by linarith)
    have hX0 : 0 ≤ Real.exp ((r + Real.log n) / 2) := (Real.exp_pos _).le
    have hsq : A ^ 2 ≤ Real.exp ((r + Real.log n) / 2) ^ 2 := by nlinarith
    have hdual := two_mul_abs_le_ccmGammaHigherBinetDualDensity_abs r
    have habs : 0 ≤ |r| := abs_nonneg r
    have hdual0 := ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
    nlinarith
  have hmono : (∫ r in d0..d1, 2 * A ^ 2 * |r|) ≤
      ∫ r in d0..d1,
        Real.exp ((r + Real.log n) / 2) ^ 2 *
          ccmGammaHigherBinetDualDensity |r| :=
    intervalIntegral.integral_mono_on hd hGint hFint hpoint
  have habs := integral_Ioc_abs_ge_length_sq_div_four hd
  rw [← intervalIntegral.integral_of_le hd] at habs
  have hdgap : d1 - d0 = gap := by dsimp only [d0, d1, gap]; ring
  have hlower : A ^ 2 * gap ^ 2 / 2 ≤
      ∫ r in d0..d1,
        Real.exp ((r + Real.log n) / 2) ^ 2 *
          ccmGammaHigherBinetDualDensity |r| := by
    have hconst : (∫ r in d0..d1, 2 * A ^ 2 * |r|) =
        2 * A ^ 2 * ∫ r in d0..d1, |r| := by
      rw [intervalIntegral.integral_const_mul]
    rw [hconst] at hmono
    rw [hdgap] at habs
    nlinarith
  have hwgap : w ≤ 2 * A * gap := by
    simpa only [w, A, gap, b0, b1] using
      criticalMellinAtomWeight_le_two_exp_half_mul_quantileWidth n
  have hw0 : 0 ≤ w := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  have hAgap0 : 0 ≤ A * gap := mul_nonneg hA0 hgap0
  have hsq : w ^ 2 ≤ 4 * A ^ 2 * gap ^ 2 := by nlinarith
  rw [ccmOutgoingQuantileGammaDiagonalCellCost_eq_interval]
  dsimp only [d0, d1, b0, b1] at hlower ⊢
  nlinarith

/-- Sum of literal cell self-interactions, with every cross-cell term removed. -/
def ccmOutgoingQuantileGammaDiagonalCost (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ccmOutgoingQuantileGammaDiagonalCellCost n

lemma integrable_ccmOutgoingQuantileGammaDiagonalCellDensity (n : ℕ) :
    Integrable (fun r : ℝ =>
      ccmOutgoingQuantileDisplacementCellDensity n r ^ 2 *
        ccmGammaHigherBinetDualDensity |r|) := by
  simpa only [pow_two, mul_assoc] using
    integrable_ccmOutgoingQuantileDisplacementCellPair_mul_dual n n

theorem ccmOutgoingQuantileGammaDiagonalCost_le_chiSquare (N : ℕ) :
    ccmOutgoingQuantileGammaDiagonalCost N ≤
      ccmOutgoingQuantileGammaChiSquare N := by
  let G : ℝ → ℝ := fun r =>
    ∑ n ∈ Finset.range N,
      ccmOutgoingQuantileDisplacementCellDensity n r ^ 2 *
        ccmGammaHigherBinetDualDensity |r|
  let F : ℝ → ℝ := fun r =>
    ccmOutgoingQuantileDisplacementDensity N r ^ 2 *
      ccmGammaHigherBinetDualDensity |r|
  have hG : Integrable G := integrable_finsetSum (Finset.range N) fun n _ =>
    integrable_ccmOutgoingQuantileGammaDiagonalCellDensity n
  have hF : Integrable F := integrable_ccmOutgoingQuantileGammaChiSquareDensity N
  have hpoint : ∀ r : ℝ, G r ≤ F r := by
    intro r
    have hsq :
        (∑ n ∈ Finset.range N,
            ccmOutgoingQuantileDisplacementCellDensity n r ^ 2) ≤
          (∑ n ∈ Finset.range N,
            ccmOutgoingQuantileDisplacementCellDensity n r) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun n _ =>
        ccmOutgoingQuantileDisplacementCellDensity_nonneg n r
    have hdual : 0 ≤ ccmGammaHigherBinetDualDensity |r| :=
      ccmGammaHigherBinetDualDensity_nonneg (abs_nonneg r)
    dsimp only [G, F]
    unfold ccmOutgoingQuantileDisplacementDensity
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsq hdual
  calc
    ccmOutgoingQuantileGammaDiagonalCost N = ∫ r : ℝ, G r := by
      unfold ccmOutgoingQuantileGammaDiagonalCost
        ccmOutgoingQuantileGammaDiagonalCellCost
      rw [MeasureTheory.integral_finsetSum (Finset.range N) fun n _ =>
        integrable_ccmOutgoingQuantileGammaDiagonalCellDensity n]
    _ ≤ ∫ r : ℝ, F r := integral_mono hG hF hpoint
    _ = ccmOutgoingQuantileGammaChiSquare N := rfl

theorem criticalMellinAtomWeight_squarePartialSum_div_eight_le_diagonalCost
    (N : ℕ) :
    (∑ n ∈ Finset.range N, criticalMellinAtomWeight n ^ 2) / 8 ≤
      ccmOutgoingQuantileGammaDiagonalCost N := by
  rw [Finset.sum_div]
  unfold ccmOutgoingQuantileGammaDiagonalCost
  exact Finset.sum_le_sum fun n _ =>
    criticalMellinAtomWeight_sq_div_eight_le_quantileGammaDiagonalCellCost n

lemma primeCoeff_half_div_four_le_criticalMellinAtomWeight_sq (n : ℕ) :
    GaloisForLFunctions.RHTower.primeCoeff (1 / 2) n / 4 ≤
      criticalMellinAtomWeight n ^ 2 := by
  by_cases hp : n.Prime
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hp.pos
    have hmem : n ∈ {p : ℕ | p.Prime} := hp
    have hlog : (1 / 2 : ℝ) ≤ Real.log n := by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
      have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn2
      linarith [Real.log_two_gt_d9]
    rw [GaloisForLFunctions.RHTower.primeCoeff, Set.indicator_of_mem hmem]
    rw [criticalMellinAtomWeight_eq_div_sqrt,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    norm_num
    rw [div_pow, Real.sq_sqrt hnpos.le]
    rw [Real.rpow_neg_one]
    calc
      (n : ℝ)⁻¹ / 4 = (1 / 4 : ℝ) / n := by field_simp
      _ ≤ Real.log n ^ 2 / n :=
        div_le_div_of_nonneg_right (by nlinarith) hnpos.le
  · have hmem : n ∉ {p : ℕ | p.Prime} := hp
    rw [GaloisForLFunctions.RHTower.primeCoeff, Set.indicator_of_notMem hmem]
    norm_num
    exact sq_nonneg _

/-- Prime atoms alone force critical Mellin square mass to escape. -/
theorem tendsto_criticalMellinAtomWeight_squarePartialSum_atTop :
    Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N, criticalMellinAtomWeight n ^ 2) atTop atTop := by
  have hprime := GaloisForLFunctions.RHTower.tendsto_sum_primeCoeff_atTop
    (show (1 / 2 : ℝ) ≤ 1 / 2 by rfl)
  have hscaled := Filter.Tendsto.const_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 4) hprime
  refine tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards with N
  calc
    (1 / 4 : ℝ) *
        (∑ n ∈ Finset.range N,
          GaloisForLFunctions.RHTower.primeCoeff (1 / 2) n) =
        ∑ n ∈ Finset.range N,
          GaloisForLFunctions.RHTower.primeCoeff (1 / 2) n / 4 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _
            ring
    _ ≤ ∑ n ∈ Finset.range N, criticalMellinAtomWeight n ^ 2 :=
      Finset.sum_le_sum fun n _ =>
        primeCoeff_half_div_four_le_criticalMellinAtomWeight_sq n

/-- The diagonal literal-cell reciprocal-Γ cost diverges. -/
theorem tendsto_ccmOutgoingQuantileGammaDiagonalCost_atTop :
    Tendsto ccmOutgoingQuantileGammaDiagonalCost atTop atTop := by
  have hscaled := Filter.Tendsto.const_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 8)
    tendsto_criticalMellinAtomWeight_squarePartialSum_atTop
  refine tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards with N
  simpa [div_eq_mul_inv, mul_comm] using
    criticalMellinAtomWeight_squarePartialSum_div_eight_le_diagonalCost N

/-- **Unsigned reciprocal-Γ absorption diverges on literal quantile heads.**

This is a source-side no-go, not an asymptotic hypothesis: already the cell self-interactions force
escape. Cross-cell overlaps are nonnegative and can only increase the full chi-square cost. -/
theorem tendsto_ccmOutgoingQuantileGammaChiSquare_atTop :
    Tendsto ccmOutgoingQuantileGammaChiSquare atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    tendsto_ccmOutgoingQuantileGammaDiagonalCost_atTop
  exact Filter.Eventually.of_forall ccmOutgoingQuantileGammaDiagonalCost_le_chiSquare

/-- Every fixed unsigned reciprocal-Γ budget is eventually exceeded. -/
theorem eventually_lt_ccmOutgoingQuantileGammaChiSquare (C : ℝ) :
    ∀ᶠ N in atTop, C < ccmOutgoingQuantileGammaChiSquare N :=
  tendsto_ccmOutgoingQuantileGammaChiSquare_atTop.eventually_gt_atTop C

/-- The only viable finite-head producer after unsigned absorption is removed: higher Γ energy
plus the literal signed completed-error autocorrelation current. -/
def ccmActualHeadSignedCompletedErrorGammaProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
    ccmActualHeadOutgoingQuantileAutocorrelationCurrent a f

/-- Exact source law. Prime, polar, and first-Γ scalar channels cancel before this identity; the
producer is not an absolute envelope or a surrogate head. -/
theorem ccmActualHeadSignedCompletedErrorGammaProducer_eq_source_sub_scalar
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmActualHeadSignedCompletedErrorGammaProducer a u =
      ccmRestrictedWeilSourceQuadratic a u -
        2 * gammaHardyPhaseRate 0 *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  have hsource := ccmRestrictedWeilSourceQuadratic_eq_quantileAutocorrelation a u
  dsimp only at hsource
  unfold ccmActualHeadSignedCompletedErrorGammaProducer
  dsimp only
  rw [hsource]
  ring

/-- Canonical Γ-Slepian heads carry exactly true ground energy, vanishing tail, and the retained
archimedean scalar. No convergence or positivity premise is hidden in the producer. -/
theorem ccmCanonicalGroundHead_signedCompletedErrorGammaProducer_eq_ground_add_tail_sub_scalar
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmActualHeadSignedCompletedErrorGammaProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) =
      ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 +
        ccmRestrictedWeilCanonicalGroundHeadDefect a n -
        2 * gammaHardyPhaseRate 0 *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 := by
  rw [ccmActualHeadSignedCompletedErrorGammaProducer_eq_source_sub_scalar]
  unfold ccmRestrictedWeilCanonicalGroundHeadDefect
  ring

/-- The RH-bearing sign is the scalar-shifted producer threshold, not bare producer
nonnegativity.  This is the literal reverse-prime inequality on one canonical actual head. -/
theorem ccmCanonicalGroundHead_reversePrimeBound_iff_signedCompletedErrorGammaProducer_ge
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      -(2 * gammaHardyPhaseRate 0 *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2) ≤
        ccmActualHeadSignedCompletedErrorGammaProducer a
          (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_source_nonneg,
    ccmActualHeadSignedCompletedErrorGammaProducer_eq_source_sub_scalar]
  constructor <;> intro h <;> linarith

/-- At fixed aperture, cofinal threshold control of the cancellation-preserving producer is
exactly nonnegativity of the true restricted-Weil ground energy.  No unsigned Γ envelope can
replace this statement because the preceding chi-square theorem proves that envelope diverges. -/
theorem ccmRestrictedWeilGroundEnergy_nonneg_iff_eventually_signedCompletedErrorGammaProducer_ge
    (a : SuzukiPositiveAperture) :
    0 ≤ ccmRestrictedWeilGroundEnergy a ↔
      ∀ᶠ n in atTop,
        -(2 * gammaHardyPhaseRate 0 *
            ‖ccmArchimedeanFormToAperture a
              (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2) ≤
          ccmActualHeadSignedCompletedErrorGammaProducer a
            (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilGroundEnergy_nonneg_iff_eventually_canonicalGroundHead_reversePrimeBound]
  constructor
  · intro h
    filter_upwards [h] with n hn
    exact (ccmCanonicalGroundHead_reversePrimeBound_iff_signedCompletedErrorGammaProducer_ge
      a n).1 hn
  · intro h
    filter_upwards [h] with n hn
    exact (ccmCanonicalGroundHead_reversePrimeBound_iff_signedCompletedErrorGammaProducer_ge
      a n).2 hn

/-- Signed producer converges on literal canonical heads without splitting prime and polar masses.
This closes the convergence half of the actual-head problem; only sign of this explicit limit plus
the retained scalar remains RH-bearing. -/
theorem tendsto_ccmCanonicalGroundHead_signedCompletedErrorGammaProducer :
    ∀ a : SuzukiPositiveAperture,
    Tendsto
      (fun n : ℕ => ccmActualHeadSignedCompletedErrorGammaProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n)) atTop
      (nhds ((ccmRestrictedWeilGroundEnergy a - 2 * gammaHardyPhaseRate 0) *
        ‖(ccmRestrictedWeilCanonicalGroundEigenstate a :
          suzukiApertureHilbert a)‖ ^ 2)) := by
  intro a
  have hhead := tendsto_ccmRestrictedWeilCanonicalGroundHead a
  have hphysical : Tendsto
      (fun n : ℕ => ‖ccmArchimedeanFormToAperture a
        (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2) atTop
      (nhds (‖(ccmRestrictedWeilCanonicalGroundEigenstate a :
        suzukiApertureHilbert a)‖ ^ 2)) := by
    have hmap := (ccmArchimedeanFormToAperture a).continuous.continuousAt.tendsto.comp hhead
    rw [ccmRestrictedWeilCanonicalGroundFormLift_embedding] at hmap
    exact ((continuous_norm.tendsto _).comp hmap).pow 2
  have hsource := tendsto_ccmRestrictedWeilCanonicalGroundHead_sourceQuadratic a
  have hsub := hsource.sub (hphysical.const_mul (2 * gammaHardyPhaseRate 0))
  convert hsub using 1
  · ext n
    rw [ccmActualHeadSignedCompletedErrorGammaProducer_eq_source_sub_scalar]
  · congr 1
    ring

end RHTower
