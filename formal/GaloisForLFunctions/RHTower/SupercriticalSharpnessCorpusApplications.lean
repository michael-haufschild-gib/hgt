import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.HTGeometry.FiniteReporterConditionalInformation
import GaloisForLFunctions.HTGeometry.GADCTreePopulationRG
import GaloisForLFunctions.HTGeometry.PathShellEdgeTail
import GaloisForLFunctions.HTGeometry.TemporalSteinerBirthSpectrum
import GaloisForLFunctions.RHTower.FiniteAndersonLocalizedSurvivalRecurrenceLaw
import GaloisForLFunctions.RHTower.FiniteWindowRecurrenceInstability
import GaloisForLFunctions.RHTower.GateWordComplexityLaws
import GaloisForLFunctions.RHTower.ParityConditionedForecastingInstability
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireBoundedHeat
import GaloisForLFunctions.RHTower.TwoSpinFKGLeeYangBridge

/-!
# Corpus applications of supercritical-sharpness mechanisms

`[BRIDGE]` Concrete applications of mechanisms extracted from arXiv:2603.03257.  These results do
not assert a percolation model in the corpus.  They identify exact places where the paper's proof
technology acts on existing objects: temporal birth accumulation, path-shell union bounds,
discount sprinkling for gate words, localization-tail recursion, and two-spin FKG selectors.
-/

open scoped BigOperators ENNReal

namespace HTGeometry

noncomputable section

open GaloisForLFunctions Module

/-! ## Sequential conditional-information collection -/

/-- After `N` admitted derivative readings, visible reporter rank is at least `N`, or a concrete
earlier reading contributed zero conditional information.  This applies the paper's
touch-or-stall induction to the corpus's exact one-dimensional reporter-rank increments. -/
theorem finiteDerivativeReporter_rank_reaches_or_conditionalInformation_zero
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (N : ℕ) (f : ℂ → ℂ) (report : (ℂ → ℂ) →ₗ[ℂ] Y) :
    N ≤ finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f report)) ∨
      ∃ i < N, finiteDerivativeReporterConditionalInformation i f report = 0 := by
  let capacity : ℕ → ℕ := fun i ↦
    finrank ℂ (LinearMap.range (finiteDerivativeReporterMap i f report))
  have hzero : capacity 0 = 0 := by
    have hle := LinearMap.finrank_range_le (finiteDerivativeReporterMap 0 f report)
    simp only [capacity]
    simpa using hle
  have hmono : Monotone capacity := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hinfo : finiteDerivativeReporterConditionalInformation i f report = 0
    · exact le_of_eq
        ((finiteDerivativeReporterConditionalInformation_eq_zero_iff_finrank_range_eq
          i f report).1 hinfo).symm
    · exact ((finiteDerivativeReporterConditionalInformation_pos_iff_finrank_range_lt
        i f report).1 (lt_of_le_of_ne
          (finiteDerivativeReporterConditionalInformation_nonneg i f report)
          (Ne.symm hinfo))).le
  rcases GaloisForLFunctions.HTGeometry.reaches_threshold_or_exists_stall
      capacity N hzero hmono with hgain | hstall
  · left
    simpa only [capacity] using hgain
  · right
    obtain ⟨i, hi, hcap⟩ := hstall
    refine ⟨i, hi, ?_⟩
    apply (finiteDerivativeReporterConditionalInformation_eq_zero_iff_finrank_range_eq
      i f report).2
    simpa only [capacity] using hcap

end

end HTGeometry

namespace RHTower.ParityForecast

/-! ## FKG-style selector for a parity midpoint record -/

/-- For the shared parity/full observation record, one of the two terminal-error marginals is no
larger than the square root of their joint product.  This is the paper's midpoint square-root
alternative with the product of the two model errors as the joint-failure scale. -/
theorem scaledMidpoint_forecast_error_le_sqrt_product
    (forecast : (ℝ → ℝ) → ℝ) (T : ℝ) (n : ℕ) :
    |forecast (scaledMidpointProbability T n) - 1| ≤
        Real.sqrt
          (|forecast (scaledMidpointProbability T n) - 1| *
            |forecast (scaledMidpointProbability T n) - 0|) ∨
      |forecast (scaledMidpointProbability T n) - 0| ≤
        Real.sqrt
          (|forecast (scaledMidpointProbability T n) - 1| *
            |forecast (scaledMidpointProbability T n) - 0|) := by
  exact GaloisForLFunctions.HTGeometry.le_sqrt_or_le_sqrt_of_mul_le
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) le_rfl

end RHTower.ParityForecast

namespace RHTower.FiniteWindow

/-! ## FKG-style selector for a finite-window midpoint record -/

/-- The same square-root selector holds for the returning/orthogonal clock midpoint record. -/
theorem scaledMidpoint_forecast_error_le_sqrt_product
    (forecast : (ℝ → ℝ) → ℝ) (T : ℝ) (N : ℕ) :
    |forecast (scaledMidpointProbability T N) - 1| ≤
        Real.sqrt
          (|forecast (scaledMidpointProbability T N) - 1| *
            |forecast (scaledMidpointProbability T N) - 0|) ∨
      |forecast (scaledMidpointProbability T N) - 0| ≤
        Real.sqrt
          (|forecast (scaledMidpointProbability T N) - 1| *
            |forecast (scaledMidpointProbability T N) - 0|) := by
  exact GaloisForLFunctions.HTGeometry.le_sqrt_or_le_sqrt_of_mul_le
    (mul_nonneg (abs_nonneg _) (abs_nonneg _)) le_rfl

end RHTower.FiniteWindow

namespace RiemannGaussian

open Complex Filter Metric Polynomial Set

/-! ## Many disjoint spectral balls touched by canonical approximants -/

/-- Around any finite family of genuine spectral-xi zeros, the canonical real Taylor
approximants eventually place at least one root occurrence in each of pairwise disjoint isolating
balls.  This is the root-cluster analogue of the paper's many-disjoint-balls touch lemma. -/
theorem exists_pairwiseDisjoint_taylorRootBalls_eventually_card_le_rootCountSum
    (S : Finset NontrivialZetaZero) :
    ∃ R : S → ℝ,
      (∀ rho : S, 0 < R rho ∧
        ∀ z ∈ closedBall (zetaSpectralCoordinate rho.1.1) (R rho),
          z ≠ zetaSpectralCoordinate rho.1.1 → riemannXiSpectral z ≠ 0) ∧
      (Set.univ : Set S).PairwiseDisjoint (fun rho : S ↦
        closedBall (zetaSpectralCoordinate rho.1.1) (R rho)) ∧
      ∀ᶠ n in atTop,
        S.card ≤ ∑ rho : S,
          realPolynomialRootCountInBall
            (riemannXiSpectralRealTaylorPolynomial n)
            (zetaSpectralCoordinate rho.1.1) (R rho) := by
  obtain ⟨R, hR, hdisjoint, hcounts⟩ :=
    exists_pairwiseDisjoint_simultaneous_riemannXiSpectral_localRootCounts
      riemannXiSpectralRealTaylorPolynomial
      riemannXiSpectralRealTaylorPolynomial_tendstoLocallyUniformlyOn S
  refine ⟨R, hR, hdisjoint, ?_⟩
  filter_upwards [hcounts] with n hn
  calc
    S.card = ∑ _rho : S, 1 := by simp
    _ ≤ ∑ rho : S, analyticZetaZeroMultiplicity rho.1 := by
      exact Finset.sum_le_sum fun rho _ ↦
        analyticZetaZeroMultiplicity_positive rho.1
    _ = ∑ rho : S,
        realPolynomialRootCountInBall
          (riemannXiSpectralRealTaylorPolynomial n)
          (zetaSpectralCoordinate rho.1.1) (R rho) := by
      exact Finset.sum_congr rfl fun rho _ ↦ (hn rho).symm

end RiemannGaussian

namespace GaloisForLFunctions.HTGeometry

/-! ## One-touch-at-a-time temporal Steiner growth -/

/-- Temporal Steiner capacity either gains at least one mode per depth, or a concrete birth layer
is empty.  This is the deterministic touch-or-stall dichotomy from the paper applied to the
corpus's connected-interaction birth spectrum. -/
theorem temporalSteinerCapacity_accumulates_or_birth_stalls
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) (r : ℕ) :
    temporalSteinerCapacity (A := A) (base := base) (R := R) G 0 + r ≤
        temporalSteinerCapacity (A := A) (base := base) (R := R) G r ∨
      ∃ i < r,
        temporalSteinerBirthMultiplicity
          (A := A) (base := base) (R := R) G (i + 1) = 0 := by
  have hmono : Monotone fun i =>
      temporalSteinerCapacity (A := A) (base := base) (R := R) G i := by
    intro i j hij
    exact temporalSteinerCapacity_mono G hij
  rcases accumulates_touches_or_exists_stall
      (fun i => temporalSteinerCapacity (A := A) (base := base) (R := R) G i)
      r hmono with hgain | ⟨i, hi, hstall⟩
  · exact Or.inl hgain
  · right
    refine ⟨i, hi, ?_⟩
    simp [temporalSteinerBirthMultiplicity, hstall]

/-! ## Union-bound collection on path-local shells -/

/-- Named union-bound interface for the path shell: every weak global cut is charged to at least
one weak edge block.  This is the paper's collection/union mechanism at a concrete corpus site. -/
theorem pathConductanceSmall_probability_le_edge_sum {n : ℕ} (x : ℝ) :
    pathShellProb
        {u : Metric.sphere (0 : PathShell n) 1 |
          pathConductance (u : PathShell n) ≤ x} ≤
      ∑ e : Fin (n + 1), pathShellProb (edgeSmall e x) := by
  exact (pathShellProb_mono conductanceSmall_subset_iUnion).trans
    (pathShellProb_iUnion_le fun e : Fin (n + 1) => edgeSmall e x)

/-- Complementary budget: the formal mass left after paying every weak-edge event is no larger
than the mass left after paying the global weak-conductance event. -/
theorem pathConductanceStrong_budget_ge_edge_union_budget {n : ℕ} (x : ℝ) :
    1 - ∑ e : Fin (n + 1), pathShellProb (edgeSmall e x) ≤
      1 - pathShellProb
        {u : Metric.sphere (0 : PathShell n) 1 |
          pathConductance (u : PathShell n) ≤ x} := by
  linarith [pathConductanceSmall_probability_le_edge_sum (n := n) x]

/-! ## Many-touch limits of the GADC tree channel -/

/-- At zero damping, every finite family of positive-input touches succeeds with unit weight. -/
@[simp] theorem gadc_noiseless_all_positive_touch_mass (p : ℕ) (N : ℚ) :
    gadcPositiveOutputProbability 0 N ^ p = 1 := by
  simp [gadcPositiveOutputProbability]

/-- At zero damping, any nonempty family of negative-input false-positive touches has zero weight. -/
@[simp] theorem gadc_noiseless_negative_touch_mass (p : ℕ) (N : ℚ) :
    gadcNegativeOutputProbability 0 N ^ (p + 1) = 0 := by
  simp [gadcNegativeOutputProbability]

/-- Full damping erases the input before any number of touches: positive- and negative-parent
branch weights coincide exactly. -/
theorem gadc_fullDamping_touch_mass_eq (p : ℕ) (N : ℚ) :
    gadcPositiveOutputProbability 1 N ^ p =
      gadcNegativeOutputProbability 1 N ^ p := by
  congr 1
  simp [gadcPositiveOutputProbability, gadcNegativeOutputProbability]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

/-! ## Sprinkling the gate-word discount -/

/-- Increasing the gate-word discount can only increase discounted first-hit mass.  This is the
monotone part of the paper's sprinkling mechanism applied to the corpus's prefix-free first-hit
partition function. -/
theorem firstHitMass_mono_discount
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {X : Type*}
    (act : Γ → X → X) (χ : X) (target : Set X) {a b : ℝ≥0∞} (hab : a ≤ b) :
    firstHitMass act χ target a ≤ firstHitMass act χ target b := by
  classical
  unfold firstHitMass
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : FirstHitWord act χ target w
  · rw [Set.indicator_of_mem
        (show w ∈ {w : List Γ | FirstHitWord act χ target w} from hw),
      Set.indicator_of_mem
        (show w ∈ {w : List Γ | FirstHitWord act χ target w} from hw)]
    gcongr
  · rw [Set.indicator_of_notMem
        (show w ∉ {w : List Γ | FirstHitWord act χ target w} from hw),
      Set.indicator_of_notMem
        (show w ∉ {w : List Γ | FirstHitWord act χ target w} from hw)]

/-- Real-valued first-hit mass inherits discount sprinkling throughout the unit interval. -/
theorem firstHitMassReal_mono_discount
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] {X : Type*}
    (act : Γ → X → X) (χ : X) (target : Set X) {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ 1) :
    firstHitMassReal act χ target a ≤ firstHitMassReal act χ target b := by
  unfold firstHitMassReal
  have hbE : ENNReal.ofReal b ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hb
  exact ENNReal.toReal_mono (firstHitMass_ne_top act χ target hbE)
    (firstHitMass_mono_discount act χ target (ENNReal.ofReal_le_ofReal hab))

end GaloisForLFunctions.RHTower

namespace RHTower

/-! ## Geometric mass collection in Anderson-localization tails -/

/-- Advancing the localization radius by `k` multiplies the explicit tail budget by the exact
geometric factor.  This is the paper's recursive mass-collection algebra at the Anderson-tail
corpus site. -/
theorem finiteLocalizationGeometricTailBound_add
    (C μ A B : ℝ) (R k : ℕ) :
    finiteLocalizationGeometricTailBound C μ A B (R + k) =
      (B * Real.exp (-2 * μ)) ^ k *
        finiteLocalizationGeometricTailBound C μ A B R := by
  unfold finiteLocalizationGeometricTailBound
  rw [show R + k + 1 = k + (R + 1) by omega, pow_add]
  ring

/-- One-radius recurrence for the localization tail budget. -/
theorem finiteLocalizationGeometricTailBound_succ
    (C μ A B : ℝ) (R : ℕ) :
    finiteLocalizationGeometricTailBound C μ A B (R + 1) =
      (B * Real.exp (-2 * μ)) *
        finiteLocalizationGeometricTailBound C μ A B R := by
  simpa using finiteLocalizationGeometricTailBound_add C μ A B R 1

end RHTower

namespace GaloisForLFunctions.RHTower

/-! ## FKG midpoint selector for prime Euler versus reciprocal pairing -/

/-- Probability of one aligned cell in the normalized symmetric two-spin table
`[[1,c],[c,1]]`. -/
noncomputable def normalizedTwoSpinAlignedJointWeight (c : ℝ) : ℝ :=
  1 / (2 * (1 + c))

/-- Every prime Euler ferromagnetic interaction has aligned joint mass strictly above the
independent value `1/4`.  This is the positive-association input used by the paper's midpoint
square-root trick. -/
theorem primeEuler_normalizedTwoSpinAlignedJointWeight_gt_quarter
    (p : Nat.Primes) :
    1 / 4 < normalizedTwoSpinAlignedJointWeight
      (RHTower.primeEulerFerromagneticCoefficient p) := by
  have hc0 := RHTower.primeEulerFerromagneticCoefficient_pos p
  have hc1 := RHTower.primeEulerFerromagneticCoefficient_lt_one p
  have hden : 0 < 2 * (1 + RHTower.primeEulerFerromagneticCoefficient p) := by
    positivity
  rw [normalizedTwoSpinAlignedJointWeight, lt_div_iff₀ hden]
  nlinarith

/-- Reciprocal pairing of a positive contracting Euler weight has aligned joint mass strictly
below `1/4`.  Thus the same midpoint mechanism reverses direction exactly where the existing FKG
defect theorem says positive association fails. -/
theorem reciprocalEulerPair_normalizedTwoSpinAlignedJointWeight_lt_quarter
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    normalizedTwoSpinAlignedJointWeight (reciprocalEulerPairCoefficient a) < 1 / 4 := by
  have hdefect := reciprocalEulerPair_twoSpinFKGDefect_neg ha ha1
  have hc0 : 0 < reciprocalEulerPairCoefficient a := by
    unfold reciprocalEulerPairCoefficient
    positivity
  have hc1 : 1 < reciprocalEulerPairCoefficient a := by
    unfold twoSpinFKGDefect at hdefect
    nlinarith
  have hden : 0 < 2 * (1 + reciprocalEulerPairCoefficient a) := by positivity
  rw [normalizedTwoSpinAlignedJointWeight, div_lt_iff₀ hden]
  nlinarith

end GaloisForLFunctions.RHTower
