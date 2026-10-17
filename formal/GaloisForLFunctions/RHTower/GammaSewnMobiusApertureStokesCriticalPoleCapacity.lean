import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalClockNonclosability
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesSquaredCompactMarkovCandidate
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPassiveDeletionSignedCorrection
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPositiveCompletionNoGo
import GaloisForLFunctions.RHTower.PrimeArchMomentRepresentationRigidity

/-!
# Critical Stokes pole capacity and the passive-deletion obstruction

At critical aperture, each inverse Stokes tilt is a positive algebraic multiple of a prime
logarithm. Gelfond–Schneider therefore separates every prime/depth pole. The exact source residue
is `log(p) p^(-(e+1)/2) < 1`, so the raw squared carrier has singleton mass strictly below `2x`
at every positive node `x`.

Functional-equation reflection gives the canonical Xi moment measure at least mass `2x` at each
of its thermal nodes. Every complete positive moment witness is already known to equal that
canonical measure. Consequently arbitrary deletion/downweighting of the critical Stokes carrier
cannot realize the completed source, even without the residual floor imposed by earlier diagonal
transfer obstructions.

The positive survivor is stronger than nonexistence: every exact witness must increase infinitely
many distinct singleton masses. Finite atom repairs fail, and combining the new obstruction with
the existing supercarrier obstruction forces both added and removed mass. These are unconditional
constraints on source completion; they do not prove RH or the complete-current sign.
-/

open Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- The critical aperture node is algebraic because its square is the reciprocal prime. -/
theorem criticalStokesNode_isAlgebraic (p : Nat.Primes) :
    IsAlgebraic ℚ (criticalStokesNode p) := by
  apply IsAlgebraic.of_pow (n := 2) (by norm_num)
  rw [criticalStokesNode_sq]
  exact (isAlgebraic_nat p.1).inv

/-- The exact fourth-power sewing law makes the critical Gamma contraction algebraic. -/
theorem criticalStokesContraction_isAlgebraic (p : Nat.Primes) :
    IsAlgebraic ℚ (gammaSewnMobiusValuationContractionMultiplier (1 / 2) p) := by
  apply IsAlgebraic.of_pow (n := 4) (by norm_num)
  rw [gammaSewnMobiusValuationContractionMultiplier_pow_four]
  change IsAlgebraic ℚ
    ((1 + criticalStokesNode p) ^ 4 / (8 * (1 + criticalStokesNode p ^ 4)))
  have hr := criticalStokesNode_isAlgebraic p
  have h1 : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  have h8 : IsAlgebraic ℚ (8 : ℝ) := isAlgebraic_nat 8
  exact ((h1.add hr).pow 4).mul ((h8.mul (h1.add (hr.pow 4))).inv)

/-- The inverse Stokes tilt differs from the prime logarithm by an algebraic factor. -/
theorem criticalStokesInverseTilt_div_log_isAlgebraic (p : Nat.Primes) :
    IsAlgebraic ℚ (gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p /
      Real.log (p : ℝ)) := by
  have hr := criticalStokesNode_isAlgebraic p
  have hc := criticalStokesContraction_isAlgebraic p
  have h1 : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (show (1 : ℝ) < p by exact_mod_cast p.2.one_lt)).ne'
  have hscale := hr.inv.mul ((h1.add (hr.pow 2)).mul (hc.mul (h1.sub hr)).inv)
  have heq : gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p / Real.log (p : ℝ) =
      (criticalStokesNode p)⁻¹ * ((1 + criticalStokesNode p ^ 2) *
        (gammaSewnMobiusValuationContractionMultiplier (1 / 2) p *
          (1 - criticalStokesNode p))⁻¹) := by
    rw [gammaSewnMobiusApertureStokesCriticalInverseTilt_eq]
    field_simp
  rw [heq]
  exact hscale

/-- Every prime/depth gap has an algebraic ratio to its own prime logarithm. -/
theorem criticalStokesGap_div_log_isAlgebraic (pk : Nat.Primes × ℕ) :
    IsAlgebraic ℚ (gammaSewnMobiusApertureStokesGap (1 / 2) pk /
      Real.log (pk.1 : ℝ)) := by
  rw [gammaSewnMobiusApertureStokesGap, mul_div_assoc]
  exact ((isAlgebraic_nat pk.2).add isAlgebraic_one).mul
    (criticalStokesInverseTilt_div_log_isAlgebraic pk.1)

/-- Distinct critical Stokes labels have distinct gaps, by Gelfond–Schneider across primes. -/
theorem criticalStokesGap_injective :
    Function.Injective (gammaSewnMobiusApertureStokesGap (1 / 2)) := by
  rintro ⟨p, e⟩ ⟨q, f⟩ hgap
  have hpq : p = q := by
    by_contra hne
    have hlogp : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (show (1 : ℝ) < p by exact_mod_cast p.2.one_lt)).ne'
    have hlogq : Real.log (q : ℝ) ≠ 0 :=
      (Real.log_pos (show (1 : ℝ) < q by exact_mod_cast q.2.one_lt)).ne'
    have hg : gammaSewnMobiusApertureStokesGap (1 / 2) (q, f) ≠ 0 :=
      (gammaSewnMobiusApertureStokesGap_pos (by norm_num) _).ne'
    have halg := (criticalStokesGap_div_log_isAlgebraic (p, e)).mul
      (criticalStokesGap_div_log_isAlgebraic (q, f)).inv
    have hratio :
        gammaSewnMobiusApertureStokesGap (1 / 2) (p, e) / Real.log (p : ℝ) *
          (gammaSewnMobiusApertureStokesGap (1 / 2) (q, f) / Real.log (q : ℝ))⁻¹ =
        Real.log (q : ℝ) / Real.log (p : ℝ) := by
      rw [hgap]
      field_simp
    rw [hratio] at halg
    exact GaloisForLFunctions.RHTower.log_ratio_transcendental p.2 q.2
      (fun h => hne (Subtype.ext h)) halg
  subst q
  have hW := (gammaSewnMobiusApertureStokesInverseTilt_pos
    (s := (1 / 2 : ℝ)) (by norm_num) p).ne'
  have hef : (e : ℝ) + 1 = (f : ℝ) + 1 :=
    mul_right_cancel₀ hW hgap
  have hef' : e = f := by exact_mod_cast (add_right_cancel hef)
  subst f
  rfl

/-- Squaring reciprocal positive gaps preserves separation of every prime/depth label. -/
theorem criticalStokesSquaredNode_injective :
    Function.Injective (gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)) := by
  intro pk qk h
  apply criticalStokesGap_injective
  apply inv_injective
  change (gammaSewnMobiusApertureStokesGap (1 / 2) pk)⁻¹ ^ 2 =
    (gammaSewnMobiusApertureStokesGap (1 / 2) qk)⁻¹ ^ 2 at h
  have hp := inv_pos.mpr (gammaSewnMobiusApertureStokesGap_pos
    (s := (1 / 2 : ℝ)) (by norm_num) pk)
  have hq := inv_pos.mpr (gammaSewnMobiusApertureStokesGap_pos
    (s := (1 / 2 : ℝ)) (by norm_num) qk)
  nlinarith

/-- The elementary exponential quadratic bound puts the leading Euler residue below one. -/
theorem criticalStokes_log_mul_node_lt_one (p : Nat.Primes) :
    Real.log (p : ℝ) * criticalStokesNode p < 1 := by
  have hL : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hquad := Real.quadratic_le_exp_of_nonneg
    (show 0 ≤ Real.log (p : ℝ) / 2 by positivity)
  have hLexp : Real.log (p : ℝ) < Real.exp (Real.log (p : ℝ) / 2) := by
    nlinarith [sq_nonneg (Real.log (p : ℝ) / 2 - 1)]
  have heq : criticalStokesNode p = (Real.exp (Real.log (p : ℝ) / 2))⁻¹ := by
    rw [criticalStokesNode, xiMobiusContinuousApertureDiskNode]
    rw [show -(1 / 2 : ℝ) * Real.log (p : ℝ) = -(Real.log (p : ℝ) / 2) by ring,
      Real.exp_neg]
  rw [heq, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
  exact hLexp

/-- Exact critical residue recovered from the pre-Gram source edge, without an analytic premise. -/
theorem criticalStokes_residue_eq (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesDualFeatureCoefficient (1 / 2) pk *
        gammaSewnMobiusApertureStokesGap (1 / 2) pk =
      Real.log (pk.1 : ℝ) * criticalStokesNode pk.1 ^ (pk.2 + 1) := by
  have hedge := gammaSewnMobiusApertureStokesInverseTilt_mul_edge
    (s := (1 / 2 : ℝ)) (by norm_num) pk.1 pk.2
  rw [gammaSewnMobiusContinuousApertureFeature_zero, sub_zero] at hedge
  rw [gammaSewnMobiusApertureStokesDualFeatureCoefficient,
    gammaSewnMobiusApertureStokesGap]
  have hn : (pk.2 : ℝ) + 1 ≠ 0 := by positivity
  calc
    _ = gammaSewnMobiusApertureStokesInverseTilt (1 / 2) pk.1 *
        gammaSewnMobiusContinuousApertureFeature (1 / 2) pk.1 pk.2 := by field_simp
    _ = _ := hedge

/-- Every critical prime-power residue is strictly below one. -/
theorem criticalStokes_residue_lt_one (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesDualFeatureCoefficient (1 / 2) pk *
      gammaSewnMobiusApertureStokesGap (1 / 2) pk < 1 := by
  rw [criticalStokes_residue_eq, pow_succ]
  have hr0 := (criticalStokesNode_pos pk.1).le
  have hr1 : criticalStokesNode pk.1 ≤ 1 :=
    (xiMobiusContinuousApertureDiskNode_lt_one (by norm_num) pk.1).le
  have hp := pow_le_one₀ hr0 hr1 (n := pk.2)
  have hL : 0 ≤ Real.log (pk.1 : ℝ) :=
    (Real.log_pos (show (1 : ℝ) < pk.1 by exact_mod_cast pk.1.2.one_lt)).le
  exact (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left hr0 hp) hL).trans_lt
    (criticalStokes_log_mul_node_lt_one pk.1)

/-- A raw Stokes atom has less than the mass required by one reflected Xi zero pair. -/
theorem criticalStokesSquaredWeight_lt_twice_node (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk <
      2 * gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk := by
  have hg := gammaSewnMobiusApertureStokesGap_pos (s := (1 / 2 : ℝ)) (by norm_num) pk
  have hres := criticalStokes_residue_lt_one pk
  change 2 * (gammaSewnMobiusApertureStokesDualFeatureCoefficient (1 / 2) pk /
    gammaSewnMobiusApertureStokesGap (1 / 2) pk) <
    2 * (gammaSewnMobiusApertureStokesGap (1 / 2) pk)⁻¹ ^ 2
  calc
    _ = (gammaSewnMobiusApertureStokesDualFeatureCoefficient (1 / 2) pk *
        gammaSewnMobiusApertureStokesGap (1 / 2) pk) *
        (2 * (gammaSewnMobiusApertureStokesGap (1 / 2) pk)⁻¹ ^ 2) := by
      field_simp
    _ < 1 * (2 * (gammaSewnMobiusApertureStokesGap (1 / 2) pk)⁻¹ ^ 2) :=
      mul_lt_mul_of_pos_right hres (by positivity)
    _ = _ := one_mul _

/-- Pole separation identifies each raw singleton mass exactly, including the full countable sum. -/
theorem criticalStokesCarrier_singleton (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier
        {gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk} =
      ENNReal.ofReal (gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk) := by
  classical
  rw [gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier,
    gammaSewnMobiusApertureStokesSquaredCompactCarrier,
    Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single pk]
  · simp
  · intro qk hne
    have hn := criticalStokesSquaredNode_injective.ne hne
    simp only [one_div] at hn
    simp [hn]

/-- The full raw carrier lies below pair capacity at every positive singleton, on or off its support. -/
theorem criticalStokesCarrier_singleton_lt_twice {x : ℝ} (hx : 0 < x) :
    gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier {x} <
      ENNReal.ofReal (2 * x) := by
  classical
  by_cases hnode : ∃ pk, gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk = x
  · obtain ⟨pk, rfl⟩ := hnode
    rw [criticalStokesCarrier_singleton]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (criticalStokesSquaredWeight_lt_twice_node pk)
  · have hzero : gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier {x} = 0 := by
      rw [gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier,
        gammaSewnMobiusApertureStokesSquaredCompactCarrier,
        Measure.sum_apply _ (measurableSet_singleton _)]
      have hterm : ∀ pk : Nat.Primes × ℕ,
          (ENNReal.ofReal (gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk) •
            Measure.dirac
              (gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk)) {x} = 0 := by
        intro pk
        have hn : gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2) pk ≠ x :=
          fun heq => hnode ⟨pk, heq⟩
        simp only [one_div] at hn
        simp [hn]
      simp only [hterm, tsum_zero]
    rw [hzero]
    exact ENNReal.ofReal_pos.mpr (by positivity)

/-- A zero copy and its distinct reflection contribute equal mass at the same thermal node; RH is unnecessary. -/
theorem twice_xiThermalNode_le_compactMomentMeasure_singleton (q : XiZeroCopy) :
    ENNReal.ofReal (2 * xiThermalNode q) ≤
      primeArchXiCompactMomentMeasure {xiThermalNode q} := by
  classical
  have href : xiThermalNode (xiZeroCopyReflectEquiv q) = xiThermalNode q := by
    simp [xiThermalNode, xiZeroCopyReciprocalSquare, xiSpectralPoint_reflect]
  have hne : xiZeroCopyReflectEquiv q ≠ q := by
    intro heq
    have hspec := congrArg xiSpectralPoint heq
    rw [xiSpectralPoint_reflect] at hspec
    apply xiSpectralPoint_ne_zero q
    linear_combination (-1 / 2 : ℂ) * hspec
  obtain ⟨j, hj⟩ := xiThermalEnumeration_bijective.2 q
  obtain ⟨k, hk⟩ := xiThermalEnumeration_bijective.2 (xiZeroCopyReflectEquiv q)
  have hjk : j ≠ k := by
    intro heq
    subst k
    exact hne (hk.symm.trans hj)
  rw [primeArchXiCompactMomentMeasure,
    Measure.sum_apply _ (measurableSet_singleton _)]
  have hpair := ENNReal.sum_le_tsum
    (f := fun n : ℕ =>
      (ENNReal.ofReal (xiThermalNode (xiThermalEnumeration n)) •
        Measure.dirac (xiThermalNode (xiThermalEnumeration n))) {xiThermalNode q})
    ({j, k} : Finset ℕ)
  rw [two_mul, ENNReal.ofReal_add (xiThermalNode_pos q).le (xiThermalNode_pos q).le]
  simpa [hjk, hj, hk, href] using hpair

/-- Every canonical Xi atom requires strictly more mass than the raw Stokes carrier supplies there. -/
theorem criticalStokesCarrier_lt_xiCompactMomentMeasure_singleton (q : XiZeroCopy) :
    gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier {xiThermalNode q} <
      primeArchXiCompactMomentMeasure {xiThermalNode q} :=
  (criticalStokesCarrier_singleton_lt_twice (xiThermalNode_pos q)).trans_le
    (twice_xiThermalNode_le_compactMomentMeasure_singleton q)

/-- The canonical Xi measure cannot be obtained by arbitrary passive deletion of raw Stokes mass. -/
theorem xiCompactMomentMeasure_not_le_criticalStokesCarrier :
    ¬ primeArchXiCompactMomentMeasure ≤
      gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier := by
  intro hle
  exact (not_le_of_gt
    (criticalStokesCarrier_lt_xiCompactMomentMeasure_singleton (xiThermalEnumeration 0)))
    (hle {xiThermalNode (xiThermalEnumeration 0)})

/-- Every complete positive source witness must increase the mass at every canonical Xi atom. -/
theorem IsPrimeArchMomentWitness.criticalStokes_singleton_lt
    {μ : Measure ℝ} (hμ : IsPrimeArchMomentWitness μ) (q : XiZeroCopy) :
    gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier {xiThermalNode q} <
      μ {xiThermalNode q} := by
  rw [hμ.eq_primeArchXiCompactMomentMeasure]
  exact criticalStokesCarrier_lt_xiCompactMomentMeasure_singleton q

/-- No unrestricted positive moment witness is dominated by the raw critical Stokes carrier. -/
theorem IsPrimeArchMomentWitness.not_le_criticalStokesCarrier
    {μ : Measure ℝ} (hμ : IsPrimeArchMomentWitness μ) :
    ¬ μ ≤ gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier := by
  rw [hμ.eq_primeArchXiCompactMomentMeasure]
  exact xiCompactMomentMeasure_not_le_criticalStokesCarrier

/-- Positive summable thermal nodes approach zero and therefore have infinitely many distinct values. -/
theorem xiThermalNode_enumeration_range_infinite :
    (Set.range fun j : ℕ => xiThermalNode (xiThermalEnumeration j)).Infinite := by
  intro hfinite
  have hT : Tendsto (fun j : ℕ => xiThermalNode (xiThermalEnumeration j))
      atTop (𝓝 0) := by
    simpa only [Nat.zero_add, pow_one] using
      (hasSum_xiThermalEnumeration_positiveMoment 0).summable.tendsto_atTop_zero
  have hzero := hfinite.isClosed.mem_of_tendsto hT
    (Filter.Eventually.of_forall (fun j => Set.mem_range_self j))
  obtain ⟨j, hj⟩ := hzero
  exact (xiThermalNode_pos (xiThermalEnumeration j)).ne' hj

/-- The raw carrier has a strict mass deficit at infinitely many distinct canonical atoms. -/
theorem criticalStokesCarrier_infinite_atom_deficit :
    {x : ℝ | gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier {x} <
      primeArchXiCompactMomentMeasure {x}}.Infinite := by
  apply xiThermalNode_enumeration_range_infinite.mono
  rintro x ⟨j, rfl⟩
  exact criticalStokesCarrier_lt_xiCompactMomentMeasure_singleton (xiThermalEnumeration j)

/-- Every exact positive source completion must add mass at infinitely many distinct singleton sets. -/
theorem IsPrimeArchMomentWitness.infinite_criticalStokes_atom_deficit
    {μ : Measure ℝ} (hμ : IsPrimeArchMomentWitness μ) :
    {x : ℝ | gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier {x} < μ {x}}.Infinite := by
  rw [hμ.eq_primeArchXiCompactMomentMeasure]
  exact criticalStokesCarrier_infinite_atom_deficit

/-- Changing only finitely many singleton masses cannot repair the raw Stokes carrier. -/
theorem not_isPrimeArchMomentWitness_of_criticalStokes_finite_atom_repair
    {μ : Measure ℝ} {S : Set ℝ} (hS : S.Finite)
    (hrepair : ∀ x ∉ S,
      μ {x} = gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier {x}) :
    ¬ IsPrimeArchMomentWitness μ := by
  intro hμ
  apply hμ.infinite_criticalStokes_atom_deficit
  apply hS.subset
  intro x hx
  by_contra hnot
  change gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier {x} < μ {x} at hx
  rw [hrepair x hnot] at hx
  exact (lt_irrefl _) hx

/-- A specified compact Markov germ fixes the moments of that same measure. -/
private theorem momentWitness_of_compactMarkovGerm
    {μ : Measure ℝ} [IsFiniteMeasure μ] {B : ℝ} (hB : 0 < B)
    (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B)
    (hgerm : completedSeamMomentGerm =ᶠ[𝓝 0] compactMarkovTransform μ) :
    IsPrimeArchMomentWitness μ := by
  constructor
  · intro n
    have hder := hgerm.iteratedDeriv_eq n
    rw [iteratedDeriv_completedSeamMomentGerm,
      iteratedDeriv_compactMarkovTransform μ hB hbound n
        (by simpa using (show (0 : ℝ) < 1 / (2 * B) by positivity)),
      compactMarkovKernelMoment_zero_node] at hder
    have hintc : (∫ x : ℝ, (x : ℂ) ^ n ∂μ) =
        ((∫ x : ℝ, x ^ n ∂μ : ℝ) : ℂ) := by
      simpa using (integral_ofReal (X := ℝ) (μ := μ) (𝕜 := ℂ)
        (f := fun x : ℝ => x ^ n))
    rw [hintc] at hder
    have hfacne : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    exact Complex.ofReal_inj.mp (mul_left_cancel₀ hfacne hder)
  · intro n
    refine Integrable.of_bound (continuous_id.pow n).aestronglyMeasurable (B ^ n) ?_
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx n

/-- Arbitrary passive deletion is impossible, including transfers without any positive residual floor. -/
theorem not_gammaSewnMobiusApertureStokesCriticalPassiveDeletionCompletion :
    ¬ GammaSewnMobiusApertureStokesCriticalPassiveDeletionCompletion := by
  rintro ⟨μ, B, hfinite, hB, hsupport, hle, hgerm⟩
  letI : IsFiniteMeasure μ := hfinite
  exact (momentWitness_of_compactMarkovGerm hB
    (hsupport.mono fun _ hx => hx.2) hgerm).not_le_criticalStokesCarrier hle

/-- A purely negative correction cannot retain positivity and reproduce the completed source. -/
theorem not_gammaSewnMobiusApertureStokesCriticalPassiveNegativeCorrectionCompletion :
    ¬ GammaSewnMobiusApertureStokesCriticalPassiveNegativeCorrectionCompletion := by
  rw [gammaSewnMobiusApertureStokesCriticalPassiveNegativeCorrection_iff_deletion]
  exact not_gammaSewnMobiusApertureStokesCriticalPassiveDeletionCompletion

/-- Exact positive completion requires both addition and removal of raw mass; neither measure dominates the other. -/
theorem criticalStokesCarrier_incomparable_of_completedSeamMomentGerm
    {μ : Measure ℝ} [IsFiniteMeasure μ] {B : ℝ} (hB : 0 < B)
    (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ B)
    (hgerm : completedSeamMomentGerm =ᶠ[𝓝 0] compactMarkovTransform μ) :
    (¬ μ ≤ gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier) ∧
      (¬ gammaSewnMobiusApertureStokesCriticalSquaredCompactCarrier ≤ μ) :=
  ⟨(momentWitness_of_compactMarkovGerm hB hbound hgerm).not_le_criticalStokesCarrier,
    criticalStokes_not_le_of_completedSeamMomentGerm_eq_compactMarkov μ hgerm⟩

end
end RHTower
