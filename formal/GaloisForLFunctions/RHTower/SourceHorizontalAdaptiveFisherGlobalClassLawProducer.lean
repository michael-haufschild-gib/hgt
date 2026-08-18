import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherCofinalContiguitySelection

/-!
# Global class-law producer classification for adaptive Fisher selection

The neutral adaptive occupation `1 / (p + 1)` is realized by one actual convergent abelian class
law before any Xi copy is selected.  Its temperature slope is `log (p + 1) / log p`, and the
observer asks whether the prime-depth-one mode is occupied.  Reusing this observer at every scale
gives an unconditional class-law scale-orbit certificate at centered rate zero.

This is the maximal source-first producer compatible with cofinal contiguity.  The existing
selector gives the converse: such a certificate exists exactly at centered rate zero.  Therefore
the corresponding global producer over all multiplicity-resolved Xi copies is equivalent to RH,
not an unconditional proof of it.  This closes the producer's neutral construction and its exact
no-go boundary without an RH premise, added axiom, or numerical computation.
-/

open Real Set MeasureTheory InformationTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Zero-indexed neutral source producer -/

/-- Convergent source law whose prime-depth-one occupation is exactly the neutral adaptive mass. -/
def sourceHorizontalPrimeAdaptiveNeutralParameters
    (p : Nat.Primes) : AbelianZetaConvergentParameters where
  sigma := Real.log ((p : ℝ) + 1) / Real.log (p : ℝ)
  tau := 0
  sigma_pos := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    have hlogp1 : 0 < Real.log ((p : ℝ) + 1) :=
      Real.log_pos (by linarith)
    positivity
  tau_nonneg := le_rfl
  firstDepth := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    have hloglt : Real.log (p : ℝ) < Real.log ((p : ℝ) + 1) :=
      Real.log_lt_log hp0 (by linarith)
    simpa only [add_zero] using
      (lt_div_iff₀ hlogp).2 (by simpa only [one_mul] using hloglt)

/-- Zero-indexed Boolean observer: occupancy of the retained prime at depth one. -/
def sourceHorizontalPrimeAdaptiveNeutralObserver
    (p : Nat.Primes) (A : AbelianZetaGroupClass) : Bool :=
  occupiedBool (A.configuration (p, 0))

/-- The chosen source slope makes prime-depth-one occupation exactly `1 / (p + 1)`. -/
theorem sourceHorizontalPrimeAdaptiveNeutralParameters_ratio
    (p : Nat.Primes) :
    (sourceHorizontalPrimeAdaptiveNeutralParameters p).toAbelianZetaParameters.ratio (p, 0) =
      1 / ((p : ℝ) + 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hlogp : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
  rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent]
  simp only [AbelianZetaMode.depth, sourceHorizontalPrimeAdaptiveNeutralParameters,
    zero_add, Nat.cast_one, one_mul, add_zero]
  rw [Real.rpow_def_of_pos hp0]
  have harg : Real.log (p : ℝ) *
      -(Real.log ((p : ℝ) + 1) / Real.log (p : ℝ)) =
      -Real.log ((p : ℝ) + 1) := by
    field_simp
  rw [harg, Real.exp_neg,
    Real.exp_log (by positivity : (0 : ℝ) < (p : ℝ) + 1)]
  simp only [one_div]

theorem sourceHorizontalPrimeAdaptiveOccupation_zero (p : Nat.Primes) :
    sourceHorizontalPrimeAdaptiveOccupation p 0 = 1 / ((p : ℝ) + 1) := by
  rw [sourceHorizontalPrimeAdaptiveOccupation]
  norm_num

/-- The neutral source observer has the exact adaptive Bernoulli law. -/
theorem classLaw_map_sourceHorizontalPrimeAdaptiveNeutralObserver
    (p : Nat.Primes) :
    (classLaw
        (sourceHorizontalPrimeAdaptiveNeutralParameters p).toAbelianZetaParameters).map
        (sourceHorizontalPrimeAdaptiveNeutralObserver p) =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p 0) := by
  have hmap := classLaw_map_modeCoordinate
    (sourceHorizontalPrimeAdaptiveNeutralParameters p) (p, 0)
  change (classLaw
      (sourceHorizontalPrimeAdaptiveNeutralParameters p).toAbelianZetaParameters).map
      (occupiedBool ∘ fun A => A.configuration (p, 0)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hmap,
    modeLaw_map_occupiedBool]
  congr 2
  ext
  rw [ratioUnit_coe, sourceHorizontalPrimeAdaptiveOccupationUnit_coe,
    sourceHorizontalPrimeAdaptiveNeutralParameters_ratio,
    sourceHorizontalPrimeAdaptiveOccupation_zero]

/-- Unconditional q-independent producer of the complete scale-orbit certificate at neutral
centered rate.  Source parameters and observer do not mention Xi or the scale index. -/
def sourceHorizontalPrimeAdaptiveNeutralClassLawScaleOrbitCertificate
    (p : Nat.Primes) (d : ℝ) :
    SourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate p d 0 where
  θP := sourceHorizontalPrimeAdaptiveNeutralParameters p
  θR := sourceHorizontalPrimeAdaptiveNeutralParameters p
  observer := fun _ => sourceHorizontalPrimeAdaptiveNeutralObserver p
  map_P := by
    intro n
    simpa using classLaw_map_sourceHorizontalPrimeAdaptiveNeutralObserver p
  map_R := by
    intro n
    simpa using classLaw_map_sourceHorizontalPrimeAdaptiveNeutralObserver p

/-! ## Exact local and global boundary -/

/-- Certificate existence is classified exactly: cofinal contiguity forbids every nonneutral
producer, while the preceding source construction supplies the neutral direction. -/
theorem sourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate_nonempty_iff
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d) :
    Nonempty (SourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate p d t) ↔
      t = 0 := by
  constructor
  · rintro ⟨C⟩
    exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_classLawScaleOrbitCertificate
      p hd C
  · rintro rfl
    exact ⟨sourceHorizontalPrimeAdaptiveNeutralClassLawScaleOrbitCertificate p d⟩

/-- Global multiplicity-resolved handoff target at a fixed retained prime and scale. -/
def SourceHorizontalAdaptiveFisherGlobalClassLawScaleOrbitProducer
    (p : Nat.Primes) (d : ℝ) : Prop :=
  ∀ q : XiZeroCopy,
    Nonempty (SourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate q p d)

/-- Exact global producer classification.  Consequently no unconditional off-center source
construction can inhabit this producer without simultaneously closing RH. -/
theorem sourceHorizontalAdaptiveFisherGlobalClassLawScaleOrbitProducer_iff_riemannHypothesis
    (p : Nat.Primes) {d : ℝ} (hd : 1 < d) :
    SourceHorizontalAdaptiveFisherGlobalClassLawScaleOrbitProducer p d ↔
      RiemannHypothesis := by
  constructor
  · intro hproducer
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro q
    exact sourceHorizontalXi_re_eq_half_of_adaptiveClassLawScaleOrbitCertificate
      (xiFirstZeroCopy q) p hd (hproducer (xiFirstZeroCopy q)).some
  · intro hRH q
    have hzero : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2
        (xi_divisor_support_re_eq_half_of_rh hRH q.1)
    change Nonempty
      (SourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate p d
        (primeDepthBVWoldXiCenteredRate q.1))
    rw [hzero]
    exact ⟨sourceHorizontalPrimeAdaptiveNeutralClassLawScaleOrbitCertificate p d⟩

/-- Closed dyadic specialization matching the cofinal-contiguity endpoint. -/
theorem sourceHorizontalAdaptiveFisherDyadicGlobalClassLawScaleOrbitProducer_iff_riemannHypothesis :
    SourceHorizontalAdaptiveFisherGlobalClassLawScaleOrbitProducer
        ⟨2, Nat.prime_two⟩ 2 ↔
      RiemannHypothesis := by
  exact sourceHorizontalAdaptiveFisherGlobalClassLawScaleOrbitProducer_iff_riemannHypothesis
    ⟨2, Nat.prime_two⟩ (by norm_num)

end

end RHTower
