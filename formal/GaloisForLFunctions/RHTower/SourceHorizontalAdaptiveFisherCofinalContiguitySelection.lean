import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherChiralitySelection

/-!
# Cofinal contiguity selection for adaptive source-horizontal observers

This module joins three previously separate corpus mechanisms:

* adaptive prime occupation records horizontal grade as an exact Bernoulli log-odds;
* global formation properness turns dilation into unbounded statistical work;
* convergent abelian class laws are mutually absolutely continuous.

The first conjectured selector asks for a finite, fixed full-source Jeffreys budget.  Data
processing then bounds every adaptive reporter on one dilation orbit, while its work diverges at
every nonzero grade.  A sharper pivot removes the quantitative budget: one-sided absolute
continuity already transports every sequence of vanishing events.  Reflected adaptive reporters
would make the same events tend to probability one in one orientation and zero in the other, so
the horizontal grade must vanish.

The final specialization uses actual abelian zeta class laws.  Their absolute continuity is
already source-derived; the remaining arithmetic producer is now exactly a coefficient-faithful
family of Boolean observers with the stated adaptive marginals.  No RH premise, added axiom, or
numerical computation occurs here.
-/

open Real Set MeasureTheory InformationTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Adaptive properness on a dilation orbit -/

theorem sourceHorizontalPrimeAdaptiveOccupation_strictMono (p : Nat.Primes) :
    StrictMono (sourceHorizontalPrimeAdaptiveOccupation p) := by
  intro a b hab
  rw [sourceHorizontalPrimeAdaptiveOccupation_eq_sigmoid,
    sourceHorizontalPrimeAdaptiveOccupation_eq_sigmoid]
  apply Real.sigmoid_strictMono
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  nlinarith

theorem sourceHorizontalPrimeAdaptiveOccupation_one (p : Nat.Primes) :
    sourceHorizontalPrimeAdaptiveOccupation p 1 = 1 / 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [sourceHorizontalPrimeAdaptiveOccupation, Real.rpow_one]
  field_simp [hp.ne']
  norm_num

theorem sourceHorizontalPrimeAdaptiveOccupation_neg_one (p : Nat.Primes) :
    sourceHorizontalPrimeAdaptiveOccupation p (-1) =
      1 / ((p : ℝ) ^ 2 + 1) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [sourceHorizontalPrimeAdaptiveOccupation, Real.rpow_neg_one]
  field_simp [hp.ne']

theorem sourceHorizontalPrimeAdaptiveOccupation_neg_one_le (p : Nat.Primes) :
    sourceHorizontalPrimeAdaptiveOccupation p (-1) ≤ 1 / 5 := by
  rw [sourceHorizontalPrimeAdaptiveOccupation_neg_one]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) ^ 2 + 1)]
  nlinarith [sq_nonneg ((p : ℝ) - 2)]

theorem sourceHorizontalPrimeAdaptiveOccupation_reflected_gap_lower
    {p : Nat.Primes} {u : ℝ} (hu : 1 ≤ u) :
    3 / 10 ≤ sourceHorizontalPrimeAdaptiveOccupation p u -
      sourceHorizontalPrimeAdaptiveOccupation p (-u) := by
  have hplus := (sourceHorizontalPrimeAdaptiveOccupation_strictMono p).monotone hu
  have hminus := (sourceHorizontalPrimeAdaptiveOccupation_strictMono p).monotone
    (by linarith : -u ≤ (-1 : ℝ))
  rw [sourceHorizontalPrimeAdaptiveOccupation_one] at hplus
  have hneg := sourceHorizontalPrimeAdaptiveOccupation_neg_one_le p
  linarith

theorem sourceHorizontalPrimeAdaptiveJeffreysWork_linear_lower
    {p : Nat.Primes} {u : ℝ} (hu : 1 ≤ u) :
    (3 / 5) * Real.log (p : ℝ) * u ≤
      sourceHorizontalPrimeAdaptiveJeffreysWork p u := by
  rw [sourceHorizontalPrimeAdaptiveJeffreysWork]
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hgap := sourceHorizontalPrimeAdaptiveOccupation_reflected_gap_lower
    (p := p) hu
  nlinarith [mul_le_mul_of_nonneg_left hgap
    (mul_nonneg (by linarith : 0 ≤ 2 * u) hlog.le)]

theorem tendsto_sourceHorizontalPrimeAdaptiveJeffreysWork_scale
    {p : Nat.Primes} {d t : ℝ} (hd : 1 < d) (ht : t ≠ 0) :
    Tendsto
      (fun n : ℕ => sourceHorizontalPrimeAdaptiveJeffreysWork p (d ^ n * |t|))
      atTop atTop := by
  have horbit : Tendsto (fun n : ℕ => d ^ n * |t|) atTop atTop :=
    scaleOrbit_tendsto hd (abs_pos.mpr ht)
  have hc : 0 < (3 / 5 : ℝ) * Real.log (p : ℝ) := by
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    positivity
  have hlower : Tendsto
      (fun n : ℕ => ((3 / 5 : ℝ) * Real.log (p : ℝ)) * (d ^ n * |t|))
      atTop atTop := Tendsto.const_mul_atTop hc horbit
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [horbit.eventually_ge_atTop 1] with n hn
  exact sourceHorizontalPrimeAdaptiveJeffreysWork_linear_lower hn

def SourceHorizontalPrimeAdaptiveBoundedScaleWork
    (p : Nat.Primes) (d t : ℝ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ,
    sourceHorizontalPrimeAdaptiveJeffreysWork p (d ^ n * |t|) ≤ B

theorem sourceHorizontalPrimeAdaptiveBoundedScaleWork_iff
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d) :
    SourceHorizontalPrimeAdaptiveBoundedScaleWork p d t ↔ t = 0 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra ht
    have htop := tendsto_sourceHorizontalPrimeAdaptiveJeffreysWork_scale
      (p := p) hd ht
    rcases (htop.eventually_gt_atTop B).exists with ⟨n, hn⟩
    linarith [hB n]
  · rintro rfl
    exact ⟨0, fun n => by simp [sourceHorizontalPrimeAdaptiveJeffreysWork]⟩

/-! ## Fixed finite source information -/

def sourceHorizontalFullJeffreys {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) : ℝ≥0∞ :=
  klDiv P R + klDiv R P

/-- A single finite source pair cannot report an unbounded reflected adaptive scale orbit. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fixedSourceFiniteJeffreys
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d)
    (hfinite : sourceHorizontalFullJeffreys P R ≠ ⊤)
    (q : ℕ → Ω → Bool) (hq : ∀ n, Measurable (q n))
    (hPobs : ∀ n, P.map (q n) =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (d ^ n * |t|)))
    (hRobs : ∀ n, R.map (q n) =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-(d ^ n * |t|)))) :
    t = 0 := by
  apply (sourceHorizontalPrimeAdaptiveBoundedScaleWork_iff p hd).mp
  refine ⟨(sourceHorizontalFullJeffreys P R).toReal, fun n => ?_⟩
  let u : ℝ := d ^ n * |t|
  have hle : bernoulliJeffreys
      (sourceHorizontalPrimeAdaptiveOccupationUnit p u)
      (sourceHorizontalPrimeAdaptiveOccupationUnit p (-u)) ≤
      sourceHorizontalFullJeffreys P R := by
    dsimp [u]
    rw [bernoulliJeffreys, sourceHorizontalFullJeffreys, ← hPobs n, ← hRobs n]
    exact add_le_add
      (klDiv_map_le P R (q := q n) (hq n))
      (klDiv_map_le R P (q := q n) (hq n))
  have hreal := ENNReal.toReal_mono hfinite hle
  rw [bernoulliJeffreys_toReal _ _
      (sourceHorizontalPrimeAdaptiveOccupation_pos p u)
      (sourceHorizontalPrimeAdaptiveOccupation_lt_one p u)
      (sourceHorizontalPrimeAdaptiveOccupation_pos p (-u))
      (sourceHorizontalPrimeAdaptiveOccupation_lt_one p (-u)),
    bernoulliJeffreysReal_sourceHorizontalPrimeAdaptive_eq] at hreal
  exact hreal

/-! ## Pivot: qualitative contiguity is sufficient -/

theorem tendsto_sourceHorizontalPrimeAdaptiveOccupation_scale_one
    {p : Nat.Primes} {d t : ℝ} (hd : 1 < d) (ht : t ≠ 0) :
    Tendsto
      (fun n : ℕ => sourceHorizontalPrimeAdaptiveOccupation p (d ^ n * |t|))
      atTop (𝓝 1) := by
  have horbit : Tendsto (fun n : ℕ => d ^ n * |t|) atTop atTop :=
    scaleOrbit_tendsto hd (abs_pos.mpr ht)
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have harg : Tendsto
      (fun n : ℕ => (d ^ n * |t| - 1) * Real.log (p : ℝ)) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (-Real.log (p : ℝ))
      (horbit.const_mul_atTop hlog) using 1
    funext n
    ring
  simpa only [sourceHorizontalPrimeAdaptiveOccupation_eq_sigmoid, Function.comp_def] using
    Real.tendsto_sigmoid_atTop.comp harg

theorem tendsto_sourceHorizontalPrimeAdaptiveOccupation_reflectedScale_zero
    {p : Nat.Primes} {d t : ℝ} (hd : 1 < d) (ht : t ≠ 0) :
    Tendsto
      (fun n : ℕ => sourceHorizontalPrimeAdaptiveOccupation p (-(d ^ n * |t|)))
      atTop (𝓝 0) := by
  have horbit : Tendsto (fun n : ℕ => d ^ n * |t|) atTop atTop :=
    scaleOrbit_tendsto hd (abs_pos.mpr ht)
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have harg : Tendsto
      (fun n : ℕ => (-(d ^ n * |t|) - 1) * Real.log (p : ℝ)) atTop atBot := by
    convert tendsto_atBot_add_const_right atTop (-Real.log (p : ℝ))
      (horbit.const_mul_atTop_of_neg (by linarith : -Real.log (p : ℝ) < 0)) using 1
    funext n
    ring
  simpa only [sourceHorizontalPrimeAdaptiveOccupation_eq_sigmoid, Function.comp_def] using
    Real.tendsto_sigmoid_atBot.comp harg

/-- Uniform absolute continuity for finite measures: events vanishing under the reference source
also vanish under the dominated source, even when the events vary cofinally. -/
theorem tendsto_measure_zero_of_absolutelyContinuous_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    (hPR : P ≪ R) {s : ℕ → Set Ω}
    (hR : Tendsto (fun n => R (s n)) atTop (𝓝 0)) :
    Tendsto (fun n => P (s n)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => P.real (s n)) atTop (𝓝 0) := by
    have h := (Measure.integrable_toReal_rnDeriv
      (μ := P) (ν := R)).tendsto_setIntegral_nhds_zero hR
    simpa only [Measure.setIntegral_toReal_rnDeriv hPR] using h
  apply (ENNReal.tendsto_toReal_zero_iff
    (fun n => measure_ne_top P (s n))).mp
  simpa only [Measure.real] using hreal

/-- Contiguous finite source laws cannot admit asymptotically perfect orientation tests. -/
theorem not_cofinalObserverSeparation_of_absolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    (hPR : P ≪ R) (s : ℕ → Set Ω) :
    ¬ (Tendsto (fun n => P (s n)) atTop (𝓝 1) ∧
      Tendsto (fun n => R (s n)) atTop (𝓝 0)) := by
  rintro ⟨hPone, hRzero⟩
  have hPzero := tendsto_measure_zero_of_absolutelyContinuous_finite
    P R hPR hRzero
  have : (0 : ℝ≥0∞) = 1 := tendsto_nhds_unique hPzero hPone
  norm_num at this

/-- Sharper selector: no KL finiteness or conditional-sufficiency premise is needed.  One-sided
absolute continuity of the fixed source pair already forces neutral horizontal grade. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fixedSourceContiguity
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d) (hPR : P ≪ R)
    (q : ℕ → Ω → Bool) (hq : ∀ n, Measurable (q n))
    (hPobs : ∀ n, P.map (q n) =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (d ^ n * |t|)))
    (hRobs : ∀ n, R.map (q n) =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-(d ^ n * |t|)))) :
    t = 0 := by
  by_contra ht
  let s : ℕ → Set Ω := fun n => (q n) ⁻¹' {true}
  have hPmeasure (n : ℕ) :
      (P (s n)).toReal = sourceHorizontalPrimeAdaptiveOccupation p (d ^ n * |t|) := by
    have hmap := congrArg (fun μ : Measure Bool => (μ {true}).toReal) (hPobs n)
    rw [Measure.map_apply (hq n) (MeasurableSet.singleton true)] at hmap
    rw [bernoulliMeasure_apply_of_mem_of_notMem
      (sourceHorizontalPrimeAdaptiveOccupationUnit p (d ^ n * |t|))
      (MeasurableSet.singleton true) (by simp) (by simp)] at hmap
    simpa only [ENNReal.coe_toReal, unitInterval.coe_toNNReal,
      sourceHorizontalPrimeAdaptiveOccupationUnit_coe, s] using hmap
  have hRmeasure (n : ℕ) :
      (R (s n)).toReal = sourceHorizontalPrimeAdaptiveOccupation p (-(d ^ n * |t|)) := by
    have hmap := congrArg (fun μ : Measure Bool => (μ {true}).toReal) (hRobs n)
    rw [Measure.map_apply (hq n) (MeasurableSet.singleton true)] at hmap
    rw [bernoulliMeasure_apply_of_mem_of_notMem
      (sourceHorizontalPrimeAdaptiveOccupationUnit p (-(d ^ n * |t|)))
      (MeasurableSet.singleton true) (by simp) (by simp)] at hmap
    simpa only [ENNReal.coe_toReal, unitInterval.coe_toNNReal,
      sourceHorizontalPrimeAdaptiveOccupationUnit_coe, s] using hmap
  have hRzeroReal : Tendsto (fun n => (R (s n)).toReal) atTop (𝓝 0) :=
    (tendsto_sourceHorizontalPrimeAdaptiveOccupation_reflectedScale_zero
      (p := p) hd ht).congr'
        (Filter.Eventually.of_forall fun n => (hRmeasure n).symm)
  have hRzero : Tendsto (fun n => R (s n)) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => measure_ne_top R (s n))).mp hRzeroReal
  have hPzero := tendsto_measure_zero_of_absolutelyContinuous_finite
    P R hPR hRzero
  have hPzeroReal : Tendsto (fun n => (P (s n)).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun n => measure_ne_top P (s n))).mpr hPzero
  have hPoneReal : Tendsto (fun n => (P (s n)).toReal) atTop (𝓝 1) :=
    (tendsto_sourceHorizontalPrimeAdaptiveOccupation_scale_one
      (p := p) hd ht).congr'
        (Filter.Eventually.of_forall fun n => (hPmeasure n).symm)
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hPzeroReal hPoneReal
  norm_num at this

/-! ## Actual abelian source and Xi endpoint -/

/-- All quantitative source hypotheses disappear for convergent abelian class laws: their
source-derived mutual absolute continuity supplies contiguity automatically. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_abelianClassLawScaleObservers
    (θP θR : AbelianZetaConvergentParameters)
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d)
    (q : ℕ → AbelianZetaGroupClass → Bool)
    (hPobs : ∀ n, (classLaw θP.toAbelianZetaParameters).map (q n) =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (d ^ n * |t|)))
    (hRobs : ∀ n, (classLaw θR.toAbelianZetaParameters).map (q n) =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-(d ^ n * |t|)))) :
    t = 0 := by
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fixedSourceContiguity
    (classLaw θP.toAbelianZetaParameters) (classLaw θR.toAbelianZetaParameters)
    p hd (classLaw_absolutelyContinuous θR θP) q (fun _ => by fun_prop) hPobs hRobs

universe u

/-- Concrete source certificate.  Unlike earlier reversal certificates, source compatibility is
not an extra field: both laws are actual convergent abelian zeta class laws and are therefore
mutually absolutely continuous by an existing arithmetic theorem. -/
structure SourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate
    (p : Nat.Primes) (d t : ℝ) where
  θP : AbelianZetaConvergentParameters
  θR : AbelianZetaConvergentParameters
  observer : ℕ → AbelianZetaGroupClass → Bool
  map_P : ∀ n, (classLaw θP.toAbelianZetaParameters).map (observer n) =
    Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (d ^ n * |t|))
  map_R : ∀ n, (classLaw θR.toAbelianZetaParameters).map (observer n) =
    Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-(d ^ n * |t|)))

theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_classLawScaleOrbitCertificate
    (p : Nat.Primes) {d t : ℝ} (hd : 1 < d)
    (C : SourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate p d t) :
    t = 0 := by
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_abelianClassLawScaleObservers
    C.θP C.θR p hd C.observer C.map_P C.map_R

abbrev SourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate
    (q : XiZeroCopy) (p : Nat.Primes) (d : ℝ) :=
  SourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate p d
    (primeDepthBVWoldXiCenteredRate q.1)

theorem sourceHorizontalXi_re_eq_half_of_adaptiveClassLawScaleOrbitCertificate
    (q : XiZeroCopy) (p : Nat.Primes) {d : ℝ} (hd : 1 < d)
    (C : SourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate q p d) :
    (q.1 : ℂ).re = 1 / 2 := by
  rw [← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_classLawScaleOrbitCertificate
    p hd C

/-- **Cofinal-contiguity Frankenstein endpoint.**  A coefficient-faithful adaptive scale-observer
orbit on two actual abelian class laws, for every multiplicity-resolved Xi copy, proves RH. -/
theorem riemannHypothesis_of_sourceHorizontalXi_adaptiveClassLawScaleOrbitCertificates
    (hcert : ∀ q : XiZeroCopy,
      SourceHorizontalXiAdaptiveClassLawScaleOrbitCertificate
        q ⟨2, Nat.prime_two⟩ 2) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  intro q
  exact sourceHorizontalXi_re_eq_half_of_adaptiveClassLawScaleOrbitCertificate
    (xiFirstZeroCopy q) ⟨2, Nat.prime_two⟩ (by norm_num)
      (hcert (xiFirstZeroCopy q))

end

end RHTower
