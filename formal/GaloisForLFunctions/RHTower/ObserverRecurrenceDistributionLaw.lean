import GaloisForLFunctions.RHTower.ObserverTemporalDimensionLaw
import GaloisForLFunctions.HTGeometry.ConvolutionAtomBounds
import GaloisForLFunctions.HTGeometry.CarriedConclusion
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Complete observer recurrence distribution

For an arbitrary probability energy spectrum, every power of survival
fidelity is itself a characteristic function: its spectral law is the
corresponding convolution power of the energy-difference measure.  Symmetric
time averaging therefore identifies every long-time fidelity moment with an
exact additive collision probability.

Polynomial approximation on `[0,1]` upgrades the moment hierarchy to a
complete distribution theorem: every continuous statistic of the fidelity
has a long-time mean.  No finiteness, discreteness, absolute continuity, or
finite-dimensional hypothesis is imposed.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal MeasureTheory Topology Polynomial

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Symmetric-window normalized `n`-th fidelity moment. -/
def spectralReturnMomentMean
    (mu : Measure ℝ) (n : ℕ) (r : ℝ) : ℂ :=
  ((2 * r : ℝ) : ℂ)⁻¹ *
    ∫ t in -r..r,
      ((Complex.normSq (charFun mu t) ^ n : ℝ) : ℂ)

/-- Real form of the symmetric-window normalized fidelity moment. -/
def spectralReturnMomentMeanReal
    (mu : Measure ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (2 * r)⁻¹ *
    ∫ t in -r..r, Complex.normSq (charFun mu t) ^ n

lemma spectralReturnMomentMean_eq_ofReal
    (mu : Measure ℝ) (n : ℕ) (r : ℝ) :
    spectralReturnMomentMean mu n r =
      (spectralReturnMomentMeanReal mu n r : ℂ) := by
  rw [spectralReturnMomentMean, spectralReturnMomentMeanReal,
    intervalIntegral.integral_ofReal]
  push_cast
  rfl

/-- Characteristic function of an `n`-fold convolution power. -/
lemma charFun_convPow
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (n : ℕ) (t : ℝ) :
    charFun (convPow nu n) t = charFun nu t ^ n := by
  induction n with
  | zero =>
      simp [convPow, charFun_apply_real]
  | succ n ih =>
      haveI : IsProbabilityMeasure (convPow nu n) :=
        isProbabilityMeasure_convPow nu n
      rw [convPow, MeasureTheory.charFun_conv, ih, pow_succ']

/-- Every fidelity power is the characteristic function of the corresponding
convolution power of the projective energy-gap law. -/
lemma charFun_convPow_spectralDifferenceMeasure
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) (t : ℝ) :
    charFun (convPow (spectralDifferenceMeasure mu) n) t =
      (Complex.normSq (charFun mu t) : ℂ) ^ n := by
  rw [charFun_convPow, charFun_spectralDifferenceMeasure]

/-- Sampled `n`-th survival-fidelity moment under an arbitrary probability
law of clock readings. -/
def clockSampledSpectralReturnMoment
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) (n : ℕ) : ℂ :=
  ∫ t,
    ((Complex.normSq (charFun mu t) ^ n : ℝ) : ℂ)
    ∂(clockLaw : Measure ℝ)

/-- Integrating the characteristic function of one real probability law
against another is symmetric.  This is the Fubini bridge exchanging clock
and spectral-collision laws. -/
lemma integral_charFun_probabilityMeasure_comm
    (mu nu : ProbabilityMeasure ℝ) :
    (∫ t, charFun (nu : Measure ℝ) t
        ∂(mu : Measure ℝ)) =
      ∫ x, charFun (mu : Measure ℝ) x
        ∂(nu : Measure ℝ) := by
  have hintegrable :
      Integrable
        (Function.uncurry
          (fun t x : ℝ =>
            Complex.exp
              ((t : ℂ) * (x : ℂ) * Complex.I)))
        ((mu : Measure ℝ).prod (nu : Measure ℝ)) := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact
        (by
          fun_prop :
          Continuous
            (Function.uncurry
              (fun t x : ℝ =>
                Complex.exp
                  ((t : ℂ) * (x : ℂ) *
                    Complex.I)))).aestronglyMeasurable
    · filter_upwards with z
      change
        ‖Complex.exp
          ((z.1 : ℂ) * (z.2 : ℂ) *
            Complex.I)‖ ≤ 1
      rw [show
        (z.1 : ℂ) * (z.2 : ℂ) =
          ((z.1 * z.2 : ℝ) : ℂ) by
            push_cast
            ring]
      rw [Complex.norm_exp_ofReal_mul_I]
  calc
    (∫ t, charFun (nu : Measure ℝ) t
        ∂(mu : Measure ℝ)) =
        ∫ t, ∫ x,
          Complex.exp
            ((t : ℂ) * (x : ℂ) * Complex.I)
          ∂(nu : Measure ℝ) ∂(mu : Measure ℝ) := by
      simp_rw [charFun_apply_real]
    _ = ∫ x, ∫ t,
          Complex.exp
            ((t : ℂ) * (x : ℂ) * Complex.I)
          ∂(mu : Measure ℝ) ∂(nu : Measure ℝ) :=
      integral_integral_swap hintegrable
    _ = ∫ x, charFun (mu : Measure ℝ) x
          ∂(nu : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [charFun_apply_real]
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      simp [mul_comm]

/-! ### Reciprocal system--clock replica hierarchy -/

/-- Two-axis harmonic replica pairing of arbitrary real probability laws.
The first index convolves the sampling law; the second replicates the
Fourier reporter. -/
def harmonicReplicaPairing
    (mu nu : ProbabilityMeasure ℝ) (m n : ℕ) : ℂ :=
  ∫ t, charFun (nu : Measure ℝ) t ^ n
    ∂convPow (mu : Measure ℝ) m

/-- **Replica reciprocity.** Exchanging the two probability laws and their
replica indices leaves the complete two-axis harmonic hierarchy unchanged. -/
theorem harmonicReplicaPairing_swap
    (mu nu : ProbabilityMeasure ℝ) (m n : ℕ) :
    harmonicReplicaPairing mu nu m n =
      harmonicReplicaPairing nu mu n m := by
  let muReplica : ProbabilityMeasure ℝ :=
    ⟨convPow (mu : Measure ℝ) m,
      isProbabilityMeasure_convPow (mu : Measure ℝ) m⟩
  let nuReplica : ProbabilityMeasure ℝ :=
    ⟨convPow (nu : Measure ℝ) n,
      isProbabilityMeasure_convPow (nu : Measure ℝ) n⟩
  have hcomm :=
    integral_charFun_probabilityMeasure_comm muReplica nuReplica
  have hmuReplica :
      (muReplica : Measure ℝ) =
        convPow (mu : Measure ℝ) m :=
    rfl
  have hnuReplica :
      (nuReplica : Measure ℝ) =
        convPow (nu : Measure ℝ) n :=
    rfl
  rw [hmuReplica, hnuReplica] at hcomm
  have hmuChar (x : ℝ) :
      charFun (convPow (mu : Measure ℝ) m) x =
        charFun (mu : Measure ℝ) x ^ m :=
    charFun_convPow (mu : Measure ℝ) m x
  have hnuChar (x : ℝ) :
      charFun (convPow (nu : Measure ℝ) n) x =
        charFun (nu : Measure ℝ) x ^ n :=
    charFun_convPow (nu : Measure ℝ) n x
  simp_rw [hmuChar, hnuChar] at hcomm
  unfold harmonicReplicaPairing
  exact hcomm

/-- Canonical probability law of visible energy gaps of a probability
spectrum. -/
def spectralGapProbabilityLaw
    (mu : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨spectralDifferenceMeasure (mu : Measure ℝ), inferInstance⟩

@[simp]
lemma spectralGapProbabilityLaw_toMeasure
    (mu : ProbabilityMeasure ℝ) :
    (spectralGapProbabilityLaw mu : Measure ℝ) =
      spectralDifferenceMeasure (mu : Measure ℝ) :=
  rfl

/-- Two-axis mutual-recurrence hierarchy of two probability spectra. Each
spectrum supplies the other's visible gap clock. -/
def mutualSpectralReplicaRecurrence
    (mu nu : ProbabilityMeasure ℝ) (m n : ℕ) : ℂ :=
  harmonicReplicaPairing
    (spectralGapProbabilityLaw mu)
    (spectralGapProbabilityLaw nu) m n

/-- The mutual hierarchy is an actual hierarchy of survival-fidelity powers
sampled against convolved visible gap laws. -/
theorem mutualSpectralReplicaRecurrence_eq
    (mu nu : ProbabilityMeasure ℝ) (m n : ℕ) :
    mutualSpectralReplicaRecurrence mu nu m n =
      ∫ t, (Complex.normSq
          (charFun (nu : Measure ℝ) t) : ℂ) ^ n
        ∂convPow
          (spectralDifferenceMeasure (mu : Measure ℝ)) m := by
  unfold mutualSpectralReplicaRecurrence harmonicReplicaPairing
  rw [spectralGapProbabilityLaw_toMeasure,
    spectralGapProbabilityLaw_toMeasure]
  simp_rw [charFun_spectralDifferenceMeasure]

/-- **Mutual recurrence reciprocity.** At every pair of replica orders,
exchanging which spectrum is called “system” and which is called “clock”
leaves the relational recurrence statistic invariant, provided the replica
orders are exchanged with them. -/
theorem mutualSpectralReplicaRecurrence_swap
    (mu nu : ProbabilityMeasure ℝ) (m n : ℕ) :
    mutualSpectralReplicaRecurrence mu nu m n =
      mutualSpectralReplicaRecurrence nu mu n m :=
  harmonicReplicaPairing_swap
    (spectralGapProbabilityLaw mu)
    (spectralGapProbabilityLaw nu) m n

/-- **Universal system--clock--probe recurrence law.** For every probability
energy spectrum, every probability law of clock readings and every moment
order, the sampled survival-fidelity moment is exactly the clock
characteristic function averaged over the corresponding additive
energy-gap collision law. -/
theorem clockSampledSpectralReturnMoment_eq_clockTransferCollision
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) :
    clockSampledSpectralReturnMoment clockLaw mu n =
      ∫ x, charFun (clockLaw : Measure ℝ) x
        ∂convPow (spectralDifferenceMeasure mu) n := by
  let collisionLaw : ProbabilityMeasure ℝ :=
    ⟨convPow (spectralDifferenceMeasure mu) n,
      isProbabilityMeasure_convPow
        (spectralDifferenceMeasure mu) n⟩
  rw [clockSampledSpectralReturnMoment]
  have hcomm :=
    integral_charFun_probabilityMeasure_comm
      clockLaw collisionLaw
  rw [show
    (collisionLaw : Measure ℝ) =
      convPow (spectralDifferenceMeasure mu) n by rfl] at hcomm
  rw [← hcomm]
  apply integral_congr_ae
  filter_upwards with t
  symm
  rw [charFun_convPow_spectralDifferenceMeasure]
  norm_cast

/-- At every positive window radius, the `n`-th fidelity moment is the sinc
average of the `n`-fold additive gap-collision law. -/
lemma spectralReturnMomentMean_eq_integral_sinc
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) {r : ℝ} (hr : 0 < r) :
    spectralReturnMomentMean mu n r =
      ∫ x, (Real.sinc (r * x) : ℂ)
        ∂convPow (spectralDifferenceMeasure mu) n := by
  haveI : IsProbabilityMeasure
      (convPow (spectralDifferenceMeasure mu) n) :=
    isProbabilityMeasure_convPow (spectralDifferenceMeasure mu) n
  rw [spectralReturnMomentMean]
  have hchar (t : ℝ) :
      (((Complex.normSq (charFun mu t) ^ n : ℝ) : ℂ)) =
        charFun (convPow (spectralDifferenceMeasure mu) n) t := by
    rw [charFun_convPow_spectralDifferenceMeasure]
    norm_cast
  simp_rw [hchar]
  rw [integral_charFun_Icc hr]
  have hne : ((2 * r : ℝ) : ℂ) ≠ 0 := by
    norm_cast
    positivity
  rw [integral_complex_ofReal]
  have hcast : (2 : ℂ) * (r : ℂ) = ((2 * r : ℝ) : ℂ) := by
    norm_num
  rw [hcast, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- Universal all-order recurrence law.  The long-time `n`-th fidelity
moment is exactly the probability that `n` independent visible energy gaps
sum to zero. -/
theorem spectralReturnMomentMean_tendsto_collisionHierarchy
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    Tendsto (spectralReturnMomentMean mu n) atTop
      (𝓝 (((convPow (spectralDifferenceMeasure mu) n).real {0} : ℝ) : ℂ)) := by
  haveI : IsProbabilityMeasure
      (convPow (spectralDifferenceMeasure mu) n) :=
    isProbabilityMeasure_convPow (spectralDifferenceMeasure mu) n
  have h :=
    tendsto_integral_complex_sinc_mul
      (nu := convPow (spectralDifferenceMeasure mu) n)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (spectralReturnMomentMean_eq_integral_sinc mu n hr).symm

/-- Real form of the universal all-order recurrence law. -/
theorem spectralReturnMomentMeanReal_tendsto_collisionHierarchy
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    Tendsto (spectralReturnMomentMeanReal mu n) atTop
      (𝓝 ((convPow (spectralDifferenceMeasure mu) n).real {0})) := by
  have h := (Complex.continuous_re.tendsto
    (((convPow (spectralDifferenceMeasure mu) n).real {0} : ℝ) : ℂ)).comp
      (spectralReturnMomentMean_tendsto_collisionHierarchy mu n)
  have heq :
      Complex.re ∘ spectralReturnMomentMean mu n =
        spectralReturnMomentMeanReal mu n := by
    funext r
    rw [Function.comp_apply, spectralReturnMomentMean_eq_ofReal,
      Complex.ofReal_re]
  rwa [heq] at h

/-- Convolution with an atomless right factor cannot create atoms. -/
lemma noAtoms_conv_of_right_noAtoms
    (mu nu : Measure ℝ) [NullSingletonClass nu] :
    NullSingletonClass (mu ∗ nu) :=
  nullSingletonClass_conv_of_right mu nu

/-- Every positive convolution power of an atomless real measure is
atomless. -/
lemma noAtoms_convPow_of_noAtoms
    (nu : Measure ℝ) [SFinite nu] [NullSingletonClass nu]
    {n : ℕ} (hn : 0 < n) :
    NullSingletonClass (convPow nu n) :=
  nullSingletonClass_convPow nu hn

/-- The difference of two independent samples from an atomless measure is
atomless. -/
lemma noAtoms_spectralDifferenceMeasure_of_noAtoms
    (mu : Measure ℝ) [NullSingletonClass mu] :
    NullSingletonClass (spectralDifferenceMeasure mu) := by
  rw [spectralDifferenceMeasure]
  apply noAtoms_map_prod_of_countable_fibers
    mu mu (fun p : ℝ × ℝ ↦ p.1 - p.2) (by fun_prop)
  intro a gap
  apply (Set.finite_singleton (a - gap)).countable.mono
  intro b hb
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hb ⊢
  linarith

/-- In the atomless phase every positive-order additive collision moment is
zero. -/
theorem spectralCollisionHierarchy_eq_zero_of_noAtoms
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    {n : ℕ} (hn : 0 < n) :
    (convPow (spectralDifferenceMeasure mu) n).real {0} = 0 := by
  letI : NullSingletonClass (spectralDifferenceMeasure mu) :=
    noAtoms_spectralDifferenceMeasure_of_noAtoms mu
  letI : NullSingletonClass (convPow (spectralDifferenceMeasure mu) n) :=
    noAtoms_convPow_of_noAtoms (spectralDifferenceMeasure mu) hn
  rw [Measure.real, measure_singleton]
  simp

/-- Fidelity always belongs to the compact unit interval. -/
lemma normSq_charFun_mem_Icc
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (t : ℝ) :
    Complex.normSq (charFun mu t) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Complex.normSq_nonneg _
  · rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (charFun mu t),
      norm_charFun_le_one (μ := mu) t]

/-- Complete probability law of survival fidelity when the readout time is
sampled from an arbitrary probability clock. -/
def clockSampledSpectralReturnProbabilityMeasure
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map clockLaw
    (f := fun t => Complex.normSq (charFun mu t))
    (by
      exact
        (Complex.continuous_normSq.comp
          continuous_charFun).aemeasurable)

/-- Every arbitrary-clock return law is carried by the fidelity interval
`[0,1]`. -/
lemma clockSampledSpectralReturnProbabilityMeasure_compl_Icc
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (clockSampledSpectralReturnProbabilityMeasure
      clockLaw mu : Measure ℝ) (Icc 0 1)ᶜ = 0 := by
  rw [clockSampledSpectralReturnProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply_of_aemeasurable
    (f := fun t => Complex.normSq (charFun mu t))
    (Complex.continuous_normSq.comp
      continuous_charFun).aemeasurable
    (measurableSet_Icc.compl)]
  have hpreimage :
      (fun t => Complex.normSq (charFun mu t)) ⁻¹'
          (Icc 0 1)ᶜ = ∅ := by
    ext t
    simp only [mem_preimage, mem_compl_iff, mem_Icc,
      mem_empty_iff_false, iff_false, not_and_or]
    push Not
    exact normSq_charFun_mem_Icc mu t
  rw [hpreimage, measure_empty]

/-- Arbitrary-clock sampled recurrence moments are the real power moments
of the complete return law. -/
lemma clockSampledSpectralReturnMoment_eq_ofReal_integral_pow
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) :
    clockSampledSpectralReturnMoment clockLaw mu n =
      ((∫ x : ℝ, x ^ n
        ∂(clockSampledSpectralReturnProbabilityMeasure
          clockLaw mu : Measure ℝ) : ℝ) : ℂ) := by
  rw [clockSampledSpectralReturnProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (φ := fun t => Complex.normSq (charFun mu t))
    (Complex.continuous_normSq.comp
      continuous_charFun).aemeasurable
    (by fun_prop)]
  rw [clockSampledSpectralReturnMoment]
  exact integral_ofReal (𝕜 := ℂ)

/-- Real form of the arbitrary-clock return-moment identity. -/
lemma integral_pow_clockSampledSpectralReturnProbabilityMeasure
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) :
    (∫ x, x ^ n
        ∂(clockSampledSpectralReturnProbabilityMeasure
          clockLaw mu : Measure ℝ)) =
      (clockSampledSpectralReturnMoment clockLaw mu n).re := by
  have h :=
    congrArg Complex.re
      (clockSampledSpectralReturnMoment_eq_ofReal_integral_pow
        clockLaw mu n)
  simpa using h.symm

/-- **Complete arbitrary-clock recurrence classification.** Two
system--clock pairs have exactly the same probability law of survival
fidelity if and only if every clock--collision moment agrees. -/
theorem clockSampledSpectralReturnProbabilityMeasure_eq_iff_moments
    (clockLaw₁ clockLaw₂ : ProbabilityMeasure ℝ)
    (mu₁ mu₂ : Measure ℝ)
    [IsProbabilityMeasure mu₁] [IsProbabilityMeasure mu₂] :
    (clockSampledSpectralReturnProbabilityMeasure
        clockLaw₁ mu₁ : Measure ℝ) =
        (clockSampledSpectralReturnProbabilityMeasure
          clockLaw₂ mu₂ : Measure ℝ) ↔
      ∀ n : ℕ,
        clockSampledSpectralReturnMoment clockLaw₁ mu₁ n =
          clockSampledSpectralReturnMoment clockLaw₂ mu₂ n := by
  constructor
  · intro hmeasure n
    rw [clockSampledSpectralReturnMoment_eq_ofReal_integral_pow,
      hmeasure,
      ← clockSampledSpectralReturnMoment_eq_ofReal_integral_pow]
  · intro hmoments
    let s : ℕ → ℝ :=
      fun n =>
        (clockSampledSpectralReturnMoment
          clockLaw₁ mu₁ n).re
    apply HTGeometry.measure_eq_of_moments_eq_of_one_carried
      (s := s) (c := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ))
      (by norm_num)
    · convert
        clockSampledSpectralReturnProbabilityMeasure_compl_Icc
          clockLaw₁ mu₁ using 1
      all_goals norm_num
    · intro n
      exact
        (integral_pow_clockSampledSpectralReturnProbabilityMeasure
          clockLaw₁ mu₁ n).symm
    · intro n
      rw [clockSampledSpectralReturnProbabilityMeasure,
        ProbabilityMeasure.toMeasure_map]
      apply (integrable_map_measure
        (f := fun t => Complex.normSq (charFun mu₁ t))
        (g := fun x : ℝ => x ^ n)
        (by fun_prop)
        (Complex.continuous_normSq.comp
          continuous_charFun).aemeasurable).mpr
      apply (integrable_const (1 : ℝ)).mono'
      · fun_prop
      ·
        filter_upwards with t
        have ht := normSq_charFun_mem_Icc mu₁ t
        simp only [mem_Icc] at ht
        change |Complex.normSq (charFun mu₁ t) ^ n| ≤ 1
        rw [abs_of_nonneg (pow_nonneg ht.1 n)]
        exact pow_le_one₀ ht.1 ht.2
    · intro n
      change
        (clockSampledSpectralReturnMoment
          clockLaw₁ mu₁ n).re =
            ∫ x, x ^ n
              ∂(clockSampledSpectralReturnProbabilityMeasure
                clockLaw₂ mu₂ : Measure ℝ)
      rw [hmoments n, ←
        integral_pow_clockSampledSpectralReturnProbabilityMeasure
          clockLaw₂ mu₂ n]
    · intro n
      rw [clockSampledSpectralReturnProbabilityMeasure,
        ProbabilityMeasure.toMeasure_map]
      apply (integrable_map_measure
        (f := fun t => Complex.normSq (charFun mu₂ t))
        (g := fun x : ℝ => x ^ n)
        (by fun_prop)
        (Complex.continuous_normSq.comp
          continuous_charFun).aemeasurable).mpr
      apply (integrable_const (1 : ℝ)).mono'
      · fun_prop
      ·
        filter_upwards with t
        have ht := normSq_charFun_mem_Icc mu₂ t
        simp only [mem_Icc] at ht
        change |Complex.normSq (charFun mu₂ t) ^ n| ≤ 1
        rw [abs_of_nonneg (pow_nonneg ht.1 n)]
        exact pow_le_one₀ ht.1 ht.2

/-! ### The maximal orientation quotient of recurrence -/

/-- Reflection of a clock-reading law through the origin. -/
def reflectedClockLaw (clockLaw : ProbabilityMeasure ℝ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map clockLaw
    (f := fun t : ℝ => -t) (by fun_prop)

/-- Clock reflection conjugates its characteristic function. -/
lemma charFun_reflectedClockLaw
    (clockLaw : ProbabilityMeasure ℝ) (x : ℝ) :
    charFun (reflectedClockLaw clockLaw : Measure ℝ) x =
      charFun (clockLaw : Measure ℝ) (-x) := by
  rw [reflectedClockLaw, ProbabilityMeasure.toMeasure_map,
    show (fun t : ℝ => -t) = fun t : ℝ => (-1) * t by
      funext t
      ring,
    charFun_map_mul]
  ring_nf

/-- Survival fidelity is even in the clock reading for every probability
energy spectrum. -/
lemma normSq_charFun_neg
    (mu : Measure ℝ) (t : ℝ) :
    Complex.normSq (charFun mu (-t)) =
      Complex.normSq (charFun mu t) := by
  rw [charFun_neg, Complex.normSq_conj]

/-- Every sampled survival-fidelity moment is invariant under reversal of
the entire clock law. -/
lemma clockSampledSpectralReturnMoment_reflected
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) :
    clockSampledSpectralReturnMoment
        (reflectedClockLaw clockLaw) mu n =
      clockSampledSpectralReturnMoment clockLaw mu n := by
  rw [clockSampledSpectralReturnMoment, reflectedClockLaw,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  filter_upwards with t
  rw [normSq_charFun_neg]

/-- The complete return-fidelity law is invariant under reversal of the
entire clock law. -/
theorem clockSampledSpectralReturnProbabilityMeasure_reflected
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    (clockSampledSpectralReturnProbabilityMeasure
        (reflectedClockLaw clockLaw) mu : Measure ℝ) =
      (clockSampledSpectralReturnProbabilityMeasure
        clockLaw mu : Measure ℝ) := by
  apply
    (clockSampledSpectralReturnProbabilityMeasure_eq_iff_moments
      (reflectedClockLaw clockLaw) clockLaw mu mu).2
  intro n
  exact clockSampledSpectralReturnMoment_reflected clockLaw mu n

/-- The orientation quotient of a clock law: the equal mixture of the law
and its reflection.  This is the maximal clock information accessible to
survival-return experiments. -/
def clockOrientationQuotient (clockLaw : ProbabilityMeasure ℝ) :
    Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ •
    ((clockLaw : Measure ℝ) +
      (reflectedClockLaw clockLaw : Measure ℝ))

instance clockOrientationQuotient.instIsProbabilityMeasure
    (clockLaw : ProbabilityMeasure ℝ) :
    IsProbabilityMeasure (clockOrientationQuotient clockLaw) where
  measure_univ := by
    simp [clockOrientationQuotient]
    exact ENNReal.inv_two_add_inv_two

/-- Probability-law packaging of the orientation quotient. -/
def clockOrientationQuotientLaw
    (clockLaw : ProbabilityMeasure ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨clockOrientationQuotient clockLaw, inferInstance⟩

@[simp]
lemma clockOrientationQuotientLaw_toMeasure
    (clockLaw : ProbabilityMeasure ℝ) :
    (clockOrientationQuotientLaw clockLaw : Measure ℝ) =
      clockOrientationQuotient clockLaw :=
  rfl

/-- The characteristic function of the orientation quotient is the even
part of the original clock characteristic function. -/
lemma charFun_clockOrientationQuotient
    (clockLaw : ProbabilityMeasure ℝ) (x : ℝ) :
    charFun (clockOrientationQuotient clockLaw) x =
      (charFun (clockLaw : Measure ℝ) x +
        charFun (clockLaw : Measure ℝ) (-x)) / 2 := by
  rw [clockOrientationQuotient, charFun_apply_real,
    integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [integral_add_measure]
  · rw [← charFun_apply_real, ← charFun_apply_real]
    rw [charFun_reflectedClockLaw]
    simp only [smul_add, Complex.real_smul]
    rw [show (((2 : ℝ)⁻¹ : ℝ) : ℂ) = (2 : ℂ)⁻¹ by norm_num]
    ring
  · apply (integrable_const (1 : ℝ)).mono'
    · fun_prop
    · filter_upwards with t
      change
        ‖Complex.exp
          ((x : ℂ) * (t : ℂ) * Complex.I)‖ ≤ 1
      rw [show
        (x : ℂ) * (t : ℂ) =
          ((x * t : ℝ) : ℂ) by
            push_cast
            ring]
      rw [Complex.norm_exp_ofReal_mul_I]
  · apply (integrable_const (1 : ℝ)).mono'
    · fun_prop
    · filter_upwards with t
      change
        ‖Complex.exp
          ((x : ℂ) * (t : ℂ) * Complex.I)‖ ≤ 1
      rw [show
        (x : ℂ) * (t : ℂ) =
          ((x * t : ℝ) : ℂ) by
            push_cast
            ring]
      rw [Complex.norm_exp_ofReal_mul_I]

/-- Averaging a recurrence moment over a clock and its reflection changes
nothing. -/
lemma clockSampledSpectralReturnMoment_orientationQuotient
    (clockLaw : ProbabilityMeasure ℝ)
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) :
    clockSampledSpectralReturnMoment
        (clockOrientationQuotientLaw clockLaw) mu n =
      clockSampledSpectralReturnMoment clockLaw mu n := by
  rw [clockSampledSpectralReturnMoment,
    clockOrientationQuotientLaw_toMeasure,
    clockOrientationQuotient, integral_smul_measure]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  have hintegrable (clock : ProbabilityMeasure ℝ) :
      Integrable
        (fun t =>
          ((Complex.normSq (charFun mu t) ^ n : ℝ) : ℂ))
        (clock : Measure ℝ) := by
    apply (integrable_const (1 : ℝ)).mono'
    · fun_prop
    · filter_upwards with t
      have ht := normSq_charFun_mem_Icc mu t
      rw [Complex.norm_real,
        Real.norm_of_nonneg (pow_nonneg ht.1 n)]
      exact pow_le_one₀ ht.1 ht.2
  rw [integral_add_measure
    (hintegrable clockLaw)
    (hintegrable (reflectedClockLaw clockLaw))]
  rw [show
    (∫ t,
        ((Complex.normSq (charFun mu t) ^ n : ℝ) : ℂ)
        ∂(reflectedClockLaw clockLaw : Measure ℝ)) =
      clockSampledSpectralReturnMoment
        (reflectedClockLaw clockLaw) mu n by
          rfl]
  rw [clockSampledSpectralReturnMoment_reflected]
  change (2 : ℝ)⁻¹ •
      (clockSampledSpectralReturnMoment clockLaw mu n +
        clockSampledSpectralReturnMoment clockLaw mu n) =
    clockSampledSpectralReturnMoment clockLaw mu n
  module

/-- Balanced two-level energy spectrum with gap `omega`. -/
def balancedTwoLevelEnergyMeasure (omega : ℝ) : Measure ℝ :=
  ProbabilityTheory.bernoulliMeasure
    (0 : ℝ) omega (⟨1 / 2, by norm_num⟩ : unitInterval)

instance balancedTwoLevelEnergyMeasure.instIsProbabilityMeasure
    (omega : ℝ) :
    IsProbabilityMeasure (balancedTwoLevelEnergyMeasure omega) := by
  unfold balancedTwoLevelEnergyMeasure
  infer_instance

/-- Exact amplitude of the balanced two-level probe. -/
lemma charFun_balancedTwoLevelEnergyMeasure
    (omega t : ℝ) :
    charFun (balancedTwoLevelEnergyMeasure omega) t =
      (1 + Complex.exp
        ((t : ℂ) * (omega : ℂ) * Complex.I)) / 2 := by
  rw [charFun_apply_real, balancedTwoLevelEnergyMeasure,
    ProbabilityTheory.integral_bernoulliMeasure]
  norm_num
  ring

/-- Exact fidelity fringe of the balanced two-level probe. -/
lemma normSq_charFun_balancedTwoLevelEnergyMeasure
    (omega t : ℝ) :
    Complex.normSq
        (charFun (balancedTwoLevelEnergyMeasure omega) t) =
      (1 + Real.cos (omega * t)) / 2 := by
  rw [charFun_balancedTwoLevelEnergyMeasure,
    show
      ((t : ℂ) * (omega : ℂ) * Complex.I) =
        ((t * omega : ℝ) : ℂ) * Complex.I by
          push_cast
          ring,
    Complex.exp_ofReal_mul_I, Complex.normSq_div]
  have htwo : Complex.normSq (2 : ℂ) = 4 := by
    norm_num [Complex.normSq]
  rw [htwo]
  rw [show
    (1 : ℂ) + ((Real.cos (t * omega) : ℂ) +
      (Real.sin (t * omega) : ℂ) * Complex.I) =
      ((1 + Real.cos (t * omega) : ℝ) : ℂ) +
        (Real.sin (t * omega) : ℂ) * Complex.I by
          push_cast
          ring]
  rw [Complex.normSq_add_mul_I]
  rw [show omega * t = t * omega by ring]
  nlinarith [Real.cos_sq_add_sin_sq (t * omega)]

/-- Probability-law packaging of the balanced two-level probe. -/
def balancedTwoLevelEnergyLaw (omega : ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨balancedTwoLevelEnergyMeasure omega, inferInstance⟩

@[simp]
lemma balancedTwoLevelEnergyLaw_toMeasure (omega : ℝ) :
    (balancedTwoLevelEnergyLaw omega : Measure ℝ) =
      balancedTwoLevelEnergyMeasure omega :=
  rfl

/-- The cosine transform of a clock law is the real part of its
characteristic function. -/
lemma integral_cos_mul_eq_charFun_re
    (clockLaw : ProbabilityMeasure ℝ) (omega : ℝ) :
    (∫ t, Real.cos (omega * t)
      ∂(clockLaw : Measure ℝ)) =
      (charFun (clockLaw : Measure ℝ) omega).re := by
  rw [charFun_apply_real]
  have hi : Integrable
      (fun t : ℝ =>
        Complex.exp
          ((omega : ℂ) * (t : ℂ) * Complex.I))
      (clockLaw : Measure ℝ) := by
    apply (integrable_const (1 : ℝ)).mono'
    · fun_prop
    · filter_upwards with t
      rw [show
        (omega : ℂ) * (t : ℂ) =
          ((omega * t : ℝ) : ℂ) by
            push_cast
            ring]
      rw [Complex.norm_exp_ofReal_mul_I]
  calc
    (∫ t, Real.cos (omega * t)
        ∂(clockLaw : Measure ℝ)) =
        ∫ t, RCLike.re
          (Complex.exp
            ((omega : ℂ) * (t : ℂ) * Complex.I))
          ∂(clockLaw : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [show
        (omega : ℂ) * (t : ℂ) =
          ((omega * t : ℝ) : ℂ) by
            push_cast
            ring]
      exact (Complex.exp_ofReal_mul_I_re _).symm
    _ = RCLike.re
        (∫ t,
          Complex.exp
            ((omega : ℂ) * (t : ℂ) * Complex.I)
          ∂(clockLaw : Measure ℝ)) :=
      integral_re hi
    _ = _ := rfl

/-- A balanced two-level system reads one Fourier-cosine coordinate of
the clock orientation quotient. -/
lemma clockSampledSpectralReturnMoment_balancedTwoLevel
    (clockLaw : ProbabilityMeasure ℝ) (omega : ℝ) :
    clockSampledSpectralReturnMoment clockLaw
        (balancedTwoLevelEnergyMeasure omega) 1 =
      (((1 + (charFun
        (clockLaw : Measure ℝ) omega).re) / 2 : ℝ) : ℂ) := by
  rw [clockSampledSpectralReturnMoment]
  simp_rw [pow_one,
    normSq_charFun_balancedTwoLevelEnergyMeasure]
  rw [integral_complex_ofReal]
  congr 1
  rw [show
    (fun t : ℝ => (1 + Real.cos (omega * t)) / 2) =
      fun t : ℝ =>
        (1 / 2) * 1 +
          (1 / 2) * Real.cos (omega * t) by
            funext t
            ring]
  rw [integral_add]
  · rw [integral_const_mul, integral_const_mul,
      integral_const, integral_cos_mul_eq_charFun_re]
    simp
    ring
  · fun_prop
  · apply Integrable.const_mul
    apply (integrable_const (1 : ℝ)).mono'
    · fun_prop
    · filter_upwards with t
      simp only [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _

/-- The orientation quotient has the real part of the original clock
characteristic function as its characteristic function. -/
lemma charFun_clockOrientationQuotient_eq_re
    (clockLaw : ProbabilityMeasure ℝ) (x : ℝ) :
    charFun (clockOrientationQuotient clockLaw) x =
      ((charFun (clockLaw : Measure ℝ) x).re : ℂ) := by
  rw [charFun_clockOrientationQuotient, charFun_neg]
  apply Complex.ext
  · simp
  · simp

/-- **Two-level clock tomography.** Balanced two-level probes with all
energy gaps distinguish exactly the orientation quotients of two arbitrary
clock laws. -/
theorem clockOrientationQuotient_eq_iff_twoLevelMoments
    (clockLaw₁ clockLaw₂ : ProbabilityMeasure ℝ) :
    clockOrientationQuotient clockLaw₁ =
        clockOrientationQuotient clockLaw₂ ↔
      ∀ omega : ℝ,
        clockSampledSpectralReturnMoment clockLaw₁
            (balancedTwoLevelEnergyMeasure omega) 1 =
          clockSampledSpectralReturnMoment clockLaw₂
            (balancedTwoLevelEnergyMeasure omega) 1 := by
  constructor
  · intro hquotient omega
    have hchar := congrFun
      (congrArg charFun hquotient) omega
    rw [charFun_clockOrientationQuotient_eq_re,
      charFun_clockOrientationQuotient_eq_re] at hchar
    have hre :
        (charFun (clockLaw₁ : Measure ℝ) omega).re =
          (charFun (clockLaw₂ : Measure ℝ) omega).re := by
      have h := congrArg Complex.re hchar
      simpa using h
    rw [clockSampledSpectralReturnMoment_balancedTwoLevel,
      clockSampledSpectralReturnMoment_balancedTwoLevel,
      hre]
  · intro hmoments
    apply Measure.ext_of_charFun
    funext omega
    rw [charFun_clockOrientationQuotient_eq_re,
      charFun_clockOrientationQuotient_eq_re]
    have h := hmoments omega
    rw [clockSampledSpectralReturnMoment_balancedTwoLevel,
      clockSampledSpectralReturnMoment_balancedTwoLevel] at h
    norm_cast
    have hreal :
        (1 + (charFun
            (clockLaw₁ : Measure ℝ) omega).re) / 2 =
          (1 + (charFun
            (clockLaw₂ : Measure ℝ) omega).re) / 2 := by
      exact_mod_cast h
    linarith

/-- **Maximal clock-information law for quantum recurrence.** Two
arbitrary clock laws are indistinguishable by the complete
survival-fidelity return distribution of every probability energy spectrum
if and only if their orientation quotients agree.  Thus recurrence loses
the direction of time, and universally loses no additional clock
information. -/
theorem clockOrientationQuotient_eq_iff_allReturnLaws
    (clockLaw₁ clockLaw₂ : ProbabilityMeasure ℝ) :
    clockOrientationQuotient clockLaw₁ =
        clockOrientationQuotient clockLaw₂ ↔
      ∀ mu : ProbabilityMeasure ℝ,
        (clockSampledSpectralReturnProbabilityMeasure
            clockLaw₁ (mu : Measure ℝ) : Measure ℝ) =
          (clockSampledSpectralReturnProbabilityMeasure
            clockLaw₂ (mu : Measure ℝ) : Measure ℝ) := by
  constructor
  · intro hquotient mu
    apply
      (clockSampledSpectralReturnProbabilityMeasure_eq_iff_moments
        clockLaw₁ clockLaw₂
        (mu : Measure ℝ) (mu : Measure ℝ)).2
    intro n
    rw [←
      clockSampledSpectralReturnMoment_orientationQuotient
        clockLaw₁ (mu : Measure ℝ) n,
      ←
      clockSampledSpectralReturnMoment_orientationQuotient
        clockLaw₂ (mu : Measure ℝ) n]
    have hlaw :
        clockOrientationQuotientLaw clockLaw₁ =
          clockOrientationQuotientLaw clockLaw₂ := by
      apply ProbabilityMeasure.toMeasure_injective
      exact hquotient
    rw [hlaw]
  · intro hall
    apply
      (clockOrientationQuotient_eq_iff_twoLevelMoments
        clockLaw₁ clockLaw₂).2
    intro omega
    have hreturn :=
      hall (balancedTwoLevelEnergyLaw omega)
    exact
      (clockSampledSpectralReturnProbabilityMeasure_eq_iff_moments
        clockLaw₁ clockLaw₂
        (balancedTwoLevelEnergyLaw omega : Measure ℝ)
        (balancedTwoLevelEnergyLaw omega : Measure ℝ)).1
          hreturn 1

/-! ### The maximal system quotient of recurrence -/

/-- Probability clock concentrated at one deterministic readout time. -/
def deterministicClockLaw (t : ℝ) : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac t, Measure.dirac.isProbabilityMeasure⟩

@[simp]
lemma deterministicClockLaw_toMeasure (t : ℝ) :
    (deterministicClockLaw t : Measure ℝ) =
      Measure.dirac t :=
  rfl

/-- A deterministic clock reads the pointwise survival-fidelity moment. -/
lemma clockSampledSpectralReturnMoment_deterministic
    (t : ℝ) (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) :
    clockSampledSpectralReturnMoment
        (deterministicClockLaw t) mu n =
      ((Complex.normSq (charFun mu t) ^ n : ℝ) : ℂ) := by
  rw [clockSampledSpectralReturnMoment,
    deterministicClockLaw_toMeasure, integral_dirac]

/-- Equal energy-gap laws give equal complete return laws under every
probability clock. -/
lemma allReturnLaws_of_spectralDifferenceMeasure_eq
    (mu₁ mu₂ : ProbabilityMeasure ℝ)
    (hgap :
      spectralDifferenceMeasure (mu₁ : Measure ℝ) =
        spectralDifferenceMeasure (mu₂ : Measure ℝ))
    (clockLaw : ProbabilityMeasure ℝ) :
    (clockSampledSpectralReturnProbabilityMeasure
        clockLaw (mu₁ : Measure ℝ) : Measure ℝ) =
      (clockSampledSpectralReturnProbabilityMeasure
        clockLaw (mu₂ : Measure ℝ) : Measure ℝ) := by
  apply
    (clockSampledSpectralReturnProbabilityMeasure_eq_iff_moments
      clockLaw clockLaw
      (mu₁ : Measure ℝ) (mu₂ : Measure ℝ)).2
  intro n
  rw [
    clockSampledSpectralReturnMoment_eq_clockTransferCollision,
    clockSampledSpectralReturnMoment_eq_clockTransferCollision,
    hgap]

/-- **Maximal system-information law for quantum recurrence.** Two
arbitrary probability energy spectra are indistinguishable by the complete
survival-fidelity return distribution under every probability clock if and
only if their energy-gap laws agree.  Thus the spectral autocorrelation is
not merely sufficient: it is the exact maximal system quotient seen by all
survival-return experiments. -/
theorem spectralDifferenceMeasure_eq_iff_allClockReturnLaws
    (mu₁ mu₂ : ProbabilityMeasure ℝ) :
    spectralDifferenceMeasure (mu₁ : Measure ℝ) =
        spectralDifferenceMeasure (mu₂ : Measure ℝ) ↔
      ∀ clockLaw : ProbabilityMeasure ℝ,
        (clockSampledSpectralReturnProbabilityMeasure
            clockLaw (mu₁ : Measure ℝ) : Measure ℝ) =
          (clockSampledSpectralReturnProbabilityMeasure
            clockLaw (mu₂ : Measure ℝ) : Measure ℝ) := by
  constructor
  · intro hgap clockLaw
    exact allReturnLaws_of_spectralDifferenceMeasure_eq
      mu₁ mu₂ hgap clockLaw
  · intro hall
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_spectralDifferenceMeasure,
      charFun_spectralDifferenceMeasure]
    have hreturn := hall (deterministicClockLaw t)
    have hmoments :=
      (clockSampledSpectralReturnProbabilityMeasure_eq_iff_moments
        (deterministicClockLaw t)
        (deterministicClockLaw t)
        (mu₁ : Measure ℝ) (mu₂ : Measure ℝ)).1
          hreturn
    simpa only [clockSampledSpectralReturnMoment_deterministic,
      pow_one] using hmoments 1

/-! ### Universal collapse to minimal probes -/

/-- The maximal system quotient is already determined by first return
moments at deterministic times.  No higher return moment is needed to
decide universal system equivalence. -/
theorem spectralDifferenceMeasure_eq_iff_deterministicFirstMoments
    (mu₁ mu₂ : ProbabilityMeasure ℝ) :
    spectralDifferenceMeasure (mu₁ : Measure ℝ) =
        spectralDifferenceMeasure (mu₂ : Measure ℝ) ↔
      ∀ t : ℝ,
        clockSampledSpectralReturnMoment
            (deterministicClockLaw t) (mu₁ : Measure ℝ) 1 =
          clockSampledSpectralReturnMoment
            (deterministicClockLaw t) (mu₂ : Measure ℝ) 1 := by
  constructor
  · intro hgap t
    have hchar := congrFun (congrArg charFun hgap) t
    rw [charFun_spectralDifferenceMeasure,
      charFun_spectralDifferenceMeasure] at hchar
    simpa only [clockSampledSpectralReturnMoment_deterministic,
      pow_one] using hchar
  · intro hmoments
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_spectralDifferenceMeasure,
      charFun_spectralDifferenceMeasure]
    simpa only [clockSampledSpectralReturnMoment_deterministic,
      pow_one] using hmoments t

/-- **Minimal system-probe collapse.** Equality of the complete
survival-return laws of two arbitrary systems under every probability
clock is decided by deterministic-clock first moments alone. -/
theorem allClockReturnLaws_eq_iff_deterministicFirstMoments
    (mu₁ mu₂ : ProbabilityMeasure ℝ) :
    (∀ clockLaw : ProbabilityMeasure ℝ,
        (clockSampledSpectralReturnProbabilityMeasure
            clockLaw (mu₁ : Measure ℝ) : Measure ℝ) =
          (clockSampledSpectralReturnProbabilityMeasure
            clockLaw (mu₂ : Measure ℝ) : Measure ℝ)) ↔
      ∀ t : ℝ,
        clockSampledSpectralReturnMoment
            (deterministicClockLaw t) (mu₁ : Measure ℝ) 1 =
          clockSampledSpectralReturnMoment
            (deterministicClockLaw t) (mu₂ : Measure ℝ) 1 :=
  (spectralDifferenceMeasure_eq_iff_allClockReturnLaws
      mu₁ mu₂).symm.trans
    (spectralDifferenceMeasure_eq_iff_deterministicFirstMoments
      mu₁ mu₂)

/-- **Minimal clock-probe collapse.** Equality of the complete
survival-return laws produced by two arbitrary clocks for every
probability energy spectrum is decided by first moments of balanced
two-level probes alone. -/
theorem allReturnLaws_eq_iff_balancedTwoLevelFirstMoments
    (clockLaw₁ clockLaw₂ : ProbabilityMeasure ℝ) :
    (∀ mu : ProbabilityMeasure ℝ,
        (clockSampledSpectralReturnProbabilityMeasure
            clockLaw₁ (mu : Measure ℝ) : Measure ℝ) =
          (clockSampledSpectralReturnProbabilityMeasure
            clockLaw₂ (mu : Measure ℝ) : Measure ℝ)) ↔
      ∀ omega : ℝ,
        clockSampledSpectralReturnMoment clockLaw₁
            (balancedTwoLevelEnergyMeasure omega) 1 =
          clockSampledSpectralReturnMoment clockLaw₂
            (balancedTwoLevelEnergyMeasure omega) 1 :=
  (clockOrientationQuotient_eq_iff_allReturnLaws
      clockLaw₁ clockLaw₂).symm.trans
    (clockOrientationQuotient_eq_iff_twoLevelMoments
      clockLaw₁ clockLaw₂)

/-- **Countable system tomography.** A countable dense family of
deterministic rational clock times already decides equality of the complete
return laws of two systems under every probability clock. -/
theorem allClockReturnLaws_eq_iff_rationalDeterministicFirstMoments
    (mu₁ mu₂ : ProbabilityMeasure ℝ) :
    (∀ clockLaw : ProbabilityMeasure ℝ,
        (clockSampledSpectralReturnProbabilityMeasure
            clockLaw (mu₁ : Measure ℝ) : Measure ℝ) =
          (clockSampledSpectralReturnProbabilityMeasure
            clockLaw (mu₂ : Measure ℝ) : Measure ℝ)) ↔
      ∀ q : ℚ,
        clockSampledSpectralReturnMoment
            (deterministicClockLaw (q : ℝ))
            (mu₁ : Measure ℝ) 1 =
          clockSampledSpectralReturnMoment
            (deterministicClockLaw (q : ℝ))
            (mu₂ : Measure ℝ) 1 := by
  constructor
  · intro hall q
    exact
      (allClockReturnLaws_eq_iff_deterministicFirstMoments
        mu₁ mu₂).1 hall (q : ℝ)
  · intro hrational
    apply
      (allClockReturnLaws_eq_iff_deterministicFirstMoments
        mu₁ mu₂).2
    have heq :
        (fun t : ℝ =>
          clockSampledSpectralReturnMoment
            (deterministicClockLaw t)
            (mu₁ : Measure ℝ) 1) =
        (fun t : ℝ =>
          clockSampledSpectralReturnMoment
            (deterministicClockLaw t)
            (mu₂ : Measure ℝ) 1) := by
      apply Rat.isDenseEmbedding_coe_real.dense.equalizer
      · simp only [
          clockSampledSpectralReturnMoment_deterministic,
          pow_one]
        exact Complex.continuous_ofReal.comp
          (Complex.continuous_normSq.comp continuous_charFun)
      · simp only [
          clockSampledSpectralReturnMoment_deterministic,
          pow_one]
        exact Complex.continuous_ofReal.comp
          (Complex.continuous_normSq.comp continuous_charFun)
      · funext q
        exact hrational q
    exact congrFun heq

/-- **Countable clock tomography.** A countable dense scan of rational gaps
with one balanced two-level probe already decides equality of the complete
return laws produced by two clocks for every probability energy spectrum. -/
theorem allReturnLaws_eq_iff_rationalTwoLevelFirstMoments
    (clockLaw₁ clockLaw₂ : ProbabilityMeasure ℝ) :
    (∀ mu : ProbabilityMeasure ℝ,
        (clockSampledSpectralReturnProbabilityMeasure
            clockLaw₁ (mu : Measure ℝ) : Measure ℝ) =
          (clockSampledSpectralReturnProbabilityMeasure
            clockLaw₂ (mu : Measure ℝ) : Measure ℝ)) ↔
      ∀ q : ℚ,
        clockSampledSpectralReturnMoment clockLaw₁
            (balancedTwoLevelEnergyMeasure (q : ℝ)) 1 =
          clockSampledSpectralReturnMoment clockLaw₂
            (balancedTwoLevelEnergyMeasure (q : ℝ)) 1 := by
  constructor
  · intro hall q
    exact
      (allReturnLaws_eq_iff_balancedTwoLevelFirstMoments
        clockLaw₁ clockLaw₂).1 hall (q : ℝ)
  · intro hrational
    apply
      (allReturnLaws_eq_iff_balancedTwoLevelFirstMoments
        clockLaw₁ clockLaw₂).2
    have heq :
        (fun omega : ℝ =>
          clockSampledSpectralReturnMoment clockLaw₁
            (balancedTwoLevelEnergyMeasure omega) 1) =
        (fun omega : ℝ =>
          clockSampledSpectralReturnMoment clockLaw₂
            (balancedTwoLevelEnergyMeasure omega) 1) := by
      apply Rat.isDenseEmbedding_coe_real.dense.equalizer
      · simp only [
          clockSampledSpectralReturnMoment_balancedTwoLevel]
        fun_prop
      · simp only [
          clockSampledSpectralReturnMoment_balancedTwoLevel]
        fun_prop
      · funext q
        exact hrational q
    exact congrFun heq

/-! ### Sharp failure of every finite universal probe schedule -/

/-- A probability measure whose characteristic function vanishes at every
nonzero frequency in a prescribed finite list. -/
def finiteFrequencyMaskingMeasure : List ℝ → Measure ℝ
  | [] => Measure.dirac 0
  | omega :: frequencies =>
      if omega = 0 then
        finiteFrequencyMaskingMeasure frequencies
      else
        balancedTwoLevelEnergyMeasure (Real.pi / omega) ∗
          finiteFrequencyMaskingMeasure frequencies

instance finiteFrequencyMaskingMeasure.instIsProbabilityMeasure
    (frequencies : List ℝ) :
    IsProbabilityMeasure
      (finiteFrequencyMaskingMeasure frequencies) := by
  induction frequencies with
  | nil =>
      simp only [finiteFrequencyMaskingMeasure]
      infer_instance
  | cons omega frequencies ih =>
      rw [finiteFrequencyMaskingMeasure]
      split_ifs
      · exact ih
      · letI :
            IsProbabilityMeasure
              (finiteFrequencyMaskingMeasure frequencies) := ih
        infer_instance

lemma charFun_balancedTwoLevel_pi_div_self
    {omega : ℝ} (homega : omega ≠ 0) :
    charFun
        (balancedTwoLevelEnergyMeasure (Real.pi / omega))
        omega = 0 := by
  rw [charFun_balancedTwoLevelEnergyMeasure]
  have hexponent :
      ((omega : ℂ) * ((Real.pi / omega : ℝ) : ℂ) *
        Complex.I) =
        (Real.pi : ℂ) * Complex.I := by
    have homegaC : (omega : ℂ) ≠ 0 := by
      exact_mod_cast homega
    push_cast
    field_simp [homegaC]
  rw [hexponent, Complex.exp_pi_mul_I]
  norm_num

theorem charFun_finiteFrequencyMaskingMeasure_eq_zero
    (frequencies : List ℝ) {omega : ℝ}
    (homega : omega ∈ frequencies) (homega0 : omega ≠ 0) :
    charFun (finiteFrequencyMaskingMeasure frequencies) omega = 0 := by
  induction frequencies with
  | nil =>
      simp at homega
  | cons head tail ih =>
      rw [finiteFrequencyMaskingMeasure]
      split_ifs with hhead
      · subst head
        exact ih ((List.mem_cons.mp homega).resolve_left homega0)
      · rw [charFun_conv]
        rcases List.mem_cons.mp homega with rfl | htail
        · rw [charFun_balancedTwoLevel_pi_div_self hhead,
            zero_mul]
        · rw [ih htail, mul_zero]

lemma exists_ne_zero_charFun_re_pos
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    ∃ t : ℝ, t ≠ 0 ∧
      0 < (charFun mu t).re := by
  have hcontinuous :
      Continuous (fun t : ℝ => (charFun mu t).re) :=
    Complex.continuous_re.comp continuous_charFun
  have hopen :
      IsOpen {t : ℝ | 0 < (charFun mu t).re} :=
    isOpen_Ioi.preimage hcontinuous
  have hzero :
      (0 : ℝ) ∈ {t : ℝ | 0 < (charFun mu t).re} := by
    simp
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  refine ⟨epsilon / 2, ne_of_gt (half_pos hepsilon), ?_⟩
  exact hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_pos (half_pos hepsilon)]
    linarith)

/-- Probability-law packaging of the finite frequency mask. -/
def finiteFrequencyMaskingLaw
    (frequencies : List ℝ) : ProbabilityMeasure ℝ :=
  ⟨finiteFrequencyMaskingMeasure frequencies, inferInstance⟩

@[simp]
lemma finiteFrequencyMaskingLaw_toMeasure
    (frequencies : List ℝ) :
    (finiteFrequencyMaskingLaw frequencies : Measure ℝ) =
      finiteFrequencyMaskingMeasure frequencies :=
  rfl

/-- Translation of the finite frequency mask, represented as convolution
with a point mass. -/
def translatedFiniteFrequencyMaskingLaw
    (frequencies : List ℝ) (shift : ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨finiteFrequencyMaskingMeasure frequencies ∗
      Measure.dirac shift, by infer_instance⟩

@[simp]
lemma translatedFiniteFrequencyMaskingLaw_toMeasure
    (frequencies : List ℝ) (shift : ℝ) :
    (translatedFiniteFrequencyMaskingLaw frequencies shift :
        Measure ℝ) =
      finiteFrequencyMaskingMeasure frequencies ∗
        Measure.dirac shift :=
  rfl

/-- **No finite clock tomography.** For every finite set of balanced
two-level probe gaps there are inequivalent clock-orientation quotients
whose first return moments agree at every chosen gap. -/
theorem exists_clockLaws_not_equivalent_of_agree_on_finiteTwoLevelProbes
    (frequencies : List ℝ) :
    ∃ clockLaw₁ clockLaw₂ : ProbabilityMeasure ℝ,
      (∀ omega ∈ frequencies,
        clockSampledSpectralReturnMoment clockLaw₁
            (balancedTwoLevelEnergyMeasure omega) 1 =
          clockSampledSpectralReturnMoment clockLaw₂
            (balancedTwoLevelEnergyMeasure omega) 1) ∧
      clockOrientationQuotient clockLaw₁ ≠
        clockOrientationQuotient clockLaw₂ := by
  let mask : Measure ℝ :=
    finiteFrequencyMaskingMeasure frequencies
  obtain ⟨t, ht0, htre⟩ :=
    exists_ne_zero_charFun_re_pos mask
  let shift : ℝ := Real.pi / t
  let clockLaw₁ := finiteFrequencyMaskingLaw frequencies
  let clockLaw₂ :=
    translatedFiniteFrequencyMaskingLaw frequencies shift
  refine ⟨clockLaw₁, clockLaw₂, ?_, ?_⟩
  · intro omega homega
    rw [clockSampledSpectralReturnMoment_balancedTwoLevel,
      clockSampledSpectralReturnMoment_balancedTwoLevel]
    by_cases homega0 : omega = 0
    · subst omega
      simp
    · have hmask :
          charFun mask omega = 0 := by
        exact charFun_finiteFrequencyMaskingMeasure_eq_zero
          frequencies homega homega0
      have hshift :
          charFun
              (finiteFrequencyMaskingMeasure frequencies ∗
                Measure.dirac shift) omega = 0 := by
        rw [charFun_conv, hmask, zero_mul]
      simp only [clockLaw₁, clockLaw₂,
        finiteFrequencyMaskingLaw_toMeasure,
        translatedFiniteFrequencyMaskingLaw_toMeasure,
        mask] at hmask hshift ⊢
      rw [hmask, hshift]
  · intro hquotient
    have hchar :=
      congrFun (congrArg charFun hquotient) t
    rw [charFun_clockOrientationQuotient_eq_re,
      charFun_clockOrientationQuotient_eq_re] at hchar
    have hshiftExp :
        Complex.exp
            (((t * shift : ℝ) : ℂ) *
              Complex.I) = -1 := by
      have htC : (t : ℂ) ≠ 0 := by
        exact_mod_cast ht0
      have hexponent :
          (((t * shift : ℝ) : ℂ) *
            Complex.I) =
            (Real.pi : ℂ) * Complex.I := by
        simp only [shift]
        push_cast
        field_simp [htC]
      rw [hexponent, Complex.exp_pi_mul_I]
    have htranslated :
        charFun
            (finiteFrequencyMaskingMeasure frequencies ∗
              Measure.dirac shift) t =
          -charFun mask t := by
      rw [charFun_conv, charFun_dirac]
      simp only [RCLike.inner_apply, conj_trivial]
      rw [hshiftExp, mul_neg, mul_one]
    simp only [clockLaw₁, clockLaw₂,
      finiteFrequencyMaskingLaw_toMeasure,
      translatedFiniteFrequencyMaskingLaw_toMeasure] at hchar
    rw [htranslated] at hchar
    have hre :
        (charFun mask t).re =
          (-charFun mask t).re := by
      exact_mod_cast congrArg Complex.re hchar
    have hre' :
        (charFun mask t).re =
          -(charFun mask t).re := by
      simpa using hre
    linarith

/-- Add one balanced two-level spectral factor to a finite frequency mask. -/
def annihilatedFiniteFrequencyMaskingLaw
    (frequencies : List ℝ) (frequency : ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨finiteFrequencyMaskingMeasure frequencies ∗
      balancedTwoLevelEnergyMeasure (Real.pi / frequency),
    by infer_instance⟩

@[simp]
lemma annihilatedFiniteFrequencyMaskingLaw_toMeasure
    (frequencies : List ℝ) (frequency : ℝ) :
    (annihilatedFiniteFrequencyMaskingLaw frequencies frequency :
        Measure ℝ) =
      finiteFrequencyMaskingMeasure frequencies ∗
        balancedTwoLevelEnergyMeasure (Real.pi / frequency) :=
  rfl

/-- **No finite system tomography.** For every finite set of deterministic
clock times there are inequivalent energy-gap laws whose first return
moments agree at every chosen time. -/
theorem exists_systemLaws_not_equivalent_of_agree_on_finiteDeterministicProbes
    (frequencies : List ℝ) :
    ∃ mu₁ mu₂ : ProbabilityMeasure ℝ,
      (∀ t ∈ frequencies,
        clockSampledSpectralReturnMoment
            (deterministicClockLaw t) (mu₁ : Measure ℝ) 1 =
          clockSampledSpectralReturnMoment
            (deterministicClockLaw t) (mu₂ : Measure ℝ) 1) ∧
      spectralDifferenceMeasure (mu₁ : Measure ℝ) ≠
        spectralDifferenceMeasure (mu₂ : Measure ℝ) := by
  let mask : Measure ℝ :=
    finiteFrequencyMaskingMeasure frequencies
  obtain ⟨t, ht0, htre⟩ :=
    exists_ne_zero_charFun_re_pos mask
  let mu₁ := finiteFrequencyMaskingLaw frequencies
  let mu₂ :=
    annihilatedFiniteFrequencyMaskingLaw frequencies t
  refine ⟨mu₁, mu₂, ?_, ?_⟩
  · intro omega homega
    rw [clockSampledSpectralReturnMoment_deterministic,
      clockSampledSpectralReturnMoment_deterministic]
    by_cases homega0 : omega = 0
    · subst omega
      simp
    · have hmask :
          charFun mask omega = 0 := by
        exact charFun_finiteFrequencyMaskingMeasure_eq_zero
          frequencies homega homega0
      have hannihilated :
          charFun
              (finiteFrequencyMaskingMeasure frequencies ∗
                balancedTwoLevelEnergyMeasure
                  (Real.pi / t)) omega = 0 := by
        rw [charFun_conv, hmask, zero_mul]
      simp only [mu₁, mu₂,
        finiteFrequencyMaskingLaw_toMeasure,
        annihilatedFiniteFrequencyMaskingLaw_toMeasure,
        mask] at hmask hannihilated ⊢
      rw [hmask, hannihilated]
  · intro hgap
    have hequal :=
      (spectralDifferenceMeasure_eq_iff_deterministicFirstMoments
        mu₁ mu₂).1 hgap t
    have hkill :
        charFun
            (balancedTwoLevelEnergyMeasure (Real.pi / t))
            t = 0 :=
      charFun_balancedTwoLevel_pi_div_self ht0
    have hnonzero :
        charFun mask t ≠ 0 := by
      intro hzero
      rw [hzero] at htre
      simp at htre
    simp only [mu₁, mu₂,
      finiteFrequencyMaskingLaw_toMeasure,
      annihilatedFiniteFrequencyMaskingLaw_toMeasure,
      clockSampledSpectralReturnMoment_deterministic,
      pow_one] at hequal
    rw [charFun_conv, hkill, mul_zero,
      Complex.normSq_zero] at hequal
    norm_num at hequal
    exact hnonzero (by simpa only [mask] using hequal)

/-- Symmetric-window mean of an arbitrary real statistic of fidelity. -/
def spectralReturnStatisticMeanReal
    (mu : Measure ℝ) (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  (2 * r)⁻¹ *
    ∫ t in -r..r, g (Complex.normSq (charFun mu t))

private lemma continuous_fidelity
    (mu : Measure ℝ) [IsProbabilityMeasure mu] :
    Continuous (fun t : ℝ ↦ Complex.normSq (charFun mu t)) :=
  Complex.continuous_normSq.comp continuous_charFun

private lemma continuous_polynomial_fidelity
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ[X]) :
    Continuous
      (fun t : ℝ ↦ p.eval (Complex.normSq (charFun mu t))) := by
  exact p.continuous.comp (continuous_fidelity mu)

/-- Exact collision-hierarchy evaluation of a polynomial fidelity
statistic. -/
def spectralCollisionPolynomialMean
    (mu : Measure ℝ) (p : ℝ[X]) : ℝ :=
  p.sum fun n a ↦
    a * (convPow (spectralDifferenceMeasure mu) n).real {0}

lemma spectralCollisionPolynomialMean_add
    (mu : Measure ℝ) (p q : ℝ[X]) :
    spectralCollisionPolynomialMean mu (p + q) =
      spectralCollisionPolynomialMean mu p +
        spectralCollisionPolynomialMean mu q := by
  refine Polynomial.sum_add_index p q _ (fun _ ↦ by ring)
    (fun _ _ _ ↦ by ring)

/-- Every polynomial fidelity statistic converges exactly to its
collision-hierarchy evaluation. -/
theorem spectralReturnStatisticMeanReal_polynomial_tendsto_collisionHierarchy
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ[X]) :
    Tendsto
      (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x))
      atTop (𝓝 (spectralCollisionPolynomialMean mu p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hadd :
          spectralReturnStatisticMeanReal mu
              (fun x ↦ (p + q).eval x) =
            fun r ↦
              spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r +
              spectralReturnStatisticMeanReal mu (fun x ↦ q.eval x) r := by
        funext r
        rw [spectralReturnStatisticMeanReal]
        simp_rw [Polynomial.eval_add]
        rw [intervalIntegral.integral_add
          ((continuous_polynomial_fidelity mu p).intervalIntegrable (-r) r)
          ((continuous_polynomial_fidelity mu q).intervalIntegrable (-r) r)]
        simp only [spectralReturnStatisticMeanReal]
        ring
      rw [hadd, spectralCollisionPolynomialMean_add]
      exact hp.add hq
  | monomial n a =>
      have hmono :
          spectralReturnStatisticMeanReal mu
              (fun x ↦ (Polynomial.monomial n a).eval x) =
            fun r ↦ a * spectralReturnMomentMeanReal mu n r := by
        funext r
        rw [spectralReturnStatisticMeanReal,
          spectralReturnMomentMeanReal]
        simp_rw [Polynomial.eval_monomial]
        rw [intervalIntegral.integral_const_mul]
        ring
      rw [hmono, spectralCollisionPolynomialMean]
      simp only [Polynomial.sum_monomial_index, zero_mul]
      exact
        (spectralReturnMomentMeanReal_tendsto_collisionHierarchy
          mu n).const_mul a

/-- Every polynomial fidelity statistic has a long-time mean. -/
lemma exists_tendsto_spectralReturnStatisticMeanReal_polynomial
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ[X]) :
    ∃ L : ℝ,
      Tendsto
        (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x))
        atTop (𝓝 L) :=
  ⟨spectralCollisionPolynomialMean mu p,
    spectralReturnStatisticMeanReal_polynomial_tendsto_collisionHierarchy
      mu p⟩

/-- In the atomless phase, every polynomial statistic has the same
long-time mean as evaluation at zero fidelity. -/
lemma spectralReturnStatisticMeanReal_polynomial_tendsto_eval_zero_of_noAtoms
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (p : ℝ[X]) :
    Tendsto
        (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x))
        atTop (𝓝 (p.eval 0)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hadd :
          spectralReturnStatisticMeanReal mu
              (fun x ↦ (p + q).eval x) =
            fun r ↦
              spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r +
              spectralReturnStatisticMeanReal mu (fun x ↦ q.eval x) r := by
        funext r
        rw [spectralReturnStatisticMeanReal]
        simp_rw [Polynomial.eval_add]
        rw [intervalIntegral.integral_add
          ((continuous_polynomial_fidelity mu p).intervalIntegrable (-r) r)
          ((continuous_polynomial_fidelity mu q).intervalIntegrable (-r) r)]
        simp only [spectralReturnStatisticMeanReal]
        ring
      rw [hadd, Polynomial.eval_add]
      exact hp.add hq
  | monomial n a =>
      have hmono :
          spectralReturnStatisticMeanReal mu
              (fun x ↦ (Polynomial.monomial n a).eval x) =
            fun r ↦ a * spectralReturnMomentMeanReal mu n r := by
        funext r
        rw [spectralReturnStatisticMeanReal,
          spectralReturnMomentMeanReal]
        simp_rw [Polynomial.eval_monomial]
        rw [intervalIntegral.integral_const_mul]
        ring
      rw [hmono, Polynomial.eval_monomial]
      by_cases hn : n = 0
      · subst n
        have hmoment :=
          spectralReturnMomentMeanReal_tendsto_collisionHierarchy mu 0
        have hzero :
            (convPow (spectralDifferenceMeasure mu) 0).real {0} = 1 := by
          rw [convPow, Measure.real,
            Measure.dirac_apply' 0 (measurableSet_singleton 0)]
          norm_num
        simpa [hzero] using hmoment.const_mul a
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hmoment :=
          spectralReturnMomentMeanReal_tendsto_collisionHierarchy mu n
        have hzero :=
          spectralCollisionHierarchy_eq_zero_of_noAtoms mu hnpos
        simpa [hzero, hn] using hmoment.const_mul a

/-- Uniform approximation on the fidelity interval controls every positive
window mean with the same error. -/
lemma spectralReturnStatisticMeanReal_dist_le_of_uniform
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    {epsilon r : ℝ} (hr : 0 < r)
    (hfg : ∀ x ∈ Icc (0 : ℝ) 1, |f x - g x| ≤ epsilon) :
    dist (spectralReturnStatisticMeanReal mu f r)
        (spectralReturnStatisticMeanReal mu g r) ≤ epsilon := by
  let F : ℝ → ℝ := fun t ↦ Complex.normSq (charFun mu t)
  have hF : Continuous F := continuous_fidelity mu
  have hfi : IntervalIntegrable (fun t ↦ f (F t)) volume (-r) r :=
    (hf.comp hF.continuousOn
      (fun t _ ↦ normSq_charFun_mem_Icc mu t)).intervalIntegrable
  have hgi : IntervalIntegrable (fun t ↦ g (F t)) volume (-r) r :=
    (hg.comp hF.continuousOn
      (fun t _ ↦ normSq_charFun_mem_Icc mu t)).intervalIntegrable
  have hnorm :
      ‖∫ t in -r..r, (f (F t) - g (F t))‖ ≤
        epsilon * |r - (-r)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    simpa [Real.norm_eq_abs] using
      hfg (F t) (normSq_charFun_mem_Icc mu t)
  rw [spectralReturnStatisticMeanReal,
    spectralReturnStatisticMeanReal, Real.dist_eq]
  have hscale : 0 ≤ (2 * r)⁻¹ := by positivity
  calc
    |(2 * r)⁻¹ * (∫ t in -r..r, f (F t)) -
        (2 * r)⁻¹ * (∫ t in -r..r, g (F t))| =
        (2 * r)⁻¹ *
          ‖(∫ t in -r..r, f (F t)) -
            (∫ t in -r..r, g (F t))‖ := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hscale,
            Real.norm_eq_abs]
    _ = (2 * r)⁻¹ *
          ‖∫ t in -r..r, (f (F t) - g (F t))‖ := by
          rw [intervalIntegral.integral_sub hfi hgi]
    _ ≤ (2 * r)⁻¹ * (epsilon * |r - (-r)|) := by
          gcongr
    _ = epsilon := by
          rw [abs_of_pos (by linarith : 0 < r - (-r))]
          field_simp
          ring

/-- Complete recurrence-distribution law.  Every continuous real statistic
of survival fidelity has a symmetric-window long-time mean for every
probability energy spectrum, finite or infinite.  The polynomial moments
determining this mean are the exact additive collision hierarchy above. -/
theorem exists_tendsto_spectralReturnStatisticMeanReal
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    ∃ L : ℝ,
      Tendsto (spectralReturnStatisticMeanReal mu g) atTop (𝓝 L) := by
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, ?_⟩
  intro epsilon hepsilon
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn
      0 1 g hg (epsilon / 8) (by positivity)
  obtain ⟨Lp, hLp⟩ :=
    exists_tendsto_spectralReturnStatisticMeanReal_polynomial mu p
  have hevent :
      ∀ᶠ r in atTop,
        dist
          (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r)
          Lp < epsilon / 4 :=
    (Metric.tendsto_nhds.mp hLp) (epsilon / 4) (by positivity)
  refine ⟨Metric.ball Lp (epsilon / 2), ?_, ?_⟩
  · rw [mem_map]
    filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with r hrp hr
    change dist (spectralReturnStatisticMeanReal mu g r) Lp <
      epsilon / 2
    have happrox :
        dist (spectralReturnStatisticMeanReal mu g r)
          (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r) ≤
            epsilon / 8 := by
      apply spectralReturnStatisticMeanReal_dist_le_of_uniform
        mu hg
        (p.continuous_eval₂ (RingHom.id ℝ)).continuousOn
        hr
      intro x hx
      rw [abs_sub_comm]
      exact (hp x hx).le
    calc
      dist (spectralReturnStatisticMeanReal mu g r) Lp ≤
          dist (spectralReturnStatisticMeanReal mu g r)
              (spectralReturnStatisticMeanReal mu
                (fun x ↦ p.eval x) r) +
            dist (spectralReturnStatisticMeanReal mu
                (fun x ↦ p.eval x) r) Lp :=
        dist_triangle _ _ _
      _ < epsilon / 8 + epsilon / 4 :=
        add_lt_add_of_le_of_lt happrox hrp
      _ < epsilon / 2 := by linarith
  · intro x hx y hy
    rw [Metric.mem_ball] at hx hy
    refine (dist_triangle x Lp y).trans_lt ?_
    rw [dist_comm Lp y]
    linarith

/-- Atomless complete-distribution law.  For every continuous fidelity
statistic, the long-time mean is its value at zero.  Equivalently, the full
asymptotic fidelity distribution is the point mass at zero, even for
singular-continuous spectra whose pointwise fidelity need not decay. -/
theorem spectralReturnStatisticMeanReal_tendsto_eval_zero_of_noAtoms
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    Tendsto (spectralReturnStatisticMeanReal mu g) atTop (𝓝 (g 0)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn
      0 1 g hg (epsilon / 4) (by positivity)
  have hpmean :=
    spectralReturnStatisticMeanReal_polynomial_tendsto_eval_zero_of_noAtoms
      mu p
  have hevent :
      ∀ᶠ r in atTop,
        dist
          (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r)
          (p.eval 0) < epsilon / 4 :=
    (Metric.tendsto_nhds.mp hpmean) (epsilon / 4) (by positivity)
  filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with r hrp hr
  have happrox :
      dist (spectralReturnStatisticMeanReal mu g r)
          (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r) ≤
        epsilon / 4 := by
    apply spectralReturnStatisticMeanReal_dist_le_of_uniform
      mu hg (p.continuous_eval₂ (RingHom.id ℝ)).continuousOn hr
    intro x hx
    rw [abs_sub_comm]
    exact (hp x hx).le
  have hzero : dist (p.eval 0) (g 0) < epsilon / 4 := by
    rw [Real.dist_eq]
    exact hp 0 (by constructor <;> norm_num)
  calc
    dist (spectralReturnStatisticMeanReal mu g r) (g 0) ≤
        dist (spectralReturnStatisticMeanReal mu g r)
            (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r) +
          dist (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r)
            (g 0) :=
      dist_triangle _ _ _
    _ ≤ epsilon / 4 +
        (dist (spectralReturnStatisticMeanReal mu (fun x ↦ p.eval x) r)
            (p.eval 0) + dist (p.eval 0) (g 0)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < epsilon := by linarith

end RHTower
