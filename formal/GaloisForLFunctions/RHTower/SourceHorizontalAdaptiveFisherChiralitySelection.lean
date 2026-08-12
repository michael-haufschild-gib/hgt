import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherReflectionCurvature
import GaloisForLFunctions.HTGeometry.ConstitutiveObserverFibreChirality

/-!
# Source-horizontal adaptive Fisher chirality selection

The symmetric Fisher/Jeffreys frame cannot orient a reflected horizontal class.  Directed KL
chirality can: adaptive prime occupation is the logistic family with natural parameter
`(t - 1) log p`, and the reflected pair is centered at `-log p`.  Bernoulli KL chirality is
strictly zero only at `t = 0` throughout the Xi critical strip `|t| < 1`.

Consequently any literal source involution exchanging two finite laws, together with a
pair-sufficient Boolean observer realizing the two adaptive prime occupations, forces the
horizontal grade to vanish.  The final theorem records the resulting exact RH endpoint.  No
existence or sufficiency of such an arithmetic observer is assumed here.
-/

open Real Set MeasureTheory InformationTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-- Log-partition function of the Bernoulli natural exponential family. -/
def sourceHorizontalSoftplus (x : ℝ) : ℝ := Real.log (Real.exp x + 1)

/-- Fisher variance of the Bernoulli logistic family. -/
def sourceHorizontalFermiVariance (x : ℝ) : ℝ :=
  Real.sigmoid x * (1 - Real.sigmoid x)

theorem sourceHorizontalSigmoid_eq_exp_div (x : ℝ) :
    Real.sigmoid x = Real.exp x / (Real.exp x + 1) := by
  rw [Real.sigmoid_def, Real.exp_neg]
  have he : Real.exp x ≠ 0 := Real.exp_ne_zero x
  field_simp

theorem sourceHorizontalOne_sub_sigmoid (x : ℝ) :
    1 - Real.sigmoid x = (Real.exp x + 1)⁻¹ := by
  rw [sourceHorizontalSigmoid_eq_exp_div]
  have he : Real.exp x + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem sourceHorizontalLog_sigmoid (x : ℝ) :
    Real.log (Real.sigmoid x) = x - sourceHorizontalSoftplus x := by
  rw [sourceHorizontalSigmoid_eq_exp_div, Real.log_div (Real.exp_ne_zero x) (by positivity),
    Real.log_exp]
  rfl

theorem sourceHorizontalLog_one_sub_sigmoid (x : ℝ) :
    Real.log (1 - Real.sigmoid x) = -sourceHorizontalSoftplus x := by
  rw [sourceHorizontalOne_sub_sigmoid, Real.log_inv]
  rfl

theorem sourceHorizontalHasDerivAt_softplus (x : ℝ) :
    HasDerivAt sourceHorizontalSoftplus (Real.sigmoid x) x := by
  have h := (Real.hasDerivAt_exp x).add_const 1 |>.log (by positivity)
  convert h using 1
  · ext y
    rfl
  · rw [sourceHorizontalSigmoid_eq_exp_div]

theorem sourceHorizontalHasDerivAt_fermiVariance (x : ℝ) :
    HasDerivAt sourceHorizontalFermiVariance
      (sourceHorizontalFermiVariance x * (1 - 2 * Real.sigmoid x)) x := by
  have hs := Real.hasDerivAt_sigmoid x
  have hc := (hasDerivAt_const x 1).sub hs
  change HasDerivAt (fun y => Real.sigmoid y * (1 - Real.sigmoid y))
    (Real.sigmoid x * (1 - Real.sigmoid x) * (1 - 2 * Real.sigmoid x)) x
  convert hs.mul hc using 1
  all_goals first | rfl | (norm_num; ring_nf)

theorem sourceHorizontalFermiVariance_pos (x : ℝ) : 0 < sourceHorizontalFermiVariance x := by
  unfold sourceHorizontalFermiVariance
  exact mul_pos (Real.sigmoid_pos x) (sub_pos.mpr (Real.sigmoid_lt_one x))

theorem sourceHorizontalFermiVariance_strictMonoOn_neg :
    StrictMonoOn sourceHorizontalFermiVariance (Set.Iio 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iio 0)
    (fun x _ => (sourceHorizontalHasDerivAt_fermiVariance x).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Iio] at hx
  rw [(sourceHorizontalHasDerivAt_fermiVariance x).deriv]
  have hs : Real.sigmoid x < 1 / 2 := by
    have := Real.sigmoid_strictMono hx
    simpa [Real.sigmoid_zero, one_div] using this
  exact mul_pos (sourceHorizontalFermiVariance_pos x) (by linarith)

/-- Directed KL chirality for two Bernoulli natural parameters centered at `c` and split by `s`. -/
def sourceHorizontalCenteredBernoulliKLChirality (c s : ℝ) : ℝ :=
  2 * s * (Real.sigmoid (c + s) + Real.sigmoid (c - s)) -
    2 * (sourceHorizontalSoftplus (c + s) - sourceHorizontalSoftplus (c - s))

theorem sourceHorizontalCenteredBernoulliKLChirality_zero (c : ℝ) :
    sourceHorizontalCenteredBernoulliKLChirality c 0 = 0 := by
  simp [sourceHorizontalCenteredBernoulliKLChirality]

theorem sourceHorizontalCenteredBernoulliKLChirality_odd (c s : ℝ) :
    sourceHorizontalCenteredBernoulliKLChirality c (-s) = -sourceHorizontalCenteredBernoulliKLChirality c s := by
  unfold sourceHorizontalCenteredBernoulliKLChirality
  ring

theorem sourceHorizontalHasDerivAt_centeredBernoulliKLChirality (c s : ℝ) :
    HasDerivAt (sourceHorizontalCenteredBernoulliKLChirality c)
      (2 * s * (sourceHorizontalFermiVariance (c + s) - sourceHorizontalFermiVariance (c - s))) s := by
  have hp := (Real.hasDerivAt_sigmoid (c + s)).comp s
    ((hasDerivAt_const s c).add (hasDerivAt_id s))
  have hm := (Real.hasDerivAt_sigmoid (c - s)).comp s
    ((hasDerivAt_const s c).sub (hasDerivAt_id s))
  have hlp := (sourceHorizontalHasDerivAt_softplus (c + s)).comp s
    ((hasDerivAt_const s c).add (hasDerivAt_id s))
  have hlm := (sourceHorizontalHasDerivAt_softplus (c - s)).comp s
    ((hasDerivAt_const s c).sub (hasDerivAt_id s))
  change HasDerivAt
    (fun y => 2 * y * (Real.sigmoid (c + y) + Real.sigmoid (c - y)) -
      2 * (sourceHorizontalSoftplus (c + y) - sourceHorizontalSoftplus (c - y)))
    (2 * s * ((Real.sigmoid (c + s) * (1 - Real.sigmoid (c + s))) -
      (Real.sigmoid (c - s) * (1 - Real.sigmoid (c - s))))) s
  convert (((hasDerivAt_id s).const_mul 2).mul (hp.add hm)).sub
    ((hlp.sub hlm).const_mul 2) using 1
  all_goals first
    | rfl
    | (simp only [Function.comp_apply, Pi.add_apply, id_eq]; ring)

theorem sourceHorizontalCenteredBernoulliKLChirality_strictMonoOn_nonneg (c : ℝ) :
    StrictMonoOn (sourceHorizontalCenteredBernoulliKLChirality c) (Set.Icc 0 (-c)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (-c))
    (fun s _ =>
      (sourceHorizontalHasDerivAt_centeredBernoulliKLChirality c s).continuousAt.continuousWithinAt)
  intro s hs
  rw [interior_Icc] at hs
  rcases hs with ⟨hs0, hsc⟩
  rw [(sourceHorizontalHasDerivAt_centeredBernoulliKLChirality c s).deriv]
  have hplus : c + s < 0 := by linarith
  have hminus : c - s < c + s := by linarith
  have hv := sourceHorizontalFermiVariance_strictMonoOn_neg (by linarith : c - s < 0) hplus hminus
  exact mul_pos (mul_pos (by norm_num) hs0) (sub_pos.mpr hv)

theorem sourceHorizontalCenteredBernoulliKLChirality_eq_zero_iff {c s : ℝ} (hc : c < 0)
    (hs : |s| < -c) : sourceHorizontalCenteredBernoulliKLChirality c s = 0 ↔ s = 0 := by
  constructor
  · intro hzero
    rcases lt_trichotomy s 0 with hneg | hzero' | hpos
    · have hmem : -s ∈ Set.Icc 0 (-c) := by
        constructor
        · linarith
        · rw [abs_of_neg hneg] at hs
          linarith
      have hlt := sourceHorizontalCenteredBernoulliKLChirality_strictMonoOn_nonneg c
        (by constructor <;> linarith : (0 : ℝ) ∈ Set.Icc 0 (-c)) hmem (by linarith)
      rw [sourceHorizontalCenteredBernoulliKLChirality_zero, sourceHorizontalCenteredBernoulliKLChirality_odd, hzero] at hlt
      linarith
    · exact hzero'
    · have hmem : s ∈ Set.Icc 0 (-c) := by
        constructor
        · linarith
        · rw [abs_of_pos hpos] at hs
          linarith
      have hlt := sourceHorizontalCenteredBernoulliKLChirality_strictMonoOn_nonneg c
        (by constructor <;> linarith : (0 : ℝ) ∈ Set.Icc 0 (-c)) hmem hpos
      rw [sourceHorizontalCenteredBernoulliKLChirality_zero, hzero] at hlt
      linarith
  · rintro rfl
    exact sourceHorizontalCenteredBernoulliKLChirality_zero c

@[simp] theorem sourceHorizontalUnitIntervalSigmoid_coe (x : ℝ) :
    ((unitInterval.sigmoid x : unitInterval) : ℝ) = Real.sigmoid x := rfl

theorem klChirality_bernoulli_sigmoid (x y : ℝ) :
    klChirality Ber(true, false, unitInterval.sigmoid x)
        Ber(true, false, unitInterval.sigmoid y) =
      (x - y) * (Real.sigmoid x + Real.sigmoid y) -
        2 * (sourceHorizontalSoftplus x - sourceHorizontalSoftplus y) := by
  rw [klChirality,
    toReal_klDiv_bernoulli (unitInterval.sigmoid x) (unitInterval.sigmoid y)
      (unitInterval.sigmoid_pos x) (unitInterval.sigmoid_lt_one x)
      (unitInterval.sigmoid_pos y) (unitInterval.sigmoid_lt_one y),
    toReal_klDiv_bernoulli (unitInterval.sigmoid y) (unitInterval.sigmoid x)
      (unitInterval.sigmoid_pos y) (unitInterval.sigmoid_lt_one y)
      (unitInterval.sigmoid_pos x) (unitInterval.sigmoid_lt_one x)]
  simp only [sourceHorizontalUnitIntervalSigmoid_coe]
  rw [Real.log_div (Real.sigmoid_pos x).ne' (Real.sigmoid_pos y).ne',
    Real.log_div (Real.sigmoid_pos y).ne' (Real.sigmoid_pos x).ne',
    Real.log_div (sub_pos.mpr (Real.sigmoid_lt_one x)).ne'
      (sub_pos.mpr (Real.sigmoid_lt_one y)).ne',
    Real.log_div (sub_pos.mpr (Real.sigmoid_lt_one y)).ne'
      (sub_pos.mpr (Real.sigmoid_lt_one x)).ne',
    sourceHorizontalLog_sigmoid, sourceHorizontalLog_sigmoid,
    sourceHorizontalLog_one_sub_sigmoid, sourceHorizontalLog_one_sub_sigmoid]
  ring

theorem sourceHorizontalPrimeAdaptiveOccupation_eq_sigmoid (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveOccupation p t =
      Real.sigmoid ((t - 1) * Real.log (p : ℝ)) := by
  rw [sourceHorizontalSigmoid_eq_exp_div]
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hexp : Real.exp ((t - 1) * Real.log (p : ℝ)) = (p.1 : ℝ) ^ (t - 1) := by
    rw [Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [hexp, Real.rpow_sub hp]
  norm_num
  unfold sourceHorizontalPrimeAdaptiveOccupation
  have hpt : (0 : ℝ) < (p.1 : ℝ) ^ t := Real.rpow_pos_of_pos hp _
  field_simp
  ring

/-- Statistical reversal is not horizontal reflection: Boolean complement translates the
source-horizontal grade by two units. -/
theorem sourceHorizontalPrimeAdaptiveOccupation_complement_eq_translateTwo
    (p : Nat.Primes) (t : ℝ) :
    1 - sourceHorizontalPrimeAdaptiveOccupation p t =
      sourceHorizontalPrimeAdaptiveOccupation p (2 - t) := by
  rw [sourceHorizontalPrimeAdaptiveOccupation_complement]
  unfold sourceHorizontalPrimeAdaptiveOccupation
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hpt : (0 : ℝ) < (p.1 : ℝ) ^ t := Real.rpow_pos_of_pos hp _
  have hp2t : (0 : ℝ) < (p.1 : ℝ) ^ (2 - t) := Real.rpow_pos_of_pos hp _
  rw [Real.rpow_sub hp]
  norm_num
  field_simp
  ring

/-- Exact no-go: the canonical Boolean involution never exchanges the two horizontally reflected
adaptive occupations.  Their natural parameters differ by the fixed translation `2 log p`. -/
theorem sourceHorizontalPrimeAdaptiveOccupation_reflected_ne_complement
    (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveOccupation p (-t) ≠
      1 - sourceHorizontalPrimeAdaptiveOccupation p t := by
  rw [sourceHorizontalPrimeAdaptiveOccupation_complement_eq_translateTwo,
    sourceHorizontalPrimeAdaptiveOccupation_eq_sigmoid,
    sourceHorizontalPrimeAdaptiveOccupation_eq_sigmoid]
  intro h
  have hparam := Real.sigmoid_inj.mp h
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  nlinarith

theorem sourceHorizontalPrimeAdaptiveOccupationUnit_eq_sigmoid (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveOccupationUnit p t =
      unitInterval.sigmoid ((t - 1) * Real.log (p : ℝ)) := by
  ext
  exact sourceHorizontalPrimeAdaptiveOccupation_eq_sigmoid p t

/-- Directed KL chirality of the two reflected source-horizontal prime occupations. -/
noncomputable def sourceHorizontalPrimeAdaptiveKLChirality (p : Nat.Primes) (t : ℝ) : ℝ :=
  klChirality
    Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p t)
    Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-t))

theorem sourceHorizontalPrimeAdaptiveKLChirality_eq_centered (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveKLChirality p t =
      sourceHorizontalCenteredBernoulliKLChirality (-Real.log (p : ℝ)) (t * Real.log (p : ℝ)) := by
  rw [sourceHorizontalPrimeAdaptiveKLChirality, sourceHorizontalPrimeAdaptiveOccupationUnit_eq_sigmoid,
    sourceHorizontalPrimeAdaptiveOccupationUnit_eq_sigmoid, klChirality_bernoulli_sigmoid]
  unfold sourceHorizontalCenteredBernoulliKLChirality
  congr 2 <;> ring

theorem sourceHorizontalPrimeAdaptiveKLChirality_eq_zero_iff (p : Nat.Primes) {t : ℝ}
    (ht : |t| < 1) : sourceHorizontalPrimeAdaptiveKLChirality p t = 0 ↔ t = 0 := by
  have hp1 : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hs : |t * Real.log (p : ℝ)| < -(-Real.log (p : ℝ)) := by
    rw [abs_mul, abs_of_pos hlog]
    simpa using mul_lt_mul_of_pos_right ht hlog
  rw [sourceHorizontalPrimeAdaptiveKLChirality_eq_centered,
    sourceHorizontalCenteredBernoulliKLChirality_eq_zero_iff (neg_neg_of_pos hlog) hs]
  exact mul_eq_zero.trans (or_iff_left hlog.ne')

/-- **Weak arithmetic producer interface.** Source reversal kills total directed chirality.  It is
enough that forward and reverse information losses in the observer fibre agree; neither loss must
vanish. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fibreBalancedSourceReversal
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    (p : Nat.Primes) {t : ℝ} (ht : |t| < 1)
    {q : Ω → Bool} (_hq : Measurable q)
    (hfibre : observerFibreChirality P R q = 0)
    (hPobs : P.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p t))
    (hRobs : R.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-t)))
    {θ : Ω → Ω} (hθ : Measurable θ) (hinv : ∀ x, θ (θ x) = x)
    (hP : P.map θ = R) (hR : R.map θ = P) : t = 0 := by
  have hsource : klChirality P R = 0 :=
    klChirality_eq_zero_of_reversal P R hθ hinv hP hR
  have hobs : klChirality (P.map q) (R.map q) = 0 := by
    rw [klChirality_observer_conservation P R q, hfibre, add_zero] at hsource
    exact hsource
  rw [hPobs, hRobs] at hobs
  exact (sourceHorizontalPrimeAdaptiveKLChirality_eq_zero_iff p ht).mp hobs

/-- Pair-sufficiency is a stronger sufficient condition for the same source selector. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_source_reversal
    {Ω : Type*} [MeasurableSpace Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    (p : Nat.Primes) {t : ℝ} (ht : |t| < 1)
    {q : Ω → Bool} (hq : Measurable q)
    (hsuff : IsKLPairSufficient P R q)
    (hPobs : P.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p t))
    (hRobs : R.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-t)))
    {θ : Ω → Ω} (hθ : Measurable θ) (hinv : ∀ x, θ (θ x) = x)
    (hP : P.map θ = R) (hR : R.map θ = P) : t = 0 := by
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fibreBalancedSourceReversal
    P R p ht hq (observerFibreChirality_eq_zero_of_pairSufficient P R q hsuff)
    hPobs hRobs hθ hinv hP hR

/-- Source reversal transports forward hidden loss for `q` to reverse hidden loss for the
non-equivariantly reflected observer `q ∘ θ`. -/
theorem conditionalForwardKL_sourceReversal_eq_reflectedObserver
    {Ω Y : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace Y] [MeasurableEq Y]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    {q : Ω → Y} (hq : Measurable q)
    {θ : Ω → Ω} (hθ : Measurable θ) (hinv : ∀ x, θ (θ x) = x)
    (hP : P.map θ = R) (hR : R.map θ = P)
    (hobs : klDiv (P.map q) (R.map q) ≠ ⊤) :
    conditionalForwardKL P R q = conditionalForwardKL R P (q ∘ θ) := by
  have htotal : klDiv R P = klDiv P R := by
    have hkl := klDiv_map_measurableEmbedding
      (measurableEmbedding_of_measurable_involution hθ hinv) P R
    rw [hP, hR] at hkl
    exact hkl
  have hRq : R.map (q ∘ θ) = P.map q := by
    rw [← Measure.map_map hq hθ, hR]
  have hPq : P.map (q ∘ θ) = R.map q := by
    rw [← Measure.map_map hq hθ, hP]
  have hf := klDiv_eq_map_add_cond P R hq
  have hr := klDiv_eq_map_add_cond R P (hq.comp hθ)
  rw [htotal, hRq, hPq] at hr
  rw [hf] at hr
  apply (ENNReal.add_right_inj hobs).mp
  simpa [conditionalForwardKL] using hr

/-- Conditional form of the weak producer.  A reflection may preserve nonzero hidden information;
only equality of the two directed conditional KL costs is required. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_conditionalFibreReversal
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    (p : Nat.Primes) {t : ℝ} (ht : |t| < 1)
    {q : Ω → Bool} (hq : Measurable q)
    (hPcond : conditionalForwardKL P R q ≠ ⊤)
    (hRcond : conditionalForwardKL R P q ≠ ⊤)
    (hcond : conditionalForwardKL P R q = conditionalForwardKL R P q)
    (hPobs : P.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p t))
    (hRobs : R.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-t)))
    {θ : Ω → Ω} (hθ : Measurable θ) (hinv : ∀ x, θ (θ x) = x)
    (hP : P.map θ = R) (hR : R.map θ = P) : t = 0 := by
  have hPmap : klDiv (P.map q) (R.map q) ≠ ⊤ := by
    rw [hPobs, hRobs]
    exact klDiv_bernoulli_ne_top _ _
      (sourceHorizontalPrimeAdaptiveOccupation_pos p t)
      (sourceHorizontalPrimeAdaptiveOccupation_lt_one p t)
      (sourceHorizontalPrimeAdaptiveOccupation_pos p (-t))
      (sourceHorizontalPrimeAdaptiveOccupation_lt_one p (-t))
  have hRmap : klDiv (R.map q) (P.map q) ≠ ⊤ := by
    rw [hPobs, hRobs]
    exact klDiv_bernoulli_ne_top _ _
      (sourceHorizontalPrimeAdaptiveOccupation_pos p (-t))
      (sourceHorizontalPrimeAdaptiveOccupation_lt_one p (-t))
      (sourceHorizontalPrimeAdaptiveOccupation_pos p t)
      (sourceHorizontalPrimeAdaptiveOccupation_lt_one p t)
  have hfibre : observerFibreChirality P R q = 0 := by
    rw [observerFibreChirality_eq_conditionalDifference P R hq
      hPmap hPcond hRmap hRcond, hcond, sub_self]
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fibreBalancedSourceReversal
    P R p ht hq hfibre hPobs hRobs hθ hinv hP hR

/-- **Non-equivariant same-source reduction.** Reversal already transports forward hidden loss to
the reverse loss of the reflected observer `q ∘ θ`.  Therefore the only additional source law is
invariance of reverse conditional loss under `q ↔ q ∘ θ`. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_reflectedObserverConditionalInvariance
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    (p : Nat.Primes) {t : ℝ} (ht : |t| < 1)
    {q : Ω → Bool} (hq : Measurable q)
    {θ : Ω → Ω}
    (hPcond : conditionalForwardKL P R q ≠ ⊤)
    (hRcond : conditionalForwardKL R P q ≠ ⊤)
    (hinvariant : conditionalForwardKL R P (q ∘ θ) = conditionalForwardKL R P q)
    (hPobs : P.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p t))
    (hRobs : R.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-t)))
    (hθ : Measurable θ) (hinv : ∀ x, θ (θ x) = x)
    (hP : P.map θ = R) (hR : R.map θ = P) : t = 0 := by
  have hobs : klDiv (P.map q) (R.map q) ≠ ⊤ := by
    rw [hPobs, hRobs]
    exact klDiv_bernoulli_ne_top _ _
      (sourceHorizontalPrimeAdaptiveOccupation_pos p t)
      (sourceHorizontalPrimeAdaptiveOccupation_lt_one p t)
      (sourceHorizontalPrimeAdaptiveOccupation_pos p (-t))
      (sourceHorizontalPrimeAdaptiveOccupation_lt_one p (-t))
  have hreflected :
      conditionalForwardKL P R q = conditionalForwardKL R P (q ∘ θ) :=
    conditionalForwardKL_sourceReversal_eq_reflectedObserver
      P R hq hθ hinv hP hR hobs
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_conditionalFibreReversal
    P R p ht hq hPcond hRcond (hreflected.trans hinvariant)
    hPobs hRobs hθ hinv hP hR

/-- **Honesty boundary.** Once source reversal and the two adaptive Bernoulli marginals are already
specified, same-source conditional invariance under `q ↔ q ∘ θ` is equivalent to neutral grade.
It is an exact producer socket, not an independent consequence of reversal. -/
theorem sourceHorizontalPrimeAdaptive_reflectedObserverConditionalInvariance_iff
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (P R : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure R]
    (p : Nat.Primes) {t : ℝ} (ht : |t| < 1)
    {q : Ω → Bool} (hq : Measurable q)
    {θ : Ω → Ω}
    (hPcond : conditionalForwardKL P R q ≠ ⊤)
    (hRcond : conditionalForwardKL R P q ≠ ⊤)
    (hPobs : P.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p t))
    (hRobs : R.map q =
      Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-t)))
    (hθ : Measurable θ) (hinv : ∀ x, θ (θ x) = x)
    (hP : P.map θ = R) (hR : R.map θ = P) :
    conditionalForwardKL R P (q ∘ θ) = conditionalForwardKL R P q ↔ t = 0 := by
  constructor
  · intro hinvariant
    exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_reflectedObserverConditionalInvariance
      P R p ht hq hPcond hRcond hinvariant hPobs hRobs hθ hinv hP hR
  · rintro rfl
    have hmaps : P.map q = R.map q := by
      calc
        P.map q = Ber(true, false,
            sourceHorizontalPrimeAdaptiveOccupationUnit p 0) := hPobs
        _ = Ber(true, false,
            sourceHorizontalPrimeAdaptiveOccupationUnit p (-0)) := by norm_num
        _ = R.map q := hRobs.symm
    have htotal : klDiv R P = klDiv P R := by
      have hkl := klDiv_map_measurableEmbedding
        (measurableEmbedding_of_measurable_involution hθ hinv) P R
      rw [hP, hR] at hkl
      exact hkl
    have hf := klDiv_eq_map_add_cond P R hq
    have hr := klDiv_eq_map_add_cond R P hq
    have hf' : klDiv P R = conditionalForwardKL P R q := by
      simpa [conditionalForwardKL, hmaps] using hf
    have hr' : klDiv R P = conditionalForwardKL R P q := by
      simpa [conditionalForwardKL, ← hmaps] using hr
    have hobs : klDiv (P.map q) (R.map q) ≠ ⊤ := by
      rw [hmaps, klDiv_self]
      simp
    have hreflected :
        conditionalForwardKL P R q = conditionalForwardKL R P (q ∘ θ) :=
      conditionalForwardKL_sourceReversal_eq_reflectedObserver
        P R hq hθ hinv hP hR hobs
    calc
      conditionalForwardKL R P (q ∘ θ) = conditionalForwardKL P R q := hreflected.symm
      _ = klDiv P R := hf'.symm
      _ = klDiv R P := htotal.symm
      _ = conditionalForwardKL R P q := hr'

universe u

/-- Minimal literal producer certificate.  Source reversal occurs before observation; observer
retains adaptive occupations and has equal—not necessarily zero—forward/reverse fibre loss. -/
structure SourceHorizontalPrimeAdaptiveFibreBalancedReversalCertificate
    (p : Nat.Primes) (t : ℝ) where
  Ω : Type u
  measurableSpace : MeasurableSpace Ω
  P : @Measure Ω measurableSpace
  R : @Measure Ω measurableSpace
  finite_P : @IsFiniteMeasure Ω measurableSpace P
  finite_R : @IsFiniteMeasure Ω measurableSpace R
  observer : Ω → Bool
  measurable_observer :
    @Measurable Ω Bool measurableSpace instMeasurableSpaceBool observer
  fibre_chirality_zero :
    @observerFibreChirality Ω Bool measurableSpace instMeasurableSpaceBool P R observer = 0
  map_P : Measure.map observer P =
    Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p t)
  map_R : Measure.map observer R =
    Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-t))
  reversal : Ω → Ω
  measurable_reversal :
    @Measurable Ω Ω measurableSpace measurableSpace reversal
  involutive_reversal : ∀ x, reversal (reversal x) = x
  reversal_P : Measure.map reversal P = R
  reversal_R : Measure.map reversal R = P

/-- Any fibre-balanced producer certificate inside the open horizontal strip selects neutrality. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fibreBalancedCertificate
    (p : Nat.Primes) {t : ℝ} (ht : |t| < 1)
    (C : SourceHorizontalPrimeAdaptiveFibreBalancedReversalCertificate p t) : t = 0 := by
  letI : MeasurableSpace C.Ω := C.measurableSpace
  letI : IsFiniteMeasure C.P := C.finite_P
  letI : IsFiniteMeasure C.R := C.finite_R
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fibreBalancedSourceReversal
    C.P C.R p ht C.measurable_observer C.fibre_chirality_zero C.map_P C.map_R
    C.measurable_reversal C.involutive_reversal C.reversal_P C.reversal_R

/-- Literal producer certificate: two source laws exchanged before observation, with a Boolean
observer that loses neither directed KL orientation and retains the adaptive prime occupations. -/
structure SourceHorizontalPrimeAdaptiveReversalCertificate
    (p : Nat.Primes) (t : ℝ) where
  Ω : Type u
  measurableSpace : MeasurableSpace Ω
  P : @Measure Ω measurableSpace
  R : @Measure Ω measurableSpace
  finite_P : @IsFiniteMeasure Ω measurableSpace P
  finite_R : @IsFiniteMeasure Ω measurableSpace R
  observer : Ω → Bool
  measurable_observer :
    @Measurable Ω Bool measurableSpace instMeasurableSpaceBool observer
  sufficient :
    @IsKLPairSufficient Ω Bool measurableSpace instMeasurableSpaceBool P R observer
  map_P : Measure.map observer P =
    Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p t)
  map_R : Measure.map observer R =
    Ber(true, false, sourceHorizontalPrimeAdaptiveOccupationUnit p (-t))
  reversal : Ω → Ω
  measurable_reversal :
    @Measurable Ω Ω measurableSpace measurableSpace reversal
  involutive_reversal : ∀ x, reversal (reversal x) = x
  reversal_P : Measure.map reversal P = R
  reversal_R : Measure.map reversal R = P

/-- Any producer certificate inside the open horizontal strip selects its neutral grade. -/
theorem sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_certificate
    (p : Nat.Primes) {t : ℝ} (ht : |t| < 1)
    (C : SourceHorizontalPrimeAdaptiveReversalCertificate p t) : t = 0 := by
  letI : MeasurableSpace C.Ω := C.measurableSpace
  letI : IsFiniteMeasure C.P := C.finite_P
  letI : IsFiniteMeasure C.R := C.finite_R
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_source_reversal
    C.P C.R p ht C.measurable_observer C.sufficient C.map_P C.map_R
    C.measurable_reversal C.involutive_reversal C.reversal_P C.reversal_R

/-- Multiplicity-resolved Xi specialization of the source reversal certificate. -/
abbrev SourceHorizontalXiAdaptiveReversalCertificate
    (q : XiZeroCopy) (p : Nat.Primes) :=
  SourceHorizontalPrimeAdaptiveReversalCertificate p
    (primeDepthBVWoldXiCenteredRate q.1)

/-- Weaker Xi certificate allowing nonzero but orientation-balanced hidden information loss. -/
abbrev SourceHorizontalXiAdaptiveFibreBalancedReversalCertificate
    (q : XiZeroCopy) (p : Nat.Primes) :=
  SourceHorizontalPrimeAdaptiveFibreBalancedReversalCertificate p
    (primeDepthBVWoldXiCenteredRate q.1)

theorem sourceHorizontalXiAdaptiveKLChirality_eq_zero_iff (q : XiZeroCopy) (p : Nat.Primes) :
    sourceHorizontalPrimeAdaptiveKLChirality p (primeDepthBVWoldXiCenteredRate q.1) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  change sourceHorizontalPrimeAdaptiveKLChirality p (2 * (q.1 : ℂ).re - 1) = 0 ↔
    (q.1 : ℂ).re = 1 / 2
  have halg : 2 * (q.1 : ℂ).re - 1 = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
    constructor <;> intro h <;> linarith
  rw [sourceHorizontalPrimeAdaptiveKLChirality_eq_zero_iff p
      (xiCenteredPrimeIdealRate_abs_lt_one q.1),
    halg]

theorem sourceHorizontalXi_re_eq_half_of_adaptiveReversalCertificate
    (q : XiZeroCopy) (p : Nat.Primes)
    (C : SourceHorizontalXiAdaptiveReversalCertificate q p) :
    (q.1 : ℂ).re = 1 / 2 := by
  rw [← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_certificate p
    (xiCenteredPrimeIdealRate_abs_lt_one q.1) C

theorem sourceHorizontalXi_re_eq_half_of_adaptiveFibreBalancedReversalCertificate
    (q : XiZeroCopy) (p : Nat.Primes)
    (C : SourceHorizontalXiAdaptiveFibreBalancedReversalCertificate q p) :
    (q.1 : ℂ).re = 1 / 2 := by
  rw [← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  exact sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fibreBalancedCertificate p
    (xiCenteredPrimeIdealRate_abs_lt_one q.1) C

/-- Vanishing of every multiplicity-resolved prime adaptive KL chirality is exactly RH. -/
theorem riemannHypothesis_iff_sourceHorizontalXi_adaptiveKLChirality_zero :
    RiemannHypothesis ↔ ∀ (q : XiZeroCopy) (p : Nat.Primes),
      sourceHorizontalPrimeAdaptiveKLChirality p (primeDepthBVWoldXiCenteredRate q.1) = 0 := by
  constructor
  · intro hRH q p
    exact (sourceHorizontalXiAdaptiveKLChirality_eq_zero_iff q p).2
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro q
    exact (sourceHorizontalXiAdaptiveKLChirality_eq_zero_iff (xiFirstZeroCopy q)
      ⟨2, Nat.prime_two⟩).1 (h (xiFirstZeroCopy q) ⟨2, Nat.prime_two⟩)

/-- A certificate for each multiplicity-resolved Xi copy at one retained prime proves RH. -/
theorem riemannHypothesis_of_sourceHorizontalXi_adaptiveReversalCertificates
    (hcert : ∀ q : XiZeroCopy,
      SourceHorizontalXiAdaptiveReversalCertificate q ⟨2, Nat.prime_two⟩) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  intro q
  exact sourceHorizontalXi_re_eq_half_of_adaptiveReversalCertificate
    (xiFirstZeroCopy q) ⟨2, Nat.prime_two⟩ (hcert (xiFirstZeroCopy q))

/-- **Shortest Frankenstein endpoint.** A fibre-balanced reversible source certificate for each
multiplicity-resolved Xi copy at one retained prime proves RH. -/
theorem riemannHypothesis_of_sourceHorizontalXi_adaptiveFibreBalancedReversalCertificates
    (hcert : ∀ q : XiZeroCopy,
      SourceHorizontalXiAdaptiveFibreBalancedReversalCertificate
        q ⟨2, Nat.prime_two⟩) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
  intro q
  exact sourceHorizontalXi_re_eq_half_of_adaptiveFibreBalancedReversalCertificate
    (xiFirstZeroCopy q) ⟨2, Nat.prime_two⟩ (hcert (xiFirstZeroCopy q))

end

end RHTower
