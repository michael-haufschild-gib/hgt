import GaloisForLFunctions.HTGeometry.CountFormationSplit
import GaloisForLFunctions.HTGeometry.PoissonSuperpositionSaturationProperness

/-!
# Bounded-conservation blindness and the modular producer criterion

Every probability-normalized bounded comparison of two superposed Poisson formations — signed
total mass, total variation, Hellinger distance, Jensen--Shannon divergence, Boolean occupancy
information — stays bounded while the recovered-history action diverges linearly.  A viable
conservation producer must therefore retain an unbounded likelihood scale.  Uniform control of the
logarithmic Radon--Nikodym cocycle is an exact sufficient law and forces rate neutrality.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ## The modular producer criterion -/

variable {X : Type*} [MeasurableSpace X]

/-- Reversing the two laws flips the sign of the logarithmic likelihood cocycle. -/
theorem llr_symm {P Q : Measure X} [SigmaFinite P] [SigmaFinite Q] (hQP : Q ≪ P) :
    llr Q P =ᵐ[Q] fun x => -llr P Q x := by
  have hinv := Measure.inv_rnDeriv hQP
  filter_upwards [hinv] with x hx
  have hx' : Q.rnDeriv P x = (P.rnDeriv Q x)⁻¹ := by
    rw [← hx]
    simp
  rw [llr, llr, hx', ENNReal.toReal_inv, Real.log_inv]

/-- Jeffreys divergence. -/
def jeffreys (P Q : Measure X) : ℝ := (klDiv P Q).toReal + (klDiv Q P).toReal

theorem jeffreys_symm (P Q : Measure X) : jeffreys P Q = jeffreys Q P := by
  rw [jeffreys, jeffreys]; ring

theorem jeffreys_nonneg (P Q : Measure X) : 0 ≤ jeffreys P Q := by
  rw [jeffreys]; positivity

/-- **Modular representation of Jeffreys information.**  Symmetrized relative entropy is the
integral of the logarithmic likelihood cocycle against the signed difference. -/
theorem jeffreys_eq_integral_llr_sub {P Q : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    jeffreys P Q = ∫ x, llr P Q x ∂P - ∫ x, llr P Q x ∂Q := by
  rw [jeffreys, toReal_klDiv_of_measure_eq hPQ (by simp),
    toReal_klDiv_of_measure_eq hQP (by simp), integral_congr_ae (llr_symm hQP)]
  rw [integral_neg]
  ring

/-- **Logarithmic-cocycle domination.**  Jeffreys information is dominated by the total modular
mass of the logarithmic likelihood cocycle. -/
theorem jeffreys_le_integral_abs_llr {P Q : Measure X} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P)
    (hint : Integrable (llr P Q) (P + Q)) :
    jeffreys P Q ≤ ∫ x, |llr P Q x| ∂(P + Q) := by
  have hP := hint.left_of_add_measure
  have hQ := hint.right_of_add_measure
  have habsP : Integrable (fun x => |llr P Q x|) P := hP.abs
  have habsQ : Integrable (fun x => |llr P Q x|) Q := hQ.abs
  rw [jeffreys_eq_integral_llr_sub hPQ hQP, integral_add_measure habsP habsQ]
  have h1 : ∫ x, llr P Q x ∂P ≤ ∫ x, |llr P Q x| ∂P :=
    integral_mono hP habsP fun x => le_abs_self _
  have h2 : -∫ x, llr P Q x ∂Q ≤ ∫ x, |llr P Q x| ∂Q := by
    rw [← integral_neg]
    exact integral_mono hQ.neg habsQ fun x => neg_le_abs _
  linarith

/-! ## Bounded positive comparisons -/

/-- Total-variation distance in the supremum-over-events convention. -/
def tvDist (P Q : Measure ℕ) : ℝ := ⨆ A : Set ℕ, |(P A).toReal - (Q A).toReal|

theorem signedMass_eq_zero (P Q : Measure ℕ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (P Set.univ).toReal - (Q Set.univ).toReal = 0 := by
  simp

theorem tvDist_le_one (P Q : Measure ℕ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    tvDist P Q ≤ 1 := by
  refine ciSup_le fun A => ?_
  have hP : (P A).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P) (s := A))
  have hQ : (Q A).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := Q) (s := A))
  have hP0 : (0 : ℝ) ≤ (P A).toReal := ENNReal.toReal_nonneg
  have hQ0 : (0 : ℝ) ≤ (Q A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- Hellinger affinity of two laws on a countable space. -/
def hellingerAffinity {α : Type*} [MeasurableSpace α] (P Q : Measure α) : ℝ :=
  ∑' a : α, Real.sqrt ((P {a}).toReal * (Q {a}).toReal)

/-- Squared Hellinger distance. -/
def hellingerSq {α : Type*} [MeasurableSpace α] (P Q : Measure α) : ℝ :=
  2 - 2 * hellingerAffinity P Q

/-- **Exact Hellinger affinity of two Poisson formations.** -/
theorem hellingerAffinity_poissonMeasure (a b : ℝ≥0) :
    hellingerAffinity Po(a) Po(b)
      = Real.exp (-((Real.sqrt (a : ℝ) - Real.sqrt (b : ℝ)) ^ 2) / 2) := by
  have ha : (0 : ℝ) ≤ (a : ℝ) := a.2
  have hb : (0 : ℝ) ≤ (b : ℝ) := b.2
  have hterm : ∀ n : ℕ, Real.sqrt ((Po(a) {n}).toReal * (Po(b) {n}).toReal)
      = Real.exp (-((a : ℝ) + (b : ℝ)) / 2) *
        (Real.sqrt ((a : ℝ) * (b : ℝ)) ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [poissonMeasure_singleton_toReal, poissonMeasure_singleton_toReal]
    have hsq : (Real.exp (-((a : ℝ) + (b : ℝ)) / 2) *
        (Real.sqrt ((a : ℝ) * (b : ℝ)) ^ n / (n.factorial : ℝ))) ^ 2
        = Real.exp (-(a : ℝ)) * (a : ℝ) ^ n / (n.factorial : ℝ) *
          (Real.exp (-(b : ℝ)) * (b : ℝ) ^ n / (n.factorial : ℝ)) := by
      rw [mul_pow, div_pow, ← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (by positivity),
        ← Real.exp_nat_mul, mul_pow]
      push_cast
      rw [show (2 : ℝ) * (-((a : ℝ) + (b : ℝ)) / 2) = -(a : ℝ) + -(b : ℝ) from by ring,
        Real.exp_add]
      field_simp
    rw [← hsq, Real.sqrt_sq (by positivity)]
  rw [hellingerAffinity]
  rw [tsum_congr hterm, tsum_mul_left, (hasSum_pow_div_factorial _).tsum_eq, ← Real.exp_add]
  congr 1
  have hprod : Real.sqrt ((a : ℝ) * (b : ℝ)) = Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ) :=
    Real.sqrt_mul ha _
  have hA : Real.sqrt (a : ℝ) ^ 2 = (a : ℝ) := Real.sq_sqrt ha
  have hB : Real.sqrt (b : ℝ) ^ 2 = (b : ℝ) := Real.sq_sqrt hb
  rw [hprod]
  nlinarith [hA, hB]

theorem hellingerAffinity_superposition (α β : ℝ≥0) (m : ℕ) :
    hellingerAffinity Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β)
      = Real.exp (-((m : ℝ) * (Real.sqrt (α : ℝ) - Real.sqrt (β : ℝ)) ^ 2) / 2) := by
  rw [hellingerAffinity_poissonMeasure]
  congr 1
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hα : (0 : ℝ) ≤ (α : ℝ) := α.2
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.2
  have hA : Real.sqrt (((m : ℝ≥0) * α : ℝ≥0) : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (α : ℝ) := by
    rw [coe_depthRate]
    exact Real.sqrt_mul hm _
  have hB : Real.sqrt (((m : ℝ≥0) * β : ℝ≥0) : ℝ) = Real.sqrt (m : ℝ) * Real.sqrt (β : ℝ) := by
    rw [coe_depthRate]
    exact Real.sqrt_mul hm _
  rw [hA, hB, ← mul_sub, mul_pow, Real.sq_sqrt hm]

/-- **Hellinger saturation.**  For distinct rates the squared Hellinger distance saturates at its
maximum under superposition. -/
theorem tendsto_hellingerSq_superposition {α β : ℝ≥0} (hαβ : α ≠ β) :
    Tendsto (fun m : ℕ => hellingerSq Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β)) atTop (𝓝 2) := by
  have hα : (0 : ℝ) ≤ (α : ℝ) := α.2
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.2
  have hne : Real.sqrt (α : ℝ) ≠ Real.sqrt (β : ℝ) := by
    intro h
    exact hαβ (NNReal.coe_injective (by
      have := congrArg (fun x : ℝ => x ^ 2) h
      simpa [Real.sq_sqrt hα, Real.sq_sqrt hβ] using this))
  have hgap : (0 : ℝ) < (Real.sqrt (α : ℝ) - Real.sqrt (β : ℝ)) ^ 2 / 2 := by
    have : Real.sqrt (α : ℝ) - Real.sqrt (β : ℝ) ≠ 0 := sub_ne_zero.2 hne
    positivity
  have haff : Tendsto (fun m : ℕ =>
      hellingerAffinity Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β)) atTop (𝓝 0) := by
    refine (tendsto_expNegDepth hgap).congr fun m => ?_
    rw [hellingerAffinity_superposition]
    congr 1
    ring
  have := (tendsto_const_nhds (x := (2 : ℝ)) (f := atTop (α := ℕ))).sub (haff.const_mul 2)
  simpa [hellingerSq] using this

/-! ## Jensen--Shannon boundedness -/

/-- The Jensen--Shannon mixture. -/
def jsMixture (P Q : Measure ℕ) : Measure ℕ := (2 : ℝ≥0∞)⁻¹ • (P + Q)

/-- Jensen--Shannon divergence. -/
def jensenShannon (P Q : Measure ℕ) : ℝ :=
  (klDiv P (jsMixture P Q)).toReal / 2 + (klDiv Q (jsMixture P Q)).toReal / 2

theorem jsMixture_comm (P Q : Measure ℕ) : jsMixture P Q = jsMixture Q P := by
  rw [jsMixture, jsMixture, add_comm]

theorem jsMixture_singleton (P Q : Measure ℕ) (n : ℕ) :
    jsMixture P Q {n} = (2 : ℝ≥0∞)⁻¹ * (P {n} + Q {n}) := by
  rw [jsMixture, Measure.smul_apply, Measure.add_apply, smul_eq_mul]

theorem jsMixture_singleton_toReal (P Q : Measure ℕ) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (n : ℕ) :
    (jsMixture P Q {n}).toReal = ((P {n}).toReal + (Q {n}).toReal) / 2 := by
  rw [jsMixture_singleton, ENNReal.toReal_mul, ENNReal.toReal_add (measure_ne_top P _)
    (measure_ne_top Q _)]
  simp [div_eq_inv_mul]

instance isProbabilityMeasure_jsMixture (P Q : Measure ℕ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : IsProbabilityMeasure (jsMixture P Q) := by
  constructor
  rw [jsMixture, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul]
  rw [show (1 : ℝ≥0∞) + 1 = 2 from by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem jsMixture_singleton_ne_zero {P Q : Measure ℕ} (hP0 : ∀ n, P {n} ≠ 0) (n : ℕ) :
    jsMixture P Q {n} ≠ 0 := by
  rw [jsMixture_singleton, ne_eq, mul_eq_zero, not_or]
  refine ⟨by simp, ?_⟩
  intro h
  exact hP0 n (by simpa using (add_eq_zero.1 h).1)

theorem mul_abs_log_le_two {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) : r * |Real.log r| ≤ 2 := by
  rcases le_or_gt r 1 with h | h
  · rw [abs_of_nonpos (Real.log_nonpos hr.le h)]
    have hinv : Real.log r⁻¹ ≤ r⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at hinv
    have hcancel : r * (r⁻¹ - 1) = 1 - r := by field_simp
    nlinarith [hinv, hcancel]
  · rw [abs_of_nonneg (Real.log_nonneg h.le)]
    have hlog : Real.log r ≤ Real.log 2 := Real.log_le_log hr hr2
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    nlinarith

theorem summable_js_abs_logRatio {P Q : Measure ℕ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP0 : ∀ n, P {n} ≠ 0) :
    Summable fun n : ℕ => (P {n}).toReal *
      |Real.log ((P {n}).toReal / (jsMixture P Q {n}).toReal)| := by
  have hM : Summable fun n : ℕ => (2 : ℝ) * (jsMixture P Q {n}).toReal :=
    ((hasSum_measure_singleton_toReal (jsMixture P Q)).summable).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hM
  have hMpos : (0 : ℝ) < (jsMixture P Q {n}).toReal := by
    rw [jsMixture_singleton_toReal]
    have hPn : (0 : ℝ) < (P {n}).toReal := ENNReal.toReal_pos (hP0 n) (measure_ne_top P _)
    have hQn : (0 : ℝ) ≤ (Q {n}).toReal := ENNReal.toReal_nonneg
    linarith
  have hPn : (0 : ℝ) < (P {n}).toReal := ENNReal.toReal_pos (hP0 n) (measure_ne_top P _)
  set r : ℝ := (P {n}).toReal / (jsMixture P Q {n}).toReal with hr
  have hrpos : 0 < r := by positivity
  have hrle : r ≤ 2 := by
    rw [hr, div_le_iff₀ hMpos, jsMixture_singleton_toReal]
    have hQn : (0 : ℝ) ≤ (Q {n}).toReal := ENNReal.toReal_nonneg
    linarith
  have hkey := mul_abs_log_le_two hrpos hrle
  have hval : (P {n}).toReal = r * (jsMixture P Q {n}).toReal := by
    rw [hr]
    field_simp
  rw [hval]
  nlinarith [hkey, hMpos.le, abs_nonneg (Real.log r)]

/-- **Jensen--Shannon divergence is uniformly bounded.** -/
theorem toReal_klDiv_jsMixture_le {P Q : Measure ℕ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP0 : ∀ n, P {n} ≠ 0) :
    (klDiv P (jsMixture P Q)).toReal ≤ Real.log 2 := by
  have hsum := summable_js_abs_logRatio (P := P) (Q := Q) hP0
  rw [toReal_klDiv_of_countable (fun n => jsMixture_singleton_ne_zero hP0 n) hsum]
  have hsig : Summable fun n : ℕ => (P {n}).toReal *
      Real.log ((P {n}).toReal / (jsMixture P Q {n}).toReal) := by
    refine Summable.of_abs (hsum.congr fun n => ?_)
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have hmaj : Summable fun n : ℕ => (P {n}).toReal * Real.log 2 :=
    (hasSum_measure_singleton_toReal P).summable.mul_right _
  have hle : ∀ n : ℕ, (P {n}).toReal * Real.log ((P {n}).toReal / (jsMixture P Q {n}).toReal)
      ≤ (P {n}).toReal * Real.log 2 := by
    intro n
    have hMpos : (0 : ℝ) < (jsMixture P Q {n}).toReal := by
      rw [jsMixture_singleton_toReal]
      have hPn : (0 : ℝ) < (P {n}).toReal := ENNReal.toReal_pos (hP0 n) (measure_ne_top P _)
      have hQn : (0 : ℝ) ≤ (Q {n}).toReal := ENNReal.toReal_nonneg
      linarith
    have hPn : (0 : ℝ) < (P {n}).toReal := ENNReal.toReal_pos (hP0 n) (measure_ne_top P _)
    have hrle : (P {n}).toReal / (jsMixture P Q {n}).toReal ≤ 2 := by
      rw [div_le_iff₀ hMpos, jsMixture_singleton_toReal]
      have hQn : (0 : ℝ) ≤ (Q {n}).toReal := ENNReal.toReal_nonneg
      linarith
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hrle) hPn.le
  calc ∑' n : ℕ, (P {n}).toReal * Real.log ((P {n}).toReal / (jsMixture P Q {n}).toReal)
      ≤ ∑' n : ℕ, (P {n}).toReal * Real.log 2 := hsig.tsum_le_tsum hle hmaj
    _ = Real.log 2 := by
        rw [tsum_mul_right, (hasSum_measure_singleton_toReal P).tsum_eq, one_mul]

theorem jensenShannon_le_log_two {P Q : Measure ℕ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP0 : ∀ n, P {n} ≠ 0) (hQ0 : ∀ n, Q {n} ≠ 0) :
    jensenShannon P Q ≤ Real.log 2 := by
  have h1 := toReal_klDiv_jsMixture_le (P := P) (Q := Q) hP0
  have h2 := toReal_klDiv_jsMixture_le (P := Q) (Q := P) hQ0
  rw [← jsMixture_comm] at h2
  rw [jensenShannon]
  linarith

/-! ## The formed modular cocycle -/

theorem poissonMeasure_absolutelyContinuous {a b : ℝ≥0} (hb : 0 < b) : Po(a) ≪ Po(b) :=
  absolutelyContinuous_of_forall_singleton_ne_zero fun n => poissonMeasure_singleton_ne_zero hb n

/-- The formed modular cocycle of the depth-`m` superposition pair. -/
def superpositionCocycle (α β : ℝ≥0) (m : ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log ((α : ℝ) / (β : ℝ)) - (m : ℝ) * ((α : ℝ) - (β : ℝ))

/-- **The formed modular cocycle is affine in the count.** -/
theorem llr_superposition_ae {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) {m : ℕ} (hm : 0 < m) :
    llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β)
      =ᵐ[Po((m : ℝ≥0) * α) + Po((m : ℝ≥0) * β)] superpositionCocycle α β m := by
  have hma := depthRate_pos hα hm
  have hmb := depthRate_pos hβ hm
  have hm' : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hβ' : ((β : ℝ)) ≠ 0 := ne_of_gt (show (0 : ℝ) < (β : ℝ) from hβ)
  have hA : llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β)
      =ᵐ[Po((m : ℝ≥0) * α)] superpositionCocycle α β m := by
    filter_upwards [llr_eq_log_singleton_ratio (P := Po((m : ℝ≥0) * β))
      (Q := Po((m : ℝ≥0) * α)) (fun n => poissonMeasure_singleton_ne_zero hmb n)] with n hn
    rw [hn, log_poissonMeasure_singleton_ratio hma hmb, superpositionCocycle, coe_depthRate,
      coe_depthRate,
      show (m : ℝ) * (α : ℝ) / ((m : ℝ) * (β : ℝ)) = (α : ℝ) / (β : ℝ) from by field_simp]
    ring
  have hB : llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β)
      =ᵐ[Po((m : ℝ≥0) * β)] superpositionCocycle α β m :=
    (poissonMeasure_absolutelyContinuous hma).ae_le hA
  exact ae_add_measure_iff.2 ⟨hA, hB⟩

theorem integrable_superpositionCocycle (α β : ℝ≥0) (m : ℕ) (c : ℝ≥0) :
    Integrable (superpositionCocycle α β m) Po(c) := by
  refine integrable_of_summable_singleton_weighted _ ?_
  have hw : Summable fun n : ℕ => (Po(c) {n}).toReal := by
    refine ((hasSum_one_poissonMeasure c).congr_fun fun n =>
      poissonMeasure_singleton_toReal c n).summable
  have hwn : Summable fun n : ℕ => (Po(c) {n}).toReal * (n : ℝ) :=
    (hasSum_poissonMeasure_mean c).summable
  have := summable_weight_mul_abs_affine (w := fun n : ℕ => (Po(c) {n}).toReal)
    (fun n => ENNReal.toReal_nonneg) hw hwn
    (-((m : ℝ) * ((α : ℝ) - (β : ℝ)))) (Real.log ((α : ℝ) / (β : ℝ)))
  refine this.congr fun n => ?_
  congr 1
  rw [superpositionCocycle]
  ring_nf

theorem integrable_llr_superposition {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) {m : ℕ} (hm : 0 < m) :
    Integrable (llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β))
      (Po((m : ℝ≥0) * α) + Po((m : ℝ≥0) * β)) := by
  refine (Integrable.add_measure (integrable_superpositionCocycle α β m ((m : ℝ≥0) * α))
    (integrable_superpositionCocycle α β m ((m : ℝ≥0) * β))).congr ?_
  exact (llr_superposition_ae hα hβ hm).symm

theorem jeffreys_superposition {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) {m : ℕ} (hm : 0 < m) :
    jeffreys Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) = (m : ℝ) * rateJeffreys α β := by
  rw [jeffreys, ← poissonJeffreys, formation_conservation hα hβ hm, formationBooleanWork,
    formationHistoryWork, poissonJeffreys_eq_boolean_add_hidden (depthRate_pos hα hm)
      (depthRate_pos hβ hm)]

/-- **Uniform modular conservation selects equal rates.** -/
theorem eq_of_bddAbove_modular_mass {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) {K : ℝ}
    (hbdd : ∀ m : ℕ, 0 < m →
      ∫ n, |llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n|
        ∂(Po((m : ℝ≥0) * α) + Po((m : ℝ≥0) * β)) ≤ K) :
    α = β := by
  by_contra hne
  have hC := rateJeffreys_pos_of_ne hα hβ hne
  obtain ⟨m, hm⟩ := exists_nat_gt (K / rateJeffreys α β)
  have hm0 : 0 < max m 1 := lt_of_lt_of_le one_pos (le_max_right m 1)
  have hmle : (m : ℝ) ≤ ((max m 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left m 1
  have hle := (jeffreys_le_integral_abs_llr
    (poissonMeasure_absolutelyContinuous (depthRate_pos hβ hm0))
    (poissonMeasure_absolutelyContinuous (depthRate_pos hα hm0))
    (integrable_llr_superposition hα hβ hm0)).trans (hbdd _ hm0)
  rw [jeffreys_superposition hα hβ hm0] at hle
  have : K / rateJeffreys α β < ((max m 1 : ℕ) : ℝ) := lt_of_lt_of_le hm hmle
  rw [div_lt_iff₀ hC] at this
  nlinarith [hle, this, hC]

/-- **Bounded modular oscillation also selects equal rates.** -/
theorem eq_of_bdd_modular_oscillation {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) {C : ℝ}
    (c : ℕ → ℝ)
    (hosc : ∀ m : ℕ, 0 < m → ∀ᵐ n ∂(Po((m : ℝ≥0) * α) + Po((m : ℝ≥0) * β)),
      |llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n - c m| ≤ C) :
    α = β := by
  by_contra hne
  have hC := rateJeffreys_pos_of_ne hα hβ hne
  have hkey : ∀ m : ℕ, 0 < m → (m : ℝ) * rateJeffreys α β ≤ 2 * C := by
    intro m hm
    have hint := integrable_llr_superposition hα hβ hm
    have hintP := hint.left_of_add_measure
    have hintQ := hint.right_of_add_measure
    have hoscP : ∀ᵐ n ∂Po((m : ℝ≥0) * α),
        |llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n - c m| ≤ C :=
      (ae_add_measure_iff.1 (hosc m hm)).1
    have hoscQ : ∀ᵐ n ∂Po((m : ℝ≥0) * β),
        |llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n - c m| ≤ C :=
      (ae_add_measure_iff.1 (hosc m hm)).2
    have hshiftP : |∫ n, (llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n - c m)
        ∂Po((m : ℝ≥0) * α)| ≤ C := by
      refine abs_integral_le_integral_abs.trans ?_
      have hb := integral_mono_of_nonneg (Filter.Eventually.of_forall fun n => abs_nonneg _)
        (integrable_const C) hoscP
      simpa using hb
    have hshiftQ : |∫ n, (llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n - c m)
        ∂Po((m : ℝ≥0) * β)| ≤ C := by
      refine abs_integral_le_integral_abs.trans ?_
      have hb := integral_mono_of_nonneg (Filter.Eventually.of_forall fun n => abs_nonneg _)
        (integrable_const C) hoscQ
      simpa using hb
    have hP : ∫ n, (llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n - c m) ∂Po((m : ℝ≥0) * α)
        = (∫ n, llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n ∂Po((m : ℝ≥0) * α)) - c m := by
      rw [integral_sub hintP (integrable_const _)]
      simp
    have hQ : ∫ n, (llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n - c m) ∂Po((m : ℝ≥0) * β)
        = (∫ n, llr Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) n ∂Po((m : ℝ≥0) * β)) - c m := by
      rw [integral_sub hintQ (integrable_const _)]
      simp
    rw [hP] at hshiftP
    rw [hQ] at hshiftQ
    have hJ := jeffreys_eq_integral_llr_sub
      (poissonMeasure_absolutelyContinuous (depthRate_pos hβ hm))
      (poissonMeasure_absolutelyContinuous (depthRate_pos hα hm))
    rw [jeffreys_superposition hα hβ hm] at hJ
    rw [hJ]
    rw [abs_le] at hshiftP hshiftQ
    linarith [hshiftP.1, hshiftP.2, hshiftQ.1, hshiftQ.2]
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * C / rateJeffreys α β)
  have hm0 : 0 < max m 1 := lt_of_lt_of_le one_pos (le_max_right m 1)
  have hmle : (m : ℝ) ≤ ((max m 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left m 1
  have hbig := hkey _ hm0
  have : 2 * C / rateJeffreys α β < ((max m 1 : ℕ) : ℝ) := lt_of_lt_of_le hm hmle
  rw [div_lt_iff₀ hC] at this
  nlinarith [hbig, this, hC]

/-! ## The blindness capstone -/

/-- Total-variation norm of the signed difference of two countable laws. -/
def tvNorm (P Q : Measure ℕ) : ℝ := ∑' n : ℕ, |(P {n}).toReal - (Q {n}).toReal|

theorem tvNorm_le_two (P Q : Measure ℕ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    tvNorm P Q ≤ 2 := by
  have hP := hasSum_measure_singleton_toReal P
  have hQ := hasSum_measure_singleton_toReal Q
  have hmaj : HasSum (fun n : ℕ => (P {n}).toReal + (Q {n}).toReal) 2 := by
    have h := hP.add hQ
    rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
    exact h
  have hle : ∀ n : ℕ, |(P {n}).toReal - (Q {n}).toReal| ≤ (P {n}).toReal + (Q {n}).toReal := by
    intro n
    have h1 : (0 : ℝ) ≤ (P {n}).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) ≤ (Q {n}).toReal := ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have hsum : Summable fun n : ℕ => |(P {n}).toReal - (Q {n}).toReal| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hle hmaj.summable
  calc tvNorm P Q ≤ ∑' n : ℕ, ((P {n}).toReal + (Q {n}).toReal) :=
        hsum.tsum_le_tsum hle hmaj.summable
    _ = 2 := hmaj.tsum_eq

/-- **Bounded positive quantities cannot control hidden formation.**  For distinct rates the signed
mass vanishes, total variation and Jensen--Shannon divergence stay bounded, Hellinger distance
saturates and Boolean occupancy work vanishes, while the recovered-history action diverges. -/
theorem boundedConservation_blindness {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) (hne : α ≠ β) :
    (∀ m : ℕ, (Po((m : ℝ≥0) * α) Set.univ).toReal
        - (Po((m : ℝ≥0) * β) Set.univ).toReal = 0)
      ∧ (∀ m : ℕ, tvDist Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) ≤ 1)
      ∧ (∀ m : ℕ, tvNorm Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) ≤ 2)
      ∧ (∀ m : ℕ, 0 < m →
          jensenShannon Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β) ≤ Real.log 2)
      ∧ Tendsto (fun m : ℕ => hellingerSq Po((m : ℝ≥0) * α) Po((m : ℝ≥0) * β)) atTop (𝓝 2)
      ∧ Tendsto (fun m : ℕ => formationBooleanWork α β m) atTop (𝓝 0)
      ∧ Tendsto (fun m : ℕ => formationHistoryWork α β m) atTop atTop := by
  refine ⟨fun m => signedMass_eq_zero _ _, fun m => tvDist_le_one _ _, fun m => tvNorm_le_two _ _,
    fun m hm => ?_, tendsto_hellingerSq_superposition hne,
    tendsto_formationBooleanWork_zero hα hβ, tendsto_formationHistoryWork_atTop hα hβ hne⟩
  exact jensenShannon_le_log_two
    (fun n => poissonMeasure_singleton_ne_zero (depthRate_pos hα hm) n)
    (fun n => poissonMeasure_singleton_ne_zero (depthRate_pos hβ hm) n)

/-- **Reflection parity and zero signed mass are insufficient.**  The reflected signed family has
vanishing total mass, is exactly antisymmetric under aperture reflection and has uniformly bounded
total variation, yet its recovered-history action is unbounded away from the neutral point. -/
theorem reflected_signed_family_insufficient {d : ℕ} (hd : 1 < d) (p : Nat.Primes) (t : ℝ) :
    (∀ m : ℕ, (Po((m : ℝ≥0) * reflectedSourceRate p t) Set.univ).toReal
        - (Po((m : ℝ≥0) * reflectedSourceRate p (-t)) Set.univ).toReal = 0)
      ∧ (∀ m n : ℕ,
          (Po((m : ℝ≥0) * reflectedSourceRate p (-t)) {n}).toReal
            - (Po((m : ℝ≥0) * reflectedSourceRate p (-(-t))) {n}).toReal
          = -((Po((m : ℝ≥0) * reflectedSourceRate p t) {n}).toReal
            - (Po((m : ℝ≥0) * reflectedSourceRate p (-t)) {n}).toReal))
      ∧ (∀ m : ℕ, tvNorm Po((m : ℝ≥0) * reflectedSourceRate p t)
          Po((m : ℝ≥0) * reflectedSourceRate p (-t)) ≤ 2)
      ∧ (completedOrbitAction d (reflectedSourceRate p t) (reflectedSourceRate p (-t)) = ⊤
          ↔ t ≠ 0) := by
  refine ⟨fun m => signedMass_eq_zero _ _, fun m n => by rw [neg_neg]; ring,
    fun m => tvNorm_le_two _ _, ?_⟩
  have h := completedOrbitAction_reflectedSourceRate_ne_top_iff hd p t
  constructor
  · intro htop hzero
    exact (h.2 hzero) htop
  · intro hne
    by_contra hfin
    exact hne (h.1 hfin)

end

end GaloisForLFunctions.HTGeometry
