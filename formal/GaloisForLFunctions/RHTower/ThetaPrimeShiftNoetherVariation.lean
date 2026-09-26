import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherIntegrated
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Local variations of the complete arithmetic shift action

The discrete prime index and continuous source coordinate carry an
integrable link density. Bounded continuous local reciprocal scalings have
an integrable first variation. Transposing every link identifies this
variation with the literal prime--Gamma Noether exchange.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower.ThetaSourceWard

abbrev thetaPrimeLinkMeasure : Measure (ℕ × ℝ) := Measure.count.prod volume

def thetaPrimeLinkDensity (S T : ThetaSource) (p : ℕ × ℝ) : ℂ :=
  primeShiftActionDensity p.1 (fun x => (T.k x : ℂ)) (fun x => (S.k x : ℂ)) p.2

theorem thetaPrimeLinkDensity_eq (S T : ThetaSource) (n : ℕ) (x : ℝ) :
    thetaPrimeLinkDensity S T (n, x) = (T.k x : ℂ) * primeSourceTerm S n x := by
  unfold thetaPrimeLinkDensity primeShiftActionDensity primeSourceTerm
  ring

theorem continuous_thetaPrimeLinkDensity (S T : ThetaSource) :
    Continuous (thetaPrimeLinkDensity S T) := by
  have hc : Continuous primeCoefficient := continuous_of_discreteTopology
  have hl : Continuous (fun n : ℕ => Real.log n) := continuous_of_discreteTopology
  unfold thetaPrimeLinkDensity primeShiftActionDensity
  exact ((hc.comp continuous_fst).mul
    ((Complex.continuous_ofReal.comp T.cont).comp continuous_snd)).mul
      ((Complex.continuous_ofReal.comp S.cont).comp
        (continuous_snd.add (hl.comp continuous_fst)))

/-- Absolute integrability retains every prime power and the whole source line. -/
theorem integrable_thetaPrimeLinkDensity (S T : ThetaSource) :
    Integrable (thetaPrimeLinkDensity S T) thetaPrimeLinkMeasure := by
  have hc : Continuous (fun p : ℕ × ℝ =>
      primeSourceTerm S p.1 p.2 * Complex.exp ((1 : ℂ) * p.2)) := by
    have hcoef : Continuous primeCoefficient := continuous_of_discreteTopology
    have hlog : Continuous (fun n : ℕ => Real.log n) := continuous_of_discreteTopology
    unfold primeSourceTerm
    exact ((hcoef.comp continuous_fst).mul
      ((Complex.continuous_ofReal.comp S.cont).comp
        (continuous_snd.add (hlog.comp continuous_fst)))).mul (by fun_prop)
  have hp : Integrable (fun p : ℕ × ℝ =>
      primeSourceTerm S p.1 p.2 * Complex.exp ((1 : ℂ) * p.2)) thetaPrimeLinkMeasure := by
    rw [integrable_prod_iff hc.aestronglyMeasurable]
    constructor
    · exact Eventually.of_forall (integrable_primeSourceTerm_laplace S 1)
    · rw [integrable_count_iff]
      simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using
        summable_integral_norm_primeSourceTerm_laplace S (w := 1) (by norm_num)
  obtain ⟨C, _, hC⟩ := exists_bound_laplaceIntegrand_one T
  have hb : ∀ p : ℕ × ℝ, ‖(T.k p.2 : ℂ) * Complex.exp (-(p.2 : ℂ))‖ ≤ C := by
    intro p
    simpa only [laplaceIntegrand, T.even', Complex.ofReal_neg, one_mul] using hC (-p.2)
  have hcont : Continuous (fun p : ℕ × ℝ =>
      (T.k p.2 : ℂ) * Complex.exp (-(p.2 : ℂ))) :=
    ((Complex.continuous_ofReal.comp T.cont).mul
      (Complex.continuous_exp.comp Complex.continuous_ofReal.neg)).comp continuous_snd
  apply (hp.mul_bdd hcont.aestronglyMeasurable (Eventually.of_forall hb)).congr
  filter_upwards with p
  rw [show p = (p.1, p.2) from rfl, thetaPrimeLinkDensity_eq]
  simp only [one_mul]
  calc
    (primeSourceTerm S p.1 p.2 * Complex.exp (p.2 : ℂ)) *
        ((T.k p.2 : ℂ) * Complex.exp (-(p.2 : ℂ))) =
      (T.k p.2 : ℂ) * primeSourceTerm S p.1 p.2 *
        (Complex.exp (p.2 : ℂ) * Complex.exp (-(p.2 : ℂ))) := by ring
    _ = _ := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

def noetherReflectedProfile (chi : ℝ →ᵇ ℂ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => chi (-x))
    (chi.continuous.comp continuous_neg) ‖chi‖ (fun x => chi.norm_coe_le_norm (-x))

theorem integrable_thetaPrimeLink_sourceTest (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (fun p : ℕ × ℝ => chi p.2 * thetaPrimeLinkDensity S T p)
      thetaPrimeLinkMeasure :=
  (integrable_thetaPrimeLinkDensity S T).bdd_mul
    (chi.continuous.comp continuous_snd).aestronglyMeasurable
    (Eventually.of_forall fun p => chi.norm_coe_le_norm p.2)

theorem integrable_thetaPrimeLink_targetTest (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (fun p : ℕ × ℝ => chi (p.2 + Real.log p.1) * thetaPrimeLinkDensity S T p)
      thetaPrimeLinkMeasure := by
  have hl : Continuous (fun n : ℕ => Real.log n) := continuous_of_discreteTopology
  exact (integrable_thetaPrimeLinkDensity S T).bdd_mul
    (chi.continuous.comp (continuous_snd.add (hl.comp continuous_fst))).aestronglyMeasurable
    (Eventually.of_forall fun p => chi.norm_coe_le_norm (p.2 + Real.log p.1))

/-- The source marginal is the complete von Mangoldt shift operator. -/
theorem integral_thetaPrimeLink_sourceTest (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    (∫ p, chi p.2 * thetaPrimeLinkDensity S T p ∂thetaPrimeLinkMeasure) =
      ∫ x : ℝ, chi x * ((T.k x : ℂ) * fullPrimeSource S x) := by
  have hi := integrable_thetaPrimeLink_sourceTest S T chi
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with x hx
  rw [integral_countable hx]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul,
    thetaPrimeLinkDensity_eq, fullPrimeSource, tsum_mul_left]

/-- Transposition reverses every local scaling increment. -/
theorem integral_thetaPrimeLink_target_row (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) (n : ℕ) :
    (∫ x : ℝ, chi (x + Real.log n) * thetaPrimeLinkDensity S T (n, x)) =
      ∫ x : ℝ, noetherReflectedProfile chi x * thetaPrimeLinkDensity T S (n, x) := by
  have he : (∫ x : ℝ, chi (x + Real.log n) * thetaPrimeLinkDensity S T (n, x)) =
      ∫ x : ℝ, chi x * ((S.k x : ℂ) * primeSourceTerm T n (-x)) := by
    calc
      _ = ∫ x : ℝ, primeShiftActionDensity n (fun y => (T.k y : ℂ))
          (fun y => chi y * (S.k y : ℂ)) x := by
        apply integral_congr_ae
        filter_upwards with x
        unfold thetaPrimeLinkDensity primeShiftActionDensity
        ring
      _ = _ := by
        rw [primeShiftActionDensity_transpose]
        apply integral_congr_ae
        filter_upwards with x
        have ht : T.k (x - Real.log n) = T.k (-x + Real.log n) := by
          rw [← T.even' (x - Real.log n)]
          congr 1
          ring
        simp only [primeSourceTerm, ht]
        ring
  rw [he]
  symm
  simpa only [noetherReflectedProfile, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    thetaPrimeLinkDensity_eq, S.even', neg_neg] using
    integral_neg_eq_self (fun x : ℝ => chi x * ((S.k x : ℂ) * primeSourceTerm T n (-x))) volume

theorem integral_thetaPrimeLink_targetTest (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    (∫ p, chi (p.2 + Real.log p.1) * thetaPrimeLinkDensity S T p ∂thetaPrimeLinkMeasure) =
      ∫ x : ℝ, chi (-x) * ((S.k x : ℂ) * fullPrimeSource T x) := by
  rw [integral_prod _ (integrable_thetaPrimeLink_targetTest S T chi)]
  simp only [integral_thetaPrimeLink_target_row]
  rw [← integral_prod _ (integrable_thetaPrimeLink_sourceTest T S (noetherReflectedProfile chi)),
    integral_thetaPrimeLink_sourceTest]
  rfl

/-- The integrated local first variation of the full reciprocal prime action. -/
def thetaPrimeLocalResponse (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) : ℂ :=
  ∫ p, (chi (p.2 + Real.log p.1) - chi p.2) * thetaPrimeLinkDensity S T p
    ∂thetaPrimeLinkMeasure

theorem integrable_thetaPrimeLocalResponse (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (fun p : ℕ × ℝ =>
      (chi (p.2 + Real.log p.1) - chi p.2) * thetaPrimeLinkDensity S T p)
      thetaPrimeLinkMeasure := by
  apply ((integrable_thetaPrimeLink_targetTest S T chi).sub
    (integrable_thetaPrimeLink_sourceTest S T chi)).congr
  filter_upwards with p
  exact (sub_mul _ _ _).symm

/-- The complete local action response equals the source/adjoint Ward pairing. -/
theorem thetaPrimeLocalResponse_eq (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    thetaPrimeLocalResponse S T chi =
      ∫ x : ℝ, chi x * (-fullPrimeShiftWardDivergence S T x) := by
  have hS := (integrable_thetaPrimePairing S T).bdd_mul chi.continuous.aestronglyMeasurable
    (Eventually.of_forall chi.norm_coe_le_norm)
  have hT := (integrable_thetaPrimePairing T S).comp_neg.bdd_mul
    chi.continuous.aestronglyMeasurable (Eventually.of_forall chi.norm_coe_le_norm)
  have hT' : Integrable (fun x : ℝ => chi x * ((S.k x : ℂ) * fullPrimeSource T (-x))) := by
    simpa only [S.even'] using hT
  have he : (∫ x : ℝ, chi (-x) * ((S.k x : ℂ) * fullPrimeSource T x)) =
      ∫ x : ℝ, chi x * ((S.k x : ℂ) * fullPrimeSource T (-x)) := by
    simpa only [S.even', neg_neg] using
      integral_neg_eq_self (fun x : ℝ => chi x * ((S.k x : ℂ) * fullPrimeSource T (-x))) volume
  unfold thetaPrimeLocalResponse
  simp only [sub_mul]
  rw [integral_sub (integrable_thetaPrimeLink_targetTest S T chi)
    (integrable_thetaPrimeLink_sourceTest S T chi),
    integral_thetaPrimeLink_targetTest, integral_thetaPrimeLink_sourceTest, he,
    ← integral_sub hT' hS]
  apply integral_congr_ae
  filter_upwards with x
  unfold fullPrimeShiftWardDivergence
  ring

/-- Actual arithmetic action variation, including the full Gamma and pole exchange. -/
theorem thetaPrimeLocalResponse_actual (chi : ℝ →ᵇ ℂ) :
    thetaPrimeLocalResponse thetaCuspTiltSource thetaCuspTiltSource chi =
      ∫ x : ℝ, chi x * thetaNoetherExchange x := by
  rw [thetaPrimeLocalResponse_eq]
  simp only [thetaNoetherExchange_eq]

end RHTower.ThetaSourceWard
