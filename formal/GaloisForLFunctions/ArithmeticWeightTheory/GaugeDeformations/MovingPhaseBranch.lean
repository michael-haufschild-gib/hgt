import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ExponentialPrimePhase
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeLogarithmRenormalization

/-!
# The first moving branch of exponentially damped Liouville phases

Separating the first phase term exposes a shifted prime logarithm.
Its singularity at `s=1-t` has exponent `iπ`; the remaining factor
is analytic and nonzero for sufficiently small positive `t`.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The analytic exponent left after removing the first moving branch. -/
def exponentialPhaseBranchExponent (t : ℝ) (s : ℂ) : ℂ :=
  -(Real.pi : ℂ) * I * primeLogRegularPart (s + (t : ℂ)) +
    exponentialPhasePrimeRemainder t s + hullRem s (twist (exponentialPhaseGauge t)) -
      hullRem s (twist 0)

/-- The nonvanishing factor accompanying the first moving branch. -/
def exponentialPhaseBranchUnit (t : ℝ) (s : ℂ) : ℂ :=
  zetaResidueFactor s * Complex.exp (exponentialPhaseBranchExponent t s)


private theorem prime_decay_eq (p : Nat.Primes) (s : ℂ) :
    Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) = (p : ℂ) ^ (-s) := by
  simpa only [primeFrequency, neg_mul] using prime_cexp_decay p s

private theorem summable_exponentialPhase_prime_terms {t : ℝ} {s : ℂ}
    (hs : 1 < s.re + t) :
    Summable (fun p : Nat.Primes => (twist (exponentialPhaseGauge t) p - 1) *
      (p : ℂ) ^ (-s)) := by
  apply Summable.of_norm
  convert exponentialPhase_prime_summability hs using 1
  funext p
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]

/-- The canonical logarithm is the sum of its first-prime part and higher-power remainders. -/
theorem jointExponent_exponentialPhase_eq {t : ℝ} {s : ℂ}
    (hs : 1 < s.re + t) (hhalf : 1 / 2 < s.re) :
    jointDeformationExponent exponentialPrimePhase ((t : ℂ), s) =
      deformationExponent (exponentialPhaseGauge t) s := by
  have hp := summable_exponentialPhase_prime_terms hs
  have hx := summable_localRem (s := s) (norm_twist_prime (exponentialPhaseGauge t)) hhalf
  have h0 := summable_localRem (s := s) (norm_twist_prime 0) hhalf
  rw [jointDeformationExponent, deformationExponent, deformationPrimeSum, hullRem, hullRem,
    ← hp.tsum_add hx, ← (hp.add hx).tsum_sub h0]
  apply tsum_congr
  intro p
  simp only [jointEulerChange, prime_cexp_decay, exponentialPrimePhase_eq_twist,
    localRem, eulerVar, powCoeff, twist_trivial, mul_one]
  rw [mul_comm ((p : ℂ) ^ (-s)) (twist (exponentialPhaseGauge t) p)]
  ring

/-- The sole first shifted prime logarithm has coefficient `-iπ`. -/
theorem deformationPrimeSum_exponentialPhase_split {t : ℝ} (ht : 0 ≤ t) {s : ℂ}
    (hs : 1 < s.re + t) :
    deformationPrimeSum (exponentialPhaseGauge t) s =
      -(Real.pi : ℂ) * I * coronaPrimeZeta (s + (t : ℂ)) +
        exponentialPhasePrimeRemainder t s := by
  have hst : 1 < (s + (t : ℂ)).re := by simpa only [Complex.add_re, Complex.ofReal_re] using hs
  have hf := (summable_coronaPrimeEigenvalue hst).mul_left (-(Real.pi : ℂ) * I)
  have hr := summable_exponentialPhasePrimeRemainder ht (s := s)
    (by linarith only [hs, ht])
  rw [deformationPrimeSum, exponentialPhasePrimeRemainder, coronaPrimeZeta,
    ← tsum_mul_left, ← hf.tsum_add hr]
  apply tsum_congr
  intro p
  rw [← exponentialPrimePhase_eq_twist]
  simp only [coronaPrimeEigenvalue]
  rw [← prime_decay_eq p s, ← prime_decay_eq p (s + (t : ℂ))]
  rw [show -(s + (t : ℂ)) * (Real.log (p : ℝ) : ℂ) =
    -(t : ℂ) * (Real.log (p : ℝ) : ℂ) + -s * (Real.log (p : ℝ) : ℂ) by ring,
    Complex.exp_add]
  ring

/-- The branch exponent is analytic at its moving singularity. -/
theorem analyticAt_exponentialPhaseBranchExponent {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    AnalyticAt ℂ (exponentialPhaseBranchExponent t) (1 - (t : ℂ)) := by
  have hreg : AnalyticAt ℂ primeLogRegularPart ((1 - (t : ℂ)) + (t : ℂ)) := by
    simpa only [sub_add_cancel] using analyticAt_primeLogRegularPart_one
  have hshift : AnalyticAt ℂ (fun s : ℂ => s + (t : ℂ)) (1 - (t : ℂ)) :=
    analyticAt_id.add analyticAt_const
  have hhalf : (1 : ℂ) - (t : ℂ) ∈ rightHalf := by
    change 1 / 2 < (1 : ℂ).re - (t : ℂ).re
    simp only [Complex.one_re, Complex.ofReal_re]
    linarith only [ht2]
  have hr := analyticOnNhd_exponentialPhasePrimeRemainder ht.le (1 - (t : ℂ))
    (by change 1 < (1 : ℂ).re - (t : ℂ).re + 2 * t
        simp only [Complex.one_re, Complex.ofReal_re]
        linarith only [ht])
  exact (((analyticAt_const.mul (hreg.comp hshift)).add hr).add
    (analyticOnNhd_hullRem (norm_twist_prime (exponentialPhaseGauge t)) _ hhalf)).sub
      (analyticOnNhd_hullRem (norm_twist_prime 0) _ hhalf)

theorem analyticAt_exponentialPhaseBranchUnit {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    AnalyticAt ℂ (exponentialPhaseBranchUnit t) (1 - (t : ℂ)) :=
  (differentiable_zetaResidueFactor.analyticAt _).mul
    (analyticAt_exponentialPhaseBranchExponent ht ht2).cexp


/-- One spectral radius works for the exact moving-branch factorization. -/
theorem exponentialPhase_moving_branch_factorization :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 ≤ t → ∀ s : ℂ,
      ‖s - (1 - (t : ℂ))‖ < r → 1 < s.re + t → 1 / 2 < s.re →
        jointGaugeRegularization exponentialPrimePhase ((t : ℂ), s) =
          exponentialPhaseBranchUnit t s *
            Complex.exp ((Real.pi : ℂ) * I * Complex.log (s - (1 - (t : ℂ)))) := by
  obtain ⟨r, hr, _, hprime⟩ := exists_primeLogRegularPart_germ
  refine ⟨r, hr, ?_⟩
  intro t ht s hsr hs hhalf
  have harg : s + (t : ℂ) - 1 = s - (1 - (t : ℂ)) := by ring
  have hball : s + (t : ℂ) ∈ ball 1 r := by
    simpa only [mem_ball, dist_eq_norm, harg] using hsr
  have hp := hprime (s + (t : ℂ)) hball
    (by simpa only [Complex.add_re, Complex.ofReal_re] using hs)
  have hH : deformationExponent (exponentialPhaseGauge t) s =
      exponentialPhaseBranchExponent t s +
        (Real.pi : ℂ) * I * Complex.log (s - (1 - (t : ℂ))) := by
    rw [deformationExponent, deformationPrimeSum_exponentialPhase_split ht hs,
      exponentialPhaseBranchExponent]
    rw [harg] at hp
    linear_combination -(Real.pi : ℂ) * I * hp
  rw [jointGaugeRegularization, jointExponent_exponentialPhase_eq hs hhalf, hH,
    Complex.exp_add, exponentialPhaseBranchUnit]
  ring


/-- For small positive parameters the branch factor is an analytic unit. -/
theorem exponentialPhase_moving_branch_unit :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t < T →
      AnalyticAt ℂ (exponentialPhaseBranchUnit t) (1 - (t : ℂ)) ∧
        exponentialPhaseBranchUnit t (1 - (t : ℂ)) ≠ 0 := by
  have hZ : ∀ᶠ s in 𝓝 (1 : ℂ), zetaResidueFactor s ≠ 0 :=
    (differentiable_zetaResidueFactor.continuous.continuousAt).eventually_ne
      (by rw [zetaResidueFactor_one]; exact one_ne_zero)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hZ
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), ?_⟩
  intro t ht htT
  have htε : t < ε := lt_of_lt_of_le htT (min_le_left _ _)
  have ht2 : t < 1 / 2 := lt_of_lt_of_le htT (min_le_right _ _)
  refine ⟨analyticAt_exponentialPhaseBranchUnit ht ht2, ?_⟩
  have hdist : dist (1 - (t : ℂ)) 1 < ε := by
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    exact htε
  exact mul_ne_zero (hb hdist) (Complex.exp_ne_zero _)

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
