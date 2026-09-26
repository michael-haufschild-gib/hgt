import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherBoundary

/-!
# Integrated prime--Gamma conservation identity

Exponential source decay makes the forward and reflected prime pairings
integrable over the whole real line. Hence the positive boundary charge is
an ordinary convergent half-line integral of the literal arithmetic exchange,
not merely a limit of finite-interval identities. The whole-line exchange
vanishes by reflection, while the positive half-line exchange equals the
strictly positive prime-link charge.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace RHTower.ThetaSourceWard

/-- Pairing the complete prime operator with another theta source is integrable. -/
theorem integrable_thetaPrimePairing (S T : ThetaSource) :
    Integrable (fun x : ℝ => (T.k x : ℂ) * fullPrimeSource S x) := by
  have hi := fullPrimeSource_laplace_integrable S (w := 1) (by norm_num)
  obtain ⟨C, _, hb⟩ := exists_bound_laplaceIntegrand_one T
  have hc : Continuous (fun x : ℝ => (T.k x : ℂ) * Complex.exp (-(x : ℂ))) :=
    (Complex.continuous_ofReal.comp T.cont).mul
      (Complex.continuous_exp.comp Complex.continuous_ofReal.neg)
  have hbound : ∀ x : ℝ, ‖(T.k x : ℂ) * Complex.exp (-(x : ℂ))‖ ≤ C := by
    intro x
    simpa only [laplaceIntegrand, T.even', Complex.ofReal_neg, one_mul] using hb (-x)
  have h := hi.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall hbound)
  apply h.congr
  filter_upwards with x
  simp only [one_mul]
  calc
    (fullPrimeSource S x * Complex.exp (x : ℂ)) *
        ((T.k x : ℂ) * Complex.exp (-(x : ℂ))) =
      (T.k x : ℂ) * fullPrimeSource S x *
        (Complex.exp (x : ℂ) * Complex.exp (-(x : ℂ))) := by ring
    _ = _ := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

theorem integrable_fullPrimeShiftWardDivergence (S T : ThetaSource) :
    Integrable (fullPrimeShiftWardDivergence S T) := by
  apply ((integrable_thetaPrimePairing S T).sub
    (integrable_thetaPrimePairing T S).comp_neg).congr
  filter_upwards with x
  simp only [Pi.sub_apply, S.even', fullPrimeShiftWardDivergence]

/-- Convergent total exchange is the skew pairing of the two complete prime sources. -/
theorem integral_fullPrimeShiftWardDivergence (S T : ThetaSource) :
    (∫ x : ℝ, fullPrimeShiftWardDivergence S T x) =
      (∫ x : ℝ, (T.k x : ℂ) * fullPrimeSource S x) -
        ∫ x : ℝ, (S.k x : ℂ) * fullPrimeSource T x := by
  have hneg : Integrable (fun x : ℝ => (S.k x : ℂ) * fullPrimeSource T (-x)) := by
    simpa only [S.even'] using (integrable_thetaPrimePairing T S).comp_neg
  change (∫ x : ℝ, (T.k x : ℂ) * fullPrimeSource S x -
    (S.k x : ℂ) * fullPrimeSource T (-x)) = _
  rw [integral_sub (integrable_thetaPrimePairing S T) hneg]
  congr 1
  simpa only [S.even'] using
    integral_neg_eq_self (fun x : ℝ => (S.k x : ℂ) * fullPrimeSource T x) volume

/-- The current at any cutoff is exactly the negative of its remaining divergence. -/
theorem integral_fullPrimeShiftWardDivergence_Ioi (S T : ThetaSource) (a : ℝ) :
    (∫ x in Set.Ioi a, fullPrimeShiftWardDivergence S T x) =
      -fullPrimeShiftNoetherCurrent S T a := by
  simpa only [zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hasDerivAt_fullPrimeShiftNoetherCurrent S T x)
    (integrable_fullPrimeShiftWardDivergence S T).integrableOn
    (tendsto_fullPrimeShiftNoetherCurrent_atTop S T)

/-- Multiplication work minus the Gamma/pole imbalance of the actual arithmetic source. -/
def thetaNoetherExchange (x : ℝ) : ℂ :=
  2 * (x : ℂ) * (thetaCuspFullSource x : ℂ) ^ 2 -
    (thetaCuspFullSource x : ℂ) *
      (thetaArchimedeanShiftSource x - thetaArchimedeanShiftSource (-x))

theorem thetaNoetherExchange_eq (x : ℝ) :
    thetaNoetherExchange x =
      -fullPrimeShiftWardDivergence thetaCuspTiltSource thetaCuspTiltSource x := by
  rw [completeTheta_primeShiftWard_balance, thetaNoetherExchange]
  ring

theorem integrable_thetaNoetherExchange : Integrable thetaNoetherExchange := by
  apply (integrable_fullPrimeShiftWardDivergence thetaCuspTiltSource thetaCuspTiltSource).neg.congr
  filter_upwards with x
  exact (thetaNoetherExchange_eq x).symm

/-- Every right tail carries exactly the positive arithmetic current at its cutoff. -/
theorem integral_thetaNoetherExchange_Ioi_from (a : ℝ) :
    (∫ x in Set.Ioi a, thetaNoetherExchange x) =
      fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource a := by
  simp only [thetaNoetherExchange_eq, integral_neg,
    integral_fullPrimeShiftWardDivergence_Ioi, neg_neg]

/-- Exact convergent arithmetic conservation identity on the positive half-line. -/
theorem integral_thetaNoetherExchange_Ioi :
    (∫ x in Set.Ioi (0 : ℝ), thetaNoetherExchange x) =
      fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource 0 :=
  integral_thetaNoetherExchange_Ioi_from 0

theorem integral_thetaNoetherExchange_Ioi_from_re_pos (a : ℝ) :
    0 < (∫ x in Set.Ioi a, thetaNoetherExchange x).re := by
  rw [integral_thetaNoetherExchange_Ioi_from]
  exact fullPrimeShiftNoetherCurrent_re_pos thetaCuspTiltSource thetaCuspTiltSource a

theorem integral_thetaNoetherExchange_Ioi_re_pos :
    0 < (∫ x in Set.Ioi (0 : ℝ), thetaNoetherExchange x).re := by
  rw [integral_thetaNoetherExchange_Ioi]
  exact fullPrimeShiftNoetherCurrent_re_pos thetaCuspTiltSource thetaCuspTiltSource 0

/-- No finite accumulated exchange reaches the strictly positive boundary charge. -/
theorem integral_thetaNoetherExchange_finite_re_lt_charge (a : ℝ) :
    (∫ x in (0 : ℝ)..a, thetaNoetherExchange x).re <
      (fullPrimeShiftNoetherCurrent thetaCuspTiltSource thetaCuspTiltSource 0).re := by
  have he := intervalIntegral.integral_interval_add_Ioi
    (a := (0 : ℝ)) (b := a) integrable_thetaNoetherExchange.integrableOn
    integrable_thetaNoetherExchange.integrableOn
  rw [integral_thetaNoetherExchange_Ioi] at he
  rw [← he, Complex.add_re]
  exact lt_add_of_pos_right _ (integral_thetaNoetherExchange_Ioi_from_re_pos a)

/-- The full-line exchange cancels, while each half-line retains the boundary charge. -/
theorem integral_thetaNoetherExchange : (∫ x : ℝ, thetaNoetherExchange x) = 0 := by
  simp only [thetaNoetherExchange_eq, integral_neg,
    integral_fullPrimeShiftWardDivergence, sub_self, neg_zero]

end RHTower.ThetaSourceWard
