import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmStokesFirstTraceMomentDualityWall
import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindow
import GaloisForLFunctions.RHTower.PolarPrimeRegularity

/-!
# First-trace sharp-polar continuation and its signedness wall

P-G140 proves that the positive Stokes moment carrying the Hedenmalm first trace is not ordinarily
summable in the critical chamber.  The bounded-variation prime-window corpus supplies a canonical
scalar polar counterterm.  This file welds that counterterm directly to P-G139's continued
valuation-one current.

The weld is exact: the full sharp prime-polar observable is a first-trace-only observable plus the
analytic higher-valuation tail.  Hence punctured regularity of the first-trace-only observable on
the shifted right half-plane is equivalent to RH.  This removes higher valuations from the
regularity gate without inserting divisor data.

The same theorem exposes a decisive positivity failure.  For the literal dyadic prime-polar
coefficient, the sample at `n=1` is positive and the sample at `n=3` is negative.  Thus the
canonical scalar finite part solves the divergence by leaving the atomic positive cone already at
finite scale.  It cannot be the missing passivity producer.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Literal finite signedness witness -/

/-- Exact first dyadic prime-polar sample. -/
theorem sharpPrimePolarCoefficient_dyadic_one :
    sharpPrimePolarCoefficient (Real.log 2) (Real.log 1) =
      4 * (1 - (Real.sqrt 2)⁻¹) := by
  have h := sharpPrimePolarCoefficient_logTwo_logSample (n := 1) (by norm_num)
  norm_num [ArithmeticFunction.vonMangoldt] at h ⊢
  exact h

/-- The first dyadic prime-polar sample is strictly positive. -/
theorem sharpPrimePolarCoefficient_dyadic_one_pos :
    0 < sharpPrimePolarCoefficient (Real.log 2) (Real.log 1) := by
  rw [sharpPrimePolarCoefficient_dyadic_one]
  have hsqrt : 1 < Real.sqrt 2 := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
  have hinv : (Real.sqrt 2)⁻¹ < 1 :=
    (inv_lt_one₀ (Real.sqrt_pos.mpr (by norm_num))).mpr hsqrt
  positivity

/-- Exact third dyadic prime-polar sample. -/
theorem sharpPrimePolarCoefficient_dyadic_three :
    sharpPrimePolarCoefficient (Real.log 2) (Real.log 3) =
      4 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt 3 -
        2 * ((2 : ℝ) ^ (-1 / 2 : ℝ) * Real.log 2 +
          (3 : ℝ) ^ (-1 / 2 : ℝ) * Real.log 3) := by
  have h := sharpPrimePolarCoefficient_logTwo_logSample (n := 3) (by norm_num)
  norm_num [Finset.sum_Ioc_succ_top, ArithmeticFunction.vonMangoldt] at h ⊢
  simp [Nat.prime_two.isPrimePow, Nat.prime_three.isPrimePow] at h
  convert h using 1
  all_goals norm_num

/-- The third dyadic prime-polar sample is strictly negative. -/
theorem sharpPrimePolarCoefficient_dyadic_three_neg :
    sharpPrimePolarCoefficient (Real.log 2) (Real.log 3) < 0 := by
  rw [sharpPrimePolarCoefficient_dyadic_three]
  have hpow2 : (2 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow]
  have hpow3 : (3 : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt 3)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow]
  rw [hpow2, hpow3]
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hs2lt : Real.sqrt 2 < 17 / 12 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hs3lt : Real.sqrt 3 < 26 / 15 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hinv2 : 12 / 17 < (Real.sqrt 2)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt hs2pos hs2lt
  have hinv3 : 15 / 26 < (Real.sqrt 3)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt hs3pos hs3lt
  have hs2one : 1 < Real.sqrt 2 := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2)
  have hinv2lt : (Real.sqrt 2)⁻¹ < 1 := (inv_lt_one₀ hs2pos).mpr hs2one
  have hApos : 0 < 1 - (Real.sqrt 2)⁻¹ := sub_pos.mpr hinv2lt
  have hA : 1 - (Real.sqrt 2)⁻¹ < 5 / 17 := by linarith
  have hpolar :
      4 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt 3 <
        4 * (5 / 17) * (26 / 15) := by
    have hmul :
        (1 - (Real.sqrt 2)⁻¹) * Real.sqrt 3 <
          (5 / 17) * (26 / 15) :=
      mul_lt_mul hA hs3lt.le hs3pos (by norm_num)
    nlinarith
  have hlog2 : 2 / 3 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog3 : 1 < Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have hprime2 :
      (2 / 3) * (12 / 17) < Real.log 2 * (Real.sqrt 2)⁻¹ :=
    mul_lt_mul hlog2 hinv2.le (by norm_num) (Real.log_pos (by norm_num)).le
  have hprime3 :
      1 * (15 / 26) < Real.log 3 * (Real.sqrt 3)⁻¹ :=
    mul_lt_mul hlog3 hinv3.le (by norm_num) (Real.log_pos (by norm_num)).le
  have hcompare :
      4 * (5 / 17 : ℝ) * (26 / 15) <
        2 * ((2 / 3) * (12 / 17) + 1 * (15 / 26)) := by norm_num
  nlinarith [hpolar, hprime2, hprime3, hcompare]

/-- Closed finite witness that canonical dyadic polar renormalization is neither nonnegative nor
nonpositive. -/
theorem sharpPrimePolarCoefficient_dyadic_signed :
    (∃ x : ℝ, 0 < sharpPrimePolarCoefficient (Real.log 2) x) ∧
      (∃ x : ℝ, sharpPrimePolarCoefficient (Real.log 2) x < 0) :=
  ⟨⟨Real.log 1, sharpPrimePolarCoefficient_dyadic_one_pos⟩,
    ⟨Real.log 3, sharpPrimePolarCoefficient_dyadic_three_neg⟩⟩

/-! ## Exact first-trace polar continuation -/

/-- Canonical sharp polar finite part with only P-G139's continued valuation-one current retained.
The parameter is the shifted prime-window Dirichlet coordinate. -/
def squarefreeFirstTraceSharpPolarObservable (L : ℝ) (a : ℂ) : ℂ :=
  4 * (1 - (Real.exp (-(L / 2)) : ℂ)) * riemannZeta (a - 1 / 2) +
    (-2 * rectangularWindowAmplitude L (a - 1)) *
      squarefreeFirstTraceContinuedCurrent (a - 1 / 2)

/-- **No higher-valuation leakage.** The canonical full sharp prime-polar observable is exactly the
first-trace polar finite part plus the analytic higher-valuation correction. -/
theorem polarPrimeObservable_sharp_eq_firstTrace_add_higherValuation
    (L : ℝ) (a : ℂ) :
    polarPrimeObservable (4 * (1 - (Real.exp (-(L / 2)) : ℂ)))
        (fun z => -2 * rectangularWindowAmplitude L (z - 1)) a =
      squarefreeFirstTraceSharpPolarObservable L a +
        (-2 * rectangularWindowAmplitude L (a - 1)) *
          xiPrimeLogHigherValuation (a - 1 / 2) := by
  simp only [polarPrimeObservable, windowObservable,
    squarefreeFirstTraceSharpPolarObservable,
    squarefreeFirstTraceContinuedCurrent, xiPrimeLogDirichletContinuation,
    infinitePrimeFlux, logDeriv, Pi.div_apply]
  ring

/-- Punctured regularity of the first-trace-only sharp polar finite part on the shifted right
half-plane is exactly RH.  Higher valuations do not affect this gate because they are analytic on
`Re(a-1/2)>1/2`. -/
theorem riemannHypothesis_iff_squarefreeFirstTraceSharpPolar_regular
    (L : ℝ) (hL : 0 < L) :
    RiemannHypothesis ↔
      ∀ a : ℂ, 1 < a.re → ∃ M : ℂ,
        Tendsto (squarefreeFirstTraceSharpPolarObservable L) (𝓝[≠] a) (𝓝 M) := by
  rw [RH_iff_sharpWindowPolar_regular L hL]
  refine forall_congr' fun a => imp_congr_right fun ha => ?_
  let C : ℂ → ℂ := fun z =>
    (-2 * rectangularWindowAmplitude L (z - 1)) *
      xiPrimeLogHigherValuation (z - 1 / 2)
  have hhalf : 1 / 2 < (a - 1 / 2).re := by
    rw [Complex.sub_re]
    norm_num
    linarith
  have hshift : ContinuousAt (fun z : ℂ => z - 1 / 2) a :=
    continuousAt_id.sub continuousAt_const
  have hhigher : ContinuousAt
      (fun z : ℂ => xiPrimeLogHigherValuation (z - 1 / 2)) a :=
    ContinuousAt.comp' (f := fun z : ℂ => z - 1 / 2)
      (differentiableAt_xiPrimeLogHigherValuation_of_half_lt_re hhalf).continuousAt
      hshift
  have hC : ContinuousAt C a := by
    dsimp only [C]
    exact (((rectangularWindowAmplitude_differentiable L).continuous.comp
      (continuous_id.sub continuous_const)).const_mul (-2)).continuousAt.mul hhigher
  have heq :
      (fun z : ℂ =>
        4 * (1 - (Real.exp (-(L / 2)) : ℂ)) * riemannZeta (z - 1 / 2) +
          -2 * rectangularWindowAmplitude L (z - 1) *
            (-deriv riemannZeta (z - 1 / 2) / riemannZeta (z - 1 / 2))) =
        fun z => squarefreeFirstTraceSharpPolarObservable L z + C z := by
    funext z
    dsimp only [C]
    simpa only [polarPrimeObservable, windowObservable] using
      polarPrimeObservable_sharp_eq_firstTrace_add_higherValuation L z
  rw [heq]
  exact exists_tendsto_add_continuousAt_iff hC

/-- Closed dyadic Route-P criterion: no width premise remains. -/
theorem riemannHypothesis_iff_dyadicSquarefreeFirstTraceSharpPolar_regular :
    RiemannHypothesis ↔
      ∀ a : ℂ, 1 < a.re → ∃ M : ℂ,
        Tendsto (squarefreeFirstTraceSharpPolarObservable (Real.log 2))
          (𝓝[≠] a) (𝓝 M) :=
  riemannHypothesis_iff_squarefreeFirstTraceSharpPolar_regular
    (Real.log 2) (Real.log_pos (by norm_num))

end

end RHTower
