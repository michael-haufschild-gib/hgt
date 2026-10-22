import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPrimePolarCellProducer
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel

/-!
# Signed control of matched prime--polar currents on actual Gamma heads

The mass-matched cell radius supplies more than coefficient-one transport.  If

`rho_n = 2 arsinh (w_n / (4 exp(log(n)/2)))`,

then the asymmetric current retained by the exact cell producer is bounded by

`|I_n(f)| <= w_n^2 / (4 exp(log(n)/2)) * ||f||^2`.

Since `w_n = Lambda(n) n^(-1/2)`, the right side is dominated by
`Lambda(n) log(n) n^(-3/2) ||f||^2 / 4`, hence is summable.  This is the
quadratic-aperture gain missing from a fixed-light Suzuki split: the actual signed asymmetric
current converges over every prime power without severing it from its prime atom, matched outgoing
polar cell, or literal Gamma-head translation defect.

The module also proves the exact finite-block producer

`prime - matched polar = symmetric same-head residual - Suzuki current`

and a uniform absolute bound for its signed current block.  The even symmetric residual is kept
intact: separating its joint rebate from its offset defect would destroy the remaining cosine
cancellation and is not licensed by this result.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Signed asymmetric current left by the exact mass-matched prime--polar cell. -/
def ccmActualHeadMatchedSuzukiCurrent (n : ℕ) (f : SoninL2) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
      ccmActualHeadTranslationSineCurrent (Real.log n) r f

/-- At every prime power the integrated asymmetric term is literally Suzuki's anti-diagonal
wall-Gram current, with the prime coefficient kept on the left rather than divided away. -/
theorem criticalMellinAtomWeight_mul_matchedSuzukiCurrent_primePower_eq_wallGram
    (f : SoninL2) (p : Nat.Primes) (e : ℕ) :
    criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) *
        ccmActualHeadMatchedSuzukiCurrent (xiGammaEulerValuationNat (p, e)) f =
      ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius
          (xiGammaEulerValuationNat (p, e)),
        Real.exp (Real.log (xiGammaEulerValuationNat (p, e)) / 2) *
          Real.sinh (r / 2) *
          (∫ xi : ℝ,
            4 * (suzukiCriticalWallFieldGramKernel
                  (2 * Real.pi * xi) (-(2 * Real.pi * xi)) p e).im *
              Real.sin (2 * Real.pi * r * xi) *
              ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by
  unfold ccmActualHeadMatchedSuzukiCurrent
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [show criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) *
        (Real.exp (Real.log (xiGammaEulerValuationNat (p, e)) / 2) *
          Real.sinh (r / 2) *
          ccmActualHeadTranslationSineCurrent
            (Real.log (xiGammaEulerValuationNat (p, e))) r f) =
      Real.exp (Real.log (xiGammaEulerValuationNat (p, e)) / 2) *
        Real.sinh (r / 2) *
        (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) *
          ccmActualHeadTranslationSineCurrent
            (Real.log (xiGammaEulerValuationNat (p, e))) r f) by ring,
    criticalMellinAtomWeight_mul_translationSineCurrent_primePower_eq_suzuki]

lemma abs_ccmActualHeadTranslationSineCurrent_le
    (s r : ℝ) (f : SoninL2) :
    |ccmActualHeadTranslationSineCurrent s r f| ≤ 4 * ‖f‖ ^ 2 := by
  unfold ccmActualHeadTranslationSineCurrent
  rw [abs_sub_le_iff]
  have hp0 : 0 ≤ ccmActualHeadTranslationDefect (s + r) f := by
    unfold ccmActualHeadTranslationDefect
    positivity
  have hm0 : 0 ≤ ccmActualHeadTranslationDefect (s - r) f := by
    unfold ccmActualHeadTranslationDefect
    positivity
  have hp := ccmActualHeadTranslationDefect_le (s + r) f
  have hm := ccmActualHeadTranslationDefect_le (s - r) f
  constructor <;> linarith

private lemma sqrt_one_add_sq_sub_one_le_half_sq (z : ℝ) :
    Real.sqrt (1 + z ^ 2) - 1 ≤ z ^ 2 / 2 := by
  have hz : 0 ≤ z ^ 2 := sq_nonneg z
  have h1 : (0 : ℝ) ≤ 1 + z ^ 2 := by linarith
  have h2 : (0 : ℝ) ≤ 1 + z ^ 2 / 2 := by linarith
  have hs : Real.sqrt (1 + z ^ 2) ≤ 1 + z ^ 2 / 2 := by
    rw [show (1 : ℝ) + z ^ 2 / 2 = Real.sqrt ((1 + z ^ 2 / 2) ^ 2) by
      rw [Real.sqrt_sq h2]]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [sq_nonneg (z ^ 2)]
  linarith

lemma integral_matched_sinh_coefficient_eq (n : ℕ) :
    (∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
        Real.exp (Real.log n / 2) * Real.sinh (r / 2)) =
      2 * Real.exp (Real.log n / 2) *
        (Real.sqrt
          (1 + (criticalMellinAtomWeight n /
            (4 * Real.exp (Real.log n / 2))) ^ 2) - 1) := by
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (Real.log n / 2)
  let P : ℝ → ℝ := fun r => 2 * A * Real.cosh (r / 2)
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) ρ,
      HasDerivAt P (A * Real.sinh (r / 2)) r := by
    intro r hr
    have hbase := (Real.hasDerivAt_cosh (r / 2)).comp r
      ((hasDerivAt_id r).div_const 2)
    change HasDerivAt (fun x : ℝ => 2 * A * Real.cosh (x / 2)) _ r
    apply (hbase.const_mul (2 * A)).congr_deriv
    ring
  have hint : IntervalIntegrable
      (fun r : ℝ => A * Real.sinh (r / 2)) volume 0 ρ :=
    (by fun_prop : Continuous fun r : ℝ => A * Real.sinh (r / 2)).intervalIntegrable _ _
  rw [show (fun r : ℝ => Real.exp (Real.log n / 2) * Real.sinh (r / 2)) =
      fun r : ℝ => A * Real.sinh (r / 2) by rfl]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [P]
  simp only [zero_div, Real.cosh_zero]
  unfold ρ ccmActualHeadMatchedPrimePolarRadius
  rw [show (2 * Real.arsinh
      (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2)))) / 2 =
      Real.arsinh
        (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2))) by ring,
    Real.cosh_arsinh]
  dsimp only [A]
  ring

theorem abs_ccmActualHeadMatchedSuzukiCurrent_le_quadratic
    (n : ℕ) (f : SoninL2) :
    |ccmActualHeadMatchedSuzukiCurrent n f| ≤
      criticalMellinAtomWeight n ^ 2 /
          (4 * Real.exp (Real.log n / 2)) * ‖f‖ ^ 2 := by
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (Real.log n / 2)
  let w := criticalMellinAtomWeight n
  let S : ℝ → ℝ := fun r =>
    ccmActualHeadTranslationSineCurrent (Real.log n) r f
  have hρ : 0 ≤ ρ := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hA : 0 < A := Real.exp_pos _
  have hw : 0 ≤ w := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  have hScont : Continuous S :=
    continuous_ccmActualHeadTranslationSineCurrent_right (Real.log n) f
  have hcoeffcont : Continuous fun r : ℝ => A * Real.sinh (r / 2) := by fun_prop
  have habsint : IntervalIntegrable (fun r : ℝ => |A * Real.sinh (r / 2) * S r|)
      volume 0 ρ := ((hcoeffcont.mul hScont).abs).intervalIntegrable _ _
  have hmajint : IntervalIntegrable
      (fun r : ℝ => 4 * ‖f‖ ^ 2 * (A * Real.sinh (r / 2)))
      volume 0 ρ := by
    exact ((continuous_const.mul hcoeffcont)).intervalIntegrable _ _
  have hpoint : ∀ r ∈ Icc (0 : ℝ) ρ,
      |A * Real.sinh (r / 2) * S r| ≤
        4 * ‖f‖ ^ 2 * (A * Real.sinh (r / 2)) := by
    intro r hr
    have hr0 : 0 ≤ r / 2 := by linarith [hr.1]
    have hsinh : 0 ≤ Real.sinh (r / 2) := Real.sinh_nonneg_iff.mpr hr0
    have hcoeff : 0 ≤ A * Real.sinh (r / 2) := mul_nonneg hA.le hsinh
    rw [abs_mul, abs_of_nonneg hcoeff]
    simpa only [S, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left
        (abs_ccmActualHeadTranslationSineCurrent_le (Real.log n) r f) hcoeff
  have hinter :
      (∫ r in (0 : ℝ)..ρ, |A * Real.sinh (r / 2) * S r|) ≤
        4 * ‖f‖ ^ 2 * (∫ r in (0 : ℝ)..ρ, A * Real.sinh (r / 2)) := by
    calc
      _ ≤ ∫ r in (0 : ℝ)..ρ,
          4 * ‖f‖ ^ 2 * (A * Real.sinh (r / 2)) :=
        intervalIntegral.integral_mono_on hρ habsint hmajint hpoint
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hsqroot := sqrt_one_add_sq_sub_one_le_half_sq (w / (4 * A))
  have hcoeff :
      (∫ r in (0 : ℝ)..ρ, A * Real.sinh (r / 2)) ≤ w ^ 2 / (16 * A) := by
    rw [show (fun r : ℝ => A * Real.sinh (r / 2)) =
        fun r : ℝ => Real.exp (Real.log n / 2) * Real.sinh (r / 2) by rfl,
      integral_matched_sinh_coefficient_eq]
    change 2 * A *
        (Real.sqrt (1 + (w / (4 * A)) ^ 2) - 1) ≤ w ^ 2 / (16 * A)
    calc
      _ ≤ 2 * A * ((w / (4 * A)) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hsqroot (by positivity)
      _ = w ^ 2 / (16 * A) := by
        field_simp
        ring
  unfold ccmActualHeadMatchedSuzukiCurrent
  change |∫ r in (0 : ℝ)..ρ, A * Real.sinh (r / 2) * S r| ≤ _
  calc
    _ ≤ ∫ r in (0 : ℝ)..ρ, |A * Real.sinh (r / 2) * S r| :=
      intervalIntegral.abs_integral_le_integral_abs hρ
    _ ≤ 4 * ‖f‖ ^ 2 * (∫ r in (0 : ℝ)..ρ, A * Real.sinh (r / 2)) := hinter
    _ ≤ 4 * ‖f‖ ^ 2 * (w ^ 2 / (16 * A)) := by
      gcongr
    _ = criticalMellinAtomWeight n ^ 2 /
          (4 * Real.exp (Real.log n / 2)) * ‖f‖ ^ 2 := by
      dsimp only [w, A]
      field_simp [Real.exp_ne_zero]
      ring

/-- Even remainder left after retaining the asymmetric Suzuki current as a signed term. -/
def ccmActualHeadMatchedSymmetricCellResidual (n : ℕ) (f : SoninL2) : ℝ :=
  ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
    (Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        ccmActualHeadSymmetricTransportRebate (Real.log n) r f -
      2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        ccmActualHeadTranslationDefect r f)

/-- Exact signed split of one completed prime--polar cell on the same actual Gamma head. -/
theorem ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_symmetric_sub_suzuki
    (n : ℕ) (f : SoninL2) :
    criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f =
      ccmActualHeadMatchedSymmetricCellResidual n f -
        ccmActualHeadMatchedSuzukiCurrent n f := by
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (Real.log n / 2)
  let E : ℝ → ℝ := fun r => ccmActualHeadTranslationDefect r f
  let J : ℝ → ℝ := fun r =>
    ccmActualHeadSymmetricTransportRebate (Real.log n) r f
  let S : ℝ → ℝ := fun r =>
    ccmActualHeadTranslationSineCurrent (Real.log n) r f
  have hE : Continuous E := by
    dsimp only [E]
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  have hJ : Continuous J := by
    rw [show J = fun r : ℝ =>
        2 * E (Real.log n) + 2 * E r - E (Real.log n + r) -
          E (Real.log n - r) by
      funext r
      dsimp only [J, E]
      have h := ccmActualHeadTranslationDefect_symmetric_pair_add_rebate
        (Real.log n) r f
      linarith]
    exact (((continuous_const.add (hE.const_mul 2)).sub
      (hE.comp (continuous_const.add continuous_id))).sub
        (hE.comp (continuous_const.sub continuous_id)))
  have hS : Continuous S :=
    continuous_ccmActualHeadTranslationSineCurrent_right (Real.log n) f
  have hsym : IntervalIntegrable (fun r : ℝ =>
      A * Real.cosh (r / 2) * J r -
        2 * A * Real.cosh (r / 2) * E r) volume 0 ρ := by
    exact (by fun_prop : Continuous fun r : ℝ =>
      A * Real.cosh (r / 2) * J r -
        2 * A * Real.cosh (r / 2) * E r).intervalIntegrable _ _
  have hcurrent : IntervalIntegrable (fun r : ℝ =>
      A * Real.sinh (r / 2) * S r) volume 0 ρ := by
    exact (by fun_prop : Continuous fun r : ℝ =>
      A * Real.sinh (r / 2) * S r).intervalIntegrable _ _
  rw [ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_signedResidual]
  unfold ccmActualHeadMatchedSymmetricCellResidual ccmActualHeadMatchedSuzukiCurrent
  change (∫ r in (0 : ℝ)..ρ,
      A * Real.cosh (r / 2) * J r -
        2 * A * Real.cosh (r / 2) * E r -
        A * Real.sinh (r / 2) * S r) =
    (∫ r in (0 : ℝ)..ρ,
      A * Real.cosh (r / 2) * J r -
        2 * A * Real.cosh (r / 2) * E r) -
      ∫ r in (0 : ℝ)..ρ, A * Real.sinh (r / 2) * S r
  exact intervalIntegral.integral_sub hsym hcurrent

/-- Finite completed prime-minus-matched-polar block on one actual Gamma head. -/
def ccmActualHeadMatchedPrimePolarFiniteBlock
    (F : Finset ℕ) (f : SoninL2) : ℝ :=
  ∑ n ∈ F,
    (criticalMellinAtomWeight n *
        ccmActualHeadTranslationDefect (Real.log n) f -
      ccmActualHeadOutgoingPolarSymmetricCell
        (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f)

def ccmActualHeadMatchedSymmetricFiniteBlock
    (F : Finset ℕ) (f : SoninL2) : ℝ :=
  ∑ n ∈ F, ccmActualHeadMatchedSymmetricCellResidual n f

def ccmActualHeadMatchedSuzukiFiniteBlock
    (F : Finset ℕ) (f : SoninL2) : ℝ :=
  ∑ n ∈ F, ccmActualHeadMatchedSuzukiCurrent n f

/-- Finite-block producer retaining prime, polar, Gamma-head rebate, and Suzuki current signs. -/
theorem ccmActualHeadMatchedPrimePolarFiniteBlock_eq_symmetric_sub_suzuki
    (F : Finset ℕ) (f : SoninL2) :
    ccmActualHeadMatchedPrimePolarFiniteBlock F f =
      ccmActualHeadMatchedSymmetricFiniteBlock F f -
        ccmActualHeadMatchedSuzukiFiniteBlock F f := by
  unfold ccmActualHeadMatchedPrimePolarFiniteBlock
    ccmActualHeadMatchedSymmetricFiniteBlock
    ccmActualHeadMatchedSuzukiFiniteBlock
  simp_rw [ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_symmetric_sub_suzuki,
    Finset.sum_sub_distrib]

lemma criticalMellinAtomWeight_sq_div_exp_le_logMajorant (n : ℕ) :
    criticalMellinAtomWeight n ^ 2 /
        Real.exp (Real.log n / 2) ≤
      ((ArithmeticFunction.vonMangoldt n : ℝ) *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [criticalMellinAtomWeight]
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hΛlog := ArithmeticFunction.vonMangoldt_le_log (n := n)
    have he : Real.exp (Real.log n / 2) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hnR]
      congr 1
      ring
    have hpow : ((n : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 /
        ((n : ℝ) ^ (1 / 2 : ℝ)) = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hnR.le]
      rw [← Real.rpow_sub hnR]
      congr 1
      norm_num
    unfold criticalMellinAtomWeight
    rw [he]
    calc
      (((n : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt n) ^ 2 /
          (n : ℝ) ^ (1 / 2 : ℝ) =
        (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
            rw [mul_pow]
            calc
              ((n : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 *
                    (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 /
                  (n : ℝ) ^ (1 / 2 : ℝ) =
                (ArithmeticFunction.vonMangoldt n : ℝ) ^ 2 *
                  (((n : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 /
                    (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
              _ = _ := by rw [hpow]
      _ ≤ ((ArithmeticFunction.vonMangoldt n : ℝ) * Real.log n) *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
        gcongr
        nlinarith
      _ = _ := by ring

theorem summable_ccmActualHeadMatchedSuzukiCurrent (f : SoninL2) :
    Summable fun n : ℕ => ccmActualHeadMatchedSuzukiCurrent n f := by
  have hbase := summable_vonMangoldt_logPow
    (σ := (3 / 2 : ℝ)) (by norm_num) 1
  apply Summable.of_norm_bounded
    ((hbase.mul_left ((1 : ℝ) / 4 * ‖f‖ ^ 2)))
  intro n
  rw [Real.norm_eq_abs]
  refine (abs_ccmActualHeadMatchedSuzukiCurrent_le_quadratic n f).trans ?_
  have hmaj := criticalMellinAtomWeight_sq_div_exp_le_logMajorant n
  have hnonneg : 0 ≤ (1 / 4 : ℝ) * ‖f‖ ^ 2 := by positivity
  calc
    criticalMellinAtomWeight n ^ 2 /
          (4 * Real.exp (Real.log n / 2)) * ‖f‖ ^ 2 =
        ((1 / 4 : ℝ) * ‖f‖ ^ 2) *
          (criticalMellinAtomWeight n ^ 2 /
            Real.exp (Real.log n / 2)) := by ring
    _ ≤ ((1 / 4 : ℝ) * ‖f‖ ^ 2) *
        (((ArithmeticFunction.vonMangoldt n : ℝ) *
          (n : ℝ) ^ (-(3 / 2 : ℝ))) * Real.log n) :=
      mul_le_mul_of_nonneg_left hmaj hnonneg
    _ = (1 / 4 * ‖f‖ ^ 2) *
        (ArithmeticFunction.vonMangoldt n *
          (n : ℝ) ^ (-(3 / 2 : ℝ)) * Real.log n ^ 1) := by ring

/-- Uniform finite-block control of the signed Suzuki current by its quadratic prime aperture. -/
theorem abs_ccmActualHeadMatchedSuzukiFiniteBlock_le
    (F : Finset ℕ) (f : SoninL2) :
    |ccmActualHeadMatchedSuzukiFiniteBlock F f| ≤
      ∑ n ∈ F,
        criticalMellinAtomWeight n ^ 2 /
          (4 * Real.exp (Real.log n / 2)) * ‖f‖ ^ 2 := by
  unfold ccmActualHeadMatchedSuzukiFiniteBlock
  refine (Finset.abs_sum_le_sum_abs
    (fun n => ccmActualHeadMatchedSuzukiCurrent n f) F).trans ?_
  gcongr with n hn
  exact abs_ccmActualHeadMatchedSuzukiCurrent_le_quadratic n f

end RHTower
