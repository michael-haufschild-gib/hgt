import GaloisForLFunctions.RHTower.SourceGammaFiniteHalfDensityTensorPhaseNoGo

open scoped BigOperators ENNReal
open Filter Topology

#check Summable.tsum_mul_left
#check Summable.tsum_mul_right
#check Summable.mul_left
#check Summable.mul_right
#check Summable.add
#check Summable.sub
#check Summable.tsum_add
#check Summable.tsum_sub
#check summable_iff_cauchySeq_finset
#check Summable.hasSum
#check Summable.le_tsum
#check Finset.single_le_sum
#check tsum_nonneg
#check Real.rpow_add
#check Real.rpow_neg
#check Real.strictMono_rpow_of_base_gt_one
#check Summable.of_nonneg_of_le
#check summable_of_sum_le
#check tsum_eq_single

theorem positive_reciprocal_mean_rigidity
    (w a : ℕ → ℝ) (A : ℝ)
    (hw0 : ∀ n, 0 ≤ w n)
    (ha0 : ∀ n, 0 < a n)
    (hA0 : 0 < A)
    (hw : Summable w)
    (hwa : Summable (fun n => w n * a n))
    (hwia : Summable (fun n => w n / a n))
    (hw_sum : ∑' n, w n = 1)
    (hwa_sum : ∑' n, w n * a n = A)
    (hwia_sum : ∑' n, w n / a n = A⁻¹) :
    ∀ n, w n ≠ 0 → a n = A := by
  let d : ℕ → ℝ := fun n =>
    (w n * a n) * A⁻¹ + A * (w n / a n) - 2 * w n
  have hs1 : Summable (fun n => (w n * a n) * A⁻¹) := hwa.mul_right A⁻¹
  have hs2 : Summable (fun n => A * (w n / a n)) := hwia.mul_left A
  have hs3 : Summable (fun n => 2 * w n) := hw.mul_left 2
  have hd : Summable d := by
    exact (hs1.add hs2).sub hs3
  have hd_nonneg : ∀ n, 0 ≤ d n := by
    intro n
    have hident : d n = w n * (a n - A) ^ 2 / (a n * A) := by
      dsimp [d]
      field_simp [ne_of_gt (ha0 n), ne_of_gt hA0]
      ring
    rw [hident]
    exact div_nonneg (mul_nonneg (hw0 n) (sq_nonneg _))
      (le_of_lt (mul_pos (ha0 n) hA0))
  have hd_sum : ∑' n, d n = 0 := by
    calc
      ∑' n, d n =
          (∑' n, (w n * a n) * A⁻¹) +
            (∑' n, A * (w n / a n)) -
              ∑' n, 2 * w n := by
                rw [Summable.tsum_sub (hs1.add hs2) hs3,
                  Summable.tsum_add hs1 hs2]
      _ = A * A⁻¹ + A * A⁻¹ - 2 * 1 := by
        rw [hwa.tsum_mul_right, hwia.tsum_mul_left, hw.tsum_mul_left,
          hwa_sum, hwia_sum, hw_sum]
      _ = 0 := by
        field_simp [ne_of_gt hA0]
        norm_num
  intro n hwn
  have hdn_le : d n ≤ 0 := by
    simpa [hd_sum] using hd.le_tsum n (fun j _ => hd_nonneg j)
  have hdn : d n = 0 := le_antisymm hdn_le (hd_nonneg n)
  have hident : d n = w n * (a n - A) ^ 2 / (a n * A) := by
    dsimp [d]
    field_simp [ne_of_gt (ha0 n), ne_of_gt hA0]
    ring
  rw [hident] at hdn
  have hden : a n * A ≠ 0 := ne_of_gt (mul_pos (ha0 n) hA0)
  have hnum : w n * (a n - A) ^ 2 = 0 :=
    (div_eq_zero_iff.mp hdn).resolve_right hden
  have hsquare : (a n - A) ^ 2 = 0 :=
    (mul_eq_zero.mp hnum).resolve_left hwn
  nlinarith

namespace RHTower

noncomputable section

/-- Positive probability mixture of physical tensor degrees fitting the Gamma-Ward radial law at
a grade and its reflection. -/
def CountablePositiveHalfDensityDegreeMixtureFitsReflectedGammaRadialLaw
    (t : ℝ) (w : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ w n) ∧
    Summable w ∧
    (∑' n, w n) = 1 ∧
    Summable (fun n => w n * ((3 : ℝ) / 2) ^ ((n : ℝ) * t / 2)) ∧
    (∑' n, w n * ((3 : ℝ) / 2) ^ ((n : ℝ) * t / 2)) =
      ((3 : ℝ) / 2) ^ (2 * t) ∧
    Summable (fun n => w n / ((3 : ℝ) / 2) ^ ((n : ℝ) * t / 2)) ∧
    (∑' n, w n / ((3 : ℝ) / 2) ^ ((n : ℝ) * t / 2)) =
      (((3 : ℝ) / 2) ^ (2 * t))⁻¹

/-- Reflected Gamma-Ward matching makes every active degree equal four away from the critical
grade. -/
theorem countablePositiveHalfDensityDegreeMixture_support_four
    {t : ℝ} {w : ℕ → ℝ}
    (hfit : CountablePositiveHalfDensityDegreeMixtureFitsReflectedGammaRadialLaw t w)
    (ht : t ≠ 0) :
    ∀ n, w n ≠ 0 → n = 4 := by
  rcases hfit with ⟨hw0, hw, hw_sum, hwa, hwa_sum, hwia, hwia_sum⟩
  intro n hwn
  have haeq : ((3 : ℝ) / 2) ^ ((n : ℝ) * t / 2) =
      ((3 : ℝ) / 2) ^ (2 * t) :=
    positive_reciprocal_mean_rigidity
      w (fun m => ((3 : ℝ) / 2) ^ ((m : ℝ) * t / 2))
      (((3 : ℝ) / 2) ^ (2 * t)) hw0
      (fun m => Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (by norm_num) _) hw hwa hwia hw_sum hwa_sum hwia_sum n hwn
  have hexp : (n : ℝ) * t / 2 = 2 * t :=
    (Real.strictMono_rpow_of_base_gt_one
      (by norm_num : (1 : ℝ) < 3 / 2)).injective haeq
  have hmul : ((n : ℝ) - 4) * t = 0 := by
    nlinarith
  have hnreal : (n : ℝ) = 4 := sub_eq_zero.mp
    ((mul_eq_zero.mp hmul).resolve_right ht)
  exact_mod_cast hnreal

/-- Countable positive tensor-degree source law with grade-universal reflected radial matching and
a positive common two-prime phase readout at one actual Xi divisor. -/
def CountablePositiveHalfDensityDegreeMixtureSharedWardProducerAt
    (rho : XiDivisorSupport) (w : ℕ → ℝ) : Prop :=
  (∀ t : ℝ,
    CountablePositiveHalfDensityDegreeMixtureFitsReflectedGammaRadialLaw t w) ∧
  ∃ c : ℝ, 0 < c ∧
    (∑' n, (w n : ℂ) *
      ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase 2 rho n) = (c : ℂ) ∧
    (∑' n, (w n : ℂ) *
      ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase 3 rho n) = (c : ℂ)

/-- **Countable positive-mixture route-class kill.**  Grade-universal reflected radial matching
forces support at degree four; its full two-prime phase is already impossible on every actual Xi
divisor. -/
theorem not_countablePositiveHalfDensityDegreeMixtureSharedWardProducerAt
    (rho : XiDivisorSupport) (w : ℕ → ℝ) :
    ¬ CountablePositiveHalfDensityDegreeMixtureSharedWardProducerAt rho w := by
  rintro ⟨hradial, c, hc, htwo, hthree⟩
  have hfit := hradial 1
  have hsupport : ∀ n, w n ≠ 0 → n = 4 :=
    countablePositiveHalfDensityDegreeMixture_support_four hfit one_ne_zero
  have hw_sum : (∑' n, w n) = 1 := hfit.2.2.1
  have hw4 : w 4 = 1 := by
    calc
      w 4 = ∑' n, w n := by
        symm
        exact tsum_eq_single 4 fun n hn => by
          by_contra hwn
          exact hn (hsupport n hwn)
      _ = 1 := hw_sum
  have hphase (p : ℕ) :
      (∑' n, (w n : ℂ) *
        ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase p rho n) =
        ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase p rho 4 := by
    calc
      (∑' n, (w n : ℂ) *
          ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase p rho n) =
          (w 4 : ℂ) *
            ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase p rho 4 := by
        exact tsum_eq_single 4 fun n hn => by
          have hwn : w n = 0 := by
            by_contra hwn
            exact hn (hsupport n hwn)
          simp [hwn]
      _ = ccmRationalAdelicPrimePhysicalHalfDensityTensorPowerPhase p rho 4 := by
        rw [hw4]
        simp
  apply not_primeGammaTwoThreePositiveArchPhysicalHalfDensityTensorPhase rho 4 (by norm_num)
  exact ⟨c, hc, (hphase 2).symm.trans htwo, (hphase 3).symm.trans hthree⟩

/-- Closed classification of the fixed positive countable tensor-mixture source class. -/
def SharedWardCountablePositiveHalfDensityDegreeMixtureRouteKilled : Prop :=
  ∀ (rho : XiDivisorSupport) (w : ℕ → ℝ),
    ¬ CountablePositiveHalfDensityDegreeMixtureSharedWardProducerAt rho w

/-- No fixed countable positive mixture of physical tensor degrees realizes the shared reflected
Gamma-Ward producer interface. -/
theorem sharedWardCountablePositiveHalfDensityDegreeMixtureRouteKilled :
    SharedWardCountablePositiveHalfDensityDegreeMixtureRouteKilled :=
  not_countablePositiveHalfDensityDegreeMixtureSharedWardProducerAt

end

end RHTower
