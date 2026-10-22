import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalHorizonIntertwiner
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianPrimeGammaCauchyLanding

/-!
# Adaptive prime-normal infinite-depth Gaussian boundary

One ordinary-prime label is retained while its honest prime-normal valuation depth tends to
infinity.  Every finite stage is coefficient augmentation of the literal adaptive codiagonal in
its convergence chamber.  The strict Mobius--theta tail then vanishes pointwise, and the fixed
reflected-Gaussian grade supplies a summable divisor majorant.  The resulting completed Xi columns
converge in norm to the negative reflected-Gaussian horizon vector.

Together with the two-sided prime--Gamma Cauchy landing, this identifies the same Gaussian Xi
vector as a boundary value of both explicit source constructions.  No prime limit, zero selection,
RH premise, or target-defined interpolation is used.
-/

open Complex MeasureTheory ArithmeticFunction Set Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal NNReal Topology Moebius

namespace RHTower

noncomputable section

/-- Cofinal multiple of the honest divisor-dependent adaptive valuation depth. -/
def xiAdaptivePrimeNormalScaleAtDepth (K : ℕ) (q : XiZeroCopy) : ℕ :=
  (K + 1) * xiAdaptivePrimeNormalScale q

theorem xiAdaptivePrimeNormalScaleAtDepth_spec (K : ℕ) (q : XiZeroCopy) :
    (1 / 2 : ℝ) ≤
      (xiAdaptivePrimeNormalScaleAtDepth K q : ℝ) *
        (mobiusThetaCenteredParameter (xiSpectralPointSupport q.1)).re := by
  have hbase := xiAdaptivePrimeNormalScale_spec q
  have hfactor : (1 : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 K
  unfold xiAdaptivePrimeNormalScaleAtDepth
  push_cast
  calc
    (1 / 2 : ℝ) ≤
        (xiAdaptivePrimeNormalScale q : ℝ) *
          (mobiusThetaCenteredParameter (xiSpectralPointSupport q.1)).re := hbase
    _ ≤ ((K : ℝ) + 1) * (xiAdaptivePrimeNormalScale q : ℝ) *
          (mobiusThetaCenteredParameter (xiSpectralPointSupport q.1)).re := by
      have hnonneg : 0 ≤
          (xiAdaptivePrimeNormalScale q : ℝ) *
            (mobiusThetaCenteredParameter (xiSpectralPointSupport q.1)).re :=
        le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hbase
      nlinarith

/-- Literal coefficient reader of the adaptive codiagonal at cofinal valuation depth. -/
def adaptivePrimeNormalDivisorReaderAtDepth (K : ℕ) (q : XiZeroCopy) :
    AdaptivePrimeL1 →L[ℂ] ℂ :=
  adaptiveArithmeticL1Augmentation.comp
    (adaptivePrimeNormalCodiagonal
      (xiAdaptivePrimeNormalScaleAtDepth K q)
      (xiSpectralPointSupport q.1)
      (xiAdaptivePrimeNormalScaleAtDepth_spec K q))

theorem norm_adaptivePrimeNormalDivisorReaderAtDepth_le
    (K : ℕ) (q : XiZeroCopy) (x : AdaptivePrimeL1) :
    ‖adaptivePrimeNormalDivisorReaderAtDepth K q x‖ ≤
      (5 / 4 : ℝ) * ‖x‖ := by
  calc
    ‖adaptivePrimeNormalDivisorReaderAtDepth K q x‖ ≤
        ‖adaptivePrimeNormalCodiagonal
          (xiAdaptivePrimeNormalScaleAtDepth K q)
          (xiSpectralPointSupport q.1)
          (xiAdaptivePrimeNormalScaleAtDepth_spec K q) x‖ :=
      norm_adaptiveArithmeticL1Augmentation_le _
    _ ≤ (5 / 4 : ℝ) * ‖x‖ :=
      norm_adaptivePrimeNormalCodiagonal_le _ _ _ x

/-- At every finite depth the reader is exactly the head-plus-strict-tail source multiplier. -/
theorem adaptivePrimeNormalDivisorReaderAtDepth_single_eq_asymptoticMultiplier
    (K : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    adaptivePrimeNormalDivisorReaderAtDepth K q
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) =
      mobiusThetaPrimeNormalAsymptoticMultiplier p.1
        (adaptivePrimeNormalExponent p.1
          (xiAdaptivePrimeNormalScaleAtDepth K q))
        (xiSpectralPointSupport q.1) := by
  rw [adaptivePrimeNormalDivisorReaderAtDepth,
    ContinuousLinearMap.comp_apply,
    adaptivePrimeNormalCodiagonal_source_column,
    map_add, adaptiveArithmeticL1Augmentation_diagonal_single,
    adaptiveArithmeticL1Augmentation_tailColumn _ _ _
      (xiAdaptivePrimeNormalScaleAtDepth_spec K q),
    mobiusThetaPrimeNormalAsymptoticMultiplier,
    ArithmeticFunction.moebius_apply_prime p.2]
  norm_num

private theorem tendsto_adaptivePrimeNormalExponentAtDepth_atTop
    (q : XiZeroCopy) (p : Nat.Primes) :
    Tendsto (fun K : ℕ => adaptivePrimeNormalExponent p.1
      (xiAdaptivePrimeNormalScaleAtDepth K q)) atTop atTop := by
  apply tendsto_atTop_mono (fun K => ?_) tendsto_id
  have hN : 0 < xiAdaptivePrimeNormalScale q := by
    by_contra hzero
    have hscale : xiAdaptivePrimeNormalScale q = 0 := Nat.eq_zero_of_not_pos hzero
    exact xiAdaptivePrimeNormalExponent_ne_zero q p (by
      simp [adaptivePrimeNormalExponent, hscale])
  have hcoefficient : 1 ≤ 8 * p.1 * xiAdaptivePrimeNormalScale q := by
    have hpositive : 0 < 8 * p.1 * xiAdaptivePrimeNormalScale q := by
      exact Nat.mul_pos (Nat.mul_pos (by norm_num) p.2.pos) hN
    exact hpositive
  have hmultiple : K + 1 ≤
      (K + 1) * (8 * p.1 * xiAdaptivePrimeNormalScale q) := by
    simpa using Nat.mul_le_mul_left (K + 1) hcoefficient
  calc
    K ≤ K + 1 := Nat.le_succ K
    _ ≤ adaptivePrimeNormalExponent p.1
        (xiAdaptivePrimeNormalScaleAtDepth K q) := by
      simpa [adaptivePrimeNormalExponent, xiAdaptivePrimeNormalScaleAtDepth,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmultiple

/-- A fixed prime-labelled source reader tends to its Mobius head `-1` at infinite depth. -/
theorem tendsto_adaptivePrimeNormalDivisorReaderAtDepth_single
    (q : XiZeroCopy) (p : Nat.Primes) :
    Tendsto (fun K : ℕ => adaptivePrimeNormalDivisorReaderAtDepth K q
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1))
      atTop (nhds (-1 : ℂ)) := by
  have hw : 0 <
      (mobiusThetaCenteredParameter (xiSpectralPointSupport q.1)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit q.1).1
  rw [show (-1 : ℂ) = ((μ p.1 : ℤ) : ℂ) by
    rw [ArithmeticFunction.moebius_apply_prime p.2]
    norm_num]
  have hsource := tendsto_mobiusThetaPrimeNormalAsymptoticMultiplier p.2.pos hw
  have hcomp := hsource.comp (tendsto_adaptivePrimeNormalExponentAtDepth_atTop q p)
  change Tendsto (fun K : ℕ =>
    mobiusThetaPrimeNormalAsymptoticMultiplier p.1
      (adaptivePrimeNormalExponent p.1 (xiAdaptivePrimeNormalScaleAtDepth K q))
      (xiSpectralPointSupport q.1)) atTop (nhds ((μ p.1 : ℤ) : ℂ)) at hcomp
  simpa only [
    adaptivePrimeNormalDivisorReaderAtDepth_single_eq_asymptoticMultiplier]
    using hcomp

/-- Normalized cofinal reader, used as a contractive diagonal multiplier. -/
def adaptivePrimeNormalInfiniteDepthColumnMultiplier
    (p : Nat.Primes) (K : ℕ) (q : XiZeroCopy) : ℂ :=
  (4 / 5 : ℂ) * adaptivePrimeNormalDivisorReaderAtDepth K q
    (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)

theorem norm_adaptivePrimeNormalInfiniteDepthColumnMultiplier_le_one
    (p : Nat.Primes) (K : ℕ) (q : XiZeroCopy) :
    ‖adaptivePrimeNormalInfiniteDepthColumnMultiplier p K q‖ ≤ 1 := by
  have hupper := norm_adaptivePrimeNormalDivisorReaderAtDepth_le K q
    (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)
  have hsingle :
      ‖(lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1 :
        AdaptivePrimeL1)‖ = 1 := by
    simp [lp.norm_single]
  rw [hsingle, mul_one] at hupper
  rw [adaptivePrimeNormalInfiniteDepthColumnMultiplier, norm_mul]
  norm_num
  nlinarith

/-- Fixed prime-labelled horizon column at one cofinal adaptive valuation depth. -/
def adaptivePrimeNormalInfiniteDepthHorizonColumn
    (p : Nat.Primes) (K : ℕ) : XiDivisorL2 :=
  (5 / 4 : ℂ) •
    deningerMultiplier
      (norm_adaptivePrimeNormalInfiniteDepthColumnMultiplier_le_one p K)
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2

@[simp]
theorem adaptivePrimeNormalInfiniteDepthHorizonColumn_apply
    (p : Nat.Primes) (K : ℕ) (q : XiZeroCopy) :
    adaptivePrimeNormalInfiniteDepthHorizonColumn p K q =
      adaptivePrimeNormalDivisorReaderAtDepth K q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) *
        DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q := by
  rw [adaptivePrimeNormalInfiniteDepthHorizonColumn, lp.coeFn_smul, Pi.smul_apply,
    deningerMultiplier_apply,
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2_apply,
    adaptivePrimeNormalInfiniteDepthColumnMultiplier]
  ring

private theorem tendsto_adaptivePrimeNormalInfiniteDepthHorizonColumn_apply
    (p : Nat.Primes) (q : XiZeroCopy) :
    Tendsto (fun K : ℕ => adaptivePrimeNormalInfiniteDepthHorizonColumn p K q)
      atTop (nhds (-DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q)) := by
  have hreader := tendsto_adaptivePrimeNormalDivisorReaderAtDepth_single q p
  have hmul := hreader.mul_const
    (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q)
  simpa only [adaptivePrimeNormalInfiniteDepthHorizonColumn_apply, neg_mul, one_mul]
    using hmul

/-- **Adaptive infinite-depth boundary landing.**  A single retained ordinary-prime label has
cofinal honest codiagonal columns converging in the complete Xi Hilbert norm to the negative fixed
reflected-Gaussian horizon vector. -/
theorem tendsto_adaptivePrimeNormalInfiniteDepthHorizonColumn
    (p : Nat.Primes) :
    Tendsto (adaptivePrimeNormalInfiniteDepthHorizonColumn p) atTop
      (nhds (-DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2)) := by
  let term : ℕ → XiZeroCopy → ℝ := fun K q =>
    ‖adaptivePrimeNormalInfiniteDepthHorizonColumn p K q -
      (-DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2) q‖ ^ 2
  let bound : XiZeroCopy → ℝ := fun q =>
    (9 / 4 : ℝ) ^ 2 *
      ‖DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q‖ ^ 2
  have hboundsum : Summable bound :=
    DeningerMeyerGaussianGreen.summable_norm_sq_reflectedGaussianHorizonGrade.mul_left
      ((9 / 4 : ℝ) ^ 2)
  have hterm : ∀ q, Tendsto (fun K => term K q) atTop (nhds 0) := by
    intro q
    have hcol := tendsto_adaptivePrimeNormalInfiniteDepthHorizonColumn_apply p q
    have hconst : Tendsto (fun _ : ℕ =>
        -DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q)
        atTop (nhds (-DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q)) :=
      tendsto_const_nhds
    simpa [term, lp.coeFn_neg, Pi.neg_apply,
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2_apply]
      using (hcol.sub hconst).norm.pow 2
  have hbound : ∀ K q, ‖term K q‖ ≤ bound q := by
    intro K q
    have hreader := norm_adaptivePrimeNormalDivisorReaderAtDepth_le K q
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)
    have hsingle :
        ‖(lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1 :
          AdaptivePrimeL1)‖ = 1 := by simp [lp.norm_single]
    rw [hsingle, mul_one] at hreader
    have hsum : ‖adaptivePrimeNormalDivisorReaderAtDepth K q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) + 1‖ ≤
        (9 / 4 : ℝ) := by
      calc
        _ ≤ ‖adaptivePrimeNormalDivisorReaderAtDepth K q
            (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)‖ + ‖(1 : ℂ)‖ :=
          norm_add_le _ _
        _ ≤ 5 / 4 + 1 := by simpa using add_le_add_right hreader 1
        _ = 9 / 4 := by norm_num
    dsimp only [term, bound]
    rw [Real.norm_of_nonneg (sq_nonneg _),
      adaptivePrimeNormalInfiniteDepthHorizonColumn_apply,
      lp.coeFn_neg, Pi.neg_apply,
      DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2_apply]
    have heq :
        adaptivePrimeNormalDivisorReaderAtDepth K q
              (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) *
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q -
          -DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q =
        (adaptivePrimeNormalDivisorReaderAtDepth K q
            (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) + 1) *
          DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q := by ring
    rw [heq, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hsum 2)
      (sq_nonneg _)
  have htsum : Tendsto (fun K => ∑' q, term K q) atTop (nhds 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hboundsum hterm
      (Eventually.of_forall hbound)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnormsq : ∀ K,
      ‖adaptivePrimeNormalInfiniteDepthHorizonColumn p K -
          (-DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2)‖ ^ 2 =
        ∑' q, term K q := by
    intro K
    rw [HilbertSchmidt.lp_norm_sq_eq]
    apply tsum_congr
    intro q
    rfl
  have hsqzero : Tendsto (fun K =>
      ‖adaptivePrimeNormalInfiniteDepthHorizonColumn p K -
        (-DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2)‖ ^ 2)
      atTop (nhds 0) :=
    htsum.congr' (Eventually.of_forall fun K => (hnormsq K).symm)
  have hsqrt := hsqzero.sqrt
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hsqrt

namespace DeningerMeyerGaussianGreen

/-- The literal prime--Gamma Cauchy source and the retained-label adaptive prime-normal source have
the same completed Gaussian boundary value. -/
theorem tendsto_neg_adaptivePrimeNormalInfiniteDepthHorizonColumn_eq_cauchyBoundary
    (p : Nat.Primes) :
    Tendsto (fun K => -adaptivePrimeNormalInfiniteDepthHorizonColumn p K) atTop
      (nhds (∫ x : ℝ, reflectedGaussianPrimeGammaCauchyBoundary x)) := by
  have h := (tendsto_adaptivePrimeNormalInfiniteDepthHorizonColumn p).neg
  rw [integral_reflectedGaussianPrimeGammaCauchyBoundary_eq_horizonGradeL2]
  simpa using h

end DeningerMeyerGaussianGreen

end

end RHTower
