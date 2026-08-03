import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalHilbertNoGo
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianHorizonAdmission
import GaloisForLFunctions.RHTower.DeningerMultiplier
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCompletedGreenDefect

/-!
# Adaptive prime-normal source--divisor horizon intertwiner

The stable adaptive source lives in prime-labelled `ell^1`, whereas the
completed Xi divisor is Hilbertian `ell^2`; the accompanying no-go theorem
proves that no bounded comparison between them can retain a positive lower
modulus on the whole infinite source.  This file constructs the exact
positive replacement forced by that obstruction.

At every actual Xi divisor copy, an adaptive exponent is selected in the
honest prime-normal convergence chamber.  Coefficient augmentation of the
exact arithmetic codiagonal is then literally the complete prime-normal
residual multiplier.  Every prime column has local modulus at least `3/4`
and at most `5/4`.  Multiplication by the fixed reflected-Gaussian horizon
grade makes all columns square-summable, and `ell^1` column synthesis gives
a bounded global prime--divisor transform with an exact pointwise formula.

Every individual prime label survives this transform, but infinite-source
stability cannot survive its Hilbert readout.  Pairing the transform with
the unchanged prime packet gives the forced source-provenance graph.  That
graph is injective, bounded below by one, has closed range, and has uniform
upper capacity.  After quotienting to any one prime label, its residual
family is instead a boundedly invertible diagonal automorphism of the whole
divisor Hilbert carrier, with lower modulus `3/4`, upper modulus `5/4`, and
inverse bound `4/3`.  Thus the correct full-source compatible carrier before
polarization is non-Hilbertian, while every fixed-label divisor comparison
is exact; the remaining hard theorem must force the explicit Green class to
vanish rather than postulate a stable identification of the full `ell^1`
range with a Hilbert quotient.
-/

open Complex MeasureTheory ArithmeticFunction Set Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal NNReal Topology Moebius

namespace RHTower

noncomputable section

/-- Absolute summability of an `ell^1` coefficient packet. -/
private theorem adaptiveArithmeticL1_summable_norm
    (x : AdaptiveArithmeticL1) : Summable (fun n : ℕ => ‖x n‖) := by
  simpa using
    (lp.hasSum_norm (by norm_num : 0 < (1 : ENNReal).toReal) x).summable

/-- The coefficient codiagonal on arithmetic `ell^1`. -/
def adaptiveArithmeticL1Augmentation : AdaptiveArithmeticL1 →L[ℂ] ℂ :=
  let L : AdaptiveArithmeticL1 →ₗ[ℂ] ℂ :=
    { toFun := fun x => ∑' n : ℕ, x n
      map_add' := by
        intro x y
        simp only [lp.coeFn_add, Pi.add_apply]
        exact (Summable.of_norm
          (adaptiveArithmeticL1_summable_norm x)).tsum_add
            (Summable.of_norm (adaptiveArithmeticL1_summable_norm y))
      map_smul' := by
        intro c x
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        exact tsum_mul_left }
  L.mkContinuous 1 (fun x => by
    calc
      ‖∑' n : ℕ, x n‖ ≤ ∑' n : ℕ, ‖x n‖ :=
        norm_tsum_le_tsum_norm (adaptiveArithmeticL1_summable_norm x)
      _ = ‖x‖ := by
        simpa using
          (lp.hasSum_norm
            (by norm_num : 0 < (1 : ENNReal).toReal) x).tsum_eq
      _ = 1 * ‖x‖ := by ring)

theorem norm_adaptiveArithmeticL1Augmentation_le
    (x : AdaptiveArithmeticL1) :
    ‖adaptiveArithmeticL1Augmentation x‖ ≤ ‖x‖ := by
  change ‖∑' n : ℕ, x n‖ ≤ ‖x‖
  calc
    ‖∑' n : ℕ, x n‖ ≤ ∑' n : ℕ, ‖x n‖ :=
      norm_tsum_le_tsum_norm (adaptiveArithmeticL1_summable_norm x)
    _ = ‖x‖ := by
      simpa using
        (lp.hasSum_norm
          (by norm_num : 0 < (1 : ENNReal).toReal) x).tsum_eq

/-- Divisor-dependent adaptive depth selected before divisor restriction. -/
def xiAdaptivePrimeNormalScale (q : XiZeroCopy) : ℕ :=
  Classical.choose
    (exists_nat_gt (1 / (2 * ((q.1 : ℂ).re))))

theorem xiAdaptivePrimeNormalScale_spec (q : XiZeroCopy) :
    (1 / 2 : ℝ) ≤
      (xiAdaptivePrimeNormalScale q : ℝ) *
        (mobiusThetaCenteredParameter (xiSpectralPointSupport q.1)).re := by
  rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
  have hre : 0 < (q.1 : ℂ).re :=
    (xi_divisor_support_re_mem_open_unit q.1).1
  have hchoose := Classical.choose_spec
    (exists_nat_gt (1 / (2 * ((q.1 : ℂ).re))))
  have hpos : 0 < 2 * (q.1 : ℂ).re := by positivity
  have hmul := (div_lt_iff₀ hpos).mp hchoose
  unfold xiAdaptivePrimeNormalScale
  ring_nf at hmul ⊢
  nlinarith

/-- Exact local arithmetic reader at one actual Xi divisor copy. -/
def adaptivePrimeNormalDivisorReader (q : XiZeroCopy) :
    AdaptivePrimeL1 →L[ℂ] ℂ :=
  adaptiveArithmeticL1Augmentation.comp
    (adaptivePrimeNormalCodiagonal
      (xiAdaptivePrimeNormalScale q)
      (xiSpectralPointSupport q.1)
      (xiAdaptivePrimeNormalScale_spec q))

theorem norm_adaptivePrimeNormalCodiagonal_le
    (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re)
    (x : AdaptivePrimeL1) :
    ‖adaptivePrimeNormalCodiagonal N w hNw x‖ ≤ (5 / 4 : ℝ) * ‖x‖ := by
  calc
    ‖adaptivePrimeNormalCodiagonal N w hNw x‖ ≤
        ‖adaptivePrimeNormalDiagonalEmbedding x‖ +
          ‖adaptivePrimeNormalTailOperator N w hNw x‖ := by
      rw [adaptivePrimeNormalCodiagonal, _root_.add_apply]
      exact norm_add_le _ _
    _ ≤ ‖x‖ + (1 / 4 : ℝ) * ‖x‖ := by
      rw [adaptivePrimeNormalDiagonalEmbedding.norm_map]
      gcongr
      exact norm_adaptivePrimeNormalTailOperator_le_quarter N w hNw x
    _ = (5 / 4 : ℝ) * ‖x‖ := by ring

theorem norm_adaptivePrimeNormalDivisorReader_le
    (q : XiZeroCopy) (x : AdaptivePrimeL1) :
    ‖adaptivePrimeNormalDivisorReader q x‖ ≤ (5 / 4 : ℝ) * ‖x‖ := by
  calc
    ‖adaptivePrimeNormalDivisorReader q x‖ ≤
        ‖adaptivePrimeNormalCodiagonal
          (xiAdaptivePrimeNormalScale q)
          (xiSpectralPointSupport q.1)
          (xiAdaptivePrimeNormalScale_spec q) x‖ :=
      norm_adaptiveArithmeticL1Augmentation_le _
    _ ≤ (5 / 4 : ℝ) * ‖x‖ :=
      norm_adaptivePrimeNormalCodiagonal_le _ _ _ x

theorem adaptiveArithmeticL1Augmentation_diagonal_single
    (p : Nat.Primes) :
    adaptiveArithmeticL1Augmentation
        (adaptivePrimeNormalDiagonalEmbedding
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)) = -1 := by
  change (∑' n : ℕ,
    adaptivePrimeNormalDiagonalFunction
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) n) = -1
  rw [tsum_eq_single p.1]
  · simp [adaptivePrimeNormalDiagonalFunction, p.2, lp.single_apply]
  · intro n hnp
    by_cases hn : n.Prime
    · have hsub : (⟨n, hn⟩ : Nat.Primes) ≠ p := by
        intro h
        exact hnp (congrArg Subtype.val h)
      have hz :
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)
              (⟨n, hn⟩ : Nat.Primes) = 0 := by
        change @Pi.single Nat.Primes (fun _ : Nat.Primes => ℂ)
          inferInstance inferInstance p (1 : ℂ)
            (show Nat.Primes from ⟨n, hn⟩) = 0
        exact Pi.single_eq_of_ne hsub 1
      simpa [adaptivePrimeNormalDiagonalFunction, hn] using congrArg Neg.neg hz
    · simp [adaptivePrimeNormalDiagonalFunction, hn]

theorem adaptivePrimeNormalDivisorReader_single_lower
    (q : XiZeroCopy) (p : Nat.Primes) :
    (3 / 4 : ℝ) ≤
      ‖adaptivePrimeNormalDivisorReader q
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)‖ := by
  let N := xiAdaptivePrimeNormalScale q
  let w := xiSpectralPointSupport q.1
  let hNw := xiAdaptivePrimeNormalScale_spec q
  let tail := adaptivePrimeNormalTailColumn p N w
  have hreader :
      adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) =
        -1 + adaptiveArithmeticL1Augmentation tail := by
    rw [adaptivePrimeNormalDivisorReader,
      ContinuousLinearMap.comp_apply,
      adaptivePrimeNormalCodiagonal_source_column]
    rw [map_add, adaptiveArithmeticL1Augmentation_diagonal_single]
  have htail : ‖adaptiveArithmeticL1Augmentation tail‖ ≤ 1 / 4 := by
    calc
      ‖adaptiveArithmeticL1Augmentation tail‖ ≤ ‖tail‖ :=
        norm_adaptiveArithmeticL1Augmentation_le _
      _ ≤ 1 / 4 := norm_adaptivePrimeNormalTailColumn_le_quarter p hNw
  rw [hreader]
  have hreverse := norm_sub_norm_le (1 : ℂ)
    (adaptiveArithmeticL1Augmentation tail)
  rw [norm_one] at hreverse
  have heq :
      ‖(-1 : ℂ) + adaptiveArithmeticL1Augmentation tail‖ =
        ‖(1 : ℂ) - adaptiveArithmeticL1Augmentation tail‖ := by
    rw [show (-1 : ℂ) + adaptiveArithmeticL1Augmentation tail =
      -((1 : ℂ) - adaptiveArithmeticL1Augmentation tail) by ring, norm_neg]
  rw [heq]
  linarith

theorem adaptivePrimeNormalDivisorReader_single_ne_zero
    (q : XiZeroCopy) (p : Nat.Primes) :
    adaptivePrimeNormalDivisorReader q
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) ≠ 0 := by
  intro hzero
  have hlower := adaptivePrimeNormalDivisorReader_single_lower q p
  rw [hzero, norm_zero] at hlower
  norm_num at hlower

@[simp]
theorem adaptiveArithmeticL1Augmentation_single
    (n : ℕ) (c : ℂ) :
    adaptiveArithmeticL1Augmentation
      (lp.single (E := fun _ : ℕ => ℂ) 1 n c) = c := by
  change (∑' j : ℕ, Pi.single n c j) = c
  rw [tsum_eq_single n]
  · simp
  · intro j hjn
    exact @Pi.single_eq_of_ne ℕ (fun _ : ℕ => ℂ)
      inferInstance inferInstance n j hjn c

theorem adaptiveArithmeticL1Augmentation_tailColumn
    (p : Nat.Primes) (N : ℕ) (w : ℂ)
    (hNw : (1 / 2 : ℝ) ≤
      (N : ℝ) * (mobiusThetaCenteredParameter w).re) :
    adaptiveArithmeticL1Augmentation
        (adaptivePrimeNormalTailColumn p N w) =
      ∑' j : ℕ, mobiusThetaPrimeNormalSpectralTailCoefficient p.1
        (adaptivePrimeNormalExponent p.1 N) w j := by
  rw [adaptivePrimeNormalTailColumn,
    ContinuousLinearMap.map_tsum _
      (summable_adaptivePrimeNormalTailColumn_terms p hNw)]
  apply tsum_congr
  intro j
  rw [adaptiveArithmeticL1Augmentation_single]

/-- At every divisor copy and every prime label, the local reader is the exact
head-plus-tail residual multiplier, not an abstract coefficient functional. -/
theorem adaptivePrimeNormalDivisorReader_single_eq_asymptoticMultiplier
    (q : XiZeroCopy) (p : Nat.Primes) :
    adaptivePrimeNormalDivisorReader q
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) =
      mobiusThetaPrimeNormalAsymptoticMultiplier p.1
        (adaptivePrimeNormalExponent p.1 (xiAdaptivePrimeNormalScale q))
        (xiSpectralPointSupport q.1) := by
  rw [adaptivePrimeNormalDivisorReader,
    ContinuousLinearMap.comp_apply,
    adaptivePrimeNormalCodiagonal_source_column,
    map_add,
    adaptiveArithmeticL1Augmentation_diagonal_single,
    adaptiveArithmeticL1Augmentation_tailColumn _ _ _
      (xiAdaptivePrimeNormalScale_spec q),
    mobiusThetaPrimeNormalAsymptoticMultiplier,
    ArithmeticFunction.moebius_apply_prime p.2]
  norm_num

theorem xiAdaptivePrimeNormalExponent_ne_zero
    (q : XiZeroCopy) (p : Nat.Primes) :
    adaptivePrimeNormalExponent p.1 (xiAdaptivePrimeNormalScale q) ≠ 0 := by
  have hscale : 0 < xiAdaptivePrimeNormalScale q := by
    by_contra hnot
    have hzero : xiAdaptivePrimeNormalScale q = 0 := Nat.eq_zero_of_not_pos hnot
    have hspec := xiAdaptivePrimeNormalScale_spec q
    rw [hzero, Nat.cast_zero, zero_mul] at hspec
    norm_num at hspec
  unfold adaptivePrimeNormalExponent
  exact mul_ne_zero (mul_ne_zero (by norm_num) p.2.ne_zero) hscale.ne'

theorem xiAdaptivePrimeNormalExponent_convergence
    (q : XiZeroCopy) (p : Nat.Primes) :
    1 / (adaptivePrimeNormalExponent p.1
          (xiAdaptivePrimeNormalScale q) : ℝ) <
      (mobiusThetaCenteredParameter (xiSpectralPointSupport q.1)).re := by
  rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
  have hspec := xiAdaptivePrimeNormalScale_spec q
  rw [mobiusThetaCenteredParameter_xiSpectralPointSupport] at hspec
  have hp : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
  have hp2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
  have hm : (0 : ℝ) <
      adaptivePrimeNormalExponent p.1 (xiAdaptivePrimeNormalScale q) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (xiAdaptivePrimeNormalExponent_ne_zero q p)
  have hmul := mul_le_mul_of_nonneg_left hspec
    (show (0 : ℝ) ≤ 8 * p.1 by positivity)
  have hmr : 1 <
      (adaptivePrimeNormalExponent p.1 (xiAdaptivePrimeNormalScale q) : ℝ) *
        (q.1 : ℂ).re := by
    calc
      1 < 4 * (p.1 : ℝ) := by nlinarith
      _ = (8 * (p.1 : ℝ)) * (1 / 2 : ℝ) := by ring
      _ ≤ (8 * (p.1 : ℝ)) *
          ((xiAdaptivePrimeNormalScale q : ℝ) * (q.1 : ℂ).re) := hmul
      _ = (adaptivePrimeNormalExponent p.1
          (xiAdaptivePrimeNormalScale q) : ℝ) * (q.1 : ℂ).re := by
        unfold adaptivePrimeNormalExponent
        push_cast
        ring
  exact (div_lt_iff₀ hm).2 (by simpa [mul_comm] using hmr)

/-- The local divisor reader is the literal complete prime-normal residual
multiplier in its honest convergence domain. -/
theorem adaptivePrimeNormalDivisorReader_single_eq_residualMultiplier
    (q : XiZeroCopy) (p : Nat.Primes) :
    adaptivePrimeNormalDivisorReader q
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) =
      mobiusThetaPrimeNormalResidualMultiplier p.1
        (adaptivePrimeNormalExponent p.1 (xiAdaptivePrimeNormalScale q))
        (xiSpectralPointSupport q.1) := by
  rw [adaptivePrimeNormalDivisorReader_single_eq_asymptoticMultiplier]
  exact (mobiusThetaPrimeNormalResidualMultiplier_eq_asymptoticMultiplier
    p.2.pos (xiAdaptivePrimeNormalExponent_ne_zero q p)
      (xiAdaptivePrimeNormalExponent_convergence q p)).symm

/-- Normalized local residual family used as a contractive diagonal multiplier. -/
def adaptivePrimeNormalHorizonColumnMultiplier
    (p : Nat.Primes) (q : XiZeroCopy) : ℂ :=
  (4 / 5 : ℂ) * adaptivePrimeNormalDivisorReader q
    (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)

theorem norm_adaptivePrimeNormalHorizonColumnMultiplier_le_one
    (p : Nat.Primes) (q : XiZeroCopy) :
    ‖adaptivePrimeNormalHorizonColumnMultiplier p q‖ ≤ 1 := by
  have hupper := norm_adaptivePrimeNormalDivisorReader_le q
    (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)
  have hsingle :
      ‖(lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1 :
        AdaptivePrimeL1)‖ = 1 := by
    simp [lp.norm_single]
  rw [hsingle, mul_one] at hupper
  rw [adaptivePrimeNormalHorizonColumnMultiplier, norm_mul]
  norm_num
  nlinarith

/-- Bounded divisor multiplier determined by one exact adaptive prime label. -/
def adaptivePrimeNormalHorizonForward (p : Nat.Primes) :
    XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  (5 / 4 : ℂ) • deningerMultiplier
    (norm_adaptivePrimeNormalHorizonColumnMultiplier_le_one p)

@[simp]
theorem adaptivePrimeNormalHorizonForward_apply
    (p : Nat.Primes) (a : XiDivisorL2) (q : XiZeroCopy) :
    adaptivePrimeNormalHorizonForward p a q =
      adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) * a q := by
  rw [adaptivePrimeNormalHorizonForward,
    _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    deningerMultiplier_apply,
    adaptivePrimeNormalHorizonColumnMultiplier]
  ring

/-- Normalized inverse residual family; the local `3/4` lower modulus makes
it contractive. -/
def adaptivePrimeNormalHorizonInverseMultiplier
    (p : Nat.Primes) (q : XiZeroCopy) : ℂ :=
  (3 / 4 : ℂ) *
    (adaptivePrimeNormalDivisorReader q
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1))⁻¹

theorem norm_adaptivePrimeNormalHorizonInverseMultiplier_le_one
    (p : Nat.Primes) (q : XiZeroCopy) :
    ‖adaptivePrimeNormalHorizonInverseMultiplier p q‖ ≤ 1 := by
  have hlower := adaptivePrimeNormalDivisorReader_single_lower q p
  have hpos : 0 < ‖adaptivePrimeNormalDivisorReader q
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)‖ :=
    norm_pos_iff.mpr (adaptivePrimeNormalDivisorReader_single_ne_zero q p)
  rw [adaptivePrimeNormalHorizonInverseMultiplier, norm_mul, norm_inv]
  norm_num
  rw [← div_eq_mul_inv, div_le_one hpos]
  exact hlower

/-- Bounded inverse divisor multiplier for one exact adaptive prime label. -/
def adaptivePrimeNormalHorizonInverse (p : Nat.Primes) :
    XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  (4 / 3 : ℂ) • deningerMultiplier
    (norm_adaptivePrimeNormalHorizonInverseMultiplier_le_one p)

@[simp]
theorem adaptivePrimeNormalHorizonInverse_apply
    (p : Nat.Primes) (a : XiDivisorL2) (q : XiZeroCopy) :
    adaptivePrimeNormalHorizonInverse p a q =
      (adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1))⁻¹ * a q := by
  rw [adaptivePrimeNormalHorizonInverse,
    _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    deningerMultiplier_apply,
    adaptivePrimeNormalHorizonInverseMultiplier]
  ring

theorem adaptivePrimeNormalHorizonInverse_forward
    (p : Nat.Primes) (a : XiDivisorL2) :
    adaptivePrimeNormalHorizonInverse p
      (adaptivePrimeNormalHorizonForward p a) = a := by
  ext q
  rw [adaptivePrimeNormalHorizonInverse_apply,
    adaptivePrimeNormalHorizonForward_apply]
  field_simp [adaptivePrimeNormalDivisorReader_single_ne_zero q p]

theorem adaptivePrimeNormalHorizonForward_inverse
    (p : Nat.Primes) (a : XiDivisorL2) :
    adaptivePrimeNormalHorizonForward p
      (adaptivePrimeNormalHorizonInverse p a) = a := by
  ext q
  rw [adaptivePrimeNormalHorizonForward_apply,
    adaptivePrimeNormalHorizonInverse_apply]
  field_simp [adaptivePrimeNormalDivisorReader_single_ne_zero q p]

theorem norm_adaptivePrimeNormalHorizonForward_le
    (p : Nat.Primes) (a : XiDivisorL2) :
    ‖adaptivePrimeNormalHorizonForward p a‖ ≤ (5 / 4 : ℝ) * ‖a‖ := by
  rw [adaptivePrimeNormalHorizonForward, _root_.smul_apply,
    norm_smul]
  norm_num
  change ‖deningerMultiplierMap
      (norm_adaptivePrimeNormalHorizonColumnMultiplier_le_one p) a‖ ≤ ‖a‖
  simpa using deningerMultiplierMap_norm_le
    (norm_adaptivePrimeNormalHorizonColumnMultiplier_le_one p) a

theorem norm_adaptivePrimeNormalHorizonInverse_le
    (p : Nat.Primes) (a : XiDivisorL2) :
    ‖adaptivePrimeNormalHorizonInverse p a‖ ≤ (4 / 3 : ℝ) * ‖a‖ := by
  rw [adaptivePrimeNormalHorizonInverse, _root_.smul_apply,
    norm_smul]
  norm_num
  change ‖deningerMultiplierMap
      (norm_adaptivePrimeNormalHorizonInverseMultiplier_le_one p) a‖ ≤ ‖a‖
  simpa using deningerMultiplierMap_norm_le
    (norm_adaptivePrimeNormalHorizonInverseMultiplier_le_one p) a

/-- The fixed-label compatible divisor comparison retains the exact `3/4`
lower modulus after source quotienting to one prime column. -/
theorem adaptivePrimeNormalHorizonForward_lower
    (p : Nat.Primes) (a : XiDivisorL2) :
    (3 / 4 : ℝ) * ‖a‖ ≤ ‖adaptivePrimeNormalHorizonForward p a‖ := by
  have h := norm_adaptivePrimeNormalHorizonInverse_le p
    (adaptivePrimeNormalHorizonForward p a)
  rw [adaptivePrimeNormalHorizonInverse_forward] at h
  nlinarith [norm_nonneg a,
    norm_nonneg (adaptivePrimeNormalHorizonForward p a)]


/-- One prime-labelled exact residual column in the completed Xi divisor,
admitted by the fixed reflected-Gaussian horizon grade. -/
def adaptivePrimeNormalHorizonColumn (p : Nat.Primes) : XiDivisorL2 :=
  adaptivePrimeNormalHorizonForward p
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2

@[simp]
theorem adaptivePrimeNormalHorizonColumn_apply
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalHorizonColumn p q =
      adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) *
        DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q := by
  rw [adaptivePrimeNormalHorizonColumn,
    adaptivePrimeNormalHorizonForward_apply,
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2_apply]

theorem norm_adaptivePrimeNormalHorizonColumn_le
    (p : Nat.Primes) :
    ‖adaptivePrimeNormalHorizonColumn p‖ ≤
      (5 / 4 : ℝ) *
        ‖DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2‖ := by
  rw [adaptivePrimeNormalHorizonColumn]
  exact norm_adaptivePrimeNormalHorizonForward_le p _

theorem adaptivePrimeNormalHorizonColumn_apply_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalHorizonColumn p q ≠ 0 := by
  rw [adaptivePrimeNormalHorizonColumn_apply]
  exact mul_ne_zero
    (adaptivePrimeNormalDivisorReader_single_ne_zero q p)
    (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade_ne_zero q)

theorem adaptivePrimeNormalHorizonColumn_ne_zero
    (p : Nat.Primes) : adaptivePrimeNormalHorizonColumn p ≠ 0 := by
  intro hzero
  let q : XiZeroCopy := Classical.choice inferInstance
  exact adaptivePrimeNormalHorizonColumn_apply_ne_zero p q
    (congrArg (fun x : XiDivisorL2 => x q) hzero)

/-- Global joint prime--divisor transform: exact adaptive residual columns,
assembled in `ell^1` and admitted into divisor `ell^2` by one fixed source grade. -/
def adaptivePrimeNormalHorizonIntertwiner :
    AdaptivePrimeL1 →L[ℂ] XiDivisorL2 :=
  lpOneColumnSynthesis adaptivePrimeNormalHorizonColumn
    ((5 / 4 : ℝ) *
      ‖DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2‖)
    norm_adaptivePrimeNormalHorizonColumn_le

theorem norm_adaptivePrimeNormalHorizonIntertwiner_le
    (x : AdaptivePrimeL1) :
    ‖adaptivePrimeNormalHorizonIntertwiner x‖ ≤
      ((5 / 4 : ℝ) *
        ‖DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2‖) * ‖x‖ := by
  exact norm_lpOneColumnSynthesis_le _ _ _ x

@[simp]
theorem adaptivePrimeNormalHorizonIntertwiner_single
    (p : Nat.Primes) (c : ℂ) :
    adaptivePrimeNormalHorizonIntertwiner
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p c) =
      c • adaptivePrimeNormalHorizonColumn p := by
  exact lpOneColumnSynthesis_single _ _ _ p c

theorem adaptivePrimeNormalHorizonIntertwiner_single_ne_zero
    (p : Nat.Primes) :
    adaptivePrimeNormalHorizonIntertwiner
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) ≠ 0 := by
  rw [adaptivePrimeNormalHorizonIntertwiner_single, one_smul]
  exact adaptivePrimeNormalHorizonColumn_ne_zero p

/-- Exact pointwise formula: the global transform is the divisorwise adaptive
residual reader multiplied by the one fixed reflected-Gaussian horizon grade. -/
theorem adaptivePrimeNormalHorizonIntertwiner_apply
    (x : AdaptivePrimeL1) (q : XiZeroCopy) :
    adaptivePrimeNormalHorizonIntertwiner x q =
      adaptivePrimeNormalDivisorReader q x *
        DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q := by
  have hsingle := lp.hasSum_single
    (E := fun _ : Nat.Primes => ℂ) (p := 1) (by norm_num) x
  have hT := hsingle.mapL adaptivePrimeNormalHorizonIntertwiner
  have hTeval := hT.mapL
    (lp.evalCLM ℂ (fun _ : XiZeroCopy => ℂ) 2 q)
  have hreader := hsingle.mapL (adaptivePrimeNormalDivisorReader q)
  have hreader' : HasSum
      (fun p : Nat.Primes =>
        x p * adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1))
      (adaptivePrimeNormalDivisorReader q x) := by
    have hfun :
        (fun p : Nat.Primes => adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p (x p))) =
        fun p : Nat.Primes => x p * adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) := by
      funext p
      rw [show lp.single (E := fun _ : Nat.Primes => ℂ) 1 p (x p) =
          x p • lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1 by
        rw [← lp.single_smul]
        congr 1
        simp,
        map_smul]
      rfl
    rw [hfun] at hreader
    exact hreader
  have hgraded := hreader'.mul_right
    (DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q)
  apply HasSum.unique hTeval
  have hterms :
      (fun p : Nat.Primes =>
        x p * adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) *
            DeningerMeyerGaussianGreen.reflectedGaussianHorizonGrade q) =
      fun p : Nat.Primes =>
        (lp.evalCLM ℂ (fun _ : XiZeroCopy => ℂ) 2 q)
          (adaptivePrimeNormalHorizonIntertwiner
            (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p (x p))) := by
    funext p
    rw [adaptivePrimeNormalHorizonIntertwiner_single, map_smul]
    change _ = x p * adaptivePrimeNormalHorizonColumn p q
    rw [adaptivePrimeNormalHorizonColumn_apply]
    ring
  rw [hterms] at hgraded
  exact hgraded

/-- Source-resolved graph forced by the Hilbert no-go.  It retains the
prime packet before the horizon comparison. -/
def adaptivePrimeNormalHorizonProvenanceGraph :
    AdaptivePrimeL1 →L[ℂ] (AdaptivePrimeL1 × XiDivisorL2) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.id ℂ AdaptivePrimeL1)
    adaptivePrimeNormalHorizonIntertwiner

@[simp]
theorem adaptivePrimeNormalHorizonProvenanceGraph_apply
    (x : AdaptivePrimeL1) :
    adaptivePrimeNormalHorizonProvenanceGraph x =
      (x, adaptivePrimeNormalHorizonIntertwiner x) := rfl

theorem adaptivePrimeNormalHorizonProvenanceGraph_lower
    (x : AdaptivePrimeL1) :
    ‖x‖ ≤ ‖adaptivePrimeNormalHorizonProvenanceGraph x‖ := by
  rw [adaptivePrimeNormalHorizonProvenanceGraph_apply]
  change ‖x‖ ≤ max ‖x‖ ‖adaptivePrimeNormalHorizonIntertwiner x‖
  exact le_max_left _ _

/-- Uniform upper capacity of the source-resolved graph. -/
theorem adaptivePrimeNormalHorizonProvenanceGraph_upper
    (x : AdaptivePrimeL1) :
    ‖adaptivePrimeNormalHorizonProvenanceGraph x‖ ≤
      max 1 ((5 / 4 : ℝ) *
        ‖DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2‖) * ‖x‖ := by
  rw [adaptivePrimeNormalHorizonProvenanceGraph_apply]
  change max ‖x‖ ‖adaptivePrimeNormalHorizonIntertwiner x‖ ≤ _
  apply max_le
  · calc
      ‖x‖ = 1 * ‖x‖ := by ring
      _ ≤ max 1 ((5 / 4 : ℝ) *
          ‖DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · calc
      ‖adaptivePrimeNormalHorizonIntertwiner x‖ ≤
          ((5 / 4 : ℝ) *
            ‖DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2‖) * ‖x‖ :=
        norm_adaptivePrimeNormalHorizonIntertwiner_le x
      _ ≤ max 1 ((5 / 4 : ℝ) *
          ‖DeningerMeyerGaussianGreen.reflectedGaussianHorizonGradeL2‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem adaptivePrimeNormalHorizonProvenanceGraph_injective :
    Function.Injective adaptivePrimeNormalHorizonProvenanceGraph := by
  intro x y hxy
  exact congrArg Prod.fst hxy

theorem adaptivePrimeNormalHorizonProvenanceGraph_isClosed_range :
    IsClosed (Set.range adaptivePrimeNormalHorizonProvenanceGraph) := by
  have hanti : AntilipschitzWith 1 adaptivePrimeNormalHorizonProvenanceGraph := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact adaptivePrimeNormalHorizonProvenanceGraph_lower (x - y)
  exact hanti.isClosed_range
    adaptivePrimeNormalHorizonProvenanceGraph.uniformContinuous

/-- Hilbert readout of the stable provenance graph is exactly the joint
prime--divisor transform. -/
theorem adaptivePrimeNormalHorizonProvenanceGraph_snd
    (x : AdaptivePrimeL1) :
    ContinuousLinearMap.snd ℂ AdaptivePrimeL1 XiDivisorL2
        (adaptivePrimeNormalHorizonProvenanceGraph x) =
      adaptivePrimeNormalHorizonIntertwiner x := rfl

/-- The Hilbert readout cannot inherit the graph's stable lower modulus. -/
theorem adaptivePrimeNormalHorizonIntertwiner_not_boundedBelow :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : AdaptivePrimeL1,
      c * ‖x‖ ≤ ‖adaptivePrimeNormalHorizonIntertwiner x‖ :=
  lpOne_to_innerProduct_not_boundedBelow adaptivePrimeNormalHorizonIntertwiner

namespace DeningerMeyerGaussianGreen

/-- Any completed divisor field nonzero at every actual Xi copy detects RH
after the completed Green fracture. -/
theorem deningerArithmeticCompletedGreenProvenance_eq_zero_iff_riemannHypothesis_of_pointwise_ne_zero
    (a : XiDivisorL2) (ha : ∀ q : XiZeroCopy, a q ≠ 0) :
    deningerArithmeticCompletedGreenProvenance a = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply deningerArithmeticGreenResolvedDefect_vanishes_iff_riemannHypothesis.mp
    intro b
    rw [deningerArithmeticGreenResolvedDefect_eq_antidiagonal]
    have hfracture : ∀ q : XiZeroCopy,
        xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) = 0 := by
      intro q
      have hq := congrArg (fun x : XiDivisorL2 => x q) hzero
      rw [deningerArithmeticCompletedGreenProvenance_apply] at hq
      apply (mul_eq_zero.mp hq).resolve_right
      rw [deningerArithmeticOrientedHodgeLp_apply,
        deningerArithmeticCompletedRieszConjugation_apply]
      apply mul_ne_zero
      · exact neg_ne_zero.mpr (deningerArithmeticFEOrientation_ne_zero q)
      · rw [starRingEnd_self_apply]
        exact ha (xiZeroCopyReflectEquiv q)
    have hfirst :
        deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation b) = 0 := by
      ext q
      rw [deningerArithmeticGradedHodgeCovarianceDefect_apply,
        hfracture q, zero_mul]
      rfl
    rw [hfirst]
    simp [resolvedDefectAntidiagonal]
  · intro hRH
    ext q
    rw [deningerArithmeticCompletedGreenProvenance_apply]
    have hline := xi_divisor_support_re_eq_half_of_rh hRH q.1
    rw [(xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
      (q.1 : ℂ)).2 hline, zero_mul]
    rfl

/-- Actual completed Green provenance of one exact adaptive prime-normal
horizon column. -/
def adaptivePrimeNormalHorizonGreenProvenance
    (ell : Nat.Primes) : XiDivisorL2 :=
  deningerArithmeticCompletedGreenProvenance
    (adaptivePrimeNormalHorizonColumn ell)

/-- Every prime-labelled exact residual column is a single global RH detector
after completed Green comparison. -/
theorem adaptivePrimeNormalHorizonGreenProvenance_eq_zero_iff_riemannHypothesis
    (ell : Nat.Primes) :
    adaptivePrimeNormalHorizonGreenProvenance ell = 0 ↔
      RiemannHypothesis := by
  exact deningerArithmeticCompletedGreenProvenance_eq_zero_iff_riemannHypothesis_of_pointwise_ne_zero
    (adaptivePrimeNormalHorizonColumn ell)
    (adaptivePrimeNormalHorizonColumn_apply_ne_zero ell)

theorem adaptivePrimeNormalHorizonGreenProvenance_ne_zero_iff_not_riemannHypothesis
    (ell : Nat.Primes) :
    adaptivePrimeNormalHorizonGreenProvenance ell ≠ 0 ↔
      ¬ RiemannHypothesis := by
  exact not_congr
    (adaptivePrimeNormalHorizonGreenProvenance_eq_zero_iff_riemannHypothesis ell)

/-- Actual cross-prime incidence image of an adaptive source column's
completed Green provenance. -/
def adaptivePrimeNormalHorizonGreenIncidence
    (ell p q : Nat.Primes) (hpq : p ≠ q) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq
    (adaptivePrimeNormalHorizonGreenProvenance ell)

theorem adaptivePrimeNormalHorizonGreenIncidence_eq_zero_iff_riemannHypothesis
    (ell p q : Nat.Primes) (hpq : p ≠ q) :
    adaptivePrimeNormalHorizonGreenIncidence ell p q hpq = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply (adaptivePrimeNormalHorizonGreenProvenance_eq_zero_iff_riemannHypothesis
      ell).mp
    apply (deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq).injective
    simpa [adaptivePrimeNormalHorizonGreenIncidence] using hzero
  · intro hRH
    rw [adaptivePrimeNormalHorizonGreenIncidence,
      (adaptivePrimeNormalHorizonGreenProvenance_eq_zero_iff_riemannHypothesis
        ell).mpr hRH]
    exact map_zero _

/-- Resolved Hellinger--Gamma quotient class of one exact adaptive source
column after horizon admission and completed Green comparison. -/
def adaptivePrimeNormalHorizonGreenResolvedClass
    (ell p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :=
  hellingerGammaResolvedProvenanceQuotientSource hpq a
    (adaptivePrimeNormalHorizonGreenIncidence ell p q hpq)

/-- The fully source-labelled resolved quotient class vanishes exactly under
RH.  No zero-displacement or range-membership hypothesis is assumed. -/
theorem adaptivePrimeNormalHorizonGreenResolvedClass_eq_zero_iff_riemannHypothesis
    (ell p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :
    adaptivePrimeNormalHorizonGreenResolvedClass ell p q hpq a = 0 ↔
      RiemannHypothesis := by
  rw [← adaptivePrimeNormalHorizonGreenIncidence_eq_zero_iff_riemannHypothesis
    ell p q hpq]
  constructor
  · intro hzero
    apply hellingerGammaResolvedProvenanceQuotientSource_injective hpq a
    simpa [adaptivePrimeNormalHorizonGreenResolvedClass] using hzero
  · intro hzero
    rw [adaptivePrimeNormalHorizonGreenResolvedClass, hzero]
    exact map_zero _

end DeningerMeyerGaussianGreen

end
end RHTower
