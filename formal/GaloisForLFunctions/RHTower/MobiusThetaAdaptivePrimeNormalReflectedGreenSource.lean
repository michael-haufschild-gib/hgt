import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalHorizonIntertwiner
import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalResolvedSector
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianHarmonicSourcePrimitive

/-!
# Reflected adaptive prime-normal Green source

The exact adaptive reader at one divisor copy is uniformly within `1/4` of
the prime head `-1`, but its divisor-dependent depth need not respect
functional-equation reflection.  Direct transport of the reflected Gaussian
source through that reader therefore need not commute with completed source
Green reflection.

This file constructs the forced two-ended correction: average the exact
reader at a divisor copy and its functional-equation mate.  The average is
still the augmentation of literal adaptive prime-normal source columns, is
reflection-even by construction, and remains within `1/4` of `-1`.  It
therefore defines a boundedly invertible diagonal automorphism of the whole
Xi divisor Hilbert carrier with lower modulus `3/4`, upper modulus `5/4`, and
inverse bound `4/3`.

Reflection-evenness makes this automorphism commute exactly with completed
source Green reflection.  Transporting the literal two-line prime--Gamma
Cauchy boundary and its harmonic orientation now gives, for every fixed
prime label, an unconditional source boundary, horizon column, and exact
completed Green primitive.  This closes the reflected source-primitive
compatibility wall.  It does not assert that the resulting Green fracture
vanishes; the source codiagonal differential remains the RH-bearing gate.
-/

open Complex Function MeasureTheory Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The exact adaptive prime reader is uniformly within `1/4` of its isolated
Möbius prime head `-1`. -/
theorem norm_adaptivePrimeNormalDivisorReader_single_add_one_le_quarter
    (q : XiZeroCopy) (p : Nat.Primes) :
    ‖adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) + 1‖ ≤
      (1 / 4 : ℝ) := by
  let tail := adaptivePrimeNormalTailColumn p
    (xiAdaptivePrimeNormalScale q) (xiSpectralPointSupport q.1)
  have hreader :
      adaptivePrimeNormalDivisorReader q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) =
        -1 + adaptiveArithmeticL1Augmentation tail := by
    rw [adaptivePrimeNormalDivisorReader,
      ContinuousLinearMap.comp_apply,
      adaptivePrimeNormalCodiagonal_source_column,
      map_add, adaptiveArithmeticL1Augmentation_diagonal_single]
  have htail : ‖adaptiveArithmeticL1Augmentation tail‖ ≤ (1 / 4 : ℝ) := by
    calc
      ‖adaptiveArithmeticL1Augmentation tail‖ ≤ ‖tail‖ :=
        norm_adaptiveArithmeticL1Augmentation_le _
      _ ≤ 1 / 4 := norm_adaptivePrimeNormalTailColumn_le_quarter p
        (xiAdaptivePrimeNormalScale_spec q)
  rw [hreader]
  have heq :
      (-1 : ℂ) + adaptiveArithmeticL1Augmentation tail + 1 =
        adaptiveArithmeticL1Augmentation tail := by ring
  rw [heq]
  exact htail

/-- Average of the two exact post-prime arithmetic tails at a divisor copy
and its functional-equation mate.  Symmetrization occurs on the full source
operator before coefficient augmentation. -/
def adaptivePrimeNormalReflectedTailOperator (q : XiZeroCopy) :
    AdaptivePrimeL1 →L[ℂ] AdaptiveArithmeticL1 :=
  (1 / 2 : ℂ) •
    (adaptivePrimeNormalTailOperator
        (xiAdaptivePrimeNormalScale q)
        (xiSpectralPointSupport q.1)
        (xiAdaptivePrimeNormalScale_spec q) +
      adaptivePrimeNormalTailOperator
        (xiAdaptivePrimeNormalScale (xiZeroCopyReflectEquiv q))
        (xiSpectralPointSupport (xiZeroCopyReflectEquiv q).1)
        (xiAdaptivePrimeNormalScale_spec (xiZeroCopyReflectEquiv q)))

theorem norm_adaptivePrimeNormalReflectedTailOperator_le_quarter
    (q : XiZeroCopy) (x : AdaptivePrimeL1) :
    ‖adaptivePrimeNormalReflectedTailOperator q x‖ ≤
      (1 / 4 : ℝ) * ‖x‖ := by
  let Tq := adaptivePrimeNormalTailOperator
    (xiAdaptivePrimeNormalScale q)
    (xiSpectralPointSupport q.1)
    (xiAdaptivePrimeNormalScale_spec q)
  let Tr := adaptivePrimeNormalTailOperator
    (xiAdaptivePrimeNormalScale (xiZeroCopyReflectEquiv q))
    (xiSpectralPointSupport (xiZeroCopyReflectEquiv q).1)
    (xiAdaptivePrimeNormalScale_spec (xiZeroCopyReflectEquiv q))
  have hq : ‖Tq x‖ ≤ (1 / 4 : ℝ) * ‖x‖ :=
    norm_adaptivePrimeNormalTailOperator_le_quarter _ _ _ x
  have hr : ‖Tr x‖ ≤ (1 / 4 : ℝ) * ‖x‖ :=
    norm_adaptivePrimeNormalTailOperator_le_quarter _ _ _ x
  rw [adaptivePrimeNormalReflectedTailOperator,
    _root_.smul_apply, norm_smul]
  change ‖(1 / 2 : ℂ)‖ * ‖Tq x + Tr x‖ ≤ _
  norm_num
  calc
    (1 / 2 : ℝ) * ‖Tq x + Tr x‖ ≤
        (1 / 2 : ℝ) * (‖Tq x‖ + ‖Tr x‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) *
        ((1 / 4 : ℝ) * ‖x‖ + (1 / 4 : ℝ) * ‖x‖) := by gcongr
    _ = (1 / 4 : ℝ) * ‖x‖ := by ring

/-- Full reflected adaptive codiagonal: average the two literal adaptive
source operators before any scalar readout. -/
def adaptivePrimeNormalReflectedCodiagonal (q : XiZeroCopy) :
    AdaptivePrimeL1 →L[ℂ] AdaptiveArithmeticL1 :=
  adaptivePrimeNormalDiagonalEmbedding.toContinuousLinearMap +
    adaptivePrimeNormalReflectedTailOperator q

theorem adaptivePrimeNormalReflectedCodiagonal_lower
    (q : XiZeroCopy) (x : AdaptivePrimeL1) :
    (3 / 4 : ℝ) * ‖x‖ ≤
      ‖adaptivePrimeNormalReflectedCodiagonal q x‖ := by
  have hdecomp : adaptivePrimeNormalDiagonalEmbedding x =
      adaptivePrimeNormalReflectedCodiagonal q x -
        adaptivePrimeNormalReflectedTailOperator q x := by
    simp [adaptivePrimeNormalReflectedCodiagonal]
  have htri : ‖adaptivePrimeNormalDiagonalEmbedding x‖ ≤
      ‖adaptivePrimeNormalReflectedCodiagonal q x‖ +
        ‖adaptivePrimeNormalReflectedTailOperator q x‖ := by
    rw [hdecomp]
    exact norm_sub_le _ _
  have htail :=
    norm_adaptivePrimeNormalReflectedTailOperator_le_quarter q x
  rw [adaptivePrimeNormalDiagonalEmbedding.norm_map] at htri
  linarith

theorem adaptivePrimeNormalReflectedCodiagonal_injective
    (q : XiZeroCopy) :
    Function.Injective (adaptivePrimeNormalReflectedCodiagonal q) := by
  intro x y hxy
  have hzero : adaptivePrimeNormalReflectedCodiagonal q (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hlower := adaptivePrimeNormalReflectedCodiagonal_lower q (x - y)
  rw [hzero, norm_zero] at hlower
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Resolved reflected source retaining the common prime head and averaged
two-ended arithmetic tail separately. -/
def adaptivePrimeNormalReflectedResolvedSource (q : XiZeroCopy) :
    AdaptivePrimeL1 →L[ℂ]
      (AdaptiveArithmeticL1 × AdaptiveArithmeticL1) :=
  adaptivePrimeNormalDiagonalEmbedding.toContinuousLinearMap.prod
    (adaptivePrimeNormalReflectedTailOperator q)

@[simp]
theorem adaptivePrimeNormalReflectedResolvedSource_apply
    (q : XiZeroCopy) (x : AdaptivePrimeL1) :
    adaptivePrimeNormalReflectedResolvedSource q x =
      (adaptivePrimeNormalDiagonalEmbedding x,
        adaptivePrimeNormalReflectedTailOperator q x) := rfl

theorem resolvedDefectCodiagonal_adaptivePrimeNormalReflectedResolvedSource
    (q : XiZeroCopy) (x : AdaptivePrimeL1) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalReflectedResolvedSource q x) =
      adaptivePrimeNormalReflectedCodiagonal q x := by
  rfl

def adaptivePrimeNormalReflectedResolvedSector (q : XiZeroCopy) :
    Submodule ℂ (AdaptiveArithmeticL1 × AdaptiveArithmeticL1) :=
  LinearMap.range (adaptivePrimeNormalReflectedResolvedSource q).toLinearMap

theorem adaptivePrimeNormalReflectedResolvedSource_isClosed_range
    (q : XiZeroCopy) :
    IsClosed (Set.range (adaptivePrimeNormalReflectedResolvedSource q)) := by
  have hanti : AntilipschitzWith 1
      (adaptivePrimeNormalReflectedResolvedSource q) := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    change ‖x - y‖ ≤ (1 : ℝ) *
      ‖(adaptivePrimeNormalDiagonalEmbedding (x - y),
        adaptivePrimeNormalReflectedTailOperator q (x - y))‖
    rw [one_mul, Prod.norm_def,
      adaptivePrimeNormalDiagonalEmbedding.norm_map]
    exact le_max_left _ _
  exact hanti.isClosed_range
    (adaptivePrimeNormalReflectedResolvedSource q).uniformContinuous

theorem adaptivePrimeNormalReflectedResolvedSector_isClosed
    (q : XiZeroCopy) :
    IsClosed (adaptivePrimeNormalReflectedResolvedSector q :
      Set (AdaptiveArithmeticL1 × AdaptiveArithmeticL1)) := by
  change IsClosed (Set.range (adaptivePrimeNormalReflectedResolvedSource q))
  exact adaptivePrimeNormalReflectedResolvedSource_isClosed_range q

/-- The reflected two-ended sector remains strictly conservative under the
universal codiagonal. -/
theorem adaptivePrimeNormalReflectedResolvedSector_conservative
    (q : XiZeroCopy) :
    IsConservativeOn
      (resolvedDefectCodiagonal (R := ℂ) (Z := AdaptiveArithmeticL1))
      (adaptivePrimeNormalReflectedResolvedSector q) := by
  change Disjoint
    (adaptivePrimeNormalReflectedResolvedSector q)
    (LinearMap.ker
      (resolvedDefectCodiagonal (R := ℂ) (Z := AdaptiveArithmeticL1)))
  rw [Submodule.disjoint_def]
  intro z hzrange hzkernel
  obtain ⟨x, rfl⟩ := hzrange
  have hcx : adaptivePrimeNormalReflectedCodiagonal q x = 0 := by
    change resolvedDefectCodiagonal (R := ℂ)
      (adaptivePrimeNormalReflectedResolvedSource q x) = 0 at hzkernel
    rw [resolvedDefectCodiagonal_adaptivePrimeNormalReflectedResolvedSource]
      at hzkernel
    exact hzkernel
  have hx : x = 0 :=
    adaptivePrimeNormalReflectedCodiagonal_injective q (by simpa using hcx)
  subst x
  exact map_zero _

/-- Canonical scalar-line comparison into the full reflected source sector. -/
def adaptivePrimeNormalReflectedResolvedLineComparison
    (q : XiZeroCopy) (p : Nat.Primes) :
    ℂ →L[ℂ] (AdaptiveArithmeticL1 × AdaptiveArithmeticL1) :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight
    (adaptivePrimeNormalReflectedResolvedSource q
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1))

@[simp]
theorem adaptivePrimeNormalReflectedResolvedLineComparison_apply
    (q : XiZeroCopy) (p : Nat.Primes) (c : ℂ) :
    adaptivePrimeNormalReflectedResolvedLineComparison q p c =
      c • adaptivePrimeNormalReflectedResolvedSource q
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) := by
  rw [adaptivePrimeNormalReflectedResolvedLineComparison,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]

theorem adaptivePrimeNormalReflectedResolvedLineComparison_mem_sector
    (q : XiZeroCopy) (p : Nat.Primes) (c : ℂ) :
    adaptivePrimeNormalReflectedResolvedLineComparison q p c ∈
      adaptivePrimeNormalReflectedResolvedSector q := by
  refine ⟨c • lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1, ?_⟩
  rw [map_smul,
    adaptivePrimeNormalReflectedResolvedLineComparison_apply]
  rfl

theorem adaptivePrimeNormalReflectedCodiagonal_single_ne_zero
    (q : XiZeroCopy) (p : Nat.Primes) :
    adaptivePrimeNormalReflectedCodiagonal q
      (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) ≠ 0 := by
  intro hzero
  have hlower := adaptivePrimeNormalReflectedCodiagonal_lower q
    (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)
  rw [hzero, norm_zero] at hlower
  have hsingle :
      ‖(lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1 :
        AdaptivePrimeL1)‖ = 1 := by
    simp [lp.norm_single]
  rw [hsingle] at hlower
  norm_num at hlower

theorem adaptivePrimeNormalReflectedResolvedLineComparison_codiagonal
    (q : XiZeroCopy) (p : Nat.Primes) (c : ℂ) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalReflectedResolvedLineComparison q p c) =
      c • adaptivePrimeNormalReflectedCodiagonal q
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) := by
  rw [adaptivePrimeNormalReflectedResolvedLineComparison_apply, map_smul,
    resolvedDefectCodiagonal_adaptivePrimeNormalReflectedResolvedSource]

/-- Exact zero fibre on the reflected common-test line.  Thus Green/source
primitive compatibility alone cannot establish codiagonal vanishing without
establishing the Green scalar itself is zero. -/
theorem adaptivePrimeNormalReflectedResolvedLineComparison_codiagonal_eq_zero_iff
    (q : XiZeroCopy) (p : Nat.Primes) (c : ℂ) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalReflectedResolvedLineComparison q p c) = 0 ↔
      c = 0 := by
  rw [adaptivePrimeNormalReflectedResolvedLineComparison_codiagonal]
  constructor
  · intro hzero
    exact (smul_eq_zero.mp hzero).resolve_right
      (adaptivePrimeNormalReflectedCodiagonal_single_ne_zero q p)
  · rintro rfl
    exact zero_smul _ _

/-- Scalar reflected divisor reader is augmentation of the full reflected
source codiagonal. -/
def adaptivePrimeNormalReflectedDivisorReader (q : XiZeroCopy) :
    AdaptivePrimeL1 →L[ℂ] ℂ :=
  adaptiveArithmeticL1Augmentation.comp
    (adaptivePrimeNormalReflectedCodiagonal q)

/-- Functional-equation symmetrization of one exact adaptive prime reader. -/
def adaptivePrimeNormalReflectedReader
    (p : Nat.Primes) (q : XiZeroCopy) : ℂ :=
  (1 / 2 : ℂ) *
    (adaptivePrimeNormalDivisorReader q
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) +
      adaptivePrimeNormalDivisorReader (xiZeroCopyReflectEquiv q)
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1))

theorem adaptivePrimeNormalReflectedDivisorReader_single
    (q : XiZeroCopy) (p : Nat.Primes) :
    adaptivePrimeNormalReflectedDivisorReader q
        (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) =
      adaptivePrimeNormalReflectedReader p q := by
  let e : AdaptivePrimeL1 :=
    lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1
  let Tq := adaptivePrimeNormalTailOperator
    (xiAdaptivePrimeNormalScale q)
    (xiSpectralPointSupport q.1)
    (xiAdaptivePrimeNormalScale_spec q)
  let Tr := adaptivePrimeNormalTailOperator
    (xiAdaptivePrimeNormalScale (xiZeroCopyReflectEquiv q))
    (xiSpectralPointSupport (xiZeroCopyReflectEquiv q).1)
    (xiAdaptivePrimeNormalScale_spec (xiZeroCopyReflectEquiv q))
  have hq : adaptivePrimeNormalDivisorReader q e =
      adaptiveArithmeticL1Augmentation
        (adaptivePrimeNormalDiagonalEmbedding e + Tq e) := by
    rfl
  have hr : adaptivePrimeNormalDivisorReader (xiZeroCopyReflectEquiv q) e =
      adaptiveArithmeticL1Augmentation
        (adaptivePrimeNormalDiagonalEmbedding e + Tr e) := by
    rfl
  rw [adaptivePrimeNormalReflectedDivisorReader,
    ContinuousLinearMap.comp_apply,
    adaptivePrimeNormalReflectedCodiagonal,
    adaptivePrimeNormalReflectedTailOperator,
    _root_.add_apply, _root_.smul_apply,
    LinearIsometry.coe_toContinuousLinearMap,
    adaptivePrimeNormalReflectedReader, hq, hr]
  simp only [map_add, map_smul, _root_.add_apply, smul_eq_mul]
  ring

/-- The reflected reader is exactly invariant under functional-equation
reflection, including multiplicity copies. -/
theorem adaptivePrimeNormalReflectedReader_reflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedReader p (xiZeroCopyReflectEquiv q) =
      adaptivePrimeNormalReflectedReader p q := by
  rw [adaptivePrimeNormalReflectedReader,
    adaptivePrimeNormalReflectedReader,
    xiZeroCopyReflectEquiv_apply_apply]
  ring

/-- Averaging the two exact source columns does not lose the prime-head
lower modulus. -/
theorem norm_adaptivePrimeNormalReflectedReader_add_one_le_quarter
    (p : Nat.Primes) (q : XiZeroCopy) :
    ‖adaptivePrimeNormalReflectedReader p q + 1‖ ≤ (1 / 4 : ℝ) := by
  let a := adaptivePrimeNormalDivisorReader q
    (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)
  let b := adaptivePrimeNormalDivisorReader (xiZeroCopyReflectEquiv q)
    (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1)
  have ha : ‖a + 1‖ ≤ (1 / 4 : ℝ) :=
    norm_adaptivePrimeNormalDivisorReader_single_add_one_le_quarter q p
  have hb : ‖b + 1‖ ≤ (1 / 4 : ℝ) :=
    norm_adaptivePrimeNormalDivisorReader_single_add_one_le_quarter
      (xiZeroCopyReflectEquiv q) p
  have hsum : ‖(a + 1) + (b + 1)‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖(a + 1) + (b + 1)‖ ≤ ‖a + 1‖ + ‖b + 1‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add ha hb
      _ = 1 / 2 := by ring
  rw [adaptivePrimeNormalReflectedReader]
  change ‖(1 / 2 : ℂ) * (a + b) + 1‖ ≤ _
  have heq : (1 / 2 : ℂ) * (a + b) + 1 =
      (1 / 2 : ℂ) * ((a + 1) + (b + 1)) := by ring
  rw [heq, norm_mul]
  norm_num
  linarith

theorem adaptivePrimeNormalReflectedReader_lower
    (p : Nat.Primes) (q : XiZeroCopy) :
    (3 / 4 : ℝ) ≤ ‖adaptivePrimeNormalReflectedReader p q‖ := by
  have hclose :=
    norm_adaptivePrimeNormalReflectedReader_add_one_le_quarter p q
  have hreverse := norm_sub_norm_le (1 : ℂ)
    (adaptivePrimeNormalReflectedReader p q + 1)
  have heq :
      ‖(1 : ℂ) - (adaptivePrimeNormalReflectedReader p q + 1)‖ =
        ‖adaptivePrimeNormalReflectedReader p q‖ := by
    rw [show (1 : ℂ) - (adaptivePrimeNormalReflectedReader p q + 1) =
      -adaptivePrimeNormalReflectedReader p q by ring, norm_neg]
  rw [norm_one, heq] at hreverse
  linarith

theorem adaptivePrimeNormalReflectedReader_upper
    (p : Nat.Primes) (q : XiZeroCopy) :
    ‖adaptivePrimeNormalReflectedReader p q‖ ≤ (5 / 4 : ℝ) := by
  have hclose :=
    norm_adaptivePrimeNormalReflectedReader_add_one_le_quarter p q
  have htri := norm_sub_le
    (adaptivePrimeNormalReflectedReader p q + 1) (1 : ℂ)
  have heq :
      ‖(adaptivePrimeNormalReflectedReader p q + 1) - 1‖ =
        ‖adaptivePrimeNormalReflectedReader p q‖ := by
    congr 1
    ring
  rw [heq, norm_one] at htri
  linarith

theorem adaptivePrimeNormalReflectedReader_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedReader p q ≠ 0 := by
  intro hzero
  have hlower := adaptivePrimeNormalReflectedReader_lower p q
  rw [hzero, norm_zero] at hlower
  norm_num at hlower

/-- Contractive normalization of the reflected exact reader. -/
def adaptivePrimeNormalReflectedReaderMultiplier
    (p : Nat.Primes) (q : XiZeroCopy) : ℂ :=
  (4 / 5 : ℂ) * adaptivePrimeNormalReflectedReader p q

theorem norm_adaptivePrimeNormalReflectedReaderMultiplier_le_one
    (p : Nat.Primes) (q : XiZeroCopy) :
    ‖adaptivePrimeNormalReflectedReaderMultiplier p q‖ ≤ 1 := by
  rw [adaptivePrimeNormalReflectedReaderMultiplier, norm_mul]
  norm_num
  nlinarith [adaptivePrimeNormalReflectedReader_upper p q]

/-- Reflection-compatible fixed-prime automorphism of the complete divisor
Hilbert carrier. -/
def adaptivePrimeNormalReflectedHorizonForward (p : Nat.Primes) :
    XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  (5 / 4 : ℂ) • deningerMultiplier
    (norm_adaptivePrimeNormalReflectedReaderMultiplier_le_one p)

@[simp]
theorem adaptivePrimeNormalReflectedHorizonForward_apply
    (p : Nat.Primes) (a : XiDivisorL2) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedHorizonForward p a q =
      adaptivePrimeNormalReflectedReader p q * a q := by
  rw [adaptivePrimeNormalReflectedHorizonForward,
    _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    deningerMultiplier_apply,
    adaptivePrimeNormalReflectedReaderMultiplier]
  ring

def adaptivePrimeNormalReflectedInverseMultiplier
    (p : Nat.Primes) (q : XiZeroCopy) : ℂ :=
  (3 / 4 : ℂ) * (adaptivePrimeNormalReflectedReader p q)⁻¹

theorem norm_adaptivePrimeNormalReflectedInverseMultiplier_le_one
    (p : Nat.Primes) (q : XiZeroCopy) :
    ‖adaptivePrimeNormalReflectedInverseMultiplier p q‖ ≤ 1 := by
  have hpos : 0 < ‖adaptivePrimeNormalReflectedReader p q‖ :=
    norm_pos_iff.mpr (adaptivePrimeNormalReflectedReader_ne_zero p q)
  rw [adaptivePrimeNormalReflectedInverseMultiplier, norm_mul, norm_inv]
  norm_num
  rw [← div_eq_mul_inv, div_le_one hpos]
  exact adaptivePrimeNormalReflectedReader_lower p q

def adaptivePrimeNormalReflectedHorizonInverse (p : Nat.Primes) :
    XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  (4 / 3 : ℂ) • deningerMultiplier
    (norm_adaptivePrimeNormalReflectedInverseMultiplier_le_one p)

@[simp]
theorem adaptivePrimeNormalReflectedHorizonInverse_apply
    (p : Nat.Primes) (a : XiDivisorL2) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedHorizonInverse p a q =
      (adaptivePrimeNormalReflectedReader p q)⁻¹ * a q := by
  rw [adaptivePrimeNormalReflectedHorizonInverse,
    _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    deningerMultiplier_apply,
    adaptivePrimeNormalReflectedInverseMultiplier]
  ring

theorem adaptivePrimeNormalReflectedHorizonInverse_forward
    (p : Nat.Primes) (a : XiDivisorL2) :
    adaptivePrimeNormalReflectedHorizonInverse p
        (adaptivePrimeNormalReflectedHorizonForward p a) = a := by
  ext q
  rw [adaptivePrimeNormalReflectedHorizonInverse_apply,
    adaptivePrimeNormalReflectedHorizonForward_apply]
  field_simp [adaptivePrimeNormalReflectedReader_ne_zero p q]

theorem adaptivePrimeNormalReflectedHorizonForward_inverse
    (p : Nat.Primes) (a : XiDivisorL2) :
    adaptivePrimeNormalReflectedHorizonForward p
        (adaptivePrimeNormalReflectedHorizonInverse p a) = a := by
  ext q
  rw [adaptivePrimeNormalReflectedHorizonForward_apply,
    adaptivePrimeNormalReflectedHorizonInverse_apply]
  field_simp [adaptivePrimeNormalReflectedReader_ne_zero p q]

theorem norm_adaptivePrimeNormalReflectedHorizonForward_le
    (p : Nat.Primes) (a : XiDivisorL2) :
    ‖adaptivePrimeNormalReflectedHorizonForward p a‖ ≤
      (5 / 4 : ℝ) * ‖a‖ := by
  rw [adaptivePrimeNormalReflectedHorizonForward,
    _root_.smul_apply, norm_smul]
  norm_num
  change ‖deningerMultiplierMap
      (norm_adaptivePrimeNormalReflectedReaderMultiplier_le_one p) a‖ ≤ ‖a‖
  simpa using deningerMultiplierMap_norm_le
    (norm_adaptivePrimeNormalReflectedReaderMultiplier_le_one p) a

theorem norm_adaptivePrimeNormalReflectedHorizonInverse_le
    (p : Nat.Primes) (a : XiDivisorL2) :
    ‖adaptivePrimeNormalReflectedHorizonInverse p a‖ ≤
      (4 / 3 : ℝ) * ‖a‖ := by
  rw [adaptivePrimeNormalReflectedHorizonInverse,
    _root_.smul_apply, norm_smul]
  norm_num
  change ‖deningerMultiplierMap
      (norm_adaptivePrimeNormalReflectedInverseMultiplier_le_one p) a‖ ≤ ‖a‖
  simpa using deningerMultiplierMap_norm_le
    (norm_adaptivePrimeNormalReflectedInverseMultiplier_le_one p) a

theorem adaptivePrimeNormalReflectedHorizonForward_lower
    (p : Nat.Primes) (a : XiDivisorL2) :
    (3 / 4 : ℝ) * ‖a‖ ≤
      ‖adaptivePrimeNormalReflectedHorizonForward p a‖ := by
  have h := norm_adaptivePrimeNormalReflectedHorizonInverse_le p
    (adaptivePrimeNormalReflectedHorizonForward p a)
  rw [adaptivePrimeNormalReflectedHorizonInverse_forward] at h
  nlinarith [norm_nonneg a,
    norm_nonneg (adaptivePrimeNormalReflectedHorizonForward p a)]

/-- Reflection symmetrization is exactly the missing commutation law with
completed source Green reflection. -/
theorem deningerArithmeticCompletedSourceGreen_reflectedHorizonForward
    (p : Nat.Primes) (a : XiDivisorL2) :
    deningerArithmeticCompletedSourceGreen
        (adaptivePrimeNormalReflectedHorizonForward p a) =
      adaptivePrimeNormalReflectedHorizonForward p
        (deningerArithmeticCompletedSourceGreen a) := by
  ext q
  rw [deningerArithmeticCompletedSourceGreen_apply,
    adaptivePrimeNormalReflectedHorizonForward_apply,
    adaptivePrimeNormalReflectedHorizonForward_apply,
    deningerArithmeticCompletedSourceGreen_apply,
    adaptivePrimeNormalReflectedReader_reflect]
  ring

/-- The reflected multiplier also preserves the physical diagonal harmonic
Hodge sector. -/
theorem deningerXiHarmonicHodge_reflectedHorizonForward
    (p : Nat.Primes) (a : XiDivisorL2) :
    deningerXiHarmonicHodge
        (adaptivePrimeNormalReflectedHorizonForward p a) =
      adaptivePrimeNormalReflectedHorizonForward p
        (deningerXiHarmonicHodge a) := by
  ext q
  rw [deningerXiHarmonicHodge_apply,
    adaptivePrimeNormalReflectedHorizonForward_apply,
    adaptivePrimeNormalReflectedHorizonForward_apply,
    deningerXiHarmonicHodge_apply]
  ring

namespace DeningerMeyerGaussianGreen

/-- Reflected adaptive horizon column with exact fixed-prime provenance. -/
def adaptivePrimeNormalReflectedHorizonColumn
    (p : Nat.Primes) : XiDivisorL2 :=
  adaptivePrimeNormalReflectedHorizonForward p reflectedGaussianHorizonGradeL2

@[simp]
theorem adaptivePrimeNormalReflectedHorizonColumn_apply
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedHorizonColumn p q =
      adaptivePrimeNormalReflectedReader p q *
        reflectedGaussianHorizonGrade q := by
  rw [adaptivePrimeNormalReflectedHorizonColumn,
    adaptivePrimeNormalReflectedHorizonForward_apply,
    reflectedGaussianHorizonGradeL2_apply]

theorem adaptivePrimeNormalReflectedHorizonColumn_apply_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedHorizonColumn p q ≠ 0 := by
  rw [adaptivePrimeNormalReflectedHorizonColumn_apply]
  exact mul_ne_zero (adaptivePrimeNormalReflectedReader_ne_zero p q)
    (reflectedGaussianHorizonGrade_ne_zero q)

/-- Completed Green provenance of the reflected, source-compatible adaptive
horizon column. -/
def adaptivePrimeNormalReflectedHorizonGreenProvenance
    (p : Nat.Primes) : XiDivisorL2 :=
  deningerArithmeticCompletedGreenProvenance
    (adaptivePrimeNormalReflectedHorizonColumn p)

/-- Green compatibility does not smuggle in vanishing: the reflected column
remains a faithful global RH detector. -/
theorem adaptivePrimeNormalReflectedHorizonGreenProvenance_eq_zero_iff_riemannHypothesis
    (p : Nat.Primes) :
    adaptivePrimeNormalReflectedHorizonGreenProvenance p = 0 ↔
      RiemannHypothesis := by
  exact
    deningerArithmeticCompletedGreenProvenance_eq_zero_iff_riemannHypothesis_of_pointwise_ne_zero
      (adaptivePrimeNormalReflectedHorizonColumn p)
      (adaptivePrimeNormalReflectedHorizonColumn_apply_ne_zero p)

/-- Local completed Green coefficient of the reflected adaptive horizon. -/
def adaptivePrimeNormalReflectedHorizonGreenCoefficient
    (p : Nat.Primes) (q : XiZeroCopy) : ℂ :=
  adaptivePrimeNormalReflectedHorizonGreenProvenance p q

theorem adaptivePrimeNormalReflectedHorizonGreenCoefficient_eq_zero_iff
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedHorizonGreenCoefficient p q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hright :
      deningerArithmeticOrientedHodgeLp
        (deningerArithmeticCompletedRieszConjugation
          (adaptivePrimeNormalReflectedHorizonColumn p)) q ≠ 0 := by
    rw [deningerArithmeticOrientedHodgeLp_apply,
      deningerArithmeticCompletedRieszConjugation_apply]
    apply mul_ne_zero
    · exact neg_ne_zero.mpr (deningerArithmeticFEOrientation_ne_zero q)
    · rw [starRingEnd_self_apply]
      exact adaptivePrimeNormalReflectedHorizonColumn_apply_ne_zero p
        (xiZeroCopyReflectEquiv q)
  rw [adaptivePrimeNormalReflectedHorizonGreenCoefficient,
    adaptivePrimeNormalReflectedHorizonGreenProvenance,
    deningerArithmeticCompletedGreenProvenance_apply]
  constructor
  · intro hzero
    exact (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (q.1 : ℂ)).mp
      ((mul_eq_zero.mp hzero).resolve_right hright)
  · intro hline
    rw [(xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
      (q.1 : ℂ)).2 hline, zero_mul]

/-- Actual reflected common-test candidate for one local Green coefficient. -/
def adaptivePrimeNormalReflectedActualGreenComparison
    (p : Nat.Primes) (q : XiZeroCopy) :
    AdaptiveArithmeticL1 × AdaptiveArithmeticL1 :=
  adaptivePrimeNormalReflectedResolvedLineComparison q p
    (adaptivePrimeNormalReflectedHorizonGreenCoefficient p q)

theorem adaptivePrimeNormalReflectedActualGreenComparison_mem_sector
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedActualGreenComparison p q ∈
      adaptivePrimeNormalReflectedResolvedSector q :=
  adaptivePrimeNormalReflectedResolvedLineComparison_mem_sector q p _

/-- For the literal reflected source object, paper condition `(7.17c).2` is
exactly the local critical-line statement.  Conditions `.1` and `.3` are
already unconditional. -/
theorem adaptivePrimeNormalReflectedActualGreenComparison_codiagonal_eq_zero_iff
    (p : Nat.Primes) (q : XiZeroCopy) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalReflectedActualGreenComparison p q) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [adaptivePrimeNormalReflectedActualGreenComparison,
    adaptivePrimeNormalReflectedResolvedLineComparison_codiagonal_eq_zero_iff,
    adaptivePrimeNormalReflectedHorizonGreenCoefficient_eq_zero_iff]

/-- Literal two-line prime--Gamma boundary transported through the reflected
adaptive source automorphism. -/
def adaptivePrimeNormalReflectedPrimeGammaCauchyBoundary
    (p : Nat.Primes) (x : ℝ) : XiDivisorL2 :=
  adaptivePrimeNormalReflectedHorizonForward p
    (reflectedGaussianPrimeGammaCauchyBoundary x)

theorem integrable_adaptivePrimeNormalReflectedPrimeGammaCauchyBoundary
    (p : Nat.Primes) :
    Integrable (adaptivePrimeNormalReflectedPrimeGammaCauchyBoundary p) := by
  exact (adaptivePrimeNormalReflectedHorizonForward p).integrable_comp
    integrable_reflectedGaussianPrimeGammaCauchyBoundary

theorem integral_adaptivePrimeNormalReflectedPrimeGammaCauchyBoundary
    (p : Nat.Primes) :
    (∫ x : ℝ, adaptivePrimeNormalReflectedPrimeGammaCauchyBoundary p x) =
      adaptivePrimeNormalReflectedHorizonColumn p := by
  have hcomm := (adaptivePrimeNormalReflectedHorizonForward p).integral_comp_comm
    integrable_reflectedGaussianPrimeGammaCauchyBoundary
  change (∫ x : ℝ, adaptivePrimeNormalReflectedHorizonForward p
    (reflectedGaussianPrimeGammaCauchyBoundary x)) = _
  rw [hcomm,
    integral_reflectedGaussianPrimeGammaCauchyBoundary_eq_horizonGradeL2]
  rfl

/-- Physical harmonic/Green primitive of the reflected adaptive horizon. -/
def adaptivePrimeNormalReflectedCompletedGreenPrimitive
    (p : Nat.Primes) : XiDivisorL2 :=
  adaptivePrimeNormalReflectedHorizonForward p
    reflectedGaussianHorizonCompletedGreenPrimitive

theorem adaptivePrimeNormalReflectedCompletedGreenPrimitive_green
    (p : Nat.Primes) :
    deningerArithmeticCompletedSourceGreen
        (adaptivePrimeNormalReflectedCompletedGreenPrimitive p) =
      adaptivePrimeNormalReflectedHorizonColumn p := by
  rw [adaptivePrimeNormalReflectedCompletedGreenPrimitive,
    deningerArithmeticCompletedSourceGreen_reflectedHorizonForward,
    reflectedGaussianHorizonCompletedGreenPrimitive_green]
  apply congrArg (adaptivePrimeNormalReflectedHorizonForward p)
  ext q
  rw [reflectedGaussianHorizonAdmittedResidue_apply,
    reflectedGaussianHorizonGradeL2_apply]

/-- Oriented literal prime--Gamma boundary for the reflected adaptive Green
primitive. -/
def adaptivePrimeNormalReflectedPrimeGammaOrientedCauchyBoundary
    (p : Nat.Primes) (x : ℝ) : XiDivisorL2 :=
  adaptivePrimeNormalReflectedHorizonForward p
    (reflectedGaussianPrimeGammaOrientedCauchyBoundary x)

theorem integrable_adaptivePrimeNormalReflectedPrimeGammaOrientedCauchyBoundary
    (p : Nat.Primes) :
    Integrable
      (adaptivePrimeNormalReflectedPrimeGammaOrientedCauchyBoundary p) := by
  exact (adaptivePrimeNormalReflectedHorizonForward p).integrable_comp
    integrable_reflectedGaussianPrimeGammaOrientedCauchyBoundary

theorem integral_adaptivePrimeNormalReflectedPrimeGammaOrientedCauchyBoundary
    (p : Nat.Primes) :
    (∫ x : ℝ,
      adaptivePrimeNormalReflectedPrimeGammaOrientedCauchyBoundary p x) =
      adaptivePrimeNormalReflectedCompletedGreenPrimitive p := by
  have hcomm := (adaptivePrimeNormalReflectedHorizonForward p).integral_comp_comm
    integrable_reflectedGaussianPrimeGammaOrientedCauchyBoundary
  change (∫ x : ℝ, adaptivePrimeNormalReflectedHorizonForward p
    (reflectedGaussianPrimeGammaOrientedCauchyBoundary x)) = _
  rw [hcomm,
    integral_reflectedGaussianPrimeGammaOrientedCauchyBoundary_eq_greenPrimitive]
  rfl

/-- The transported primitive is still the physical harmonic Hodge transform
of its transported Gaussian horizon. -/
theorem adaptivePrimeNormalReflectedCompletedGreenPrimitive_eq_harmonicHodge
    (p : Nat.Primes) :
    adaptivePrimeNormalReflectedCompletedGreenPrimitive p =
      Complex.I • deningerXiHarmonicHodge
        (adaptivePrimeNormalReflectedHorizonColumn p) := by
  have hgrade : reflectedGaussianHorizonAdmittedResidue =
      reflectedGaussianHorizonGradeL2 := by
    ext q
    rw [reflectedGaussianHorizonAdmittedResidue_apply,
      reflectedGaussianHorizonGradeL2_apply]
  rw [adaptivePrimeNormalReflectedCompletedGreenPrimitive,
    reflectedGaussianHorizonCompletedGreenPrimitive_eq_harmonicHodge,
    map_smul, adaptivePrimeNormalReflectedHorizonColumn,
    ← deningerXiHarmonicHodge_reflectedHorizonForward, hgrade]

end DeningerMeyerGaussianGreen

end

end RHTower
