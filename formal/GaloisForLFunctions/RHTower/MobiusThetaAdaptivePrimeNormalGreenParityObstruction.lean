import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalGlobalReflectedComparison

/-!
# Double-odd parity obstruction for the reflected adaptive Green record

The reflected adaptive source, horizon column, resolved unit, and global
codiagonal are invariant under functional-equation reflection.  The completed
Green construction does not reverse that parity: its boundary-fracture
multiplier and oriented Hodge sign are both reflection-odd, so their product is
reflection-even.

Consequently the actual global Green record is reflection-even.  Asking it,
or its conservative codiagonal, to be reflection-odd forces it to vanish and
is equivalent to the Riemann hypothesis.  Thus reflection-odd observation
descent cannot provide an unconditional annihilator for this source object;
the needed oddness is already the target theorem.
-/

open Complex Function Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Reflection exchanges the two exact arithmetic tails, leaving their
average fixed. -/
theorem adaptivePrimeNormalReflectedTailOperator_reflect (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedTailOperator (xiZeroCopyReflectEquiv q) =
      adaptivePrimeNormalReflectedTailOperator q := by
  ext x
  simp only [adaptivePrimeNormalReflectedTailOperator,
    _root_.smul_apply, _root_.add_apply,
    xiZeroCopyReflectEquiv_apply_apply]
  rw [add_comm]

/-- The full reflected source codiagonal is reflection-invariant. -/
theorem adaptivePrimeNormalReflectedCodiagonal_reflect (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedCodiagonal (xiZeroCopyReflectEquiv q) =
      adaptivePrimeNormalReflectedCodiagonal q := by
  rw [adaptivePrimeNormalReflectedCodiagonal,
    adaptivePrimeNormalReflectedCodiagonal,
    adaptivePrimeNormalReflectedTailOperator_reflect]

/-- The head--tail resolved source map is reflection-invariant. -/
theorem adaptivePrimeNormalReflectedResolvedSource_reflect (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedResolvedSource (xiZeroCopyReflectEquiv q) =
      adaptivePrimeNormalReflectedResolvedSource q := by
  rw [adaptivePrimeNormalReflectedResolvedSource,
    adaptivePrimeNormalReflectedResolvedSource,
    adaptivePrimeNormalReflectedTailOperator_reflect]

/-- Every fixed-prime resolved unit is reflection-invariant. -/
theorem adaptivePrimeNormalReflectedResolvedUnit_reflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedResolvedUnit p (xiZeroCopyReflectEquiv q) =
      adaptivePrimeNormalReflectedResolvedUnit p q := by
  rw [adaptivePrimeNormalReflectedResolvedUnit,
    adaptivePrimeNormalReflectedResolvedUnit,
    adaptivePrimeNormalReflectedResolvedSource_reflect]

namespace DeningerMeyerGaussianGreen

/-- Double-odd law: on a reflection-fixed input, the odd boundary fracture
and odd Hodge orientation make completed Green provenance reflection-even. -/
theorem deningerArithmeticCompletedGreenProvenance_reflect_of_reflectFixed
    (a : XiDivisorL2)
    (ha : ∀ q : XiZeroCopy,
      a (xiZeroCopyReflectEquiv q) = a q)
    (q : XiZeroCopy) :
    deningerArithmeticCompletedGreenProvenance a
        (xiZeroCopyReflectEquiv q) =
      deningerArithmeticCompletedGreenProvenance a q := by
  rw [deningerArithmeticCompletedGreenProvenance_apply,
    deningerArithmeticCompletedGreenProvenance_apply,
    xiNearbyPoleDualityAdjunctionFracture_reflect,
    deningerArithmeticOrientedHodgeLp_apply,
    deningerArithmeticOrientedHodgeLp_apply,
    deningerArithmeticCompletedRieszConjugation_apply,
    deningerArithmeticCompletedRieszConjugation_apply,
    xiZeroCopyReflectEquiv_apply_apply,
    deningerArithmeticFEOrientation_reflect,
    starRingEnd_self_apply, starRingEnd_self_apply,
    ha q]
  ring

/-- The reflected adaptive horizon column belongs to the even reflection
sector. -/
theorem adaptivePrimeNormalReflectedHorizonColumn_reflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedHorizonColumn p
        (xiZeroCopyReflectEquiv q) =
      adaptivePrimeNormalReflectedHorizonColumn p q := by
  rw [adaptivePrimeNormalReflectedHorizonColumn_apply,
    adaptivePrimeNormalReflectedHorizonColumn_apply,
    adaptivePrimeNormalReflectedReader_reflect,
    reflectedGaussianHorizonGrade_reflect]

/-- Actual completed Green provenance remains reflection-even. -/
theorem adaptivePrimeNormalReflectedHorizonGreenProvenance_reflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalReflectedHorizonGreenProvenance p
        (xiZeroCopyReflectEquiv q) =
      adaptivePrimeNormalReflectedHorizonGreenProvenance p q := by
  exact deningerArithmeticCompletedGreenProvenance_reflect_of_reflectFixed
    (adaptivePrimeNormalReflectedHorizonColumn p)
    (adaptivePrimeNormalReflectedHorizonColumn_reflect p) q

/-- The literal assembled head--tail Green record is reflection-even. -/
theorem adaptivePrimeNormalGlobalReflectedGreenRecord_reflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalGlobalReflectedGreenRecord p
        (xiZeroCopyReflectEquiv q) =
      adaptivePrimeNormalGlobalReflectedGreenRecord p q := by
  rw [adaptivePrimeNormalGlobalReflectedGreenRecord,
    adaptivePrimeNormalGlobalReflectedComparison_apply,
    adaptivePrimeNormalGlobalReflectedComparison_apply,
    adaptivePrimeNormalReflectedHorizonGreenProvenance_reflect,
    adaptivePrimeNormalReflectedResolvedUnit_reflect]

/-- The conservative global codiagonal of the actual Green record is also
reflection-even. -/
theorem adaptivePrimeNormalGlobalReflectedGreenCodiagonal_reflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalGlobalReflectedCodiagonal p
        (adaptivePrimeNormalReflectedHorizonGreenProvenance p)
        (xiZeroCopyReflectEquiv q) =
      adaptivePrimeNormalGlobalReflectedCodiagonal p
        (adaptivePrimeNormalReflectedHorizonGreenProvenance p) q := by
  rw [adaptivePrimeNormalGlobalReflectedCodiagonal_apply,
    adaptivePrimeNormalGlobalReflectedCodiagonal_apply,
    adaptivePrimeNormalReflectedHorizonGreenProvenance_reflect,
    adaptivePrimeNormalReflectedCodiagonal_reflect]

/-- If the even actual Green provenance were also reflection-odd, it would
vanish identically. -/
theorem adaptivePrimeNormalReflectedHorizonGreenProvenance_eq_zero_of_reflectOdd
    (p : Nat.Primes)
    (hodd : ∀ q : XiZeroCopy,
      adaptivePrimeNormalReflectedHorizonGreenProvenance p
          (xiZeroCopyReflectEquiv q) =
        -adaptivePrimeNormalReflectedHorizonGreenProvenance p q) :
    adaptivePrimeNormalReflectedHorizonGreenProvenance p = 0 := by
  apply lp.ext
  funext q
  change adaptivePrimeNormalReflectedHorizonGreenProvenance p q = 0
  have heven :=
    adaptivePrimeNormalReflectedHorizonGreenProvenance_reflect p q
  have hoddq := hodd q
  rw [heven] at hoddq
  linear_combination hoddq / 2

/-- Reflection-oddness of actual Green provenance is exactly RH, not an
independent symmetry consequence. -/
theorem adaptivePrimeNormalReflectedHorizonGreenProvenance_reflectOdd_iff_riemannHypothesis
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy,
      adaptivePrimeNormalReflectedHorizonGreenProvenance p
          (xiZeroCopyReflectEquiv q) =
        -adaptivePrimeNormalReflectedHorizonGreenProvenance p q) ↔
      RiemannHypothesis := by
  constructor
  · intro hodd
    rw [← adaptivePrimeNormalReflectedHorizonGreenProvenance_eq_zero_iff_riemannHypothesis]
    exact
      adaptivePrimeNormalReflectedHorizonGreenProvenance_eq_zero_of_reflectOdd
        p hodd
  · intro hrh q
    have hzero : adaptivePrimeNormalReflectedHorizonGreenProvenance p = 0 :=
      (adaptivePrimeNormalReflectedHorizonGreenProvenance_eq_zero_iff_riemannHypothesis p).2 hrh
    rw [hzero]
    simp

/-- If the even conservative codiagonal were also reflection-odd, its global
field would vanish. -/
theorem adaptivePrimeNormalGlobalReflectedGreenCodiagonal_eq_zero_of_reflectOdd
    (p : Nat.Primes)
    (hodd : ∀ q : XiZeroCopy,
      adaptivePrimeNormalGlobalReflectedCodiagonal p
          (adaptivePrimeNormalReflectedHorizonGreenProvenance p)
          (xiZeroCopyReflectEquiv q) =
        -adaptivePrimeNormalGlobalReflectedCodiagonal p
          (adaptivePrimeNormalReflectedHorizonGreenProvenance p) q) :
    adaptivePrimeNormalGlobalReflectedCodiagonal p
        (adaptivePrimeNormalReflectedHorizonGreenProvenance p) = 0 := by
  apply lp.ext
  funext q
  change adaptivePrimeNormalGlobalReflectedCodiagonal p
      (adaptivePrimeNormalReflectedHorizonGreenProvenance p) q = 0
  have heven := adaptivePrimeNormalGlobalReflectedGreenCodiagonal_reflect p q
  have hoddq := hodd q
  rw [heven] at hoddq
  have htwo : (2 : ℂ) • adaptivePrimeNormalGlobalReflectedCodiagonal p
      (adaptivePrimeNormalReflectedHorizonGreenProvenance p) q = 0 := by
    simpa [two_smul] using congrArg
      (fun z => z + adaptivePrimeNormalGlobalReflectedCodiagonal p
        (adaptivePrimeNormalReflectedHorizonGreenProvenance p) q) hoddq
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Reflection-oddness of the actual conservative codiagonal is exactly RH.
This is the precise obstruction to applying odd-target observation descent. -/
theorem adaptivePrimeNormalGlobalReflectedGreenCodiagonal_reflectOdd_iff_riemannHypothesis
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy,
      adaptivePrimeNormalGlobalReflectedCodiagonal p
          (adaptivePrimeNormalReflectedHorizonGreenProvenance p)
          (xiZeroCopyReflectEquiv q) =
        -adaptivePrimeNormalGlobalReflectedCodiagonal p
          (adaptivePrimeNormalReflectedHorizonGreenProvenance p) q) ↔
      RiemannHypothesis := by
  constructor
  · intro hodd
    rw [← adaptivePrimeNormalGlobalReflectedGreenRecord_codiagonal_eq_zero_iff_riemannHypothesis]
    exact
      adaptivePrimeNormalGlobalReflectedGreenCodiagonal_eq_zero_of_reflectOdd
        p hodd
  · intro hrh q
    have hzero : adaptivePrimeNormalGlobalReflectedCodiagonal p
        (adaptivePrimeNormalReflectedHorizonGreenProvenance p) = 0 :=
      (adaptivePrimeNormalGlobalReflectedGreenRecord_codiagonal_eq_zero_iff_riemannHypothesis p).2 hrh
    rw [hzero]
    simp

end DeningerMeyerGaussianGreen

end

end RHTower
