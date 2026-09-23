import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCountertransport
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianHorizonAdmission
import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalGlobalReflectedComparison

/-!
# Global Xi capacity of reflected Gaussian countertransport

The uniformly half-density-capacity-bounded reflected Gaussian
countertransport is assembled here over every multiplicity-exact Xi divisor
copy.  At each fixed depth its evaluations form an honest `ell^(2 : ℕ)` divisor
field.  The field remains reflection-even.

The new global separation law says that these `ell^(2 : ℕ)` norms are uniformly
bounded over all countertransport depths exactly under RH.  If RH fails, the
source cohomology capacity stays at most two while the global divisor norm
escapes every finite ceiling.  Thus completed divisor assembly cannot hide
the pointwise off-line escape, and continuity from this source capacity into
the global Xi carrier is itself RH-equivalent.
-/

open Complex Filter Function Set Topology MeasureTheory Asymptotics
open scoped Real
open GaloisForLFunctions

namespace RHTower

noncomputable section

namespace DeningerMeyerGaussianGreen

/-- Two-sided centered-flow character on one Xi divisor copy. -/
def deningerMeyerReflectedGaussianCountertransportXiMultiplier
    (c : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2)) +
    Complex.exp (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2))

/-- Uniform coordinate multiplier bound at each fixed countertransport
depth. -/
theorem norm_deningerMeyerReflectedGaussianCountertransportXiMultiplier_le
    (c : ℝ) (q : XiZeroCopy) :
    ‖deningerMeyerReflectedGaussianCountertransportXiMultiplier c q‖ ≤
      2 * Real.exp (|c| / 2) := by
  have hrange := xi_divisor_support_re_mem_open_unit q.1
  have habs : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hrange.1, hrange.2]
  have hmul (d : ℝ) :
      d * ((q.1 : ℂ).re - 1 / 2) ≤ |d| / 2 := by
    calc
      d * ((q.1 : ℂ).re - 1 / 2) ≤
          |d * ((q.1 : ℂ).re - 1 / 2)| := le_abs_self _
      _ = |d| * |(q.1 : ℂ).re - 1 / 2| := abs_mul _ _
      _ ≤ |d| * (1 / 2) :=
        mul_le_mul_of_nonneg_left habs (abs_nonneg d)
      _ = |d| / 2 := by ring
  have hpos :
      ‖Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ ≤
        Real.exp (|c| / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using hmul c
  have hneg :
      ‖Complex.exp (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ ≤
        Real.exp (|c| / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h := hmul (-c)
    simpa [Complex.mul_re, abs_neg] using h
  calc
    ‖deningerMeyerReflectedGaussianCountertransportXiMultiplier c q‖ ≤
        ‖Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ +
          ‖Complex.exp (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (|c| / 2) + Real.exp (|c| / 2) :=
      add_le_add hpos hneg
    _ = 2 * Real.exp (|c| / 2) := by ring

/-- Global multiplicity-exact Xi evaluation field of one countertransport
depth.  Gaussian decay makes this an `ell^(2 : ℕ)` vector for every real depth. -/
def deningerMeyerReflectedGaussianCountertransportXiField
    (c : ℝ) : XiDivisorL2 :=
  ⟨fun q =>
      deningerMeyerReflectedGaussianCountertransportXiMultiplier c q *
        reflectedGaussianHorizonGrade q,
    Memℓp.mono
      ((lp.memℓp reflectedGaussianHorizonGradeL2).norm.const_smul
        (2 * Real.exp (|c| / 2) : ℝ))
      (fun q => by
        rw [norm_mul, Pi.smul_apply, smul_eq_mul,
          reflectedGaussianHorizonGradeL2_apply]
        exact mul_le_mul_of_nonneg_right
          (norm_deningerMeyerReflectedGaussianCountertransportXiMultiplier_le
            c q)
          (norm_nonneg _))⟩

@[simp]
theorem deningerMeyerReflectedGaussianCountertransportXiField_apply
    (c : ℝ) (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianCountertransportXiField c q =
      deningerMeyerReflectedGaussianCountertransportXiMultiplier c q *
        reflectedGaussianHorizonGrade q := rfl

/-- Every coordinate of the global field is the literal Xi source
evaluation of the countertransport class. -/
theorem deningerMeyerReflectedGaussianCountertransportXiField_source_evaluation
    (c : ℝ) (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianCountertransportXiField c q =
      deningerMeyerXiSupportJetEvaluationLM q.1
        (⟨0, xiSupportMultiplicity_pos q.1⟩ :
          DeningerArithmeticJetIndex q.1)
        (deningerMeyerReflectedGaussianCountertransportClass c) := by
  rw [deningerMeyerReflectedGaussianCountertransportXiField_apply,
    deningerMeyerReflectedGaussianCountertransportClass_evaluation,
    deningerMeyerReflectedGaussianCountertransportXiMultiplier,
    reflectedGaussianHorizonGrade,
    deningerMeyerReflectedLogGaussianSource_mellin]

/-- Functional-equation reflection reverses centered time inside each
exponential and therefore fixes their sum. -/
theorem deningerMeyerReflectedGaussianCountertransportXiMultiplier_reflect
    (c : ℝ) (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianCountertransportXiMultiplier c
        (xiZeroCopyReflectEquiv q) =
      deningerMeyerReflectedGaussianCountertransportXiMultiplier c q := by
  rw [deningerMeyerReflectedGaussianCountertransportXiMultiplier,
    deningerMeyerReflectedGaussianCountertransportXiMultiplier]
  have hreflect :
      ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl
  rw [hreflect]
  have hpos : (c : ℂ) * (1 - (q.1 : ℂ) - 1 / 2) =
      -(c : ℂ) * ((q.1 : ℂ) - 1 / 2) := by ring
  have hneg : -(c : ℂ) * (1 - (q.1 : ℂ) - 1 / 2) =
      (c : ℂ) * ((q.1 : ℂ) - 1 / 2) := by ring
  rw [hpos, hneg, add_comm]

/-- The complete countertransport evaluation field lies in the even
reflection sector at every depth. -/
theorem deningerMeyerReflectedGaussianCountertransportXiField_reflect
    (c : ℝ) (q : XiZeroCopy) :
    deningerMeyerReflectedGaussianCountertransportXiField c
        (xiZeroCopyReflectEquiv q) =
      deningerMeyerReflectedGaussianCountertransportXiField c q := by
  rw [deningerMeyerReflectedGaussianCountertransportXiField_apply,
    deningerMeyerReflectedGaussianCountertransportXiField_apply,
    deningerMeyerReflectedGaussianCountertransportXiMultiplier_reflect,
    reflectedGaussianHorizonGrade_reflect]

/-- On a critical-line divisor copy, every centered-flow character has
modulus at most two. -/
theorem norm_deningerMeyerReflectedGaussianCountertransportXiMultiplier_le_two_of_re_eq_half
    (c : ℝ) (q : XiZeroCopy) (hq : (q.1 : ℂ).re = 1 / 2) :
    ‖deningerMeyerReflectedGaussianCountertransportXiMultiplier c q‖ ≤
      2 := by
  have hpos :
      ‖Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ = 1 := by
    rw [Complex.norm_exp]
    have hzero :
        (((c : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = 0 := by
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      rw [hq]
      ring
    rw [hzero, Real.exp_zero]
  have hneg :
      ‖Complex.exp (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ = 1 := by
    rw [Complex.norm_exp]
    have hzero :
        (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = 0 := by
      rw [show -(c : ℂ) * ((q.1 : ℂ) - 1 / 2) =
          -((c : ℂ) * ((q.1 : ℂ) - 1 / 2)) by ring,
        Complex.neg_re]
      have hposRe :
          (((c : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = 0 := by
        rw [Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
        rw [hq]
        ring
      rw [hposRe, neg_zero]
    rw [hzero, Real.exp_zero]
  calc
    ‖deningerMeyerReflectedGaussianCountertransportXiMultiplier c q‖ ≤
        ‖Complex.exp ((c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ +
          ‖Complex.exp (-(c : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ :=
      norm_add_le _ _
    _ = 2 := by rw [hpos, hneg]; norm_num

/-- Uniform global Hilbert capacity of the explicit countertransport
evaluation orbit. -/
def DeningerMeyerReflectedGaussianCountertransportXiFieldsBounded : Prop :=
  ∃ C : ℝ, ∀ c : ℝ,
    ‖deningerMeyerReflectedGaussianCountertransportXiField c‖ ≤ C

/-- **Global capacity-separation law.**  Uniform boundedness of all completed
Xi evaluation fields is equivalent to RH. -/
theorem deningerMeyerReflectedGaussianCountertransportXiFieldsBounded_iff_rh :
    DeningerMeyerReflectedGaussianCountertransportXiFieldsBounded ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨C, hC⟩
    apply
      deningerMeyerReflectedGaussianCountertransportEvaluationsBounded_iff_rh.mp
    intro rho
    refine ⟨C, fun c => ?_⟩
    let q : XiZeroCopy :=
      ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
    rw [←
      deningerMeyerReflectedGaussianCountertransportXiField_source_evaluation
        c q]
    exact
      (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
        (deningerMeyerReflectedGaussianCountertransportXiField c) q).trans
          (hC c)
  · intro hRH
    refine
      ⟨2 * ‖reflectedGaussianHorizonGradeL2‖, fun c => ?_⟩
    have hpoint (q : XiZeroCopy) : (q.1 : ℂ).re = 1 / 2 := by
      have hfracture :=
        (xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) q.1
      exact
        (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
          (q.1 : ℂ)).mp hfracture
    have hmono :
        ‖deningerMeyerReflectedGaussianCountertransportXiField c‖ ≤
          ‖(2 : ℂ) • reflectedGaussianHorizonGradeL2‖ :=
      lp.norm_mono (by norm_num) (fun q => by
        rw [deningerMeyerReflectedGaussianCountertransportXiField_apply,
          norm_mul, lp.coeFn_smul, Pi.smul_apply, norm_smul,
          reflectedGaussianHorizonGradeL2_apply]
        norm_num
        exact mul_le_mul_of_nonneg_right
          (norm_deningerMeyerReflectedGaussianCountertransportXiMultiplier_le_two_of_re_eq_half
            c q (hpoint q))
          (norm_nonneg _))
    rw [norm_smul] at hmono
    norm_num at hmono
    exact hmono

/-- If RH fails, the completed Xi norm of this single source orbit escapes
every finite ceiling. -/
theorem deningerMeyerReflectedGaussianCountertransportXiField_norm_unbounded_of_not_rh
    (hRH : ¬RiemannHypothesis) :
    ∀ C : ℝ, ∃ c : ℝ,
      C < ‖deningerMeyerReflectedGaussianCountertransportXiField c‖ := by
  intro C
  by_contra hnone
  simp only [not_exists, not_lt] at hnone
  exact hRH
    (deningerMeyerReflectedGaussianCountertransportXiFieldsBounded_iff_rh.mp
      ⟨C, hnone⟩)

/-- Exact source/target capacity split off the critical line: source
cohomology capacity remains uniformly at most two while completed Xi capacity
is unbounded. -/
theorem deningerMeyerReflectedGaussianCountertransport_capacity_separation_of_not_rh
    (hRH : ¬RiemannHypothesis) :
    (∀ c : ℝ,
      deningerMeyerHalfDensityCohomologySeminorm
        (deningerMeyerReflectedGaussianCountertransportClass c) ≤ 2) ∧
    (∀ C : ℝ, ∃ c : ℝ,
      C < ‖deningerMeyerReflectedGaussianCountertransportXiField c‖) := by
  exact
    ⟨deningerMeyerReflectedGaussianCountertransportClass_uniform_capacity,
      deningerMeyerReflectedGaussianCountertransportXiField_norm_unbounded_of_not_rh
        hRH⟩

/-- Reflected adaptive common-test record of the whole Gaussian
countertransport evaluation field. -/
def adaptivePrimeNormalGlobalReflectedCountertransportRecord
    (p : Nat.Primes) (c : ℝ) :
    AdaptivePrimeNormalGlobalReflectedResolvedL2 :=
  adaptivePrimeNormalGlobalReflectedComparison p
    (deningerMeyerReflectedGaussianCountertransportXiField c)

/-- Source comparison is isometric on every countertransport depth. -/
theorem norm_adaptivePrimeNormalGlobalReflectedCountertransportRecord
    (p : Nat.Primes) (c : ℝ) :
    ‖adaptivePrimeNormalGlobalReflectedCountertransportRecord p c‖ =
      ‖deningerMeyerReflectedGaussianCountertransportXiField c‖ := by
  exact (adaptivePrimeNormalGlobalReflectedComparison p).norm_map _

/-- Uniform Hilbert capacity of all resolved adaptive source records. -/
def AdaptivePrimeNormalGlobalReflectedCountertransportRecordsBounded
    (p : Nat.Primes) : Prop :=
  ∃ C : ℝ, ∀ c : ℝ,
    ‖adaptivePrimeNormalGlobalReflectedCountertransportRecord p c‖ ≤ C

/-- Uniform capacity of the isometric resolved common-test records is
equivalent to RH. -/
theorem adaptivePrimeNormalGlobalReflectedCountertransportRecordsBounded_iff_rh
    (p : Nat.Primes) :
    AdaptivePrimeNormalGlobalReflectedCountertransportRecordsBounded p ↔
      RiemannHypothesis := by
  rw [←
    deningerMeyerReflectedGaussianCountertransportXiFieldsBounded_iff_rh]
  constructor <;> rintro ⟨C, hC⟩ <;>
    exact
      ⟨C, fun c => by
        simpa [norm_adaptivePrimeNormalGlobalReflectedCountertransportRecord]
          using hC c⟩

/-- Conservative codiagonal field of one reflected adaptive
countertransport record. -/
def adaptivePrimeNormalGlobalReflectedCountertransportCodiagonal
    (p : Nat.Primes) (c : ℝ) :
    AdaptivePrimeNormalGlobalReflectedCodiagonalL2 :=
  adaptivePrimeNormalGlobalReflectedCodiagonal p
    (deningerMeyerReflectedGaussianCountertransportXiField c)

/-- Global `5/4` upper modulus for the countertransport codiagonal. -/
theorem norm_adaptivePrimeNormalGlobalReflectedCountertransportCodiagonal_le
    (p : Nat.Primes) (c : ℝ) :
    ‖adaptivePrimeNormalGlobalReflectedCountertransportCodiagonal p c‖ ≤
      (5 / 4 : ℝ) *
        ‖deningerMeyerReflectedGaussianCountertransportXiField c‖ := by
  have hmono :
      ‖adaptivePrimeNormalGlobalReflectedCountertransportCodiagonal p c‖ ≤
        ‖(5 / 4 : ℂ) •
          deningerMeyerReflectedGaussianCountertransportXiField c‖ :=
    lp.norm_mono (by norm_num) (fun q => by
      rw [adaptivePrimeNormalGlobalReflectedCountertransportCodiagonal,
        adaptivePrimeNormalGlobalReflectedCodiagonal_apply,
        norm_smul, lp.coeFn_smul, Pi.smul_apply, norm_smul]
      norm_num
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (norm_adaptivePrimeNormalReflectedCodiagonal_single_le p q)
        (norm_nonneg
          (deningerMeyerReflectedGaussianCountertransportXiField c q)))
  rw [norm_smul] at hmono
  norm_num at hmono
  exact hmono

/-- Uniform capacity of all observed countertransport codiagonals. -/
def AdaptivePrimeNormalGlobalReflectedCountertransportCodiagonalsBounded
    (p : Nat.Primes) : Prop :=
  ∃ C : ℝ, ∀ c : ℝ,
    ‖adaptivePrimeNormalGlobalReflectedCountertransportCodiagonal p c‖ ≤ C

/-- Even after the explicit conservative common-test observation, uniform
countertransport capacity is equivalent to RH. -/
theorem adaptivePrimeNormalGlobalReflectedCountertransportCodiagonalsBounded_iff_rh
    (p : Nat.Primes) :
    AdaptivePrimeNormalGlobalReflectedCountertransportCodiagonalsBounded p ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨C, hC⟩
    apply
      deningerMeyerReflectedGaussianCountertransportXiFieldsBounded_iff_rh.mp
    refine ⟨(4 / 3 : ℝ) * C, fun c => ?_⟩
    have hlower := adaptivePrimeNormalGlobalReflectedCodiagonal_lower p
      (deningerMeyerReflectedGaussianCountertransportXiField c)
    change
      (3 / 4 : ℝ) *
          ‖deningerMeyerReflectedGaussianCountertransportXiField c‖ ≤
        ‖adaptivePrimeNormalGlobalReflectedCountertransportCodiagonal p c‖
      at hlower
    have hupper := hC c
    nlinarith
      [norm_nonneg
        (deningerMeyerReflectedGaussianCountertransportXiField c)]
  · intro hRH
    obtain ⟨C, hC⟩ :=
      deningerMeyerReflectedGaussianCountertransportXiFieldsBounded_iff_rh.mpr
        hRH
    refine ⟨(5 / 4 : ℝ) * C, fun c => ?_⟩
    exact
      (norm_adaptivePrimeNormalGlobalReflectedCountertransportCodiagonal_le
        p c).trans
        (mul_le_mul_of_nonneg_left (hC c) (by norm_num))

end DeningerMeyerGaussianGreen

end

end RHTower
