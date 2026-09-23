import GaloisForLFunctions.RHTower.DeningerBurnolConormalRadialTopBoundaryComparison
import GaloisForLFunctions.HTGeometry.LowDegreeHochschildFaceFlatness

/-!
# Ordinary-integer BV Green--Stokes radial comparison

The Wold/BV first-trace boundary at an ordinary integer `n` has normalized
conormal evaluation

`n⁻¹ * (1 - χ_n(s)⁻¹)`,

where `χ_n(s)` is the Deninger half-density mate gain.  Reflection changes
`χ` to `χ⁻¹`; therefore the reflected difference of the two
Green--Stokes evaluations is exactly `1/n` times the physical
Deninger--Burnol radial defect.

This identifies the exact chain-level descent obstruction.  It does not
assert that the physical conormal evaluation annihilates the boundary:
that statement is equivalent to the critical-line equation.
-/

open Complex
open scoped TensorProduct
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Pre-specialization ordinary-integer Green--Stokes chain -/

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Algebraic positive-integer sequence carrier.  The formulas below preserve
the `ℓ²` subspace, but their Green--Stokes identity needs only this source-first
carrier and therefore contains no analytic or divisor premise. -/
abbrev DeningerOrdinaryIntegerSequence := PNat → ℂ

/-- Endomorphism algebra of the pre-specialization positive-integer carrier. -/
abbrev DeningerOrdinaryIntegerEnd :=
  Module.End ℂ DeningerOrdinaryIntegerSequence

/-- Unique positive quotient of `k` by `n` when `n ∣ k`. -/
def pnatDvdQuotient (n k : PNat) (h : n ∣ k) : PNat :=
  Classical.choose (dvd_iff_exists_eq_mul_right.mp h)

theorem pnatDvdQuotient_spec (n k : PNat) (h : n ∣ k) :
    n * pnatDvdQuotient n k h = k :=
  (Classical.choose_spec (dvd_iff_exists_eq_mul_right.mp h)).symm

theorem pnatDvdQuotient_mul (n k : PNat) :
    pnatDvdQuotient n (n * k) (dvd_mul_right n k) = k := by
  apply mul_left_cancel (a := n)
  exact (pnatDvdQuotient_spec n (n * k) (dvd_mul_right n k)).trans rfl

/-- Ordinary-integer Wold shift `S_n e_k = e_{nk}` on coefficient
sequences. -/
def deningerOrdinaryIntegerWoldShift (n : PNat) :
    DeningerOrdinaryIntegerEnd where
  toFun x k := if h : n ∣ k then x (pnatDvdQuotient n k h) else 0
  map_add' x y := by
    funext k
    split <;> simp_all
  map_smul' c x := by
    funext k
    split <;> simp_all

@[simp]
theorem deningerOrdinaryIntegerWoldShift_apply (n : PNat)
    (x : DeningerOrdinaryIntegerSequence) (k : PNat) :
    deningerOrdinaryIntegerWoldShift n x k =
      if h : n ∣ k then x (pnatDvdQuotient n k h) else 0 := rfl

/-- Algebraic adjoint formula `S_n^* x(k)=x(nk)`. -/
def deningerOrdinaryIntegerWoldBackward (n : PNat) :
    DeningerOrdinaryIntegerEnd where
  toFun x k := x (n * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem deningerOrdinaryIntegerWoldBackward_apply (n : PNat)
    (x : DeningerOrdinaryIntegerSequence) (k : PNat) :
    deningerOrdinaryIntegerWoldBackward n x k = x (n * k) := rfl

/-- Range projection `P_n` onto indices divisible by `n`. -/
def deningerOrdinaryIntegerDivisibilityProjection (n : PNat) :
    DeningerOrdinaryIntegerEnd where
  toFun x k := if n ∣ k then x k else 0
  map_add' x y := by
    funext k
    split <;> simp_all
  map_smul' c x := by
    funext k
    split <;> simp_all

@[simp]
theorem deningerOrdinaryIntegerDivisibilityProjection_apply (n : PNat)
    (x : DeningerOrdinaryIntegerSequence) (k : PNat) :
    deningerOrdinaryIntegerDivisibilityProjection n x k =
      if n ∣ k then x k else 0 := rfl

/-- Reciprocal Green density `Qe_k=k⁻¹e_k`. -/
def deningerOrdinaryIntegerReciprocalGreen :
    DeningerOrdinaryIntegerEnd where
  toFun x k := (((k : ℕ) : ℂ))⁻¹ * x k
  map_add' x y := by
    funext k
    simp only [Pi.add_apply, mul_add]
  map_smul' c x := by
    funext k
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

@[simp]
theorem deningerOrdinaryIntegerReciprocalGreen_apply
    (x : DeningerOrdinaryIntegerSequence) (k : PNat) :
    deningerOrdinaryIntegerReciprocalGreen x k =
      (((k : ℕ) : ℂ))⁻¹ * x k := rfl

/-- `S_n^*S_n=1` before any spectral specialization. -/
theorem deningerOrdinaryIntegerWoldBackward_comp_WoldShift (n : PNat) :
    deningerOrdinaryIntegerWoldBackward n *
      deningerOrdinaryIntegerWoldShift n = 1 := by
  ext x k
  change deningerOrdinaryIntegerWoldShift n x (n * k) = x k
  rw [deningerOrdinaryIntegerWoldShift_apply]
  rw [dif_pos (dvd_mul_right n k), pnatDvdQuotient_mul]

/-- `S_nS_n^*=P_n` on the ordinary divisibility sublattice. -/
theorem deningerOrdinaryIntegerWoldShift_comp_WoldBackward (n : PNat) :
    deningerOrdinaryIntegerWoldShift n *
        deningerOrdinaryIntegerWoldBackward n =
      deningerOrdinaryIntegerDivisibilityProjection n := by
  ext x k
  change (if h : n ∣ k then
      x (n * pnatDvdQuotient n k h) else 0) =
    if n ∣ k then x k else 0
  split
  · rw [pnatDvdQuotient_spec]
  · rfl

/-- Reciprocal Green density commutes with divisibility projection. -/
theorem deningerOrdinaryIntegerDivisibilityProjection_commutes_reciprocalGreen
    (n : PNat) :
    deningerOrdinaryIntegerDivisibilityProjection n *
        deningerOrdinaryIntegerReciprocalGreen =
      deningerOrdinaryIntegerReciprocalGreen *
        deningerOrdinaryIntegerDivisibilityProjection n := by
  ext x k
  change (if n ∣ k then (((k : ℕ) : ℂ))⁻¹ * x k else 0) =
    (((k : ℕ) : ℂ))⁻¹ * (if n ∣ k then x k else 0)
  split <;> simp_all

/-- Exact ordinary-integer scaling law `S_n^*QS_n=n⁻¹Q`. -/
theorem deningerOrdinaryIntegerWoldBackward_reciprocalGreen_WoldShift
    (n : PNat) :
    deningerOrdinaryIntegerWoldBackward n *
        (deningerOrdinaryIntegerReciprocalGreen *
          deningerOrdinaryIntegerWoldShift n) =
      ((((n : ℕ) : ℂ))⁻¹) • deningerOrdinaryIntegerReciprocalGreen := by
  ext x k
  change ((((n * k : PNat) : ℕ) : ℂ))⁻¹ *
      (if h : n ∣ n * k then x (pnatDvdQuotient n (n * k) h) else 0) =
    (((n : ℕ) : ℂ))⁻¹ * ((((k : ℕ) : ℂ))⁻¹ * x k)
  rw [dif_pos (dvd_mul_right n k), pnatDvdQuotient_mul]
  push_cast
  rw [mul_inv_rev]
  ring

/-- Pre-specialization ordinary-integer BV Green--Stokes commutator
`[S_n^*,QS_n]`. -/
def deningerOrdinaryIntegerBVGreenStokesBoundary (n : PNat) :
    DeningerOrdinaryIntegerEnd :=
  deningerOrdinaryIntegerWoldBackward n *
      (deningerOrdinaryIntegerReciprocalGreen *
        deningerOrdinaryIntegerWoldShift n) -
    (deningerOrdinaryIntegerReciprocalGreen *
      deningerOrdinaryIntegerWoldShift n) *
        deningerOrdinaryIntegerWoldBackward n

/-- **Ordinary-integer Green--Stokes relation.**
`[S_n^*,QS_n]=n⁻¹Q-P_nQ`. -/
theorem deningerOrdinaryIntegerBVGreenStokesBoundary_eq
    (n : PNat) :
    deningerOrdinaryIntegerBVGreenStokesBoundary n =
      ((((n : ℕ) : ℂ))⁻¹) • deningerOrdinaryIntegerReciprocalGreen -
        deningerOrdinaryIntegerDivisibilityProjection n *
          deningerOrdinaryIntegerReciprocalGreen := by
  rw [deningerOrdinaryIntegerBVGreenStokesBoundary,
    deningerOrdinaryIntegerWoldBackward_reciprocalGreen_WoldShift,
    mul_assoc,
    deningerOrdinaryIntegerWoldShift_comp_WoldBackward,
    deningerOrdinaryIntegerDivisibilityProjection_commutes_reciprocalGreen]

/-- The Green--Stokes commutator is literally the degree-one Hochschild
boundary of `S_n^* ⊗ QS_n`. -/
theorem deningerOrdinaryIntegerBVGreenStokesBoundary_eq_hochschildBoundary
    (n : PNat) :
    deningerOrdinaryIntegerBVGreenStokesBoundary n =
      hochschildBoundaryOne (R := ℂ) (A := DeningerOrdinaryIntegerEnd)
        (deningerOrdinaryIntegerWoldBackward n ⊗ₜ[ℂ]
          (deningerOrdinaryIntegerReciprocalGreen *
            deningerOrdinaryIntegerWoldShift n)) := by
  simp [deningerOrdinaryIntegerBVGreenStokesBoundary,
    hochschildBoundaryOne]

/-! ## Exact physical radial comparison -/

/-- Normalized physical conormal evaluation of the ordinary-integer BV
Green--Stokes boundary.  Operator-theoretically this is the evaluation of
`[S_n^*, Q S_n] = n⁻¹ Q - P_n Q`, divided by the nonzero value on `Q`. -/
def deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
    (n : ℕ) (s : ℂ) : ℝ :=
  ((n : ℝ))⁻¹ * (1 - (deningerHalfDensityMateGain n s)⁻¹)

/-- Critical reflection exchanges the physical conormal evaluation with the
opposite mate-gain branch. -/
theorem deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_reflection
    (n : ℕ) (s : ℂ) :
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (1 - star s) =
      ((n : ℝ))⁻¹ * (1 - deningerHalfDensityMateGain n s) := by
  rw [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation,
    deningerHalfDensityMateGain_reflection]
  simp only [inv_inv]

/-- **Ordinary-integer BV Green--Stokes reflected-difference law.**
Multiplication by the ordinary index recovers the full Deninger radial mate
curvature. -/
theorem deningerOrdinaryIntegerBVGreenStokes_reflectedDifference
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (n : ℝ) *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n s -
          deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (1 - star s)) =
      deningerTensorSquareRadialMateCurvature n s := by
  rw [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation,
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_reflection,
    ← deningerHalfDensityMateGain_sub_inv_eq_mateCurvature hn s]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgain0 : deningerHalfDensityMateGain n s ≠ 0 :=
    ne_of_gt (deningerHalfDensityMateGain_pos n s)
  field_simp [hn0, hgain0]
  ring

/-- The actual multiplicity-exact Burnol conormal radial defect is the
reflected ordinary-integer BV Green--Stokes boundary evaluation. -/
theorem deningerBurnolActualConormalRadialReflectionDefect_eq_bvGreenStokes
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    deningerBurnolActualConormalRadialReflectionDefect n rho =
      (n : ℝ) *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (rho : ℂ) -
          deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n
            (1 - star (rho : ℂ))) := by
  rw [deningerBurnolActualConormalRadialReflectionDefect_eq hn,
    deningerOrdinaryIntegerBVGreenStokes_reflectedDifference
      (lt_of_lt_of_le Nat.zero_lt_two hn)]

/-- A physical conormal marginal kills the ordinary-integer BV
Green--Stokes boundary exactly on the critical line.  Thus replacing the
physical marginal by a cyclic source trace is the RH-bearing descent step,
not a formal consequence of commutatorhood. -/
theorem deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ) :
    deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n s = 0 ↔
      s.re = 1 / 2 := by
  rw [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation]
  have hn0 : ((n : ℝ))⁻¹ ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn).ne')
  rw [mul_eq_zero, or_iff_right hn0, sub_eq_zero]
  have hgain := deningerHalfDensityMateGain_pos n s
  constructor
  · intro h
    have hgainOne : deningerHalfDensityMateGain n s = 1 := by
      have hinv := congrArg Inv.inv h
      simpa using hinv.symm
    apply (deningerTensorSquareRadialMateCurvature_eq_zero_iff n s hn).mp
    rw [← deningerHalfDensityMateGain_sub_inv_eq_mateCurvature
      (lt_of_lt_of_le Nat.zero_lt_two hn), hgainOne]
    norm_num
  · intro h
    have hcurv :=
      (deningerTensorSquareRadialMateCurvature_eq_zero_iff n s hn).mpr h
    have hgainSub :=
      deningerHalfDensityMateGain_sub_inv_eq_mateCurvature
        (lt_of_lt_of_le Nat.zero_lt_two hn) s
    rw [hcurv] at hgainSub
    have hgainPos := deningerHalfDensityMateGain_pos n s
    have hgainOne : deningerHalfDensityMateGain n s = 1 := by
      have hsq : deningerHalfDensityMateGain n s ^ (2 : ℕ) = 1 := by
        field_simp [ne_of_gt hgainPos] at hgainSub
        nlinarith
      nlinarith
    rw [hgainOne, inv_one]

end

end RHTower
