import GaloisForLFunctions.RHTower.XiPolarizedIrregularType

/-!
# Global Hermitian duality versus constituentwise irregular purity

Hermitian duality sends an exponential irregular type `t` to `-conj t`.  Their determinant
character has unit norm at every source scale for every `t`, so global Real self-duality cannot
select the critical line.  In contrast, unitarity of either simple constituent at one nonzero
source scale forces `Re t = 0`.

For an actual Xi divisor copy this separates an unconditional global symmetry from the selective
condition: the reflected pair is globally unitary everywhere, while constituentwise purity is
exactly critical-line placement.  Thus a viable irregular Riemann--Hilbert formulation must retain
the simple exponential constituents and a fixed source metric; determinant, Witt, or paired
polarization data alone are structurally blind.
-/

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Hermitian dual of an irregular exponential type. -/
def dualConjugateIrregularType (t : ℂ) : ℂ :=
  -starRingEnd ℂ t

@[simp] theorem dualConjugateIrregularType_re (t : ℂ) :
    (dualConjugateIrregularType t).re = -t.re := by
  simp [dualConjugateIrregularType]

/-- Determinant character of a type and its Hermitian dual. -/
def dualConjugateIrregularDeterminant (t : ℂ) (x : ℝ) : ℂ :=
  continuousIrregularGauge t x *
    continuousIrregularGauge (dualConjugateIrregularType t) x

/-- Hermitian-dual pairing makes the determinant unitary for every exponential type. -/
theorem norm_dualConjugateIrregularDeterminant (t : ℂ) (x : ℝ) :
    ‖dualConjugateIrregularDeterminant t x‖ = 1 := by
  rw [dualConjugateIrregularDeterminant, norm_mul,
    continuousIrregularGauge, continuousIrregularGauge,
    Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  rw [show
      (2 * t * (x : ℂ)).re +
          (2 * dualConjugateIrregularType t * (x : ℂ)).re = 0 by
        simp [Complex.mul_re]]
  exact Real.exp_zero

/-- One nonzero source scale already detects whether a simple exponential type is unitary. -/
theorem norm_continuousIrregularGauge_eq_one_iff
    {t : ℂ} {x : ℝ} (hx : x ≠ 0) :
    ‖continuousIrregularGauge t x‖ = 1 ↔ t.re = 0 := by
  rw [continuousIrregularGauge, Complex.norm_exp, ← Real.exp_zero,
    Real.exp_eq_exp]
  constructor
  · intro h
    have hmul : t.re * x = 0 := by
      simpa [Complex.mul_re] using h
    exact (mul_eq_zero.mp hmul).resolve_right hx
  · intro h
    simp [Complex.mul_re, h]

/-- Constituentwise unitarity is strictly stronger than unitary determinant: it selects the
anti-Hermitian formal types. -/
theorem dualConjugateIrregularPair_constituentwiseUnitary_iff
    {t : ℂ} {x : ℝ} (hx : x ≠ 0) :
    (‖continuousIrregularGauge t x‖ = 1 ∧
      ‖continuousIrregularGauge (dualConjugateIrregularType t) x‖ = 1) ↔
      t.re = 0 := by
  constructor
  · exact fun h => (norm_continuousIrregularGauge_eq_one_iff hx).mp h.1
  · intro hre
    exact ⟨(norm_continuousIrregularGauge_eq_one_iff hx).mpr hre,
      (norm_continuousIrregularGauge_eq_one_iff hx).mpr (by simp [hre])⟩

/-- Explicit falsifier for global-polarization selection: every non-anti-Hermitian type has a
unitary Hermitian-dual determinant but fails constituentwise unitarity. -/
theorem dualConjugateIrregularPair_globalUnitary_but_not_constituentwise
    {t : ℂ} (ht : t.re ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    ‖dualConjugateIrregularDeterminant t x‖ = 1 ∧
      ¬ (‖continuousIrregularGauge t x‖ = 1 ∧
        ‖continuousIrregularGauge (dualConjugateIrregularType t) x‖ = 1) := by
  refine ⟨norm_dualConjugateIrregularDeterminant t x, ?_⟩
  rw [dualConjugateIrregularPair_constituentwiseUnitary_iff hx]
  exact ht

/-- For an actual Xi divisor copy, constituentwise Hermitian-dual purity is exactly critical-line
placement, although the paired determinant is unitary unconditionally. -/
theorem xiCenteredIrregularPair_constituentwiseUnitary_iff
    (q : XiZeroCopy) {x : ℝ} (hx : x ≠ 0) :
    (‖continuousIrregularGauge (xiCenteredIrregularType q) x‖ = 1 ∧
      ‖continuousIrregularGauge
        (dualConjugateIrregularType (xiCenteredIrregularType q)) x‖ = 1) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [dualConjugateIrregularPair_constituentwiseUnitary_iff hx]
  simp only [xiCenteredIrregularType, Complex.sub_re]
  norm_num
  constructor <;> intro h <;> linarith

/-- Functional-equation Hermitian duality makes every actual Xi pair globally unitary, without
using critical-line placement. -/
theorem norm_xiCenteredDualConjugateIrregularDeterminant
    (q : XiZeroCopy) (x : ℝ) :
    ‖dualConjugateIrregularDeterminant (xiCenteredIrregularType q) x‖ = 1 :=
  norm_dualConjugateIrregularDeterminant _ _

/-- An off-critical Xi type is a concrete counterexample to any selector using only global
Hermitian-dual determinant unitarity. -/
theorem xiCenteredIrregularPair_offCritical_globalUnitary_but_not_constituentwise
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x : ℝ} (hx : x ≠ 0) :
    ‖dualConjugateIrregularDeterminant (xiCenteredIrregularType q) x‖ = 1 ∧
      ¬ (‖continuousIrregularGauge (xiCenteredIrregularType q) x‖ = 1 ∧
        ‖continuousIrregularGauge
          (dualConjugateIrregularType (xiCenteredIrregularType q)) x‖ = 1) := by
  refine ⟨norm_xiCenteredDualConjugateIrregularDeterminant q x, ?_⟩
  rw [xiCenteredIrregularPair_constituentwiseUnitary_iff q hx]
  exact hoff

end

end RHTower
