import GaloisForLFunctions.HTGeometry.FiniteTailCountingStieltjes
import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiInfiniteUpperKernelInertia

/-!
# Shifted-Xi transverse tail as a Stieltjes counting measure

Once one strict-right shifted-Xi tail is finite, every higher tail is finite.  Multiplicity copies
of Xi zeros then form a finite atomic measure of transverse displacements.  Its mass on `(a,b]` is
exactly the drop in the raw strict-right divisor count.  At every nonexceptional positive shift,
that raw count is the exact negative index of the literal regular Suzuki kernel.

The distinction between raw count and literal index at exceptional shifts is intentional: common
numerator/denominator factors can create an isolated cancellation dip.  The atomic Stieltjes law is
therefore stated for the raw monotone divisor filtration and identified with kernel index precisely
at nonexceptional shifts.
-/

open Complex Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Classical

namespace RHTower

noncomputable section

/-- Horizontal displacement of one multiplicity-labelled Xi zero from the critical line. -/
def xiTransverseDisplacement (q : XiZeroCopy) : ℝ :=
  (I * xiSpectralPoint q).re

/-- Transverse location on a fixed finite strict-right tail. -/
def xiShiftFiniteTailLocation (omega0 : ℝ)
    (q : XiShiftRightZeroCopy omega0) : ℝ :=
  xiTransverseDisplacement q.1

/-- A higher strict-right Xi tail is exactly the corresponding threshold subtype of a lower
tail.  Multiplicity labels are preserved literally. -/
def xiShiftRightZeroCopyEquivFiniteTailSubtype
    {omega0 t : ℝ} (h : omega0 ≤ t) :
    XiShiftRightZeroCopy t ≃
      {q : XiShiftRightZeroCopy omega0 //
        t < xiShiftFiniteTailLocation omega0 q} where
  toFun q := ⟨⟨q.1, h.trans_lt q.2⟩, q.2⟩
  invFun q := ⟨q.1.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Raw strict-right divisor count, computed inside one known finite anchor tail. -/
def xiShiftFiniteTailCount (omega0 t : ℝ)
    [Fintype (XiShiftRightZeroCopy omega0)] : ℕ :=
  finiteTailCount (xiShiftFiniteTailLocation omega0) t

/-- Multiplicity-weighted atomic measure of transverse Xi displacements in a finite anchor tail. -/
def xiShiftFiniteTailAtomicMeasure (omega0 : ℝ)
    [Fintype (XiShiftRightZeroCopy omega0)] : Measure ℝ :=
  finiteTailAtomicMeasure (xiShiftFiniteTailLocation omega0)

/-- The anchored finite tail count is the intrinsic cardinality of the strict-right divisor at
every higher shift. -/
theorem xiShiftFiniteTailCount_eq_natCard
    {omega0 t : ℝ} (h : omega0 ≤ t)
    [Fintype (XiShiftRightZeroCopy omega0)] :
    xiShiftFiniteTailCount omega0 t = Nat.card (XiShiftRightZeroCopy t) := by
  let e := xiShiftRightZeroCopyEquivFiniteTailSubtype h
  letI : Fintype (XiShiftRightZeroCopy t) :=
    Fintype.ofEquiv
      {q : XiShiftRightZeroCopy omega0 //
        t < xiShiftFiniteTailLocation omega0 q} e.symm
  rw [xiShiftFiniteTailCount, finiteTailCount, ← Fintype.card_subtype]
  simpa only [Nat.card_eq_fintype_card] using (Fintype.card_congr e).symm

/-- Formula `(F)` in finite-tail form: the multiplicity-weighted atomic mass on `(a,b]` is the
drop in the transverse strict-right divisor count. -/
theorem xiShiftFiniteTailAtomicMeasure_Ioc
    {omega0 a b : ℝ} (h0a : omega0 ≤ a) (hab : a ≤ b)
    [Fintype (XiShiftRightZeroCopy omega0)] :
    xiShiftFiniteTailAtomicMeasure omega0 (Ioc a b) =
      (Nat.card (XiShiftRightZeroCopy a) -
        Nat.card (XiShiftRightZeroCopy b) : ℕ) := by
  rw [xiShiftFiniteTailAtomicMeasure,
    finiteTailAtomicMeasure_Ioc_eq_tailCount_sub _ hab]
  change ((xiShiftFiniteTailCount omega0 a -
    xiShiftFiniteTailCount omega0 b : ℕ) : ENNReal) = _
  rw [xiShiftFiniteTailCount_eq_natCard h0a,
    xiShiftFiniteTailCount_eq_natCard (h0a.trans hab)]

/-- At every nonexceptional higher shift, the Stieltjes tail count is the exact negative index of
the literal regular shifted-Xi kernel. -/
theorem xiShiftFiniteTailCount_exact_kernel_index
    {omega0 t : ℝ} (h0 : 0 < omega0) (h0t : omega0 ≤ t)
    [Fintype (XiShiftRightZeroCopy omega0)]
    (hnon : SuzukiShiftNonexceptional t) :
    HasFiniteKernelNegativeDimension
        (xiShiftRegularUpperKernel t)
        (xiShiftFiniteTailCount omega0 t) ∧
      ∀ r : ℕ,
        HasFiniteKernelNegativeDimension (xiShiftRegularUpperKernel t) r →
          r ≤ xiShiftFiniteTailCount omega0 t := by
  have ht : 0 < t := h0.trans_le h0t
  let e := xiShiftRightZeroCopyEquivFiniteTailSubtype h0t
  letI : Fintype (XiShiftRightZeroCopy t) :=
    Fintype.ofEquiv
      {q : XiShiftRightZeroCopy omega0 //
        t < xiShiftFiniteTailLocation omega0 q} e.symm
  have hfiniteIndex :=
    xiShiftRegularUpperKernel_exactNegativeSquares_finite ht.le hnon
  rw [xiShiftFiniteTailCount_eq_natCard h0t]
  rw [Nat.card_eq_fintype_card]
  exact hfiniteIndex

end

end RHTower
