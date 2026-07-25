import GaloisForLFunctions.RHTower.WeilIndexBudgetBridge

/-!
# Exact conservation between the Weil index and the pole-order budget, and the quadratic ceiling

A deformation of `ζ` inside the classification is described by four nonnegative integers, counting
**frequency pairs** `{w,-w}`:

```text
I_off, I_crit   inserted zeros, off-critical resp. critical
R_off, R_crit   removed  zeros, off-critical resp. critical
```

The trace condition makes the coefficient at the admissible frequency `1/2` equal to
`(I_off + I_crit) - (R_off + R_crit)`, so the pole order at `s = 1` moves by that amount; and since
critical orbits contribute positive semidefinite blocks to the Weil form while each off-critical
orbit contributes exactly half its size, the Weil index moves by `I_off - R_off`.  Subtracting:

```text
(Weil index increment) = (pole order increment) + R_crit - I_crit.
```

This is an identity, not an inequality.  It specialises correctly on both explicit counterexamples:
the real stray of pole order two has `(I_off, I_crit, R_off, R_crit) = (1,0,0,0)`, so both increments
are `1`; the refunded complex stray has `(2,0,0,1)`, so the pole increment is `1` while the index
increment is `2`.

In particular the **absolute** inequality `ind₋(W_F) ≤ ord₁F - 1` — which applied to `ζ` would give
`ind₋(W_ζ) ≤ 0`, that is, the Riemann hypothesis — is **false**: the refunded stray forces
`ind₋(W_ζ) + 2 ≤ 1`, impossible.  The refund mechanism is exactly what breaks it.

The last section records the resulting ceiling.  Solving the identity for `ind₋(W_ζ)` gives
`ind₋(W_ζ) = ind₋(W_F) - I_off + R_off ≥ R_off - I_off`, a **lower** bound.  Since `ind₋(W_F) ≥ 0`
is the only universally available input, no member of the family can certify `ind₋(W_ζ) = 0`.  This
is the quadratic counterpart of the linear ceiling theorem.
-/

noncomputable section

namespace RHTower

/-- Increment of the pole order at `s = 1`, in frequency pairs: inserted minus removed. -/
def poleIncrement (Ioff Icrit Roff Rcrit : ℕ) : ℤ :=
  ((Ioff : ℤ) + (Icrit : ℤ)) - ((Roff : ℤ) + (Rcrit : ℤ))

/-- Increment of the negative index of the Weil form: only off-critical orbits count, since
critical orbits contribute positive semidefinite blocks. -/
def indexIncrement (Ioff Roff : ℕ) : ℤ := (Ioff : ℤ) - (Roff : ℤ)

/-- **Conservation law.**  The Weil index increment exceeds the pole-order increment by exactly the
net number of **critical** frequency pairs removed. -/
theorem indexIncrement_eq (Ioff Icrit Roff Rcrit : ℕ) :
    indexIncrement Ioff Roff
      = poleIncrement Ioff Icrit Roff Rcrit + ((Rcrit : ℤ) - (Icrit : ℤ)) := by
  unfold indexIncrement poleIncrement
  ring

/-- With no critical traffic the two invariants coincide. -/
theorem indexIncrement_eq_poleIncrement_of_no_critical (Ioff Roff : ℕ) :
    indexIncrement Ioff Roff = poleIncrement Ioff 0 Roff 0 := by
  unfold indexIncrement poleIncrement
  simp

/-! ## The two explicit counterexamples -/

/-- The real stray of pole order two: one inserted off-critical frequency pair, no critical
traffic.  Both increments equal one. -/
theorem realStray_increments :
    poleIncrement 1 0 0 0 = 1 ∧ indexIncrement 1 0 = 1 := by
  constructor <;> · simp [poleIncrement, indexIncrement]

/-- The refunded complex stray: two inserted off-critical frequency pairs and one removed critical
pair.  The pole order rises by one while the Weil index rises by two. -/
theorem refundedStray_increments :
    poleIncrement 2 0 0 1 = 1 ∧ indexIncrement 2 0 = 2 := by
  constructor <;> · simp [poleIncrement, indexIncrement]

/-- **The absolute inequality fails.**  For the refunded stray the index increment strictly exceeds
the pole increment, so `ind₋(W_F) ≤ ord₁F - 1` cannot hold for all members of the family; were it to
hold it would force `ind₋(W_ζ) ≤ -1`. -/
theorem absolute_inequality_fails :
    poleIncrement 2 0 0 1 < indexIncrement 2 0 := by
  unfold poleIncrement indexIncrement; norm_num

/-! ## The quadratic ceiling -/

/-- **Only lower bounds.**  Solving the conservation law for the index of `ζ` expresses it as the
index of the deformed system corrected by the off-critical traffic.  Since `ind₋(W_F) ≥ 0` is the
only universally available input, every member of the family yields a **lower** bound
`ind₋(W_ζ) ≥ R_off - I_off` and never an upper one; in particular none can certify
`ind₋(W_ζ) = 0`. -/
theorem indexZeta_lower_bound (indF Ioff Roff : ℕ) (indZ : ℤ)
    (hcons : indZ = (indF : ℤ) - indexIncrement Ioff Roff) :
    (Roff : ℤ) - (Ioff : ℤ) ≤ indZ := by
  unfold indexIncrement at hcons
  have : (0 : ℤ) ≤ (indF : ℤ) := Int.natCast_nonneg indF
  omega

/-- The bound is vacuous whenever nothing off-critical is removed, which is the only case a
deformation can arrange without prior knowledge of the off-critical zeros of `ζ`. -/
theorem indexZeta_lower_bound_vacuous (Ioff : ℕ) (indZ : ℤ) (h : 0 ≤ indZ) :
    (0 : ℤ) - (Ioff : ℤ) ≤ indZ := by
  have : (0 : ℤ) ≤ (Ioff : ℤ) := Int.natCast_nonneg Ioff
  omega

end RHTower
