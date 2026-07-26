import GaloisForLFunctions.RHTower.HankelToeplitzWindow

/-!
# The two minors are the same determinant up to a sign of period four

The window at order two came from a coincidence: the free inequality and the hypothesis constrained
the same scalar with opposite signs.  This file shows the coincidence is structural and computes its
sign at every order.

**The identity.**  For a two-sided sequence `a`, the `m × m` Hankel matrix centred so that its entries
have index sum `0` is

```text
H r c = a (r + c - (m-1)) ,
```

and the `m × m` Toeplitz matrix is `T r c = a (c - r)`.  Reversing the rows of `T` sends `r` to
`m-1-r` and turns the entry into `a (c + r - (m-1))`, which is exactly `H`:

```text
H = T.submatrix Fin.rev id .
```

**The sign.**  Row reversal is a permutation with `m(m-1)/2` inversions, so

```text
det H = (-1)^{m(m-1)/2} · det T ,
```

and the exponent's parity has **period four** in `m`: `+, -, -, +, +, -, -, +, …`

**The consequence.**  The factorial weights `a_j = M_j/(2j)!` are asymptotically constant on each
isobaric monomial — a monomial with offsets summing to zero picks up `(2j)^{-2·0} = 1` — so at leading
order in `1/j` the hypothesis at order `m` reads `det T ≥ 0` in the moments themselves, while the free
moment structure gives `det H ≥ 0`.  With the sign above:

> **For `m ≡ 0, 1 (mod 4)` the hypothesis at order `m` agrees with the free moment inequality at
> leading order.  For `m ≡ 2, 3 (mod 4)` it is its exact negation, so both sides are forced to vanish
> to leading order and the whole content sits in the `O(1/j)` correction.  The difficulty of the
> hypothesis at order `m` is periodic in `m` with period four.**

Order two lies in the second class, which is why the order-two inequality for this sequence is a
delicate theorem rather than a free consequence of positivity.

This file formalizes the reversal identity, the determinant relation, and the sign at orders one
through eight.
-/

open Matrix

noncomputable section

namespace RHTower

variable (a : ℤ → ℝ)

/-- The `m × m` Toeplitz matrix of a two-sided sequence. -/
def toeplitzMat (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun r c => a ((c : ℤ) - (r : ℤ))

/-- The `m × m` Hankel matrix, centred so that every entry's index offset sums to zero along a
permutation. -/
def hankelMat (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun r c => a ((r : ℤ) + (c : ℤ) - ((m : ℤ) - 1))

/-- **The reversal identity.**  The Hankel matrix is the Toeplitz matrix with its rows reversed. -/
theorem hankel_eq_toeplitz_submatrix (m : ℕ) :
    hankelMat a m = (toeplitzMat a m).submatrix Fin.rev id := by
  funext r c
  simp only [hankelMat, toeplitzMat, submatrix_apply, id_eq]
  congr 1
  have hr : (r : ℕ) + 1 ≤ m := r.isLt
  have hval : ((Fin.rev r : Fin m) : ℕ) = m - ((r : ℕ) + 1) := Fin.val_rev r
  rw [hval]
  have : (((m - ((r : ℕ) + 1) : ℕ) : ℤ)) = (m : ℤ) - ((r : ℤ) + 1) := by
    push_cast [Nat.cast_sub hr]
    ring
  rw [this]
  ring

/-- **The determinant relation.**  The two determinants differ by the sign of the row reversal. -/
theorem det_hankel_eq_sign_mul_det_toeplitz (m : ℕ) :
    (hankelMat a m).det
      = (Equiv.Perm.sign (Fin.revPerm (n := m)) : ℝ) * (toeplitzMat a m).det := by
  rw [hankel_eq_toeplitz_submatrix]
  exact Matrix.det_permute (Fin.revPerm (n := m)) (toeplitzMat a m)

section Signs

theorem revSign_one : Equiv.Perm.sign (Fin.revPerm (n := 1)) = 1 := by decide
theorem revSign_two : Equiv.Perm.sign (Fin.revPerm (n := 2)) = -1 := by decide
theorem revSign_three : Equiv.Perm.sign (Fin.revPerm (n := 3)) = -1 := by decide
theorem revSign_four : Equiv.Perm.sign (Fin.revPerm (n := 4)) = 1 := by decide
theorem revSign_five : Equiv.Perm.sign (Fin.revPerm (n := 5)) = 1 := by decide
theorem revSign_six : Equiv.Perm.sign (Fin.revPerm (n := 6)) = -1 := by decide
theorem revSign_seven : Equiv.Perm.sign (Fin.revPerm (n := 7)) = -1 := by decide
theorem revSign_eight : Equiv.Perm.sign (Fin.revPerm (n := 8)) = 1 := by decide

end Signs

/-- **The agreeing orders.**  At order four the two determinants are equal, so the hypothesis at that
order agrees with the free moment inequality at leading order. -/
theorem det_agree_four : (hankelMat a 4).det = (toeplitzMat a 4).det := by
  rw [det_hankel_eq_sign_mul_det_toeplitz, revSign_four]
  norm_num

theorem det_agree_five : (hankelMat a 5).det = (toeplitzMat a 5).det := by
  rw [det_hankel_eq_sign_mul_det_toeplitz, revSign_five]
  norm_num

/-- **The opposing orders.**  At order two and order three the two determinants are exact negatives,
so a free nonnegativity and the hypothesis together force both to vanish at leading order. -/
theorem det_oppose_two : (hankelMat a 2).det = -(toeplitzMat a 2).det := by
  rw [det_hankel_eq_sign_mul_det_toeplitz, revSign_two]
  norm_num

theorem det_oppose_three : (hankelMat a 3).det = -(toeplitzMat a 3).det := by
  rw [det_hankel_eq_sign_mul_det_toeplitz, revSign_three]
  norm_num

/-- **The pinch, in general form.**  If a quantity is nonnegative and its negative is also
nonnegative, it vanishes: at the opposing orders the free fact and the hypothesis leave only zero. -/
theorem opposing_forces_zero {x : ℝ} (hfree : 0 ≤ x) (hhyp : 0 ≤ -x) : x = 0 := by
  linarith

end RHTower
