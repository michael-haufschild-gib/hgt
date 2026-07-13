import Mathlib

/-!
# Two-generator exponential flank series as shift eigenslices

The elementary restatement feeding the finite-transverse reflection-rigidity capstone
`finiteTransverse_reflection_rigidity`: a two-generator exponential flank series
`∑_{m,n} a_{m,n} e^{i(mα+nβ)z}` regroups, under the shift `z ↦ z + T` with `T = 2π/α`, into
shift-eigenslices `Gₙ(z) = ∑_m a_{m,n} e^{i(mα+nβ)z}` with

`Gₙ(z + T) = ωⁿ · Gₙ(z),   ω = e^{2πi(β/α)}`,

and `ω` has infinite multiplicative order exactly when `β/α` is irrational.  These are precisely the
`heig` and `hωinf` hypotheses the capstone takes as inputs; `hslice` holds by definition of the
series as the sum of its slices.
-/

open scoped Real
open Real Complex

namespace RHTower

/-- **Infinite multiplicative order of `e^{2πi r}` for irrational `r`.**  Supplies the capstone's
`hωinf` hypothesis: no positive power of `ω = e^{2πi(β/α)}` is `1` when `β/α` is irrational. -/
theorem expOmega_pow_ne_one {r : ℝ} (hr : Irrational r) (k : ℕ) (hk : 0 < k) :
    (Complex.exp (2 * Real.pi * Complex.I * r)) ^ k ≠ 1 := by
  rw [← Complex.exp_nat_mul]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2pii : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hkr : (k : ℂ) * (r : ℂ) = (n : ℂ) := by
    have h' : ((k : ℂ) * r) * (2 * Real.pi * Complex.I) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination hn
    exact mul_right_cancel₀ h2pii h'
  have hkrR : (k : ℝ) * r = (n : ℝ) := by exact_mod_cast hkr
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hrq : r = (n : ℝ) / (k : ℝ) := by field_simp; linarith [hkrR]
  exact hr ⟨(n : ℚ) / (k : ℚ), by push_cast; exact hrq.symm⟩

/-- **Per-frequency shift-eigenvalue.**  `e^{i(mα+nβ)(z+T)} = ωⁿ · e^{i(mα+nβ)z}` with `T = 2π/α`,
`ω = e^{2πi(β/α)}`: the `mα`-part contributes `e^{2πim} = 1`, the `nβ`-part contributes `ωⁿ`. -/
theorem expFlankFreq_shiftEig (α β : ℝ) (hα : α ≠ 0) (m n : ℤ) (z : ℂ) :
    Complex.exp (Complex.I * (((m : ℝ) * α + (n : ℝ) * β : ℝ)) * (z + (2 * π / α : ℝ)))
      = (Complex.exp (2 * π * Complex.I * ((β / α : ℝ)))) ^ n
        * Complex.exp (Complex.I * (((m : ℝ) * α + (n : ℝ) * β : ℝ)) * z) := by
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  rw [mul_add, Complex.exp_add, mul_comm]
  congr 1
  have hfreqT : Complex.I * (((m : ℝ) * α + (n : ℝ) * β : ℝ)) * ((2 * π / α : ℝ) : ℂ)
      = (m : ℂ) * (2 * π * Complex.I) + (n : ℂ) * (2 * π * Complex.I * ((β / α : ℝ))) := by
    push_cast; field_simp
  rw [hfreqT, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_int_mul]

/-- The second-generator eigenslice at index `n`: the sub-sum over the first-generator index `m`. -/
noncomputable def expFlankSlice (α β : ℝ) (a : ℤ → ℤ → ℂ) (M : Finset ℤ) (n : ℤ) (z : ℂ) : ℂ :=
  ∑ m ∈ M, a m n * Complex.exp (Complex.I * (((m : ℝ) * α + (n : ℝ) * β : ℝ)) * z)

/-- **Slice shift-eigenvalue.**  Each eigenslice is a shift eigenfunction of eigenvalue `ωⁿ`:
`Gₙ(z + T) = ωⁿ · Gₙ(z)`.  This is the `heig` hypothesis of the reflection-rigidity capstone. -/
theorem expFlankSlice_shiftEig (α β : ℝ) (hα : α ≠ 0) (a : ℤ → ℤ → ℂ) (M : Finset ℤ) (n : ℤ)
    (z : ℂ) :
    expFlankSlice α β a M n (z + (2 * π / α : ℝ))
      = (Complex.exp (2 * π * Complex.I * ((β / α : ℝ)))) ^ n * expFlankSlice α β a M n z := by
  simp only [expFlankSlice, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [expFlankFreq_shiftEig α β hα m n z]
  ring

/-- The full two-generator series is the sum of its eigenslices — the `hslice` hypothesis, here an
exact identity by regrouping the double sum by second-generator index. -/
theorem expFlankSeries_eq_sum_slices (α β : ℝ) (a : ℤ → ℤ → ℂ) (M S : Finset ℤ) (z : ℂ) :
    ∑ n ∈ S, expFlankSlice α β a M n z
      = ∑ n ∈ S, ∑ m ∈ M, a m n * Complex.exp (Complex.I * (((m : ℝ) * α + (n : ℝ) * β : ℝ)) * z) :=
  rfl

end RHTower
