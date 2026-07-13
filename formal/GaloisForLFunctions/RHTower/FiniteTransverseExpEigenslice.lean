import Mathlib
import GaloisForLFunctions.RHTower.FiniteTransverseReflectionRigidityAnalytic

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

/-- Each eigenslice is entire (finite sum of scalar multiples of exponentials of a linear map). -/
theorem differentiable_expFlankSlice (α β : ℝ) (a : ℤ → ℤ → ℂ) (M : Finset ℤ) (n : ℤ) :
    Differentiable ℂ (fun z => expFlankSlice α β a M n z) := by
  have hrw : (fun z => expFlankSlice α β a M n z)
      = ∑ m ∈ M, (fun z : ℂ =>
          a m n * Complex.exp (Complex.I * (((m : ℝ) * α + (n : ℝ) * β : ℝ)) * z)) := by
    funext z; simp [expFlankSlice, Finset.sum_apply]
  rw [hrw]
  exact Differentiable.sum (fun m _ =>
    (Differentiable.cexp ((differentiable_const _).mul differentiable_id)).const_mul _)

/-- **Lower-flank boundedness from frequency non-positivity.**  If every flank frequency
`mα + nβ` is non-positive, the two-generator series is bounded on the whole lower half-plane by the
sum of the coefficient norms: on `Im z ≤ 0` each `‖e^{i(mα+nβ)z}‖ = e^{-(mα+nβ)·Im z} ≤ 1`.  This
discharges the capstone's lower-flank boundedness hypothesis. -/
theorem expFlank_lowerFlank_bounded (α β : ℝ) (a : ℤ → ℤ → ℂ) (M : Finset ℤ) (S : Finset ℕ)
    (hfreq : ∀ n ∈ S, ∀ m ∈ M, (m : ℝ) * α + (n : ℝ) * β ≤ 0) :
    ∀ z : ℂ, z.im ≤ 0 →
      ‖∑ n ∈ S, expFlankSlice α β a M (n : ℤ) z‖ ≤ ∑ n ∈ S, ∑ m ∈ M, ‖a m (n : ℤ)‖ := by
  intro z hz
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
  simp only [expFlankSlice]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => ?_))
  rw [norm_mul, Complex.norm_exp]
  have hre : (Complex.I * (((m : ℝ) * α + ((n : ℤ) : ℝ) * β : ℝ)) * z).re
      = -((m : ℝ) * α + ((n : ℤ) : ℝ) * β) * z.im := by
    simp [Complex.mul_re, Complex.mul_im]; ring
  rw [hre]
  have hf : (m : ℝ) * α + ((n : ℤ) : ℝ) * β ≤ 0 := by
    have := hfreq n hn m hm; push_cast at this ⊢; linarith
  have hle : Real.exp (-((m : ℝ) * α + ((n : ℤ) : ℝ) * β) * z.im) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hf, hz])
  nlinarith [norm_nonneg (a m (n : ℤ)), hle]

/-- **Top-level reflection rigidity for a two-generator flank series.**  An even two-generator flank
exponential series `G = ∑_{n∈S} Gₙ` (with `Gₙ` the second-generator eigenslices), whose frequency
ratio `β/α` is irrational and which is bounded on the lower flank `Im z ≤ -w`, is constant.  All the
shift-eigenslice structure is discharged from `FiniteTransverseExpEigenslice`; only the two genuinely
analytic inputs — evenness of the concrete series and its lower-flank boundedness — remain as
hypotheses (supplied by the explicit `A·Pₙ` construction). -/
theorem expFlank_reflection_rigidity (α β : ℝ) (hα : 0 < α) (hirr : Irrational (β / α))
    {w : ℝ} (hw : 0 < w) (a : ℤ → ℤ → ℂ) (M : Finset ℤ) (S : Finset ℕ)
    (hEven : ∀ z, (∑ n ∈ S, expFlankSlice α β a M (n : ℤ) (-z))
                  = ∑ n ∈ S, expFlankSlice α β a M (n : ℤ) z)
    {B : ℝ} (hbound : ∀ z, z.im ≤ -w →
        ‖∑ n ∈ S, expFlankSlice α β a M (n : ℤ) z‖ ≤ B) :
    ∀ s t : ℂ, (∑ n ∈ S, expFlankSlice α β a M (n : ℤ) s)
             = ∑ n ∈ S, expFlankSlice α β a M (n : ℤ) t := by
  have hαne : α ≠ 0 := ne_of_gt hα
  refine finiteTransverse_reflection_rigidity
    (G := fun z => ∑ n ∈ S, expFlankSlice α β a M (n : ℤ) z)
    (T := 2 * π / α) (w := w) (ω := Complex.exp (2 * π * Complex.I * ((β / α : ℝ)))) (S := S)
    (Gn := fun (n : ℕ) z => expFlankSlice α β a M (n : ℤ) z)
    ?hG hEven (by positivity) hw (Complex.exp_ne_zero _)
    (fun k hk => expOmega_pow_ne_one hirr k hk) (fun z _ => rfl) ?heig hbound
  case hG =>
    have hrw : (fun z => ∑ n ∈ S, expFlankSlice α β a M (n : ℤ) z)
        = ∑ n ∈ S, (fun z => expFlankSlice α β a M (n : ℤ) z) := by
      funext z; simp [Finset.sum_apply]
    rw [hrw]
    exact Differentiable.sum (fun n _ => differentiable_expFlankSlice α β a M (n : ℤ))
  case heig =>
    intro n _ z _
    show expFlankSlice α β a M (n : ℤ) (z + ((2 * π / α : ℝ) : ℂ))
        = Complex.exp (2 * π * Complex.I * ((β / α : ℝ))) ^ n * expFlankSlice α β a M (n : ℤ) z
    rw [expFlankSlice_shiftEig α β hαne a M (n : ℤ) z, zpow_natCast]

/-- **Reflection rigidity from evenness and frequency non-positivity.**  Combining the boundedness
lemma with the top-level theorem: an even two-generator flank series with irrational `β/α` and all
flank frequencies `mα + nβ ≤ 0` is constant.  Here the only non-combinatorial input is evenness — the
lower-flank boundedness is discharged internally by `expFlank_lowerFlank_bounded`. -/
theorem expFlank_reflection_rigidity_of_freqNonpos (α β : ℝ) (hα : 0 < α) (hirr : Irrational (β / α))
    (a : ℤ → ℤ → ℂ) (M : Finset ℤ) (S : Finset ℕ)
    (hEven : ∀ z, (∑ n ∈ S, expFlankSlice α β a M (n : ℤ) (-z))
                  = ∑ n ∈ S, expFlankSlice α β a M (n : ℤ) z)
    (hfreq : ∀ n ∈ S, ∀ m ∈ M, (m : ℝ) * α + (n : ℝ) * β ≤ 0) :
    ∀ s t : ℂ, (∑ n ∈ S, expFlankSlice α β a M (n : ℤ) s)
             = ∑ n ∈ S, expFlankSlice α β a M (n : ℤ) t :=
  expFlank_reflection_rigidity α β hα hirr (w := 1) one_pos a M S hEven
    (fun z hz => expFlank_lowerFlank_bounded α β a M S hfreq z (le_trans hz (by norm_num)))

end RHTower
