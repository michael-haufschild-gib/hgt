import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeLogHeightGreen

/-!
# Cartan contraction of the nonzero arithmetic-character sectors

Let a differential `d` and a contraction `ι` act on an arithmetic-character piece of a graded
complex, and suppose their anticommutator is the scalar `ℓ(m)` of that character:

`d ι + ι d = ℓ(m)`.

For every nonzero character the frequency is invertible, so `h = ℓ(m)⁻¹ ι` is a genuine chain
contraction: `d h + h d = 1`.  The prime-log height bound turns this into a *bounded* contraction
on a height-graded seminorm, at the price of a single height step — no uniform spectral gap for
the prime-log frequencies is needed.

* `deningerCartanContraction` : **`d h + h d = 1` on every nonzero character.**
* `deningerCartanContraction_seminorm_le` : the one-step height bound for `h`.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [AddCommGroup C] [Module ℂ C]

/-- The Cartan contraction of a nonzero arithmetic-character piece. -/
def deningerCartanHomotopy (m : DeningerPrimeLattice) (iota : C →ₗ[ℂ] C) : C →ₗ[ℂ] C :=
  (((deningerFreq m)⁻¹ : ℝ) : ℂ) • iota

@[simp]
theorem deningerCartanHomotopy_apply (m : DeningerPrimeLattice) (iota : C →ₗ[ℂ] C) (x : C) :
    deningerCartanHomotopy m iota x = (((deningerFreq m)⁻¹ : ℝ) : ℂ) • iota x := rfl

/-- **Strict contractibility of every nonzero arithmetic-character sector.**  If the
anticommutator of the differential and the contraction is the character scalar, then dividing
the contraction by that scalar produces a chain homotopy to the identity. -/
theorem deningerCartanContraction (d iota : C →ₗ[ℂ] C) {m : DeningerPrimeLattice} (hm : m ≠ 0)
    (hL : ∀ x : C, d (iota x) + iota (d x) = ((deningerFreq m : ℝ) : ℂ) • x) (x : C) :
    d (deningerCartanHomotopy m iota x) + deningerCartanHomotopy m iota (d x) = x := by
  have hne : ((deningerFreq m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast deningerFreq_ne_zero hm
  have hinv : (((deningerFreq m)⁻¹ : ℝ) : ℂ) = ((deningerFreq m : ℝ) : ℂ)⁻¹ := by
    push_cast
    ring
  rw [deningerCartanHomotopy_apply, deningerCartanHomotopy_apply, map_smul, ← smul_add, hL x,
    smul_smul, hinv, inv_mul_cancel₀ hne, one_smul]

/-- **The contraction costs one height step.**  A contraction bounded by `Cι` on a seminorm gives
a homotopy bounded by `Cι` after raising the height weight by one. -/
theorem deningerCartanContraction_seminorm_le (q : Seminorm ℂ C) (iota : C →ₗ[ℂ] C)
    {Ciota : ℝ} (hiota : ∀ x : C, q (iota x) ≤ Ciota * q x)
    (m : DeningerPrimeLattice) (k : ℕ) (x : C) :
    deningerHeight m ^ k * q (deningerCartanHomotopy m iota x)
      ≤ Ciota * (deningerHeight m ^ (k + 1) * q x) := by
  have hnorm : q (deningerCartanHomotopy m iota x)
      = |(deningerFreq m)⁻¹| * q (iota x) := by
    rw [deningerCartanHomotopy_apply, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs]
  have hbound : |(deningerFreq m)⁻¹| ≤ deningerHeight m := by
    by_cases hm : m = 0
    · subst hm
      rw [deningerFreq_zero, inv_zero, abs_zero]
      exact (deningerHeight_pos 0).le
    · have hle := deningerHeight_inv_le_abs_freq hm
      have hfpos : 0 < |deningerFreq m| := abs_pos.mpr (deningerFreq_ne_zero hm)
      rw [abs_inv, inv_le_comm₀ hfpos (deningerHeight_pos m)]
      exact hle
  have hqnn : 0 ≤ q (iota x) := apply_nonneg _ _
  have hkey : |(deningerFreq m)⁻¹| * q (iota x)
      ≤ deningerHeight m * (Ciota * q x) := by
    calc |(deningerFreq m)⁻¹| * q (iota x)
        ≤ deningerHeight m * q (iota x) :=
          mul_le_mul_of_nonneg_right hbound hqnn
      _ ≤ deningerHeight m * (Ciota * q x) :=
          mul_le_mul_of_nonneg_left (hiota x) (deningerHeight_pos m).le
  calc deningerHeight m ^ k * q (deningerCartanHomotopy m iota x)
      = deningerHeight m ^ k * (|(deningerFreq m)⁻¹| * q (iota x)) := by rw [hnorm]
    _ ≤ deningerHeight m ^ k * (deningerHeight m * (Ciota * q x)) :=
        mul_le_mul_of_nonneg_left hkey (pow_nonneg (deningerHeight_pos m).le _)
    _ = Ciota * (deningerHeight m ^ (k + 1) * q x) := by
        rw [pow_succ]
        ring

end

end RHTower
