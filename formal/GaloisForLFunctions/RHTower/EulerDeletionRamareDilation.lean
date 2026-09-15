import GaloisForLFunctions.RHTower.BaezDuarteGram

noncomputable section
open MeasureTheory Set Complex
open scoped BigOperators InnerProductSpace

namespace RHTower.DeletionRamareDilation

/-- Physical dilation with the normalization forced by reciprocal generators. -/
def dilate (p : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => (1 / (p : ℝ)) * f (u / (p : ℝ))

/-- A reciprocal generator at a composite modulus is exactly its dilated cofactor
plus the compulsory affine prime correction. -/
theorem bdGenReal_inv_mul_decompose {p m : ℕ} (hp : 0 < p) (hm : 0 < m) (u : ℝ) :
    bdGenReal (1 / ((p * m : ℕ) : ℝ)) u =
      dilate p (bdGenReal (1 / (m : ℝ))) u +
        (1 / (m : ℝ)) * bdGenReal (1 / (p : ℝ)) u := by
  rw [dilate, bdGenReal, bdGenReal, bdGenReal]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpm0 : ((p * m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hp.ne' hm.ne'
  push_cast
  by_cases hu : u = 0
  · subst u
    simp
  field_simp
  ring

/-- A whole finite cofactor packet obeys the same affine dilation identity. -/
theorem sum_bdGenReal_inv_mul_decompose (p M : ℕ) (hp : 0 < p)
    (a : ℕ → ℝ) (u : ℝ) :
    (∑ m ∈ Finset.Icc 1 M, a m * bdGenReal (1 / ((p * m : ℕ) : ℝ)) u) =
      dilate p (fun v => ∑ m ∈ Finset.Icc 1 M,
        a m * bdGenReal (1 / (m : ℝ)) v) u +
        (∑ m ∈ Finset.Icc 1 M, a m / (m : ℝ)) * bdGenReal (1 / (p : ℝ)) u := by
  rw [dilate, Finset.sum_mul]
  calc
    _ = ∑ m ∈ Finset.Icc 1 M,
        ((1 / (p : ℝ)) * (a m * bdGenReal (1 / (m : ℝ)) (u / (p : ℝ))) +
          (a m / (m : ℝ)) * bdGenReal (1 / (p : ℝ)) u) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmpos : 0 < m := Finset.mem_Icc.mp hm |>.1
      rw [bdGenReal_inv_mul_decompose hp hmpos u]
      simp only [dilate]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end RHTower.DeletionRamareDilation
