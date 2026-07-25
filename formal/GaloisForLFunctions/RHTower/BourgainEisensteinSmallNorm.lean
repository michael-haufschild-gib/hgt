/-
# Finite small-norm region in the Eisenstein lattice

The positive-definite identity

`4N(a+bω) = (2a-b)² + 3b²`

puts every Eisenstein integer of norm below `M` in an explicit finite
coordinate box.  This is the finiteness input needed to make the constant
in the Eisenstein divisor bound independent of the integer being factored.
-/
import GaloisForLFunctions.RHTower.BourgainEisensteinDivisorCount

namespace RHTower

open BourgainEisensteinInt

noncomputable section

/-- Explicit finite coordinate box `[-4M,4M]²`. -/
def bourgainEisensteinBox (M : ℕ) :
    Finset BourgainEisensteinInt :=
  ((Finset.Icc (-(4 * (M : ℤ))) (4 * M)).product
      (Finset.Icc (-(4 * (M : ℤ))) (4 * M))).image
    fun ab : ℤ × ℤ => ⟨ab.1, ab.2⟩

/-- Norm `< M`, with `M ≥ 1`, forces both coordinates into
`[-4M,4M]`. -/
theorem coordinates_mem_Icc_of_norm_lt
    {z : BourgainEisensteinInt} {M : ℕ}
    (hM : 1 ≤ M) (hz : norm z < (M : ℤ)) :
    z.re ∈ Finset.Icc (-(4 * (M : ℤ))) (4 * M) ∧
      z.im ∈ Finset.Icc (-(4 * (M : ℤ))) (4 * M) := by
  have hfour := four_mul_norm z
  have hMnonneg : (0 : ℤ) ≤ M := by exact_mod_cast (Nat.zero_le M)
  have hMone : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have himsq : z.im ^ (2 : ℕ) < 4 * (M : ℤ) := by
    nlinarith [sq_nonneg (2 * z.re - z.im)]
  have hdiffsq :
      (2 * z.re - z.im) ^ (2 : ℕ) < 4 * (M : ℤ) := by
    nlinarith [sq_nonneg z.im]
  have himLower : -(4 * (M : ℤ)) ≤ z.im := by
    nlinarith [sq_nonneg (z.im + 4 * (M : ℤ))]
  have himUpper : z.im ≤ 4 * (M : ℤ) := by
    nlinarith [sq_nonneg (z.im - 4 * (M : ℤ))]
  have hdiffLower :
      -(4 * (M : ℤ)) ≤ 2 * z.re - z.im := by
    nlinarith [sq_nonneg
      (2 * z.re - z.im + 4 * (M : ℤ))]
  have hdiffUpper :
      2 * z.re - z.im ≤ 4 * (M : ℤ) := by
    nlinarith [sq_nonneg
      (2 * z.re - z.im - 4 * (M : ℤ))]
  rw [Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · constructor <;> omega
  · exact ⟨himLower, himUpper⟩

/-- Every Eisenstein integer of norm `< M` belongs to the explicit box. -/
theorem mem_bourgainEisensteinBox_of_norm_lt
    {z : BourgainEisensteinInt} {M : ℕ}
    (hM : 1 ≤ M) (hz : norm z < (M : ℤ)) :
    z ∈ bourgainEisensteinBox M := by
  classical
  obtain ⟨hre, him⟩ := coordinates_mem_Icc_of_norm_lt hM hz
  rw [bourgainEisensteinBox, Finset.mem_image]
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · rw [Finset.product_eq_sprod, Finset.mem_product]
    exact ⟨hre, him⟩
  · exact BourgainEisensteinInt.ext rfl rfl

end

end RHTower
