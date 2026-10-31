import GaloisForLFunctions.HeckeKreinToeplitz.Index.NullKernelRigidity
import GaloisForLFunctions.ArithmeticPositiveDuality.TheExtremalsOfTheHeckeLawAreTwistedHaarStates

/-!
# Negative squares of affine kernels with zero axis readings

A Hermitian affine kernel vanishing on translations and dilations is either zero or has at
least two negative squares. At index at most one, the zero set is a subgroup; the two affine
axes generate the whole group.
-/

open Complex
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- An index-one affine kernel vanishing on both generating subgroups is zero. -/
theorem eq_zero_of_zero_axes_of_negIndex_le_one {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hi : negIndex k ≤ 1)
    (ht : ∀ b : ℚ, k (translation b) = 0) (hd : ∀ u : ℚˣ, k (dilation u) = 0) :
    k = 0 := by
  have h1 : k 1 = 0 := by simpa only [translation_zero] using ht 0
  let Z := nullKernelZeroSubgroup hk h1 hi
  funext g
  rw [eq_translation_mul_dilation g]
  exact Z.mul_mem (ht _) (hd _)

/-- A nonzero mixed affine perturbation invisible on both axes needs at least two negative squares. -/
theorem two_le_negIndex_of_zero_axes {k : AffineGroupQ → ℂ} (hk : IsHermKernel k)
    (ht : ∀ b : ℚ, k (translation b) = 0) (hd : ∀ u : ℚˣ, k (dilation u) = 0)
    (hne : k ≠ 0) : 2 ≤ negIndex k := by
  by_contra hn
  have hlt : negIndex k < 2 := lt_of_not_ge hn
  have htop : negIndex k ≠ ⊤ := by intro h; simp [h] at hlt
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  have hm2 : m < 2 := by rw [← hm] at hlt; exact_mod_cast hlt
  have hle : negIndex k ≤ 1 := by
    rw [← hm]
    exact_mod_cast (show m ≤ 1 by omega)
  exact hne (eq_zero_of_zero_axes_of_negIndex_le_one hk hle ht hd)

#print axioms eq_zero_of_zero_axes_of_negIndex_le_one
#print axioms two_le_negIndex_of_zero_axes
end GaloisForLFunctions.AdelicKreinGeometry
