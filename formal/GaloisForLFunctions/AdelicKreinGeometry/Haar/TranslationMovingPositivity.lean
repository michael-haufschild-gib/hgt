import GaloisForLFunctions.BiarithmeticGeometry.Affine.PeriodicTranslations
import GaloisForLFunctions.HeckeKreinToeplitz.Index.PeriodicDilationPositivity

/-!
# Positivity on rational translation differences

Reciprocal integer dilations replicate periodic zero-mean columns orthogonally. A finite-index
affine kernel invariant under right integer translations is therefore nonnegative on every
translation difference range.
-/

open Module Finset
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The difference of a periodic translation vector has nonnegative column norm.
Reciprocal integer dilation replicates any negative direction orthogonally. -/
theorem periodic_translation_difference_nonneg {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (b : ℚ)
    (y : kernelColumnSpan k) {m : ℕ} (hm : m ≠ 0)
    (hy : ((kernelColumnRepresentation k (translation b)) ^ m) y = y) :
    let x := (kernelColumnRepresentation k (translation b) + (-1 : ℂ) • 1) y
    0 ≤ (kernelColumnPairing k x x).re := by
  let T := kernelColumnRepresentation k (translation b)
  let x := (T + (-1 : ℂ) • 1) y
  let u : ℚˣ := (Units.mk0 (m : ℚ) (Nat.cast_ne_zero.mpr hm))⁻¹
  have ha : translation b * dilation u = dilation u * (translation b) ^ m := by
    rw [translation_mul_affine_eq]
    have hp : (translation b) ^ m = translation ((m : ℚ) * b) := by
      simpa only [MonoidHom.id_apply] using
        rational_affine_translation_pow (MonoidHom.id AffineGroupQ) b m
    rw [hp, affSlope_dilation]
    congr 2
    simp only [u, Units.val_inv_eq_inv_val, Units.val_mk0, div_inv_eq_mul, mul_comm]
  have hx : (T ^ m) x = x := by
    change (T ^ m) ((T + (-1 : ℂ) • 1) y) = (T + (-1 : ℂ) • 1) y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul]
    have hc : T ^ m * T = T * T ^ m := by rw [← pow_succ, ← pow_succ']
    have hc' := LinearMap.congr_fun hc y
    rw [Module.End.mul_apply, Module.End.mul_apply, hy] at hc'
    rw [hc', hy]
  exact nonneg_of_periodic_dilation hk hi (translation b) (dilation u) hm ha x hx
    (sum_periodic_difference T hy)

/-- Integer-periodic finite-index affine kernels are nonnegative on every translation range. -/
theorem translation_moving_subspace_nonnegative {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ)
    (x : kernelColumnSpan k)
    (hx : x ∈ LinearMap.range (kernelColumnRepresentation k (translation b) + (-1 : ℂ) • 1)) :
    0 ≤ (kernelColumnPairing k x x).re := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨m, hm, hy⟩ := kernel_translation_locally_periodic hp b y
  exact periodic_translation_difference_nonneg hk hi b y hm hy

#print axioms periodic_translation_difference_nonneg
#print axioms translation_moving_subspace_nonnegative
end GaloisForLFunctions.AdelicKreinGeometry
