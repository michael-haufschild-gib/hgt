import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnPositivity
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnProjections

/-!
# Saturation for periodic actions with positive moving spaces

A null vector in a nonnegative moving space is orthogonal to both that space and
its fixed complement, hence vanishes by nondegeneracy of the full column form.
Equality of a kernel value with its identity value consequently forces a period.
-/

open Complex Module
open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G : Type*} [Group G]

/-- A null moving vector vanishes when its moving space is nonnegative. -/
theorem kernelColumnPairing_moving_null_eq_zero {k : G → ℂ} (hk : IsHermKernel k)
    (g : G) (hper : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k g) ^ m) x = x)
    (hpos : ∀ x ∈ LinearMap.range (kernelColumnRepresentation k g + (-1 : ℂ) • 1),
      0 ≤ (kernelColumnPairing k x x).re)
    (v : kernelColumnSpan k)
    (hv : v ∈ LinearMap.range (kernelColumnRepresentation k g + (-1 : ℂ) • 1))
    (hzero : (kernelColumnPairing k v v).re = 0) : v = 0 := by
  let P := locallyPeriodicProjection (kernelColumnRepresentation k g) hper
  apply kernelColumnPairing_nondegenerate hk v
  intro w
  have hfixed : kernelColumnPairing k (P w) v = 0 :=
    kernelColumnPairing_fixed_moving hk g (P w) v
      (locallyPeriodicProjection_fixed _ hper w) hv
  have hmov : w - P w ∈
      LinearMap.range (kernelColumnRepresentation k g + (-1 : ℂ) • 1) := by
    simpa only [neg_smul, one_smul, sub_eq_add_neg, P] using
      add_neg_locallyPeriodicProjection_mem_range (kernelColumnRepresentation k g) hper w
  have hcs := kernelColumnPairing_normSq_le_on_subspace hk _ hpos (w - P w) v hmov hv
  rw [hzero, mul_zero] at hcs
  have hnull : kernelColumnPairing k (w - P w) v = 0 :=
    Complex.normSq_eq_zero.mp (le_antisymm hcs (Complex.normSq_nonneg _))
  have he : w = P w + (w - P w) := by abel
  calc
    kernelColumnPairing k w v = kernelColumnPairing k (P w + (w - P w)) v :=
      congrArg (fun z => kernelColumnPairing k z v) he
    _ = kernelColumnPairing k (P w) v + kernelColumnPairing k (w - P w) v :=
      LinearMap.congr_fun (map_add (kernelColumnSesquilinear k hk) (P w) (w - P w)) v
    _ = 0 := by rw [hfixed, hnull, add_zero]

/-- The nonnegative moving space is positive definite in the algebraic column realization. -/
theorem kernelColumnPairing_moving_re_pos {k : G → ℂ} (hk : IsHermKernel k)
    (g : G) (hper : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k g) ^ m) x = x)
    (hpos : ∀ x ∈ LinearMap.range (kernelColumnRepresentation k g + (-1 : ℂ) • 1),
      0 ≤ (kernelColumnPairing k x x).re)
    (v : kernelColumnSpan k)
    (hv : v ∈ LinearMap.range (kernelColumnRepresentation k g + (-1 : ℂ) • 1))
    (hv0 : v ≠ 0) : 0 < (kernelColumnPairing k v v).re := by
  rcases eq_or_lt_of_le (hpos v hv) with he | hlt
  · exact (hv0 (kernelColumnPairing_moving_null_eq_zero hk g hper hpos v hv he.symm)).elim
  · exact hlt

/-- Saturating the identity value forces right invariance along a periodic positive-moving action. -/
theorem periodic_saturation_right_invariant {k : G → ℂ} (hk : IsHermKernel k)
    (g : G) (hper : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k g) ^ m) x = x)
    (hpos : ∀ x ∈ LinearMap.range (kernelColumnRepresentation k g + (-1 : ℂ) • 1),
      0 ≤ (kernelColumnPairing k x x).re)
    (hsat : k g = k 1) (a : G) : k (a * g) = k a := by
  let v := kernelColumnPoint k g - kernelColumnPoint k 1
  have hv : v ∈ LinearMap.range (kernelColumnRepresentation k g + (-1 : ℂ) • 1) := by
    refine ⟨kernelColumnPoint k 1, ?_⟩
    simp only [v, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      kernelColumnRepresentation_point, mul_one, neg_smul, one_smul, sub_eq_add_neg]
  have hdiag : kernelColumnPairing k v v = 0 := by
    have hl := LinearMap.congr_fun
      (map_sub (kernelColumnSesquilinear k hk) (kernelColumnPoint k g) (kernelColumnPoint k 1)) v
    change kernelColumnPairing k v v =
      kernelColumnPairing k (kernelColumnPoint k g) v -
        kernelColumnPairing k (kernelColumnPoint k 1) v at hl
    rw [hl]
    change kernelColumnPairing k (kernelColumnPoint k g)
        (kernelColumnPoint k g - kernelColumnPoint k 1) -
      kernelColumnPairing k (kernelColumnPoint k 1)
        (kernelColumnPoint k g - kernelColumnPoint k 1) = 0
    rw [map_sub, map_sub]
    simp only [kernelColumnPairing_point_left hk]
    change (k (g⁻¹ * g) - k (g⁻¹ * 1)) - (k (1⁻¹ * g) - k (1⁻¹ * 1)) = 0
    have h1 : conj (k 1) = k 1 := by simpa only [inv_one] using (hk 1).symm
    simp only [inv_mul_cancel, mul_one, inv_one, one_mul, hk g, hsat, h1, sub_self]
  have hv0 := kernelColumnPairing_moving_null_eq_zero hk g hper hpos v hv
    (by rw [hdiag, Complex.zero_re])
  have hpoints : kernelColumnPoint k g = kernelColumnPoint k 1 := sub_eq_zero.mp hv0
  have h := congrArg (fun x : kernelColumnSpan k => (x : G → ℂ) a⁻¹) hpoints
  change k ((a⁻¹)⁻¹ * g) = k ((a⁻¹)⁻¹ * 1) at h
  simpa only [inv_inv, mul_one] using h

/-- Hermitian symmetry turns right invariance into left invariance. -/
theorem isHermKernel_left_invariant_of_right {k : G → ℂ} (hk : IsHermKernel k) (g : G)
    (hright : ∀ a, k (a * g) = k a) (a : G) : k (g * a) = k a := by
  have hinv : k (a⁻¹ * g⁻¹) = k a⁻¹ := by
    have h := hright (a⁻¹ * g⁻¹)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h.symm
  have h := congrArg (starRingEnd ℂ) hinv
  simpa only [← hk (a⁻¹ * g⁻¹), ← hk (a⁻¹), mul_inv_rev, inv_inv] using h

#print axioms kernelColumnPairing_moving_re_pos
#print axioms periodic_saturation_right_invariant
#print axioms isHermKernel_left_invariant_of_right
end GaloisForLFunctions.HeckeKreinToeplitz
