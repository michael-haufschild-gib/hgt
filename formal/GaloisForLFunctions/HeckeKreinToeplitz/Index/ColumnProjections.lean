import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnForm
import GaloisForLFunctions.HeckeKreinToeplitz.Index.LocallyPeriodicProjection

/-!
# Orthogonal projections of locally periodic column representations

Finite orbit averages project onto fixed vectors. The complementary operator differences
are orthogonal to fixed vectors, so projected Gram entries are cyclic averages.
-/

open Module
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G : Type*} [Group G]

/-- Pairing an orbit sum with a fixed vector multiplies the original pairing by its length. -/
theorem kernelColumnPairing_orbit_sum_fixed {k : G → ℂ} (hk : IsHermKernel k) (g : G)
    (v w : kernelColumnSpan k) (hw : kernelColumnRepresentation k g w = w) (m : ℕ) :
    kernelColumnPairing k
      (∑ j ∈ Finset.range m, ((kernelColumnRepresentation k g) ^ j) v) w =
      (m : ℂ) * kernelColumnPairing k v w := by
  have hpow (j : ℕ) : ((kernelColumnRepresentation k g) ^ j) w = w := by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, Module.End.mul_apply, hw, ih]
  have hpair (j : ℕ) : kernelColumnPairing k
      (((kernelColumnRepresentation k g) ^ j) v) w = kernelColumnPairing k v w := by
    have h := kernelColumnPairing_invariant hk (g ^ j) v w
    rwa [map_pow, hpow] at h
  change (kernelColumnSesquilinear k hk
    (∑ j ∈ Finset.range m, ((kernelColumnRepresentation k g) ^ j) v)) w = _
  rw [map_sum, LinearMap.sum_apply]
  change (∑ j ∈ Finset.range m, kernelColumnPairing k
    (((kernelColumnRepresentation k g) ^ j) v) w) = _
  simp only [hpair, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- A fixed vector is orthogonal to the range of the corresponding group difference. -/
theorem kernelColumnPairing_fixed_moving {k : G → ℂ} (hk : IsHermKernel k) (g : G)
    (v w : kernelColumnSpan k) (hv : kernelColumnRepresentation k g v = v)
    (hw : w ∈ LinearMap.range (kernelColumnRepresentation k g + (-1 : ℂ) • 1)) :
    kernelColumnPairing k v w = 0 := by
  obtain ⟨y, rfl⟩ := hw
  rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    map_add, map_smul, smul_eq_mul]
  have h := kernelColumnPairing_invariant hk g v y
  rw [hv] at h
  rw [h]
  ring

/-- The algebraic fixed-space projection of a periodic isometry is self-adjoint. -/
theorem kernelColumnPairing_projection_selfadjoint {k : G → ℂ} (hk : IsHermKernel k)
    (g : G) (hp : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k g) ^ m) x = x)
    (v w : kernelColumnSpan k) :
    kernelColumnPairing k (locallyPeriodicProjection (kernelColumnRepresentation k g) hp v) w =
      kernelColumnPairing k v (locallyPeriodicProjection (kernelColumnRepresentation k g) hp w) := by
  let T := kernelColumnRepresentation k g
  let P := locallyPeriodicProjection T hp
  have ho (v w : kernelColumnSpan k) : kernelColumnPairing k (P v) (w - P w) = 0 :=
    kernelColumnPairing_fixed_moving hk g _ _
      (locallyPeriodicProjection_fixed T hp v)
      (by simpa only [neg_smul, one_smul, sub_eq_add_neg] using
        add_neg_locallyPeriodicProjection_mem_range T hp w)
  have hvw := ho v w
  rw [map_sub] at hvw
  have hwv := ho w v
  rw [map_sub] at hwv
  have hc := congrArg (starRingEnd ℂ) (sub_eq_zero.mp hwv)
  rw [← kernelColumnPairing_conj_symm hk, ← kernelColumnPairing_conj_symm hk] at hc
  exact (sub_eq_zero.mp hvw).trans hc.symm

/-- Fixed and moving projections give an orthogonal decomposition of the column form. -/
theorem kernelColumnPairing_projection_decomposition {k : G → ℂ} (hk : IsHermKernel k)
    (g : G) (hp : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k g) ^ m) x = x)
    (v w : kernelColumnSpan k) :
    let P := locallyPeriodicProjection (kernelColumnRepresentation k g) hp
    kernelColumnPairing k v w = kernelColumnPairing k (P v) (P w) +
      kernelColumnPairing k (v - P v) (w - P w) := by
  let T := kernelColumnRepresentation k g
  let P := locallyPeriodicProjection T hp
  change kernelColumnPairing k v w = kernelColumnPairing k (P v) (P w) +
    kernelColumnPairing k (v - P v) (w - P w)
  have ho := kernelColumnPairing_fixed_moving hk g (P v) (w - P w)
    (locallyPeriodicProjection_fixed T hp v)
    (by simpa only [neg_smul, one_smul, sub_eq_add_neg] using
      add_neg_locallyPeriodicProjection_mem_range T hp w)
  have hs := kernelColumnPairing_projection_selfadjoint hk g hp v w
  have hl := LinearMap.congr_fun (map_sub (kernelColumnSesquilinear k hk) v (P v)) (w - P w)
  change kernelColumnPairing k (v - P v) (w - P w) =
    kernelColumnPairing k v (w - P w) - kernelColumnPairing k (P v) (w - P w) at hl
  have hproj := ho
  rw [map_sub] at hproj
  rw [hl, ho, sub_zero, map_sub, ← hs, sub_eq_zero.mp hproj]
  ring

#print axioms kernelColumnPairing_fixed_moving
#print axioms kernelColumnPairing_projection_selfadjoint
#print axioms kernelColumnPairing_projection_decomposition

/-- A projected Gram entry is a finite cyclic average of the original pairing. -/
theorem kernelColumnPairing_projection_average {k : G → ℂ} (hk : IsHermKernel k)
    (g : G) (hp : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k g) ^ m) x = x)
    (v w : kernelColumnSpan k) {m : ℕ} (hm : m ≠ 0)
    (hw : ((kernelColumnRepresentation k g) ^ m) w = w) :
    let P := locallyPeriodicProjection (kernelColumnRepresentation k g) hp
    kernelColumnPairing k (P v) (P w) =
      (m : ℂ)⁻¹ * ∑ j ∈ Finset.range m,
        kernelColumnPairing k v (((kernelColumnRepresentation k g) ^ j) w) := by
  let T := kernelColumnRepresentation k g
  let P := locallyPeriodicProjection T hp
  change kernelColumnPairing k (P v) (P w) = _
  rw [kernelColumnPairing_projection_selfadjoint hk g hp v (P w)]
  rw [locallyPeriodicProjection_apply_of_fixed T hp
    (locallyPeriodicProjection_fixed T hp w)]
  rw [locallyPeriodicProjection_eq_average T hp hm hw]
  simp only [periodicOrbitAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, smul_eq_mul, map_sum, T]

#print axioms kernelColumnPairing_projection_average
end GaloisForLFunctions.HeckeKreinToeplitz
