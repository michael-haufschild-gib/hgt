import GaloisForLFunctions.HTGeometry.DifferentialOperatorOre

/-!
# Coefficientwise transport of differential operators

A ring homomorphism between differential rings transports operators coefficientwise.  Only the
additive and scalar structure is used here, so no compatibility with the derivations is required;
the transported operator has the same order whenever the homomorphism is injective.

This file also records the coefficient of a product computed over any finite set carrying the
support of the left factor.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} {L : Type v} [CommRing K] [Differential K] [CommRing L] [Differential L]

/-- Coefficientwise transport of an operator along a ring homomorphism. -/
def map (f : K →+* L) (p : DiffOp K) : DiffOp L :=
  ofFinsupp (Finsupp.mapRange f (map_zero f) (toFinsupp p))

@[simp] theorem coeff_map (f : K →+* L) (p : DiffOp K) (n : ℕ) :
    coeff (map f p) n = f (coeff p n) := by
  rw [map, coeff, toFinsupp_ofFinsupp, Finsupp.mapRange_apply]
  rfl

theorem map_add (f : K →+* L) (p q : DiffOp K) : map f (p + q) = map f p + map f q := by
  ext n
  rw [coeff_map, coeff_add, coeff_add, coeff_map, coeff_map, RingHom.map_add]

theorem map_smul (f : K →+* L) (a : K) (p : DiffOp K) :
    map f (a • p) = f a • map f p := by
  ext n
  rw [coeff_map, coeff_smul, coeff_smul, coeff_map, map_mul]

theorem map_mono (f : K →+* L) (n : ℕ) (a : K) : map f (mono n a) = mono n (f a) := by
  ext m
  rw [coeff_map, coeff_mono, coeff_mono]
  by_cases h : n = m
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

theorem degree_map_le (f : K →+* L) (p : DiffOp K) : degree (map f p) ≤ degree p := by
  refine degree_le_iff.mpr fun m hm => ?_
  rw [coeff_map, coeff_eq_zero_of_degree_lt hm, map_zero]

theorem degree_map (f : K →+* L) (hf : Function.Injective f) (p : DiffOp K) :
    degree (map f p) = degree p := by
  refine le_antisymm (degree_map_le f p) (degree_le_iff.mpr fun m hm => ?_)
  have h := coeff_eq_zero_of_degree_lt (p := map f p) hm
  rw [coeff_map] at h
  have hz : f (coeff p m) = f 0 := by rw [h, map_zero]
  exact hf hz

/-- The coefficient of a product, computed over any finite set carrying the support of the left
factor. -/
theorem coeff_mul_of_subset {p q : DiffOp K} {t : Finset ℕ} (ht : ∀ n ∉ t, coeff p n = 0)
    (N : ℕ) :
    coeff (p * q) N = ∑ n ∈ t, coeff p n * coeff (dpartial^[n] q) N := by
  classical
  rw [coeff_mul]
  have hsupp : ∑ n ∈ (toFinsupp p).support, coeff p n * coeff (dpartial^[n] q) N
      = ∑ n ∈ (toFinsupp p).support ∪ t, coeff p n * coeff (dpartial^[n] q) N := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro n _ hn
    rw [show coeff p n = 0 from by
      by_contra hc
      exact hn (Finsupp.mem_support_iff.mpr hc), zero_mul]
  have ht' : ∑ n ∈ t, coeff p n * coeff (dpartial^[n] q) N
      = ∑ n ∈ (toFinsupp p).support ∪ t, coeff p n * coeff (dpartial^[n] q) N := by
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro n _ hn
    rw [ht n hn, zero_mul]
  rw [hsupp, ← ht']

end

end DiffOp

end GaloisForLFunctions.HTGeometry
