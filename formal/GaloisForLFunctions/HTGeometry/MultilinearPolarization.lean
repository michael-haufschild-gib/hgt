import GaloisForLFunctions.HTGeometry.SymmetricMultilinearPolarization
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Polarization: a symmetric multilinear map is determined by its diagonal

The signed finite difference of the diagonal of an order-`n` multilinear map keeps exactly the
surjective slot selections, and for an endomap of `Fin n` surjectivity is being a permutation.  For
a symmetric map all `n!` permutations give the same value, so

```text
∑ s ⊆ Fin n, (-1) ^ (n - |s|) • B (∑_{j ∈ s} v j, …, ∑_{j ∈ s} v j) = n! • B (v 0, …, v (n-1)) .
```

No topology and no norm enter: this is an identity of `MultilinearMap`s over an arbitrary
commutative ring, and it is enough to force two symmetric multilinear maps with the same diagonal to
agree whenever `n!` is invertible in the ring — over `ℝ` or `ℚ`, always.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {R V W : Type*} [CommRing R] [AddCommMonoid V] [Module R V]
  [AddCommMonoid W] [Module R W]

/-- Expand a diagonal value of a multilinear map as a sum over all slot selections. -/
theorem multilinearMap_diagonal_sum {n : ℕ} (B : MultilinearMap R (fun _ : Fin n => V) W)
    (dirs : Fin n → V) (s : Finset (Fin n)) :
    B (fun _ => ∑ j ∈ s, dirs j)
      = ∑ r ∈ Fintype.piFinset (fun _ : Fin n => s), B (fun i => dirs (r i)) := by
  simpa only using B.map_sum_finset (fun _ j => dirs j) (fun _ => s)

/-- Inclusion–exclusion in the diagonal polarization sum retains exactly the surjective slot
endomaps.  Symmetry is not used at this stage. -/
theorem multilinearMap_polarization_sum_eq_surjective {n : ℕ}
    (B : MultilinearMap R (fun _ : Fin n => V) W) (dirs : Fin n → V) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      (-1 : R) ^ (n - s.card) • B (fun _ => ∑ j ∈ s, dirs j))
      = ∑ r : Fin n → Fin n, if Function.Surjective r then B (fun i => dirs (r i)) else 0 := by
  classical
  simp_rw [multilinearMap_diagonal_sum, piFinset_const_eq_filter_range, smul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ : Finset (Fin n)).powerset.filter (fun s => Finset.univ.image r ⊆ s)
        = Finset.Icc (Finset.univ.image r) Finset.univ := by
    ext s
    simp
  rw [hfilter, ← Finset.sum_smul]
  have hcoeff := sum_Icc_neg_one_pow_card_sub (R := R) (r := Finset.univ.image r)
  simp only [Fintype.card_fin] at hcoeff
  rw [hcoeff]
  have hrange : Finset.univ.image r = (Finset.univ : Finset (Fin n)) ↔ Function.Surjective r := by
    constructor
    · intro h b
      have hb : b ∈ Finset.univ.image r := by rw [h]; simp
      simpa using hb
    · intro h
      refine Finset.eq_univ_iff_forall.mpr fun b => ?_
      obtain ⟨a, rfl⟩ := h b
      simp
  by_cases hsurj : Function.Surjective r
  · simp [hsurj, hrange.mpr hsurj]
  · have himage : Finset.univ.image r ≠ (Finset.univ : Finset (Fin n)) := fun h => hsurj (hrange.mp h)
    simp [hsurj, himage]

/-- **The unnormalised polarization identity.**  The signed finite difference of the diagonal of a
symmetric multilinear map is `n!` times its mixed value. -/
theorem multilinearMap_symmetric_polarization_sum {n : ℕ}
    (B : MultilinearMap R (fun _ : Fin n => V) W) (dirs : Fin n → V)
    (hsymm : ∀ σ : Equiv.Perm (Fin n), B (fun i => dirs (σ i)) = B dirs) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
      (-1 : R) ^ (n - s.card) • B (fun _ => ∑ j ∈ s, dirs j))
      = (n.factorial : R) • B dirs := by
  classical
  rw [multilinearMap_polarization_sum_eq_surjective]
  trans ∑ _r : Fin n → Fin n, if Function.Surjective _r then B dirs else 0
  · refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hsurj : Function.Surjective r
    · have hbij : Function.Bijective r :=
        (Fintype.bijective_iff_surjective_and_card r).2 ⟨hsurj, rfl⟩
      simp only [if_pos hsurj]
      simpa using hsymm (Equiv.ofBijective r hbij)
    · simp [hsurj]
  · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, card_surjective_end,
      ← Nat.cast_smul_eq_nsmul R]

/-- **A symmetric multilinear map is determined by its diagonal** whenever `n!` is invertible. -/
theorem multilinearMap_eq_of_diagonal_eq {n : ℕ}
    (B C : MultilinearMap R (fun _ : Fin n => V) W)
    (hB : ∀ (σ : Equiv.Perm (Fin n)) (m : Fin n → V), B (fun i => m (σ i)) = B m)
    (hC : ∀ (σ : Equiv.Perm (Fin n)) (m : Fin n → V), C (fun i => m (σ i)) = C m)
    (hdiag : ∀ v : V, B (fun _ => v) = C (fun _ => v))
    (hunit : IsUnit (n.factorial : R)) : B = C := by
  obtain ⟨u, hu⟩ := hunit
  ext dirs
  have hfac : (n.factorial : R) • B dirs = (n.factorial : R) • C dirs := by
    rw [← multilinearMap_symmetric_polarization_sum B dirs (fun σ => hB σ dirs),
      ← multilinearMap_symmetric_polarization_sum C dirs (fun σ => hC σ dirs)]
    exact Finset.sum_congr rfl fun s _ => by rw [hdiag]
  rw [← hu] at hfac
  calc B dirs = ((u⁻¹ : Rˣ) : R) • ((u : R) • B dirs) := by
        rw [smul_smul, Units.inv_mul, one_smul]
    _ = ((u⁻¹ : Rˣ) : R) • ((u : R) • C dirs) := by rw [hfac]
    _ = C dirs := by rw [smul_smul, Units.inv_mul, one_smul]

end GaloisForLFunctions.HTGeometry
