import GaloisForLFunctions.HTGeometry.DiscreteOrbitReciprocity
import GaloisForLFunctions.HTGeometry.TripticCornerAccumulation

/-!
# Triptic orbit-residue reciprocity

Let `τ` and `σ` lie in the upper half plane with `1, τ, σ` independent over the integers, and let
`F` be meromorphic on the plane, `1`-periodic, with constant mixed difference

`F(z+τ+σ) - F(z+τ) - F(z+σ) + F(z) = C`.

The two boundary functions `Δ_σ F` and `Δ_τ F` then have, respectively, `τ`-periodic and
`σ`-periodic principal parts.  Summing a fixed principal-part coefficient of `Δ_σ F` along the
`σ`-orbit of a point gives the same number as summing the corresponding coefficient of `Δ_τ F`
along the `τ`-orbit.

The proof is the direct one: the doubly-indexed coefficient array of `F` has row-independent and
column-independent increments, hence is additively separable; its two boundary jump families have
finite support, so the separated summands are eventually constant in all four directions; and the
two mixed quadrants force the two corner constants to vanish, which is exactly the equality of the
two total jumps.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-! ### Discrete preliminaries -/

/-- A sequence whose forward increments vanish beyond a threshold is constant beyond it. -/
theorem eq_of_forall_ge_increment_zero {d : ℤ → ℂ} {N : ℤ}
    (h : ∀ n : ℤ, N ≤ n → d (n + 1) = d n) : ∀ n : ℤ, N ≤ n → d n = d N := by
  intro n hn
  induction n, hn using Int.le_induction with
  | base => rfl
  | succ k hk ih => rw [h k hk, ih]

/-- A sequence whose forward increments vanish below a threshold is constant below it. -/
theorem eq_of_forall_le_increment_zero {d : ℤ → ℂ} {N : ℤ}
    (h : ∀ n : ℤ, n < N → d (n + 1) = d n) : ∀ n : ℤ, n ≤ N → d n = d N := by
  intro n hn
  induction n, hn using Int.le_induction_down with
  | base => rfl
  | pred k hk ih =>
      have hstep := h (k - 1) (by omega)
      rw [show k - 1 + 1 = k from by ring] at hstep
      rw [hstep, ih]

/-- Telescoping over a symmetric integer interval. -/
theorem sum_Ico_increment_telescope (d : ℤ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), (d (n + 1) - d n) = d (N : ℤ) - d (-(N : ℤ)) := by
  classical
  have h := Finset.sum_range_sub (fun j : ℕ => d ((j : ℤ) - (N : ℤ))) (2 * N)
  have hreindex : ∑ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), (d (n + 1) - d n)
      = ∑ j ∈ Finset.range (2 * N),
        ((fun j : ℕ => d ((j : ℤ) - (N : ℤ))) (j + 1)
          - (fun j : ℕ => d ((j : ℤ) - (N : ℤ))) j) := by
    refine Finset.sum_nbij' (i := fun n => (n + (N : ℤ)).toNat)
      (j := fun j => (j : ℤ) - (N : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_Ico] at hn ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Ico]
      omega
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      have h1 : (((n + (N : ℤ)).toNat : ℤ) - (N : ℤ)) = n := by omega
      have h2 : ((((n + (N : ℤ)).toNat + 1 : ℕ) : ℤ) - (N : ℤ)) = n + 1 := by
        push_cast
        omega
      simp only [h1, h2]
  rw [hreindex, h]
  congr 1 <;> [skip; skip] <;> congr 1 <;> push_cast <;> ring

/-- A finitely supported family is supported in a symmetric interval. -/
theorem exists_symmetric_bound_of_finite_support {A : ℤ → ℂ}
    (hA : {n : ℤ | A n ≠ 0}.Finite) :
    ∃ N : ℕ, ∀ n : ℤ, ((N : ℤ) ≤ n ∨ n < -(N : ℤ)) → A n = 0 := by
  classical
  obtain ⟨s, hs⟩ := hA.exists_finset
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ∈ s, |n| < (M : ℤ) := by
    refine ⟨(s.image fun n => n.natAbs).sup id + 1, fun n hn => ?_⟩
    have : n.natAbs ≤ (s.image fun n => n.natAbs).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hn)
    omega
  refine ⟨M, fun n hn => ?_⟩
  by_contra hne
  have := hM n ((hs n).mpr hne)
  omega

end GaloisForLFunctions.HTGeometry
