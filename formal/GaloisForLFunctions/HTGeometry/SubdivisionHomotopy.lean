import GaloisForLFunctions.HTGeometry.SmallChains

/-!
# The iterated subdivision homotopy, and smallness in homology

Composing the subdivision homotopy with the powers of the subdivision gives, for each `N`, a chain
homotopy `D_N = ∑_{i < N} T ∘ Sd^i` from `Sd^N` to the identity:

  `∂ D_N + D_N ∂ = Sd^N − 1`.

Since a chain has finitely many simplices, one `N` makes it small, and since `Sd` and `T` never
enlarge the image of a simplex, `D_N` preserves smallness.  Two consequences follow with no
per-simplex bookkeeping:

* every cycle is homologous to a small cycle;
* a small cycle that bounds, bounds a small chain.

Together these say that the chains that are small for a cover compute the same homology as all
chains — the statement excision rests on.
-/

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

/-- The boundary commutes with iterated subdivision. -/
theorem singBd_singSdPow {k : ℕ} (N : ℕ) (c : C(topSimplex (k + 1), X) →₀ R) :
    singBd R X k (singSdPow R (k + 1) N c) = singSdPow R k N (singBd R X k c) := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih =>
    rw [singSdPow_succ, singBd_singSd, ih, singSdPow_succ]

/-- The chain homotopy from the `N`-fold subdivision to the identity. -/
noncomputable def singD (k N : ℕ) :
    (C(topSimplex k, X) →₀ R) →ₗ[R] (C(topSimplex (k + 1), X) →₀ R) :=
  ∑ i ∈ Finset.range N, (singT R k).comp (singSdPow R k i)

theorem singD_zero {k : ℕ} (c : C(topSimplex k, X) →₀ R) : singD R k 0 c = 0 := by
  rw [singD, Finset.range_zero, Finset.sum_empty, LinearMap.zero_apply]

theorem singD_succ {k N : ℕ} (c : C(topSimplex k, X) →₀ R) :
    singD R k (N + 1) c = singD R k N c + singT R k (singSdPow R k N c) := by
  rw [singD, singD, Finset.sum_range_succ, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.sum_apply, LinearMap.comp_apply]

/-- **The iterated subdivision is chain homotopic to the identity.** -/
theorem singBd_singD {k : ℕ} (N : ℕ) (c : C(topSimplex (k + 1), X) →₀ R) :
    singBd R X (k + 1) (singD R (k + 1) N c) + singD R k N (singBd R X k c)
      = singSdPow R (k + 1) N c - c := by
  induction N generalizing c with
  | zero =>
    rw [singD_zero, singD_zero, map_zero, add_zero, singSdPow_zero, sub_self]
  | succ N ih =>
    have hy := singBd_singT R (k := k) (singSdPow R (k + 1) N c)
    have hbd : singSdPow R k N (singBd R X k c) = singBd R X k (singSdPow R (k + 1) N c) :=
      (singBd_singSdPow R N c).symm
    rw [singD_succ, singD_succ, map_add, hbd, singSdPow_succ]
    calc (singBd R X (k + 1) (singD R (k + 1) N c)
            + singBd R X (k + 1) (singT R (k + 1) (singSdPow R (k + 1) N c)))
          + (singD R k N (singBd R X k c)
            + singT R k (singBd R X k (singSdPow R (k + 1) N c)))
        = (singBd R X (k + 1) (singD R (k + 1) N c) + singD R k N (singBd R X k c))
          + (singBd R X (k + 1) (singT R (k + 1) (singSdPow R (k + 1) N c))
            + singT R k (singBd R X k (singSdPow R (k + 1) N c))) := by abel
      _ = (singSdPow R (k + 1) N c - c)
          + (singSd R (k + 1) (singSdPow R (k + 1) N c) - singSdPow R (k + 1) N c) := by
            rw [ih c, hy]
      _ = singSd R (k + 1) (singSdPow R (k + 1) N c) - c := by abel

theorem smallChain_singD {𝒰 : Set (Set X)} {k : ℕ} (N : ℕ) {c : C(topSimplex k, X) →₀ R}
    (hc : SmallChain R 𝒰 c) : SmallChain R 𝒰 (singD R k N c) := by
  induction N with
  | zero => rw [singD_zero]; exact smallChain_zero R 𝒰
  | succ N ih =>
    rw [singD_succ]
    exact smallChain_add R ih (smallChain_singT R (smallChain_singSdPow R N hc))

/-! ### Smallness in homology -/

/-- **Every cycle is homologous to a small cycle.** -/
theorem exists_small_cycle_homologous (𝒰 : Set (Set X)) (hopen : ∀ U ∈ 𝒰, IsOpen U)
    (hcover : (Set.univ : Set X) ⊆ ⋃₀ 𝒰) {k : ℕ} (z : C(topSimplex (k + 1), X) →₀ R)
    (hz : singBd R X k z = 0) :
    ∃ z' : C(topSimplex (k + 1), X) →₀ R, SmallChain R 𝒰 z' ∧ singBd R X k z' = 0
      ∧ ∃ b : C(topSimplex (k + 2), X) →₀ R, z' - z = singBd R X (k + 1) b := by
  obtain ⟨N, hN⟩ := exists_singSdPow_small R 𝒰 hopen hcover z
  refine ⟨singSdPow R (k + 1) N z, hN, ?_, singD R (k + 1) N z, ?_⟩
  · rw [singBd_singSdPow, hz, map_zero]
  · have h := singBd_singD R N z
    rw [hz, map_zero, add_zero] at h
    exact h.symm

/-- **A small cycle that bounds, bounds a small chain.** -/
theorem exists_small_bounding (𝒰 : Set (Set X)) (hopen : ∀ U ∈ 𝒰, IsOpen U)
    (hcover : (Set.univ : Set X) ⊆ ⋃₀ 𝒰) {k : ℕ} (z : C(topSimplex (k + 1), X) →₀ R)
    (hz : SmallChain R 𝒰 z) (b : C(topSimplex (k + 2), X) →₀ R)
    (hb : z = singBd R X (k + 1) b) :
    ∃ b' : C(topSimplex (k + 2), X) →₀ R, SmallChain R 𝒰 b' ∧ z = singBd R X (k + 1) b' := by
  obtain ⟨N, hN⟩ := exists_singSdPow_small R 𝒰 hopen hcover b
  refine ⟨singSdPow R (k + 2) N b - singD R (k + 1) N z, ?_, ?_⟩
  · exact smallChain_sub R hN (smallChain_singD R N hz)
  · have h := singBd_singD R (k := k + 1) N b
    have h2 := congrArg (fun w => singBd R X (k + 1) w) h
    simp only [map_add, map_sub] at h2
    rw [singBd_singBd, zero_add, ← hb] at h2
    rw [map_sub]
    rw [← h2]
    abel

end GaloisForLFunctions.HTGeometry
