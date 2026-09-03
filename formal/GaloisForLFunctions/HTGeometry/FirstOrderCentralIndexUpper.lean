import GaloisForLFunctions.HTGeometry.FirstOrderCoefficientDecomposition
import GaloisForLFunctions.HTGeometry.GoldbergCentralIndex

open Finset Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- Every transcendental entire solution of an arbitrary order-one ADE has eventually polynomially
bounded central index. -/
theorem exists_centralIndex_le_pow_of_order_one
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ((centralIndex a t : ℕ) : ℝ) ≤ C * t ^ K := by
  classical
  obtain ⟨S, A, -, hne, -, hrel⟩ :=
    exists_firstOrderRelation_of_differentiallyAlgebraicOfOrder_one hDA
  set S₀ : Finset (ℕ × ℕ) := S.filter (fun p => A p ≠ 0) with hS₀
  have hS₀ne : S₀.Nonempty := by
    obtain ⟨p, hpS, hpA⟩ := hne
    exact ⟨p, Finset.mem_filter.mpr ⟨hpS, hpA⟩⟩
  have hS₀sub : S₀ ⊆ S := by
    rw [hS₀]
    exact Finset.filter_subset _ _
  have hA₀ : ∀ p ∈ S₀, A p ≠ 0 := by
    intro p hp
    rw [hS₀, Finset.mem_filter] at hp
    exact hp.2
  have hrel₀ : ∀ z : ℂ,
      ∑ p ∈ S₀, (A p).eval z * (coeffFun a z) ^ p.1 *
        (deriv (coeffFun a) z) ^ p.2 = 0 := by
    intro z
    rw [Finset.sum_subset hS₀sub]
    · exact hrel z
    · intro p hpS hpnot
      have hAp : A p = 0 := by
        by_contra hpA
        exact hpnot (by rw [hS₀, Finset.mem_filter]; exact ⟨hpS, hpA⟩)
      rw [hAp]
      simp
  obtain ⟨q, hqS₀, hqmax⟩ :=
    Finset.exists_max_image S₀ (fun p => p.1 + p.2) hS₀ne
  set d : ℕ := q.1 + q.2 with hd
  have hdeg₀ : ∀ p ∈ S₀, p.1 + p.2 ≤ d := by
    intro p hp
    rw [hd]
    exact hqmax p hp
  let sh : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.2 + 1)
  have hshinj : Function.Injective sh := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ hpq
    simp only [sh, Prod.mk.injEq] at hpq ⊢
    omega
  set S₁ : Finset (ℕ × ℕ) := S₀.image sh with hS₁
  let A₁ : ℕ × ℕ → Polynomial ℂ := fun p => A (p.1, p.2 - 1)
  have hmem₁ : ∀ p, p ∈ S₁ ↔ ∃ q ∈ S₀, sh q = p := by
    intro p
    rw [hS₁, Finset.mem_image]
  have hA₁sh : ∀ p, A₁ (sh p) = A p := by
    intro p
    simp [A₁, sh]
  have hdeg₁ : ∀ p ∈ S₁, p.1 + p.2 ≤ d + 1 := by
    intro p hp
    obtain ⟨q', hq'S₀, rfl⟩ := (hmem₁ p).mp hp
    have hq'deg := hdeg₀ q' hq'S₀
    dsimp [sh]
    omega
  have hrel₁ : ∀ z : ℂ,
      ∑ p ∈ S₁, (A₁ p).eval z * (coeffFun a z) ^ p.1 *
        (deriv (coeffFun a) z) ^ p.2 = 0 := by
    intro z
    rw [hS₁, Finset.sum_image]
    · simp_rw [hA₁sh]
      calc
        ∑ p ∈ S₀, (A p).eval z * (coeffFun a z) ^ p.1 *
              deriv (coeffFun a) z ^ (p.2 + 1) =
            (∑ p ∈ S₀, (A p).eval z * (coeffFun a z) ^ p.1 *
              deriv (coeffFun a) z ^ p.2) * deriv (coeffFun a) z := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro p _
                rw [pow_succ]
                ring
        _ = 0 := by rw [hrel₀ z, zero_mul]
    · exact fun x _ y _ hxy => hshinj hxy
  set Stop : Finset (ℕ × ℕ) := S₁.filter (fun p => p.1 + p.2 = d + 1) with hStop
  have hqStop : sh q ∈ Stop := by
    rw [hStop, Finset.mem_filter, hS₁, Finset.mem_image]
    refine ⟨⟨q, hqS₀, rfl⟩, ?_⟩
    dsimp [sh]
    omega
  have hStopne : Stop.Nonempty := ⟨sh q, hqStop⟩
  obtain ⟨t, htStop, htmax⟩ := Finset.exists_max_image Stop Prod.snd hStopne
  set m : ℕ := t.2 with hm
  have htStop' := htStop
  rw [hStop, Finset.mem_filter] at htStop'
  have htS₁ : t ∈ S₁ := htStop'.1
  have htd : t.1 + t.2 = d + 1 := htStop'.2
  obtain ⟨u, huS₀, hu⟩ := (hmem₁ t).mp htS₁
  have hmpos : 1 ≤ m := by
    rw [hm, ← hu]
    dsimp [sh]
    omega
  have hmle : m ≤ d + 1 := by omega
  have htcoord : t = (d + 1 - m, m) := by
    apply Prod.ext
    · dsimp
      rw [hm]
      omega
    · exact hm.symm
  have htargetMem : (d + 1 - m, m) ∈ S₁ := by
    rw [← htcoord]
    exact htS₁
  have htopdeg : ∀ p ∈ S₁, p.1 + p.2 = d + 1 → p.2 ≤ m := by
    intro p hpS₁ hpd
    have hpStop : p ∈ Stop := by
      rw [hStop, Finset.mem_filter]
      exact ⟨hpS₁, hpd⟩
    rw [hm]
    exact htmax p hpStop
  have hAne : A₁ (d + 1 - m, m) ≠ 0 := by
    rw [← htcoord, ← hu, hA₁sh]
    exact hA₀ u huS₀
  exact exists_centralIndex_le_pow_of_relation ha hn₀ htrans hdeg₁ hrel₁
    hmpos hmle htargetMem htopdeg hAne

end

end GaloisForLFunctions.HTGeometry
