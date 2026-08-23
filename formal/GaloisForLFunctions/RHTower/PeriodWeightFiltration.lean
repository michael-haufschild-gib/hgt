import Mathlib

/-!
# The weighted period filtration

Euler's constant and every prime logarithm carry weight one, and `ζ(k)` carries weight `k`.  The
weight-`≤ T` layer is the `ℚ`-span of all products of generators of total weight at most `T`.  It
is closed under multiplication with weights adding, and it is finite-dimensional: weights are
positive, so a product of total weight `≤ T` has at most `T` factors, drawn from the finite
generator set of weight `≤ T`.
-/

open Set

namespace RHTower

noncomputable section

/-- Weighted generators of the friable period filtration. -/
def periodGen (S : Finset ℕ) : Set (ℂ × ℕ) :=
  insert (((Real.eulerMascheroniConstant : ℝ) : ℂ), 1)
    ({x : ℂ × ℕ | ∃ k : ℕ, 2 ≤ k ∧ x = (riemannZeta (k : ℂ), k)}
      ∪ {x : ℂ × ℕ | ∃ p ∈ S, x = (((Real.log p : ℝ) : ℂ), 1)})

theorem periodGen_weight_pos {S : Finset ℕ} {g : ℂ × ℕ} (hg : g ∈ periodGen S) : 0 < g.2 := by
  rcases hg with h | h | h
  · rw [h]
    exact one_pos
  · obtain ⟨k, hk, rfl⟩ := h
    exact lt_of_lt_of_le two_pos hk
  · obtain ⟨p, _, rfl⟩ := h
    exact one_pos

/-- Products of weighted generators of total weight at most `T`. -/
def periodProducts (S : Finset ℕ) (T : ℕ) : Set ℂ :=
  {x | ∃ l : List (ℂ × ℕ), (∀ g ∈ l, g ∈ periodGen S) ∧ (l.map Prod.snd).sum ≤ T
    ∧ x = (l.map Prod.fst).prod}

/-- The weight-`≤ T` layer of the period filtration. -/
def periodFilt (S : Finset ℕ) (T : ℕ) : Submodule ℚ ℂ :=
  Submodule.span ℚ (periodProducts S T)

theorem one_mem_periodProducts (S : Finset ℕ) (T : ℕ) : (1 : ℂ) ∈ periodProducts S T :=
  ⟨[], by simp, by simp, by simp⟩

theorem periodProducts_mono (S : Finset ℕ) {T T' : ℕ} (h : T ≤ T') :
    periodProducts S T ⊆ periodProducts S T' := by
  rintro x ⟨l, hl, hw, rfl⟩
  exact ⟨l, hl, hw.trans h, rfl⟩

theorem periodFilt_mono (S : Finset ℕ) {T T' : ℕ} (h : T ≤ T') :
    periodFilt S T ≤ periodFilt S T' :=
  Submodule.span_mono (periodProducts_mono S h)

theorem mul_mem_periodProducts {S : Finset ℕ} {a b : ℕ} {x y : ℂ}
    (hx : x ∈ periodProducts S a) (hy : y ∈ periodProducts S b) :
    x * y ∈ periodProducts S (a + b) := by
  obtain ⟨l, hl, hwl, rfl⟩ := hx
  obtain ⟨m, hm, hwm, rfl⟩ := hy
  refine ⟨l ++ m, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hl g h
    · exact hm g h
  · rw [List.map_append, List.sum_append]
    exact Nat.add_le_add hwl hwm
  · rw [List.map_append, List.prod_append]

theorem one_mem_periodFilt (S : Finset ℕ) (T : ℕ) : (1 : ℂ) ∈ periodFilt S T :=
  Submodule.subset_span (one_mem_periodProducts S T)

theorem ratCast_mem_periodFilt (S : Finset ℕ) (T : ℕ) (q : ℚ) :
    ((q : ℚ) : ℂ) ∈ periodFilt S T := by
  have h := (periodFilt S T).smul_mem q (one_mem_periodFilt S T)
  rwa [Rat.smul_one_eq_cast] at h

theorem periodFilt_mul {S : Finset ℕ} {a b : ℕ} {x y : ℂ}
    (hx : x ∈ periodFilt S a) (hy : y ∈ periodFilt S b) :
    x * y ∈ periodFilt S (a + b) := by
  have hmul : periodFilt S a * periodFilt S b ≤ periodFilt S (a + b) := by
    rw [periodFilt, periodFilt, Submodule.span_mul_span]
    refine Submodule.span_mono ?_
    rintro z ⟨u, hu, v, hv, rfl⟩
    exact mul_mem_periodProducts hu hv
  exact hmul (Submodule.mul_mem_mul hx hy)

theorem eulerMascheroni_mem_periodFilt (S : Finset ℕ) :
    (((Real.eulerMascheroniConstant : ℝ) : ℂ)) ∈ periodFilt S 1 := by
  refine Submodule.subset_span ⟨[(((Real.eulerMascheroniConstant : ℝ) : ℂ), 1)], ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_singleton.mp hg]
    exact Or.inl rfl
  · simp
  · simp

theorem riemannZeta_mem_periodFilt (S : Finset ℕ) {k : ℕ} (hk : 2 ≤ k) :
    riemannZeta (k : ℂ) ∈ periodFilt S k := by
  refine Submodule.subset_span ⟨[(riemannZeta (k : ℂ), k)], ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_singleton.mp hg]
    exact Or.inr (Or.inl ⟨k, hk, rfl⟩)
  · simp
  · simp

theorem log_mem_periodFilt {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    (((Real.log p : ℝ) : ℂ)) ∈ periodFilt S 1 := by
  refine Submodule.subset_span ⟨[(((Real.log p : ℝ) : ℂ), 1)], ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_singleton.mp hg]
    exact Or.inr (Or.inr ⟨p, hp, rfl⟩)
  · simp
  · simp

/-! ## Finite dimensionality -/

/-- Weighted generators of weight at most `T`. -/
def periodGenLe (S : Finset ℕ) (T : ℕ) : Set (ℂ × ℕ) := {g | g ∈ periodGen S ∧ g.2 ≤ T}

theorem finite_periodGenLe (S : Finset ℕ) (T : ℕ) : (periodGenLe S T).Finite := by
  refine Set.Finite.subset (Set.Finite.union (Set.finite_singleton
      (((Real.eulerMascheroniConstant : ℝ) : ℂ), 1))
    (Set.Finite.union
      (Set.Finite.image (fun k : ℕ => (riemannZeta (k : ℂ), k))
        (Finset.finite_toSet (Finset.Icc 2 T)))
      (Set.Finite.image (fun p : ℕ => (((Real.log p : ℝ) : ℂ), 1))
        (Finset.finite_toSet S)))) ?_
  rintro g ⟨hg, hw⟩
  rcases hg with h | h | h
  · exact Or.inl h
  · obtain ⟨k, hk, rfl⟩ := h
    refine Or.inr (Or.inl ⟨k, ?_, rfl⟩)
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨hk, hw⟩
  · obtain ⟨p, hp, rfl⟩ := h
    exact Or.inr (Or.inr ⟨p, hp, rfl⟩)

theorem finite_periodProducts (S : Finset ℕ) (T : ℕ) : (periodProducts S T).Finite := by
  classical
  have hfin := finite_periodGenLe S T
  have hsub : Finite ↥(periodGenLe S T) := hfin.to_subtype
  have hlists : Set.Finite
      ((fun l : List ↥(periodGenLe S T) =>
        (List.map (fun g : ↥(periodGenLe S T) => (g : ℂ × ℕ).1) l).prod)
        '' {l : List ↥(periodGenLe S T) | l.length ≤ T}) :=
    Set.Finite.image _ (List.finite_length_le _ T)
  refine Set.Finite.subset hlists ?_
  rintro x ⟨l, hl, hw, rfl⟩
  have hmem : ∀ g ∈ l, g ∈ periodGenLe S T := by
    intro g hg
    refine ⟨hl g hg, ?_⟩
    have hle : g.2 ≤ (l.map Prod.snd).sum := by
      refine List.le_sum_of_mem ?_
      exact List.mem_map_of_mem hg
    omega
  refine ⟨l.pmap (fun g h => (⟨g, h⟩ : ↥(periodGenLe S T))) hmem, ?_, ?_⟩
  · have hlen : (l.pmap (fun g h => (⟨g, h⟩ : ↥(periodGenLe S T))) hmem).length = l.length :=
      List.length_pmap
    rw [Set.mem_setOf_eq, hlen]
    have hone : ∀ i ∈ l.map Prod.snd, 1 ≤ i := by
      intro i hi
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hi
      exact periodGen_weight_pos (hl g hg)
    have := List.length_le_sum_of_one_le (l.map Prod.snd) hone
    rw [List.length_map] at this
    omega
  · show (List.map (fun g : ↥(periodGenLe S T) => (g : ℂ × ℕ).1)
        (l.pmap (fun g h => (⟨g, h⟩ : ↥(periodGenLe S T))) hmem)).prod = (l.map Prod.fst).prod
    rw [List.map_pmap]
    congr 1
    exact List.pmap_eq_map _

instance finiteDimensional_periodFilt (S : Finset ℕ) (T : ℕ) :
    Module.Finite ℚ (periodFilt S T) :=
  Module.Finite.span_of_finite ℚ (finite_periodProducts S T)

end

end RHTower
