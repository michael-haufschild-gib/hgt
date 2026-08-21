import GaloisForLFunctions.HTGeometry.SmallSimplices

/-!
# Chains that are small for a cover

A singular simplex is small for a family of subsets when its image lies inside one member, and a
chain is small when all its simplices are.  The subdivision operator, its chain homotopy and the
boundary all produce simplices whose images are contained in the image of the simplex they come
from — for subdivision and the homotopy because both are pushforwards along the simplex, for the
boundary because the faces are restrictions — so all three preserve smallness.

Since a chain has finitely many simplices, one number of subdivisions works for all of them at once:
every chain becomes small after finitely many subdivisions.  This is the form of the small simplices
theorem that the excision argument uses; no per-simplex bookkeeping is needed, because the argument
only ever subdivides one chain at a time.
-/

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] {X : Type v} [TopologicalSpace X]

/-- A singular simplex is small for `𝒰` when its image lies in a member of `𝒰`. -/
def SmallSimplex (𝒰 : Set (Set X)) {k : ℕ} (σ : C(topSimplex k, X)) : Prop :=
  ∃ U ∈ 𝒰, Set.range σ ⊆ U

/-- A chain is small when all of its simplices are. -/
def SmallChain (𝒰 : Set (Set X)) {k : ℕ} (c : C(topSimplex k, X) →₀ R) : Prop :=
  ∀ σ ∈ c.support, SmallSimplex 𝒰 σ

theorem SmallSimplex.mono {𝒰 : Set (Set X)} {k j : ℕ} {σ : C(topSimplex k, X)}
    {τ : C(topSimplex j, X)} (h : SmallSimplex 𝒰 σ) (hr : Set.range τ ⊆ Set.range σ) :
    SmallSimplex 𝒰 τ := by
  obtain ⟨U, hU, hsub⟩ := h
  exact ⟨U, hU, hr.trans hsub⟩

theorem smallChain_zero (𝒰 : Set (Set X)) {k : ℕ} :
    SmallChain R 𝒰 (0 : C(topSimplex k, X) →₀ R) := by
  intro σ hσ
  simp at hσ

theorem smallChain_add {𝒰 : Set (Set X)} {k : ℕ} {c d : C(topSimplex k, X) →₀ R}
    (hc : SmallChain R 𝒰 c) (hd : SmallChain R 𝒰 d) : SmallChain R 𝒰 (c + d) := by
  classical
  intro σ hσ
  rcases Finset.mem_union.mp (Finsupp.support_add hσ) with h | h
  · exact hc σ h
  · exact hd σ h

theorem smallChain_sub {𝒰 : Set (Set X)} {k : ℕ} {c d : C(topSimplex k, X) →₀ R}
    (hc : SmallChain R 𝒰 c) (hd : SmallChain R 𝒰 d) : SmallChain R 𝒰 (c - d) := by
  classical
  intro σ hσ
  rcases Finset.mem_union.mp (Finsupp.support_sub hσ) with h | h
  · exact hc σ h
  · exact hd σ h

theorem smallChain_smul {𝒰 : Set (Set X)} {k : ℕ} (r : R) {c : C(topSimplex k, X) →₀ R}
    (hc : SmallChain R 𝒰 c) : SmallChain R 𝒰 (r • c) :=
  fun σ hσ => hc σ (Finsupp.support_smul hσ)

/-! ### The three operators shrink images -/

theorem range_affSing_subset {k n : ℕ} (σ : C(topSimplex n, X))
    (w : Fin (k + 1) → (Fin (n + 1) → ℝ)) : Set.range (affSing σ w) ⊆ Set.range σ := by
  rintro _ ⟨x, rfl⟩
  exact ⟨simplexRetr (affComb w x), (affSing_apply σ w x).symm⟩

theorem range_subset_of_mem_affToSing {k n : ℕ} (σ : C(topSimplex n, X))
    (c : (Fin (k + 1) → (Fin (n + 1) → ℝ)) →₀ R) {τ : C(topSimplex k, X)}
    (hτ : τ ∈ (affToSing R σ c).support) : Set.range τ ⊆ Set.range σ := by
  obtain ⟨w, _, hw⟩ := support_linear_apply_subset R (affToSing R σ) c hτ
  rw [affToSing_single] at hw
  have hτw : τ = affSing σ w := Finset.mem_singleton.mp (Finsupp.support_single_subset hw)
  subst hτw
  exact range_affSing_subset σ w

/-- A simplex occurring in a finite formal combination of simplices is one of them. -/
theorem support_sum_single_subset {α : Type*} {ι : Type*} (s : Finset ι) (f : ι → α) (g : ι → R)
    {b : α} (hb : b ∈ (∑ i ∈ s, Finsupp.single (f i) (g i)).support) : ∃ i ∈ s, b = f i := by
  by_contra hcon
  push Not at hcon
  rw [Finsupp.mem_support_iff] at hb
  refine hb ?_
  rw [Finset.sum_apply']
  refine Finset.sum_eq_zero fun i hi => ?_
  exact Finsupp.single_eq_of_ne fun heq => hcon i hi heq

theorem range_subset_of_mem_singSd {k : ℕ} (σ : C(topSimplex k, X))
    {τ : C(topSimplex k, X)} (hτ : τ ∈ (singSd R k (Finsupp.single σ (1 : R))).support) :
    Set.range τ ⊆ Set.range σ := by
  rw [singSd_single, one_smul] at hτ
  exact range_subset_of_mem_affToSing R σ _ hτ

theorem range_subset_of_mem_singT {k : ℕ} (σ : C(topSimplex k, X))
    {τ : C(topSimplex (k + 1), X)} (hτ : τ ∈ (singT R k (Finsupp.single σ (1 : R))).support) :
    Set.range τ ⊆ Set.range σ := by
  rw [singT_single, one_smul] at hτ
  exact range_subset_of_mem_affToSing R σ _ hτ

theorem range_subset_of_mem_singBd {k : ℕ} (σ : C(topSimplex (k + 1), X))
    {τ : C(topSimplex k, X)} (hτ : τ ∈ (singBd R X k (Finsupp.single σ (1 : R))).support) :
    Set.range τ ⊆ Set.range σ := by
  rw [singBd_single] at hτ
  obtain ⟨i, _, rfl⟩ := support_sum_single_subset R Finset.univ
    (fun i : Fin (k + 2) => σ.comp (topMap i.succAbove)) (fun i => (-1 : R) ^ (i : ℕ)) hτ
  rintro _ ⟨x, rfl⟩
  exact ⟨topMap i.succAbove x, rfl⟩

/-- An operator that shrinks images preserves smallness. -/
theorem smallChain_map {𝒰 : Set (Set X)} {k j : ℕ}
    (L : (C(topSimplex k, X) →₀ R) →ₗ[R] (C(topSimplex j, X) →₀ R))
    (hL : ∀ σ : C(topSimplex k, X), ∀ τ ∈ (L (Finsupp.single σ (1 : R))).support,
      Set.range τ ⊆ Set.range σ)
    {c : C(topSimplex k, X) →₀ R} (hc : SmallChain R 𝒰 c) : SmallChain R 𝒰 (L c) := by
  intro τ hτ
  obtain ⟨σ, hσ, hτσ⟩ := support_linear_apply_subset R L c hτ
  exact (hc σ hσ).mono (hL σ τ hτσ)

theorem smallChain_singSd {𝒰 : Set (Set X)} {k : ℕ} {c : C(topSimplex k, X) →₀ R}
    (hc : SmallChain R 𝒰 c) : SmallChain R 𝒰 (singSd R k c) :=
  smallChain_map R _ (fun σ _ hτ => range_subset_of_mem_singSd R σ hτ) hc

theorem smallChain_singT {𝒰 : Set (Set X)} {k : ℕ} {c : C(topSimplex k, X) →₀ R}
    (hc : SmallChain R 𝒰 c) : SmallChain R 𝒰 (singT R k c) :=
  smallChain_map R _ (fun σ _ hτ => range_subset_of_mem_singT R σ hτ) hc

theorem smallChain_singBd {𝒰 : Set (Set X)} {k : ℕ} {c : C(topSimplex (k + 1), X) →₀ R}
    (hc : SmallChain R 𝒰 c) : SmallChain R 𝒰 (singBd R X k c) :=
  smallChain_map R _ (fun σ _ hτ => range_subset_of_mem_singBd R σ hτ) hc

/-! ### Iterated subdivision as a linear map -/

/-- The `N`-fold subdivision, as a linear map. -/
noncomputable def singSdPow (k : ℕ) :
    ℕ → ((C(topSimplex k, X) →₀ R) →ₗ[R] (C(topSimplex k, X) →₀ R))
  | 0 => LinearMap.id
  | (N + 1) => (singSd R k).comp (singSdPow k N)

theorem singSdPow_zero {k : ℕ} (c : C(topSimplex k, X) →₀ R) : singSdPow R k 0 c = c := rfl

theorem singSdPow_succ {k N : ℕ} (c : C(topSimplex k, X) →₀ R) :
    singSdPow R k (N + 1) c = singSd R k (singSdPow R k N c) := rfl

theorem singSdPow_apply {k : ℕ} (N : ℕ) (c : C(topSimplex k, X) →₀ R) :
    singSdPow R k N c = (singSd R (X := X) k)^[N] c := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih =>
    rw [singSdPow_succ, ih, ← Function.iterate_succ_apply' (singSd R (X := X) k)]

theorem singSdPow_add {k : ℕ} (m n : ℕ) (c : C(topSimplex k, X) →₀ R) :
    singSdPow R k (m + n) c = singSdPow R k m (singSdPow R k n c) := by
  rw [singSdPow_apply, singSdPow_apply, singSdPow_apply, Function.iterate_add_apply]

theorem smallChain_singSdPow {𝒰 : Set (Set X)} {k : ℕ} (N : ℕ) {c : C(topSimplex k, X) →₀ R}
    (hc : SmallChain R 𝒰 c) : SmallChain R 𝒰 (singSdPow R k N c) := by
  induction N with
  | zero => exact hc
  | succ N ih => rw [singSdPow_succ]; exact smallChain_singSd R ih

/-- **Every chain becomes small after finitely many subdivisions.** -/
theorem exists_singSdPow_small (𝒰 : Set (Set X)) (hopen : ∀ U ∈ 𝒰, IsOpen U)
    (hcover : (Set.univ : Set X) ⊆ ⋃₀ 𝒰) {k : ℕ} (c : C(topSimplex k, X) →₀ R) :
    ∃ N : ℕ, SmallChain R 𝒰 (singSdPow R k N c) := by
  classical
  choose f hf using fun σ : C(topSimplex k, X) => exists_iterate_small R 𝒰 hopen hcover σ
  refine ⟨c.support.sup f, fun τ hτ => ?_⟩
  obtain ⟨σ, hσ, hτσ⟩ := support_linear_apply_subset R (singSdPow R k (c.support.sup f)) c hτ
  have hle : f σ ≤ c.support.sup f := Finset.le_sup hσ
  have hsplit : c.support.sup f = (c.support.sup f - f σ) + f σ := by omega
  have hbase : SmallChain R 𝒰 (singSdPow R k (f σ) (Finsupp.single σ (1 : R))) := by
    intro ρ hρ
    rw [singSdPow_apply] at hρ
    exact hf σ ρ hρ
  have := smallChain_singSdPow R (𝒰 := 𝒰) (c.support.sup f - f σ) hbase
  rw [← singSdPow_add] at this
  rw [← hsplit] at this
  exact this τ hτσ

end GaloisForLFunctions.HTGeometry
