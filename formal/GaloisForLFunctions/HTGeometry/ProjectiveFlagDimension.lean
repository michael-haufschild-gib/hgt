import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.Data.Finite.Perm

/-!
# The dimension of a chain of horizons

A chain of proper nonzero subspaces is measured by its members' dimensions, which strictly increase
along the chain and lie strictly between zero and the ambient dimension.  So such a chain has at most
`N - 1` members, and a maximal one has exactly that many: the simplex it spans has dimension `N - 2`.

This is the combinatorial half of the identification of the horizon complex with a spherical
building: an elementary horizon is a vertex, a strict chain of horizons is a simplex, and a complete
frame gives a top-dimensional simplex of dimension `N - 2`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Along a chain of subspaces the dimension determines the member.** -/
theorem finrank_injOn_of_chain (S : Finset (Submodule K V))
    (hchain : ∀ W ∈ S, ∀ W' ∈ S, W ≤ W' ∨ W' ≤ W) :
    Set.InjOn (fun W : Submodule K V => Module.finrank K W) (S : Set (Submodule K V)) := by
  intro W hW W' hW' heq
  simp only [Finset.mem_coe] at hW hW'
  have hrank : Module.finrank K W = Module.finrank K W' := heq
  rcases hchain W hW W' hW' with h | h
  · rcases lt_or_eq_of_le h with hlt | he
    · exact absurd hrank (Nat.ne_of_lt (Submodule.finrank_lt_finrank_of_lt hlt))
    · exact he
  · rcases lt_or_eq_of_le h with hlt | he
    · exact absurd hrank.symm (Nat.ne_of_lt (Submodule.finrank_lt_finrank_of_lt hlt))
    · exact he.symm

/-- **A chain of proper nonzero subspaces has at most `N - 1` members.**  Equivalently, the simplex
it spans in the horizon complex has dimension at most `N - 2`. -/
theorem card_le_finrank_sub_one (S : Finset (Submodule K V))
    (hchain : ∀ W ∈ S, ∀ W' ∈ S, W ≤ W' ∨ W' ≤ W)
    (hbot : ∀ W ∈ S, W ≠ ⊥) (htop : ∀ W ∈ S, W ≠ ⊤) :
    S.card ≤ Module.finrank K V - 1 := by
  classical
  have hmaps : Set.MapsTo (fun W : Submodule K V => Module.finrank K W)
      (S : Set (Submodule K V)) (Finset.Icc 1 (Module.finrank K V - 1) : Finset ℕ) := by
    intro W hW
    simp only [Finset.mem_coe] at hW
    have hlt : Module.finrank K W < Module.finrank K V := Submodule.finrank_lt (htop W hW)
    have hpos : Module.finrank K W ≠ 0 := by
      intro hcon
      exact hbot W hW (Submodule.finrank_eq_zero.1 hcon)
    simp only [Finset.coe_Icc, Set.mem_Icc]
    omega
  refine le_trans (Finset.card_le_card_of_injOn _ hmaps (finrank_injOn_of_chain S hchain)) ?_
  rw [Nat.card_Icc]
  omega

/-! ## The bound is attained -/

/-- **A complete frame gives a chain of exactly `N - 1` proper nonzero subspaces.**  The flag of a
basis, with its two trivial ends removed, is such a chain: it is strictly increasing, so its members
are distinct, and each lies strictly between the zero subspace and the whole space. -/
theorem exists_chain_card_eq_finrank_sub_one (hN : 0 < Module.finrank K V) :
    ∃ S : Finset (Submodule K V),
      S.card = Module.finrank K V - 1 ∧
      (∀ W ∈ S, ∀ W' ∈ S, W ≤ W' ∨ W' ≤ W) ∧
      (∀ W ∈ S, W ≠ ⊥) ∧ (∀ W ∈ S, W ≠ ⊤) := by
  classical
  set N := Module.finrank K V with hNdef
  set b := Module.finBasis K V with hb
  set f : Fin (N - 1) → Fin (N + 1) := fun i => ⟨(i : ℕ) + 1, by have := i.isLt; omega⟩ with hf
  have hfmono : StrictMono f := by
    intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    rw [Fin.lt_def]
    simp only [hf]
    omega
  have hinj : Function.Injective (fun i : Fin (N - 1) => b.flag (f i)) :=
    ((Module.Basis.flag_strictMono b).comp hfmono).injective
  refine ⟨Finset.image (fun i : Fin (N - 1) => b.flag (f i)) Finset.univ, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro W hW W' hW'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hW
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hW'
    rcases le_total (f i) (f j) with h | h
    · exact Or.inl (Module.Basis.flag_mono b h)
    · exact Or.inr (Module.Basis.flag_mono b h)
  · intro W hW
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hW
    have hlt : (0 : Fin (N + 1)) < f i := by
      rw [Fin.lt_def]
      simp only [hf, Fin.val_zero]
      omega
    have := Module.Basis.flag_strictMono b hlt
    rw [Module.Basis.flag_zero] at this
    exact fun hcon => absurd (hcon ▸ this) (lt_irrefl _)
  · intro W hW
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hW
    have hlt : f i < Fin.last N := by
      rw [Fin.lt_def]
      simp only [hf, Fin.val_last]
      have := i.isLt
      omega
    have := Module.Basis.flag_strictMono b hlt
    rw [Module.Basis.flag_last] at this
    exact fun hcon => absurd (hcon ▸ this) (lt_irrefl _)

/-- **The horizon simplices have dimension exactly `N - 2` at the top.**  The longest chain of proper
nonzero subspaces has exactly `N - 1` members. -/
theorem isGreatest_chain_card (hN : 0 < Module.finrank K V) :
    IsGreatest {k : ℕ | ∃ S : Finset (Submodule K V), S.card = k ∧
      (∀ W ∈ S, ∀ W' ∈ S, W ≤ W' ∨ W' ≤ W) ∧
      (∀ W ∈ S, W ≠ ⊥) ∧ (∀ W ∈ S, W ≠ ⊤)} (Module.finrank K V - 1) := by
  refine ⟨exists_chain_card_eq_finrank_sub_one hN, ?_⟩
  rintro k ⟨S, rfl, hchain, hbot, htop⟩
  exact card_le_finrank_sub_one S hchain hbot htop

/-! ## The projective action -/

omit [FiniteDimensional K V] in
/-- **A linear automorphism preserves the type of a vertex.** -/
theorem finrank_map_of_equiv (e : V ≃ₗ[K] V) (W : Submodule K V) :
    Module.finrank K (W.map (e : V →ₗ[K] V)) = Module.finrank K W :=
  LinearEquiv.finrank_map_eq e W

omit [FiniteDimensional K V] in
/-- **The action is injective on vertices.** -/
theorem map_equiv_injective (e : V ≃ₗ[K] V) :
    Function.Injective (fun W : Submodule K V => W.map (e : V →ₗ[K] V)) := by
  intro W W' h
  exact Submodule.map_injective_of_injective e.injective h

omit [FiniteDimensional K V] in
/-- **The action carries chains to chains of the same size**, so it acts on the horizon complex
simplicially. -/
theorem card_image_map_equiv (e : V ≃ₗ[K] V) (S : Finset (Submodule K V)) :
    (S.image (fun W => W.map (e : V →ₗ[K] V))).card = S.card :=
  Finset.card_image_of_injective _ (map_equiv_injective e)

/-- **Vertices of the same type form a single orbit.**  Two subspaces of the same dimension are
carried to one another by a linear automorphism, so the dimension is a complete invariant of a vertex
under the projective action: an elementary horizon of a given codimension is a vertex of one
type. -/
theorem exists_equiv_map_eq (W W' : Submodule K V)
    (h : Module.finrank K W = Module.finrank K W') :
    ∃ e : V ≃ₗ[K] V, W.map (e : V →ₗ[K] V) = W' := by
  classical
  obtain ⟨Wc, hWc⟩ := Submodule.exists_isCompl W
  obtain ⟨Wc', hWc'⟩ := Submodule.exists_isCompl W'
  have hsum : Module.finrank K W + Module.finrank K Wc = Module.finrank K V := by
    have := Submodule.finrank_sup_add_finrank_inf_eq W Wc
    rw [hWc.sup_eq_top, hWc.inf_eq_bot, finrank_bot K V, finrank_top K V] at this
    omega
  have hsum' : Module.finrank K W' + Module.finrank K Wc' = Module.finrank K V := by
    have := Submodule.finrank_sup_add_finrank_inf_eq W' Wc'
    rw [hWc'.sup_eq_top, hWc'.inf_eq_bot, finrank_bot K V, finrank_top K V] at this
    omega
  have hc : Module.finrank K Wc = Module.finrank K Wc' := by omega
  set e₁ := LinearEquiv.ofFinrankEq (R := K) W W' h with he₁
  set e₂ := LinearEquiv.ofFinrankEq (R := K) Wc Wc' hc with he₂
  set e := ((Submodule.prodEquivOfIsCompl W Wc hWc).symm.trans (LinearEquiv.prodCongr e₁ e₂)).trans
    (Submodule.prodEquivOfIsCompl W' Wc' hWc') with hedef
  refine ⟨e, ?_⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro x ⟨w, hw, rfl⟩
    have hx : (Submodule.prodEquivOfIsCompl W Wc hWc) (⟨w, hw⟩, 0) = w := by
      simp
    have hcomp : e ((Submodule.prodEquivOfIsCompl W Wc hWc) (⟨w, hw⟩, 0))
        = ((e₁ ⟨w, hw⟩ : W') : V) := by
      rw [hedef, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      simp
    rw [hx] at hcomp
    have hmem : ((e : V →ₗ[K] V) w) = ((e₁ ⟨w, hw⟩ : W') : V) := hcomp
    rw [hmem]
    exact (e₁ ⟨w, hw⟩).2
  · rw [LinearEquiv.finrank_map_eq, h]

/-! ## The apartment of a frame -/

omit [FiniteDimensional K V] in
/-- **An ordering of a frame is read off its flag.**  A basis vector lies in the flag of the reordered
basis exactly below the position the ordering gives it. -/
theorem mem_flag_reindex_iff {N : ℕ} (b : Module.Basis (Fin N) K V) (ρ : Equiv.Perm (Fin N))
    (j : Fin N) (k : Fin (N + 1)) :
    b j ∈ (b.reindex ρ).flag k ↔ (ρ j).castSucc < k := by
  have h := Module.Basis.self_mem_flag_iff (b.reindex ρ) (i := ρ j) (k := k)
  simpa using h

omit [FiniteDimensional K V] in
/-- **Distinct orderings of a frame give distinct complete flags.**  So the apartment of a frame
carries one top-dimensional simplex for each ordering of the frame. -/
theorem flag_reindex_injective {N : ℕ} (b : Module.Basis (Fin N) K V) :
    Function.Injective (fun σ : Equiv.Perm (Fin N) => (b.reindex σ).flag) := by
  intro σ τ h
  have h' : (b.reindex σ).flag = (b.reindex τ).flag := h
  refine Equiv.ext fun j => ?_
  have hσ := mem_flag_reindex_iff b σ j
  have hτ := mem_flag_reindex_iff b τ j
  have hiff : ∀ k : Fin (N + 1), (σ j).castSucc < k ↔ (τ j).castSucc < k := by
    intro k
    rw [← hσ k, ← hτ k, h']
  have h1 : (τ j).castSucc < (σ j).succ := (hiff (σ j).succ).1 Fin.castSucc_lt_succ
  have h2 : (σ j).castSucc < (τ j).succ := (hiff (τ j).succ).2 Fin.castSucc_lt_succ
  have h1' : τ j ≤ σ j := Fin.castSucc_lt_succ_iff.1 h1
  have h2' : σ j ≤ τ j := Fin.castSucc_lt_succ_iff.1 h2
  exact le_antisymm h2' h1'

omit [FiniteDimensional K V] in
/-- **An apartment has exactly `N!` complete flags.**  This is the Coxeter complex of the symmetric
group on the frame: a complete projective observer frame gives an apartment whose top-dimensional
simplices are its orderings. -/
theorem card_flags_of_frame {N : ℕ} (b : Module.Basis (Fin N) K V) :
    Nat.card (Set.range (fun σ : Equiv.Perm (Fin N) => (b.reindex σ).flag)) = Nat.factorial N := by
  classical
  rw [Nat.card_range_of_injective (flag_reindex_injective b), Nat.card_perm,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## Transport along an order-reversing injection -/

section Transport

variable {β : Type*} [PartialOrder β] [DecidableEq β]

omit [FiniteDimensional K V] in
/-- **An order-reversing injection carries a chain of horizons to a chain of the same size.**  This
is the passage from a strict chain of common-horizon fields to a flag of subspaces: the horizon
assignment is injective and order-reversing, so the two complexes have the same simplices. -/
theorem card_image_eq_and_chain (f : Submodule K V → β)
    (hanti : ∀ W W' : Submodule K V, W ≤ W' → f W' ≤ f W) (hinj : Function.Injective f)
    (S : Finset (Submodule K V)) (hchain : ∀ W ∈ S, ∀ W' ∈ S, W ≤ W' ∨ W' ≤ W) :
    (S.image f).card = S.card ∧ ∀ u ∈ S.image f, ∀ v ∈ S.image f, u ≤ v ∨ v ≤ u := by
  refine ⟨Finset.card_image_of_injective _ hinj, ?_⟩
  intro u hu v hv
  obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨W', hW', rfl⟩ := Finset.mem_image.1 hv
  rcases hchain W hW W' hW' with h | h
  · exact Or.inr (hanti W W' h)
  · exact Or.inl (hanti W' W h)

/-- **The transported horizon complex has simplices of dimension at most `N - 2`.** -/
theorem card_image_le_finrank_sub_one (f : Submodule K V → β)
    (hanti : ∀ W W' : Submodule K V, W ≤ W' → f W' ≤ f W) (hinj : Function.Injective f)
    (S : Finset (Submodule K V)) (hchain : ∀ W ∈ S, ∀ W' ∈ S, W ≤ W' ∨ W' ≤ W)
    (hbot : ∀ W ∈ S, W ≠ ⊥) (htop : ∀ W ∈ S, W ≠ ⊤) :
    (S.image f).card ≤ Module.finrank K V - 1 := by
  rw [(card_image_eq_and_chain f hanti hinj S hchain).1]
  exact card_le_finrank_sub_one S hchain hbot htop

/-- **And attains it.**  So the order complex of common-horizon fields has top simplices of dimension
exactly `N - 2`, as does the flag complex it is identified with. -/
theorem exists_image_chain_card_eq (f : Submodule K V → β)
    (hanti : ∀ W W' : Submodule K V, W ≤ W' → f W' ≤ f W) (hinj : Function.Injective f)
    (hN : 0 < Module.finrank K V) :
    ∃ T : Finset β, T.card = Module.finrank K V - 1 ∧
      (∀ u ∈ T, ∀ v ∈ T, u ≤ v ∨ v ≤ u) := by
  obtain ⟨S, hcard, hchain, -, -⟩ := exists_chain_card_eq_finrank_sub_one (K := K) (V := V) hN
  obtain ⟨himg, hchain'⟩ := card_image_eq_and_chain f hanti hinj S hchain
  exact ⟨S.image f, by rw [himg, hcard], hchain'⟩

end Transport

end GaloisForLFunctions.HTGeometry
