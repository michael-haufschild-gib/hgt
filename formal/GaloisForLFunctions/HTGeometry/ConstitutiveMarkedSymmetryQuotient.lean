import Mathlib

/-!
# Marked-symmetry experiment quotient, recurrence, and lift

A compact group `H` acts on a space of laws.  A passive source law is invariant under all of `H`,
so nothing passive sees the group; a marked intervention law `ν` has stabilizer `K`, and the exact
experiment phase space is the homogeneous quotient `H ⧸ K`.

* `smul_eq_smul_iff_mem_stabilizer` and `markedResponse` — two transformations have the same marked
  response exactly when they lie in the same right `K`-coset, so the response descends to an
  injection of `H ⧸ K`, and `markedResponse_isClosedEmbedding` upgrades it to an embedding because
  `H ⧸ K` is compact and the law space is Hausdorff;
* `oneParameter_recurrence` — a continuous one-parameter subgroup of a compact group returns to
  every neighbourhood of the identity at arbitrarily large times, and
  `oneParameter_periodic` gives exact periodicity when it meets `K`;
* `character_norm_one` — a unitary character has constant positive modulus, so positive character
  data cannot carry phase history.
-/

namespace GaloisForLFunctions.HTGeometry

open Topology Pointwise

section ExperimentQuotient

variable {H : Type*} [Group H] {P : Type*} [MulAction H P]

/-- **Two transformations have the same marked response exactly on a right coset of the
stabilizer.** -/
theorem smul_eq_smul_iff_mem_stabilizer (ν : P) (g h : H) :
    g • ν = h • ν ↔ h⁻¹ * g ∈ MulAction.stabilizer H ν := by
  rw [MulAction.mem_stabilizer_iff, mul_smul]
  constructor
  · intro hgh
    rw [hgh, ← mul_smul, inv_mul_cancel, one_smul]
  · intro hgh
    have := congrArg (fun x => h • x) hgh
    simpa [← mul_smul] using this

/-- **Passive invisibility.**  An invariant source law is unchanged by every transformation. -/
theorem passive_invisible {μ : P} (hμ : ∀ h : H, h • μ = μ) (h : H) : h • μ = μ := hμ h

variable [TopologicalSpace H] [TopologicalSpace P]

/-- The marked response map on the experiment quotient. -/
def markedResponse (ν : P) : H ⧸ MulAction.stabilizer H ν → P :=
  Quotient.lift (fun g : H => g • ν) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ MulAction.stabilizer H ν := QuotientGroup.leftRel_apply.mp hab
    exact ((smul_eq_smul_iff_mem_stabilizer ν b a).mpr hab').symm)

omit [TopologicalSpace H] [TopologicalSpace P] in
@[simp] theorem markedResponse_mk (ν : P) (g : H) :
    markedResponse ν (QuotientGroup.mk g : H ⧸ MulAction.stabilizer H ν) = g • ν := rfl

/-- **The marked response is injective on the experiment quotient.** -/
theorem markedResponse_injective (ν : P) :
    Function.Injective (markedResponse (H := H) ν) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | H g =>
    induction y using QuotientGroup.induction_on with
    | H h =>
      rw [markedResponse_mk, markedResponse_mk] at hxy
      exact QuotientGroup.eq.mpr (by
        have := (smul_eq_smul_iff_mem_stabilizer ν h g).mp hxy.symm
        simpa using this)

variable [ContinuousSMul H P]

theorem markedResponse_continuous (ν : P) : Continuous (markedResponse (H := H) ν) := by
  refine continuous_quot_lift _ ?_
  exact (continuous_id.smul continuous_const)

/-- **The experiment quotient embeds in the law space.**  For a compact group and a Hausdorff law
space the marked response is a closed embedding of `H ⧸ K`. -/
theorem markedResponse_isClosedEmbedding [CompactSpace H] [T2Space P] (ν : P) :
    Topology.IsClosedEmbedding (markedResponse (H := H) ν) :=
  (markedResponse_continuous ν).isClosedEmbedding (markedResponse_injective ν)

end ExperimentQuotient

section Recurrence

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem oneParameter_zero {γ : ℝ → H} (hhom : ∀ s t, γ (s + t) = γ s * γ t) : γ 0 = 1 := by
  have h := hhom 0 0
  rw [add_zero] at h
  have h2 : (γ 0)⁻¹ * γ 0 = (γ 0)⁻¹ * (γ 0 * γ 0) := by rw [← h]
  simpa using h2.symm

omit [TopologicalSpace H] [IsTopologicalGroup H] in
theorem oneParameter_sub {γ : ℝ → H} (hhom : ∀ s t, γ (s + t) = γ s * γ t) (a b : ℝ) :
    γ a * (γ b)⁻¹ = γ (a - b) := by
  have h := hhom (a - b) b
  rw [sub_add_cancel] at h
  rw [h]
  group

/-- **Recurrence of a one-parameter subgroup in a compact group.**  It returns to every
neighbourhood of the identity at arbitrarily large times. -/
theorem oneParameter_recurrence [CompactSpace H] {γ : ℝ → H} (_hcont : Continuous γ)
    (hhom : ∀ s t, γ (s + t) = γ s * γ t) {U : Set H} (hU : U ∈ 𝓝 (1 : H)) {M : ℝ} (hM : 0 < M) :
    ∃ t : ℝ, M ≤ t ∧ γ t ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ : ∃ W ∈ 𝓝 (1 : H), W * W ⊆ U := by
    obtain ⟨W, hW, hWU⟩ := exists_nhds_one_split hU
    exact ⟨W, hW, by rintro x ⟨a, ha, b, hb, rfl⟩; exact hWU a ha b hb⟩
  set V : Set H := W ∩ (fun x : H => x⁻¹) ⁻¹' W with hV
  have hVnhds : V ∈ 𝓝 (1 : H) := by
    refine Filter.inter_mem hW ?_
    have hc : ContinuousAt (fun x : H => x⁻¹) 1 := (continuous_inv (G := H)).continuousAt
    exact hc.preimage_mem_nhds (by simpa using hW)
  have hVU : ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ U := by
    intro a ha b hb
    exact hWU ⟨a, ha.1, b⁻¹, hb.2, rfl⟩
  -- an open cover of `H` by right translates of `V`
  set nbhd : H → Set H := fun g => (fun x : H => x * g⁻¹) ⁻¹' V with hnbhd
  have hnbhd_mem : ∀ g : H, nbhd g ∈ 𝓝 g := by
    intro g
    have hc : ContinuousAt (fun x : H => x * g⁻¹) g := (continuous_mul_const g⁻¹).continuousAt
    refine hc.preimage_mem_nhds ?_
    simpa using hVnhds
  obtain ⟨S, -, hS⟩ := isCompact_univ.elim_nhds_subcover nbhd (fun g _ => hnbhd_mem g)
  -- pigeonhole on the sample times `M, 2M, …`
  have hchoose : ∀ k : ℕ, ∃ g ∈ S, γ (M * k) ∈ nbhd g := by
    intro k
    have hmem : γ (M * k) ∈ ⋃ g ∈ S, nbhd g := hS (Set.mem_univ _)
    simpa using hmem
  choose f hfS hfmem using hchoose
  have hcard : S.card < (Finset.Icc 1 (S.card + 1)).card := by
    rw [Nat.card_Icc]
    omega
  obtain ⟨k₁, hk₁, k₂, hk₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := f) (fun k _ => hfS k)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨M * (k₂ - k₁ : ℕ), ?_, ?_⟩
    · have h1 : 1 ≤ (k₂ - k₁ : ℕ) := by omega
      have h1' : (1 : ℝ) ≤ ((k₂ - k₁ : ℕ) : ℝ) := by exact_mod_cast h1
      nlinarith [hM, h1']
    · have hsub : γ (M * (k₂ : ℕ)) * (γ (M * (k₁ : ℕ)))⁻¹ = γ (M * (k₂ - k₁ : ℕ)) := by
        rw [oneParameter_sub hhom]
        congr 1
        have : ((k₂ - k₁ : ℕ) : ℝ) = (k₂ : ℝ) - (k₁ : ℝ) := by
          have : k₁ ≤ k₂ := le_of_lt hlt
          push_cast [Nat.cast_sub this]
          ring
        rw [this]
        ring
      rw [← hsub]
      have e1 : γ (M * (k₂ : ℕ)) * (f k₂)⁻¹ ∈ V := hfmem k₂
      have e2 : γ (M * (k₁ : ℕ)) * (f k₁)⁻¹ ∈ V := hfmem k₁
      rw [heq] at e2
      have := hVU _ e1 _ e2
      have hrw : (γ (M * (k₂ : ℕ)) * (f k₂)⁻¹) * (γ (M * (k₁ : ℕ)) * (f k₂)⁻¹)⁻¹
          = γ (M * (k₂ : ℕ)) * (γ (M * (k₁ : ℕ)))⁻¹ := by group
      rwa [hrw] at this
  · refine ⟨M * (k₁ - k₂ : ℕ), ?_, ?_⟩
    · have h1 : 1 ≤ (k₁ - k₂ : ℕ) := by omega
      have h1' : (1 : ℝ) ≤ ((k₁ - k₂ : ℕ) : ℝ) := by exact_mod_cast h1
      nlinarith [hM, h1']
    · have hsub : γ (M * (k₁ : ℕ)) * (γ (M * (k₂ : ℕ)))⁻¹ = γ (M * (k₁ - k₂ : ℕ)) := by
        rw [oneParameter_sub hhom]
        congr 1
        have : ((k₁ - k₂ : ℕ) : ℝ) = (k₁ : ℝ) - (k₂ : ℝ) := by
          have : k₂ ≤ k₁ := le_of_lt hlt
          push_cast [Nat.cast_sub this]
          ring
        rw [this]
        ring
      rw [← hsub]
      have e1 : γ (M * (k₁ : ℕ)) * (f k₁)⁻¹ ∈ V := hfmem k₁
      have e2 : γ (M * (k₂ : ℕ)) * (f k₂)⁻¹ ∈ V := hfmem k₂
      rw [← heq] at e2
      have := hVU _ e1 _ e2
      have hrw : (γ (M * (k₁ : ℕ)) * (f k₁)⁻¹) * (γ (M * (k₂ : ℕ)) * (f k₁)⁻¹)⁻¹
          = γ (M * (k₁ : ℕ)) * (γ (M * (k₂ : ℕ)))⁻¹ := by group
      rwa [hrw] at this

omit [TopologicalSpace H] [IsTopologicalGroup H] in
/-- **Exact periodicity when the path meets the stabilizer.** -/
theorem oneParameter_periodic {P : Type*} [MulAction H P] {γ : ℝ → H}
    (hhom : ∀ s t, γ (s + t) = γ s * γ t) (ν : P) {T : ℝ}
    (hT : γ T ∈ MulAction.stabilizer H ν) (t : ℝ) :
    γ (t + T) • ν = γ t • ν := by
  rw [hhom, mul_smul, hT]

end Recurrence

section PositiveErasure

/-- **A unitary character has constant positive modulus.**  Positive character data therefore
cannot carry phase history. -/
theorem character_norm_one {H : Type*} [Group H] (χ : H →* Circle) (h : H) :
    ‖(χ h : ℂ)‖ = 1 := by
  simpa using (χ h).property

end PositiveErasure

end GaloisForLFunctions.HTGeometry
