import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeHorizon
import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeModularGain

/-!
# The exchange horizon topology

The coherent framed subspace of the polarized exchange family takes exactly two values: the whole
frame at the trivial character and the permanent conormal line elsewhere.  Pulling back the Scott
topology of the subspace lattice therefore leaves a three-open Sierpinski topology on the parameter:
the empty set, the horizon locus, and everything.  All nonzero modular weights are topologically
indistinguishable.

Pulling back the finer provenance-exactness topology of the flag `(image, kernel)` of the exchange
differential gives the same three opens, but with the stronger meaning that the permanent line
consists of cycles at every parameter and of boundaries off the horizon.
-/

namespace RHTower

noncomputable section

open Set Topology TopologicalSpace GaloisForLFunctions.HTGeometry

variable {k : Type*} [Field k]

/-! ## Two-valued profiles and the Scott pullback -/

theorem eq_top_of_mem_of_mem {Z : Submodule k (Fin 2 → k)} (h0 : ![(1 : k), 0] ∈ Z)
    (h1 : ![(0 : k), 1] ∈ Z) : Z = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have hv : v = v 0 • ![(1 : k), 0] + v 1 • ![(0 : k), 1] := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  exact Z.add_mem (Z.smul_mem _ h0) (Z.smul_mem _ h1)

/-- The top subspace is Scott isolated in the subspace lattice of the plane. -/
theorem isOpen_scott_singleton_top :
    IsOpen[Topology.scott (Submodule k (Fin 2 → k)) univ]
      ({⊤} : Set (Submodule k (Fin 2 → k))) := by
  have hset : ({⊤} : Set (Submodule k (Fin 2 → k))) =
      {Z : Submodule k (Fin 2 → k) | ![(1 : k), 0] ∈ Z} ∩
        {Z : Submodule k (Fin 2 → k) | ![(0 : k), 1] ∈ Z} := by
    ext Z
    constructor
    · rintro rfl
      exact ⟨trivial, trivial⟩
    · rintro ⟨h0, h1⟩
      exact eq_top_of_mem_of_mem h0 h1
  rw [hset]
  letI : TopologicalSpace (Submodule k (Fin 2 → k)) :=
    Topology.scott (Submodule k (Fin 2 → k)) univ
  exact (isOpen_scott_Ici_span_singleton _).inter (isOpen_scott_Ici_span_singleton _)

/-- **Two-valued coherent profiles have a three-open initial Scott topology.** -/
theorem isOpen_induced_scott_iff {α : Type*} (κ : α → Submodule k (Fin 2 → k)) (S : Set α)
    (htop : ∀ a ∈ S, κ a = ⊤) (hline : ∀ a, a ∉ S → κ a = permanentLine k) (U : Set α) :
    IsOpen[induced κ (Topology.scott (Submodule k (Fin 2 → k)) univ)] U ↔
      U = ∅ ∨ U = S ∨ U = univ := by
  constructor
  · rintro ⟨W, hW, rfl⟩
    rw [isOpen_scott_submodule_iff] at hW
    obtain ⟨hUp, -⟩ := hW
    by_cases hTop : (⊤ : Submodule k (Fin 2 → k)) ∈ W
    · by_cases hLine : permanentLine k ∈ W
      · refine Or.inr (Or.inr ?_)
        refine eq_univ_of_forall fun a => ?_
        by_cases ha : a ∈ S
        · simpa [htop a ha] using hTop
        · simpa [hline a ha] using hLine
      · refine Or.inr (Or.inl ?_)
        ext a
        by_cases ha : a ∈ S
        · simp only [mem_preimage, htop a ha]
          exact ⟨fun _ => ha, fun _ => hTop⟩
        · simp only [mem_preimage, hline a ha]
          exact ⟨fun h => absurd h hLine, fun h => absurd h ha⟩
    · refine Or.inl ?_
      have hLine : permanentLine k ∉ W := fun h => hTop (hUp le_top h)
      ext a
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      by_cases ha : a ∈ S
      · rw [htop a ha]; exact hTop
      · rw [hline a ha]; exact hLine
  · rintro (rfl | rfl | rfl)
    · exact ⟨∅, isOpen_empty, by simp⟩
    · refine ⟨{⊤}, isOpen_scott_singleton_top, ?_⟩
      ext a
      simp only [mem_preimage, mem_singleton_iff]
      by_cases ha : a ∈ S
      · simp [htop a ha, ha]
      · simp only [hline a ha, ha, iff_false]
        exact (permanentLine_lt_top).ne
    · exact ⟨univ, isOpen_univ, by simp⟩

/-! ## The exchange horizon profile -/

theorem coherentKernel_modularGain_zero :
    coherentKernel (modularGain 0) = (⊤ : Submodule ℝ (Fin 2 → ℝ)) := by
  rw [(modularGain_eq_one_iff 0).2 rfl, coherentKernel_one]

theorem coherentKernel_modularGain_of_ne_zero {θ : ℝ} (h : θ ≠ 0) :
    coherentKernel (modularGain θ) = permanentLine ℝ :=
  coherentKernel_of_ne_one fun hc => h ((modularGain_eq_one_iff θ).1 hc)

/-- **The exchange horizon topology.**  The initial Scott topology of the coherent framed profile
`θ ↦ H θ` has exactly three opens, so all nonzero modular weights are indistinguishable. -/
theorem isOpen_exchangeHorizon_iff (U : Set ℝ) :
    IsOpen[induced (fun θ : ℝ => coherentKernel (modularGain θ))
      (Topology.scott (Submodule ℝ (Fin 2 → ℝ)) univ)] U ↔
      U = ∅ ∨ U = {0} ∨ U = univ := by
  refine isOpen_induced_scott_iff _ {0} ?_ ?_ U
  · rintro a rfl
    exact coherentKernel_modularGain_zero
  · intro a ha
    exact coherentKernel_modularGain_of_ne_zero (by simpa using ha)

/-- **The universal character horizon topology.**  On the full character set the initial Scott
topology of `χ ↦ H χ` has exactly three opens. -/
theorem isOpen_characterHorizon_iff (U : Set (ℕ+ →* kˣ)) :
    IsOpen[induced (fun χ : ℕ+ →* kˣ => coherentKernel χ)
      (Topology.scott (Submodule k (Fin 2 → k)) univ)] U ↔
      U = ∅ ∨ U = {1} ∨ U = univ := by
  refine isOpen_induced_scott_iff _ {1} ?_ ?_ U
  · rintro a rfl
    exact coherentKernel_one
  · intro a ha
    exact coherentKernel_of_ne_one (by simpa using ha)

/-! ## The provenance flag profile -/

/-- **The rank-one provenance horizon.**  Two-valued exchange flag profiles have a three-open
initial provenance-exactness topology. -/
theorem isOpen_induced_flag_iff {α : Type*} (φ : α → ExFlag k (Fin 2 → k)) (S : Set α)
    (hhor : ∀ a ∈ S, φ a = ⟨⊥, ⊤, le_top⟩)
    (hoff : ∀ a, a ∉ S → φ a = ⟨permanentLine k, permanentLine k, le_rfl⟩) (U : Set α) :
    IsOpen[induced φ ExFlag.instTopologicalSpace] U ↔ U = ∅ ∨ U = S ∨ U = univ := by
  set p₀ : ExFlag k (Fin 2 → k) := ⟨⊥, ⊤, le_top⟩ with hp₀
  set p₁ : ExFlag k (Fin 2 → k) := ⟨permanentLine k, permanentLine k, le_rfl⟩ with hp₁
  have hspec : p₀ ⤳ p₁ := ExFlag.specializes_iff.2 ⟨bot_le, le_top⟩
  constructor
  · rintro ⟨V, hV, rfl⟩
    by_cases hp0 : p₀ ∈ V
    · by_cases hp1 : p₁ ∈ V
      · refine Or.inr (Or.inr (eq_univ_of_forall fun a => ?_))
        by_cases ha : a ∈ S
        · simpa [hhor a ha] using hp0
        · simpa [hoff a ha] using hp1
      · refine Or.inr (Or.inl ?_)
        ext a
        by_cases ha : a ∈ S
        · simp only [mem_preimage, hhor a ha]
          exact ⟨fun _ => ha, fun _ => hp0⟩
        · simp only [mem_preimage, hoff a ha]
          exact ⟨fun h => absurd h hp1, fun h => absurd h ha⟩
    · refine Or.inl ?_
      have hp1 : p₁ ∉ V := fun h => hp0 (specializes_iff_forall_open.1 hspec V hV h)
      ext a
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      by_cases ha : a ∈ S
      · rw [hhor a ha]; exact hp0
      · rw [hoff a ha]; exact hp1
  · rintro (rfl | rfl | rfl)
    · exact ⟨∅, isOpen_empty, by simp⟩
    · refine ⟨ExFlag.survival ![(0 : k), 1], ExFlag.isOpen_survival _, ?_⟩
      have hnot : ![(0 : k), 1] ∉ permanentLine k := by
        rw [mem_permanentLine_iff]
        simp
      ext a
      simp only [mem_preimage]
      by_cases ha : a ∈ S
      · simp only [hhor a ha, ha, iff_true]
        exact ⟨trivial, by simp⟩
      · simp only [hoff a ha, ha, iff_false]
        exact fun hc => hnot hc.1
    · exact ⟨univ, isOpen_univ, by simp⟩

theorem exchangeFlag_modularGain_zero :
    exchangeFlag (modularGain 0) = ⟨⊥, ⊤, le_top⟩ :=
  exchangeFlag_of_eq_one (by rw [(modularGain_eq_one_iff 0).2 rfl]; rfl)

theorem exchangeFlag_modularGain_of_ne_zero {θ : ℝ} (h : θ ≠ 0) :
    exchangeFlag (modularGain θ) = ⟨permanentLine ℝ, permanentLine ℝ, le_rfl⟩ :=
  exchangeFlag_of_ne_one fun hc => h ((modularGain_two_eq_one_iff θ).1 hc)

/-- **The rank-one provenance-exactness horizon topology.**  The initial provenance topology of the
exchange flag profile has exactly three opens. -/
theorem isOpen_exchangeFlagHorizon_iff (U : Set ℝ) :
    IsOpen[induced (fun θ : ℝ => exchangeFlag (modularGain θ)) ExFlag.instTopologicalSpace] U ↔
      U = ∅ ∨ U = {0} ∨ U = univ := by
  refine isOpen_induced_flag_iff _ {0} ?_ ?_ U
  · rintro a rfl
    exact exchangeFlag_modularGain_zero
  · intro a ha
    exact exchangeFlag_modularGain_of_ne_zero (by simpa using ha)

end

end RHTower
