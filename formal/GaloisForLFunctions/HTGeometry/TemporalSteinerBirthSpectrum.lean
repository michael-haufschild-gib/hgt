import GaloisForLFunctions.HTGeometry.SteinerMobiusDuality

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-!
# Temporal Steiner birth spectrum

Connected interaction geometry carries a canonical projective capacity at every generator depth.
Its successive increments form the temporal Steiner birth spectrum. This file proves monotonicity,
the exact telescoping law, and saturation at the full connected-graph depth for every finite graph,
finite pointed local alphabet, and coefficient field.
-/

/-- Increasing generator depth preserves Steiner eligibility. -/
theorem SteinerEligible.mono
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r s : ℕ} {sites : Finset V} (hrs : r ≤ s)
    (h : SteinerEligible G r sites) :
    SteinerEligible G s sites := by
  obtain ⟨H, hconnected, hdepth, hsites⟩ := h
  exact ⟨H, hconnected, hdepth.trans hrs, hsites⟩

/-- The connected interaction-mode space is monotone in generator depth. -/
theorem anchoredSteinerInteractionSubmodule_mono
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) {r s : ℕ} (hrs : r ≤ s) :
    anchoredSteinerInteractionSubmodule
        (A := A) (base := base) (R := R) G r ≤
      anchoredSteinerInteractionSubmodule
        (A := A) (base := base) (R := R) G s := by
  classical
  apply Submodule.span_mono
  rintro f ⟨index, hindex, rfl⟩
  exact ⟨index, hindex.mono hrs, rfl⟩

/-- Projective interaction-mode capacity exposed by connected generators through depth `r`. -/
noncomputable def temporalSteinerCapacity
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) (r : ℕ) : ℕ :=
  Module.finrank R
      (anchoredSteinerInteractionSubmodule
        (A := A) (base := base) (R := R) G r) - 1

/-- Number of new projective interaction modes first made eligible at exact generator depth. -/
noncomputable def temporalSteinerBirthMultiplicity
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) : ℕ → ℕ
  | 0 => temporalSteinerCapacity (A := A) (base := base) (R := R) G 0
  | r + 1 =>
      temporalSteinerCapacity (A := A) (base := base) (R := R) G (r + 1) -
        temporalSteinerCapacity (A := A) (base := base) (R := R) G r

/-- Temporal Steiner capacity cannot decrease with generator depth. -/
theorem temporalSteinerCapacity_mono
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) {r s : ℕ} (hrs : r ≤ s) :
    temporalSteinerCapacity (A := A) (base := base) (R := R) G r ≤
      temporalSteinerCapacity (A := A) (base := base) (R := R) G s := by
  unfold temporalSteinerCapacity
  have hfin :
      Module.finrank R
          (anchoredSteinerInteractionSubmodule
            (A := A) (base := base) (R := R) G r) ≤
        Module.finrank R
          (anchoredSteinerInteractionSubmodule
            (A := A) (base := base) (R := R) G s) :=
    Submodule.finrank_mono (anchoredSteinerInteractionSubmodule_mono G hrs)
  omega

/-- **Exact temporal-birth sum law.** Birth multiplicities through depth `r` telescope exactly to
the projective connected-interaction capacity at that depth. -/
theorem sum_temporalSteinerBirthMultiplicity_eq_capacity
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    (G : SimpleGraph V) (r : ℕ) :
    ∑ i ∈ Finset.range (r + 1),
        temporalSteinerBirthMultiplicity
          (A := A) (base := base) (R := R) G i =
      temporalSteinerCapacity (A := A) (base := base) (R := R) G r := by
  induction r with
  | zero =>
      simp [temporalSteinerBirthMultiplicity]
  | succ r ih =>
      rw [show r + 1 + 1 = (r + 1) + 1 by omega]
      rw [Finset.sum_range_succ, ih]
      simp only [temporalSteinerBirthMultiplicity]
      exact Nat.add_sub_of_le (temporalSteinerCapacity_mono G (Nat.le_succ r))

/-- A canonical depth at which the full connected graph itself is an allowed cluster. -/
noncomputable def fullTemporalSteinerDepth
    {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.card (⊤ : G.Subgraph).coe.edgeSet

/-- Every site packet is Steiner-eligible at the full depth of a connected graph. -/
theorem steinerEligible_fullTemporalSteinerDepth
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.Connected) (sites : Finset V) :
    SteinerEligible G (fullTemporalSteinerDepth G) sites := by
  refine ⟨⊤, ?_, le_rfl, ?_⟩
  · exact SimpleGraph.Subgraph.connected_iff'.mpr
      (SimpleGraph.Subgraph.topIso.connected_iff.mpr hG)
  · simp

/-- At full connected-graph depth, every arbitrary-alphabet interaction mode is available. -/
theorem anchoredSteinerInteractionSubmodule_fullTemporalSteinerDepth_eq_top
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    {G : SimpleGraph V} (hG : G.Connected) :
    anchoredSteinerInteractionSubmodule
        (A := A) (base := base) (R := R) G
          (fullTemporalSteinerDepth G) =
      ⊤ := by
  apply top_unique
  intro f hf
  rw [mem_anchoredSteinerInteractionSubmodule_iff]
  intro index hindex
  exact (hindex (steinerEligible_fullTemporalSteinerDepth hG _)).elim

/-- The pointed copy of a local alphabet is equivalent to the original alphabet. -/
def anchoredValueEquiv
    {A : Type*} {base : A} : AnchoredValue A base ≃ A where
  toFun := AnchoredValue.val
  invFun := AnchoredValue.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- Full connected-graph capacity is the complete projective configuration dimension. -/
theorem temporalSteinerCapacity_fullTemporalSteinerDepth
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    {G : SimpleGraph V} (hG : G.Connected) :
    temporalSteinerCapacity
        (A := A) (base := base) (R := R) G
          (fullTemporalSteinerDepth G) =
      Fintype.card A ^ Fintype.card V - 1 := by
  rw [temporalSteinerCapacity,
    anchoredSteinerInteractionSubmodule_fullTemporalSteinerDepth_eq_top hG]
  rw [finrank_top]
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun]
  congr 2
  exact Fintype.card_congr anchoredValueEquiv

/-- **Universal temporal-birth conservation law.** On every finite connected interaction graph,
the sum of all Steiner birth multiplicities is exactly the complete projective configuration
dimension. -/
theorem sum_temporalSteinerBirthMultiplicity_full
    {V A R : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [DecidableEq A] [Field R] {base : A}
    {G : SimpleGraph V} (hG : G.Connected) :
    ∑ i ∈ Finset.range (fullTemporalSteinerDepth G + 1),
        temporalSteinerBirthMultiplicity
          (A := A) (base := base) (R := R) G i =
      Fintype.card A ^ Fintype.card V - 1 := by
  rw [sum_temporalSteinerBirthMultiplicity_eq_capacity,
    temporalSteinerCapacity_fullTemporalSteinerDepth hG]

end GaloisForLFunctions.HTGeometry
