import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Published recurrence-packing frontier

Formalization of the metric-packing core of Proposition 1 in Kotowski--Oszmaniec,
"Tight bounds on recurrence time in closed quantum systems" (arXiv:2601.10409v3, 2026).

The paper uses the weak convention that distinct points in an `ε`-packing have distance at least
`ε`.  `ClosedPackingBound` records that convention literally.  The first theorem is the discrete
orbit statement used in the published proof.  The second specializes it to a one-parameter
metric-invariant flow and gives the stated `T * N` deadline; setting `T` to the exit time recovers
the paper's Proposition 1.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Paper-exact weak packing convention: every finite set whose distinct points are at least
`ε` apart has at most `N` elements. -/
def ClosedPackingBound {X : Type*} [PseudoMetricSpace X]
    (ε : ℝ) (N : ℕ) : Prop :=
  ∀ C : Finset X,
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε ≤ dist x y) → C.card ≤ N

/-- Kotowski--Oszmaniec (2026), Proposition 1, discrete packing core. -/
theorem published2026_recurrence_packing_frontier
    {X : Type*} [PseudoMetricSpace X]
    (orbit : ℕ → X)
    (hshift : ∀ i j k : ℕ,
      dist (orbit (i + k)) (orbit (j + k)) =
        dist (orbit i) (orbit j))
    {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (hpack : ClosedPackingBound (X := X) ε N) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧
      dist (orbit 0) (orbit k) < ε := by
  classical
  by_contra hreturn
  push Not at hreturn
  let f : Fin (N + 1) → X := fun i => orbit i.1
  have hsep :
      ∀ i j : Fin (N + 1), i ≠ j → ε ≤ dist (f i) (f j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hkpos : 1 ≤ j.1 - i.1 := by omega
      have hkle : j.1 - i.1 ≤ N := by omega
      have hret := hreturn (j.1 - i.1) hkpos hkle
      have hstationary := hshift 0 (j.1 - i.1) i.1
      rw [Nat.zero_add, Nat.sub_add_cancel (Nat.le_of_lt hijlt)] at hstationary
      exact hstationary.symm ▸ hret
    · have hkpos : 1 ≤ i.1 - j.1 := by omega
      have hkle : i.1 - j.1 ≤ N := by omega
      have hret := hreturn (i.1 - j.1) hkpos hkle
      have hstationary := hshift 0 (i.1 - j.1) j.1
      rw [Nat.zero_add, Nat.sub_add_cancel (Nat.le_of_lt hjilt)] at hstationary
      rw [dist_comm]
      exact hstationary.symm ▸ hret
  have hfinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hpositive := hsep i j hne
    rw [hij, dist_self] at hpositive
    linarith
  let C : Finset X := Finset.univ.image f
  have hCcard : C.card = N + 1 := by
    dsimp [C]
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ,
      Fintype.card_fin]
  have hCsep :
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε ≤ dist x y := by
    intro x hx y hy hxy
    simp only [C, Finset.mem_image] at hx hy
    obtain ⟨i, _, rfl⟩ := hx
    obtain ⟨j, _, rfl⟩ := hy
    exact hsep i j (fun hij => hxy (congrArg f hij))
  have := hpack C hCsep
  rw [hCcard] at this
  omega

/-- Kotowski--Oszmaniec (2026), Proposition 1, in one-parameter-flow form.  Taking `T` to be the
exit time gives their bound `t_rec ≤ T * N_pack`. -/
theorem published2026_flow_recurrence_packing_frontier
    {X : Type*} [PseudoMetricSpace X]
    (flow : ℝ → X)
    (hshift : ∀ s t u : ℝ,
      dist (flow (s + u)) (flow (t + u)) =
        dist (flow s) (flow t))
    {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (N : ℕ)
    (hpack : ClosedPackingBound (X := X) ε N) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧
      dist (flow 0) (flow (k * T)) < ε ∧
      T ≤ k * T ∧ k * T ≤ N * T := by
  let orbit : ℕ → X := fun k => flow (k * T)
  have horbitShift : ∀ i j k : ℕ,
      dist (orbit (i + k)) (orbit (j + k)) =
        dist (orbit i) (orbit j) := by
    intro i j k
    dsimp [orbit]
    simpa [Nat.cast_add, add_mul] using
      hshift ((i : ℝ) * T) ((j : ℝ) * T) ((k : ℝ) * T)
  obtain ⟨k, hk1, hkN, hreturn⟩ :=
    published2026_recurrence_packing_frontier
      orbit horbitShift hε N hpack
  refine ⟨k, hk1, hkN, ?_, ?_, ?_⟩
  · simpa [orbit] using hreturn
  · have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    simpa using mul_le_mul_of_nonneg_right hk1R hT.le
  · have hkNR : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
    exact mul_le_mul_of_nonneg_right hkNR hT.le

end GaloisForLFunctions.HTGeometry
