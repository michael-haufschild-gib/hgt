import GaloisForLFunctions.HTGeometry.ObserverFieldEquation
import Mathlib.Algebra.Order.Chebyshev

/-!
# Tree independence of the observer holonomy gap

Two spanning-tree gauges of the same observer graph have the same exact root values, and two
finite generating sets of the same holonomy group have mutually bounded defect sums.  Hence the
kernel and the positivity of the transverse gap do not depend on the chosen gauge, although the
numerical constant does.

* `rootSolutionSet_tree_independent` : the exact root values are gauge independent;
* `defectSumSq_le_of_closure` : the squared defect sums of two finite generating sets bound each
  other up to positive constants.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-! ## Gauge independence of the exact root values -/

section TreeIndependence

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} {H : V → Type*}
  [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace 𝕜 (H v)] {o : V} {C C' : Type*}

/-- The based extension of a root value along a tree gauge. -/
noncomputable def basedExtension (T : TreeGauge 𝕜 H o) (z : H o) : ∀ v, H v :=
  fun v => T.A v z + T.a v

theorem basedExtension_root (T : TreeGauge 𝕜 H o) (z : H o) : basedExtension T z o = z := by
  rw [basedExtension, T.A_root, T.a_root, add_zero]

theorem basedExtension_isBased (T : TreeGauge 𝕜 H o) (z : H o) :
    T.IsBased (basedExtension T z) := by
  intro v
  rw [basedExtension, basedExtension_root]

/-- The exact root values of a tree/chord splitting. -/
def rootSolutionSet (T : TreeGauge 𝕜 H o) (K : ChordData 𝕜 H C) : Set (H o) :=
  {z : H o | ∀ e : C, z - ChordData.holonomy T K e z = ChordData.current T K e}

theorem mem_rootSolutionSet_iff (T : TreeGauge 𝕜 H o) (K : ChordData 𝕜 H C) (z : H o) :
    z ∈ rootSolutionSet T K
      ↔ (T.IsTreeExact (basedExtension T z) ∧ K.IsChordExact (basedExtension T z)) := by
  rw [ChordData.isExact_iff, rootSolutionSet, Set.mem_setOf_eq]
  constructor
  · intro hz
    refine ⟨basedExtension_isBased T z, fun e => ?_⟩
    rw [basedExtension_root]
    exact hz e
  · rintro ⟨-, hchord⟩ e
    have := hchord e
    rwa [basedExtension_root] at this

/-- **Proposition 7.1(1).**  Two spanning-tree gauges of the same observer graph have the same
exact root values. -/
theorem rootSolutionSet_tree_independent (T T' : TreeGauge 𝕜 H o)
    (K : ChordData 𝕜 H C) (K' : ChordData 𝕜 H C')
    (hsame : ∀ x : ∀ v, H v,
      (T.IsTreeExact x ∧ K.IsChordExact x) ↔ (T'.IsTreeExact x ∧ K'.IsChordExact x)) :
    rootSolutionSet T K = rootSolutionSet T' K' := by
  ext z
  constructor
  · intro hz
    have hex := (mem_rootSolutionSet_iff T K z).mp hz
    have hex' := (hsame _).mp hex
    obtain ⟨hbased', hchord'⟩ := (ChordData.isExact_iff T' K' _).mp hex'
    intro e
    have := hchord' e
    rwa [basedExtension_root] at this
  · intro hz
    have hex := (mem_rootSolutionSet_iff T' K' z).mp hz
    have hex' := (hsame _).mpr hex
    obtain ⟨hbased, hchord⟩ := (ChordData.isExact_iff T K _).mp hex'
    intro e
    have := hchord e
    rwa [basedExtension_root] at this

end TreeIndependence

/-! ## Generating sets and defect sums -/

section GeneratingSet

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {G : Type*} [Group G]

/-- The defect of a group element on a vector. -/
noncomputable def unitaryDefect (π : G →* (E ≃ₗᵢ[𝕜] E)) (g : G) (x : E) : ℝ :=
  ‖π g x - x‖

theorem unitaryDefect_one (π : G →* (E ≃ₗᵢ[𝕜] E)) (x : E) : unitaryDefect π 1 x = 0 := by
  rw [unitaryDefect, map_one]
  simp

theorem unitaryDefect_mul_le (π : G →* (E ≃ₗᵢ[𝕜] E)) (g h : G) (x : E) :
    unitaryDefect π (g * h) x ≤ unitaryDefect π g x + unitaryDefect π h x := by
  have hval : π (g * h) x = π g (π h x) := by
    rw [map_mul]
    rfl
  have hsplit : π g (π h x) - x = (π g (π h x) - π g x) + (π g x - x) := by abel
  have hiso : ‖π g (π h x) - π g x‖ = ‖π h x - x‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  rw [unitaryDefect, unitaryDefect, unitaryDefect, hval, hsplit]
  calc ‖(π g (π h x) - π g x) + (π g x - x)‖
      ≤ ‖π g (π h x) - π g x‖ + ‖π g x - x‖ := norm_add_le _ _
    _ = ‖π h x - x‖ + ‖π g x - x‖ := by rw [hiso]
    _ = ‖π g x - x‖ + ‖π h x - x‖ := by ring

theorem unitaryDefect_inv (π : G →* (E ≃ₗᵢ[𝕜] E)) (g : G) (x : E) :
    unitaryDefect π g⁻¹ x = unitaryDefect π g x := by
  have hval : π g (π g⁻¹ x) = x := by
    have h1 : π g (π g⁻¹ x) = π (g * g⁻¹) x := by rw [map_mul]; rfl
    rw [h1, mul_inv_cancel, map_one]
    rfl
  have hiso : ‖π g (π g⁻¹ x - x)‖ = ‖π g⁻¹ x - x‖ := LinearIsometryEquiv.norm_map _ _
  rw [unitaryDefect, unitaryDefect, ← hiso, map_sub, hval, norm_sub_rev]

/-- Telescoping: an element of the generated subgroup has defect bounded by a multiple of the
generating defect sum. -/
theorem exists_defect_bound (π : G →* (E ≃ₗᵢ[𝕜] E)) (S : Finset G) {g : G}
    (hg : g ∈ Subgroup.closure (S : Set G)) :
    ∃ m : ℕ, ∀ x : E, unitaryDefect π g x ≤ m * ∑ s ∈ S, unitaryDefect π s x := by
  classical
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    refine ⟨1, fun x => ?_⟩
    rw [Nat.cast_one, one_mul]
    refine Finset.single_le_sum (f := fun t => unitaryDefect π t x) (fun t _ => ?_) hs
    exact norm_nonneg _
  | one => exact ⟨0, fun x => by rw [unitaryDefect_one]; simp⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨ma, hma⟩ := iha
    obtain ⟨mb, hmb⟩ := ihb
    refine ⟨ma + mb, fun x => ?_⟩
    have h := unitaryDefect_mul_le π a b x
    have ha := hma x
    have hb := hmb x
    push_cast
    linarith
  | inv a _ iha =>
    obtain ⟨m, hm⟩ := iha
    refine ⟨m, fun x => ?_⟩
    rw [unitaryDefect_inv]
    exact hm x

/-- **Proposition 7.1(3).**  The squared defect sums of two finite generating sets bound each
other: the kernel and the positivity of the transverse gap are gauge invariants. -/
theorem defectSumSq_le_of_closure (π : G →* (E ≃ₗᵢ[𝕜] E)) (S S' : Finset G)
    (hS' : ∀ s' ∈ S', s' ∈ Subgroup.closure (S : Set G)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x : E,
      ∑ s' ∈ S', unitaryDefect π s' x ^ (2 : ℕ) ≤ κ * ∑ s ∈ S, unitaryDefect π s x ^ (2 : ℕ) := by
  classical
  choose m hm using fun (s' : S') => exists_defect_bound π S (hS' s'.1 s'.2)
  set M : ℕ := ∑ s' ∈ S'.attach, m s' with hM
  have hMbound : ∀ (s' : G) (hs' : s' ∈ S') (x : E),
      unitaryDefect π s' x ≤ M * ∑ s ∈ S, unitaryDefect π s x := by
    intro s' hs' x
    have hle := hm ⟨s', hs'⟩ x
    have hmle : (m ⟨s', hs'⟩ : ℝ) ≤ (M : ℝ) := by
      have : m ⟨s', hs'⟩ ≤ M := by
        rw [hM]
        exact Finset.single_le_sum (f := fun t : S' => m t) (fun t _ => Nat.zero_le _)
          (Finset.mem_attach _ _)
      exact_mod_cast this
    have hsumnn : (0 : ℝ) ≤ ∑ s ∈ S, unitaryDefect π s x :=
      Finset.sum_nonneg fun s _ => norm_nonneg _
    calc unitaryDefect π s' x ≤ (m ⟨s', hs'⟩ : ℝ) * ∑ s ∈ S, unitaryDefect π s x := hle
      _ ≤ (M : ℝ) * ∑ s ∈ S, unitaryDefect π s x :=
        mul_le_mul_of_nonneg_right hmle hsumnn
  refine ⟨(S'.card : ℝ) * (M : ℝ) ^ (2 : ℕ) * (S.card : ℝ) + 1, by positivity, fun x => ?_⟩
  have hcs : (∑ s ∈ S, unitaryDefect π s x) ^ (2 : ℕ)
      ≤ (S.card : ℝ) * ∑ s ∈ S, unitaryDefect π s x ^ (2 : ℕ) := sq_sum_le_card_mul_sum_sq
  have hterm : ∀ s' ∈ S', unitaryDefect π s' x ^ (2 : ℕ)
      ≤ (M : ℝ) ^ (2 : ℕ) * ((S.card : ℝ) * ∑ s ∈ S, unitaryDefect π s x ^ (2 : ℕ)) := by
    intro s' hs'
    have h1 := hMbound s' hs' x
    have h2 : unitaryDefect π s' x ^ (2 : ℕ)
        ≤ ((M : ℝ) * ∑ s ∈ S, unitaryDefect π s x) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc unitaryDefect π s' x ^ (2 : ℕ)
        ≤ ((M : ℝ) * ∑ s ∈ S, unitaryDefect π s x) ^ (2 : ℕ) := h2
      _ = (M : ℝ) ^ (2 : ℕ) * (∑ s ∈ S, unitaryDefect π s x) ^ (2 : ℕ) := by ring
      _ ≤ (M : ℝ) ^ (2 : ℕ) * ((S.card : ℝ) * ∑ s ∈ S, unitaryDefect π s x ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
  have hsum : ∑ s' ∈ S', unitaryDefect π s' x ^ (2 : ℕ)
      ≤ (S'.card : ℝ) * ((M : ℝ) ^ (2 : ℕ) * ((S.card : ℝ) * ∑ s ∈ S, unitaryDefect π s x ^ (2 : ℕ))) := by
    calc ∑ s' ∈ S', unitaryDefect π s' x ^ (2 : ℕ)
        ≤ ∑ _s' ∈ S', (M : ℝ) ^ (2 : ℕ) * ((S.card : ℝ) * ∑ s ∈ S, unitaryDefect π s x ^ (2 : ℕ)) :=
          Finset.sum_le_sum hterm
      _ = (S'.card : ℝ) * ((M : ℝ) ^ (2 : ℕ) * ((S.card : ℝ) * ∑ s ∈ S, unitaryDefect π s x ^ (2 : ℕ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hnn : (0 : ℝ) ≤ ∑ s ∈ S, unitaryDefect π s x ^ (2 : ℕ) :=
    Finset.sum_nonneg fun s _ => sq_nonneg _
  nlinarith [hsum, hnn]

end GeneratingSet

end GaloisForLFunctions.HTGeometry
