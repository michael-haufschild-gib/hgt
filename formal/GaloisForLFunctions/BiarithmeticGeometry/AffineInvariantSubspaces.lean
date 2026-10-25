import GaloisForLFunctions.BiarithmeticGeometry.HorizonBoundaryCalculus
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp

/-!
# The submodules of the natural finite affine action

The absorbing successor is a single nilpotent Jordan block. Every invariant subspace is
therefore a coordinate tail. The full affine action preserves exactly the same chain;
its scalar common commutant coexists with these proper subrepresentations.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Rows whose first `m` coordinates vanish. -/
def horizonTail (N m : ℕ) : Submodule ℝ (HorizonSpace N) where
  carrier := {v | ∀ i : Fin (N + 1), i.val < m → v i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro v w hv hw i hi
    change v i + w i = 0
    rw [hv i hi, hw i hi, add_zero]
  smul_mem' := by
    intro c v hv i hi
    change c * v i = 0
    rw [hv i hi, mul_zero]

theorem horizonCell_mem_tail_iff (N m : ℕ) (j : Fin (N + 1)) :
    horizonCell N j.val ∈ horizonTail N m ↔ m ≤ j.val := by
  constructor
  · intro h
    by_contra hj
    have hz := h j (by omega)
    simp only [horizonCell, if_true] at hz
    exact one_ne_zero hz
  · intro hj i hi
    exact if_neg (by omega)

theorem horizonTail_antitone (N : ℕ) : Antitone (horizonTail N) := by
  intro m n hmn v hv i hi
  exact hv i (hi.trans_le hmn)

theorem horizonTail_end (N : ℕ) : horizonTail N (N + 1) = ⊥ := by
  apply le_antisymm
  · intro v hv
    change v = 0
    funext i
    exact hv i i.isLt
  · exact bot_le

/-- Every coordinate tail is preserved by the complete positive affine action. -/
theorem horizonTail_affine (N m : ℕ) (a : ℕ+) (b : ℕ)
    (v : HorizonSpace N) (hv : v ∈ horizonTail N m) :
    horizonAffine N a b v ∈ horizonTail N m :=
  horizonAffine_preserves_tail N a b m v hv

/-- A shift reads the unique predecessor when it exists. -/
theorem horizonShift_apply (N b : ℕ) (v : HorizonSpace N) (i : Fin (N + 1)) :
    horizonAffine N 1 b v i = if h : b ≤ i.val then v ⟨i.val - b, by omega⟩ else 0 := by
  classical
  rw [horizonAffine_apply]
  simp only [PNat.val_ofNat, one_mul]
  by_cases hi : b ≤ i.val
  · rw [dif_pos hi, sum_eq_single ⟨i.val - b, by omega⟩]
    · rw [if_pos (by change i.val = i.val - b + b; omega), mul_one]
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro he
      apply hj
      apply Fin.ext
      dsimp
      omega
    · exact fun h => False.elim (h (mem_univ _))
  · rw [dif_neg hi]
    apply sum_eq_zero
    intro j _
    rw [if_neg (by omega), mul_zero]

/-- Successor stability propagates to every nonnegative shift. -/
theorem horizon_successor_stable_shifts (N : ℕ) (W : Submodule ℝ (HorizonSpace N))
    (hW : ∀ v ∈ W, horizonAffine N 1 1 v ∈ W) :
    ∀ b : ℕ, ∀ v ∈ W, horizonAffine N 1 b v ∈ W := by
  intro b
  induction b with
  | zero =>
    intro v hv
    rwa [horizonAffine_one_zero, LinearMap.id_apply]
  | succ b ih =>
    intro v hv
    have h := hW _ (ih v hv)
    have he := congrArg (fun L : HorizonSpace N →ₗ[ℝ] HorizonSpace N => L v)
      (horizonAffine_comp N 1 1 1 b)
    simp only [LinearMap.comp_apply, PNat.val_ofNat, one_mul, mul_one] at he
    rw [← he]
    exact h

/-- The successor-invariant subspaces are exactly the coordinate tails. -/
theorem horizon_successor_submodules (N : ℕ) (W : Submodule ℝ (HorizonSpace N)) :
    (∀ v ∈ W, horizonAffine N 1 1 v ∈ W) ↔
      ∃ m : Fin (N + 2), W = horizonTail N m.val := by
  classical
  constructor
  · intro hW
    by_cases hex : ∃ m : ℕ, ∃ hm : m < N + 1,
        ∃ v ∈ W, v ⟨m, hm⟩ ≠ 0
    · let m := Nat.find hex
      obtain ⟨hm, v, hv, hvm⟩ := Nat.find_spec hex
      have hbelow : ∀ w ∈ W, ∀ i : Fin (N + 1), i.val < m → w i = 0 := by
        intro w hw i hi
        by_contra hz
        have hmin : m ≤ i.val := Nat.find_min' hex ⟨i.isLt, w, hw, hz⟩
        omega
      have hcells : ∀ r : ℕ, ∀ j : Fin (N + 1), N - j.val = r → m ≤ j.val →
          horizonCell N j.val ∈ W := by
        intro r
        induction r using Nat.strong_induction_on with
        | h r ih =>
          intro j hj hmj
          let w := horizonAffine N 1 (j.val - m) v
          have hw : w ∈ W := horizon_successor_stable_shifts N W hW _ v hv
          have hwbelow : ∀ i : Fin (N + 1), i.val < j.val → w i = 0 := by
            intro i hi
            dsimp [w]
            rw [horizonShift_apply]
            split_ifs with hbi
            · exact hbelow v hv _ (by change i.val - (j.val - m) < m; omega)
            · rfl
          have hwj : w j = v ⟨m, hm⟩ := by
            dsimp [w]
            rw [horizonShift_apply, dif_pos (Nat.sub_le _ _)]
            congr 1
            apply Fin.ext
            dsimp
            omega
          have hhigh : ∀ i : Fin (N + 1), j.val < i.val → horizonCell N i.val ∈ W := by
            intro i hi
            exact ih (N - i.val) (by omega) i rfl (by omega)
          have hsum : (∑ i : Fin (N + 1),
              if j.val < i.val then w i • horizonCell N i.val else 0) ∈ W := by
            apply W.sum_mem
            intro i _
            split_ifs with hi
            · exact W.smul_mem _ (hhigh i hi)
            · exact W.zero_mem
          have hsplit : w = w j • horizonCell N j.val +
              ∑ i : Fin (N + 1), if j.val < i.val then w i • horizonCell N i.val else 0 := by
            calc
              w = ∑ i : Fin (N + 1), w i • horizonCell N i.val := (sum_horizonCell N w).symm
              _ = ∑ i : Fin (N + 1),
                  ((if i = j then w j • horizonCell N j.val else 0) +
                    (if j.val < i.val then w i • horizonCell N i.val else 0)) := by
                apply sum_congr rfl
                intro i _
                by_cases hij : i = j
                · subst i
                  simp only [if_true, lt_self_iff_false, if_false, add_zero]
                · rw [if_neg hij]
                  by_cases hji : j.val < i.val
                  · rw [if_pos hji, zero_add]
                  · rw [if_neg hji, add_zero, hwbelow i (by
                      have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
                      omega), zero_smul]
              _ = _ := by
                rw [sum_add_distrib]
                simp only [sum_ite_eq', mem_univ, if_true]
          have hlead : w j • horizonCell N j.val ∈ W := by
            have h := W.sub_mem hw hsum
            have he := congrArg (fun z : HorizonSpace N => z -
              ∑ i : Fin (N + 1), if j.val < i.val then w i • horizonCell N i.val else 0) hsplit
            simp only [add_sub_cancel_right] at he
            rwa [he] at h
          have hnz : w j ≠ 0 := by rw [hwj]; exact hvm
          have h := W.smul_mem (w j)⁻¹ hlead
          simpa only [smul_smul, inv_mul_cancel₀ hnz, one_smul] using h
      refine ⟨⟨m, by omega⟩, le_antisymm (fun w hw => hbelow w hw) ?_⟩
      intro w hw
      rw [← sum_horizonCell N w]
      apply W.sum_mem
      intro i _
      by_cases hi : m ≤ i.val
      · exact W.smul_mem _ (hcells (N - i.val) i rfl hi)
      · rw [hw i (by change i.val < m; omega), zero_smul]
        exact W.zero_mem
    · refine ⟨⟨N + 1, by omega⟩, ?_⟩
      rw [horizonTail_end]
      apply le_antisymm
      · intro v hv
        change v = 0
        funext i
        by_contra hi
        exact hex ⟨i.val, i.isLt, v, hv, hi⟩
      · exact bot_le
  · rintro ⟨m, rfl⟩
    exact fun v hv => horizonTail_affine N m.val 1 1 v hv

/-- Adding every dilation leaves the successor's submodule lattice unchanged. -/
theorem horizon_affine_submodules (N : ℕ) (W : Submodule ℝ (HorizonSpace N)) :
    (∀ (a : ℕ+) (b : ℕ), ∀ v ∈ W, horizonAffine N a b v ∈ W) ↔
      ∃ m : Fin (N + 2), W = horizonTail N m.val := by
  constructor
  · intro h
    exact (horizon_successor_submodules N W).mp (h 1 1)
  · rintro ⟨m, rfl⟩ a b v hv
    exact horizonTail_affine N m.val a b v hv

/-- Distinct thresholds give distinct subrepresentations, including the zero tail. -/
theorem horizonTail_injective (N : ℕ) :
    Function.Injective (fun m : Fin (N + 2) => horizonTail N m.val) := by
  intro m n h
  change horizonTail N m.val = horizonTail N n.val at h
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hmn | hnm
  · have hm : m.val < N + 1 := by omega
    have hc := (horizonCell_mem_tail_iff N m.val ⟨m.val, hm⟩).mpr le_rfl
    rw [h] at hc
    have hn := (horizonCell_mem_tail_iff N n.val ⟨m.val, hm⟩).mp hc
    change n.val ≤ m.val at hn
    omega
  · have hn : n.val < N + 1 := by omega
    have hc := (horizonCell_mem_tail_iff N n.val ⟨n.val, hn⟩).mpr le_rfl
    rw [← h] at hc
    have hm := (horizonCell_mem_tail_iff N m.val ⟨n.val, hn⟩).mp hc
    change m.val ≤ n.val at hm
    omega

/-- The threshold is a complete finite coordinate for the invariant-subspace lattice. -/
def horizonInvariantSubspaceEquiv (N : ℕ) :
    Fin (N + 2) ≃ {W : Submodule ℝ (HorizonSpace N) //
      ∀ v ∈ W, horizonAffine N 1 1 v ∈ W} :=
  Equiv.ofBijective
    (fun m => ⟨horizonTail N m.val,
      fun v hv => horizonTail_affine N m.val 1 1 v hv⟩)
    ⟨fun m n h => horizonTail_injective N (congrArg Subtype.val h), by
      intro W
      obtain ⟨m, hm⟩ := (horizon_successor_submodules N W.val).mp W.property
      exact ⟨m, Subtype.ext hm.symm⟩⟩

/-- There are exactly `N+2` invariant subspaces, including zero and the whole horizon. -/
theorem card_horizonInvariantSubspaces (N : ℕ) :
    Nat.card {W : Submodule ℝ (HorizonSpace N) //
      ∀ v ∈ W, horizonAffine N 1 1 v ∈ W} = N + 2 := by
  rw [← Nat.card_congr (horizonInvariantSubspaceEquiv N), Nat.card_fin]

/-- Any two invariant subspaces are comparable. -/
theorem horizon_invariant_submodules_chain (N : ℕ) (W Z : Submodule ℝ (HorizonSpace N))
    (hW : ∀ v ∈ W, horizonAffine N 1 1 v ∈ W)
    (hZ : ∀ v ∈ Z, horizonAffine N 1 1 v ∈ Z) : W ≤ Z ∨ Z ≤ W := by
  obtain ⟨m, rfl⟩ := (horizon_successor_submodules N W).mp hW
  obtain ⟨n, rfl⟩ := (horizon_successor_submodules N Z).mp hZ
  rcases le_total m.val n.val with h | h
  · exact Or.inr (horizonTail_antitone N h)
  · exact Or.inl (horizonTail_antitone N h)

/-- Two invariant summands with zero intersection cannot both be nonzero. -/
theorem horizon_affine_indecomposable (N : ℕ) (W Z : Submodule ℝ (HorizonSpace N))
    (hW : ∀ v ∈ W, horizonAffine N 1 1 v ∈ W)
    (hZ : ∀ v ∈ Z, horizonAffine N 1 1 v ∈ Z) :
    W ⊓ Z = ⊥ → W = ⊥ ∨ Z = ⊥ := by
  intro hi
  rcases horizon_invariant_submodules_chain N W Z hW hZ with h | h
  · exact Or.inl ((inf_eq_left.mpr h).symm.trans hi)
  · exact Or.inr ((inf_eq_right.mpr h).symm.trans hi)

end GaloisForLFunctions.BiarithmeticGeometry
