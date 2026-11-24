import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechTopColumns

/-! Appending weights to a Koszul column preserves exactness below its
first possible cohomology degree. In that degree the obstruction to
extension is the action of each appended weight on the old class. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι κ M : Type} [Field k] [LinearOrder ι] [Fintype ι]
  [LinearOrder κ] [Fintype κ] [AddCommGroup M] [Module k M]
  {P : Submodule k M} {w : ι ⊕ₗ κ → Module.End k M} {d n : ℤ}

local notation "C" => acx (fun _ => P) w
local notation "wR" => (fun j : κ => w (toLex (Sum.inr j)))
local notation "D" => acx (fun _ => P) wR

omit [Fintype ι] in
private theorem rightDegree_le_of_terms {c : Finset (ι ⊕ₗ κ) → M}
    (hc : c ∈ (C).C n) (hn : n ≤ d) : Lev rightIndices (· ≤ d) c := by
  intro s hs
  have hcard : (s.card : ℤ) ≠ n := by
    intro he
    have hle : ((s ∩ rightIndices).card : ℤ) ≤ s.card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : s ∩ rightIndices ⊆ s)
    exact hs (hle.trans (he.symm ▸ hn))
  exact (Submodule.mem_bot k).mp (by simpa only [if_neg hcard] using acx_mem_terms_iff.mp hc s)

/-- Below the first possible right cohomology degree every cycle is a
boundary. At that degree it suffices to test the restriction. -/
theorem appended_mem_boundary (hw : ∀ i j, Commute (w i) (w j))
    (hP : ∀ i, P ≤ P.comap (w i)) (hE : ∀ m < d, (D).Z m ≤ (D).B m)
    {c : Finset (ι ⊕ₗ κ) → M} (hc : c ∈ (C).Z n) (hn : n ≤ d)
    (hb : n = d → (fun J => c (uni ∅ J)) ∈ (D).B d) : c ∈ (C).B n := by
  refine boundary_of_top_columns (acx_isCx _ _ hw (fun _ i _ => hP i))
    (fun _ m hm => hE m hm) hc (rightDegree_le_of_terms hc.1 hn) ?_
  intro I hI
  have hI₀ : I.card = 0 := by omega
  have hn' : n = d := by omega
  obtain rfl := Finset.card_eq_zero.mp hI₀
  exact hb hn'

omit [Fintype ι] in
/-- Restricting to the old indices takes cycles to cycles. -/
theorem appended_restrict_mem_cycles {c : Finset (ι ⊕ₗ κ) → M}
    (hc : c ∈ (C).Z n) : (fun J => c (uni ∅ J)) ∈ (D).Z n := by
  exact rightColumn_top_mem_cycles hc (rightDegree_le_of_terms hc.1 (le_refl n)) ∅
    (by simp only [Finset.card_empty, Nat.cast_zero, sub_self])

/-- Lift a cycle of the old weights when application of each appended
weight gives a boundary in the old column. -/
theorem exists_cocycle_appending_weights
    (hw : ∀ i j, Commute (w i) (w j)) (hP : ∀ i, P ≤ P.comap (w i))
    (hE : ∀ m < d, (D).Z m ≤ (D).B m)
    {a : Finset κ → M} (ha : a ∈ (D).Z d)
    (hb : ∀ i : ι, (fun J => w (toLex (Sum.inl i)) (a J)) ∈ (D).B d) :
    ∃ c ∈ (C).Z d, ∀ J, c (uni ∅ J) = a J := by
  classical
  let b (s : Finset (ι ⊕ₗ κ)) := if lft s = ∅ then a (rgt s) else 0
  have hbu (I : Finset ι) (J : Finset κ) : b (uni I J) = if I = ∅ then a J else 0 := by
    simp only [b, lft_uni, rgt_uni]
  have hgrade (I : Finset ι) (J : Finset κ) : (((uni I J ∩ rightIndices).card : ℕ) : ℤ) = J.card :=
    congrArg (fun t : ℕ => (t : ℤ)) (card_inter_rightIndices I J)
  have hbC : b ∈ (C).C d := by
    refine acx_mem_terms_iff.mpr fun s => ?_
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [hbu]
    by_cases hI : I = ∅
    · subst I
      have he : ((uni (∅ : Finset ι) J).card : ℤ) = J.card := by
        simp only [card_uni, Finset.card_empty, zero_add]
      simpa only [he, if_true] using acx_mem_terms_iff.mp ha.1 J
    · rw [if_neg hI]
      exact zero_mem _
  have hbL : Lev rightIndices (· = d) b := by
    intro s hs
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [hbu]
    split_ifs
    · have hJ : (J.card : ℤ) ≠ d := fun h => hs ((hgrade I J).trans h)
      exact (Submodule.mem_bot k).mp (by simpa only [if_neg hJ] using acx_mem_terms_iff.mp ha.1 J)
    · rfl
  have hbV : wd (wOn rightIndices w) b = 0 := by
    funext s
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [wd_rightIndices, show (fun L => b (uni I L)) = _ from funext (hbu I)]
    split_ifs
    · rw [show wd wR a = 0 from ha.2, Pi.zero_apply, smul_zero, Pi.zero_apply]
    · rw [show (fun _ : Finset κ => (0 : M)) = 0 from rfl, map_zero, Pi.zero_apply, smul_zero, Pi.zero_apply]
  have hleft (I : Finset ι) (J : Finset κ) :
      wd (wOn rightIndicesᶜ w) b (uni I J) =
        wd (fun i : ι => w (toLex (Sum.inl i))) (fun S => b (uni S J)) I := by
    rw [wd_uni]
    have h₁ : (fun i : ι => wOn rightIndicesᶜ w (toLex (Sum.inl i))) =
        fun i => w (toLex (Sum.inl i)) := by
      funext i
      simp [wOn, rightIndices, uni]
    have h₀ : (fun j : κ => wOn rightIndicesᶜ w (toLex (Sum.inr j))) = 0 := by
      funext j
      simp [wOn, rightIndices, uni]
    rw [h₁, h₀]
    simp [wd_apply]
  have hbH (I : Finset ι) (hI : (I.card : ℤ) = d + 1 - d) :
      (fun J => wd (wOn rightIndicesᶜ w) b (uni I J)) ∈ (D).B d := by
    have hcard : I.card = 1 := by omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    have he : (fun J => wd (wOn rightIndicesᶜ w) b (uni {i} J)) =
        fun J => w (toLex (Sum.inl i)) (a J) := by
      funext J
      have hs : cubeSign ({i} : Finset ι) i = 1 := by
        change (-1 : ℤ) ^ (({i} : Finset ι).filter (· < i)).card = 1
        simp [Finset.filter_singleton]
      rw [hleft, wd_apply]
      simp only [Finset.sum_singleton, hs, one_smul, Finset.erase_singleton, hbu, if_true]
    rw [he]
    exact hb i
  obtain ⟨c, hc, hcl⟩ := exists_cocycle_of_top_columns hw (fun _ i _ => hP i)
    (fun _ m hm => hE m hm) hbC hbL hbV hbH
  refine ⟨c, hc, fun J => ?_⟩
  by_cases hJ : (J.card : ℤ) = d
  · have he := hcl (uni ∅ J) (fun hj => (not_lt_of_ge (le_of_eq ((hgrade ∅ J).trans hJ).symm)) hj)
    change c (uni ∅ J) - b (uni ∅ J) = 0 at he
    rw [sub_eq_zero.mp he, hbu, if_pos rfl]
  · have he : ((uni (∅ : Finset ι) J).card : ℤ) ≠ d := by
      simpa only [card_uni, Finset.card_empty, zero_add] using hJ
    have hzero : c (uni ∅ J) = 0 := (Submodule.mem_bot k).mp
      (by simpa only [if_neg he] using acx_mem_terms_iff.mp hc.1 (uni ∅ J))
    rw [hzero]
    exact ((Submodule.mem_bot k).mp (by simpa only [if_neg hJ] using acx_mem_terms_iff.mp ha.1 J)).symm

end GlobalTheory.WH
