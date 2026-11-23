import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechCup

/-! The ordered cup product on a joined cover identifies the signed
left edge with the product of the left and right restrictions. -/

noncomputable section

namespace GlobalTheory.WH

open GlobalTheory.CechDR

variable {k ι κ E M N : Type} [Field k] [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The augmented Čech complex supported on intersections meeting both covers. -/
def mixedCech (A : Finset ι → Finset κ → Submodule k N) : Cx k (Finset (ι ⊕ₗ κ) → N) :=
  acx (fun s => if (lft s).Nonempty ∧ (rgt s).Nonempty then A (lft s) (rgt s) else ⊥) 1

private theorem cech_component {σ V : Type} [LinearOrder σ] [AddCommGroup V] [Module k V]
    {A : Finset σ → Submodule k V} {q : ℕ} {a : Finset σ → V}
    (ha : a ∈ cechC A q) (s : Finset σ) :
    a s = 0 ∨ s.Nonempty ∧ s.card = q + 1 ∧ a s ∈ A s := by
  have h := (Submodule.mem_pi.mp ha) s (Set.mem_univ _)
  split_ifs at h with hs
  · exact Or.inr ⟨hs.1, by exact_mod_cast hs.2, h⟩
  · exact Or.inl ((Submodule.mem_bot k).mp h)

private theorem deltaL_rightEmpty (b : Finset (ι ⊕ₗ κ) → M)
    (hb : deltaL k (ι ⊕ₗ κ) M b = 0) :
    deltaL k ι M (fun I => b (uni I ∅)) = 0 := by
  funext I
  have h := deltaL_uni (k := k) b I ∅
  rw [hb, Pi.zero_apply, deltaL_apply (k := k) _ ∅, Finset.sum_empty, smul_zero, add_zero] at h
  exact h.symm

/-- For a left cocycle and a joined cocycle, the product of the left
and right restrictions differs from the signed left edge by a mixed boundary. -/
theorem joinedCup_sub_edge1_mem_mixed_boundary
    (μ : E →ₗ[k] M →ₗ[k] N) (A : Finset ι → Submodule k E)
    (G : Finset (ι ⊕ₗ κ) → Submodule k M) (H : Finset ι → Finset κ → Submodule k N)
    (hH : ∀ {I J I' S}, J.Nonempty → I'.Nonempty → S.Nonempty → I' ⊆ I → S ⊆ uni I J →
      ∀ {x y}, x ∈ A I' → y ∈ G S → μ x y ∈ H I J)
    {q p : ℕ} {a : Finset ι → E} {b : Finset (ι ⊕ₗ κ) → M}
    (ha : a ∈ (cech A).Z q) (hb : b ∈ (cech G).Z p) :
    let w := cechCup μ a (fun I => b (uni I (∅ : Finset κ)))
    cechJoin μ a (fun J => b (uni ∅ J)) - (-1 : ℤ) ^ p • edge1 w ∈
      (mixedCech H).B ((q : ℤ) + p + 2) ∧ deltaL k ι N w = 0 := by
  intro w
  let bL (I : Finset ι) := b (uni I (∅ : Finset κ))
  let bR (J : Finset κ) := b (uni (∅ : Finset ι) J)
  have hda : deltaL k ι E a = 0 := LinearMap.mem_ker.mp ha.2
  have hdb : deltaL k (ι ⊕ₗ κ) M b = 0 := LinearMap.mem_ker.mp hb.2
  have ha0 : a ∅ = 0 := (cech_component ha.1 ∅).resolve_right (by simp)
  have hb0 : b ∅ = 0 := (cech_component hb.1 ∅).resolve_right (by simp)
  have hbL0 : bL ∅ = 0 := by simp only [bL, uni_empty_empty, hb0]
  have hdw : deltaL k ι N w = 0 := by
    change deltaL k ι N (cechCup μ a bL) = 0
    rw [deltaL_cechCup_of_rightCycle μ a bL ha0 hbL0 (deltaL_rightEmpty b hdb), hda]
    funext I
    simp only [cechCup_apply, Pi.zero_apply, map_zero, LinearMap.zero_apply, Finset.sum_const_zero]
  have haq (I : Finset ι) (hI : I.card ≠ q + 1) : a I = 0 :=
    (cech_component ha.1 I).resolve_right fun e => hI e.2.1
  have hterm (I : Finset ι) (J : Finset κ) (i : ι) (hi : i ∈ I)
      (hdeg : I.card + J.card ≠ q + p + 1) :
      μ (a (I.filter (· ≤ i))) (b (uni (I.filter (i ≤ ·)) J)) = 0 := by
    rcases cech_component ha.1 (I.filter (· ≤ i)) with h | ⟨_, hq, _⟩
    · rw [h, map_zero, LinearMap.zero_apply]
    rcases cech_component hb.1 (uni (I.filter (i ≤ ·)) J) with h | ⟨_, hp, _⟩
    · rw [h, map_zero]
    rw [card_uni] at hp
    have hc := card_filter_le_add_card_filter_ge I i hi
    exact False.elim (hdeg (by omega))
  have hwcard (I : Finset ι) (hI : I.card ≠ q + p + 1) : w I = 0 := by
    change cechCup μ a bL I = 0
    rw [cechCup_apply]
    exact Finset.sum_eq_zero fun i hi => hterm I ∅ i hi (by simpa using hI)
  let v := cechCup μ (extendLeft a) b - extendLeft w
  have hvD : deltaL k (ι ⊕ₗ κ) N v =
      (-1 : ℤ) ^ (q + 1) • (cechJoin μ a bR - (-1 : ℤ) ^ p • edge1 w) := by
    have hzero : extendLeft (κ := κ) a ∅ = 0 := by
      rw [← uni_empty_empty (ι := ι) (κ := κ)]
      simp only [extendLeft, rgt_uni, lft_uni, if_true, ha0]
    change deltaL k (ι ⊕ₗ κ) N (cechCup μ (extendLeft a) b - extendLeft w) = _
    rw [map_sub, deltaL_cechCup_of_rightCycle μ _ b hzero hb0 hdb, deltaL_extendLeft a hda,
      cechCup_signed_edge1 μ q a haq b hb0, deltaL_extendLeft w hdw, smul_sub, smul_smul, ← pow_add]
    funext s
    have hs : (-1 : ℤ) ^ (lft s).card • edge1 w s =
        (-1 : ℤ) ^ (q + 1 + p) • edge1 w s := by
      by_cases hI : (lft s).card = q + p + 1
      · rw [hI, show q + 1 + p = q + p + 1 by omega]
      · simp only [edge1, hwcard _ hI, ite_self, smul_zero]
    simp only [Pi.sub_apply, Pi.smul_apply, bR, hs]
  have hvC : v ∈ (mixedCech H).C ((q : ℤ) + p + 1) := by
    refine Submodule.mem_pi.mpr fun s _ => ?_
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    change cechCup μ (extendLeft a) b (uni I J) - extendLeft w (uni I J) ∈
      (if ((uni I J).card : ℤ) = (q : ℤ) + p + 1 then
        (if (lft (uni I J)).Nonempty ∧ (rgt (uni I J)).Nonempty then
          H (lft (uni I J)) (rgt (uni I J)) else ⊥) else ⊥)
    rw [cechCup_extendLeft_uni]
    simp only [extendLeft, rgt_uni, lft_uni, card_uni]
    by_cases hJ : J = ∅
    · subst J
      simp only [if_true]
      rw [← cechCup_apply μ a bL I, show cechCup μ a bL I = w I from rfl, sub_self]
      exact zero_mem _
    rw [if_neg hJ, sub_zero]
    by_cases hdeg : I.card + J.card = q + p + 1
    · rw [if_pos (by exact_mod_cast hdeg)]
      obtain rfl | hI := I.eq_empty_or_nonempty
      · rw [Finset.sum_empty]
        exact zero_mem _
      rw [if_pos ⟨hI, Finset.nonempty_iff_ne_empty.mpr hJ⟩]
      refine Submodule.sum_mem _ fun i _ => ?_
      rcases cech_component ha.1 (I.filter (· ≤ i)) with h | ⟨hI', _, hx⟩
      · rw [h, map_zero, LinearMap.zero_apply]
        exact zero_mem _
      rcases cech_component hb.1 (uni (I.filter (i ≤ ·)) J) with h | ⟨hS, _, hy⟩
      · rw [h, map_zero]
        exact zero_mem _
      have hsub : uni (I.filter (i ≤ ·)) J ⊆ uni I J :=
        Finset.map_subset_map.mpr (Finset.disjSum_mono (Finset.filter_subset _ _) subset_rfl)
      exact hH (Finset.nonempty_iff_ne_empty.mpr hJ) hI' hS (Finset.filter_subset _ _) hsub hx hy
    · rw [Finset.sum_eq_zero fun i hi => hterm I J i hi hdeg]
      exact zero_mem _
  refine ⟨⟨(-1 : ℤ) ^ (q + 1) • v, ?_, ?_⟩, hdw⟩
  · rw [show ((q : ℤ) + p + 2 - 1) = (q : ℤ) + p + 1 by omega]
    exact zsmul_mem hvC _
  · change wd (1 : (ι ⊕ₗ κ) → Module.End k N) ((-1 : ℤ) ^ (q + 1) • v) = _
    rw [wd_one, map_zsmul, hvD, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

end GlobalTheory.WH
