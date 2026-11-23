import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechEdge
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCupProduct

/-! Ordered cup products with a left extension or a left edge on a joined cover. -/

noncomputable section

namespace GlobalTheory.WH

open GlobalTheory.CechDR

variable {k ι κ E M N : Type} [Field k] [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

private abbrev li (i : ι) : ι ⊕ₗ κ := toLex (Sum.inl i)
private abbrev ri (j : κ) : ι ⊕ₗ κ := toLex (Sum.inr j)

private theorem filter_le_left (I : Finset ι) (J : Finset κ) (i : ι) :
    (uni I J).filter (· ≤ li i) = uni (I.filter (· ≤ i)) (∅ : Finset κ) := by
  ext t
  rcases h : ofLex t with a | b <;> rw [← toLex_ofLex t, h] <;> simp [uni, li]

private theorem filter_ge_left (I : Finset ι) (J : Finset κ) (i : ι) :
    (uni I J).filter (li i ≤ ·) = uni (I.filter (i ≤ ·)) J := by
  ext t
  rcases h : ofLex t with a | b <;> rw [← toLex_ofLex t, h] <;> simp [uni, li]

private theorem filter_le_right (I : Finset ι) (J : Finset κ) (j : κ) :
    (uni I J).filter (· ≤ ri j) = uni I (J.filter (· ≤ j)) := by
  ext t
  rcases h : ofLex t with a | b <;> rw [← toLex_ofLex t, h] <;> simp [uni, ri]

private theorem filter_ge_right (I : Finset ι) (J : Finset κ) (j : κ) :
    (uni I J).filter (ri j ≤ ·) = uni (∅ : Finset ι) (J.filter (j ≤ ·)) := by
  ext t
  rcases h : ofLex t with a | b <;> rw [← toLex_ofLex t, h] <;> simp [uni, ri]

/-- Multiply a left and a right cochain over their joined intersection. -/
def cechJoin (μ : E →ₗ[k] M →ₗ[k] N) (a : Finset ι → E) (b : Finset κ → M)
    (s : Finset (ι ⊕ₗ κ)) : N :=
  μ (a (lft s)) (b (rgt s))

theorem cechCup_extendLeft_uni (μ : E →ₗ[k] M →ₗ[k] N)
    (a : Finset ι → E) (b : Finset (ι ⊕ₗ κ) → M) (I : Finset ι) (J : Finset κ) :
    cechCup μ (extendLeft a) b (uni I J) =
      ∑ i ∈ I, μ (a (I.filter (· ≤ i))) (b (uni (I.filter (i ≤ ·)) J)) := by
  rw [cechCup_apply, sum_uni]
  have hL : ∀ i ∈ I, μ (extendLeft a ((uni I J).filter (· ≤ li i)))
      (b ((uni I J).filter (li i ≤ ·))) =
        μ (a (I.filter (· ≤ i))) (b (uni (I.filter (i ≤ ·)) J)) := by
    intro i _
    simp only [filter_le_left, filter_ge_left, extendLeft, rgt_uni, lft_uni, if_true]
  have hR : ∀ j ∈ J, μ (extendLeft a ((uni I J).filter (· ≤ ri j)))
      (b ((uni I J).filter (ri j ≤ ·))) = 0 := by
    intro j hj
    have hne : J.filter (· ≤ j) ≠ ∅ :=
      (show (J.filter (· ≤ j)).Nonempty from ⟨j, Finset.mem_filter.mpr ⟨hj, le_rfl⟩⟩).ne_empty
    simp only [filter_le_right, extendLeft, rgt_uni, if_neg hne, map_zero, LinearMap.zero_apply]
  rw [Finset.sum_congr rfl hL, Finset.sum_eq_zero hR, add_zero]

/-- Cup product with the signed edge selects the right cochain. The
sign is fixed by the degree of the left cochain. -/
theorem cechCup_signed_edge1 (μ : E →ₗ[k] M →ₗ[k] N)
    (q : ℕ) (a : Finset ι → E) (ha : ∀ I : Finset ι, I.card ≠ q + 1 → a I = 0)
    (b : Finset (ι ⊕ₗ κ) → M) (hb : b ∅ = 0) :
    cechCup μ (fun s => (-1 : ℤ) ^ (lft s).card • edge1 a s) b =
      (-1 : ℤ) ^ (q + 1) • cechJoin μ a (fun J => b (uni ∅ J)) := by
  funext s
  obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  rw [cechCup_apply, sum_uni]
  beta_reduce
  rw [Finset.sum_eq_zero (s := I) (fun i _ => ?_), zero_add]
  · simp only [Pi.smul_apply, cechJoin, lft_uni, rgt_uni]
    rcases J.eq_empty_or_nonempty with rfl | hJ
    · simp only [Finset.sum_empty, uni_empty_empty, hb, map_zero, smul_zero]
    · let j := J.min' hJ
      have hj : j ∈ J := J.min'_mem _
      have hle (l : κ) (hl : l ∈ J) : j ≤ l := J.min'_le l hl
      rw [Finset.sum_eq_single_of_mem j hj (fun l hl hlj => ?_)]
      · have h₁ : J.filter (· ≤ j) = {j} := by
          ext l
          simp only [Finset.mem_filter, Finset.mem_singleton]
          exact ⟨fun ⟨hl, h⟩ => le_antisymm h (hle l hl), fun h => ⟨h.symm ▸ hj, h.le⟩⟩
        have h₂ : J.filter (j ≤ ·) = J := Finset.filter_true_of_mem hle
        simp only [filter_le_right, filter_ge_right, h₁, h₂, edge1, lft_uni, rgt_uni,
          Finset.card_singleton, if_true, map_zsmul, LinearMap.smul_apply]
        by_cases hI : I.card = q + 1
        · rw [hI]
        · simp only [ha I hI, map_zero, LinearMap.zero_apply, smul_zero]
      · have hcard : 1 < (J.filter (· ≤ l)).card := Finset.one_lt_card.mpr
          ⟨j, Finset.mem_filter.mpr ⟨hj, hle l hl⟩,
            l, Finset.mem_filter.mpr ⟨hl, le_rfl⟩, hlj.symm⟩
        simp only [filter_le_right, edge1, rgt_uni, if_neg (ne_of_gt hcard), smul_zero,
          map_zero, LinearMap.zero_apply]
  · simp only [filter_le_left, edge1, rgt_uni, Finset.card_empty, zero_ne_one, if_false, smul_zero,
      map_zero, LinearMap.zero_apply]

end GlobalTheory.WH
