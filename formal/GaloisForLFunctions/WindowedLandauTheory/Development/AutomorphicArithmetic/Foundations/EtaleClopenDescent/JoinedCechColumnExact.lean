import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechEdge
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechFiltration

/-! Exactness of the right columns implies exactness of the level
complexes of the joined Čech cover. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι κ M : Type} [Field k] [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup M] [Module k M]

/-- The column on a fixed left intersection. -/
def rightColumn (A : Finset (ι ⊕ₗ κ) → Submodule k M)
    (w : ι ⊕ₗ κ → Module.End k M) (I : Finset ι) : Cx k (Finset κ → M) :=
  acx (fun J => A (uni I J)) (fun j => w (toLex (Sum.inr j)))

theorem acx_mem_terms_iff {σ : Type} [LinearOrder σ] {A : Finset σ → Submodule k M}
    {w : σ → Module.End k M} {n : ℤ} {c : Finset σ → M} :
    c ∈ (acx A w).C n ↔
      ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule k M) :=
  ⟨fun h s => Submodule.mem_pi.mp h s (Set.mem_univ _),
    fun h => Submodule.mem_pi.mpr (fun s _ => h s)⟩

section

variable [Fintype κ]

/-- The set of indices on the right side of a joined cover. -/
def rightIndices : Finset (ι ⊕ₗ κ) := uni ∅ Finset.univ

theorem card_inter_rightIndices (I : Finset ι) (J : Finset κ) :
    (uni I J ∩ rightIndices).card = J.card := by
  have e : uni I J ∩ rightIndices = uni (∅ : Finset ι) J := by
    ext t
    rcases h : ofLex t with i | j <;> rw [← toLex_ofLex t, h] <;>
      simp [rightIndices, uni]
  rw [e, card_uni, Finset.card_empty, zero_add]

theorem wd_rightIndices (w : ι ⊕ₗ κ → Module.End k M) (c : Finset (ι ⊕ₗ κ) → M)
    (I : Finset ι) (J : Finset κ) :
    wd (wOn rightIndices w) c (uni I J) =
      (-1 : ℤ) ^ I.card • wd (fun j => w (toLex (Sum.inr j))) (fun S => c (uni I S)) J := by
  rw [wd_uni]
  have hl : (fun i : ι => wOn rightIndices w (toLex (Sum.inl i))) = 0 := by
    funext i
    simp [wOn, rightIndices, uni]
  have hr (j : κ) : wOn rightIndices w (toLex (Sum.inr j)) = w (toLex (Sum.inr j)) := by
    simp [wOn, rightIndices, uni]
  rw [hl, funext hr]
  simp [wd_apply]

omit [LinearOrder ι] in
private theorem sign_smul_sign (I : Finset ι) (v : M) :
    (-1 : ℤ) ^ I.card • ((-1 : ℤ) ^ I.card • v) = v := by
  rw [smul_smul, ← mul_pow]
  simp

/-- A graded primitive for each column assembles into a graded
primitive for the right part of the joined differential. -/
theorem qEx_of_rightColumn_exact (A : Finset (ι ⊕ₗ κ) → Submodule k M)
    (w : ι ⊕ₗ κ → Module.End k M) (d : ℤ)
    (hE : ∀ I m, m < d → (rightColumn A w I).Z m ≤ (rightColumn A w I).B m) :
    QEx A w rightIndices d := by
  intro n m hm c hc hL hc₀
  let wR (j : κ) := w (toLex (Sum.inr j))
  have hcard (I : Finset ι) (J : Finset κ) :
      ((uni I J ∩ rightIndices).card : ℤ) = (J.card : ℤ) :=
    congrArg (fun j : ℕ => (j : ℤ)) (card_inter_rightIndices I J)
  have hterm := acx_mem_terms_iff.mp hc
  have hcol (I : Finset ι) :
      ∃ y ∈ (rightColumn A w I).C (m - 1), wd wR y = fun J => c (uni I J) := by
    have hZ : (fun J => c (uni I J)) ∈ (rightColumn A w I).Z m := by
      refine ⟨acx_mem_terms_iff.mpr (fun J => ?_), ?_⟩
      · by_cases hJ : (J.card : ℤ) = m
        · rw [if_pos hJ]
          have h := hterm (uni I J)
          split_ifs at h
          · exact h
          · rw [(Submodule.mem_bot k).mp h]
            exact zero_mem _
        · rw [if_neg hJ, Submodule.mem_bot]
          exact hL (uni I J) (fun he => hJ ((hcard I J).symm.trans he))
      · change wd wR (fun J => c (uni I J)) = 0
        funext J
        have e := (wd_rightIndices w c I J).symm.trans (congrFun hc₀ (uni I J))
        calc
          _ = (-1 : ℤ) ^ I.card • ((-1 : ℤ) ^ I.card • wd wR (fun L => c (uni I L)) J) :=
            (sign_smul_sign I _).symm
          _ = 0 := by rw [e, Pi.zero_apply, smul_zero]
    exact Submodule.mem_map.mp (hE I m hm hZ)
  choose y hy hdy using hcol
  let z (s : Finset (ι ⊕ₗ κ)) :=
    if ((lft s).card : ℤ) = n - m then (-1 : ℤ) ^ (lft s).card • y (lft s) (rgt s) else 0
  have hz (I : Finset ι) (J : Finset κ) :
      z (uni I J) = if (I.card : ℤ) = n - m then (-1 : ℤ) ^ I.card • y I J else 0 := by
    simp only [z, lft_uni, rgt_uni]
  have hy' (I : Finset ι) (J : Finset κ) :
      y I J ∈ (if (J.card : ℤ) = m - 1 then A (uni I J) else ⊥ : Submodule k M) :=
    acx_mem_terms_iff.mp (hy I) J
  refine ⟨z, acx_mem_terms_iff.mpr (fun s => ?_), ?_, ?_⟩
  · obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [hz]
    by_cases hI : (I.card : ℤ) = n - m
    · rw [if_pos hI]
      by_cases hJ : (J.card : ℤ) = m - 1
      · have ht : ((uni I J).card : ℤ) = n - 1 := by rw [card_uni]; omega
        rw [if_pos ht]
        exact zsmul_mem (by simpa only [if_pos hJ] using hy' I J) _
      · have h₀ : y I J = 0 := (Submodule.mem_bot k).mp (by simpa only [if_neg hJ] using hy' I J)
        rw [h₀, smul_zero]
        exact zero_mem _
    · rw [if_neg hI]
      exact zero_mem _
  · intro s hs
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    have hJ : (J.card : ℤ) ≠ m - 1 := fun e => hs ((hcard I J).trans e)
    have h₀ : y I J = 0 := (Submodule.mem_bot k).mp (by simpa only [if_neg hJ] using hy' I J)
    simp [hz, h₀]
  · funext s
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [wd_rightIndices]
    change (-1 : ℤ) ^ I.card • wd wR (fun L => z (uni I L)) J = c (uni I J)
    by_cases hI : (I.card : ℤ) = n - m
    · have e : (fun L => z (uni I L)) = (-1 : ℤ) ^ I.card • y I := by
        funext L
        rw [hz, if_pos hI, Pi.smul_apply]
      rw [e, map_zsmul, Pi.smul_apply, sign_smul_sign, hdy]
    · have e : (fun L => z (uni I L)) = 0 := by
        funext L
        rw [hz, if_neg hI, Pi.zero_apply]
      rw [e, map_zero, Pi.zero_apply, smul_zero]
      symm
      by_cases hJ : (J.card : ℤ) = m
      · have ht : ((uni I J).card : ℤ) ≠ n := by rw [card_uni]; omega
        exact (Submodule.mem_bot k).mp (by simpa only [if_neg ht] using hterm (uni I J))
      · exact hL (uni I J) (fun he => hJ ((hcard I J).symm.trans he))

end

end GlobalTheory.WH
