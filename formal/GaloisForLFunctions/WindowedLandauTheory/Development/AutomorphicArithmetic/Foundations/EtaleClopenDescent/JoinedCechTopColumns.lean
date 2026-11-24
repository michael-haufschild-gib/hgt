import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnPrimitive
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechFiltrationExact

/-! Boundary detection and cocycle lifting on the joined cover from
exact columns and a primitive in the highest filtration degree. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι κ M : Type} [Field k] [LinearOrder ι] [LinearOrder κ] [Fintype ι] [Fintype κ]
  [AddCommGroup M] [Module k M]
  {A : Finset (ι ⊕ₗ κ) → Submodule k M} {w : ι ⊕ₗ κ → Module.End k M}
  {n d : ℤ}

omit [Fintype ι] in
/-- In the highest permitted right degree, a joined cocycle restricts
to a cocycle of the column. -/
theorem rightColumn_top_mem_cycles {c : Finset (ι ⊕ₗ κ) → M}
    (hc : c ∈ (acx A w).Z n) (hL : Lev rightIndices (· ≤ d) c)
    (I : Finset ι) (hI : (I.card : ℤ) = n - d) :
    (fun J => c (uni I J)) ∈ (rightColumn A w I).Z d := by
  have hC : (fun J => c (uni I J)) ∈ (rightColumn A w I).C d := by
    refine acx_mem_terms_iff.mpr fun J => ?_
    have he : ((uni I J).card : ℤ) = n ↔ (J.card : ℤ) = d := by
      rw [card_uni]
      omega
    simpa only [he] using acx_mem_terms_iff.mp hc.1 (uni I J)
  refine ⟨hC, ?_⟩
  let wr (j : κ) := w (toLex (Sum.inr j))
  change wd wr (fun J => c (uni I J)) = 0
  funext J
  by_cases hJ : (J.card : ℤ) = d + 1
  · have hzero : (fun K : Finset ι => c (uni K J)) = 0 := funext fun K =>
      hL _ (by
        have hcard : (((uni K J ∩ rightIndices).card : ℕ) : ℤ) = J.card :=
          congrArg (fun a : ℕ => (a : ℤ)) (card_inter_rightIndices K J)
        intro hle
        change (((uni K J ∩ rightIndices).card : ℕ) : ℤ) ≤ d at hle
        omega)
    have hd : wd w c = 0 := hc.2
    have he := congrFun hd (uni I J)
    rw [wd_uni, hzero, map_zero, Pi.zero_apply, zero_add, Pi.zero_apply] at he
    have he' := congrArg (fun a : M => (-1 : ℤ) ^ I.card • a) he
    change (-1 : ℤ) ^ I.card • ((-1 : ℤ) ^ I.card • wd wr (fun L => c (uni I L)) J) =
      (-1 : ℤ) ^ I.card • (0 : M) at he'
    rwa [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, smul_zero] at he'
  · rw [wd_apply, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : ((J.erase j).card : ℤ) ≠ d := by
      have he := Finset.card_erase_add_one hj
      omega
    have hz := (Submodule.mem_bot k).mp
      (by simpa only [if_neg hj'] using acx_mem_terms_iff.mp hC (J.erase j))
    rw [hz, map_zero, smul_zero]

/-- A cocycle supported in levels at most d is a boundary if its level-d
columns are boundaries and the columns are exact below d. -/
theorem boundary_of_top_columns (hcx : (acx A w).IsCx)
    (hE : ∀ I m, m < d → (rightColumn A w I).Z m ≤ (rightColumn A w I).B m)
    {c : Finset (ι ⊕ₗ κ) → M} (hc : c ∈ (acx A w).Z n)
    (hL : Lev rightIndices (· ≤ d) c)
    (hcol : ∀ I : Finset ι, (I.card : ℤ) = n - d →
      (fun J => c (uni I J)) ∈ (rightColumn A w I).B d) :
    c ∈ (acx A w).B n := by
  let Q : Finset (ι ⊕ₗ κ) := rightIndices
  have hcol' (I : Finset ι) (hi : (I.card : ℤ) = n - d) :
      (fun J => levelPart Q d c (uni I J)) ∈ (rightColumn A w I).B d := by
    have he : (fun J => levelPart Q d c (uni I J)) = (fun J => c (uni I J)) := by
      funext J
      have hcard : (((uni I J) ∩ Q).card : ℤ) = J.card :=
        congrArg (fun a : ℕ => (a : ℤ)) (card_inter_rightIndices I J)
      unfold levelPart
      split_ifs with hlevel
      · rfl
      · have hj : (J.card : ℤ) ≠ d := fun h' => hlevel (hcard.trans h')
        have hdeg : ((uni I J).card : ℤ) ≠ n := by rw [card_uni]; omega
        have hz : c (uni I J) = 0 := (Submodule.mem_bot k).mp
          (by simpa only [if_neg hdeg] using acx_mem_terms_iff.mp hc.1 (uni I J))
        exact hz.symm
    rw [he]
    exact hcol I hi
  obtain ⟨y, hy, hyl, hdy⟩ :=
    exists_rightPrimitive_of_columns (levelPart_mem Q hc.1) (levelPart_support Q d c) hcol'
  refine boundary_of_top_level_boundary hcx (qEx_of_rightColumn_exact A w d hE) hc hL hy hyl ?_
  intro s hs
  exact (congrFun hdy s).trans (if_pos hs)

/-- A prescribed top-level cochain lifts to a joined cocycle when its
horizontal differential has a primitive in each top-level column. -/
theorem exists_cocycle_of_top_columns
    (hw : ∀ i j, Commute (w i) (w j))
    (hA : ∀ t i, i ∉ t → A t ≤ (A (insert i t)).comap (w i))
    (hE : ∀ I m, m < d → (rightColumn A w I).Z m ≤ (rightColumn A w I).B m)
    {c₀ : Finset (ι ⊕ₗ κ) → M} (hc₀ : c₀ ∈ (acx A w).C n)
    (hl₀ : Lev rightIndices (· = d) c₀)
    (hv₀ : wd (wOn rightIndices w) c₀ = 0)
    (hcol : ∀ I : Finset ι, (I.card : ℤ) = n + 1 - d →
      (fun J => wd (wOn rightIndicesᶜ w) c₀ (uni I J)) ∈ (rightColumn A w I).B d) :
    ∃ c ∈ (acx A w).Z n, Lev rightIndices (· < d) (c - c₀) := by
  let Q : Finset (ι ⊕ₗ κ) := rightIndices
  let b := wd (wOn Qᶜ w) c₀
  have hbC : b ∈ (acx A w).C (n + 1) := wd_on_mem hw hA Qᶜ hc₀
  have hbL : Lev Q (· = d) b := wd_compl_support w hl₀
  obtain ⟨y, hy, hyl, hdy⟩ := exists_rightPrimitive_of_columns hbC hbL hcol
  have hy' : y ∈ (acx A w).C n := by rwa [add_sub_cancel_right] at hy
  exact exists_cocycle_of_top_level hw hA (qEx_of_rightColumn_exact A w d hE) hc₀ hv₀ hy' hyl hdy

end GlobalTheory.WH
