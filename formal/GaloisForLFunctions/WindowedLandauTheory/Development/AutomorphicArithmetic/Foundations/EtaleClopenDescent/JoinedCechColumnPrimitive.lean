import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact

/-! Column primitives in one filtration degree assemble into a global
primitive for the right part of the joined differential. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι κ M : Type} [Field k] [LinearOrder ι] [LinearOrder κ] [Fintype κ]
  [AddCommGroup M] [Module k M]
  {A : Finset (ι ⊕ₗ κ) → Submodule k M} {w : ι ⊕ₗ κ → Module.End k M}
  {n d : ℤ} {c : Finset (ι ⊕ₗ κ) → M}

private theorem card_at_rightIndices (I : Finset ι) (J : Finset κ) :
    ((uni I J ∩ (rightIndices : Finset (ι ⊕ₗ κ))).card : ℤ) = J.card :=
  congrArg (fun a : ℕ => (a : ℤ)) (card_inter_rightIndices I J)

/-- A cochain supported in one filtration level has a right primitive
when the cochain in every column in that level is a boundary. -/
theorem exists_rightPrimitive_of_columns
    (hc : c ∈ (acx A w).C n) (hL : Lev rightIndices (· = d) c)
    (h : ∀ I : Finset ι, (I.card : ℤ) = n - d →
      (fun J => c (uni I J)) ∈ (rightColumn A w I).B d) :
    ∃ y ∈ (acx A w).C (n - 1), Lev rightIndices (· = d - 1) y ∧ wd (wOn rightIndices w) y = c := by
  let wR (j : κ) := w (toLex (Sum.inr j))
  have hc₀ (I : Finset ι) (hI : (I.card : ℤ) ≠ n - d) (J : Finset κ) : c (uni I J) = 0 := by
    by_cases hJ : (J.card : ℤ) = d
    · have he : ((uni I J).card : ℤ) ≠ n := by
        rw [card_uni]
        push_cast
        omega
      exact (Submodule.mem_bot k).mp (by
        simpa only [if_neg he] using acx_mem_terms_iff.mp hc (uni I J))
    · exact hL (uni I J) (fun h' => hJ ((card_at_rightIndices I J).symm.trans h'))
  have hcol (I : Finset ι) :
      ∃ v ∈ (rightColumn A w I).C (d - 1),
        wd wR v = (fun J => c (uni I J)) ∧ ((I.card : ℤ) ≠ n - d → v = 0) := by
    by_cases hI : (I.card : ℤ) = n - d
    · obtain ⟨v, hv, hdv⟩ := Submodule.mem_map.mp (h I hI)
      exact ⟨v, hv, hdv, fun hne => (hne hI).elim⟩
    · refine ⟨0, zero_mem _, ?_, fun _ => rfl⟩
      rw [map_zero]
      exact funext fun J => (hc₀ I hI J).symm
  choose v hv hdv hv₀ using hcol
  let y (s : Finset (ι ⊕ₗ κ)) := (-1 : ℤ) ^ (lft s).card • v (lft s) (rgt s)
  have he (I : Finset ι) (J : Finset κ) : y (uni I J) = (-1 : ℤ) ^ I.card • v I J := by
    simp only [y, lft_uni, rgt_uni]
  have hv₁ (I : Finset ι) (J : Finset κ) (hJ : (J.card : ℤ) ≠ d - 1) : v I J = 0 :=
    (Submodule.mem_bot k).mp (by simpa only [if_neg hJ] using acx_mem_terms_iff.mp (hv I) J)
  refine ⟨y, acx_mem_terms_iff.mpr (fun s => ?_), ?_, ?_⟩
  · obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [he]
    by_cases hI : (I.card : ℤ) = n - d
    · by_cases hJ : (J.card : ℤ) = d - 1
      · have hs : ((uni I J).card : ℤ) = n - 1 := by rw [card_uni]; omega
        rw [if_pos hs]
        exact zsmul_mem (by simpa only [if_pos hJ] using acx_mem_terms_iff.mp (hv I) J) _
      · rw [hv₁ I J hJ, smul_zero]
        exact zero_mem _
    · rw [hv₀ I hI, Pi.zero_apply, smul_zero]
      exact zero_mem _
  · intro s hs
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    have hJ : (J.card : ℤ) ≠ d - 1 := fun h' => hs ((card_at_rightIndices I J).trans h')
    rw [he, hv₁ I J hJ, smul_zero]
  · funext s
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [wd_rightIndices, show (fun L => y (uni I L)) = (-1 : ℤ) ^ I.card • v I from funext (he I),
      map_zsmul, Pi.smul_apply, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, hdv]

end GlobalTheory.WH
