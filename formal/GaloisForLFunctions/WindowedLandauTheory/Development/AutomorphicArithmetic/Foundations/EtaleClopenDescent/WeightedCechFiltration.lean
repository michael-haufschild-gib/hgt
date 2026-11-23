import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechComplex

/-! A filtration of weighted Čech cochains by the number of indices in a
fixed subset. The differential for those indices raises the level by one. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι M : Type*} [Field k] [LinearOrder ι] [AddCommGroup M] [Module k M]

/-- Keep the weights on the indicated indices. -/
def wOn (Q : Finset ι) (w : ι → Module.End k M) : ι → Module.End k M :=
  fun i => if i ∈ Q then w i else 0

/-- A cochain is supported on the specified levels of the filtration. -/
def Lev (Q : Finset ι) (P : ℤ → Prop) (c : Finset ι → M) : Prop :=
  ∀ t, ¬ P ((t ∩ Q).card : ℤ) → c t = 0

/-- The complex for the weights in `Q` is exact in levels below `d`. -/
def QEx (A : Finset ι → Submodule k M) (w : ι → Module.End k M) (Q : Finset ι) (d : ℤ) :
    Prop :=
  ∀ (n m : ℤ), m < d → ∀ c ∈ (acx A w).C n, Lev Q (· = m) c →
    wd (wOn Q w) c = 0 →
    ∃ y ∈ (acx A w).C (n - 1), Lev Q (· = m - 1) y ∧ wd (wOn Q w) y = c

/-- Project onto the summands with exactly `m` indices in `Q`. -/
def levelPart (Q : Finset ι) (m : ℤ) (c : Finset ι → M) : Finset ι → M :=
  fun t => if ((t ∩ Q).card : ℤ) = m then c t else 0

theorem levelPart_support (Q : Finset ι) (m : ℤ) (c : Finset ι → M) :
    Lev Q (· = m) (levelPart Q m c) := fun _ ht => if_neg ht

theorem levelPart_eq_self {Q : Finset ι} {m : ℤ} {c : Finset ι → M}
    (h : Lev Q (· = m) c) : levelPart Q m c = c := by
  funext t
  by_cases ht : ((t ∩ Q).card : ℤ) = m
  · exact if_pos ht
  · exact (if_neg ht).trans (h t ht).symm

theorem levelPart_eq_zero {Q : Finset ι} {m : ℤ} {c : Finset ι → M}
    (h : ∀ t, ((t ∩ Q).card : ℤ) = m → c t = 0) : levelPart Q m c = 0 := by
  funext t
  by_cases ht : ((t ∩ Q).card : ℤ) = m
  · exact (if_pos ht).trans (h t ht)
  · exact if_neg ht

theorem levelPart_mem {A : Finset ι → Submodule k M} {w : ι → Module.End k M}
    {n m : ℤ} (Q : Finset ι) {c : Finset ι → M} (hc : c ∈ (acx A w).C n) :
    levelPart Q m c ∈ (acx A w).C n := by
  refine Submodule.mem_pi.mpr fun t ht => ?_
  change (if ((t ∩ Q).card : ℤ) = m then c t else 0) ∈
    (if (t.card : ℤ) = n then A t else ⊥ : Submodule k M)
  by_cases h : ((t ∩ Q).card : ℤ) = m
  · rw [if_pos h]
    exact Submodule.mem_pi.mp hc t ht
  · rw [if_neg h]
    exact zero_mem _

private theorem inter_erase (t Q : Finset ι) (i : ι) :
    (t.erase i) ∩ Q = (t ∩ Q).erase i := by
  ext j
  simp only [Finset.mem_inter, Finset.mem_erase]
  exact and_assoc

theorem wd_on_levelPart (w : ι → Module.End k M) (Q : Finset ι) (m : ℤ) (c : Finset ι → M) :
    wd (wOn Q w) (levelPart Q m c) = levelPart Q (m + 1) (wd (wOn Q w) c) := by
  funext t
  simp only [wd_apply, levelPart]
  split_ifs with ht
  · refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hQ : i ∈ Q
    · have he := Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨hi, hQ⟩)
      rw [inter_erase, if_pos (show (((t ∩ Q).erase i).card : ℤ) = m by omega)]
    · simp only [wOn, if_neg hQ, LinearMap.zero_apply, smul_zero]
  · refine Finset.sum_eq_zero fun i hi => ?_
    by_cases hQ : i ∈ Q
    · have he := Finset.card_erase_add_one (Finset.mem_inter.mpr ⟨hi, hQ⟩)
      rw [inter_erase, if_neg (show (((t ∩ Q).erase i).card : ℤ) ≠ m by omega), map_zero,
        smul_zero]
    · simp only [wOn, if_neg hQ, LinearMap.zero_apply, smul_zero]

section Complement

variable [Fintype ι]

theorem wd_compl_levelPart (w : ι → Module.End k M) (Q : Finset ι) (m : ℤ)
    (c : Finset ι → M) :
    wd (wOn Qᶜ w) (levelPart Q m c) = levelPart Q m (wd (wOn Qᶜ w) c) := by
  funext t
  simp only [wd_apply, levelPart]
  split_ifs with ht
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hQ : i ∈ Q
    · simp only [wOn, Finset.mem_compl, not_not.mpr hQ, if_false, LinearMap.zero_apply, smul_zero]
    · rw [inter_erase, Finset.erase_eq_of_notMem (fun h => hQ (Finset.mem_inter.mp h).2), if_pos ht]
  · refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hQ : i ∈ Q
    · simp only [wOn, Finset.mem_compl, not_not.mpr hQ, if_false, LinearMap.zero_apply, smul_zero]
    · rw [inter_erase, Finset.erase_eq_of_notMem (fun h => hQ (Finset.mem_inter.mp h).2), if_neg ht,
        map_zero, smul_zero]

omit [Fintype ι] in
theorem wd_on_support (w : ι → Module.End k M) {Q : Finset ι} {m : ℤ} {c : Finset ι → M}
    (h : Lev Q (· = m) c) : Lev Q (· = m + 1) (wd (wOn Q w) c) := by
  have e := wd_on_levelPart w Q m c
  rw [levelPart_eq_self h] at e
  rw [e]
  exact levelPart_support _ _ _

theorem wd_compl_support (w : ι → Module.End k M) {Q : Finset ι} {m : ℤ} {c : Finset ι → M}
    (h : Lev Q (· = m) c) : Lev Q (· = m) (wd (wOn Qᶜ w) c) := by
  have e := wd_compl_levelPart w Q m c
  rw [levelPart_eq_self h] at e
  rw [e]
  exact levelPart_support _ _ _

theorem wd_on_split (w : ι → Module.End k M) (Q : Finset ι) (c : Finset ι → M) :
    wd w c = wd (wOn Q w) c + wd (wOn Qᶜ w) c := by
  have e : wOn Q w + wOn Qᶜ w = w := by
    funext i
    by_cases hi : i ∈ Q <;> simp [wOn, hi]
  rw [← LinearMap.add_apply, ← wd_add, e]

end Complement

theorem wOn_commute {w : ι → Module.End k M} (h : ∀ i j, Commute (w i) (w j))
    (P Q : Finset ι) (i j : ι) : Commute (wOn P w i) (wOn Q w j) := by
  unfold wOn
  split_ifs
  · exact h i j
  · exact Commute.zero_right _
  · exact Commute.zero_left _
  · exact Commute.zero_left _

theorem wd_on_mem {A : Finset ι → Submodule k M} {w : ι → Module.End k M}
    (hw : ∀ i j, Commute (w i) (w j))
    (hA : ∀ t i, i ∉ t → A t ≤ (A (insert i t)).comap (w i))
    (P : Finset ι) {n : ℤ} {c : Finset ι → M} (hc : c ∈ (acx A w).C n) :
    wd (wOn P w) c ∈ (acx A w).C (n + 1) := by
  have hP (t : Finset ι) (i : ι) (hi : i ∉ t) :
      A t ≤ (A (insert i t)).comap (wOn P w i) := by
    intro b hb
    change wOn P w i b ∈ A (insert i t)
    unfold wOn
    split_ifs
    · exact hA t i hi hb
    · exact zero_mem _
  exact (acx_isCx A (wOn P w) (wOn_commute hw P P) hP n c hc).1

end GlobalTheory.WH
