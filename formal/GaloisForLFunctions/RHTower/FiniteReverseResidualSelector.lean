import GaloisForLFunctions.RHTower.FiniteReverseResidualSeam

/-!
# Continuous padded reverse residual selector

At fixed positive residual mass and energy, the reverse head uses the least
integer count above its effective rank. The count changes at integer ranks.
We prove equality of the complete padded vectors at each seam, continuity
of every fixed-count branch, and continuity of a finite fold over all rank
thresholds. Moment preservation and positivity of selected branches are
separate obligations.
-/

namespace RHTower
noncomputable section

/-- Reverse `n`-atom head in `N` slots, padded by zeros. -/
def reverseResidualVector (A B : ℝ) (N n : ℕ) : Fin N → ℝ :=
  fun i => if i.val < n - 1 then reverseResidualLarge A B n
    else if i.val = n - 1 then reverseResidualSmall A B n else 0

theorem reverseResidualVector_at_integerRank
    {A : ℝ} {k N : ℕ} (hA : 0 < A) (hk : 2 ≤ k) (i : Fin N) :
    reverseResidualVector A (A^2/k) N k i =
      if i.val < k then A/k else 0 := by
  have hseam := reverseResidual_integerRank_seam hA hk
  have hL := hseam.2.2.1
  have hS := hseam.2.2.2.1
  simp only [reverseResidualVector, hL, hS]
  by_cases hlt : i.val < k - 1
  · have hlt' : i.val < k := by omega
    rw [if_pos hlt, if_pos hlt']
  by_cases heq : i.val = k - 1
  · have hlt' : i.val < k := by omega
    rw [if_neg hlt, if_pos heq, if_pos hlt']
  · have hnot : ¬ i.val < k := by omega
    rw [if_neg hlt, if_neg heq, if_neg hnot]

theorem reverseResidualVector_succ_at_integerRank
    {A : ℝ} {k N : ℕ} (hA : 0 < A) (hk : 2 ≤ k) (i : Fin N) :
    reverseResidualVector A (A^2/k) N (k+1) i =
      if i.val < k then A/k else 0 := by
  have hseam := reverseResidual_integerRank_seam hA hk
  have hL := hseam.2.2.2.2.1
  have hS := hseam.2.2.2.2.2
  simp [reverseResidualVector, hL, hS]

/-- Adjacent padded reverse vectors agree at an integer effective rank. -/
theorem reverseResidualVector_integerRank_seam
    {A : ℝ} {k N : ℕ} (hA : 0 < A) (hk : 2 ≤ k) :
    reverseResidualVector A (A^2/k) N k =
      reverseResidualVector A (A^2/k) N (k+1) := by
  funext i
  rw [reverseResidualVector_at_integerRank hA hk i,
    reverseResidualVector_succ_at_integerRank hA hk i]

/-- Each fixed-count padded reverse vector is continuous in its two moments. -/
theorem continuous_reverseResidualVector_comp
    {T : Type*} [TopologicalSpace T] {A B : T → ℝ}
    (hA : Continuous A) (hB : Continuous B) (N n : ℕ) :
    Continuous (fun t => reverseResidualVector (A t) (B t) N n) := by
  apply continuous_pi
  intro i
  dsimp [reverseResidualVector]
  split_ifs
  · unfold reverseResidualLarge twoLevelDeviation
    fun_prop
  · unfold reverseResidualSmall twoLevelDeviation
    fun_prop
  · fun_prop

theorem frontier_le_threshold_eq
    {T : Type*} [TopologicalSpace T] {r : T → ℝ}
    (hr : Continuous r) (c : ℝ) {t : T}
    (ht : t ∈ frontier {u | r u ≤ c}) : r t = c := by
  let s : Set T := {u | r u ≤ c}
  have hs : IsClosed s := isClosed_Iic.preimage hr
  have hge : IsClosed {u : T | c ≤ r u} := isClosed_Ici.preimage hr
  have hcomp : sᶜ ⊆ {u : T | c ≤ r u} := by
    intro u hu
    have hnot : ¬ r u ≤ c := by
      simpa only [s, Set.mem_compl_iff, Set.mem_setOf_eq] using hu
    exact le_of_lt (lt_of_not_ge hnot)
  have hclosure := closure_minimal hcomp hge
  rw [frontier_eq_closure_inter_closure] at ht
  have hle : r t ≤ c := by
    have hmem : t ∈ s := by
      rw [← hs.closure_eq]
      exact ht.1
    exact hmem
  have hge' : c ≤ r t := hclosure ht.2
  exact le_antisymm hle hge'

/-- Two neighboring reverse heads glue continuously across their rank seam. -/
theorem continuous_twoReverseBranches
    {T : Type*} [TopologicalSpace T]
    {A B : T → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hApos : ∀ t, 0 < A t) (hBpos : ∀ t, 0 < B t)
    (N k : ℕ) (hk : 2 ≤ k) :
    Continuous (fun t =>
      if (A t)^2 / B t ≤ (k : ℝ) then
        reverseResidualVector (A t) (B t) N k
      else reverseResidualVector (A t) (B t) N (k+1)) := by
  classical
  have hr : Continuous (fun t => (A t)^2 / B t) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hA.continuousAt.pow 2).div hB.continuousAt (ne_of_gt (hBpos t))
  apply continuous_if
  · intro t ht
    have hrank : (A t)^2 / B t = (k : ℝ) :=
      frontier_le_threshold_eq hr k ht
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast (show k ≠ 0 by omega)
    have hmul : (A t)^2 = (k : ℝ) * B t :=
      (div_eq_iff (ne_of_gt (hBpos t))).mp hrank
    have hBeq : B t = (A t)^2 / k := by
      apply (eq_div_iff hk0).mpr
      nlinarith [hmul]
    rw [hBeq]
    exact reverseResidualVector_integerRank_seam (hApos t) hk
  · exact (continuous_reverseResidualVector_comp hA hB N k).continuousOn
  · exact (continuous_reverseResidualVector_comp hA hB N (k+1)).continuousOn

/-- Finite fold over rank thresholds. Stage `j` uses counts from `2` through
`j+2`, selecting the first count above the residual effective rank. -/
def reverseResidualSelectorAux (A B : ℝ) (N : ℕ) : ℕ → Fin N → ℝ
  | 0 => reverseResidualVector A B N 2
  | j+1 =>
    if A^2/B ≤ ((j+2 : ℕ) : ℝ) then reverseResidualSelectorAux A B N j
    else reverseResidualVector A B N (j+3)

theorem reverseResidualSelectorAux_at_threshold
    (A B : ℝ) (N j : ℕ)
    (hrank : A^2/B = ((j+2 : ℕ) : ℝ)) :
    reverseResidualSelectorAux A B N j =
      reverseResidualVector A B N (j+2) := by
  cases j with
  | zero =>
      simp [reverseResidualSelectorAux]
  | succ j =>
      have hnot : ¬ A^2/B ≤ ((j+2 : ℕ) : ℝ) := by
        rw [hrank]
        exact_mod_cast (show ¬ (j+1)+2 ≤ j+2 by omega)
      change (if A^2/B ≤ ((j+2 : ℕ) : ℝ) then
          reverseResidualSelectorAux A B N j else
          reverseResidualVector A B N (j+3)) =
        reverseResidualVector A B N (Nat.succ j+2)
      rw [if_neg hnot]

/-- The finite rank-changing reverse selector is continuous wherever
residual mass and energy stay strictly positive. -/
theorem continuous_reverseResidualSelectorAux
    {T : Type*} [TopologicalSpace T]
    {A B : T → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hApos : ∀ t, 0 < A t) (hBpos : ∀ t, 0 < B t)
    (N j : ℕ) :
    Continuous (fun t => reverseResidualSelectorAux (A t) (B t) N j) := by
  classical
  induction j with
  | zero =>
      simpa [reverseResidualSelectorAux] using
        continuous_reverseResidualVector_comp hA hB N 2
  | succ j ih =>
      change Continuous (fun t =>
        if (A t)^2 / B t ≤ ((j+2 : ℕ) : ℝ) then
          reverseResidualSelectorAux (A t) (B t) N j
        else reverseResidualVector (A t) (B t) N (j+3))
      have hr : Continuous (fun t => (A t)^2 / B t) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        exact (hA.continuousAt.pow 2).div hB.continuousAt (ne_of_gt (hBpos t))
      apply continuous_if
      · intro t ht
        have hrank : (A t)^2 / B t = ((j+2 : ℕ) : ℝ) :=
          frontier_le_threshold_eq hr _ ht
        have hprev := reverseResidualSelectorAux_at_threshold (A t) (B t) N j hrank
        have hk0 : (((j+2 : ℕ) : ℝ)) ≠ 0 := by
          exact_mod_cast (show j+2 ≠ 0 by omega)
        have hmul : (A t)^2 = ((j+2 : ℕ) : ℝ) * B t :=
          (div_eq_iff (ne_of_gt (hBpos t))).mp hrank
        have hBeq : B t = (A t)^2 / (j+2 : ℕ) := by
          apply (eq_div_iff hk0).mpr
          nlinarith [hmul]
        calc
          reverseResidualSelectorAux (A t) (B t) N j =
              reverseResidualVector (A t) (B t) N (j+2) := hprev
          _ = reverseResidualVector (A t) (B t) N (j+3) := by
            rw [hBeq]
            simpa [show j+2+1=j+3 by omega] using
              (reverseResidualVector_integerRank_seam
                (hApos t) (show 2 ≤ j+2 by omega) (N:=N))
      · exact ih.continuousOn
      · exact (continuous_reverseResidualVector_comp hA hB N (j+3)).continuousOn

/-- If the effective rank is in the finite selector's range, the selected
branch has the exact strict-lower and weak-upper rank inequalities. -/
theorem reverseResidualSelectorAux_branch
    (A B : ℝ) (N j : ℕ) :
    (2 : ℝ) ≤ A^2/B →
    A^2/B ≤ ((j+2 : ℕ) : ℝ) →
    ∃ n : ℕ, 2 ≤ n ∧ n ≤ j+2 ∧
      (((n-1 : ℕ) : ℝ) < A^2/B) ∧
      (A^2/B ≤ (n : ℝ)) ∧
      reverseResidualSelectorAux A B N j =
        reverseResidualVector A B N n := by
  induction j with
  | zero =>
      intro hlow hhigh
      refine ⟨2, by omega, by omega, ?_, ?_, rfl⟩
      · norm_num
        linarith
      · simpa using hhigh
  | succ j ih =>
      intro hlow hhigh
      by_cases hcut : A^2/B ≤ ((j+2 : ℕ) : ℝ)
      · obtain ⟨n, hn2, hnmax, hnlow, hnup, hsel⟩ := ih hlow hcut
        refine ⟨n, hn2, by omega, hnlow, hnup, ?_⟩
        change (if A^2/B ≤ ((j+2 : ℕ) : ℝ) then
          reverseResidualSelectorAux A B N j else
          reverseResidualVector A B N (j+3)) = reverseResidualVector A B N n
        rw [if_pos hcut]
        exact hsel
      · refine ⟨j+3, by omega, by omega, ?_, ?_, ?_⟩
        · have hlt : ((j+2 : ℕ) : ℝ) < A^2/B := lt_of_not_ge hcut
          simpa [show (j+3 : ℕ)-1=j+2 by omega] using hlt
        · simpa [Nat.succ_eq_add_one, add_assoc] using hhigh
        · change (if A^2/B ≤ ((j+2 : ℕ) : ℝ) then
            reverseResidualSelectorAux A B N j else
            reverseResidualVector A B N (j+3)) = reverseResidualVector A B N (j+3)
          rw [if_neg hcut]

end
end RHTower
