import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.MixedCechCupBoundary
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCupLeibniz

/-! Pairing in the left Čech coordinate and evaluating in top degree
sends a mixed boundary to a right boundary when the pairing kills faces. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι κ E M N : Type} [Field k] [LinearOrder ι] [Fintype ι] [LinearOrder κ]
  [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

omit [Fintype ι] in
private theorem mixed_component {A : Finset ι → Finset κ → Submodule k E} {p : ℤ}
    {a : Finset (ι ⊕ₗ κ) → E} (ha : a ∈ (mixedCech A).C p) (I : Finset ι) (J : Finset κ) :
    a (uni I J) = 0 ∨ I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card : ℕ) : ℤ) = p ∧
      a (uni I J) ∈ A I J := by
  have h := (Submodule.mem_pi.mp ha) (uni I J) (Set.mem_univ _)
  change a (uni I J) ∈
    (if ((uni I J).card : ℤ) = p then
      (if (lft (uni I J)).Nonempty ∧ (rgt (uni I J)).Nonempty then
        A (lft (uni I J)) (rgt (uni I J)) else ⊥) else ⊥) at h
  rw [card_uni, lft_uni, rgt_uni] at h
  split_ifs at h with hp hIJ
  · exact Or.inr ⟨hIJ.1, hIJ.2, hp, h⟩
  · exact Or.inl ((Submodule.mem_bot k).mp h)
  · exact Or.inl ((Submodule.mem_bot k).mp h)

/-- Evaluate the left Čech cup pairing on the full left index set. -/
def cupAlongLeft (μ : E →ₗ[k] M →ₗ[k] N) (a : Finset ι → M)
    (t : Finset (ι ⊕ₗ κ) → E) (J : Finset κ) : N :=
  cechCup μ (fun I => t (uni I J)) a Finset.univ

/-- A left cocycle paired against a mixed boundary gives a right
boundary. The hypothesis at proper faces removes the left differential. -/
theorem cupAlongLeft_mem_boundary
    (μ : E →ₗ[k] M →ₗ[k] N) (A : Finset ι → Finset κ → Submodule k E)
    (B : Finset ι → Submodule k M) (C : Finset κ → Submodule k N)
    (hmem : ∀ {I L J}, ∀ {v w}, v ∈ A I J → w ∈ B L → μ v w ∈ C J)
    (hface : ∀ {I L W J}, W ⊂ (Finset.univ : Finset ι) →
      I.Nonempty → L.Nonempty → I ⊆ W → L ⊆ W →
      ∀ {v w}, v ∈ A I J → w ∈ B L → μ v w = 0)
    {p : ℕ} (hp : p < Fintype.card ι) {a : Finset ι → M}
    (ha : a ∈ (cech B).Z p) {t : Finset (ι ⊕ₗ κ) → E}
    (ht : t ∈ (mixedCech A).B ((Fintype.card ι : ℤ) + 1)) :
    cupAlongLeft μ a t ∈ (cech C).B p := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp ht
  let m := Fintype.card ι - p
  have ha0 := cechC_apply_empty ha.1
  have hda : deltaL k ι M a = 0 := ha.2
  have hac (L : Finset ι) : a L = 0 ∨ L.Nonempty ∧ L.card = p + 1 ∧ a L ∈ B L := by
    have h := (Submodule.mem_pi.mp ha.1) L (Set.mem_univ _)
    split_ifs at h with hL
    · exact Or.inr ⟨hL.1, by exact_mod_cast hL.2, h⟩
    · exact Or.inl ((Submodule.mem_bot k).mp h)
  have hC : cupAlongLeft μ a y ∈ (cech C).C ((p : ℤ) - 1) := by
    refine Submodule.mem_pi.mpr (fun J _ => ?_)
    change cupAlongLeft μ a y J ∈
      (if J.Nonempty ∧ (J.card : ℤ) = (p : ℤ) - 1 + 1 then C J else ⊥)
    rw [cupAlongLeft, cechCup_apply]
    split_ifs with hJ
    · refine Submodule.sum_mem _ (fun i _ => ?_)
      rcases hac (Finset.univ.filter (i ≤ ·)) with ha' | ⟨_, _, ha'⟩
      · rw [ha', map_zero]
        exact zero_mem _
      exact hmem (by
        rcases mixed_component hy (Finset.univ.filter (· ≤ i)) J with he | ⟨_, _, _, he⟩
        · rw [he]
          exact zero_mem _
        · exact he) ha'
    · refine (Submodule.mem_bot k).mpr (Finset.sum_eq_zero ?_)
      intro i hi
      rcases hac (Finset.univ.filter (i ≤ ·)) with ha' | ⟨_, hcard, _⟩
      · rw [ha', map_zero]
      rcases mixed_component hy (Finset.univ.filter (· ≤ i)) J with he | ⟨_, hJn, hcd, _⟩
      · rw [he, map_zero, LinearMap.zero_apply]
      have hsum := card_filter_le_add_card_filter_ge Finset.univ i hi
      simp only [Finset.card_univ] at hsum
      exact (hJ ⟨hJn, by omega⟩).elim
  have hleft (J : Finset κ) :
      cechCup μ (deltaL k ι E (fun I => y (uni I J))) a Finset.univ = 0 := by
    have h0 : y (uni (∅ : Finset ι) J) = 0 :=
      (mixed_component hy ∅ J).resolve_right (by simp)
    rw [← deltaL_cechCup_of_rightCycle μ _ a h0 ha0 hda, deltaL_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    let W : Finset ι := Finset.univ.erase i
    have hW : W ⊂ Finset.univ := Finset.erase_ssubset hi
    change _ • cechCup μ (fun I => y (uni I J)) a W = 0
    rw [cechCup_apply]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
    rcases hac (W.filter (j ≤ ·)) with h | ⟨hL, _, hw⟩
    · rw [h, map_zero]
    rcases mixed_component hy (W.filter (· ≤ j)) J with h | ⟨hI, _, _, hv⟩
    · rw [h, map_zero, LinearMap.zero_apply]
    exact hface hW hI hL (Finset.filter_subset _ _) (Finset.filter_subset _ _) hv hw
  have hD : cupAlongLeft μ a (deltaL k (ι ⊕ₗ κ) E y) =
      (-1 : ℤ) ^ m • deltaL k κ N (cupAlongLeft μ a y) := by
    funext J
    simp only [cupAlongLeft, cechCup_apply, deltaL_uni, map_add, LinearMap.add_apply,
      map_zsmul, LinearMap.smul_apply, Finset.sum_add_distrib, Pi.smul_apply]
    rw [show (∑ i, μ (deltaL k ι E (fun I => y (uni I J))
        (Finset.univ.filter (· ≤ i))) (a (Finset.univ.filter (i ≤ ·)))) = 0 from hleft J, zero_add,
      deltaL_apply (k := k) (cupAlongLeft μ a y) J]
    simp only [cupAlongLeft, cechCup_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rcases hac (Finset.univ.filter (i ≤ ·)) with ha' | ⟨_, hcard, _⟩
    · simp only [ha', map_zero, smul_zero, Finset.sum_const_zero]
    have hsum := card_filter_le_add_card_filter_ge Finset.univ i hi
    simp only [Finset.card_univ] at hsum
    rw [show (Finset.univ.filter (· ≤ i)).card = m by dsimp [m]; omega, deltaL_apply]
    simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, Finset.smul_sum]
  refine ⟨(-1 : ℤ) ^ m • cupAlongLeft μ a y, zsmul_mem hC _, ?_⟩
  change deltaL k κ N ((-1 : ℤ) ^ m • cupAlongLeft μ a y) =
    cupAlongLeft μ a (wd (1 : (ι ⊕ₗ κ) → Module.End k E) y)
  rw [wd_one, map_zsmul, hD]

end GlobalTheory.WH
