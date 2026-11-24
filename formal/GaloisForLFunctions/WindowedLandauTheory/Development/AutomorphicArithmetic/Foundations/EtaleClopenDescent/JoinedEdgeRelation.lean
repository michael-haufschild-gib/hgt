import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechRefinementSigns
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.MixedCechCupBoundary
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCupLeibniz
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCoverSubcovers

/-! Folding the two copies of a cover onto the original cover gives
the cochain whose differential is the signed difference of the edges. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD

namespace GlobalTheory.WH

variable {k ι M : Type} [Field k] [LinearOrder ι] [AddCommGroup M] [Module k M]

/-- Repeat a right cochain on intersections with one left chart. -/
def edge2 (a : Finset ι → M) (s : Finset (ι ⊕ₗ ι)) : M :=
  if (lft s).card = 1 then a (rgt s) else 0

private def extendRight (a : Finset ι → M) (s : Finset (ι ⊕ₗ ι)) : M :=
  if lft s = ∅ then a (rgt s) else 0

private theorem deltaL_extendRight (a : Finset ι → M) (ha : deltaL k ι M a = 0) :
    deltaL k (ι ⊕ₗ ι) M (extendRight a) = edge2 a := by
  funext s
  obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  rw [deltaL_uni]
  simp only [extendRight, edge2, lft_uni, rgt_uni]
  have hJ : deltaL k ι M (fun S => if I = ∅ then a S else 0) J = 0 := by
    by_cases hI : I = ∅
    · simpa only [if_pos hI, Pi.zero_apply] using congrFun ha J
    · simp only [if_neg hI, ← Pi.zero_def, map_zero, Pi.zero_apply]
  rw [hJ, smul_zero, add_zero, deltaL_apply]
  by_cases hI : I.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
    have hs : GlobalTheory.cubeSign ({i} : Finset ι) i = 1 := by
      change (-1 : ℤ) ^ (({i} : Finset ι).filter (· < i)).card = 1
      simp [Finset.filter_singleton]
    simp [hs]
  · rw [if_neg hI]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hne : I.erase i ≠ ∅ := fun e => hI (by
      simpa only [e, Finset.card_empty, zero_add] using (Finset.card_erase_add_one hi).symm)
    rw [if_neg hne, smul_zero]

private def foldCover (i : ι ⊕ₗ ι) : ι := Sum.elim id id (ofLex i)

private theorem foldCover_image (I J : Finset ι) :
    (uni I J).image foldCover = I ∪ J := by
  ext i
  simp only [uni, Finset.mem_image, Finset.mem_map, Finset.mem_disjSum, Equiv.coe_toEmbedding,
    Finset.mem_union]
  constructor
  · rintro ⟨_, ⟨u, (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩), rfl⟩, rfl⟩
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (hi | hi)
    · exact ⟨toLex (Sum.inl i), ⟨Sum.inl i, Or.inl ⟨i, hi, rfl⟩, rfl⟩, rfl⟩
    · exact ⟨toLex (Sum.inr i), ⟨Sum.inr i, Or.inr ⟨i, hi, rfl⟩, rfl⟩, rfl⟩

private theorem pull_fold_oneSide (a : Finset ι → M) (I : Finset ι)
    (e : ι ↪o (ι ⊕ₗ ι)) (he : ∀ i, foldCover (e i) = i) :
    pullC foldCover (LinearMap.id : M →ₗ[k] M) a (I.map e.toEmbedding) = a I := by
  have hinj : Set.InjOn (foldCover (ι := ι)) (↑(I.map e.toEmbedding) : Set (ι ⊕ₗ ι)) := by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
    change foldCover (e i) = foldCover (e j) at hxy
    rw [he, he] at hxy
    exact congrArg e hxy
  rw [pullC_inj _ _ _ hinj]
  have himage : (I.map e.toEmbedding).image foldCover = I := by
    ext i
    simp only [Finset.mem_image, Finset.mem_map, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, hji⟩
      exact (he j).symm.trans hji ▸ hj
    · intro hi
      exact ⟨e i, ⟨i, hi, rfl⟩, he i⟩
  rw [himage, LinearMap.id_apply, sortSign]
  have hsign : (∏ x ∈ I.map e.toEmbedding, ∏ y ∈ I.map e.toEmbedding,
      if x < y ∧ foldCover y < foldCover x then (-1 : ℤ) else 1) = 1 := by
    refine Finset.prod_eq_one fun x hx => Finset.prod_eq_one fun y hy => ?_
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
    rw [if_neg]
    rintro ⟨hij, hji⟩
    change foldCover (e j) < foldCover (e i) at hji
    rw [he, he] at hji
    exact (not_lt_of_ge (e.lt_iff_lt.mp hij).le) hji
  rw [hsign, one_smul]

private theorem pull_fold_left (a : Finset ι → M) (I : Finset ι) :
    pullC foldCover (LinearMap.id : M →ₗ[k] M) a (uni I ∅) = a I := by
  let e : ι ↪o (ι ⊕ₗ ι) := joinedLeft
  have he : I.map e.toEmbedding = uni I (∅ : Finset ι) := map_joinedLeft I
  rw [← he]
  exact pull_fold_oneSide a I e (fun _ => rfl)

private theorem pull_fold_right (a : Finset ι → M) (J : Finset ι) :
    pullC foldCover (LinearMap.id : M →ₗ[k] M) a (uni ∅ J) = a J := by
  let e : ι ↪o (ι ⊕ₗ ι) := joinedRight
  have he : J.map e.toEmbedding = uni (∅ : Finset ι) J := map_joinedRight J
  rw [← he]
  exact pull_fold_oneSide a J e (fun _ => rfl)

/-- The right Čech edge and the signed left edge differ by a mixed
boundary for the chart unions. -/
theorem edge2_sub_edge1_mem_boundary (A : Finset ι → Submodule k M) {m : ℕ}
    {a : Finset ι → M} (ha : a ∈ (cech A).Z m) :
    edge2 a - (-1 : ℤ) ^ m • edge1 a ∈
      (mixedCech fun I J => A (I ∪ J)).B ((m : ℤ) + 2) := by
  let b := pullC foldCover (LinearMap.id : M →ₗ[k] M) a
  let y := extendLeft a + extendRight a - b
  have ha₀ : a ∅ = 0 := cechC_apply_empty ha.1
  have hD : deltaL k ι M a = 0 := ha.2
  refine ⟨y, ?_, ?_⟩
  · refine acx_mem_terms_iff.mpr fun s => ?_
    obtain ⟨I, J, rfl⟩ : ∃ I J, s = uni I J := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    by_cases hI : I = ∅
    · rw [hI]
      simp only [y, b, pull_fold_right, extendLeft, extendRight, lft_uni, rgt_uni, Pi.add_apply,
        Pi.sub_apply, if_true, ha₀, ite_self, zero_add, sub_self]
      exact zero_mem _
    by_cases hJ : J = ∅
    · rw [hJ]
      simp only [y, b, pull_fold_left, extendLeft, extendRight, lft_uni, rgt_uni, Pi.add_apply,
        Pi.sub_apply, if_true, if_neg hI, add_zero, sub_self]
      exact zero_mem _
    change y (uni I J) ∈ (if ((uni I J).card : ℤ) = (m : ℤ) + 2 - 1 then
      (if (lft (uni I J)).Nonempty ∧ (rgt (uni I J)).Nonempty then
        A (lft (uni I J) ∪ rgt (uni I J)) else ⊥) else ⊥)
    have hI' := Finset.nonempty_iff_ne_empty.mpr hI
    have hJ' := Finset.nonempty_iff_ne_empty.mpr hJ
    have hBoth : I.Nonempty ∧ J.Nonempty := ⟨hI', hJ'⟩
    simp only [lft_uni, rgt_uni, if_pos hBoth, y, extendLeft, extendRight,
      Pi.add_apply, Pi.sub_apply, if_neg hI, if_neg hJ, zero_add, zero_sub]
    by_cases hinj : Set.InjOn (foldCover (ι := ι)) (↑(uni I J) : Set (ι ⊕ₗ ι))
    · have hc : (uni I J).card = (I ∪ J).card := by
        rw [← foldCover_image, Finset.card_image_of_injOn hinj]
      have hdeg : ((uni I J).card : ℤ) = (m : ℤ) + 2 - 1 ↔
          (I ∪ J).Nonempty ∧ ((I ∪ J).card : ℤ) = (m : ℤ) + 1 := by
        rw [hc]
        exact ⟨fun h => ⟨hI'.mono Finset.subset_union_left, by omega⟩, fun h => by omega⟩
      rw [show b (uni I J) = sortSign foldCover (uni I J) • a (I ∪ J) by
        dsimp only [b]
        rw [pullC_inj _ _ _ hinj, foldCover_image, LinearMap.id_apply]]
      simpa only [hdeg] using
        neg_mem (zsmul_mem (Submodule.mem_pi.mp ha.1 (I ∪ J) (Set.mem_univ _))
          (sortSign foldCover (uni I J)))
    · rw [show b (uni I J) = 0 from pullC_ninj _ _ _ hinj, neg_zero]
      exact zero_mem _
  · change wd (1 : (ι ⊕ₗ ι) → Module.End k M) y = _
    have hb : deltaL k (ι ⊕ₗ ι) M b = 0 := by
      dsimp only [b]
      rw [← pullC_delta, hD, map_zero]
    dsimp only [y]
    rw [wd_one, map_sub, map_add, deltaL_extendLeft a hD, deltaL_extendRight a hD, hb, sub_zero]
    funext s
    rw [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    by_cases hs : (lft s).card = m + 1
    · rw [hs, pow_succ, mul_neg_one, neg_smul, sub_eq_add_neg, add_comm]
    · have h₀ : a (lft s) = 0 := (Submodule.mem_bot k).mp (by
        simpa only [if_neg (fun h : (lft s).Nonempty ∧ ((lft s).card : ℤ) = (m : ℤ) + 1 =>
          hs (by omega))] using Submodule.mem_pi.mp ha.1 (lft s) (Set.mem_univ _))
      simp [edge1, h₀]

end GlobalTheory.WH
