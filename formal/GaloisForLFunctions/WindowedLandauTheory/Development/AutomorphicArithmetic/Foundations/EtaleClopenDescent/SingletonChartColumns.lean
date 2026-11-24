import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartProjection
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartDifferential
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechTopColumns
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCoefficientMap

/-! Closed columns on single chart pairs give a global cocycle when
their horizontal differences have column primitives on overlaps. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E κ : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] [LinearOrder κ] [Fintype κ]
  {d : ℕ} (T : WeightedChartSystem k d S E)
  {n : κ → ℕ × ℕ} {z : κ → S}

/-- Place the given columns on intersections with one chart on each side. -/
def singletonChartColumns
    (u : Fin (d + 1) → Fin (d + 1) → Finset κ → E)
    (s : Finset (ChartPair d ⊕ₗ κ)) : E :=
  if (lft (lft s)).card = 1 ∧ (rgt (lft s)).card = 1 then
    u (chartIndex (lft (lft s))) (chartIndex (rgt (lft s))) (rgt s) else 0

private lemma eq_singleton_chartIndex {I : Finset (Fin (d + 1))} (hI : I.card = 1) :
    I = {chartIndex I} := by
  have hn : I.Nonempty := Finset.card_pos.mp (by omega)
  exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (chartIndex_mem hn))
    (by rw [hI, Finset.card_singleton])).symm

omit [LinearOrder κ] [Fintype κ] in
theorem singletonChartColumns_apply
    (u : Fin (d + 1) → Fin (d + 1) → Finset κ → E) (i j : Fin (d + 1)) (L : Finset κ) :
    singletonChartColumns u (uni (uni {i} {j}) L) = u i j L := by
  have h (a : Fin (d + 1)) : chartIndex ({a} : Finset (Fin (d + 1))) = a :=
    Finset.mem_singleton.mp (chartIndex_mem (Finset.singleton_nonempty a))
  simp only [singletonChartColumns, lft_uni, rgt_uni, Finset.card_singleton, true_and, if_true, h]

private theorem deltaL_constant_singletons {ι W : Type} [LinearOrder ι] [AddCommGroup W]
    [Module k W] (v : W) :
    deltaL k ι W (fun I => if I.card = 1 then v else 0) = 0 := by
  rw [← wd_one]
  let f : Finset ι → W := Pi.single ∅ v
  have hf : (fun I : Finset ι => if I.card = 1 then v else 0) =
      wd (1 : ι → Module.End k W) f := by
    funext I
    by_cases hI : I.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
      simp [wd_apply, f, Finset.filter_singleton, GlobalTheory.cubeSign,
        GaloisForLFunctions.HTGeometry.BorelWeil.cechSign,
        GaloisForLFunctions.HTGeometry.BorelWeil.belowCard]
    · rw [if_neg hI, wd_apply]
      symm
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : I.erase i ≠ ∅ := by
        intro he
        have hc := Finset.card_erase_add_one hi
        rw [he, Finset.card_empty, zero_add] at hc
        exact hI hc.symm
      simp only [Pi.one_apply, Module.End.one_apply, f, Pi.single_eq_of_ne hne, smul_zero]
  rw [hf]
  exact wd_wd _ (fun _ _ => Commute.one_left _) f

omit [LinearOrder κ] [Fintype κ] in
/-- A contraction constant on all singleton chart pairs kills every
horizontal difference of those columns. -/
theorem map_deltaL_singletonChartColumns_eq_zero {W : Type} [AddCommGroup W] [Module k W]
    (f : E →ₗ[k] W) (u : Fin (d + 1) → Fin (d + 1) → Finset κ → E)
    (L : Finset κ) (v : W) (hv : ∀ i j, f (u i j L) = v) (B : Finset (ChartPair d)) :
    f (deltaL k (ChartPair d) E (fun C => singletonChartColumns u (uni C L)) B) = 0 := by
  have hc : (fun C : Finset (ChartPair d) => f (singletonChartColumns u (uni C L))) =
      (fun C => if (lft C).card = 1 ∧ (rgt C).card = 1 then v else 0) := by
    funext C
    simp only [singletonChartColumns, lft_uni, rgt_uni]
    split_ifs <;> simp only [hv, map_zero]
  have hδ : deltaL k (ChartPair d) W
      (fun C => if (lft C).card = 1 ∧ (rgt C).card = 1 then v else 0) = 0 := by
    funext C
    obtain ⟨I, J, rfl⟩ : ∃ I J, C = uni I J := ⟨lft C, rgt C, (uni_lft_rgt C).symm⟩
    rw [deltaL_uni]
    simp only [lft_uni, rgt_uni, Pi.zero_apply]
    have h₁ : (fun I' : Finset (Fin (d + 1)) =>
        if I'.card = 1 ∧ J.card = 1 then v else 0) =
        (fun I' => if I'.card = 1 then (if J.card = 1 then v else 0) else 0) := by
      funext I'
      by_cases hI : I'.card = 1 <;> simp [hI]
    have h₂ : (fun J' : Finset (Fin (d + 1)) =>
        if I.card = 1 ∧ J'.card = 1 then v else 0) =
        (fun J' => if J'.card = 1 then (if I.card = 1 then v else 0) else 0) := by
      funext J'
      by_cases hJ : J'.card = 1 <;> simp [hJ]
    rw [h₁, h₂, deltaL_constant_singletons, deltaL_constant_singletons, Pi.zero_apply,
      Pi.zero_apply, smul_zero, add_zero]
  let c (C : Finset (ChartPair d)) := singletonChartColumns u (uni C L)
  calc
    _ = deltaL k (ChartPair d) W (mapCochain f c) B := congrFun (mapCochain_delta f c) B
    _ = 0 := by
      rw [show mapCochain f c = _ from hc, hδ, Pi.zero_apply]

/-- The horizontal differential is the ordinary Čech differential at
each fixed Koszul index set. -/
theorem wd_chartIndices (z : κ → S) (c : Finset (ChartPair d ⊕ₗ κ) → E)
    (B : Finset (ChartPair d)) (L : Finset κ) :
    wd (wOn rightIndicesᶜ (T.weights z)) c (uni B L) =
      deltaL k (ChartPair d) E (fun C => c (uni C L)) B := by
  rw [wd_uni]
  have h₁ : (fun a : ChartPair d => wOn rightIndicesᶜ (T.weights z) (toLex (Sum.inl a))) = 1 := by
    funext a
    simp [wOn, rightIndices, uni, weights]
  have h₀ : (fun b : κ => wOn rightIndicesᶜ (T.weights z) (toLex (Sum.inr b))) = 0 := by
    funext b
    simp [wOn, rightIndices, uni]
  rw [h₁, h₀, wd_one]
  simp [wd_apply]

variable {u : Fin (d + 1) → Fin (d + 1) → Finset κ → E} {m : ℤ}

/-- Extend singleton columns of degree (m) to a cocycle by adding
cochains of Koszul degree below (m). -/
theorem exists_cocycle_of_singletonChartColumns (hT : T.Good) (hz : T.Admitted n z)
    (hu : ∀ i j, u i j ∈ (T.columnComplex n z {i} {j}).Z m)
    (hex : ∀ I J, I.Nonempty → J.Nonempty → ∀ p < m,
      (T.columnComplex n z I J).Z p ≤ (T.columnComplex n z I J).B p)
    (hb : ∀ B : Finset (ChartPair d), B.card = 3 → (lft B).Nonempty → (rgt B).Nonempty →
      ∀ b ∈ (T.columnComplex n z (lft B) (rgt B)).Z m,
        (∀ L, b L = deltaL k (ChartPair d) E
          (fun C => singletonChartColumns u (uni C L)) B) →
        b ∈ (T.columnComplex n z (lft B) (rgt B)).B m) :
    ∃ c ∈ (T.complex n z).Z (m + 2),
      Lev rightIndices (· < m) (c - singletonChartColumns u) := by
  let K (s : Finset (ChartPair d ⊕ₗ κ)) := T.mixedCoefficients n (rgt s) (lft s)
  let w := T.weights z
  let W := acx K w
  let a := singletonChartColumns u
  have hcol (B : Finset (ChartPair d)) :
      (fun L => a (uni B L)) ∈ (rightColumn K w B).Z m := by
    by_cases hB : (lft B).card = 1 ∧ (rgt B).card = 1
    · have hI : lft B = {chartIndex (lft B)} := eq_singleton_chartIndex hB.1
      have hJ : rgt B = {chartIndex (rgt B)} := eq_singleton_chartIndex hB.2
      have hIn : (lft B).Nonempty := by rw [hI]; exact Finset.singleton_nonempty _
      have hJn : (rgt B).Nonempty := by rw [hJ]; exact Finset.singleton_nonempty _
      rw [T.rightColumn_eq n z B hIn hJn, hI, hJ]
      simpa only [a, singletonChartColumns, lft_uni, rgt_uni, if_pos hB] using
        hu (chartIndex (lft B)) (chartIndex (rgt B))
    · have he : (fun L => a (uni B L)) = 0 := by
        funext L
        simp only [a, singletonChartColumns, lft_uni, rgt_uni, if_neg hB, Pi.zero_apply]
      rw [he]
      exact zero_mem _
  have hcard (B : Finset (ChartPair d)) (L : Finset κ) :
      (((uni B L) ∩ rightIndices).card : ℤ) = L.card :=
    congrArg (fun j : ℕ => (j : ℤ)) (card_inter_rightIndices B L)
  have haL : Lev rightIndices (· = m) a := by
    intro s hs
    obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    have hL : (L.card : ℤ) ≠ m := fun he => hs ((hcard B L).trans he)
    have hm := acx_mem_terms_iff.mp (hcol B).1 L
    exact (Submodule.mem_bot k).mp (by simpa only [if_neg hL] using hm)
  have haC : a ∈ W.C (m + 2) := by
    refine acx_mem_terms_iff.mpr fun s => ?_
    obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    by_cases hB : (lft B).card = 1 ∧ (rgt B).card = 1
    · have hB₂ : B.card = 2 := by
        rw [← uni_lft_rgt B, card_uni, hB.1, hB.2]
      have hBL : ((uni B L).card : ℤ) = m + 2 ↔ (L.card : ℤ) = m := by
        rw [card_uni, hB₂]
        omega
      simpa only [hBL] using acx_mem_terms_iff.mp (hcol B).1 L
    · simp only [a, singletonChartColumns, lft_uni, rgt_uni, if_neg hB]
      exact zero_mem _
  have haV : wd (wOn rightIndices w) a = 0 := by
    funext s
    obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [wd_rightIndices, show wd (fun j => w (toLex (Sum.inr j))) (fun L => a (uni B L)) = 0
      from (hcol B).2, Pi.zero_apply, smul_zero, Pi.zero_apply]
  have hw (i j : ChartPair d ⊕ₗ κ) : Commute (w i) (w j) := (Commute.all _ _).map T.act
  have hK := T.weights_preserve_mixedCoefficients hT hz
  let b := wd (wOn rightIndicesᶜ w) a
  have hbC : b ∈ W.C (m + 2 + 1) := wd_on_mem hw hK _ haC
  have hbV : wd (wOn rightIndices w) b = 0 := by
    have he := wd_anticommute (wOn rightIndices w) (wOn rightIndicesᶜ w)
      (wOn_commute hw _ _) a
    rwa [haV, map_zero, add_zero] at he
  refine exists_cocycle_of_top_columns hw hK
    (T.rightColumn_exact_of_columnExact n z m hex) haC haL haV ?_
  intro B hB
  have hB₃ : B.card = 3 := by omega
  have hbCol : (fun L => b (uni B L)) ∈ (rightColumn K w B).Z m := by
    refine ⟨acx_mem_terms_iff.mpr (fun L => ?_), ?_⟩
    · have he : ((uni B L).card : ℤ) = m + 2 + 1 ↔ (L.card : ℤ) = m := by
        rw [card_uni, hB₃]
        omega
      simpa only [he] using acx_mem_terms_iff.mp hbC (uni B L)
    · change wd (fun j => w (toLex (Sum.inr j))) (fun L => b (uni B L)) = 0
      funext L
      have he := congrFun hbV (uni B L)
      have hsign : (-1 : ℤ) ^ (3 : ℕ) = -1 := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, neg_mul_neg, one_mul, one_mul]
      rw [wd_rightIndices, hB₃, hsign,
        neg_one_zsmul, Pi.zero_apply, neg_eq_zero] at he
      exact he
  by_cases h : (lft B).Nonempty ∧ (rgt B).Nonempty
  · rw [T.rightColumn_eq n z B h.1 h.2] at hbCol ⊢
    exact hb B hB₃ h.1 h.2 _ hbCol (T.wd_chartIndices z a B)
  · have he : (fun L => b (uni B L)) = 0 := by
      funext L
      have hm := acx_mem_terms_iff.mp hbCol.1 L
      exact (Submodule.mem_bot k).mp (by
        simpa only [K, mixedCoefficients, lft_uni, rgt_uni, if_neg h, ite_self] using hm)
    change (fun L => b (uni B L)) ∈ (rightColumn K w B).B m
    rw [he]
    exact zero_mem _

end GlobalTheory.WH.WeightedChartSystem
