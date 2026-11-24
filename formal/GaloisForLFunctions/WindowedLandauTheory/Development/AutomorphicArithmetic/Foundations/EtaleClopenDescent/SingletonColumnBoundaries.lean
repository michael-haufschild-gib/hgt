import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAppendRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SingletonChartColumns

/-! At total degree two above the Koszul dimension, only the
singleton chart pairs need a top boundary check. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E κ : Type} [Field k] [CommRing S] [Algebra k S] [LinearOrder κ]
  [Fintype κ] [AddCommGroup E] [Module k E] {d : ℕ} (T : WeightedChartSystem k d S E)
  {n : κ → ℕ × ℕ} {z : κ → S}

/-- The top Koszul coefficients of a joined cocycle restrict to a
cocycle on each singleton chart pair. -/
theorem singletonColumn_mem_cycles
    {c : Finset (ChartPair d ⊕ₗ κ) → E} (hc : c ∈ (T.complex n z).Z ((d : ℤ) + 2))
    (i j : Fin (d + 1)) :
    (fun L => c (uni (uni {i} {j}) L)) ∈ (T.columnComplex n z {i} {j}).Z (d : ℤ) := by
  let B : Finset (ChartPair d) := uni {i} {j}
  have hB : (B.card : ℤ) = (d : ℤ) + 2 - d := by
    simp [B, card_uni]
  have hI : (lft B).Nonempty := by simpa only [B, lft_uni] using Finset.singleton_nonempty i
  have hJ : (rgt B).Nonempty := by simpa only [B, rgt_uni] using Finset.singleton_nonempty j
  have h := rightColumn_top_mem_cycles hc (T.lev_rightIndices_of_mem_complex_terms hc.1) B hB
  rw [T.rightColumn_eq n z B hI hJ] at h
  simpa only [B, lft_uni, rgt_uni] using h

/-- Exactness below the dimension and top boundaries on singleton
chart pairs suffice for the Čech projection to be a boundary. -/
theorem chartPart_mem_boundaries_of_singletonColumns (hT : T.Good) (hz : T.Admitted n z)
    (hex : ∀ I J, I.Nonempty → J.Nonempty → ∀ m < (d : ℤ),
      (T.columnComplex n z I J).Z m ≤ (T.columnComplex n z I J).B m)
    {c : Finset (ChartPair d ⊕ₗ κ) → E} (hc : c ∈ (T.complex n z).Z ((d : ℤ) + 2))
    (hcol : ∀ i j : Fin (d + 1), (fun L => c (uni (uni {i} {j}) L)) ∈
      (T.columnComplex n z {i} {j}).B (d : ℤ)) :
    chartPart c ∈ (mixedCech T.M).B ((d : ℤ) + 2) := by
  apply T.chartPart_mem_boundaries (n := n) (z := z)
  have hL := T.lev_rightIndices_of_mem_complex_terms hc.1
  refine boundary_of_top_columns (T.complex_isCx hT hz)
    (T.rightColumn_exact_of_columnExact n z d hex) hc hL (fun B hB => ?_)
  have hsize : B.card = (lft B).card + (rgt B).card :=
    (congrArg Finset.card (uni_lft_rgt B)).symm.trans (card_uni _ _)
  by_cases h : (lft B).Nonempty ∧ (rgt B).Nonempty
  · rw [T.rightColumn_eq n z B h.1 h.2]
    have hI : (lft B).card = 1 := by
      have hJ := Finset.card_pos.mpr h.2
      have hI := Finset.card_pos.mpr h.1
      omega
    have hJ : (rgt B).card = 1 := by omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hI
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hJ
    have he : B = uni {i} {j} := (uni_lft_rgt B).symm.trans (by rw [hi, hj])
    rw [hi, hj, he]
    exact hcol i j
  · have hz' (L : Finset κ) : c (uni B L) = 0 := by
      have hm := acx_mem_terms_iff.mp hc.1 (uni B L)
      exact (Submodule.mem_bot k).mp (by
        simpa only [lft_uni, rgt_uni, mixedCoefficients, if_neg h, ite_self] using hm)
    rw [funext hz']
    exact zero_mem _

/-- A top class supported on the origin chart pair extends globally
when the other chart pairs have zero top cohomology. -/
theorem exists_originSupportedCocycle (hT : T.Good) (hz : T.Admitted n z)
    (hex : ∀ I J, I.Nonempty → J.Nonempty → ∀ m < (d : ℤ),
      (T.columnComplex n z I J).Z m ≤ (T.columnComplex n z I J).B m)
    (hoff : ∀ I J, I.Nonempty → J.Nonempty → (I ≠ {0} ∨ J ≠ {0}) →
      (T.columnComplex n z I J).Z (d : ℤ) ≤ (T.columnComplex n z I J).B (d : ℤ))
    {a : Finset κ → E} (ha : a ∈ (T.columnComplex n z {0} {0}).Z (d : ℤ)) :
    ∃ c ∈ (T.complex n z).Z ((d : ℤ) + 2),
      ∀ (i j : Fin (d + 1)) L, L.card = d →
        c (uni (uni {i} {j}) L) = if i = 0 ∧ j = 0 then a L else 0 := by
  let u (i j : Fin (d + 1)) : Finset κ → E := if i = 0 ∧ j = 0 then a else 0
  have hu (i j : Fin (d + 1)) : u i j ∈ (T.columnComplex n z {i} {j}).Z (d : ℤ) := by
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij
      rw [show u 0 0 = a from if_pos ⟨rfl, rfl⟩]
      exact ha
    · rw [show u i j = 0 from if_neg hij]
      exact zero_mem _
  have hoff' (S : Finset (ChartPair d)) (hS : S.card = 3)
      (hI : (lft S).Nonempty) (hJ : (rgt S).Nonempty) :
      (T.columnComplex n z (lft S) (rgt S)).Z (d : ℤ) ≤
        (T.columnComplex n z (lft S) (rgt S)).B (d : ℤ) := by
    apply hoff _ _ hI hJ
    by_contra! h
    have hcard := (congrArg Finset.card (uni_lft_rgt S)).symm.trans (card_uni _ _)
    simp only [h.1, h.2, Finset.card_singleton] at hcard
    omega
  obtain ⟨c, hc, htop⟩ := T.exists_cocycle_of_singletonChartColumns hT hz hu hex
    (fun S hS hI hJ _ hb _ => hoff' S hS hI hJ hb)
  refine ⟨c, hc, fun i j L hL => ?_⟩
  have hcard : (((uni (uni {i} {j}) L ∩ rightIndices).card : ℕ) : ℤ) = d :=
    (congrArg (fun a : ℕ => (a : ℤ)) (card_inter_rightIndices (uni {i} {j}) L)).trans
      (congrArg (fun a : ℕ => (a : ℤ)) hL)
  have he := htop (uni (uni {i} {j}) L) (fun h => (lt_irrefl (d : ℤ)) (hcard ▸ h))
  change c (uni (uni {i} {j}) L) - singletonChartColumns u (uni (uni {i} {j}) L) = 0 at he
  have hu' := sub_eq_zero.mp he
  rw [singletonChartColumns_apply] at hu'
  rw [hu']
  by_cases hij : i = 0 ∧ j = 0
  · rw [show u i j = a from if_pos hij, if_pos hij]
  · rw [show u i j = 0 from if_neg hij, if_neg hij, Pi.zero_apply]

end GlobalTheory.WH.WeightedChartSystem
