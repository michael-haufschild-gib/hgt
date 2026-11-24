import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartComplex

/-! The weighted differential respects chart lattices. Changing the
chart used to normalize a weight leaves the scaled lattice unchanged. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E κ : Type} [Field k] [CommRing S] [Algebra k S] [AddCommGroup E] [Module k E]
  [LinearOrder κ] {d : ℕ} (T : WeightedChartSystem k d S E)

private theorem mem_lft_iff {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    (s : Finset (ι ⊕ₗ κ)) (i : ι) : i ∈ lft s ↔ toLex (Sum.inl i) ∈ s := by
  simp [lft, Finset.mem_toLeft]

private theorem mem_rgt_iff {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
    (s : Finset (ι ⊕ₗ κ)) (i : κ) : i ∈ rgt s ↔ toLex (Sum.inr i) ∈ s := by
  simp [rgt, Finset.mem_toRight]

private theorem scaled_le (hT : T.Good) (n : κ → ℕ × ℕ)
    {I J : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    {i j i' j' : Fin (d + 1)} (hi' : i' ∈ I) (hj' : j' ∈ J) (L : Finset κ) :
    (T.M I J).map (T.act ((∏ l ∈ L, T.weightUnit n i j l : Sˣ) : S)) ≤
      (T.M I J).map (T.act ((∏ l ∈ L, T.weightUnit n i' j' l : Sˣ) : S)) := by
  have hratio (l : κ) : ((T.weightUnit n i j l * (T.weightUnit n i' j' l)⁻¹ : Sˣ) : S) ∈ T.R I J := by
    have e : T.weightUnit n i j l * (T.weightUnit n i' j' l)⁻¹ =
        (T.X i * (T.X i')⁻¹) ^ (n l).1 * (T.Y j * (T.Y j')⁻¹) ^ (n l).2 := by
      simp only [weightUnit, mul_inv, mul_pow, inv_pow]
      ac_rfl
    rw [e, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    exact mul_mem (pow_mem (hT.memX I J hJ i' hi' i) _) (pow_mem (hT.memY I J hI j' hj' j) _)
  let a : Sˣ := ∏ l ∈ L, T.weightUnit n i j l
  let b : Sˣ := ∏ l ∈ L, T.weightUnit n i' j' l
  have hr : ((a * b⁻¹ : Sˣ) : S) ∈ T.R I J := by
    simp only [a, b]
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Units.coe_prod]
    exact Subalgebra.prod_mem _ (fun l _ => hratio l)
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨T.act ((a * b⁻¹ : Sˣ) : S) m, hT.stab I J hI hJ _ hr m hm, ?_⟩
  change T.act (b : S) (T.act ((a * b⁻¹ : Sˣ) : S) m) = T.act (a : S) m
  rw [← Module.End.mul_apply, ← map_mul, ← Units.val_mul, mul_comm b, mul_assoc,
    inv_mul_cancel, mul_one]

theorem scaledCoefficients_mono (hT : T.Good) (n : κ → ℕ × ℕ)
    {I I' J J' : Finset (Fin (d + 1))} (hI : I.Nonempty) (hJ : J.Nonempty)
    (hII : I ⊆ I') (hJJ : J ⊆ J') (L : Finset κ) :
    T.scaledCoefficients n I J L ≤ T.scaledCoefficients n I' J' L := by
  refine le_trans (Submodule.map_mono (hT.monoM I I' J J' hI hJ hII hJJ)) ?_
  exact scaled_le T hT n (hI.mono hII) (hJ.mono hJJ)
    (chartIndex_mem (hI.mono hII)) (chartIndex_mem (hJ.mono hJJ)) L

omit [LinearOrder κ] in
theorem normalizedWeight_mem (hT : T.Good) {n : κ → ℕ × ℕ} {z : κ → S} (hz : T.Admitted n z)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) (l : κ) :
    T.normalizedWeight n z i j l ∈ T.R I J :=
  hT.monoR (Singleton.singleton i) I (Singleton.singleton j) J (Finset.singleton_nonempty i)
    (Finset.singleton_nonempty j) (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_subset_iff.mpr hj)
    (hz i j l)

/-- All choices of affine coordinate origins in a chart pair give the
same weighted column. -/
theorem columnComplex_eq (hT : T.Good) (n : κ → ℕ × ℕ) (z : κ → S)
    {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    T.columnComplex n z I J =
      acx (fun L => (T.M I J).map (T.act ((∏ l ∈ L, T.weightUnit n i j l : Sˣ) : S)))
        (fun l => T.act (z l)) := by
  unfold columnComplex
  congr 1
  funext L
  have hI : I.Nonempty := ⟨i, hi⟩
  have hJ : J.Nonempty := ⟨j, hj⟩
  exact le_antisymm (scaled_le T hT n hI hJ hi hj L)
    (scaled_le T hT n hI hJ (chartIndex_mem hI) (chartIndex_mem hJ) L)

private theorem mixedCoefficients_mono (hT : T.Good) (n : κ → ℕ × ℕ) (L : Finset κ)
    {s t : Finset (ChartPair d)} (hst : s ⊆ t) :
    T.mixedCoefficients n L s ≤ T.mixedCoefficients n L t := by
  unfold mixedCoefficients
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · have hL : lft s ⊆ lft t := Finset.toLeft_monotone (Finset.map_subset_map.mpr hst)
    have hR : rgt s ⊆ rgt t := Finset.toRight_monotone (Finset.map_subset_map.mpr hst)
    rw [if_pos h, if_pos ⟨h.1.mono hL, h.2.mono hR⟩]
    exact T.scaledCoefficients_mono hT n h.1 h.2 hL hR L
  · rw [if_neg h]
    exact bot_le

private theorem weight_mem_mixedCoefficients (hT : T.Good) {n : κ → ℕ × ℕ} {z : κ → S}
    (hz : T.Admitted n z) {L : Finset κ} {l : κ} (hl : l ∉ L)
    {s : Finset (ChartPair d)} {m : E} (hm : m ∈ T.mixedCoefficients n L s) :
    T.act (z l) m ∈ T.mixedCoefficients n (insert l L) s := by
  unfold mixedCoefficients at hm ⊢
  by_cases h : (lft s).Nonempty ∧ (rgt s).Nonempty
  · rw [if_pos h, scaledCoefficients] at hm ⊢
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hm
    let i := chartIndex (lft s)
    let j := chartIndex (rgt s)
    let b : Sˣ := T.weightUnit n i j l
    let a : Sˣ := ∏ t ∈ L, T.weightUnit n i j t
    let r := T.normalizedWeight n z i j l
    have hr := T.normalizedWeight_mem hT hz (chartIndex_mem h.1) (chartIndex_mem h.2) l
    refine ⟨T.act r v, hT.stab _ _ h.1 h.2 _ hr _ hv, ?_⟩
    rw [Finset.prod_insert hl]
    change T.act ((b * a : Sˣ) : S) (T.act r v) = T.act (z l) (T.act (a : S) v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    rw [Units.val_mul, show r = z l * (b⁻¹ : Sˣ) from rfl]
    calc
      (b : S) * (a : S) * (z l * (b⁻¹ : Sˣ)) =
          ((b : S) * (b⁻¹ : Sˣ)) * (z l * (a : S)) := by ring
      _ = _ := by rw [Units.mul_inv, one_mul]
  · rw [if_neg h, Submodule.mem_bot] at hm
    rw [if_neg h, hm, map_zero]
    exact zero_mem _

/-- Each admissible weight sends the coefficient lattice into the
lattice on the enlarged index set. -/
theorem weights_preserve_mixedCoefficients (hT : T.Good)
    {n : κ → ℕ × ℕ} {z : κ → S} (hz : T.Admitted n z) :
    ∀ s t, t ∉ s → T.mixedCoefficients n (rgt s) (lft s) ≤
      (T.mixedCoefficients n (rgt (insert t s)) (lft (insert t s))).comap (T.weights z t) := by
  intro s t ht m hm
  obtain ⟨x, rfl⟩ : ∃ x : ChartPair d ⊕ κ, toLex x = t := ⟨ofLex t, toLex_ofLex t⟩
  rcases x with a | l
  · have hL : lft s ⊆ lft (insert (toLex (Sum.inl a)) s) :=
      Finset.toLeft_monotone (Finset.map_subset_map.mpr (Finset.subset_insert _ _))
    have hR : rgt (insert (toLex (Sum.inl a)) s) = rgt s := by
      ext b
      simp [mem_rgt_iff]
    change T.weights z (toLex (Sum.inl a)) m ∈ T.mixedCoefficients n _ _
    simp only [weights, ofLex_toLex, Sum.elim_inl, map_one, Module.End.one_apply]
    have he := mixedCoefficients_mono T hT n (rgt s) hL hm
    rwa [← hR] at he
  · have hl : l ∉ rgt s := fun h => ht ((mem_rgt_iff s l).mp h)
    have hL : lft (insert (toLex (Sum.inr l)) s) = lft s := by
      ext b
      simp [mem_lft_iff]
    have hR : rgt (insert (toLex (Sum.inr l)) s) = insert l (rgt s) := by
      ext b
      simp [mem_rgt_iff]
    change T.weights z (toLex (Sum.inr l)) m ∈ T.mixedCoefficients n _ _
    simp only [weights, ofLex_toLex, Sum.elim_inr]
    have he := weight_mem_mixedCoefficients T hT hz hl hm
    rwa [← hL, ← hR] at he

/-- Admissible weights preserve the graded chart lattices and define
a differential with square zero. -/
theorem complex_isCx (hT : T.Good) {n : κ → ℕ × ℕ} {z : κ → S} (hz : T.Admitted n z) :
    (T.complex n z).IsCx :=
  acx_isCx _ _ (fun i j => (Commute.all _ _).map T.act)
    (T.weights_preserve_mixedCoefficients hT hz)

end GlobalTheory.WH.WeightedChartSystem
