import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicColumns
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LogarithmicColumnLift
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SingletonChartColumns

/-! Lift a chart primitive through the determinant columns, then
remove the remaining cocycle using the top collapse criterion. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {p : ℕ}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "π" => (Algebra.TensorProduct.lmul' k : F ⊗[k] F →ₐ[k] F)
local notation "V₀" => ExteriorDifferentials k E p
local notation "W₀" => (F ⊗[k] ExteriorDifferentials k E p)
local notation "K₀" => ChartPair d ⊕ₗ DiagonalIndex d
local notation "A₀" => (fun I J : Finset (Fin (d + 1)) =>
  regularExteriorLattice (rB k E x (I ∪ J)) p)

/-- A logarithmic cocycle is a boundary when the collapse of its top
components is the determinant multiple of a chart boundary. -/
theorem IsFinCover.logarithmic_boundary_of_collapse_boundary (h : IsFinCover k E x)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) {n : ℤ}
    {c : Finset K₀ → W₀} {γ : Finset (ChartPair d) → V₀}
    (hγ : γ ∈ (mixedCech A₀).B (n - d))
    (hc : let T := logarithmicChartSystem (E := E) h.pd p
      c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).Z n)
    (hL : Lev rightIndices (· ≤ (d : ℤ)) c)
    (hcollapse : let T := logarithmicChartSystem (E := E) h.pd p
      ∀ (B : Finset (ChartPair d)) (L : Finset (DiagonalIndex d)), L.card = d →
        collapseLogarithmicTensor (k := k) (F := F) p (c (uni B L)) =
          π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L)) • γ B) :
    let T := logarithmicChartSystem (E := E) h.pd p
    c ∈ (T.complex (fun _ => (1, 1)) T.homogeneousMinor).B n := by
  let T := logarithmicChartSystem (E := E) h.pd p
  let deg : DiagonalIndex d → ℕ × ℕ := fun _ => (1, 1)
  let z := T.homogeneousMinor
  let w := T.weights z
  let K (s : Finset K₀) := T.mixedCoefficients deg (rgt s) (lft s)
  let V := acx K w
  let f : W₀ →ₗ[k] V₀ := collapseLogarithmicTensor p
  let fC := mapCochain (ι := ChartPair d) (M := W₀) (N := V₀) f
  let kap (L : Finset (DiagonalIndex d)) :=
    π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} L))
  have hCx : V.IsCx := T.complex_isCx (logarithmicChartSystem_good (E := E) h.pd p)
    (logarithmicChartSystem_admitted (E := E) h.pd p)
  obtain ⟨η, hη, hηD⟩ := hγ
  have hδ : deltaL k (ChartPair d) V₀ η = γ := by
    change wd (1 : ChartPair d → Module.End k V₀) η = γ at hηD
    rwa [wd_one] at hηD
  have hcol (B : Finset (ChartPair d)) :
      ∃ a ∈ (rightColumn K w B).Z (d : ℤ),
        (∀ L, f (a L) = kap L • η B) ∧
        ((B.card : ℤ) ≠ n - d - 1 → a = 0) := by
    have hηB : η B ∈ (if (B.card : ℤ) = n - d - 1 then
        if (lft B).Nonempty ∧ (rgt B).Nonempty then A₀ (lft B) (rgt B) else ⊥
      else ⊥) := acx_mem_terms_iff.mp hη B
    by_cases hb : (B.card : ℤ) = n - d - 1 ∧ (lft B).Nonempty ∧ (rgt B).Nonempty
    · rw [if_pos hb.1, if_pos hb.2] at hηB
      obtain ⟨a, ha, he⟩ := h.pd.exists_logarithmicColumn_of_joinedForm
        (chartIndex_mem hb.2.1) (chartIndex_mem hb.2.2) (η B) hηB
      rw [T.rightColumn_eq deg z B hb.2.1 hb.2.2]
      exact ⟨a, ha, he, fun hn => (hn hb.1).elim⟩
    · have he : η B = 0 := by
        split_ifs at hηB with h1 h2
        · exact (hb ⟨h1, h2⟩).elim
        · exact (Submodule.mem_bot k).mp hηB
        · exact (Submodule.mem_bot k).mp hηB
      exact ⟨0, zero_mem _, fun L => by rw [Pi.zero_apply, map_zero, he, smul_zero], fun _ => rfl⟩
  choose Y hYZ hY hY₀ using hcol
  let y (s : Finset K₀) := Y (lft s) (rgt s)
  have hy (B : Finset (ChartPair d)) (L : Finset (DiagonalIndex d)) :
      y (uni B L) = Y B L := by simp only [y, lft_uni, rgt_uni]
  have hyC : y ∈ V.C (n - 1) := by
    refine acx_mem_terms_iff.mpr fun s => ?_
    obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [hy]
    by_cases he : (B.card : ℤ) = n - d - 1
    · have ht : ((uni B L).card : ℤ) = n - 1 ↔ (L.card : ℤ) = d := by rw [card_uni]; omega
      simpa only [ht] using acx_mem_terms_iff.mp (hYZ B).1 L
    · rw [hY₀ B he, Pi.zero_apply]
      exact zero_mem _
  have hyL : Lev rightIndices (· = (d : ℤ)) y := by
    intro s hs
    obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    have hcard : (((uni B L ∩ rightIndices).card : ℕ) : ℤ) = L.card :=
      congrArg (fun a : ℕ => (a : ℤ)) (card_inter_rightIndices B L)
    have hn : (L.card : ℤ) ≠ d := fun ht => hs (hcard.trans ht)
    rw [hy]
    exact (Submodule.mem_bot k).mp (by simpa only [if_neg hn] using acx_mem_terms_iff.mp (hYZ B).1 L)
  have hyV : wd (wOn rightIndices w) y = 0 := by
    funext s
    obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    rw [wd_rightIndices, funext (hy B),
      show wd (fun j => w (toLex (Sum.inr j))) (Y B) = 0 from (hYZ B).2,
      Pi.zero_apply, smul_zero, Pi.zero_apply]
  have hd : wd w y = wd (wOn rightIndicesᶜ w) y := by
    let b := wd (wOn (rightIndices : Finset K₀)ᶜ w) y
    have hs : wd w y = wd (wOn rightIndices w) y + b := wd_on_split w rightIndices y
    exact hs.trans ((congrArg (fun a => a + b) hyV).trans (zero_add b))
  have hdiff (B : Finset (ChartPair d)) (L : Finset (DiagonalIndex d)) :
      f (wd w y (uni B L)) = kap L • γ B := by
    rw [hd, T.wd_chartIndices]
    change fC (deltaL k (ChartPair d) W₀ (fun C => y (uni C L))) B = _
    have hcomm : fC (deltaL k (ChartPair d) W₀ (fun C => y (uni C L))) =
        deltaL k (ChartPair d) V₀ (fC (fun C => y (uni C L))) :=
      mapCochain_delta (M := W₀) (N := V₀) f (fun C => y (uni C L))
    rw [hcomm, show fC (fun C => y (uni C L)) = kap L • η from
      funext (fun C => by simpa only [fC, mapCochain_apply, Pi.smul_apply, hy] using hY C L)]
    rw [← hδ, deltaL_apply, deltaL_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_comm]
  have hyB : wd w y ∈ V.B n := Submodule.mem_map_of_mem hyC
  have hyZ := (Cx.boundaries_le_cycles hCx n) hyB
  let c' := c - wd w y
  have hc' : c' ∈ V.Z n := sub_mem hc hyZ
  have hc'L : Lev rightIndices (· ≤ (d : ℤ)) c' := by
    intro s hs
    change c s - wd w y s = 0
    have hys : wd (wOn rightIndicesᶜ w) y s = 0 :=
      wd_compl_support w hyL s (fun he => hs he.le)
    exact sub_eq_zero.mpr ((hL s hs).trans ((congrFun hd s).trans hys).symm)
  have hex (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) (m : ℤ)
      (hm : m < (d : ℤ)) :
      (T.columnComplex deg z I J).Z m ≤ (T.columnComplex deg z I J).B m :=
    (h.logarithmicColumn_exact_and_boundary τ hτ (chartIndex_mem hI) (chartIndex_mem hJ)).1 m hm
  have hb : c' ∈ V.B n := by
    apply boundary_of_top_columns hCx (T.rightColumn_exact_of_columnExact deg z d hex) hc' hc'L
    intro B hB
    have hBZ := rightColumn_top_mem_cycles hc' hc'L B hB
    by_cases he : (lft B).Nonempty ∧ (rgt B).Nonempty
    · rw [T.rightColumn_eq deg z B he.1 he.2] at hBZ ⊢
      apply (h.logarithmicColumn_exact_and_boundary τ hτ
        (chartIndex_mem he.1) (chartIndex_mem he.2)).2 _ hBZ
      let L := selectedIndices (diagonalIndexEmbedding (chartIndex (rgt B)))
      have hLcard : L.card = d := by simp [L, selectedIndices]
      change f (c (uni B L) - wd w y (uni B L)) = 0
      rw [map_sub, hcollapse B L hLcard, hdiff, sub_self]
    · have hz : (fun L => c' (uni B L)) = 0 := by
        funext L
        exact (Submodule.mem_bot k).mp (by
          simpa only [K, mixedCoefficients, lft_uni, rgt_uni, if_neg he, ite_self] using
            acx_mem_terms_iff.mp hBZ.1 L)
      rw [hz]
      exact zero_mem _
  change c ∈ V.B n
  rw [← sub_add_cancel c (wd w y)]
  exact add_mem hb hyB

end GlobalTheory.PD
