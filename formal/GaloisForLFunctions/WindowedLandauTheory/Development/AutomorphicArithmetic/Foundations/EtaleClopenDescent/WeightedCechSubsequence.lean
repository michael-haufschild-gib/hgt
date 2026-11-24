import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartProjection
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartColumnScaling

/-! Restricting the homogeneous weights to an ordered subsequence
preserves the regularity of the chart coefficients. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E κ κ' : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] [LinearOrder κ] [LinearOrder κ'] {d : ℕ}
  (T : WeightedChartSystem k d S E) (e : κ' ↪o κ)
  {n : κ → ℕ × ℕ} {z : κ → S} {p : ℤ}

theorem restrictKoszulIndices_mem_terms {a : Finset (ChartPair d ⊕ₗ κ) → E}
    (ha : a ∈ (T.complex n z).C p) :
    restrictKoszulIndices e a ∈ (T.complex (n ∘ e) (z ∘ e)).C p := by
  refine acx_mem_terms_iff.mpr fun s => ?_
  obtain ⟨I, L, rfl⟩ : ∃ I L, s = uni I L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  have hm := acx_mem_terms_iff.mp ha (uni I (L.map e.toEmbedding))
  simpa only [restrictKoszulIndices, card_uni, Finset.card_map, lft_uni, rgt_uni,
    mixedCoefficients, scaledCoefficients, Finset.prod_map, RelEmbedding.coe_toEmbedding,
    weightUnit, Function.comp_apply] using hm

/-- Taking an ordered subcube of the Koszul direction preserves
cocycles in the same total degree. -/
theorem restrictKoszulIndices_mem_cycles {a : Finset (ChartPair d ⊕ₗ κ) → E}
    (ha : a ∈ (T.complex n z).Z p) :
    restrictKoszulIndices e a ∈ (T.complex (n ∘ e) (z ∘ e)).Z p := by
  refine ⟨T.restrictKoszulIndices_mem_terms e ha.1, ?_⟩
  change wd (T.weights fun l => z (e l)) (restrictKoszulIndices e a) = 0
  rw [T.restrictKoszulIndices_wd e z, show wd (T.weights z) a = 0 from ha.2]
  rfl

omit [AddCommGroup E] in
/-- The Koszul-empty component is independent of the chosen subcube. -/
theorem chartPart_restrictKoszulIndices (a : Finset (ChartPair d ⊕ₗ κ) → E) :
    chartPart (restrictKoszulIndices e a) = chartPart a := by
  funext I
  simp only [chartPart, restrictKoszulIndices, lft_uni, rgt_uni, Finset.map_empty]

/-- Unscaling a selected component commutes with restricting the
weight indices. -/
theorem unscale_restrictKoszulIndices (i j : Fin (d + 1))
    (a : Finset κ → E) (L : Finset κ') :
    (T.scaleColumn (n ∘ e) i j).symm (fun s => a (s.map e.toEmbedding)) L =
      (T.scaleColumn n i j).symm a (L.map e.toEmbedding) := by
  have he : T.normalizationProduct (n ∘ e) i j L =
      T.normalizationProduct n i j (L.map e.toEmbedding) := by
    simp only [normalizationProduct, Finset.prod_map, weightUnit, Function.comp_apply,
      RelEmbedding.coe_toEmbedding]
  change T.act ((T.normalizationProduct (n ∘ e) i j L)⁻¹ : Sˣ) (a (L.map e.toEmbedding)) = _
  rw [he]
  rfl

end GlobalTheory.WH.WeightedChartSystem
