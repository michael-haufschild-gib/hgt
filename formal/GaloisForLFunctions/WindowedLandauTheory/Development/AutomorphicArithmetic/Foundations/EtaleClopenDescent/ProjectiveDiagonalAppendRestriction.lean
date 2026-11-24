import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAppendScaling
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartProjection
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCoverSubcovers

/-! Dropping the appended weights is a cochain map to the base
diagonal complex, with the same Čech component. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E κ : Type} [Field k] [Field F] [Field E] [LinearOrder κ]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (q p : ℕ)
  {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}

local notation "V" => ExteriorDifferentials k E q ⊗[k] ExteriorDifferentials k E p
local notation "T" => diagonalChartSystem (E := E) h q p
local notation "W" => normalizedDiagonalSystem (E := E) h q p
local notation "n₀" => (fun _ : DiagonalIndex d => ((1, 1) : ℕ × ℕ))

/-- Restrict a cochain to the chart indices and the base-coordinate weights. -/
def restrictAppendedDiagonal (c : Finset (ChartPair d ⊕ₗ (κ ⊕ₗ DiagonalIndex d)) → V)
    (s : Finset (ChartPair d ⊕ₗ DiagonalIndex d)) : V :=
  c (uni (lft s) (uni ∅ (rgt s)))

theorem restrictAppendedDiagonal_mem_cycles
    {c : Finset (ChartPair d ⊕ₗ (κ ⊕ₗ DiagonalIndex d)) → V} {m : ℤ}
    (hc : c ∈ ((W).complex (appendedDiagonalDegrees n) (appendedDiagonalWeights h q p z)).Z m) :
    restrictAppendedDiagonal q p c ∈ ((T).complex n₀ (T).homogeneousMinor).Z m := by
  let a := appendedDiagonalWeights h q p z
  refine ⟨acx_mem_terms_iff.mpr (fun s => ?_), ?_⟩
  · obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
    have hm := acx_mem_terms_iff.mp hc.1 (uni B (uni ∅ L))
    simpa only [restrictAppendedDiagonal, lft_uni, rgt_uni, card_uni, Finset.card_empty,
      zero_add, mixedCoefficients, appendedDiagonal_scaledCoefficients_restrict h q p n] using hm
  · let e : DiagonalIndex d ↪o (κ ⊕ₗ DiagonalIndex d) := joinedRight
    have he (L : Finset (DiagonalIndex d)) : L.map e.toEmbedding = uni ∅ L :=
      map_joinedRight L
    have hres : restrictAppendedDiagonal q p c = restrictKoszulIndices e c := by
      funext s
      rw [restrictAppendedDiagonal, restrictKoszulIndices, he]
    have hw : (W).weights (fun l => a (e l)) = (T).weights (T).homogeneousMinor := by
      funext s
      rcases hs : ofLex s with b | l
      · simp only [weights, hs, Sum.elim_inl, map_one]
      · simp only [weights, hs, Sum.elim_inr]
        change (W).act ((W).homogeneousMinor l) = _
        rw [normalizedDiagonalSystem_homogeneousMinor]
        exact tensorScalarAction_diagonalScalarMap _
    change wd ((T).weights (T).homogeneousMinor) (restrictAppendedDiagonal q p c) = 0
    rw [hres, ← hw, (W).restrictKoszulIndices_wd e a c, show wd ((W).weights a) c = 0 from hc.2]
    rfl

end GlobalTheory.PD

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E κ : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] [LinearOrder κ] [Fintype κ] {d : ℕ}
  (T : WeightedChartSystem k d S E) {n : κ → ℕ × ℕ} {z : κ → S}

/-- Two nonempty chart index sets consume at least two degrees. -/
theorem lev_rightIndices_of_mem_complex_terms {m : ℤ}
    {c : Finset (ChartPair d ⊕ₗ κ) → E} (hc : c ∈ (T.complex n z).C (m + 2)) :
    Lev rightIndices (· ≤ m) c := by
  intro s hs
  obtain ⟨B, L, rfl⟩ : ∃ B L, s = uni B L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  have hcard : (((uni B L ∩ rightIndices).card : ℕ) : ℤ) = L.card :=
    congrArg (fun b : ℕ => (b : ℤ)) (card_inter_rightIndices B L)
  have hL : m < (L.card : ℤ) := lt_of_not_ge (fun he => hs (hcard.symm ▸ he))
  have hm := acx_mem_terms_iff.mp hc (uni B L)
  by_cases hB : (lft B).Nonempty ∧ (rgt B).Nonempty
  · have hsize : B.card = (lft B).card + (rgt B).card :=
      (congrArg Finset.card (uni_lft_rgt B)).symm.trans (card_uni _ _)
    have hleft := Finset.card_pos.mpr hB.1
    have hright := Finset.card_pos.mpr hB.2
    have hbad : ((uni B L).card : ℤ) ≠ m + 2 := by rw [card_uni, hsize]; omega
    exact (Submodule.mem_bot k).mp (by simpa only [if_neg hbad] using hm)
  · exact (Submodule.mem_bot k).mp (by
      simpa only [lft_uni, rgt_uni, mixedCoefficients, if_neg hB, ite_self] using hm)

end GlobalTheory.WH.WeightedChartSystem
