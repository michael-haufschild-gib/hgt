import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnLevels.HigherOrder
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Earlier affordable dates bought by a local product formula -/

open Set
open scoped NNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels.FirstContactOrder
open LocalPatches (Register)
open PrecisionReturns (firstVisit firstVisit_isLeast)
noncomputable section

/-- For every desired advance `h`, a short local word transfers the actual
first fitting circuit back by `h`, clipped at the observation origin. -/
theorem first_visit_word_advance {n : ℕ} (x : PathShell n) (j : ℕ) :
    let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian _⟩
    let J := 3^j*Fintype.card (PathLabel n)
    ∃ B : ℝ≥0, ∀ (s : ℕ) (a : ℝ) (e h : ℝ), 0 < e → 0 ≤ h →
      firstVisit H a (s+J) (e+(B:ℝ)*h^(j+2)) ≤ max a (firstVisit H a s e-h) := by
  intro H J
  obtain ⟨B,hB⟩ := higher_increment x j
  refine ⟨B,?_⟩
  intro s a e h he hh
  let v := firstVisit H a s e
  let t := max a (v-h)
  have hv := firstVisit_isLeast H a s he
  have htv : t ≤ v := max_le hv.1.1 (sub_le_self _ hh)
  have hdist : |t-v| ≤ h := by
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr htv)]
    linarith only [le_max_right a (v-h)]
  have hd := hB s t v
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist ..).mp hv.1.2
  have htol := add_pos_of_pos_of_nonneg he (mul_nonneg B.property (pow_nonneg hh (j+2)))
  apply (firstVisit_isLeast H a (s+J) htol).2
  exact ⟨le_max_left ..,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr
    (hd.trans (add_le_add hfit (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) hdist _) B.property)))⟩

#print axioms first_visit_word_advance
end
end GaloisForLFunctions.HTGeometry.ReturnLevels.FirstContactOrder
