import GaloisForLFunctions.HTGeometry.PaperGenealogyFiberDefects
import GaloisForLFunctions.HTGeometry.LpHilbertFiberMasks

/-! # Complete channel-masked observations of certificate genealogies

Finite histories recover genealogy, adjoint and Gram uniformly over every
fixed per-depth energy envelope. Even the attained worst channel mask loses
the defect; the full genealogy error keeps its compact-ideal obstruction.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology
open scoped ENNReal
variable {d : ℕ}

theorem paperGenealogy_uniform_fiberHull (a : OpCertStream d) (x : FibSeq d) :
    TendstoUniformlyOn (fun N y => paperGenealogyError a N y) (fun _ => 0)
      atTop (lpFiberSolidHull x) :=
  tendstoUniformlyOn_lpFiberSolidHull _ _ (by positivity)
    (paperGenealogyError_norm_le a) (paperGenealogyError_strong a) x

theorem paperGenealogyAdjoint_uniform_fiberHull (a : OpCertStream d) (x : FibSeq d) :
    TendstoUniformlyOn (fun N y => paperGenealogyAdjointError a N y) (fun _ => 0)
      atTop (lpFiberSolidHull x) :=
  tendstoUniformlyOn_lpFiberSolidHull _ _ (by positivity)
    (paperGenealogyAdjointError_norm_le a) (paperGenealogyAdjointError_strong a) x

theorem paperGenealogyGram_uniform_fiberHull (a : OpCertStream d) (x : FibSeq d) :
    TendstoUniformlyOn (fun N y => paperGenealogyGramError a N y) (fun _ => 0)
      atTop (lpFiberSolidHull x) :=
  tendstoUniformlyOn_lpFiberSolidHull _ _ (by positivity)
    (paperGenealogyGramError_norm_le a) (paperGenealogyGramError_strong a) x

theorem paperGenealogy_fiberObservation_tendsto (a : OpCertStream d) (x : FibSeq d) :
    Tendsto (fun N => lpFiberObservation (paperGenealogyError a N) x) atTop (𝓝 0) :=
  tendsto_lpFiberObservation _ _ (by positivity)
    (paperGenealogyError_norm_le a) (paperGenealogyError_strong a) x

theorem paperGenealogyAdjoint_fiberObservation_tendsto (a : OpCertStream d) (x : FibSeq d) :
    Tendsto (fun N => lpFiberObservation (paperGenealogyAdjointError a N) x) atTop (𝓝 0) :=
  tendsto_lpFiberObservation _ _ (by positivity)
    (paperGenealogyAdjointError_norm_le a) (paperGenealogyAdjointError_strong a) x

theorem paperGenealogyGram_fiberObservation_tendsto (a : OpCertStream d) (x : FibSeq d) :
    Tendsto (fun N => lpFiberObservation (paperGenealogyGramError a N) x) atTop (𝓝 0) :=
  tendsto_lpFiberObservation _ _ (by positivity)
    (paperGenealogyGramError_norm_le a) (paperGenealogyGramError_strong a) x

theorem paperGenealogy_moving_fiberMask_tendsto (a : OpCertStream d) (x : FibSeq d)
    (m : ℕ → LpFiberMask (fun _ : ℕ => Fib d)) :
    Tendsto (fun N => paperGenealogyError a N (lpFiberMaskedHistory x (m N))) atTop (𝓝 0) :=
  tendsto_moving_lpFiberMaskedHistory _ _ (by positivity)
    (paperGenealogyError_norm_le a) (paperGenealogyError_strong a) x m

theorem paperGenealogyAdjoint_moving_fiberMask_tendsto (a : OpCertStream d) (x : FibSeq d)
    (m : ℕ → LpFiberMask (fun _ : ℕ => Fib d)) :
    Tendsto (fun N => paperGenealogyAdjointError a N (lpFiberMaskedHistory x (m N))) atTop (𝓝 0) :=
  tendsto_moving_lpFiberMaskedHistory _ _ (by positivity)
    (paperGenealogyAdjointError_norm_le a) (paperGenealogyAdjointError_strong a) x m

theorem paperGenealogyGram_moving_fiberMask_tendsto (a : OpCertStream d) (x : FibSeq d)
    (m : ℕ → LpFiberMask (fun _ : ℕ => Fib d)) :
    Tendsto (fun N => paperGenealogyGramError a N (lpFiberMaskedHistory x (m N))) atTop (𝓝 0) :=
  tendsto_moving_lpFiberMaskedHistory _ _ (by positivity)
    (paperGenealogyGramError_norm_le a) (paperGenealogyGramError_strong a) x m

/-- The full channel-mask maximum is attained, not only a supremal bound. -/
theorem paperGenealogy_fiberObservation_attained (a : OpCertStream d) (N : ℕ) (x : FibSeq d) :
    (∃ m : LpFiberMask (fun _ : ℕ => Fib d),
      ‖paperGenealogyError a N (lpFiberMaskedHistory x m)‖ = lpFiberObservation (paperGenealogyError a N) x) ∧
    (∃ m : LpFiberMask (fun _ : ℕ => Fib d),
      ‖paperGenealogyAdjointError a N (lpFiberMaskedHistory x m)‖ =
        lpFiberObservation (paperGenealogyAdjointError a N) x) ∧
    (∃ m : LpFiberMask (fun _ : ℕ => Fib d),
      ‖paperGenealogyGramError a N (lpFiberMaskedHistory x m)‖ =
        lpFiberObservation (paperGenealogyGramError a N) x) :=
  ⟨lpFiberObservation_mask_attained _ x, lpFiberObservation_mask_attained _ x,
    lpFiberObservation_mask_attained _ x⟩

/-- Uniform masked recovery coexists with the full norm and ideal-cost gaps. -/
theorem paperGenealogy_fiberCompletion (d : ℕ) (a : OpCertStream (d + 1)) (x : FibSeq (d + 1)) :
    (∀ N, 1 ≤ ‖paperGenealogyError a N‖) ∧
    (∀ N, compactOperatorTraceCost (FibSeq (d + 1)) (paperGenealogyError a N) = ∞) ∧
    Tendsto (fun N => lpFiberObservation (paperGenealogyError a N) x) atTop (𝓝 0) ∧
    Tendsto (fun N => lpFiberObservation (paperGenealogyAdjointError a N) x) atTop (𝓝 0) ∧
    Tendsto (fun N => lpFiberObservation (paperGenealogyGramError a N) x) atTop (𝓝 0) :=
  ⟨paperGenealogyError_norm_gap d a, paperGenealogyError_traceCost d a,
    paperGenealogy_fiberObservation_tendsto a x, paperGenealogyAdjoint_fiberObservation_tendsto a x,
    paperGenealogyGram_fiberObservation_tendsto a x⟩

end
end GaloisForLFunctions.HTGeometry
