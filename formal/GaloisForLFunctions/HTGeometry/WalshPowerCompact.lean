import GaloisForLFunctions.HTGeometry.WalshPowerEntries

/-! # Compact Walsh signing of separated power kernels

The complete operator is constructed by a norm-summable series; no bounded
or compact realization is assumed. Every coefficient is retained exactly.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter
open scoped Topology

namespace WalshPowerKernel

def operator (D : WalshPowerKernel) : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  ∑' k, D.level k

theorem operator_compact (D : WalshPowerKernel) : IsCompactOperator D.operator := by
  apply isClosed_setOf_isCompactOperator.mem_of_tendsto D.level_summable.hasSum.tendsto_sum_nat
  apply Eventually.of_forall
  intro N
  have hc (s : Finset ℕ) : IsCompactOperator
      (∑ k ∈ s, D.level k : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact isCompactOperator_zero
    | @insert k s hk ih =>
        rw [Finset.sum_insert hk]
        exact (D.level_compact k).add ih
  exact hc _

theorem operator_single (D : WalshPowerKernel) (n j : ℕ) :
    D.operator (lp.single 2 j 1) n =
      dyadicWalshSign n j * (if n < j then D.row n * D.column j else 0) := by
  let ev : (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).comp
      (ContinuousLinearMap.apply ℂ (lp (fun _ : ℕ => ℂ) 2) (lp.single 2 j 1))
  have he : D.operator (lp.single 2 j 1) n = ∑' k, D.levelEntry k n j := by
    change ev (∑' k, D.level k) = _
    rw [ev.map_tsum D.level_summable]
    exact tsum_congr fun k => D.level_single k n j
  rw [he]
  by_cases h : n < j
  · rw [if_pos h, tsum_eq_single (dyadicSiblingLevel n j)]
    · simp [levelEntry, dyadicSibling_level h, dyadicWalshSign, h]
    · intro k hk
      have hs : ¬ DyadicSibling k n j := fun hs => hk ((dyadicSibling_iff_level h).mp hs)
      simp [levelEntry, hs]
  · have hs (k : ℕ) : ¬ DyadicSibling k n j := fun hs => h hs.lt
    simp [levelEntry, hs, h]

theorem operator_abs_entry (D : WalshPowerKernel) (n j : ℕ) :
    ‖D.operator (lp.single 2 j 1) n‖ = ‖if n < j then D.row n * D.column j else 0‖ := by
  rw [D.operator_single, norm_mul, dyadicWalshSign_norm, one_mul]

end WalshPowerKernel
end
end GaloisForLFunctions.HTGeometry
