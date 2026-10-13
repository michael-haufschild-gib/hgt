import GaloisForLFunctions.HTGeometry.DyadicWalshEntries

/-! # A compact operator with the absolute matrix of the half Hardy tail

The norm-convergent sum of all Walsh levels has exactly one contribution
to each strict upper-triangular coefficient. Its sign mask has modulus one.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter QuantumAlg.WalshHadamard
open scoped Topology

def dyadicWalshOperator : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  ∑' k, dyadicWalshLevel k

theorem dyadicWalshOperator_compact : IsCompactOperator dyadicWalshOperator := by
  apply isClosed_setOf_isCompactOperator.mem_of_tendsto
    dyadicWalshLevel_summable.hasSum.tendsto_sum_nat
  apply Eventually.of_forall
  intro N
  have hc (s : Finset ℕ) : IsCompactOperator
      (∑ k ∈ s, dyadicWalshLevel k : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact isCompactOperator_zero
    | @insert k s hk ih =>
        rw [Finset.sum_insert hk]
        exact (dyadicWalshLevel_compact k).add ih
  exact hc _

def dyadicWalshSign (n j : ℕ) : ℂ :=
  if n < j then
    walshSign ⟨n % 2 ^ dyadicSiblingLevel n j, Nat.mod_lt _ (by positivity)⟩
      ⟨j % 2 ^ dyadicSiblingLevel n j, Nat.mod_lt _ (by positivity)⟩ else 1

theorem dyadicWalshSign_norm (n j : ℕ) : ‖dyadicWalshSign n j‖ = 1 := by
  unfold dyadicWalshSign
  split_ifs <;> simp

theorem dyadicWalshSign_eq_one_or_neg_one (n j : ℕ) :
    dyadicWalshSign n j = 1 ∨ dyadicWalshSign n j = -1 := by
  unfold dyadicWalshSign walshSign
  split_ifs <;> simp

theorem dyadicWalshOperator_single (n j : ℕ) :
    dyadicWalshOperator (lp.single 2 j 1) n =
      dyadicWalshSign n j *
        (if n < j then ((2 * (j : ℝ) + 2)⁻¹ : ℝ) else 0) := by
  let ev : (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).comp
      (ContinuousLinearMap.apply ℂ (lp (fun _ : ℕ => ℂ) 2) (lp.single 2 j 1))
  have he : dyadicWalshOperator (lp.single 2 j 1) n = ∑' k, dyadicWalshEntry k n j := by
    change ev (∑' k, dyadicWalshLevel k) = _
    rw [ev.map_tsum dyadicWalshLevel_summable]
    exact tsum_congr fun k => dyadicWalshLevel_single k n j
  rw [he]
  by_cases h : n < j
  · rw [if_pos h, tsum_eq_single (dyadicSiblingLevel n j)]
    · simp [dyadicWalshEntry, dyadicSibling_level h, dyadicWalshSign, h]
    · intro k hk
      have hs : ¬ DyadicSibling k n j := fun hs => hk ((dyadicSibling_iff_level h).mp hs)
      simp [dyadicWalshEntry, hs]
  · have hs (k : ℕ) : ¬ DyadicSibling k n j := fun hs => h hs.lt
    simp [dyadicWalshEntry, hs, h]

end
end GaloisForLFunctions.HTGeometry
