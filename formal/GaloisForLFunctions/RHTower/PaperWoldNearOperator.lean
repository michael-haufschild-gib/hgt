import GaloisForLFunctions.RHTower.PaperWoldNearEnvelope
import GaloisForLFunctions.HTGeometry.PaperHilbertOffDiagonal
import GaloisForLFunctions.HTGeometry.PaperDiagonalCluster

/-! # The completed signed Wold near-window operator

Summing compact lag operators in norm retains every actual increment and every
admitted interaction. The wider budget `2*t+eta<2` suffices for compactness.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal

abbrev PaperWoldHistory := lp (fun _ : ℕ => ℂ) 2

def paperWoldLagShift (k : ℕ) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  lpCoordinatePullback (fun n => n + k + 1) (fun _ _ h => by dsimp at h; omega)

@[simp] theorem paperWoldLagShift_apply (k : ℕ) (x : PaperWoldHistory) (n : ℕ) :
    paperWoldLagShift k x n = x (n + k + 1) := rfl

theorem paperWoldLagShift_norm_le (k : ℕ) : ‖paperWoldLagShift k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa [paperWoldLagShift, lpCoordinatePullback] using
    lpCoordinatePullbackLinear_norm_le (fun n => n + k + 1) (fun _ _ h => by dsimp at h; omega) x

def paperWoldLagOperator (p : PaperWoldNearParameters) (k : ℕ) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  (lpDiagonalCLM (paperWoldLagCoeff p k) (paperWoldLagMajorant_nonneg p k)
    (paperWoldLagCoeff_bound p k)).comp (paperWoldLagShift k)

@[simp] theorem paperWoldLagOperator_apply (p : PaperWoldNearParameters) (k n : ℕ)
    (x : PaperWoldHistory) :
    paperWoldLagOperator p k x n = paperWoldLagCoeff p k n * x (n + k + 1) := rfl

theorem paperWoldLagOperator_norm_le (p : PaperWoldNearParameters) (k : ℕ) :
    ‖paperWoldLagOperator p k‖ ≤ paperWoldLagMajorant p k := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (norm_lpDiagonalCLM_le _ _ _) (paperWoldLagShift_norm_le k)
      (norm_nonneg _) (paperWoldLagMajorant_nonneg p k)).trans_eq (mul_one _))

theorem paperWoldLagOperator_compact (p : PaperWoldNearParameters) (k : ℕ) :
    IsCompactOperator (paperWoldLagOperator p k) :=
  (isCompactOperator_lpDiagonalCLM (paperWoldLagCoeff p k)
    (paperWoldLagMajorant_nonneg p k) (paperWoldLagCoeff_bound p k)
    (paperWoldLagCoeff_tendsto p k)).comp_clm (paperWoldLagShift k)

theorem paperWoldLagOperator_summable (p : PaperWoldNearParameters) :
    Summable (paperWoldLagOperator p) :=
  Summable.of_norm_bounded (paperWoldLagMajorant_summable p) (paperWoldLagOperator_norm_le p)

def paperWoldNearOperator (p : PaperWoldNearParameters) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  ∑' k, paperWoldLagOperator p k

def paperWoldNearPartial (p : PaperWoldNearParameters) (K : ℕ) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory := ∑ k ∈ Finset.range K, paperWoldLagOperator p k

theorem paperWoldNearPartial_tendsto (p : PaperWoldNearParameters) :
    Tendsto (paperWoldNearPartial p) atTop (𝓝 (paperWoldNearOperator p)) :=
  (paperWoldLagOperator_summable p).hasSum.tendsto_sum_nat

theorem paperWoldNearPartial_compact (p : PaperWoldNearParameters) (K : ℕ) :
    IsCompactOperator (paperWoldNearPartial p K) := by
  have hsum (s : Finset ℕ) : IsCompactOperator
      (∑ k ∈ s, paperWoldLagOperator p k : PaperWoldHistory →L[ℂ] PaperWoldHistory) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact isCompactOperator_zero
    | @insert k s hk ih =>
        rw [Finset.sum_insert hk]
        convert (paperWoldLagOperator_compact p k).add ih using 1
        · congr 1
        · exact FunLike.coe_add _ _
  exact hsum _

theorem paperWoldNearOperator_compact (p : PaperWoldNearParameters) :
    IsCompactOperator (paperWoldNearOperator p) :=
  isClosed_setOf_isCompactOperator.mem_of_tendsto (paperWoldNearPartial_tendsto p)
    (Eventually.of_forall (paperWoldNearPartial_compact p))

theorem paperWoldNearOperator_apply (p : PaperWoldNearParameters) (x : PaperWoldHistory) (n : ℕ) :
    paperWoldNearOperator p x n = ∑' k, paperWoldLagCoeff p k n * x (n + k + 1) := by
  let ev : (PaperWoldHistory →L[ℂ] PaperWoldHistory) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n).comp (ContinuousLinearMap.apply ℂ PaperWoldHistory x)
  exact ev.map_tsum (paperWoldLagOperator_summable p)

theorem paperWoldNearOperator_row (p : PaperWoldNearParameters) (x : PaperWoldHistory) (n : ℕ) :
    paperWoldNearOperator p x n =
      ∑ k ∈ Finset.range ⌊((n : ℝ) + 1) ^ p.eta⌋₊,
        (paperWoldInteraction p n (n + k + 1) : ℂ) * x (n + k + 1) := by
  rw [paperWoldNearOperator_apply]
  rw [tsum_eq_sum (s := Finset.range ⌊((n : ℝ) + 1) ^ p.eta⌋₊) (fun k hk => by
    have hk' : ¬ k + 1 ≤ ⌊((n : ℝ) + 1) ^ p.eta⌋₊ := by
      simp only [Finset.mem_range] at hk
      omega
    simp [paperWoldLagCoeff, hk'])]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k + 1 ≤ ⌊((n : ℝ) + 1) ^ p.eta⌋₊ := by
    have := Finset.mem_range.mp hk
    omega
  simp only [paperWoldLagCoeff, if_pos hk']

theorem paperWoldNearOperator_traceCost (p : PaperWoldNearParameters) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldNearOperator p) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldNearOperator_compact p)

theorem paperWoldNearOperator_distance (p : PaperWoldNearParameters) :
    compactIdealDistance (paperWoldNearOperator p) = 0 :=
  compactIdealDistance_eq_zero_of_isCompactOperator _ (paperWoldNearOperator_compact p)

theorem paperWoldNearOperator_trace_add (p : PaperWoldNearParameters)
    (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) :
    compactOperatorTraceCost PaperWoldHistory (T + paperWoldNearOperator p) =
      compactOperatorTraceCost PaperWoldHistory T :=
  compactOperatorTraceCost_add_compact T ⟨_, paperWoldNearOperator_compact p⟩

theorem paperWoldNearOperator_distance_add (p : PaperWoldNearParameters)
    (T : PaperWoldHistory →L[ℂ] PaperWoldHistory) :
    compactIdealDistance (T + paperWoldNearOperator p) = compactIdealDistance T :=
  paperCompactIdealDistance_add_compact T ⟨_, paperWoldNearOperator_compact p⟩

end
end RHTower
