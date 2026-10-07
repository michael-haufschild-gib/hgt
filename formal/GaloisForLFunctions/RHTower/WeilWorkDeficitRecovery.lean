import GaloisForLFunctions.RHTower.WeilConeSingularDeficitCounting
import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction

/-!
# Uniform recovery of spectral deficits on bounded ordinate windows

The Poisson values of a full-positive system recover its atoms at each critical zero.
The resulting clipped deficits converge uniformly over every prefix of a bounded ordinate
window. The error is controlled by a finite sum over the actual zero copies, including their
multiplicities. No rate uniform in the height of the window is asserted.
-/

open Complex MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable section

namespace RHTower.WeilSpectral

/-- The actual zero copies with positive ordinate at most `T`. -/
abbrev deficitWindow (T : ℝ) : Set XiZeroCopy :=
  {q | 0 < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ T}

theorem finite_deficitWindow (T : ℝ) : (deficitWindow T).Finite := by
  refine (finite_xiZeroCopy_band 0 (abs_nonneg T)).subset ?_
  intro q hq
  change |(q.1 : ℂ).im - 0| ≤ |T|
  rw [sub_zero, abs_of_pos hq.1]
  exact hq.2.trans (le_abs_self T)

/-- The Poisson approximation to the deficit of one zero copy. -/
def regularizedDeficitWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (b : ℝ) (q : XiZeroCopy) : ℝ :=
  if (q.1 : ℂ).re = 1 / 2 then
    max (1 - b * (weilContinuation hW
      (((1 / 2 + b : ℝ) : ℂ) + (q.1 : ℂ).im * I)).re / xiDivisorMult q.1) 0
  else 1

/-- The regularized deficit retains every off-line copy with weight one. -/
def regularizedDeficitCount {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (b T : ℝ) : ℝ :=
  ∑' q, if q ∈ deficitWindow T then regularizedDeficitWeight hW b q else 0

/-- The complete atom-recovery error on a bounded window. -/
def deficitRecoveryError {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (M b : ℝ) : ℝ :=
  ∑ q ∈ (finite_deficitWindow M).toFinset,
    |regularizedDeficitWeight hW b q - deficitWeight hW q|

theorem tendsto_regularizedDeficitWeight {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (q : XiZeroCopy) :
    Tendsto (fun b => regularizedDeficitWeight hW b q) (𝓝[>] 0)
      (𝓝 (deficitWeight hW q)) := by
  by_cases hq : (q.1 : ℂ).re = 1 / 2
  · have h := (tendsto_mul_re_weilContinuation_atom hW (q.1 : ℂ).im).div_const
      (xiDivisorMult q.1 : ℝ)
    simpa only [regularizedDeficitWeight, deficitWeight, if_pos hq, atomShare,
      measureReal_def] using (tendsto_const_nhds.sub h).max tendsto_const_nhds
  · simp only [regularizedDeficitWeight, deficitWeight, if_neg hq]
    exact tendsto_const_nhds

theorem deficitCount_eq_sum_window {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T M : ℝ} (hTM : T ≤ M) :
    deficitCount hW T = ∑ q ∈ (finite_deficitWindow M).toFinset,
      if q ∈ deficitWindow T then deficitWeight hW q else 0 := by
  classical
  unfold deficitCount ordinateWindowWeight
  apply tsum_eq_sum
  intro q hq
  apply if_neg
  intro h
  apply hq
  rw [Set.Finite.mem_toFinset]
  exact ⟨h.1, h.2.trans hTM⟩

theorem regularizedDeficitCount_eq_sum_window {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (b : ℝ) {T M : ℝ} (hTM : T ≤ M) :
    regularizedDeficitCount hW b T = ∑ q ∈ (finite_deficitWindow M).toFinset,
      if q ∈ deficitWindow T then regularizedDeficitWeight hW b q else 0 := by
  classical
  unfold regularizedDeficitCount
  apply tsum_eq_sum
  intro q hq
  apply if_neg
  intro h
  apply hq
  rw [Set.Finite.mem_toFinset]
  exact ⟨h.1, h.2.trans hTM⟩

/-- Exact deficit decomposition, with no window-to-atom replacement. -/
theorem deficitCount_eq_regularized_add_remainder {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (b T : ℝ) :
    deficitCount hW T = regularizedDeficitCount hW b T +
      ∑ q ∈ (finite_deficitWindow T).toFinset,
        (deficitWeight hW q - regularizedDeficitWeight hW b q) := by
  classical
  rw [deficitCount_eq_sum_window hW le_rfl,
    regularizedDeficitCount_eq_sum_window hW b le_rfl, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Set.Finite.mem_toFinset] at hq
  simp only [if_pos hq]
  ring

/-- One finite recovery error controls all prefixes of the same height window. -/
theorem abs_regularizedDeficitCount_sub_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (b : ℝ) {T M : ℝ} (hTM : T ≤ M) :
    |regularizedDeficitCount hW b T - deficitCount hW T| ≤ deficitRecoveryError hW M b := by
  classical
  rw [regularizedDeficitCount_eq_sum_window hW b hTM,
    deficitCount_eq_sum_window hW hTM, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro q _
  by_cases hq : q ∈ deficitWindow T
  · simp only [if_pos hq, le_refl]
  · simp only [if_neg hq, sub_self, abs_zero]
    exact abs_nonneg _

theorem tendsto_deficitRecoveryError {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (M : ℝ) :
    Tendsto (deficitRecoveryError hW M) (𝓝[>] 0) (𝓝 0) := by
  have h : ∀ q : XiZeroCopy,
      Tendsto (fun b => |regularizedDeficitWeight hW b q - deficitWeight hW q|)
        (𝓝[>] 0) (𝓝 0) := fun q => by
    simpa only [sub_self, abs_zero] using ((tendsto_regularizedDeficitWeight hW q).sub
      (tendsto_const_nhds (x := deficitWeight hW q))).abs
  exact (show Tendsto (fun b => ∑ q ∈ (finite_deficitWindow M).toFinset,
    |regularizedDeficitWeight hW b q - deficitWeight hW q|) (𝓝[>] 0) (𝓝 0) from by
      simpa only [Finset.sum_const_zero] using
        tendsto_finsetSum (finite_deficitWindow M).toFinset (fun q _ => h q))

/-- Every bounded family of ordinate prefixes admits one common atom-recovery scale. -/
theorem exists_uniform_deficitRecovery_scale {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b : ℝ, 0 < b → b < δ → ∀ T : ℝ, T ≤ M →
      |regularizedDeficitCount hW b T - deficitCount hW T| < ε := by
  have hev := (tendsto_deficitRecoveryError hW M).eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  exact ⟨δ, hδ, fun b hb hbδ T hTM =>
    (abs_regularizedDeficitCount_sub_le hW b hTM).trans_lt (hsub ⟨hb, hbδ⟩)⟩

end RHTower.WeilSpectral

end
