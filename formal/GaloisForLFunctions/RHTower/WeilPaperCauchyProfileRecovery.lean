import GaloisForLFunctions.RHTower.WeilPaperCauchyDeficitProfile

/-!
# Recovery of the entire Cauchy deficit profile from Poisson atom approximations

The native regularized deficit weights use values of the actual Weil continuation.
Their finite-window recovery error controls the `ℓ¹` error across every integer
sample simultaneously. Recovery is uniform over all prefixes of a fixed height
window; no rate uniform in unbounded height is introduced.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace RHTower.WeilSpectral

/-- The sampled profile formed from the native Poisson atom-recovery weights. -/
def recoveredPaperDeficitCauchyProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (b T : ℝ) (n : ℤ) : ℝ :=
  ∑ q ∈ (finite_deficitWindow T).toFinset,
    regularizedDeficitWeight hW b q * paperCauchyKernel k ((n : ℝ) - (q.1 : ℂ).im)

/-- Total absolute recovery error over the whole sampling lattice. -/
def paperCauchyProfileRecoveryError {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T b : ℝ) : ℝ :=
  ∑' n : ℤ, |recoveredPaperDeficitCauchyProfile hW k b T n - paperDeficitCauchyProfile hW k T n|

theorem summable_recoveredPaperDeficitCauchyProfile {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (b T : ℝ) :
    Summable (recoveredPaperDeficitCauchyProfile hW k b T) :=
  summable_sum fun q _ =>
    (summable_paperCauchyKernel_lattice k (q.1 : ℂ).im).mul_left (regularizedDeficitWeight hW b q)

private theorem profile_abs_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (b T : ℝ) (n : ℤ) :
    |recoveredPaperDeficitCauchyProfile hW k b T n - paperDeficitCauchyProfile hW k T n| ≤
      ∑ q ∈ (finite_deficitWindow T).toFinset,
        |regularizedDeficitWeight hW b q - deficitWeight hW q| *
          paperCauchyKernel k ((n : ℝ) - (q.1 : ℂ).im) := by
  rw [recoveredPaperDeficitCauchyProfile, paperDeficitCauchyProfile, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro q _
  rw [← sub_mul, abs_mul, abs_of_nonneg (paperCauchyKernel_nonneg _ _)]

private theorem summable_error_majorant {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (b T : ℝ) :
    Summable (fun n : ℤ => ∑ q ∈ (finite_deficitWindow T).toFinset,
      |regularizedDeficitWeight hW b q - deficitWeight hW q| *
        paperCauchyKernel k ((n : ℝ) - (q.1 : ℂ).im)) :=
  summable_sum fun q _ => (summable_paperCauchyKernel_lattice k (q.1 : ℂ).im).mul_left _

theorem summable_abs_recoveredPaperDeficitCauchyProfile_sub {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (b T : ℝ) :
    Summable (fun n : ℤ =>
      |recoveredPaperDeficitCauchyProfile hW k b T n - paperDeficitCauchyProfile hW k T n|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (profile_abs_sub_le hW k b T)
    (summable_error_majorant hW k b T)

theorem paperCauchyProfileRecoveryError_nonneg {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (T b : ℝ) :
    0 ≤ paperCauchyProfileRecoveryError hW k T b := tsum_nonneg (fun _ => abs_nonneg _)

/-- The source lattice estimate removes any dependence on the number of recovery sites. -/
theorem paperCauchyProfileRecoveryError_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T b : ℝ) :
    paperCauchyProfileRecoveryError hW k T b ≤
      (2 + Real.pi / ((k : ℝ) + 1)) * deficitRecoveryError hW T b := by
  calc
    _ ≤ ∑' n : ℤ, ∑ q ∈ (finite_deficitWindow T).toFinset,
        |regularizedDeficitWeight hW b q - deficitWeight hW q| *
          paperCauchyKernel k ((n : ℝ) - (q.1 : ℂ).im) :=
      (summable_abs_recoveredPaperDeficitCauchyProfile_sub hW k b T).tsum_le_tsum
        (profile_abs_sub_le hW k b T) (summable_error_majorant hW k b T)
    _ = ∑ q ∈ (finite_deficitWindow T).toFinset,
        |regularizedDeficitWeight hW b q - deficitWeight hW q| *
          ∑' n : ℤ, paperCauchyKernel k ((n : ℝ) - (q.1 : ℂ).im) := by
      rw [Summable.tsum_finsetSum (s := (finite_deficitWindow T).toFinset)
        (fun q _ => (summable_paperCauchyKernel_lattice k (q.1 : ℂ).im).mul_left _)]
      simp only [tsum_mul_left]
    _ ≤ _ := by
      rw [deficitRecoveryError, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q _
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (tsum_paperCauchyKernel_lattice_le k (q.1 : ℂ).im)
        (abs_nonneg (regularizedDeficitWeight hW b q - deficitWeight hW q))

theorem tendsto_paperCauchyProfileRecoveryError {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (T : ℝ) :
    Tendsto (paperCauchyProfileRecoveryError hW k T) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero (paperCauchyProfileRecoveryError_nonneg hW k T)
    (paperCauchyProfileRecoveryError_le hW k T)
  simpa only [mul_zero] using
    (tendsto_deficitRecoveryError hW T).const_mul (2 + Real.pi / ((k : ℝ) + 1))

/-- A single recovery scale controls every sample and every prefix of a fixed height window. -/
theorem exists_uniform_paperCauchyProfileRecovery_scale {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (M : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ b : ℝ, 0 < b → b < δ →
      ∀ T : ℝ, T ≤ M → paperCauchyProfileRecoveryError hW k T b < ε := by
  intro ε hε
  let B := 2 + Real.pi / ((k : ℝ) + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hev := (tendsto_deficitRecoveryError hW M).eventually (gt_mem_nhds (div_pos hε hB))
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨δ, hδ, fun b hb hbδ T hTM => ?_⟩
  have he : deficitRecoveryError hW T b ≤ deficitRecoveryError hW M b := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rw [Set.Finite.mem_toFinset] at hq ⊢
      exact ⟨hq.1, hq.2.trans hTM⟩
    · intro q _ _
      exact abs_nonneg _
  calc
    paperCauchyProfileRecoveryError hW k T b ≤ B * deficitRecoveryError hW T b :=
      paperCauchyProfileRecoveryError_le hW k T b
    _ ≤ B * deficitRecoveryError hW M b := mul_le_mul_of_nonneg_left he hB.le
    _ < B * (ε / B) := mul_lt_mul_of_pos_left (hsub ⟨hb, hbδ⟩) hB
    _ = ε := by field_simp

end RHTower.WeilSpectral
