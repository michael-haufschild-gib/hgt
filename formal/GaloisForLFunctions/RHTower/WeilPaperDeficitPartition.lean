import GaloisForLFunctions.RHTower.WeilPaperCauchyPartition
import GaloisForLFunctions.RHTower.WeilPaperCauchyProfileRecovery

/-!
# Exact deficit conservation under normalized Cauchy sampling

The normalized paper kernels partition one at every actual zero ordinate.
Consequently the discrete profile sums exactly to WP06's native deficit count,
with all multiplicities retained. Poisson recovery has constant one uniformly
in width, lattice site, and every prefix of a fixed height window.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower.WeilSpectral

def paperDeficitPartitionProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) (n : ℤ) : ℝ :=
  ∑ q ∈ (finite_deficitWindow T).toFinset,
    deficitWeight hW q * paperCauchyPartition k n (q.1 : ℂ).im

def recoveredPaperDeficitPartitionProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (b T : ℝ) (n : ℤ) : ℝ :=
  ∑ q ∈ (finite_deficitWindow T).toFinset,
    regularizedDeficitWeight hW b q * paperCauchyPartition k n (q.1 : ℂ).im

def paperDeficitPartitionRecoveryError {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T b : ℝ) : ℝ :=
  ∑' n : ℤ, |recoveredPaperDeficitPartitionProfile hW k b T n -
    paperDeficitPartitionProfile hW k T n|

theorem paperDeficitPartitionProfile_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) (n : ℤ) : 0 ≤ paperDeficitPartitionProfile hW k T n :=
  Finset.sum_nonneg fun q _ =>
    mul_nonneg (deficitWeight_nonneg hW q) (paperCauchyPartition_nonneg _ _ _)

theorem summable_paperDeficitPartitionProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) : Summable (paperDeficitPartitionProfile hW k T) :=
  summable_sum fun q _ => (summable_paperCauchyPartition k (q.1 : ℂ).im).mul_left _

/-- Exact native deficit, independent of probe width or the positions of the zero copies. -/
theorem tsum_paperDeficitPartitionProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) :
    (∑' n : ℤ, paperDeficitPartitionProfile hW k T n) = deficitCount hW T := by
  unfold paperDeficitPartitionProfile
  rw [Summable.tsum_finsetSum (s := (finite_deficitWindow T).toFinset) (fun q _ =>
    (summable_paperCauchyPartition k (q.1 : ℂ).im).mul_left (deficitWeight hW q))]
  simp only [tsum_mul_left, tsum_paperCauchyPartition, mul_one]
  rw [deficitCount_eq_sum_window hW le_rfl]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Set.Finite.mem_toFinset] at hq
  exact (if_pos hq).symm

theorem frequently_small_partitionProfile_iff_deficitCount {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) :
    (∀ η > 0, ∃ᶠ T in atTop, (∑' n : ℤ, paperDeficitPartitionProfile hW k T n) / T ≤ η) ↔
      (∀ η > 0, ∃ᶠ T in atTop, deficitCount hW T / T ≤ η) := by
  simp only [tsum_paperDeficitPartitionProfile]

theorem summable_recoveredPaperDeficitPartitionProfile {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (b T : ℝ) :
    Summable (recoveredPaperDeficitPartitionProfile hW k b T) :=
  summable_sum fun q _ => (summable_paperCauchyPartition k (q.1 : ℂ).im).mul_left _

private theorem profile_abs_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (b T : ℝ) (n : ℤ) :
    |recoveredPaperDeficitPartitionProfile hW k b T n - paperDeficitPartitionProfile hW k T n| ≤
      ∑ q ∈ (finite_deficitWindow T).toFinset,
        |regularizedDeficitWeight hW b q - deficitWeight hW q| *
          paperCauchyPartition k n (q.1 : ℂ).im := by
  rw [recoveredPaperDeficitPartitionProfile, paperDeficitPartitionProfile,
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro q _
  rw [← sub_mul, abs_mul, abs_of_nonneg (paperCauchyPartition_nonneg _ _ _)]

private theorem summable_error_majorant {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (b T : ℝ) :
    Summable (fun n : ℤ => ∑ q ∈ (finite_deficitWindow T).toFinset,
      |regularizedDeficitWeight hW b q - deficitWeight hW q| *
        paperCauchyPartition k n (q.1 : ℂ).im) :=
  summable_sum fun q _ => (summable_paperCauchyPartition k (q.1 : ℂ).im).mul_left _

theorem summable_abs_paperDeficitPartitionProfile_error {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (b T : ℝ) :
    Summable (fun n : ℤ => |recoveredPaperDeficitPartitionProfile hW k b T n -
      paperDeficitPartitionProfile hW k T n|) :=
  (summable_error_majorant hW k b T).of_nonneg_of_le (fun _ => abs_nonneg _)
    (profile_abs_sub_le hW k b T)

theorem paperDeficitPartitionRecoveryError_nonneg {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (T b : ℝ) :
    0 ≤ paperDeficitPartitionRecoveryError hW k T b := tsum_nonneg fun _ => abs_nonneg _

/-- No amplification of atom-recovery error at any lattice width. -/
theorem paperDeficitPartitionRecoveryError_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (T b : ℝ) :
    paperDeficitPartitionRecoveryError hW k T b ≤ deficitRecoveryError hW T b := by
  calc
    _ ≤ ∑' n : ℤ, ∑ q ∈ (finite_deficitWindow T).toFinset,
        |regularizedDeficitWeight hW b q - deficitWeight hW q| *
          paperCauchyPartition k n (q.1 : ℂ).im :=
      (summable_abs_paperDeficitPartitionProfile_error hW k b T).tsum_le_tsum
        (profile_abs_sub_le hW k b T) (summable_error_majorant hW k b T)
    _ = _ := by
      rw [Summable.tsum_finsetSum (s := (finite_deficitWindow T).toFinset)
        (fun q _ => (summable_paperCauchyPartition k (q.1 : ℂ).im).mul_left _)]
      simp only [tsum_mul_left, tsum_paperCauchyPartition, mul_one, deficitRecoveryError]

theorem tendsto_paperDeficitPartitionRecoveryError {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (T : ℝ) :
    Tendsto (paperDeficitPartitionRecoveryError hW k T) (𝓝[>] 0) (𝓝 0) :=
  squeeze_zero (paperDeficitPartitionRecoveryError_nonneg hW k T)
    (paperDeficitPartitionRecoveryError_le hW k T) (tendsto_deficitRecoveryError hW T)

/-- One scale works for all widths, all lattice sites, and every bounded-height prefix. -/
theorem exists_uniform_paperDeficitPartitionRecovery_scale {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (M : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ b : ℝ, 0 < b → b < δ →
      ∀ k : ℕ, ∀ T : ℝ, T ≤ M → paperDeficitPartitionRecoveryError hW k T b < ε := by
  intro ε hε
  have hev := (tendsto_deficitRecoveryError hW M).eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨δ, hδ, fun b hb hbδ k T hTM => ?_⟩
  have he : deficitRecoveryError hW T b ≤ deficitRecoveryError hW M b := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rw [Set.Finite.mem_toFinset] at hq ⊢
      exact ⟨hq.1, hq.2.trans hTM⟩
    · intro q _ _
      exact abs_nonneg _
  exact ((paperDeficitPartitionRecoveryError_le hW k T b).trans he).trans_lt (hsub ⟨hb, hbδ⟩)

end RHTower.WeilSpectral
