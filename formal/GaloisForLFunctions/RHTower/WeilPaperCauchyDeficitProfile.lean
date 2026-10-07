import GaloisForLFunctions.RHTower.WeilPaperCauchyLattice
import GaloisForLFunctions.RHTower.WeilWorkDeficitSharedMass

/-!
# A Cauchy profile equivalent to the actual Weil deficit

Every multiplicity copy contributes its actual deficit times a Cauchy probe.
The lattice upper bound and nearest-integer lower bound compare the total
sampled profile with `deficitCount` in both directions. Consequently the
frequent small-density target of WP06 is equivalent to the same target for
this smooth profile. No decay of either quantity is assumed or asserted.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace RHTower.WeilSpectral

/-- The actual deficit of every zero copy spread across integer Cauchy probes. -/
def paperDeficitCauchyProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) (n : ℤ) : ℝ :=
  ∑ q ∈ (finite_deficitWindow T).toFinset,
    deficitWeight hW q * paperCauchyKernel k ((n : ℝ) - (q.1 : ℂ).im)

/-- Total sampled deficit, retaining all multiplicities. -/
def paperDeficitCauchyMass {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) : ℝ := ∑' n : ℤ, paperDeficitCauchyProfile hW k T n

theorem paperDeficitCauchyProfile_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) (n : ℤ) : 0 ≤ paperDeficitCauchyProfile hW k T n :=
  Finset.sum_nonneg fun q _ =>
    mul_nonneg (deficitWeight_nonneg hW q) (paperCauchyKernel_nonneg _ _)

theorem summable_paperDeficitCauchyProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) : Summable (paperDeficitCauchyProfile hW k T) :=
  summable_sum fun q _ =>
    (summable_paperCauchyKernel_lattice k (q.1 : ℂ).im).mul_left (deficitWeight hW q)

theorem paperDeficitCauchyMass_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) : 0 ≤ paperDeficitCauchyMass hW k T :=
  tsum_nonneg (paperDeficitCauchyProfile_nonneg hW k T)

/-- Exact resummation over the actual finite zero-copy window. -/
theorem paperDeficitCauchyMass_eq_sum {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) :
    paperDeficitCauchyMass hW k T =
      ∑ q ∈ (finite_deficitWindow T).toFinset,
        deficitWeight hW q * ∑' n : ℤ, paperCauchyKernel k ((n : ℝ) - (q.1 : ℂ).im) := by
  unfold paperDeficitCauchyMass paperDeficitCauchyProfile
  rw [Summable.tsum_finsetSum (fun q _ =>
    (summable_paperCauchyKernel_lattice k (q.1 : ℂ).im).mul_left (deficitWeight hW q))]
  simp only [tsum_mul_left]

private theorem count_eq_window_sum {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) :
    deficitCount hW T = ∑ q ∈ (finite_deficitWindow T).toFinset, deficitWeight hW q := by
  rw [deficitCount_eq_sum_window hW le_rfl]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Set.Finite.mem_toFinset] at hq
  exact if_pos hq

/-- No finite-window cardinality loss occurs in the total profile. -/
theorem paperDeficitCauchyMass_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) :
    paperDeficitCauchyMass hW k T ≤ (2 + Real.pi / ((k : ℝ) + 1)) * deficitCount hW T := by
  rw [paperDeficitCauchyMass_eq_sum, count_eq_window_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (tsum_paperCauchyKernel_lattice_le k (q.1 : ℂ).im) (deficitWeight_nonneg hW q)

/-- Sampling cannot hide deficit: one nearest lattice site captures a fixed fraction. -/
theorem paperCauchyKernel_half_mul_deficitCount_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) (T : ℝ) :
    paperCauchyKernel k (1 / 2) * deficitCount hW T ≤ paperDeficitCauchyMass hW k T := by
  rw [paperDeficitCauchyMass_eq_sum, count_eq_window_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (paperCauchyKernel_half_le_lattice k (q.1 : ℂ).im) (deficitWeight_nonneg hW q)

/-- At unit width the lower comparison is the numerical factor `4 / 5`. -/
theorem four_deficitCount_le_five_cauchyMass {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (T : ℝ) :
    4 * deficitCount hW T ≤ 5 * paperDeficitCauchyMass hW 0 T := by
  have h := paperCauchyKernel_half_mul_deficitCount_le hW 0 T
  norm_num [paperCauchyKernel] at h
  linarith

theorem paperDeficitCauchyMass_eq_zero_iff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (k : ℕ) (T : ℝ) : paperDeficitCauchyMass hW k T = 0 ↔ deficitCount hW T = 0 := by
  have hc : 0 < paperCauchyKernel k (1 / 2) := by unfold paperCauchyKernel; positivity
  have hd : 0 ≤ deficitCount hW T := by
    rw [count_eq_window_sum]
    exact Finset.sum_nonneg fun q _ => deficitWeight_nonneg hW q
  constructor
  · intro h
    have hb := paperCauchyKernel_half_mul_deficitCount_le hW k T
    rw [h] at hb
    nlinarith
  · intro h
    have hb := paperDeficitCauchyMass_le hW k T
    rw [h, mul_zero] at hb
    exact le_antisymm hb (paperDeficitCauchyMass_nonneg hW k T)

/-- Exact reformulation of WP06's frequent small-density target at every fixed width. -/
theorem frequently_small_cauchyMass_iff_deficitCount {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (k : ℕ) :
    (∀ η > 0, ∃ᶠ T in atTop, paperDeficitCauchyMass hW k T / T ≤ η) ↔
      (∀ η > 0, ∃ᶠ T in atTop, deficitCount hW T / T ≤ η) := by
  let c := paperCauchyKernel k (1 / 2)
  let B := 2 + Real.pi / ((k : ℝ) + 1)
  have hc : 0 < c := by dsimp [c, paperCauchyKernel]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  constructor
  · intro h η hη
    refine ((eventually_gt_atTop (0 : ℝ)).and_frequently (h (c * η) (mul_pos hc hη))).mono ?_
    intro T hT
    have hb := div_le_div_of_nonneg_right
      (paperCauchyKernel_half_mul_deficitCount_le hW k T) hT.1.le
    rw [mul_div_assoc] at hb
    change c * (deficitCount hW T / T) ≤ paperDeficitCauchyMass hW k T / T at hb
    nlinarith only [hc, hb, hT.2]
  · intro h η hη
    refine ((eventually_gt_atTop (0 : ℝ)).and_frequently (h (η / B) (div_pos hη hB))).mono ?_
    intro T hT
    calc
      paperDeficitCauchyMass hW k T / T ≤ B * (deficitCount hW T / T) := by
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
          (paperDeficitCauchyMass_le hW k T) hT.1.le
      _ ≤ B * (η / B) := mul_le_mul_of_nonneg_left hT.2 hB.le
      _ = η := by field_simp

end RHTower.WeilSpectral
