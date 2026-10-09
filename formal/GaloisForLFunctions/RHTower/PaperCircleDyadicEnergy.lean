import GaloisForLFunctions.RHTower.PaperCircleJointEnergy
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Dyadic.Lift
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Dyadic.Discrete

/-! # Compatible finite-grid energy witnesses for native circle symbols

Cell averaging preserves the whole family's integrated energy exactly. Its common
local-energy anchor selects a nested good cell at every dyadic resolution.
-/

open MeasureTheory Set
open scoped BigOperators
open GaloisForLFunctions.HTGeometry.FourierLLogL.Period
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

private theorem square_integrableOn (a : CCMCircleBoundedSymbol) (b c : ℝ) :
    IntegrableOn (fun x : ℝ => ‖a (x : AddCircle (1 : ℝ))‖ ^ 2) (Ico b c) := by
  refine seg_integrable _ ((a.measurable.comp AddCircle.measurable_mk').norm.pow_const 2)
    (a.bound ^ 2) b c (fun x _ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (a.norm_le _) 2

private theorem family_square_integrable (a : ι → CCMCircleBoundedSymbol) :
    Integrable (fun x : ℝ => ∑ i, ‖a i (x : AddCircle (1 : ℝ))‖ ^ 2) μ₁ :=
  integrable_finsetSum Finset.univ fun i _ => square_integrableOn (a i) 0 1

/-- The actual family energy averaged over each dyadic cell. -/
def paperCircleGridEnergy (a : ι → CCMCircleBoundedSymbol) (M : ℕ) : Grid M → ℝ :=
  liftGrid M (fun x : ℝ => ∑ i, ‖a i (x : AddCircle (1 : ℝ))‖ ^ 2)

theorem paperCircleGridEnergy_nonneg (a : ι → CCMCircleBoundedSymbol)
    (M : ℕ) (y : Grid M) : 0 ≤ paperCircleGridEnergy a M y := by
  exact (lift_bounds (family_square_integrable a)
    (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) (∑ i, (a i).bound ^ 2)
    (fun x => Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) ((a i).norm_le _) 2) y).1

theorem paperCircleGridEnergy_le (a : ι → CCMCircleBoundedSymbol)
    (M : ℕ) (y : Grid M) : paperCircleGridEnergy a M y ≤ ∑ i, (a i).bound ^ 2 := by
  exact (lift_bounds (family_square_integrable a)
    (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) (∑ i, (a i).bound ^ 2)
    (fun x => Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) ((a i).norm_le _) 2) y).2

/-- Every finite resolution retains exactly the native integrated energy. -/
theorem expU_paperCircleGridEnergy (a : ι → CCMCircleBoundedSymbol) (M : ℕ) :
    expU (paperCircleGridEnergy a M) = paperCircleFamilyEnergy a := by
  rw [paperCircleGridEnergy, expU_liftGrid M _ (family_square_integrable a)]
  exact integral_paperCircleFamilySquaredNorm a

/-- The finite Fourier zero mode is independent of resolution. -/
theorem fc_zero_paperCircleGridEnergy (a : ι → CCMCircleBoundedSymbol) (M : ℕ) :
    fc (fun y : Grid M => (paperCircleGridEnergy a M y : ℂ)) 0 =
      (paperCircleFamilyEnergy a : ℂ) := by
  unfold fc
  simp only [neg_zero, chi_zero_left, mul_one]
  rw [expU_real, expU_paperCircleGridEnergy]

/-- One continuous anchor produces compatible good cells at every finite resolution.
The threshold depends only on integrated family energy, not on resolution or depth. -/
theorem paperCircleGridEnergy_good_thread (a : ι → CCMCircleBoundedSymbol) :
    ∃ x ∈ Ico (0 : ℝ) 1, ∃ y : (M : ℕ) → Grid M,
      (∀ M, x ∈ atom (y M)) ∧
      (∀ M, atom (y (M + 1)) ⊆ atom (y M)) ∧
      ∀ M, finGood (128 * (1 + paperCircleFamilyEnergy a)) M
        (paperCircleGridEnergy a M) (y M) := by
  classical
  obtain ⟨x, hx, hlocal⟩ := paperCircleFamilyEnergy_good_anchor a
  have hcell (M : ℕ) : ∃ z : Grid M, x ∈ atom z := by
    have h : x ∈ unitInt := hx
    rw [atom_partition M] at h
    exact mem_iUnion.mp h
  choose y hy using hcell
  refine ⟨x, hx, y, hy, ?_, ?_⟩
  · intro M z hz
    exact (coarse_const (p := vertex (y M)) (q := vertex (y (M + 1)))
      (by change M ≤ M + 1; omega) (hy (M + 1)) hz).mp (hy M)
  · intro M p hp hl hpy
    have hpx := (atom_iff_coarse p hl.le (hy M)).mpr hpy
    have H := hlocal p.a p.len p.len_pos (side_le _) hpx
    rw [paperCircleGridEnergy, avg_liftGrid _ (family_square_integrable a) hp hl.le]
    change p.len⁻¹ * (∫ z in Ico p.a (p.a + p.len),
      ∑ i, ‖a i (z : AddCircle (1 : ℝ))‖ ^ 2) ≤ _
    rw [integral_finsetSum Finset.univ
      (fun i _ => square_integrableOn (a i) p.a (p.a + p.len))]
    calc
      _ ≤ p.len⁻¹ * (128 * p.len * (1 + paperCircleFamilyEnergy a)) :=
        mul_le_mul_of_nonneg_left H (inv_pos.mpr p.len_pos).le
      _ = 128 * (p.len⁻¹ * p.len) * (1 + paperCircleFamilyEnergy a) := by ring
      _ = _ := by rw [inv_mul_cancel₀ p.len_pos.ne', mul_one]

end
end RHTower
