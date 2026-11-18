import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionMellin
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The Fourier multiplier of the logarithmic floor discrepancy

The floor primitive on a line of real part σ decays exponentially at both
ends of the logarithmic axis. Its Fourier multiplier is ζ(s)/s.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- The logarithmic floor discrepancy on the vertical Mellin line of real part σ. -/
def weightedFloorDiscrepancy (σ v : ℝ) : ℝ := -Real.exp (-σ*v)*Int.fract (Real.exp v)

theorem measurable_weightedFloorDiscrepancy (σ : ℝ) : Measurable (weightedFloorDiscrepancy σ) :=
  (by fun_prop : Measurable fun v : ℝ => -Real.exp (-σ*v)).mul (measurable_fract.comp Real.measurable_exp)

theorem abs_weightedFloorDiscrepancy_le (σ v : ℝ) :
    |weightedFloorDiscrepancy σ v| ≤ Real.exp (-σ*v) ∧
      |weightedFloorDiscrepancy σ v| ≤ Real.exp ((1-σ)*v) := by
  rw [weightedFloorDiscrepancy,abs_mul,abs_neg,abs_of_pos (Real.exp_pos _),abs_of_nonneg (Int.fract_nonneg _)]
  refine ⟨mul_le_of_le_one_right (Real.exp_pos _).le (Int.fract_lt_one _).le,?_⟩
  have hfrac : Int.fract (Real.exp v) ≤ Real.exp v := by
    rw [Int.fract]
    exact sub_le_self _ (by exact_mod_cast Int.floor_nonneg.2 (Real.exp_pos v).le)
  calc _ ≤ Real.exp (-σ*v)*Real.exp v := mul_le_mul_of_nonneg_left hfrac (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem integrable_weightedFloorDiscrepancy {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1) :
    Integrable (weightedFloorDiscrepancy σ) := by
  have hm : AEStronglyMeasurable (weightedFloorDiscrepancy σ) volume :=
    (measurable_weightedFloorDiscrepancy σ).aestronglyMeasurable
  have hneg : IntegrableOn (weightedFloorDiscrepancy σ) (Iic 0) :=
    (integrableOn_exp_mul_Iic (sub_pos.2 hσ') 0).mono' hm.restrict
      (Eventually.of_forall fun v => (Real.norm_eq_abs _).trans_le (abs_weightedFloorDiscrepancy_le σ v).2)
  have hpos : IntegrableOn (weightedFloorDiscrepancy σ) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.2 hσ) 0).mono' hm.restrict
      (Eventually.of_forall fun v => (Real.norm_eq_abs _).trans_le (abs_weightedFloorDiscrepancy_le σ v).1)
  simpa only [Iic_union_Ioi,integrableOn_univ] using hneg.union hpos

theorem abs_weightedFloorDiscrepancy_le_one {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (v : ℝ) :
    |weightedFloorDiscrepancy σ v| ≤ 1 := by
  rcases le_total 0 v with h | h
  · exact (abs_weightedFloorDiscrepancy_le σ v).1.trans
      (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hσ) h))
  · exact (abs_weightedFloorDiscrepancy_le σ v).2.trans
      (Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hσ') h))

/-- Fourier frequencies use cycles per unit on the logarithmic axis. -/
theorem fourier_weightedFloorDiscrepancy {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1) (ξ : ℝ) :
    let s : ℂ := (σ:ℂ)+(2*Real.pi*ξ:ℝ)*I
    𝓕 (fun v : ℝ => (weightedFloorDiscrepancy σ v:ℂ)) ξ = riemannZeta s/s := by
  let s : ℂ := (σ:ℂ)+(2*Real.pi*ξ:ℝ)*I
  have hre : s.re=σ := by simp [s]
  have h := _root_.RHTower.integral_Ioi_zero_fract_cpow (w := s) (hre.symm ▸ hσ) (hre.symm ▸ hσ')
  rw [_root_.RHTower.integral_Ioi_comp_exp_complex] at h
  change _ = riemannZeta s/s
  rw [← neg_neg (riemannZeta s/s),← h,← integral_neg,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae (Eventually.of_forall fun v => ?_)
  have hp : ((Real.exp v:ℝ):ℂ)^(-(s+1))=Complex.exp ((v:ℂ)*(-(s+1))) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
  rw [hp,weightedFloorDiscrepancy,smul_eq_mul]
  push_cast
  have he : Complex.exp (((-2:ℂ)*(Real.pi:ℂ)*v*ξ)*I)*Complex.exp (-(σ:ℂ)*v) =
      Complex.exp (v:ℂ)*Complex.exp ((v:ℂ)*(-(s+1))) := by
    rw [← Complex.exp_add,← Complex.exp_add]; dsimp only [s]; push_cast; congr 1; ring
  linear_combination -((Int.fract (Real.exp v):ℝ):ℂ)*he

#print axioms fourier_weightedFloorDiscrepancy
end GaloisForLFunctions.ExclusionOfTheCriticalState
