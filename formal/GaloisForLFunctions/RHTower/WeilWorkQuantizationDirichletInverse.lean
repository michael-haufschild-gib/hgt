import GaloisForLFunctions.RHTower.WeilWorkQuantizationPeriodicResidues
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Exact inverse of the actual forward coefficients

The negative logarithmic Dirichlet exponential is the convolution inverse of
the forward exponential. Both weighted coefficient sequences are absolutely
summable at 3/2. These facts use only the original Weil-positive source.
-/

open Complex Filter
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open IntegerMassRigidity AbelianTwist GaloisForLFunctions.HTGeometry

def quantizationInverseCoeff (lam : ℕ → ℝ) : ℕ → ℂ :=
  dirichletExp (fun n => -lamLog lam n)

theorem quantization_inverse_lseries {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (quantizationInverseCoeff lam) s ∧
      LSeries (quantizationInverseCoeff lam) s = cexp (-LSeries (lamLog lam) s) := by
  have hsl := fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ
  have hf := lseriesSummable_of_le (norm_lamLog_le lam) hsl hs
  obtain ⟨hb, he⟩ := LSeries_dirichletExp
    (f := fun n => -lamLog lam n) (by simp [lamLog_zero]) (by simp [lamLog_one]) hf.neg
  refine ⟨hb, ?_⟩
  rw [quantizationInverseCoeff, he]
  congr 1
  exact LSeries_neg _ _

theorem summable_quantization_inverse_terms {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Summable fun n => ‖LSeries.term (quantizationInverseCoeff lam) (((3 / 2 : ℝ) : ℂ)) n‖ :=
  (quantization_inverse_lseries hW (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)).1.norm

theorem quantization_inverse_convolution {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (n : ℕ) :
    LSeries.convolution (quantizationInverseCoeff lam) (dirichletExp (lamLog lam)) n =
      if n = 1 then 1 else 0 := by
  classical
  let a := dirichletExp (lamLog lam)
  let b := quantizationInverseCoeff lam
  let e := dirichletConvPow (lamLog lam) 0
  have hsl := fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ
  have ha {s : ℂ} (hs : 1 < s.re) := LSeries_dirichletExp (lamLog_zero lam)
    (lamLog_one lam) (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have hb {s : ℂ} (hs : 1 < s.re) := quantization_inverse_lseries hW hs
  have hc : LSeriesSummable (LSeries.convolution b a) (2 : ℂ) :=
    (hb (by norm_num : 1 < (2 : ℂ).re)).1.convolution (ha (by norm_num)).1
  have he : LSeriesSummable e (2 : ℂ) := lseriesSummable_dirichletConvPow_zero' _ _
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have heq := LSeries.eq_of_LSeries_eventually_eq
    (lt_of_le_of_lt hc.abscissaOfAbsConv_le (by simp))
    (lt_of_le_of_lt he.abscissaOfAbsConv_le (by simp)) (n := n) ?_ hn
  · exact heq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [LSeries_convolution' (hb hx).1 (ha hx).1, (hb hx).2, (ha hx).2,
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
    LSeries_dirichletConvPow_zero]

end RHTower.WeilSpectral
