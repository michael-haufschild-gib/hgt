import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.CauchyLogJumpSpectrum
import GaloisForLFunctions.HilbertMetric.Kernels.SparsePowerSeriesMinors
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Ordered cross minors of the logarithmic Cauchy jump kernel

On the positive side of an anchor, every pair of ordered contrast grids
has strictly positive cross determinant. The first n Taylor coefficients
already give an explicit lower bound in terms of the two Vandermonde products.
-/

noncomputable section
open Finset Matrix
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy

abbrev ContrastGrid (n : ℕ) := Fin n ↪o Set.Ioo (0:ℝ) 1

/-- Product of the coordinates and all successive-pair differences. -/
def gridVolume {n : ℕ} (z : Fin n → ℝ) :=
  (∏ i, z i)*∏ i, ∏ j ∈ Ioi i, (z j-z i)

private theorem shifted_vandermonde {n : ℕ} (z : Fin n → ℝ) :
    (genVandermonde (fun i : Fin n => i.val+1) z).det=gridVolume z := by
  have he : genVandermonde (fun i : Fin n => i.val+1) z =
      Matrix.of fun i j => z j*(vandermonde z).transpose i j := by
    ext i j
    simp only [genVandermonde,Matrix.of_apply,transpose_apply,vandermonde_apply,pow_succ,mul_comm]
  rw [he,det_mul_row,det_transpose,det_vandermonde,gridVolume]

private theorem first_coefficients (n : ℕ) :
    (∏ i : Fin n, ((i.val:ℝ)+1)⁻¹)=(n.factorial:ℝ)⁻¹ := by
  rw [Finset.prod_inv_distrib]
  congr 1
  exact_mod_cast (Fin.prod_univ_eq_prod_range (fun k : ℕ => k+1) n).trans
    (Finset.prod_range_add_one_eq_factorial n)

def positiveGrid {n : ℕ} (z : ContrastGrid n) : Fin n ↪o Set.Ioi (0:ℝ) :=
  OrderEmbedding.ofStrictMono (fun i => ⟨(z i).val,(z i).property.1⟩) (fun _ _ h => z.strictMono h)

/-- A quantitative lower bound for every cross minor, including rectangular
samplings with unrelated row and column coordinates. -/
theorem cross_det_lower {n : ℕ} (z w : ContrastGrid n) :
    gridVolume (fun i => (z i).val)*gridVolume (fun i => (w i).val)/(n.factorial:ℝ) ≤
      (Matrix.of fun i j => diskKernel (z i).val (w j).val).det := by
  let e := OrderEmbedding.ofStrictMono (fun k : ℕ => k+1) (fun _ _ h => Nat.succ_lt_succ h)
  let a (k : ℕ) : Set.Ioi (0:ℝ) := ⟨((k:ℝ)+1)⁻¹,show (0:ℝ) < ((k:ℝ)+1)⁻¹ by positivity⟩
  have H := HilbertMetric.seriesMinor_grid_lower e a (positiveGrid z) (positiveGrid w)
    (Matrix.of fun i j => diskKernel (z i).val (w j).val) (fun i j => by
      have h := diskKernel_hasSum
        (show |(z i).val|<1 by rw [abs_of_pos (z i).property.1]; exact (z i).property.2)
        (show |(w j).val|<1 by rw [abs_of_pos (w j).property.1]; exact (w j).property.2)
      change HasSum (fun k : ℕ => ((k:ℝ)+1)⁻¹*((z i).val*(w j).val)^(k+1))
        (diskKernel (z i).val (w j).val)
      simpa only [mul_pow,div_eq_inv_mul] using h)
  change (genVandermonde (fun i : Fin n => i.val+1) (fun i => (z i).val)).det *
    ((∏ i : Fin n, ((i.val:ℝ)+1)⁻¹) *
      (genVandermonde (fun i : Fin n => i.val+1) (fun i => (w i).val)).det) ≤ _ at H
  rw [shifted_vandermonde,shifted_vandermonde,first_coefficients] at H
  convert H using 1
  ring

/-- The logarithmic jump kernel is strictly totally positive on either
ordered positive contrast grid. -/
theorem cross_det_pos {n : ℕ} (z w : ContrastGrid n) :
    0 < (Matrix.of fun i j => diskKernel (z i).val (w j).val).det := by
  have hp (v : ContrastGrid n) : 0 < gridVolume (fun i => (v i).val) :=
    mul_pos (prod_pos fun i _ => (v i).property.1)
      (prod_pos fun i _ => prod_pos fun j h => sub_pos.mpr (v.strictMono (mem_Ioi.mp h)))
  exact (div_pos (mul_pos (hp _) (hp _)) (by positivity)).trans_le (cross_det_lower z w)

#print axioms cross_det_lower
#print axioms cross_det_pos
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy
