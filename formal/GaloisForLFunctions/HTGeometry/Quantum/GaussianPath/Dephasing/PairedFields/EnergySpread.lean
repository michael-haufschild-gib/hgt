import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Mean deviations under a doubly stochastic change of spectral weights -/

open Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
noncomputable section
variable {I : Type*} [Fintype I]

/-- Sum of absolute gaps over ordered pairs, including multiplicities. -/
def spread (v : I → ℝ) : ℝ := ∑ i, ∑ j, |v i-v j|

/-- The energy expectation in one row of a change of basis. -/
def rowMean (p : I → I → ℝ) (v : I → ℝ) (j : I) := ∑ i, p j i*v i

private theorem sum_means {p : I → I → ℝ} (hcol : ∀ i, ∑ j, p j i=1) (f : I → ℝ) :
    ∑ j, rowMean p f j=∑ i, f i := by
  simp only [rowMean]
  rw [sum_comm]
  simp only [←sum_mul,hcol,one_mul]

private theorem abs_row {p : I → I → ℝ} (hn : ∀ j i, 0≤p j i) (j : I) (f : I → ℝ) :
    |rowMean p f j| ≤ rowMean p (fun i => |f i|) j := by
  simpa only [rowMean,abs_mul,abs_of_nonneg (hn j _)] using
    (Finset.abs_sum_le_sum_abs (fun i => p j i*f i) univ)

private theorem from_mean {p : I → I → ℝ} (hn : ∀ j i, 0≤p j i)
    (hr : ∀ j, ∑ i, p j i=1) (v : I → ℝ) (j : I) (x : ℝ) :
    |x-rowMean p v j| ≤ rowMean p (fun l => |x-v l|) j := by
  have h := abs_row hn j (fun l => x-v l)
  simpa only [rowMean,mul_sub,sum_sub_distrib,←sum_mul,hr,one_mul] using h

private def pairGap (p : I → I → ℝ) (v : I → ℝ) (j k : I) :=
  rowMean p (fun i => rowMean p (fun l => |v i-v l|) k) j

private theorem row_deviation {p : I → I → ℝ} (hn : ∀ j i, 0≤p j i)
    (hr : ∀ j, ∑ i, p j i=1) (v : I → ℝ) (j k : I) :
    rowMean p (fun i => |v i-rowMean p v k|) j ≤ pairGap p v j k :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (from_mean hn hr v k (v i)) (hn j i)

private theorem between_rows {p : I → I → ℝ} (hn : ∀ j i, 0≤p j i)
    (hr : ∀ j, ∑ i, p j i=1) (v : I → ℝ) (j k : I) :
    |rowMean p v j-rowMean p v k| ≤ pairGap p v j k := by
  apply le_trans _ (row_deviation hn hr v j k)
  have h := abs_row hn j (fun i => v i-rowMean p v k)
  simpa only [rowMean,mul_sub,sum_sub_distrib,←sum_mul,hr,one_mul] using h

private theorem sum_pairGap {p : I → I → ℝ} (hc : ∀ i, ∑ j, p j i=1) (v : I → ℝ) :
    ∑ j, ∑ k, pairGap p v j k = spread v := by
  rw [sum_comm]
  simp only [pairGap,sum_means hc]
  rw [sum_comm]
  simp only [sum_means hc,spread]

/-- The loss of pairwise energy spread pays for the full within-row mean
absolute deviation. The diagonal pairs of rows supply that extra term. -/
theorem deviation_le_spread_loss {p : I → I → ℝ} (hn : ∀ j i, 0≤p j i)
    (hr : ∀ j, ∑ i, p j i=1) (hc : ∀ i, ∑ j, p j i=1) (v : I → ℝ) :
    (∑ j, rowMean p (fun i => |v i-rowMean p v j|) j)+spread (rowMean p v) ≤ spread v := by
  classical
  rw [←sum_pairGap hc v,spread,←sum_add_distrib]
  apply sum_le_sum
  intro j _
  let d := rowMean p (fun i => |v i-rowMean p v j|) j
  have h (k : I) : (if j=k then d else 0)+|rowMean p v j-rowMean p v k| ≤ pairGap p v j k := by
    by_cases he : j=k
    · subst k
      simpa only [if_true,sub_self,abs_zero,add_zero] using row_deviation hn hr v j j
    · simpa only [if_neg he,zero_add] using between_rows hn hr v j k
  simpa only [sum_add_distrib,sum_ite_eq,mem_univ,if_true] using sum_le_sum (s:=univ) (fun k _ => h k)

/-- Opposite changes of the energies in a fixed basis preserve their midpoint. -/
theorem paired_spread (e f g : I → ℝ) (a : ℝ) (ha : 0≤a)
    (h : ∀ j, f j+g j=2*a*e j) : 2*a*spread e ≤ spread f+spread g := by
  simp only [spread,mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  have he : (f i-f j)+(g i-g j)=(2*a)*(e i-e j) := by linarith only [h i,h j]
  have ht := abs_add_le (f i-f j) (g i-g j)
  rwa [he,abs_mul,abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) ha)] at ht

#print axioms deviation_le_spread_loss
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
