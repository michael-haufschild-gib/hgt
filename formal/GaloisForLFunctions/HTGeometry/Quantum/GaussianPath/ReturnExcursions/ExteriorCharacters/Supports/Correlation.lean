import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.Hamming
import Mathlib.Analysis.Complex.Basic

/-! # Removing small differences from a coherent exterior sum -/

open Finset Complex
open scoped symmDiff ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Real contribution of pairs whose energy-index sets differ on more
than the prescribed number of levels. -/
def farCorrelation (F : Finset (Finset I)) (a : Finset I → ℂ) (r : ℕ) : ℝ :=
  ∑ S ∈ F, ∑ T ∈ F.filter (fun T => r<(S ∆ T).card), (a S*conj (a T)).re

/-- Deleting every small-support pair costs at most its Hamming-ball price.
All complex signs of the surviving modes are retained. -/
theorem far_correlation_floor (F : Finset (Finset I)) (a : Finset I → ℂ)
    (ha : ∀ S∈F, ‖a S‖≤1) (r : ℕ) :
    ‖∑ S ∈ F, a S‖^2-(F.card:ℝ)*(2^r*(3/2)^Fintype.card I)≤farCorrelation F a r := by
  let b (S T : Finset I) := (a S*conj (a T)).re
  have htotal : (∑ S ∈ F, ∑ T ∈ F, b S T)=‖∑ S ∈ F, a S‖^2 := by
    dsimp only [b]
    simp_rw [←Complex.re_sum,←mul_sum,←map_sum,←sum_mul,Complex.mul_conj,Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hrow (S) (hS : S∈F) : (∑ T ∈ F, b S T)≤
      2^r*(3/2:ℝ)^Fintype.card I+∑ T ∈ F.filter (fun T => r<(S ∆ T).card), b S T := by
    let B := F.filter fun T => (S ∆ T).card≤r
    have hn : (∑ T ∈ B, b S T)≤(B.card:ℝ) := by
      calc
        _ ≤ ∑ T ∈ B, (1:ℝ) := by
          apply sum_le_sum
          intro T ht
          apply (Complex.re_le_norm _).trans
          rw [norm_mul,Complex.norm_conj]
          exact mul_le_one₀ (ha S hS) (norm_nonneg _) (ha T (mem_filter.mp ht).1)
        _ = _ := by simp
    have hsplit := sum_filter_add_sum_filter_not F (fun T => (S ∆ T).card≤r) (b S)
    simp only [not_le] at hsplit
    rw [←hsplit]
    exact add_le_add (hn.trans (small_support_count F S r)) le_rfl
  have hh := sum_le_sum hrow
  rw [htotal,sum_add_distrib,sum_const,nsmul_eq_mul] at hh
  exact sub_le_iff_le_add.mpr (by simpa only [farCorrelation,b,add_comm] using hh)

#print axioms far_correlation_floor
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
