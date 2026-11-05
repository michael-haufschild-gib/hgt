import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilDiagonalKernelsAreAbsolutelyContinuous
import GaloisForLFunctions.HTGeometry.PencilCauchySchwarz
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFirstDerivativeRegularity

/-!
# Finite evaluation Grams have no singular precontact part

Cauchy–Schwarz bounds each Gram increment by a fixed multiple of the sum
of its diagonal kernel increments. Absolute continuity of those diagonal
kernels therefore excludes singular growth of every finite evaluation Gram.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open CanonicalSystemOfTheWindowTower CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

variable {ι : Type*} [Fintype ι]

/-- Cauchy–Schwarz controls each finite Gram increment by its diagonal increments. -/
theorem evalGram_sub_le_diagonal_sum (α z : ι → ℂ) {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) :
    evalGram α z b.1.1-evalGram α z a.1.1 ≤
      (∑ i, ‖α i‖^2) * ∑ i, (diagonalEvalGram (z i) b.1.1-diagonalEvalGram (z i) a.1.1) := by
  have he (c : PrecontactAperture) : evalGram α z c.1.1 = ‖evalCombination α z c‖^2 := by
    rw [evalGram, dif_pos (show c.1.1 ∈ precontactSet from ⟨c.1.2, c.2⟩)]
    rfl
  rw [he b, he a, norm_evalCombination_sq α z (a := a) (b := b) hab, add_sub_cancel_left]
  change ‖∑ i, α i • evalVectorIncrement hab (z i)‖^2 ≤ _
  simpa only [diagonalEvalGram_sub_eq (a := a) (b := b) hab] using
    HTGeometry.norm_sum_smul_sq_le α (fun i => evalVectorIncrement hab (z i))

private def evalGramDiagonalMajorant (α z : ι → ℂ) (x : ℝ) : ℝ :=
  (∑ i, ‖α i‖^2) * ∑ i, diagonalEvalGram (z i) x

private theorem monotoneOn_evalGramDiagonalMajorant (α z : ι → ℂ) :
    MonotoneOn (evalGramDiagonalMajorant α z) precontactSet := by
  intro x hx y hy hxy
  apply mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ =>
      monotoneOn_evalGram (fun _ : Unit => (1 : ℂ)) (fun _ => z i) hx hy hxy)
    (Finset.sum_nonneg fun i _ => sq_nonneg ‖α i‖)

private theorem evalGram_sub_le_majorant (α z : ι → ℂ) {x y : ℝ}
    (hx : x ∈ precontactSet) (hy : y ∈ precontactSet) (hxy : x ≤ y) :
    evalGram α z y-evalGram α z x ≤
      evalGramDiagonalMajorant α z y-evalGramDiagonalMajorant α z x := by
  have h := evalGram_sub_le_diagonal_sum α z (a := toPrecontact hx) (b := toPrecontact hy) hxy
  simpa only [evalGramDiagonalMajorant, toPrecontact, Finset.sum_sub_distrib, mul_sub] using h

private theorem ac_of_dist_le {f g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  apply lt_of_le_of_lt (Finset.sum_le_sum ?_) (hbound E hE hlen)
  intro i hi
  exact hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

/-- Every finite evaluation Gram is absolutely continuous on every compact
interval strictly before contact. -/
theorem absolutelyContinuousOnInterval_evalGram (α z : ι → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    AbsolutelyContinuousOnInterval (evalGram α z) a b := by
  have hsum := GaloisForLFunctions.RHTower.absolutelyContinuousOnInterval_finset_sum
    Finset.univ (fun i => diagonalEvalGram (z i))
    (fun i _ => absolutelyContinuousOnInterval_diagonalEvalGram (z i) hab hs)
  have hH : AbsolutelyContinuousOnInterval (evalGramDiagonalMajorant α z) a b :=
    AbsolutelyContinuousOnInterval.const_mul (∑ i, ‖α i‖^2) hsum
  have hd {x y : ℝ} (hx : x ∈ precontactSet) (hy : y ∈ precontactSet) (hxy : x ≤ y) :
      dist (evalGram α z x) (evalGram α z y) ≤
        dist (evalGramDiagonalMajorant α z x) (evalGramDiagonalMajorant α z y) := by
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (monotoneOn_evalGram α z hx hy hxy)),
      abs_of_nonpos (sub_nonpos.mpr (monotoneOn_evalGramDiagonalMajorant α z hx hy hxy)),
      neg_sub, neg_sub]
    exact evalGram_sub_le_majorant α z hx hy hxy
  apply ac_of_dist_le hH
  intro x hx y hy
  rw [uIcc_of_le hab] at hx hy
  rcases le_total x y with hxy | hyx
  · exact hd (hs hx) (hs hy) hxy
  · rw [dist_comm (evalGram α z x), dist_comm (evalGramDiagonalMajorant α z x)]
    exact hd (hs hy) (hs hx) hyx

/-- The ordinary Gram density accounts for the entire precontact kernel gain. -/
theorem integral_evalDensity_eq_sub (α z : ι → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    (∫ x in a..b, evalDensity α z x) = evalGram α z b-evalGram α z a :=
  (absolutelyContinuousOnInterval_evalGram α z hab hs).integral_deriv_eq_sub

#print axioms evalGram_sub_le_diagonal_sum
#print axioms absolutelyContinuousOnInterval_evalGram
#print axioms integral_evalDensity_eq_sub
end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
