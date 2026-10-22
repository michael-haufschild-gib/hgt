import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHilbertConvolution
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionQuotient

/-! # The actual convolution algebra on all Hasse blocks

Whole-line orbit integration has the full triangular Mellin-jet action.
It extends literal source convolution and preserves its multiplication,
including every nilpotent coefficient at multiple Xi zeros.
-/

noncomputable section
open Complex MeasureTheory Filter

namespace RHTower

theorem deningerMeyerHilbertConvolution_jets (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHilbertConvolution g x q =
      ∑ k ∈ Finset.range (q.2.val+1),
        deningerMeyerHasseMoment g k (q.1 : ℂ) * x (deningerHasseLower q k) := by
  rw [deningerMeyerHilbertConvolution_coordinate]
  have he (t : ℝ) : g.val t * deningerMeyerHilbertFlow t x q =
      ∑ k ∈ Finset.range (q.2.val+1),
        (deningerMeyerStrongLogMellinJet k (q.1 : ℂ) g.val t /
          (k.factorial : ℂ)) * x (deningerHasseLower q k) := by
    rw [deningerMeyerHilbertFlow_apply, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [deningerMeyerStrongLogMellinJet, mul_comm (t : ℂ) (q.1 : ℂ)]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ =>
    ((integrable_deningerMeyerStrongLogMellinJet g.property k (q.1 : ℂ)).div_const _).mul_const _)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_mul_const, integral_div]
  rfl

private theorem hasse_product_coefficient (j k : ℕ) (hkj : k ≤ j) (a b : ℂ) :
    (j.choose k : ℂ)*a*b/(j.factorial : ℂ) =
      (a/(k.factorial : ℂ))*(b/((j-k).factorial : ℂ)) := by
  have h : (j.choose k : ℂ)*(k.factorial : ℂ)*((j-k).factorial : ℂ) =
      (j.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkj
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hd : ((j-k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j-k)
  field_simp
  linear_combination a*b*h

theorem deningerMeyerHasseMoment_convolution (g h : DeningerMeyerStrongLogTarget)
    (j : ℕ) (s : ℂ) :
    deningerMeyerHasseMoment (deningerMeyerSourceConvolution g h) j s =
      ∑ k ∈ Finset.range (j+1),
        deningerMeyerHasseMoment g k s * deningerMeyerHasseMoment h (j-k) s := by
  have he : deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g h) =
      deningerMeyerStrongLogMellin g * deningerMeyerStrongLogMellin h :=
    funext (deningerMeyerSourceConvolution_mellin g h)
  simp only [deningerMeyerHasseMoment, deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  rw [he, iteratedDeriv_mul
    ((deningerMeyerStrongLogMellin_entireRegular g).differentiable.contDiff.of_le le_top).contDiffAt
    ((deningerMeyerStrongLogMellin_entireRegular h).differentiable.contDiff.of_le le_top).contDiffAt,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  exact hasse_product_coefficient j k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) _ _

/-- The bounded operator extends the original source algebra, not only its diagonal. -/
theorem deningerMeyerHilbertConvolution_source (g : DeningerMeyerStrongLogTarget)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHilbertConvolution g (deningerMeyerHasseHilbertLM u) =
      deningerMeyerHasseHilbertLM
        (deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) u) := by
  induction u using Submodule.Quotient.induction_on with
  | H h =>
    apply lp.ext
    funext q
    rw [deningerMeyerHilbertConvolution_jets, deningerMeyerCohomologyConvolution_mk]
    exact (deningerMeyerHasseMoment_convolution g h q.2.val (q.1 : ℂ)).symm

theorem deningerMeyerHilbertConvolution_mul (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerHilbertConvolution (deningerMeyerSourceConvolution g h) =
      (deningerMeyerHilbertConvolution g).comp (deningerMeyerHilbertConvolution h) := by
  apply deningerHasseCLM_ext_source
  intro u
  simp only [ContinuousLinearMap.comp_apply, deningerMeyerHilbertConvolution_source]
  rw [← deningerMeyerCohomologyConvolution_mk, deningerMeyerCohomologyConvolution_assoc]

theorem deningerMeyerHilbertConvolution_congr {g h : DeningerMeyerStrongLogTarget}
    (hgh : (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) =
      Submodule.Quotient.mk h) :
    deningerMeyerHilbertConvolution g = deningerMeyerHilbertConvolution h := by
  apply deningerHasseCLM_ext_source
  intro u
  rw [deningerMeyerHilbertConvolution_source, deningerMeyerHilbertConvolution_source, hgh]

end RHTower
