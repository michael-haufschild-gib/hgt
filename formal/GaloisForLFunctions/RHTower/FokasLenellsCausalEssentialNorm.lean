import GaloisForLFunctions.RHTower.FokasLenellsCausalUnitBoundaryWeakLimit
import GaloisForLFunctions.RHTower.CCMPrimePolePolynomialBoundary
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Order.Field
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
open scoped NNReal
open Complex Set Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section EssentialBoundary
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem inner_weak_to_dual (v : ℕ → H)
    (hv : ∀ y, Tendsto (fun n => inner ℂ y (v n)) atTop (𝓝 0))
    (ℓ : H →L[ℂ] ℂ) : Tendsto (fun n => ℓ (v n)) atTop (𝓝 0) := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    hv ((InnerProductSpace.toDual ℂ H).symm ℓ)

private theorem unit_boundary_essentialNorm (T : H →L[ℂ] H) (hT : ‖T‖ = 1)
    (v : ℕ → H) (hv : ∀ n, ‖v n‖ = 1)
    (hw : ∀ y, Tendsto (fun n => inner ℂ y (v n)) atTop (𝓝 0))
    (α : ℕ → ℂ) (μ : ℂ) (hμ : ‖μ‖ = 1)
    (he : ∀ n, T (v n) = α n • v n) (hα : Tendsto α atTop (𝓝 μ)) :
    RHTower.essentialNorm T = 1 := by
  have hd : Tendsto (fun n => α n - μ) atTop (𝓝 (0 : ℂ)) := by
    simpa using hα.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => μ) atTop (𝓝 μ))
  have hn : ∀ n, ‖T (v n) - μ • v n‖ = ‖α n - μ‖ := by
    intro n
    rw [he, ← sub_smul, norm_smul, hv, mul_one]
  have ha : Tendsto (fun n => ‖T (v n) - μ • v n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hn, norm_zero] using hd.norm
  have hl := RHTower.norm_le_essentialNorm_of_weaklyNull_approx_eigenvector
    T v μ hv (inner_weak_to_dual v hw) ha
  rw [hμ] at hl
  apply le_antisymm _ hl
  simpa only [sub_zero, hT] using
    (RHTower.essentialNorm_le T 0 isCompactOperator_zero)
end EssentialBoundary

/-- The actual causal evolution stays at distance one from compact operators at
all nonnegative times, despite strong decay on every fixed Hilbert input. -/
theorem essentialNorm_causalLowerCauchyEvolution (t : ℝ≥0) :
    RHTower.essentialNorm (causalLowerCauchyEvolution t) = 1 := by
  letI : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
  have hn : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply unit_boundary_essentialNorm (causalLowerCauchyEvolution t)
    (norm_causalLowerCauchyEvolution t)
    (fun n => (causalUnitBoundaryEigenvector (-(n : ℝ)) 1).val)
    (fun n => norm_causalUnitBoundaryEigenvector (-(n : ℝ)) 1)
    (fun y => (causalUnitBoundaryEigenvector_weak_tendsto_pos y).comp hn)
    (fun n => Complex.exp (((t : ℝ) : ℂ) * (causalUnitBoundaryRate (-(n : ℝ)) 1).val))
    (Complex.exp (((t : ℝ) : ℂ) * I))
    (by simp [Complex.norm_exp, Complex.mul_re])
    (fun n => causalLowerCauchyEvolution_unitBoundaryEigenvector t (-(n : ℝ)) 1)
  exact (Complex.continuous_exp.tendsto _).comp
    ((causalUnitBoundaryRate_tendsto_pos.comp hn).const_mul (((t : ℝ) : ℂ)))

/-- No nonnegative-time actual causal evolution operator is compact. -/
theorem causalLowerCauchyEvolution_not_isCompactOperator (t : ℝ≥0) :
    ¬IsCompactOperator (causalLowerCauchyEvolution t) := by
  intro h
  have hb := RHTower.essentialNorm_le (causalLowerCauchyEvolution t)
    (causalLowerCauchyEvolution t) h
  rw [essentialNorm_causalLowerCauchyEvolution, sub_self, norm_zero] at hb
  exact (by norm_num : ¬(1 : ℝ) ≤ 0) hb

end RHTower.FokasLenells
