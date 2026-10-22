import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogMellin
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonOperator
import GaloisForLFunctions.HTGeometry.HighDegreeJetFreedom

/-!
# Polynomial multipliers produced by actual Meyer cap sources

Whole-line integration by parts identifies negative log differentiation with
multiplication by the Mellin parameter. The negative Euler operator preserves
the actual cap and intertwines with the literal Poisson map. Thus every
polynomial multiplier of a boundary Mellin transform has a cap preimage.
-/

open Complex Filter Topology MeasureTheory Set
open scoped SchwartzMap
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

theorem deningerMeyerStrongLogMellin_deriv {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (s : ℂ) :
    deningerMeyerStrongLogMellin (deriv g) s =
      -s * deningerMeyerStrongLogMellin g s := by
  have hi : Integrable (fun t : ℝ => Complex.exp (s * t) * g t) := by
    apply (integrable_deningerMeyerStrongLogMellinJet hg 0 s).congr
    filter_upwards with t
    simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul]
  have hi' : Integrable (fun t : ℝ => Complex.exp (s * t) * deriv g t) := by
    apply (integrable_deningerMeyerStrongLogMellinJet hg.deriv 0 s).congr
    filter_upwards with t
    simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul]
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (s * t))
      (s * Complex.exp (s * t)) t := by
    intro t
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, mul_comm] using
      (Complex.ofRealCLM.hasDerivAt.const_mul s).cexp (x := t)
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => Complex.exp (s * t)) (u' := fun t => s * Complex.exp (s * t))
    (v := g) (v' := deriv g)
    (fun t _ => hd t)
    (fun t _ => (hg.smooth.differentiable (by simp) t).hasDerivAt)
    hi' (by
      apply (hi.const_mul s).congr
      filter_upwards with t
      exact (mul_assoc _ _ _).symm) hi
  simp only [deningerMeyerStrongLogMellin, deningerMeyerStrongLogMellinJet,
    pow_zero, one_mul]
  rw [he]
  simp only [mul_assoc, integral_const_mul, neg_mul]

/-- Negative Euler differentiation on the genuine source cap. -/
def deningerMeyerNegativeEuler : DeningerMeyerCap →ₗ[ℂ] DeningerMeyerCap where
  toFun f := ⟨-eulerSCLM f, DeningerMeyerCap.neg_mem (deningerMeyerCap_eulerSCLM f.property)⟩
  map_add' f g := by apply Subtype.ext; simp [add_comm]
  map_smul' c f := by apply Subtype.ext; simp

theorem deningerMeyerNegativeEuler_boundary (f : DeningerMeyerCap) :
    (deningerMeyerStrongLogSumLM (deningerMeyerNegativeEuler f) : ℝ → ℂ) =
      -deriv (deningerMeyerStrongLogSumLM f : ℝ → ℂ) := by
  have he : deningerMeyerEulerCLM (f : SchwartzMap ℝ ℂ) = eulerSCLM f := by
    ext x
    rw [deningerMeyerEulerCLM_apply, eulerSCLM_apply]
  let E : DeningerMeyerCap := ⟨eulerSCLM f, deningerMeyerCap_eulerSCLM f.property⟩
  have hd : deriv (deningerMeyerStrongLogSumLM f : ℝ → ℂ) =
      (deningerMeyerStrongLogSumLM E : ℝ → ℂ) := by
    change deriv (deningerMeyerLogSum (f : SchwartzMap ℝ ℂ)) =
      deningerMeyerLogSum (eulerSCLM f)
    rw [deriv_deningerMeyerLogSum, he]
  rw [hd]
  change (deningerMeyerStrongLogSumLM (-E) : ℝ → ℂ) = _
  rw [map_neg]
  rfl

/-- The entire Mellin transform of a literal Poisson boundary. -/
def deningerMeyerBoundaryMellin (f : DeningerMeyerCap) (s : ℂ) : ℂ :=
  deningerMeyerStrongLogMellin (deningerMeyerStrongLogSumLM f) s

def deningerMeyerBoundaryMellinLM (s : ℂ) : DeningerMeyerCap →ₗ[ℂ] ℂ :=
  (deningerMeyerStrongLogMellinLM s).comp deningerMeyerStrongLogSumLM

theorem deningerMeyerBoundaryMellin_negativeEuler (f : DeningerMeyerCap) (s : ℂ) :
    deningerMeyerBoundaryMellin (deningerMeyerNegativeEuler f) s =
      s * deningerMeyerBoundaryMellin f s := by
  change deningerMeyerStrongLogMellin _ s = s * deningerMeyerStrongLogMellin _ s
  rw [deningerMeyerNegativeEuler_boundary]
  calc
    deningerMeyerStrongLogMellin (-deriv (deningerMeyerStrongLogSumLM f : ℝ → ℂ)) s =
        -deningerMeyerStrongLogMellin (deriv (deningerMeyerStrongLogSumLM f : ℝ → ℂ)) s := by
      simp only [deningerMeyerStrongLogMellin, deningerMeyerStrongLogMellinJet,
        Pi.neg_apply, mul_neg, integral_neg]
    _ = _ := by
      rw [deningerMeyerStrongLogMellin_deriv (deningerMeyerStrongLogSumLM f).property]
      ring

theorem deningerMeyerBoundaryMellin_negativeEuler_iterate
    (f : DeningerMeyerCap) (n : ℕ) (s : ℂ) :
    deningerMeyerBoundaryMellin ((deningerMeyerNegativeEuler^[n]) f) s =
      s ^ n * deningerMeyerBoundaryMellin f s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', deningerMeyerBoundaryMellin_negativeEuler, ih,
      pow_succ]
    ring

/-- A finite polynomial orbit inside the cap, constructed before taking any jets. -/
def deningerMeyerBoundaryPolynomialSource (f : DeningerMeyerCap) (n : ℕ) :
    (Fin n → ℂ) →ₗ[ℂ] DeningerMeyerCap :=
  ∑ i : Fin n, (LinearMap.proj i).smulRight ((deningerMeyerNegativeEuler^[i.val]) f)

theorem deningerMeyerBoundaryPolynomialSource_mellin
    (f : DeningerMeyerCap) (n : ℕ) (c : Fin n → ℂ) (s : ℂ) :
    deningerMeyerBoundaryMellin (deningerMeyerBoundaryPolynomialSource f n c) s =
      (windowLin 0 n c).eval s * deningerMeyerBoundaryMellin f s := by
  change deningerMeyerBoundaryMellinLM s _ = _
  simp only [deningerMeyerBoundaryPolynomialSource, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, map_sum, map_smul,
    smul_eq_mul, windowLin_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, zero_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  change c i * deningerMeyerBoundaryMellin ((deningerMeyerNegativeEuler^[i.val]) f) s = _
  rw [deningerMeyerBoundaryMellin_negativeEuler_iterate]
  ring

end
end RHTower
