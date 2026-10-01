import GaloisForLFunctions.RHTower.TwoGaussianSourceDerivativeAdmission
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The literal two-Gaussian derivative history

The actual pinned primitive restricts to the algebraic span of the ordinary
derivatives. Integrability proves its linearity there. Its powers prove full
independence; no lowering basis or whole-space bounded inverse is assumed.
-/

open MeasureTheory Set GaloisForLFunctions.HTGeometry
open RHTower.HedenmalmQuantile
open scoped ENNReal

noncomputable section

namespace RHTower.TwoGaussianComparison

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

private abbrev μS := volume.withDensity (realDensity (sourceWeight source))

/-- The algebraic span of the ACTUAL ordinary derivative functions. -/
def functionDerivativeHistory : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (Set.range derivativeFunction)

theorem functionDerivativeHistory_admission {f : ℝ → ℂ}
    (hf : f ∈ functionDerivativeHistory) :
    Continuous f ∧ Integrable f ∧ MemLp f 2 μS := by
  refine Submodule.span_induction (p := fun f _ =>
    Continuous f ∧ Integrable f ∧ MemLp f 2 μS) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨n, rfl⟩
    exact ⟨continuous_derivativeFunction n, integrable_derivativeFunction n,
      derivativeFunction_memLp n⟩
  · exact ⟨continuous_zero, integrable_zero ℝ ℂ volume, MemLp.zero⟩
  · intro f g _ _ hfp hgp
    exact ⟨hfp.1.add hgp.1, hfp.2.1.add hgp.2.1, hfp.2.2.add hgp.2.2⟩
  · intro c f _ hfp
    refine ⟨hfp.1.const_smul c, ?_, hfp.2.2.const_smul c⟩
    convert hfp.2.1.const_mul c using 1
    funext x
    exact smul_eq_mul c (f x)

private theorem sourceInverse_add_of_integrable {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    sourceInverse source (f + g) = sourceInverse source f + sourceInverse source g := by
  funext x
  have hk : Integrable (fun y : ℝ => (source.k y : ℂ)) := source.integrable_k.ofReal
  have hfc := hf.sub (hk.const_mul ((∫ z, f z) / (source.mass : ℂ)))
  have hgc := hg.sub (hk.const_mul ((∫ z, g z) / (source.mass : ℂ)))
  change Integrable (fun y => f y -
    ((∫ z, f z) / (source.mass : ℂ)) * (source.k y : ℂ)) at hfc
  change Integrable (fun y => g y -
    ((∫ z, g z) / (source.mass : ℂ)) * (source.k y : ℂ)) at hgc
  simp only [sourceInverse, Pi.add_apply]
  rw [integral_add hf hg]
  have heq :
      (fun y : ℝ => f y + g y -
        (((∫ z, f z) + (∫ z, g z)) / (source.mass : ℂ)) * (source.k y : ℂ)) =
      (fun y : ℝ => (f y - ((∫ z, f z) / (source.mass : ℂ)) * (source.k y : ℂ)) +
        (g y - ((∫ z, g z) / (source.mass : ℂ)) * (source.k y : ℂ))) := by
    funext y
    ring
  rw [heq, integral_add hfc.integrableOn hgc.integrableOn]
  ring

private theorem sourceInverse_smul (c : ℂ) (f : ℝ → ℂ) :
    sourceInverse source (c • f) = c • sourceInverse source f := by
  funext x
  simp only [sourceInverse, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul c f]
  have heq :
      (fun y : ℝ => c * f y -
        ((c * ∫ z, f z) / (source.mass : ℂ)) * (source.k y : ℂ)) =
      (fun y : ℝ => c * (f y -
        ((∫ z, f z) / (source.mass : ℂ)) * (source.k y : ℂ))) := by
    funext y
    ring
  rw [heq, integral_const_mul c]
  ring

private theorem sourceInverse_zero : sourceInverse source (0 : ℝ → ℂ) = 0 := by
  funext x
  simp [sourceInverse]

private theorem sourceInverse_derivativeFunction_zero_fun :
    sourceInverse source (derivativeFunction 0) = 0 :=
  funext sourceInverse_derivativeFunction_zero

private theorem sourceInverse_derivativeFunction_succ_fun (n : ℕ) :
    sourceInverse source (derivativeFunction (n + 1)) = Complex.I • derivativeFunction n :=
  funext (sourceInverse_derivativeFunction_succ n)

theorem functionDerivativeHistory_sourceInverse_invariant {f : ℝ → ℂ}
    (hf : f ∈ functionDerivativeHistory) :
    sourceInverse source f ∈ functionDerivativeHistory := by
  refine Submodule.span_induction (p := fun f _ =>
    sourceInverse source f ∈ functionDerivativeHistory) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨n, rfl⟩
    cases n with
    | zero =>
        rw [sourceInverse_derivativeFunction_zero_fun]
        exact functionDerivativeHistory.zero_mem
    | succ n =>
        rw [sourceInverse_derivativeFunction_succ_fun]
        exact functionDerivativeHistory.smul_mem _ (Submodule.subset_span ⟨n, rfl⟩)
  · rw [sourceInverse_zero]
    exact functionDerivativeHistory.zero_mem
  · intro f g hf hg hfp hgp
    rw [sourceInverse_add_of_integrable (functionDerivativeHistory_admission hf).2.1
      (functionDerivativeHistory_admission hg).2.1]
    exact functionDerivativeHistory.add_mem hfp hgp
  · intro c f _ hfp
    rw [sourceInverse_smul]
    exact functionDerivativeHistory.smul_mem c hfp

/-- Restriction of the actual integral, whose linearity follows from admission. -/
def functionHistoryInverse : functionDerivativeHistory →ₗ[ℂ] functionDerivativeHistory where
  toFun f := ⟨sourceInverse source f,
    functionDerivativeHistory_sourceInverse_invariant f.property⟩
  map_add' f g := Subtype.ext (sourceInverse_add_of_integrable
    (functionDerivativeHistory_admission f.property).2.1
    (functionDerivativeHistory_admission g.property).2.1)
  map_smul' c f := Subtype.ext (sourceInverse_smul c f)

/-- The actual derivative, as a vector of its algebraic history. -/
def functionHistoryDerivativeVector (n : ℕ) : functionDerivativeHistory :=
  ⟨derivativeFunction n, Submodule.subset_span ⟨n, rfl⟩⟩

theorem functionHistoryInverse_derivative_zero :
    functionHistoryInverse (functionHistoryDerivativeVector 0) = 0 :=
  Subtype.ext sourceInverse_derivativeFunction_zero_fun

theorem functionHistoryInverse_derivative_succ (n : ℕ) :
    functionHistoryInverse (functionHistoryDerivativeVector (n + 1)) =
      Complex.I • functionHistoryDerivativeVector n :=
  Subtype.ext (sourceInverse_derivativeFunction_succ_fun n)

theorem functionHistoryDerivativeVector_zero_ne_zero : functionHistoryDerivativeVector 0 ≠ 0 := by
  intro h
  have hz := congrArg (fun f : functionDerivativeHistory => (f : ℝ → ℂ) 0) h
  change derivativeFunction 0 0 = 0 at hz
  rw [derivativeFunction_zero] at hz
  have hk : (source.k 0 : ℂ) ≠ 0 := by exact_mod_cast (source.pos_k 0).ne'
  exact hk hz

theorem functionHistoryInverse_pow_derivative_self (n : ℕ) :
    (functionHistoryInverse ^ n) (functionHistoryDerivativeVector n) =
      Complex.I ^ n • functionHistoryDerivativeVector 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      change (functionHistoryInverse ^ n)
        (functionHistoryInverse (functionHistoryDerivativeVector (n + 1))) =
          Complex.I ^ (n + 1) • functionHistoryDerivativeVector 0
      rw [functionHistoryInverse_derivative_succ, map_smul,
        ih, pow_succ, smul_smul]
      congr 1
      ring

theorem functionHistoryInverse_pow_derivative_eq_zero (n k : ℕ) (hnk : n < k) :
    (functionHistoryInverse ^ k) (functionHistoryDerivativeVector n) = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      cases n with
      | zero =>
          rw [pow_succ]
          change (functionHistoryInverse ^ k)
            (functionHistoryInverse (functionHistoryDerivativeVector 0)) = 0
          rw [functionHistoryInverse_derivative_zero, map_zero]
      | succ n =>
          rw [pow_succ]
          change (functionHistoryInverse ^ k)
            (functionHistoryInverse (functionHistoryDerivativeVector (n + 1))) = 0
          rw [functionHistoryInverse_derivative_succ, map_smul,
            ih n (by omega), smul_zero]

/-- Full independence follows from actual primitive powers and source positivity. -/
theorem linearIndependent_functionHistoryDerivativeVector :
    LinearIndependent ℂ functionHistoryDerivativeVector := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert n s hlt hs =>
      intro c hsum j hj
      have hn : n ∉ s := by
        intro hns
        exact (lt_irrefl n) (hlt n hns)
      have hpow := congrArg (fun f : functionDerivativeHistory =>
        (functionHistoryInverse ^ n) f) hsum
      rw [Finset.sum_insert hn, map_add, map_smul, map_sum, map_zero,
        functionHistoryInverse_pow_derivative_self] at hpow
      simp_rw [map_smul] at hpow
      have htail : (∑ i ∈ s, c i •
          (functionHistoryInverse ^ n) (functionHistoryDerivativeVector i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [functionHistoryInverse_pow_derivative_eq_zero i n (by
          have := hlt i hi
          omega), smul_zero]
      rw [htail, add_zero] at hpow
      have hcn : c n = 0 := (smul_eq_zero.mp hpow).resolve_right
        (smul_ne_zero (pow_ne_zero n Complex.I_ne_zero)
          functionHistoryDerivativeVector_zero_ne_zero)
      have hsump : (∑ i ∈ s, c i • functionHistoryDerivativeVector i) = 0 := by
        simpa only [Finset.sum_insert hn, hcn, zero_smul, zero_add] using hsum
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact hcn
      · exact hs c hsump j hjs

end RHTower.TwoGaussianComparison
