import GaloisForLFunctions.RHTower.Deninger.DeningerSchwartzNuclear
import GaloisForLFunctions.RHTower.Deninger.DeningerStrictLineBounds
import GaloisForLFunctions.HTGeometry.HermiteCoordinateMoments
import GaloisForLFunctions.HTGeometry.SchwartzEulerOperator

/-!
# The Gaussian is cyclic for Euler differentiation on even Schwartz space

Hermite expansion converges in the full Schwartz topology. The Euler ladder
then identifies the closure of the polynomial Euler orbit of the Gaussian
with the entire even Schwartz subspace.
-/

open Complex Filter Topology Polynomial
open scoped SchwartzMap
open GaloisForLFunctions

namespace RHTower
noncomputable section

theorem deningerHermiteExpansion_hasSum (f : 𝓢(ℝ, ℂ)) :
    HasSum (fun j => hermiteCoeff f j • hermiteUnit j) f := by
  rw [HasSum, (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
  intro i ε hε
  obtain ⟨m, C, _, hb⟩ := schwartzSup_le_shiftedSeminorm {i}
  have ht := hasSum_hermiteExpansion_shiftedQuotient m f
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero] at ht
  have hs : Tendsto (fun S : Finset ℕ =>
      shiftedSeminorm m ((∑ j ∈ S, hermiteCoeff f j • hermiteUnit j) - f))
        (SummationFilter.unconditional ℕ).filter (𝓝 0) := by
    simpa only [← map_smul, ← map_sum, ← map_sub, deningerSeminormMk_norm] using ht
  have hc : Tendsto (fun S : Finset ℕ =>
      C * shiftedSeminorm m ((∑ j ∈ S, hermiteCoeff f j • hermiteUnit j) - f))
        (SummationFilter.unconditional ℕ).filter (𝓝 0) := by simpa using hs.const_mul C
  filter_upwards [hc.eventually_lt_const hε] with S hS
  have hb' := hb ((∑ j ∈ S, hermiteCoeff f j • hermiteUnit j) - f)
  simp only [Finset.sup_singleton] at hb'
  exact hb'.trans_lt hS

/-- Negative Euler differentiation before imposing the cap constraints. -/
def deningerSchwartzNegativeEuler : Module.End ℂ 𝓢(ℝ, ℂ) := -eulerSCLM.toLinearMap

/-- Polynomial Euler synthesis from the single self-dual Gaussian. -/
def deningerGaussianEulerPolynomial : ℂ[X] →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  (LinearMap.applyₗ gaussianSchwartz).comp
    (Polynomial.aeval deningerSchwartzNegativeEuler).toLinearMap

@[simp] theorem deningerGaussianEulerPolynomial_one :
    deningerGaussianEulerPolynomial 1 = gaussianSchwartz := by
  simp [deningerGaussianEulerPolynomial]

theorem deningerGaussianEulerPolynomial_X_mul (p : ℂ[X]) :
    deningerGaussianEulerPolynomial (X * p) =
      deningerSchwartzNegativeEuler (deningerGaussianEulerPolynomial p) := by
  simp [deningerGaussianEulerPolynomial, Polynomial.aeval_mul]

private theorem euler_hermite (n : ℕ) :
    deningerSchwartzNegativeEuler (hermiteSchwartz n) =
      ((Real.pi : ℂ) / 2) • hermiteSchwartz (n + 2) +
        (1 / 2 : ℂ) • hermiteSchwartz n -
          ((n : ℂ) * (n - 1 : ℕ) / (2 * (Real.pi : ℂ))) • hermiteSchwartz (n - 2) := by
  have hd : derivSCLM (hermiteSchwartz n) =
      -(Real.pi : ℂ) • hermiteSchwartz (n + 1) +
        (n : ℂ) • hermiteSchwartz (n - 1) := by
    have ha : annihilationCLM (hermiteSchwartz n) =
        (2 * (n : ℂ)) • hermiteSchwartz (n - 1) := by
      cases n with
      | zero => simp [annihilationCLM_hermiteSchwartz_zero]
      | succ n => simpa using annihilationCLM_hermiteSchwartz n
    rw [annihilationCLM_eq, mulXCLM_hermiteSchwartz] at ha
    ext x
    have hx := congrArg (fun f : 𝓢(ℝ, ℂ) => f x) ha
    simp only [add_apply, smul_apply, smul_eq_mul] at hx ⊢
    field_simp [pi_ne_zero_complex] at hx ⊢
    linear_combination hx
  change -mulXCLM (derivSCLM (hermiteSchwartz n)) = _
  rw [hd, map_add, map_smul, map_smul, mulXCLM_hermiteSchwartz,
    mulXCLM_hermiteSchwartz]
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_smul, add_zero, sub_zero, zero_mul, zero_div]
    ext x
    simp only [neg_apply, add_apply, smul_apply, smul_eq_mul]
    field_simp [pi_ne_zero_complex]
    ring
  | succ n =>
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    ext x
    simp only [neg_apply, add_apply, sub_apply, smul_apply, smul_eq_mul]
    push_cast
    field_simp [pi_ne_zero_complex]
    ring

private theorem euler_mem_range {f : 𝓢(ℝ, ℂ)}
    (hf : f ∈ LinearMap.range deningerGaussianEulerPolynomial) :
    deningerSchwartzNegativeEuler f ∈ LinearMap.range deningerGaussianEulerPolynomial := by
  obtain ⟨p, rfl⟩ := hf
  exact ⟨X * p, deningerGaussianEulerPolynomial_X_mul p⟩

private theorem evenHermite_mem_range (n : ℕ) :
    hermiteSchwartz (2 * n) ∈ LinearMap.range deningerGaussianEulerPolynomial := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨1, by simp [hermiteSchwartz_zero]⟩
    | succ n =>
      have hn := ih n (by omega)
      have hlow : (((2 * n : ℕ) : ℂ) * ((2 * n - 1 : ℕ) : ℂ) /
          (2 * (Real.pi : ℂ))) • hermiteSchwartz (2 * n - 2) ∈
            LinearMap.range deningerGaussianEulerPolynomial := by
        by_cases h : n = 0
        · simp [h]
        · have he : 2 * n - 2 = 2 * (n - 1) := by omega
          rw [he]
          exact Submodule.smul_mem _ _ (ih (n - 1) (by omega))
      have hm := (LinearMap.range deningerGaussianEulerPolynomial).add_mem
        ((LinearMap.range deningerGaussianEulerPolynomial).sub_mem (euler_mem_range hn)
          ((LinearMap.range deningerGaussianEulerPolynomial).smul_mem (1 / 2 : ℂ) hn)) hlow
      have he : deningerSchwartzNegativeEuler (hermiteSchwartz (2 * n)) -
          (1 / 2 : ℂ) • hermiteSchwartz (2 * n) +
            (((2 * n : ℕ) : ℂ) * ((2 * n - 1 : ℕ) : ℂ) / (2 * (Real.pi : ℂ))) •
              hermiteSchwartz (2 * n - 2) =
          ((Real.pi : ℂ) / 2) • hermiteSchwartz (2 * (n + 1)) := by
        rw [euler_hermite, show 2 * (n + 1) = 2 * n + 2 by omega]
        module
      have hm' : ((Real.pi : ℂ) / 2) • hermiteSchwartz (2 * (n + 1)) ∈
          LinearMap.range deningerGaussianEulerPolynomial := by
        rwa [he] at hm
      exact (Submodule.smul_mem_iff _ (div_ne_zero pi_ne_zero_complex two_ne_zero)).mp hm'

/-- The continuous even part on the original Schwartz source. -/
def deningerSchwartzEvenPart : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ _ + deningerReflectCLM)

@[simp] theorem deningerSchwartzEvenPart_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deningerSchwartzEvenPart f x = (1 / 2 : ℂ) * (f x + f (-x)) := rfl

private theorem evenPart_hermite_mem_range (n : ℕ) :
    deningerSchwartzEvenPart (hermiteSchwartz n) ∈
      LinearMap.range deningerGaussianEulerPolynomial := by
  by_cases hn : n % 2 = 0
  · have he : n = 2 * (n / 2) := by omega
    rw [he]
    have hf : deningerSchwartzEvenPart (hermiteSchwartz (2 * (n / 2))) =
        hermiteSchwartz (2 * (n / 2)) := by
      ext x
      rw [deningerSchwartzEvenPart_apply, hermiteSchwartz_even]
      ring
    rw [hf]
    exact evenHermite_mem_range _
  · have he : n = 2 * (n / 2) + 1 := by omega
    have hf : deningerSchwartzEvenPart (hermiteSchwartz n) = 0 := by
      ext x
      rw [deningerSchwartzEvenPart_apply, hermiteSchwartz_neg, he]
      simp [pow_add, pow_mul]
    rw [hf]
    exact Submodule.zero_mem _

/-- Every even Schwartz function is a strong limit of polynomial Euler–Gaussian sources. -/
theorem deningerGaussianEulerPolynomial_dense_even (f : 𝓢(ℝ, ℂ))
    (hf : f ∈ deningerEvenSchwartz) :
    f ∈ (LinearMap.range deningerGaussianEulerPolynomial).topologicalClosure := by
  have he : deningerSchwartzEvenPart f = f := by
    ext x
    rw [deningerSchwartzEvenPart_apply, (deningerEvenSchwartz_mem_iff f).mp hf]
    ring
  have hs := (deningerHermiteExpansion_hasSum f).map deningerSchwartzEvenPart
    deningerSchwartzEvenPart.continuous
  rw [he] at hs
  apply (LinearMap.range deningerGaussianEulerPolynomial).isClosed_topologicalClosure.mem_of_tendsto
    hs
  exact Filter.Eventually.of_forall fun S => Submodule.sum_mem _ fun n _ =>
    Submodule.le_topologicalClosure _ (by
      simp only [Function.comp_def, map_smul, hermiteUnit]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (evenPart_hermite_mem_range n)))

end
end RHTower
