import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Schrödinger propagator of a bounded self-adjoint Hamiltonian

For a bounded self-adjoint operator `H` on a complex Hilbert space, the Banach-algebra exponential

```text
propagator H t = exp (t • (-i H))
```

is the exact solution operator of `i ψ' = H ψ`.  This file records the four properties any
perturbative argument needs and that mathlib does not package: the group law, the derivative, the
adjoint, and unitarity.  Unitarity is proved from `star (exp x) = exp (star x)` together with
`exp (x + y) = exp x * exp y` for commuting arguments; no spectral theory is involved.
-/

open scoped InnerProductSpace
open NormedSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-- The Schrödinger propagator `exp (-i t H)` of a bounded Hamiltonian. -/
def propagator (H : 𝓗 →L[ℂ] 𝓗) (t : ℝ) : 𝓗 →L[ℂ] 𝓗 :=
  NormedSpace.exp (t • ((-Complex.I) • H))

omit [CompleteSpace 𝓗] in
@[simp] theorem propagator_zero (H : 𝓗 →L[ℂ] 𝓗) : propagator H 0 = 1 := by
  simp [propagator]

/-- **The propagator solves the Schrödinger equation.** -/
theorem hasDerivAt_propagator (H : 𝓗 →L[ℂ] 𝓗) (t : ℝ) :
    HasDerivAt (propagator H) ((-Complex.I) • (H ∘L propagator H t)) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) ((-Complex.I) • H) t
  have hrw : ((-Complex.I) • H) * NormedSpace.exp (t • ((-Complex.I) • H))
      = (-Complex.I) • (H ∘L propagator H t) := by
    rw [propagator]
    rfl
  rw [hrw] at h
  exact h

/-- The propagator is a one-parameter group. -/
theorem propagator_comp (H : 𝓗 →L[ℂ] 𝓗) (s t : ℝ) :
    propagator H s ∘L propagator H t = propagator H (s + t) := by
  have hc : Commute (s • ((-Complex.I) • H)) (t • ((-Complex.I) • H)) := by
    refine Commute.smul_left ?_ _
    refine Commute.smul_right ?_ _
    exact Commute.refl _
  have hadd : (s + t) • ((-Complex.I) • H) = s • ((-Complex.I) • H) + t • ((-Complex.I) • H) :=
    add_smul _ _ _
  letI : NormedAlgebra ℚ (𝓗 →L[ℂ] 𝓗) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [propagator, propagator, propagator, hadd, NormedSpace.exp_add_of_commute hc]
  rfl

/-- The adjoint of the propagator is the reversed propagator. -/
theorem star_propagator {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) :
    star (propagator H t) = propagator H (-t) := by
  have hstar : star (t • ((-Complex.I) • H)) = (-t) • ((-Complex.I) • H) := by
    rw [star_smul, star_smul, hH.star_eq]
    simp [neg_smul]
  rw [propagator, propagator, NormedSpace.star_exp, hstar]

/-- **Unitarity of the propagator.** -/
theorem propagator_mem_unitary {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) :
    propagator H t ∈ unitary (𝓗 →L[ℂ] 𝓗) := by
  letI : NormedAlgebra ℚ (𝓗 →L[ℂ] 𝓗) := NormedAlgebra.restrictScalars ℚ ℂ _
  refine NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ?_
  rw [skewAdjoint.mem_iff, star_smul, star_smul, hH.star_eq]
  simp [neg_smul]

/-- A unitary operator on a Hilbert space preserves norms. -/
theorem norm_apply_of_mem_unitary {U : 𝓗 →L[ℂ] 𝓗} (hU : U ∈ unitary (𝓗 →L[ℂ] 𝓗)) (x : 𝓗) :
    ‖U x‖ = ‖x‖ := by
  have hone : (ContinuousLinearMap.adjoint U) (U x) = x := by
    have h := (Unitary.mem_iff.mp hU).1
    have h2 := congrArg (fun T : 𝓗 →L[ℂ] 𝓗 => T x) h
    simpa [ContinuousLinearMap.star_eq_adjoint] using h2
  have hinner : (inner ℂ (U x) (U x) : ℂ) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_right U x (U x), hone]
  have hsq : ‖U x‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
  calc ‖U x‖ = Real.sqrt (‖U x‖ ^ (2 : ℕ)) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ (2 : ℕ)) := by rw [hsq]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_propagator_apply {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) (x : 𝓗) :
    ‖propagator H t x‖ = ‖x‖ :=
  norm_apply_of_mem_unitary (propagator_mem_unitary hH t) x

theorem norm_propagator_le_one {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) :
    ‖propagator H t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [norm_propagator_apply hH t x, one_mul]

theorem continuous_propagator (H : 𝓗 →L[ℂ] 𝓗) : Continuous (propagator H) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  exact (hasDerivAt_propagator H t).continuousAt

/-- **The propagator acts on an eigenvector by a phase.**  Termwise from the exponential series:
`A = -i t H` sends `ψ` to `c • ψ` with `c = -i t μ`, so `Aⁿ ψ = cⁿ • ψ` and the series collapses to
the scalar exponential. -/
theorem propagator_apply_eigen (H : 𝓗 →L[ℂ] 𝓗) (t : ℝ) (μ : ℂ) (ψ : 𝓗) (hψ : H ψ = μ • ψ) :
    propagator H t ψ = Complex.exp ((-(t : ℂ) * Complex.I) * μ) • ψ := by
  set c : ℂ := (-(t : ℂ) * Complex.I) * μ with hc
  set A : 𝓗 →L[ℂ] 𝓗 := t • ((-Complex.I) • H) with hA
  have hArw : A = (-(t : ℂ) * Complex.I) • H := by
    rw [hA, ← smul_assoc]
    congr 1
    rw [Complex.real_smul]
    ring
  have hAψ : A ψ = c • ψ := by
    rw [hArw, smul_apply, hψ, smul_smul, hc]
  have hpow : ∀ n : ℕ, (A ^ n) ψ = c ^ n • ψ := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, mul_apply_eq_comp, hAψ, map_smul, ih, smul_smul, pow_succ]
        congr 1
        ring
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • A ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hsumc : Summable (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * c ^ n) := by
    simpa [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℂ) c
  have hexpc : Complex.exp c = ∑' n : ℕ, ((n.factorial : ℂ))⁻¹ * c ^ n := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
    simp [smul_eq_mul]
  have happ : (NormedSpace.exp A) ψ = ∑' n : ℕ, (((n.factorial : ℂ))⁻¹ • A ^ n) ψ := by
    conv_lhs => rw [NormedSpace.exp_eq_tsum ℂ]
    simpa using ContinuousLinearMap.map_tsum (ContinuousLinearMap.apply ℂ 𝓗 ψ) hsum
  have hterm : ∀ n : ℕ, (((n.factorial : ℂ))⁻¹ • A ^ n) ψ
      = (((n.factorial : ℂ))⁻¹ * c ^ n) • ψ := by
    intro n
    rw [smul_apply, hpow, smul_smul]
  rw [propagator, ← hA, happ]
  simp_rw [hterm]
  rw [hsumc.tsum_smul_const, ← hexpc]

/-- The propagator of a self-adjoint generator, packaged as a linear isometry. -/
def selfAdjointPropagator {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) : 𝓗 →ₗᵢ[ℂ] 𝓗 where
  toLinearMap := (propagator H t).toLinearMap
  norm_map' := norm_propagator_apply hH t

@[simp] theorem selfAdjointPropagator_apply {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ)
    (x : 𝓗) : selfAdjointPropagator hH t x = propagator H t x := rfl

/-- The isometric propagator acts on an eigenvector by a phase. -/
theorem selfAdjointPropagator_apply_eigen {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) (μ : ℂ)
    (ψ : 𝓗) (hψ : H ψ = μ • ψ) :
    selfAdjointPropagator hH t ψ = Complex.exp ((-(t : ℂ) * Complex.I) * μ) • ψ :=
  propagator_apply_eigen H t μ ψ hψ

end GaloisForLFunctions.HTGeometry
