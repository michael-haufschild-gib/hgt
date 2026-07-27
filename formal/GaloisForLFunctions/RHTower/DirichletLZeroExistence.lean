import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne
import GaloisForLFunctions.RHTower.DirichletCompletedLRayGrowth
import GaloisForLFunctions.HTGeometry.EntireLogarithm
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Unconditional existence of a Dirichlet L-zero in the right half-plane

The completed L-function of a nontrivial character is entire, carries an order-one growth envelope
and grows super-linearly along the real ray.  A zero-free entire function with a subquadratic
envelope has an affine logarithm, hence at most exponential growth on every ray; the Archimedean
factor forbids that.  So `Λ(·,χ)` has a zero.

For a primitive character the functional equation places every such zero in the right half-plane:
reflecting a zero with `Re ≤ 0` would produce a zero of `L(·,χ⁻¹)` with `Re ≥ 1`, where that
function does not vanish.  Dividing by the Archimedean factor transfers the zero to `L(·,χ)`.
-/

open Complex Filter
open scoped Topology

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- The completed L-function does not vanish somewhere on the real ray: at a point where the
ray-growth bound applies with slope `1`, vanishing would force `σ < 0`. -/
theorem exists_completedLFunction_ne_zero_ray {χ : DirichletCharacter ℂ N} :
    ∃ σ : ℝ, 1 ≤ σ ∧ DirichletCharacter.completedLFunction χ (σ : ℂ) ≠ 0 := by
  obtain ⟨σ, hσ1, hlt⟩ := completedLFunction_ray_growth (χ := χ) 1
  refine ⟨σ, hσ1, fun h => ?_⟩
  rw [h, norm_zero, Real.log_zero] at hlt
  linarith

/-- **The root number of a primitive character is nonzero.**  If it vanished, the functional
equation would make the completed L-function identically zero, contradicting its nonvanishing on
the real ray. -/
theorem rootNumber_ne_zero {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) :
    χ.rootNumber ≠ 0 := by
  obtain ⟨σ, hσ1, hne⟩ := exists_completedLFunction_ne_zero_ray (χ := χ)
  intro h0
  refine hne ?_
  have hFE := hprim.completedLFunction_one_sub (1 - (σ : ℂ))
  rw [show (1 : ℂ) - (1 - (σ : ℂ)) = (σ : ℂ) by ring, h0] at hFE
  simpa using hFE

/-- **The completed L-function of a nontrivial character has a zero.**  Hadamard's argument in the
form `exists_zero_of_superlinear_ray_growth`: the order-one envelope is subquadratic, so a zero-free
completion would grow at most exponentially on the real ray, which the Archimedean factor
contradicts. -/
theorem exists_completedLFunction_eq_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ z : ℂ, DirichletCharacter.completedLFunction χ z = 0 := by
  obtain ⟨C, hC, hgrow⟩ := (completedLFunction_orderOneEnvelope hχ).subquadratic
  exact GaloisForLFunctions.HTGeometry.exists_zero_of_superlinear_ray_growth
    (DirichletCharacter.differentiable_completedLFunction hχ)
    (by norm_num) (by norm_num) hC hgrow (fun A => completedLFunction_ray_growth A)

/-- **A nontrivial primitive Dirichlet L-function has a zero with positive real part.** -/
theorem exists_LFunction_eq_zero_pos_re {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    ∃ ρ : ℂ, 0 < ρ.re ∧ DirichletCharacter.LFunction χ ρ = 0 := by
  obtain ⟨z, hz⟩ := exists_completedLFunction_eq_zero hχ
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    exact hχ (by rw [← inv_inv χ, h, inv_one])
  have hre : 0 < z.re := by
    rcases le_or_gt z.re 0 with hcon | hpos
    swap
    · exact hpos
    exfalso
    have hwre : 1 ≤ (1 - z).re := by
      rw [Complex.sub_re, Complex.one_re]; linarith
    have hwne : (1 : ℂ) - z ≠ 0 := by
      intro h
      rw [h] at hwre
      simp at hwre
      linarith
    have hFE := hprim.completedLFunction_one_sub (1 - z)
    rw [show (1 : ℂ) - (1 - z) = z by ring, hz] at hFE
    have hNne : ((N : ℂ)) ^ ((1 - z) - 1 / 2) ≠ 0 := by
      refine fun h => ?_
      rw [Complex.cpow_eq_zero_iff] at h
      exact (Nat.cast_ne_zero.mpr (NeZero.ne N)) h.1
    have hΛinv : DirichletCharacter.completedLFunction χ⁻¹ (1 - z) = 0 := by
      rcases mul_eq_zero.mp hFE.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hNne
        · exact absurd h' (rootNumber_ne_zero hprim)
      · exact h
    have hLinv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - z)
      (Or.inl hwne)
    rw [hΛinv, zero_div] at hLinv
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχinv) hwre hLinv
  refine ⟨z, hre, ?_⟩
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inl hzne)
  rw [hz, zero_div] at hL
  exact hL

end RHTower
