import GaloisForLFunctions.HTGeometry.GomesPolynomialGroundState

/-!
# Complete polynomial dilaton kernel classification

Finite raw mass, existence of a nonzero Schwartz ground state, and a negative leading
coefficient in positive even degree are equivalent for every real polynomial. The
kernel is exactly one-dimensional in that sector and zero elsewhere. No convexity,
nondegenerate minimum, or coefficient hypotheses are supplied to these classifications.
-/

noncomputable section
open Polynomial MeasureTheory Filter Classical
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- Nonzero Schwartz ground states exist exactly for finite polynomial densities. -/
theorem gomesPolynomialHamiltonian_nonzero_kernel_iff (H : ℝ[X]) :
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM H ψ = 0) ↔
      IsFiniteMeasure (gomesDilatonMeasure H) := by
  constructor
  · rintro ⟨ψ, hψ, hk⟩
    have hc := (dilatonHamiltonian_kernel_classification H ψ).mp hk
    have hn : dilatonUndressed H ψ 0 ≠ 0 := by
      intro hz
      apply hψ
      ext x
      apply mul_left_cancel₀ (dilatonGauge_ne_zero H x)
      change dilatonUndressed H ψ x = dilatonGauge H x * 0
      rw [hc, hz, mul_zero]
    have hn2 : ‖dilatonUndressed H ψ 0‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hn)
    have hi : Integrable (fun x => dilatonWeight H x * ‖dilatonUndressed H ψ 0‖ ^ 2) :=
      (dilatonUndressed_weighted_integrable H ψ).congr
        (Eventually.of_forall (fun x => by
          change dilatonWeight H x * ‖dilatonUndressed H ψ x‖ ^ 2 = _
          rw [hc x]))
    rw [gomesDilatonMeasure_finite_iff_integrable]
    exact (hi.div_const (‖dilatonUndressed H ψ 0‖ ^ 2)).congr
      (Eventually.of_forall (fun x => mul_div_cancel_right₀ (dilatonWeight H x) hn2))
  · intro h
    let P : GomesFinitePolynomialProfile := ⟨H, h⟩
    exact ⟨gomesPolynomialGroundState P, gomesPolynomialGroundState_ne_zero P,
      gomesPolynomialGroundState_kernel P⟩

/-- The existence criterion is completely determined by polynomial degree and leading sign. -/
theorem gomesPolynomialHamiltonian_nonzero_kernel_polynomial_iff (H : ℝ[X]) :
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM H ψ = 0) ↔
      0 < H.natDegree ∧ Even H.natDegree ∧ H.leadingCoeff < 0 := by
  rw [gomesPolynomialHamiltonian_nonzero_kernel_iff, gomesDilatonMeasure_finite_polynomial_iff]

/-- The zero-kernel sector is exactly the infinite-mass sector. -/
theorem gomesPolynomialHamiltonian_ker_bot_iff (H : ℝ[X]) :
    LinearMap.ker (dilatonHamiltonianCLM H).toLinearMap = ⊥ ↔
      ¬ IsFiniteMeasure (gomesDilatonMeasure H) := by
  rw [← gomesPolynomialHamiltonian_nonzero_kernel_iff]
  constructor
  · rintro hb ⟨ψ, hn, hk⟩
    exact hn ((Submodule.eq_bot_iff _).mp hb ψ hk)
  · intro hn
    apply (Submodule.eq_bot_iff _).mpr
    intro ψ hk
    by_contra hψ
    exact hn ⟨ψ, hψ, hk⟩

/-- In the finite sector, the actual linear kernel equals the explicit half-density line. -/
theorem gomesPolynomialHamiltonian_ker_eq_span (P : GomesFinitePolynomialProfile) :
    LinearMap.ker (dilatonHamiltonianCLM P.val).toLinearMap =
      Submodule.span ℂ {gomesPolynomialGroundState P} := by
  ext ψ
  change dilatonHamiltonianCLM P.val ψ = 0 ↔ ψ ∈ Submodule.span ℂ {gomesPolynomialGroundState P}
  rw [gomesPolynomialGroundState_kernel_span, Submodule.mem_span_singleton]
  constructor <;> rintro ⟨c, hc⟩ <;> exact ⟨c, hc.symm⟩

/-- Every finite profile has a one-dimensional complex Schwartz ground space. -/
theorem gomesPolynomialHamiltonian_finrank_one (P : GomesFinitePolynomialProfile) :
    Module.finrank ℂ (LinearMap.ker (dilatonHamiltonianCLM P.val).toLinearMap) = 1 := by
  rw [gomesPolynomialHamiltonian_ker_eq_span]
  exact finrank_span_singleton (gomesPolynomialGroundState_ne_zero P)

/-- The ground-space dimension is classified for all real polynomials, without exceptions. -/
theorem gomesPolynomialHamiltonian_finrank (H : ℝ[X]) :
    Module.finrank ℂ (LinearMap.ker (dilatonHamiltonianCLM H).toLinearMap) =
      if IsFiniteMeasure (gomesDilatonMeasure H) then 1 else 0 := by
  classical
  by_cases h : IsFiniteMeasure (gomesDilatonMeasure H)
  · rw [if_pos h]
    exact gomesPolynomialHamiltonian_finrank_one ⟨H, h⟩
  · rw [if_neg h, (gomesPolynomialHamiltonian_ker_bot_iff H).mpr h, finrank_bot]

/-- A polynomial profile and its tensor dual cannot both carry nonzero Schwartz ground states. -/
theorem gomesPolynomialHamiltonian_no_dual_ground_states (H : ℝ[X]) :
    ¬ ((∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM H ψ = 0) ∧
      (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM (-H) ψ = 0)) := by
  rw [gomesPolynomialHamiltonian_nonzero_kernel_iff, gomesPolynomialHamiltonian_nonzero_kernel_iff]
  exact gomesFinitePolynomialProfiles_no_dual H

end GaloisForLFunctions.HTGeometry
