import GaloisForLFunctions.RHTower.WeilPaperMixtureRealification
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Arbitrarily many invisible real correlation directions

The paper-derived consecutive-ratio sampler admits finite linear sections.
Rank-nullity leaves any requested number of independent sampled directions in
the kernel of a finite observer after positive conjugation averaging.
-/

noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Any `k` real observations miss `n` independent directions, detected using only the
`k+n` consecutive primitive ratios, with labels at most `k+n+2`. -/
theorem exists_paperNullObservationDirections (k n : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ D : (Fin n → ℝ) →ₗ[ℝ] paperNullMassSpace,
      (∀ v, T (paperRealMixture (D v).1) = 0) ∧
      Function.Injective ((paperConsecutiveSampler (k + n)).comp D) := by
  obtain ⟨S, hS⟩ := exists_paperConsecutiveSampler_rightInverse (k + n)
  let U := T.comp (paperRealMixture.comp (paperNullMassSpace.subtype.comp S))
  have hdim : Module.finrank ℝ (Fin n → ℝ) ≤ Module.finrank ℝ (LinearMap.ker U) := by
    have h := U.finrank_range_add_finrank_ker
    have hr := U.range.finrank_le
    simp only [Module.finrank_fin_fun] at h hr ⊢
    omega
  obtain ⟨J, hJ⟩ := finrank_le_iff_exists_linearMap.mp hdim
  let D := S.comp ((LinearMap.ker U).subtype.comp J)
  refine ⟨D, fun v => (J v).property, ?_⟩
  have hsample (v : Fin n → ℝ) : paperConsecutiveSampler (k + n) (D v) = (J v).1 :=
    congrArg (fun A : (Fin (k + n) → ℝ) →ₗ[ℝ] (Fin (k + n) → ℝ) => A (J v).1) hS
  intro v w hvw
  apply hJ
  apply Subtype.ext
  exact (hsample v).symm.trans (hvw.trans (hsample w))

end RHTower.WeilWorkPBAP
