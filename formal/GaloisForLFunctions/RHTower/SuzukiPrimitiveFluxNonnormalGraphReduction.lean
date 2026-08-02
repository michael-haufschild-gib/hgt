import GaloisForLFunctions.RHTower.SuzukiCoordinateCutoffPrimitiveFlux

/-!
# Suzuki primitive-flux nonnormal graph reduction

A rough primitive source `G'` in the differentiated Suzuki normal equation can be removed by
augmenting the state with the flux `(2L + C)F - G`.  The first two theorems certify the exact
unweighted and exponentially conjugated identities.  The final two theorems certify the scalar
absorption step in the weighted graph estimate.

All results are unconditional.  They assume neither RH nor existence of the conjectural completed
Suzuki carrier.
-/

namespace GaloisForLFunctions.RHTower

/-- Zero-order coefficient in the primitive-flux equation. -/
def fluxZeroOrder {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Z : Module.End ℝ V) : Module.End ℝ V :=
  (2 : ℝ) • LinearMap.id - Z

/-- Pointwise core of `Y' = (2I - Z)F + H` for
`Y = (2L I + C)F - G`.

The hypothesis is the differentiated equation
`(2L I + C)F' + ZF = G' + H`.  No regularity of the primitive `G` is encoded or assumed. -/
theorem primitiveFluxSystem_pointwise
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℝ) (C Z : Module.End ℝ V)
    (F Fdot Gdot H : V)
    (hEq : twoLPlus L C Fdot + Z F = Gdot + H) :
    (2 : ℝ) • F + twoLPlus L C Fdot - Gdot =
      fluxZeroOrder Z F + H := by
  have hAF :
      twoLPlus L C Fdot = Gdot + H - Z F :=
    (eq_sub_iff_add_eq).2 hEq
  have hcore : twoLPlus L C Fdot - Gdot = H - Z F := by
    rw [hAF]
    abel
  calc
    (2 : ℝ) • F + twoLPlus L C Fdot - Gdot =
        (2 : ℝ) • F + (twoLPlus L C Fdot - Gdot) := by abel
    _ = (2 : ℝ) • F + (H - Z F) := by rw [hcore]
    _ = fluxZeroOrder Z F + H := by
      simp only [fluxZeroOrder, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq]
      abel

/-- Exact pointwise cancellation after exponential conjugation.

The displayed left side is `(∂L - σ)((2L I + C)V - G)`.  In particular every occurrence of
`Gdot` cancels from the resulting flux equation. -/
theorem primitiveFluxSystem_exponential_pointwise
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L σ : ℝ) (C Z : Module.End ℝ V)
    (V₀ Vdot G Gdot H : V)
    (hEq :
      twoLPlus L C (Vdot - σ • V₀) + Z V₀ =
        (Gdot - σ • G) + H) :
    ((2 : ℝ) • V₀ + twoLPlus L C Vdot - Gdot) -
        σ • (twoLPlus L C V₀ - G) =
      fluxZeroOrder Z V₀ + H := by
  have hcore :
      twoLPlus L C Vdot - σ • twoLPlus L C V₀ - Gdot + σ • G =
        H - Z V₀ := by
    rw [map_sub, map_smul] at hEq
    have hAV :
        twoLPlus L C Vdot - σ • twoLPlus L C V₀ =
          (Gdot - σ • G + H) - Z V₀ :=
      (eq_sub_iff_add_eq).2 hEq
    rw [hAV]
    abel
  rw [show
    ((2 : ℝ) • V₀ + twoLPlus L C Vdot - Gdot) -
          σ • (twoLPlus L C V₀ - G) =
        (2 : ℝ) • V₀ +
          (twoLPlus L C Vdot - σ • twoLPlus L C V₀ - Gdot + σ • G) by
      module]
  rw [hcore]
  simp only [fluxZeroOrder, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]
  module

/-- Denominator-free absorption core for the weighted primitive-flux graph estimate.

Interpret `v,y,g,h` as nonnegative norms.  The proof itself needs only the displayed order
hypotheses. -/
theorem primitiveFlux_absorption_mul
    {c d σ v y g h : ℝ}
    (hσ : 0 ≤ σ)
    (hcv : c * v ≤ y + g)
    (hσy : σ * y ≤ d * v + h) :
    (σ * c - d) * v ≤ σ * g + h := by
  calc
    (σ * c - d) * v = σ * (c * v) - d * v := by ring
    _ ≤ σ * (y + g) - d * v := sub_le_sub_right (mul_le_mul_of_nonneg_left hcv hσ) _
    _ ≤ σ * g + h := by linarith

/-- Division form of the primitive-flux absorption estimate when the terminal coercive gap is
strictly positive. -/
theorem primitiveFlux_absorption_div
    {c d σ v g h : ℝ}
    (hgap : 0 < σ * c - d)
    (hbound : (σ * c - d) * v ≤ σ * g + h) :
    v ≤ (σ * g + h) / (σ * c - d) := by
  exact (le_div_iff₀ hgap).2 (by simpa [mul_comm] using hbound)

end GaloisForLFunctions.RHTower
