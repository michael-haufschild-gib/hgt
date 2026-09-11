import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAbsoluteSynthesis
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyShift
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
open Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

private theorem dense_synthesis_maps_eq
    {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : I → E) (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E) (hdense : DenseRange S)
    (hsum : ∀ c, HasSum (fun i => c i • v i) (S c))
    (A B : E →L[ℂ] F) (hv : ∀ i, A (v i) = B (v i)) (u : E) : A u = B u := by
  have hcore : ∀ x : E, x ∈ Set.range S → A x = B x := by
    rintro _ ⟨c, rfl⟩
    have ha := (hsum c).mapL A
    have hb := (hsum c).mapL B
    simp only [map_smul, hv] at ha
    simp only [map_smul] at hb
    exact ha.unique hb
  exact hdense.induction hcore (isClosed_eq A.continuous B.continuous) u


private theorem coefficient_eigen_from_dense_synthesis
    {I E : Type*} [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : I → E) (a : I → E →L[ℂ] ℂ)
    (hdual : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E) (hdense : DenseRange S)
    (hsum : ∀ c, HasSum (fun i => c i • v i) (S c))
    (T : E →L[ℂ] E) (z : I → ℂ) (hT : ∀ i, T (v i) = z i • v i)
    (u : E) (i : I) : a i (T u) = z i * a i u := by
  change ((a i).comp T) u = (z i • a i) u
  apply dense_synthesis_maps_eq v S hdense hsum
  intro j
  change a i (T (v j)) = z i * a i (v j)
  rw [hT, map_smul, smul_eq_mul, hdual]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- The derivative shift multiplies each canonical scalar frequency amplitude by
its own unit boundary rate, on every vector of the completed frequency space. -/
theorem causalFrequencyCoefficient_shift (b ω : ℝ) (u : causalFrequencySpace b) :
    causalFrequencyCoefficient b ω (causalFrequencyShift b u) =
      (causalUnitBoundaryRate b ω).val * causalFrequencyCoefficient b ω u :=
  coefficient_eigen_from_dense_synthesis (causalFrequencyMode b) (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_mode b) (causalFrequencyAbsoluteSynthesis b)
    (causalFrequencyAbsoluteSynthesis_denseRange b) (causalFrequencyAbsoluteSynthesis_hasSum b)
    (causalFrequencyShift b).toLinearIsometry.toContinuousLinearMap
    (fun η => (causalUnitBoundaryRate b η).val) (causalFrequencyShift_mode b) u ω

/-- The inverse derivative shift multiplies each canonical amplitude by the
reciprocal boundary rate. -/
theorem causalFrequencyCoefficient_shift_symm (b ω : ℝ) (u : causalFrequencySpace b) :
    causalFrequencyCoefficient b ω ((causalFrequencyShift b).symm u) =
      (causalUnitBoundaryRate b ω).val⁻¹ * causalFrequencyCoefficient b ω u :=
  coefficient_eigen_from_dense_synthesis (causalFrequencyMode b) (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_mode b) (causalFrequencyAbsoluteSynthesis b)
    (causalFrequencyAbsoluteSynthesis_denseRange b) (causalFrequencyAbsoluteSynthesis_hasSum b)
    (causalFrequencyShift b).symm.toLinearIsometry.toContinuousLinearMap
    (fun η => (causalUnitBoundaryRate b η).val⁻¹) (causalFrequencyShift_symm_mode b) u ω

end RHTower.FokasLenells
