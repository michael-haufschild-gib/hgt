import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Homotopy.Product

/-!
# Local logarithm nullhomotopy for unitary loops

A based loop in a unital C⋆-algebra is nullhomotopic whenever its image stays in the open
radius-two ball about the identity. The contraction uses Mathlib's continuous principal
self-adjoint logarithm on that ball and keeps both path endpoints fixed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Radial principal-logarithm contraction of a based unitary loop contained
in the open radius-two ball about the identity. -/
def unitaryLocalLogHomotopy {A : Type*} [CStarAlgebra A]
    (p : Path (1 : unitary A) 1)
    (hp : ∀ t, ‖((p t : A) - 1)‖ < 2) :
    p.Homotopy (Path.refl 1) := by
  have harg : Continuous (fun t ↦ Unitary.argSelfAdjoint (p t)) := by
    apply Unitary.continuousOn_argSelfAdjoint.comp_continuous p.continuous
    intro t
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hp t
  have harg_one : Unitary.argSelfAdjoint (1 : unitary A) = 0 := by
    simpa using (argSelfAdjoint_expUnitary
      (x := (0 : selfAdjoint A)) (by simpa using Real.pi_pos))
  let Hmap : C(unitInterval × unitInterval, unitary A) :=
    ⟨fun st ↦ selfAdjoint.expUnitary
        ((1 - (st.1 : ℝ)) • Unitary.argSelfAdjoint (p st.2)), by
      apply selfAdjoint.continuous_expUnitary.comp
      exact (by fun_prop : Continuous (fun st : unitInterval × unitInterval ↦
        (1 - (st.1 : ℝ)))).smul (harg.comp continuous_snd)⟩
  refine
    { toContinuousMap := Hmap
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro t
    change selfAdjoint.expUnitary
      ((1 - (0 : ℝ)) • Unitary.argSelfAdjoint (p t)) = p t
    simpa using expUnitary_argSelfAdjoint (hp t)
  · intro t
    simp [Hmap]
  · intro t x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [Hmap, harg_one]

/-- Every based unitary loop contained in the principal logarithm ball is
endpoint-fixed homotopic to the constant loop. -/
theorem unitaryLocalLog_nullhomotopic {A : Type*} [CStarAlgebra A]
    (p : Path (1 : unitary A) 1)
    (hp : ∀ t, ‖((p t : A) - 1)‖ < 2) :
    p.Homotopic (Path.refl 1) :=
  ⟨unitaryLocalLogHomotopy p hp⟩

end

end GaloisForLFunctions.HTGeometry
