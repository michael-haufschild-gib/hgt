import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic

/-!
# Borgnakke--Larsen collision kinematics and orthogonal equivariance

Equations (2)--(3) of arXiv:2608.29825 in the dimensional convention of
Section 2.1. The incoming velocities live in actual Euclidean three-space;
internal energies are nonnegative, partition coordinates lie in `[0,1]`,
and scattering directions lie on the unit sphere. These are input domains,
not assumed conservation or symmetry laws. Conservation and equivariance
are proved from the explicit collision map, including zero-energy endpoints.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

abbrev CollisionVelocity := EuclideanSpace ℝ (Fin 3)
abbrev CollisionPartition := Set.Icc (0 : ℝ) 1
abbrev CollisionDirection := Metric.sphere (0 : CollisionVelocity) 1

/-- Relative kinetic energy plus the two internal energies. -/
def polyatomicCollisionEnergy (v w : CollisionVelocity) (I J : NNReal) : ℝ :=
  ‖v - w‖ ^ 2 / 4 + I + J

/-- Post-collision relative velocity in the chosen scattering direction. -/
def polyatomicRelativeOut (v w : CollisionVelocity) (I J : NNReal)
    (R : CollisionPartition) (s : CollisionDirection) : CollisionVelocity :=
  (2 * Real.sqrt (R.1 * polyatomicCollisionEnergy v w I J)) • s.1

/-- Outgoing velocity pair at fixed total momentum. -/
def polyatomicVelocitiesOut (v w : CollisionVelocity) (I J : NNReal)
    (R : CollisionPartition) (s : CollisionDirection) :
    CollisionVelocity × CollisionVelocity :=
  ((1 / 2 : ℝ) • (v + w + polyatomicRelativeOut v w I J R s),
   (1 / 2 : ℝ) • (v + w - polyatomicRelativeOut v w I J R s))

/-- Outgoing internal energies after kinetic and internal partitioning. -/
def polyatomicInternalOut (v w : CollisionVelocity) (I J : NNReal)
    (R r : CollisionPartition) : ℝ × ℝ :=
  (r.1 * (1 - R.1) * polyatomicCollisionEnergy v w I J,
   (1 - r.1) * (1 - R.1) * polyatomicCollisionEnergy v w I J)

/-- Available energy is nonnegative without excluding a stationary collision. -/
theorem polyatomicCollisionEnergy_nonneg (v w : CollisionVelocity) (I J : NNReal) :
    0 ≤ polyatomicCollisionEnergy v w I J := by
  unfold polyatomicCollisionEnergy
  positivity

/-- Both internal energies remain in the physical domain, including endpoints. -/
theorem polyatomicInternalOut_nonneg (v w : CollisionVelocity) (I J : NNReal)
    (R r : CollisionPartition) :
    0 ≤ (polyatomicInternalOut v w I J R r).1 ∧
      0 ≤ (polyatomicInternalOut v w I J R r).2 := by
  have hE := polyatomicCollisionEnergy_nonneg v w I J
  have hR : 0 ≤ 1 - R.1 := sub_nonneg.mpr R.2.2
  have hr : 0 ≤ 1 - r.1 := sub_nonneg.mpr r.2.2
  exact ⟨mul_nonneg (mul_nonneg r.2.1 hR) hE,
    mul_nonneg (mul_nonneg hr hR) hE⟩

/-- The partition spends exactly the nonkinetic energy budget. -/
theorem polyatomicInternalOut_sum (v w : CollisionVelocity) (I J : NNReal)
    (R r : CollisionPartition) :
    (polyatomicInternalOut v w I J R r).1 +
      (polyatomicInternalOut v w I J R r).2 =
      (1 - R.1) * polyatomicCollisionEnergy v w I J := by
  simp only [polyatomicInternalOut]
  ring

/-- The prescribed scattering direction has unit norm. -/
theorem collisionDirection_norm (s : CollisionDirection) : ‖s.1‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using s.2

/-- The new relative kinetic energy is exactly the assigned fraction. -/
theorem polyatomicRelativeOut_norm_sq (v w : CollisionVelocity) (I J : NNReal)
    (R : CollisionPartition) (s : CollisionDirection) :
    ‖polyatomicRelativeOut v w I J R s‖ ^ 2 =
      4 * R.1 * polyatomicCollisionEnergy v w I J := by
  have hRE := mul_nonneg R.2.1 (polyatomicCollisionEnergy_nonneg v w I J)
  rw [polyatomicRelativeOut, norm_smul, collisionDirection_norm, mul_one,
    Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hRE]
  ring

/-- Exact momentum conservation for every admissible collision. -/
theorem polyatomicVelocitiesOut_momentum (v w : CollisionVelocity) (I J : NNReal)
    (R : CollisionPartition) (s : CollisionDirection) :
    (polyatomicVelocitiesOut v w I J R s).1 +
      (polyatomicVelocitiesOut v w I J R s).2 = v + w := by
  simp only [polyatomicVelocitiesOut]
  module

/-- Reconstructed outgoing velocities have the prescribed relative velocity. -/
theorem polyatomicVelocitiesOut_relative (v w : CollisionVelocity) (I J : NNReal)
    (R : CollisionPartition) (s : CollisionDirection) :
    (polyatomicVelocitiesOut v w I J R s).1 -
      (polyatomicVelocitiesOut v w I J R s).2 =
      polyatomicRelativeOut v w I J R s := by
  simp only [polyatomicVelocitiesOut]
  module

/-- Exact conservation of collision-frame energy. -/
theorem polyatomicCollisionEnergy_conserved (v w : CollisionVelocity) (I J : NNReal)
    (R r : CollisionPartition) (s : CollisionDirection) :
    ‖(polyatomicVelocitiesOut v w I J R s).1 -
        (polyatomicVelocitiesOut v w I J R s).2‖ ^ 2 / 4 +
      (polyatomicInternalOut v w I J R r).1 +
      (polyatomicInternalOut v w I J R r).2 =
      polyatomicCollisionEnergy v w I J := by
  rw [polyatomicVelocitiesOut_relative, polyatomicRelativeOut_norm_sq]
  have h := polyatomicInternalOut_sum v w I J R r
  linear_combination h

/-- The parallelogram identity converts relative and total momentum to lab energy. -/
theorem collisionLabEnergy_decomposition (v w : CollisionVelocity) :
    (‖v‖ ^ 2 + ‖w‖ ^ 2) / 2 =
      (‖v + w‖ ^ 2 + ‖v - w‖ ^ 2) / 4 := by
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

/-- Conservation holds for the full laboratory-frame molecular energy. -/
theorem polyatomicLabEnergy_conserved (v w : CollisionVelocity) (I J : NNReal)
    (R r : CollisionPartition) (s : CollisionDirection) :
    (‖(polyatomicVelocitiesOut v w I J R s).1‖ ^ 2 +
      ‖(polyatomicVelocitiesOut v w I J R s).2‖ ^ 2) / 2 +
      (polyatomicInternalOut v w I J R r).1 +
      (polyatomicInternalOut v w I J R r).2 =
      (‖v‖ ^ 2 + ‖w‖ ^ 2) / 2 + I + J := by
  rw [collisionLabEnergy_decomposition, polyatomicVelocitiesOut_momentum,
    polyatomicVelocitiesOut_relative, polyatomicRelativeOut_norm_sq,
    collisionLabEnergy_decomposition]
  have h := polyatomicInternalOut_sum v w I J R r
  dsimp only [polyatomicCollisionEnergy] at h ⊢
  linear_combination h

/-- Rotate a unit scattering direction by an arbitrary orthogonal transformation. -/
def collisionRotateDirection (g : CollisionVelocity ≃ₗᵢ[ℝ] CollisionVelocity)
    (s : CollisionDirection) : CollisionDirection :=
  ⟨g s.1, by simpa only [Metric.mem_sphere, dist_zero_right, g.norm_map]
    using collisionDirection_norm s⟩

/-- Collision energy is invariant under the full orthogonal group, hence under SO(3). -/
theorem polyatomicCollisionEnergy_rotate (g : CollisionVelocity ≃ₗᵢ[ℝ] CollisionVelocity)
    (v w : CollisionVelocity) (I J : NNReal) :
    polyatomicCollisionEnergy (g v) (g w) I J = polyatomicCollisionEnergy v w I J := by
  simp only [polyatomicCollisionEnergy, ← map_sub, g.norm_map]

/-- Internal partitioning is a rotational scalar. -/
theorem polyatomicInternalOut_rotate (g : CollisionVelocity ≃ₗᵢ[ℝ] CollisionVelocity)
    (v w : CollisionVelocity) (I J : NNReal) (R r : CollisionPartition) :
    polyatomicInternalOut (g v) (g w) I J R r = polyatomicInternalOut v w I J R r := by
  simp only [polyatomicInternalOut, polyatomicCollisionEnergy_rotate]

/-- The explicit relative scattering map commutes with every orthogonal transformation. -/
theorem polyatomicRelativeOut_rotate (g : CollisionVelocity ≃ₗᵢ[ℝ] CollisionVelocity)
    (v w : CollisionVelocity) (I J : NNReal) (R : CollisionPartition)
    (s : CollisionDirection) :
    polyatomicRelativeOut (g v) (g w) I J R (collisionRotateDirection g s) =
      g (polyatomicRelativeOut v w I J R s) := by
  simp only [polyatomicRelativeOut, collisionRotateDirection,
    polyatomicCollisionEnergy_rotate, map_smul]

/-- Full Borgnakke--Larsen equivariance, derived rather than assumed. -/
theorem polyatomicVelocitiesOut_rotate (g : CollisionVelocity ≃ₗᵢ[ℝ] CollisionVelocity)
    (v w : CollisionVelocity) (I J : NNReal) (R : CollisionPartition)
    (s : CollisionDirection) :
    polyatomicVelocitiesOut (g v) (g w) I J R (collisionRotateDirection g s) =
      (g (polyatomicVelocitiesOut v w I J R s).1,
       g (polyatomicVelocitiesOut v w I J R s).2) := by
  simp only [polyatomicVelocitiesOut, polyatomicRelativeOut_rotate,
    map_smul, map_add, map_sub]

end GaloisForLFunctions.HTGeometry
