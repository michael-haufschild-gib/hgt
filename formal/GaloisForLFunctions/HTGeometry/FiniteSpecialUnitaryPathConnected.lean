import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitaryExponentialAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Topology.Separation.Connected

/-!
# Path-connected finite unitary and special-unitary groups

Every finite complex unitary matrix is path-connected to the identity.  The
proof chooses a scalar phase on the circle outside the finite spectrum, so
the phase-scaled matrix has no `-1` eigenvalue and admits Mathlib's
self-adjoint logarithm path.  The explicit determinant normalizer transports
these paths to finite special-unitary groups.
-/

open Matrix Complex
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A point of the complex unit circle, regarded as a scalar unitary. -/
def circleUnitary (z : Circle) : unitary ℂ :=
  ⟨z, Unitary.mem_iff.mpr ⟨by
    change star (z : ℂ) * (z : ℂ) = 1
    calc
      star (z : ℂ) * (z : ℂ) = ↑(Complex.normSq (z : ℂ)) :=
        (Complex.normSq_eq_conj_mul_self (z := (z : ℂ))).symm
      _ = 1 := by exact_mod_cast Circle.normSq_coe z
  , by
    change (z : ℂ) * star (z : ℂ) = 1
    calc
      (z : ℂ) * star (z : ℂ) = ↑(Complex.normSq (z : ℂ)) := Complex.mul_conj _
      _ = 1 := by exact_mod_cast Circle.normSq_coe z⟩⟩

/-- Circle scalars vary continuously as scalar unitaries. -/
theorem continuous_circleUnitary :
    Continuous (circleUnitary : Circle → unitary ℂ) := by
  apply continuous_induced_rng.2
  change Continuous (fun z : Circle => (z : ℂ))
  fun_prop

/-- Scalar multiplication of a finite unitary matrix by the complex circle. -/
def circleScaleUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) : Circle → Matrix.unitaryGroup ι ℂ :=
  fun z => circleUnitary z • U

/-- Circle scalar multiplication of a finite unitary is continuous. -/
theorem continuous_circleScaleUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    Continuous (circleScaleUnitary U) := by
  apply continuous_induced_rng.2
  change Continuous (fun z : Circle => (z : ℂ) • (U : Matrix ι ι ℂ))
  fun_prop

/-- Circle scalar multiplication at `1` fixes a finite unitary. -/
theorem circleScaleUnitary_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) : circleScaleUnitary U 1 = U := by
  apply Subtype.ext
  simp [circleScaleUnitary, circleUnitary]

/-- Some point of the complex unit circle avoids the finite spectrum of every
finite matrix. -/
theorem exists_circle_not_mem_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    ∃ z : Circle, (z : ℂ) ∉ spectrum ℂ (U : Matrix ι ι ℂ) := by
  letI : Nontrivial Circle := ⟨⟨1, -1,
    by simpa using (Circle.neg_ne_self (1 : Circle)).symm⟩⟩
  letI : Infinite Circle := PreconnectedSpace.infinite
  let bad : Set Circle := ((fun z : Circle => (z : ℂ)) ⁻¹'
    spectrum ℂ (U : Matrix ι ι ℂ))
  have hbad : bad.Finite := by
    exact (Matrix.finite_spectrum (U : Matrix ι ι ℂ)).preimage
      (fun _ _ _ _ h => Circle.coe_injective h)
  rcases hbad.exists_notMem with ⟨z, hz⟩
  exact ⟨z, hz⟩

/-- A circle phase can be chosen so its scalar multiple of a finite unitary
has no `-1` spectral value. -/
theorem exists_circle_minus_one_not_mem_scaled_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    ∃ z : Circle, (-1 : ℂ) ∉ spectrum ℂ
      (circleScaleUnitary U (-(z⁻¹)) : Matrix ι ι ℂ) := by
  rcases exists_circle_not_mem_spectrum U with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  intro h
  have h' : (-1 : ℂ) ∈ spectrum ℂ
      ((Circle.toUnits (-(z⁻¹))) • (U : Matrix ι ι ℂ)) := by
    simpa [circleScaleUnitary, circleUnitary, Circle.toUnits_apply,
      Units.smul_def] using h
  rw [spectrum.unit_smul_eq_smul, Set.mem_smul_set_iff_inv_smul_mem] at h'
  apply hz
  change (((Circle.toUnits (-(z⁻¹)))⁻¹ : ℂ) • (-1 : ℂ)) ∈
    spectrum ℂ (U : Matrix ι ι ℂ) at h'
  simpa [Circle.toUnits_apply] using h'

/-- A path from a finite unitary to any of its circle scalar multiples. -/
noncomputable def path_to_circleScale
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (r : Circle) :
    Path U (circleScaleUnitary U r) := by
  let p := (PathConnectedSpace.somePath (1 : Circle) r).map
    (continuous_circleScaleUnitary U)
  rw [circleScaleUnitary_one] at p
  exact p

/-- The matrix underlying a circle-scaled unitary is unitary.  Naming this
certificate avoids expensive repeated instance synthesis in the local-log
path below. -/
theorem circleScaleUnitary_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (r : Circle) :
    (circleScaleUnitary U r : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ :=
  (circleScaleUnitary U r).2

/-- A circle-scaled finite unitary with no `-1` spectral value is connected to
the identity by its self-adjoint logarithm path. -/
noncomputable def path_circleScale_to_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (r : Circle)
    (h : (-1 : ℂ) ∉ spectrum ℂ
      (circleScaleUnitary U r : Matrix ι ι ℂ)) :
    Path (circleScaleUnitary U r) 1 := by
  /- This explicit local instance is definitionally assembled from Mathlib's
  scoped operator-norm matrix structures.  Keeping it named prevents the
  elaborator from repeatedly rediscovering the same composite C⋆ structure. -/
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  let V : Matrix.unitaryGroup ι ℂ :=
    ⟨(circleScaleUnitary U r : Matrix ι ι ℂ), circleScaleUnitary_mem U r⟩
  have hdist : ‖(circleScaleUnitary U r : Matrix ι ι ℂ) - 1‖ < 2 :=
    (Unitary.norm_sub_one_lt_two_iff (circleScaleUnitary_mem U r)).mpr h
  have p := (selfAdjoint.expUnitaryPathToOne (Unitary.argSelfAdjoint V)).symm
  rw [expUnitary_argSelfAdjoint hdist] at p
  change Path V 1 at p
  change Path (circleScaleUnitary U r) 1
  exact p

/-- Every finite complex unitary matrix is joined to the identity. -/
theorem joined_one_finiteUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) : Joined (1 : Matrix.unitaryGroup ι ℂ) U := by
  rcases exists_circle_minus_one_not_mem_scaled_spectrum U with ⟨z, hz⟩
  let r : Circle := -(z⁻¹)
  have hVone : Path (circleScaleUnitary U r) 1 :=
    path_circleScale_to_one U r (by simpa only [r] using hz)
  exact ⟨hVone.symm.trans (path_to_circleScale U r).symm⟩

/-- Finite complex unitary groups are path connected. -/
noncomputable instance finiteUnitaryPathConnectedSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    PathConnectedSpace (Matrix.unitaryGroup ι ℂ) where
  nonempty := ⟨1⟩
  joined U V := (joined_one_finiteUnitary U).symm.trans
    (joined_one_finiteUnitary V)

/-- Every finite special-unitary matrix is joined to the identity by pushing a
finite-unitary path through the explicit determinant normalizer. -/
theorem joined_one_finiteSpecialUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i0 : ι)
    (S : Matrix.specialUnitaryGroup ι ℂ) :
    Joined (1 : Matrix.specialUnitaryGroup ι ℂ) S := by
  let p : Path (1 : Matrix.unitaryGroup ι ℂ) (specialUnitaryToUnitary S) :=
    (joined_one_finiteUnitary (specialUnitaryToUnitary S)).somePath
  have q := p.map (continuous_specialUnitaryNormalize i0)
  have hsource : specialUnitaryNormalize i0 (1 : Matrix.unitaryGroup ι ℂ) = 1 := by
    change specialUnitaryNormalize i0 (specialUnitaryToUnitary
      (1 : Matrix.specialUnitaryGroup ι ℂ)) = 1
    exact specialUnitaryNormalize_toUnitary i0 1
  rw [hsource, specialUnitaryNormalize_toUnitary] at q
  exact ⟨q⟩

/-- Nonempty finite complex special-unitary groups are path connected. -/
noncomputable instance finiteSpecialUnitaryPathConnectedSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    PathConnectedSpace (Matrix.specialUnitaryGroup ι ℂ) where
  nonempty := ⟨1⟩
  joined S T := by
    let i0 : ι := Classical.choice ‹Nonempty ι›
    exact (joined_one_finiteSpecialUnitary i0 S).symm.trans
      (joined_one_finiteSpecialUnitary i0 T)

/-- Every finite unitary is a finite product of self-adjoint exponential
unitaries.  This is the factorization form of the connectedness theorem used
to move a translated exponential chart to an arbitrary unitary point. -/
theorem exists_list_expUnitary_prod_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    ∃ l : List (selfAdjoint (Matrix ι ι ℂ)),
      (l.map selfAdjoint.expUnitary).prod = U := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
  apply Unitary.mem_pathComponentOne_iff.mp
  exact mem_pathComponent_iff.mpr (joined_one_finiteUnitary U)

end

end GaloisForLFunctions.HTGeometry
