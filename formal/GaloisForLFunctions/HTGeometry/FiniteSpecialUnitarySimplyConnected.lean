import GaloisForLFunctions.HTGeometry.FiniteUnitaryFundamentalGroupReindex

/-!
# Global simple connectivity of finite special-unitary groups

Determinant normalization retracts `U(ι)` onto `SU(ι)`. Since determinant
classifies unitary loop classes, every special-unitary loop contracts.
Path connectedness transports this conclusion to all basepoints and all
pairs of paths. No logarithm chart or spectral confinement is required.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inclusion of the special-unitary group as a continuous homomorphism. -/
def finiteSpecialUnitaryInclusionHom :
    Matrix.specialUnitaryGroup ι ℂ →ₜ* Matrix.unitaryGroup ι ℂ where
  toFun := specialUnitaryToUnitary
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by
    apply continuous_induced_rng.2
    exact continuous_subtype_val

private theorem normalize_one (i0 : ι) :
    specialUnitaryNormalize i0 (1 : Matrix.unitaryGroup ι ℂ) = 1 :=
  specialUnitaryNormalize_toUnitary i0 1

private def normalizeFundamentalGroup (i0 : ι) :
    FundamentalGroup (Matrix.unitaryGroup ι ℂ) 1 →*
      FundamentalGroup (Matrix.specialUnitaryGroup ι ℂ) 1 :=
  FundamentalGroup.mapOfEq
    ⟨specialUnitaryNormalize i0, continuous_specialUnitaryNormalize i0⟩ (normalize_one i0)

private theorem normalizeFundamentalGroup_leftInverse (i0 : ι) :
    Function.LeftInverse (normalizeFundamentalGroup i0)
      (fundamentalGroupContinuousHom (finiteSpecialUnitaryInclusionHom (ι := ι))) := by
  intro p
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [fundamentalGroupContinuousHom_mk]
    unfold normalizeFundamentalGroup
    rw [FundamentalGroup.mapOfEq_apply]
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk p
    congr 1
    apply Path.ext
    funext t
    exact specialUnitaryNormalize_toUnitary i0 (p t)

private theorem determinant_inclusion_fundamentalGroup
    (p : FundamentalGroup (Matrix.specialUnitaryGroup ι ℂ) 1) :
    fundamentalGroupContinuousHom (finiteUnitaryDeterminant ι)
      (fundamentalGroupContinuousHom finiteSpecialUnitaryInclusionHom p) = 1 := by
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [fundamentalGroupContinuousHom_mk, fundamentalGroupContinuousHom_mk]
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk (Path.refl 1)
    congr 1
    ext t
    exact (Matrix.mem_specialUnitaryGroup_iff.mp (p t).2).2

/-- Every identity-based special-unitary loop class is trivial, for arbitrary
nonempty finite coordinate carriers. -/
theorem finiteSpecialUnitary_fundamentalGroup_eq_one [Nonempty ι]
    (p : FundamentalGroup (Matrix.specialUnitaryGroup ι ℂ) 1) : p = 1 := by
  let i0 : ι := Classical.choice inferInstance
  apply (normalizeFundamentalGroup_leftInverse i0).injective
  apply finiteUnitaryDeterminant_fundamentalGroup_bijective_index.1
  rw [map_one, map_one]
  exact determinant_inclusion_fundamentalGroup p

/-- Every finite complex special-unitary group is simply connected, including
the empty matrix carrier. -/
instance finiteSpecialUnitarySimplyConnectedSpace :
    SimplyConnectedSpace (Matrix.specialUnitaryGroup ι ℂ) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    infer_instance
  | inr h =>
    letI := h
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨inferInstance, fun S p => ?_⟩
    let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected S
      (1 : Matrix.specialUnitaryGroup ι ℂ)
    apply Path.Homotopic.Quotient.exact
    change Path.Homotopic.Quotient.mk p = (1 : FundamentalGroup _ S)
    apply e.injective
    rw [map_one]
    exact finiteSpecialUnitary_fundamentalGroup_eq_one _

/-- All finite special-unitary loops contract, at every basepoint. -/
theorem finiteSpecialUnitary_loop_nullhomotopic
    (S : Matrix.specialUnitaryGroup ι ℂ) (p : Path S S) :
    p.Homotopic (Path.refl S) :=
  SimplyConnectedSpace.paths_homotopic p (Path.refl S)

open scoped Matrix.Norms.L2Operator in
/-- Determinant normalization also makes the special-unitary group locally
path connected: it is a continuous retract of the unitary group. -/
instance finiteSpecialUnitaryLocallyPathConnectedSpace :
    LocallyPathConnectedSpace (Matrix.specialUnitaryGroup ι ℂ) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    infer_instance
  | inr h =>
    letI := h
    let i0 : ι := Classical.choice h
    letI : CStarAlgebra (Matrix ι ι ℂ) := CStarAlgebra.mk
    have hq := Topology.IsQuotientMap.of_inverse
      (finiteSpecialUnitaryInclusionHom (ι := ι)).continuous
      (continuous_specialUnitaryNormalize i0)
      (specialUnitaryNormalize_toUnitary i0)
    exact hq.locallyPathConnectedSpace

/-- Endpoint-fixed homotopy of special-unitary paths has no residual obstruction. -/
theorem finiteSpecialUnitary_paths_homotopic
    {S T : Matrix.specialUnitaryGroup ι ℂ} (p q : Path S T) : p.Homotopic q :=
  SimplyConnectedSpace.paths_homotopic p q

/-- A global homotopy between arbitrary special-unitary paths. -/
def finiteSpecialUnitaryPathHomotopy
    {S T : Matrix.specialUnitaryGroup ι ℂ} (p q : Path S T) : p.Homotopy q :=
  (finiteSpecialUnitary_paths_homotopic p q).some

end

end GaloisForLFunctions.HTGeometry
