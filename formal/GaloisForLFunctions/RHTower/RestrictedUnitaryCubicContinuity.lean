import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicOperator
import GaloisForLFunctions.RHTower.RestrictedProjectionCubicContinuity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity

/-!
# Restricted-unitary cubic continuity

Operator-norm continuity of a unitary path together with Hilbert--Schmidt continuity of its
polarization commutator implies Hilbert--Schmidt continuity of the conjugated-projection
displacement.  The cubic defect therefore varies continuously in trace norm.  This is exactly
the analytic homotopy clause RUCRI-A(6), with no uniform-bound assumption added: unitarity gives
the needed operator-norm bound.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Commutator of a reference polarization with a unitary. -/
def restrictedUnitaryCommutator (P U : H →L[ℂ] H) : H →L[ℂ] H :=
  P * U - U * P

/-- Unitary conjugate of a reference polarization. -/
def restrictedUnitaryConjugateProjection (P U : H →L[ℂ] H) : H →L[ℂ] H :=
  ContinuousLinearMap.adjoint U * P * U

/-- The conjugated displacement is the adjoint-unitary image of the commutator. -/
theorem restrictedUnitaryDisplacement_eq_adjoint_mul_commutator
    (P U : H →L[ℂ] H)
    (hU : ContinuousLinearMap.adjoint U * U = 1) :
    restrictedProjectionDisplacement (restrictedUnitaryConjugateProjection P U) P =
      ContinuousLinearMap.adjoint U * restrictedUnitaryCommutator P U := by
  rw [restrictedProjectionDisplacement, restrictedUnitaryConjugateProjection,
    restrictedUnitaryCommutator]
  simp only [mul_sub, ← mul_assoc, hU, one_mul]

/-- A Hilbert--Schmidt restricted commutator gives a Hilbert--Schmidt projection displacement. -/
theorem restrictedUnitaryDisplacement_isHilbertSchmidt
    (P U : H →L[ℂ] H)
    (hU : ContinuousLinearMap.adjoint U * U = 1)
    (hcomm : (restrictedUnitaryCommutator P U).IsHilbertSchmidt) :
    (restrictedProjectionDisplacement
      (restrictedUnitaryConjugateProjection P U) P).IsHilbertSchmidt := by
  rw [restrictedUnitaryDisplacement_eq_adjoint_mul_commutator P U hU]
  exact hcomm.comp_left (ContinuousLinearMap.adjoint U)

/-- Unitary conjugation preserves idempotence of the reference polarization. -/
theorem restrictedUnitaryConjugateProjection_idempotent
    (P U : H →L[ℂ] H) (hP : IsIdempotentElem P)
    (hU : U * ContinuousLinearMap.adjoint U = 1) :
    IsIdempotentElem (restrictedUnitaryConjugateProjection P U) := by
  rw [isIdempotentElem_iff]
  have hPP : P * P = P := hP
  have hcollapse : U * (ContinuousLinearMap.adjoint U * (P * U)) = P * U := by
    rw [← mul_assoc, hU, one_mul]
  have hPPU : P * (P * U) = P * U := by
    rw [← mul_assoc, hPP]
  rw [restrictedUnitaryConjugateProjection]
  simp only [mul_assoc]
  rw [hcollapse, hPPU]

/-- Unitary conjugation preserves self-adjointness of the reference polarization. -/
theorem restrictedUnitaryConjugateProjection_adjoint
    (P U : H →L[ℂ] H)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (restrictedUnitaryConjugateProjection P U) =
      restrictedUnitaryConjugateProjection P U := by
  rw [restrictedUnitaryConjugateProjection]
  change ContinuousLinearMap.adjoint
      ((ContinuousLinearMap.adjoint U ∘L P) ∘L U) =
    (ContinuousLinearMap.adjoint U ∘L P) ∘L U
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hP]
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

/-- An isometric bounded operator has operator norm at most one. -/
theorem norm_unitary_le_one
    (U : H →L[ℂ] H)
    (hU : ContinuousLinearMap.adjoint U * U = 1) : ‖U‖ ≤ 1 := by
  apply U.opNorm_le_bound zero_le_one
  intro x
  have hinner : inner ℂ (U x) (U x) = inner ℂ x x := by
    calc
      inner ℂ (U x) (U x) =
          inner ℂ x (ContinuousLinearMap.adjoint U (U x)) :=
        (ContinuousLinearMap.adjoint_inner_right U x (U x)).symm
      _ = inner ℂ x ((ContinuousLinearMap.adjoint U * U) x) := rfl
      _ = inner ℂ x x := by rw [hU]; simp
  have hre := congrArg Complex.re hinner
  simp only [inner_self_eq_norm_sq_to_K] at hre
  have hsquare : ‖U x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast hre
  nlinarith [norm_nonneg (U x), norm_nonneg x]

/-- Quantitative mixed-topology bound for two restricted-unitary displacements. -/
theorem hsNorm_restrictedUnitaryDisplacement_sub_le
    (P U V : H →L[ℂ] H)
    (hU : ContinuousLinearMap.adjoint U * U = 1)
    (hV : ContinuousLinearMap.adjoint V * V = 1)
    (hcommU : (restrictedUnitaryCommutator P U).IsHilbertSchmidt)
    (hcommV : (restrictedUnitaryCommutator P V).IsHilbertSchmidt) :
    (restrictedProjectionDisplacement (restrictedUnitaryConjugateProjection P U) P -
        restrictedProjectionDisplacement (restrictedUnitaryConjugateProjection P V) P).hsNorm ≤
      ‖U - V‖ * (restrictedUnitaryCommutator P V).hsNorm +
        (restrictedUnitaryCommutator P U - restrictedUnitaryCommutator P V).hsNorm := by
  let CU := restrictedUnitaryCommutator P U
  let CV := restrictedUnitaryCommutator P V
  let X := (ContinuousLinearMap.adjoint U - ContinuousLinearMap.adjoint V) * CV
  let Y := ContinuousLinearMap.adjoint U * (CU - CV)
  have hdiff : (CU - CV).IsHilbertSchmidt := hcommU.sub hcommV
  have hX : X.IsHilbertSchmidt := hcommV.comp_left _
  have hY : Y.IsHilbertSchmidt := hdiff.comp_left _
  have hXbound : X.hsNorm ≤
      ‖ContinuousLinearMap.adjoint U - ContinuousLinearMap.adjoint V‖ * CV.hsNorm := by
    simpa [X, ContinuousLinearMap.mul_def] using
      (hcommV.hsNorm_comp_left_le
        (ContinuousLinearMap.adjoint U - ContinuousLinearMap.adjoint V))
  have hYbound : Y.hsNorm ≤
      ‖ContinuousLinearMap.adjoint U‖ * (CU - CV).hsNorm := by
    simpa [Y, ContinuousLinearMap.mul_def] using
      (hdiff.hsNorm_comp_left_le (ContinuousLinearMap.adjoint U))
  have hdecomp :
      restrictedProjectionDisplacement (restrictedUnitaryConjugateProjection P U) P -
          restrictedProjectionDisplacement (restrictedUnitaryConjugateProjection P V) P = X + Y := by
    rw [restrictedUnitaryDisplacement_eq_adjoint_mul_commutator P U hU,
      restrictedUnitaryDisplacement_eq_adjoint_mul_commutator P V hV]
    dsimp [X, Y, CU, CV]
    noncomm_ring
  rw [hdecomp]
  calc
    (X + Y).hsNorm ≤ X.hsNorm + Y.hsNorm := hsNorm_add_le hX hY
    _ ≤ ‖ContinuousLinearMap.adjoint U - ContinuousLinearMap.adjoint V‖ * CV.hsNorm +
        ‖ContinuousLinearMap.adjoint U‖ * (CU - CV).hsNorm :=
      add_le_add hXbound hYbound
    _ = ‖U - V‖ * CV.hsNorm + ‖U‖ * (CU - CV).hsNorm := by
      rw [← ContinuousLinearMap.adjoint.map_sub]
      rw [show ‖ContinuousLinearMap.adjoint (U - V)‖ = ‖U - V‖ by
        exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (U - V)]
      rw [show ‖ContinuousLinearMap.adjoint U‖ = ‖U‖ by
        exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint U]
    _ ≤ ‖U - V‖ * CV.hsNorm + (CU - CV).hsNorm := by
      gcongr
      exact mul_le_of_le_one_left
        (ContinuousLinearMap.hsNorm_nonneg (CU - CV))
        (norm_unitary_le_one U hU)

/-- RUCRI-A(6): operator-norm convergence of the unitary and Hilbert--Schmidt convergence of its
commutator imply trace-norm convergence of the cubic restricted-projection defect. -/
theorem traceNorm_restrictedUnitaryCubicDefect_tendsto
    {I : Type*} {l : Filter I}
    {P : H →L[ℂ] H} {U : I → H →L[ℂ] H} {U₀ : H →L[ℂ] H}
    (hPidem : IsIdempotentElem P)
    (hPadj : ContinuousLinearMap.adjoint P = P)
    (hUadj : ∀ i, ContinuousLinearMap.adjoint (U i) * U i = 1)
    (hUunit : ∀ i, U i * ContinuousLinearMap.adjoint (U i) = 1)
    (hU₀adj : ContinuousLinearMap.adjoint U₀ * U₀ = 1)
    (hU₀unit : U₀ * ContinuousLinearMap.adjoint U₀ = 1)
    (hcomm : ∀ i, (restrictedUnitaryCommutator P (U i)).IsHilbertSchmidt)
    (hcomm₀ : (restrictedUnitaryCommutator P U₀).IsHilbertSchmidt)
    (htU : Tendsto (fun i => ‖U i - U₀‖) l (nhds 0))
    (htcomm : Tendsto (fun i =>
      (restrictedUnitaryCommutator P (U i) -
        restrictedUnitaryCommutator P U₀).hsNorm) l (nhds 0)) :
    Tendsto (fun i => traceNorm H
      (restrictedProjectionCubicDefect
          (restrictedUnitaryConjugateProjection P (U i)) P -
        restrictedProjectionCubicDefect
          (restrictedUnitaryConjugateProjection P U₀) P)) l (nhds 0) := by
  have htdelta : Tendsto (fun i =>
      (restrictedProjectionDisplacement
          (restrictedUnitaryConjugateProjection P (U i)) P -
        restrictedProjectionDisplacement
          (restrictedUnitaryConjugateProjection P U₀) P).hsNorm) l (nhds 0) := by
    have hupper : Tendsto (fun i =>
        ‖U i - U₀‖ * (restrictedUnitaryCommutator P U₀).hsNorm +
          (restrictedUnitaryCommutator P (U i) -
            restrictedUnitaryCommutator P U₀).hsNorm) l (nhds 0) := by
      simpa using (htU.mul_const _).add htcomm
    refine squeeze_zero' (Eventually.of_forall fun i =>
      ContinuousLinearMap.hsNorm_nonneg _) ?_ hupper
    exact Eventually.of_forall fun i =>
      hsNorm_restrictedUnitaryDisplacement_sub_le P (U i) U₀
        (hUadj i) hU₀adj (hcomm i) hcomm₀
  exact traceNorm_restrictedProjectionCubicDefect_tendsto
    (fun i => restrictedUnitaryConjugateProjection_idempotent
      P (U i) hPidem (hUunit i))
    (fun _ => hPidem)
    (restrictedUnitaryConjugateProjection_idempotent
      P U₀ hPidem hU₀unit)
    hPidem
    (fun i => restrictedUnitaryConjugateProjection_adjoint P (U i) hPadj)
    (fun _ => hPadj)
    (restrictedUnitaryConjugateProjection_adjoint P U₀ hPadj)
    hPadj
    (fun i => restrictedUnitaryDisplacement_isHilbertSchmidt
      P (U i) (hUadj i) (hcomm i))
    (restrictedUnitaryDisplacement_isHilbertSchmidt P U₀ hU₀adj hcomm₀)
    htdelta

end RHTower
