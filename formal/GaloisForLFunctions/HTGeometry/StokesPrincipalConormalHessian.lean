import GaloisForLFunctions.HTGeometry.StokesGlobalPuiseuxWittLaw

open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

noncomputable section

variable {r s A B : ℕ}

/-- Algebraic half-Hessian of the positive local Stokes form: identity plus the weighted sum of
rank-one principal-conormal tensors. -/
theorem localPositiveForm_associated_apply
    (d : PuiseuxOrbitCoareaDatum r s A B) (x y : Fin r → ℝ) :
    (localPositiveForm d).associated x y =
      (∑ i, x i * y i) +
        ∑ edge, d.toOrbitCoareaDatum.cuts.length edge *
          (localCutLinear d edge x * localCutLinear d edge y) := by
  simp only [localPositiveForm, map_add, LinearMap.add_apply,
    QuadraticMap.associated_comp, QuadraticMap.associated_sq,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply_apply, coordinateLinear_apply,
    map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul]

/-- The sole subtractive half-Hessian of the local Witt form is the physical-rank conormal
tensor. -/
theorem localWittForm_associated_apply
    (d : PuiseuxOrbitCoareaDatum r s A B) (x y : Fin r → ℝ) :
    (localWittForm d).associated x y =
      (∑ i, x i * y i) +
        ∑ edge, d.toOrbitCoareaDatum.cuts.length edge *
          (localCutLinear d edge x * localCutLinear d edge y) -
        (d.toOrbitCoareaDatum.cuts.root - 1) *
          (localRankLinear d x * localRankLinear d y) := by
  simp only [localWittForm, map_sub, LinearMap.sub_apply,
    localPositiveForm_associated_apply, map_smul, LinearMap.smul_apply,
    QuadraticMap.associated_comp, QuadraticMap.associated_sq,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply_apply,
    smul_eq_mul]

end

end GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt
