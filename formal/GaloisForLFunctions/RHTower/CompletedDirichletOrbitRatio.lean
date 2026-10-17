import GaloisForLFunctions.RHTower.CompletedDirichletUpperEnd

/-!
# The surviving arithmetic quotient on a completed Dirichlet pole orbit

Integer shifts of the doubled Gamma factor differ by a nonzero rational multiplier. Thus
completed functions on one archimedean pole orbit have their actual quotient in the Dirichlet
coefficient field, not merely a differential-algebraicity relation.
-/

open Filter Set

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance completedDirichletRatioDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance completedDirichletRatioComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

theorem rotGammaRealAnalytic_shift :
    upperEndTranslationAnalyticEquiv Complex.I rotGammaRealAnalytic =
      (dirCoordAnalytic * upperEndPolyToAnalytic (Polynomial.C ((Real.pi : ℂ)⁻¹))) *
        rotGammaRealAnalytic := by
  apply Subtype.ext
  change upperEndTranslateGerm Complex.I (Germ.coeRingHom upperEndFilter rotGammaRealFun) =
    ((Germ.coeRingHom upperEndFilter dirCoordFun) *
      ((upperEndPolyToAnalytic (Polynomial.C ((Real.pi : ℂ)⁻¹)) : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ)) * (Germ.coeRingHom upperEndFilter rotGammaRealFun)
  have hc : ((upperEndPolyToAnalytic (Polynomial.C ((Real.pi : ℂ)⁻¹)) :
      upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
      Germ.coeRingHom upperEndFilter (fun _ : ℂ => (Real.pi : ℂ)⁻¹) := by
    exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => by simp)
  rw [upperEndTranslateGerm_coe, hc, ← map_mul, ← map_mul]
  apply Germ.coe_eq.mpr
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨0, trivial, fun z hz => ?_⟩
  have hs0 : 2 * (-Complex.I * z) ≠ 0 := by
    intro h
    have hp := doubled_rot_re_pos hz
    rw [h] at hp
    norm_num at hp
  have harg : 2 * (-Complex.I * (z + Complex.I)) = 2 * (-Complex.I * z) + 2 := by
    simp [mul_add, mul_assoc]
    <;> ring
  change Complex.Gammaℝ (2 * (-Complex.I * (z + Complex.I))) =
    ((-Complex.I * z) * (Real.pi : ℂ)⁻¹) * Complex.Gammaℝ (2 * (-Complex.I * z))
  rw [harg, Complex.Gammaℝ_add_two hs0]
  ring

theorem rotGammaRealMero_shift :
    upperEndTranslationMeroEquiv Complex.I rotGammaRealMero =
      (dirCoordMero / algebraMap ℂ upperEndMeroField (Real.pi : ℂ)) * rotGammaRealMero := by
  rw [rotGammaRealMero, upperEndTranslationMeroEquiv_algebraMap, rotGammaRealAnalytic_shift,
    map_mul, map_mul]
  change (dirCoordMero * algebraMap ℂ upperEndMeroField ((Real.pi : ℂ)⁻¹)) * _ = _
  rw [map_inv₀, div_eq_mul_inv]

theorem shiftedRotGammaReal_add_one (lam : ℂ) :
    shiftedRotGammaRealMero (lam + 1) =
      ((dirCoordMero + algebraMap ℂ upperEndMeroField lam) /
        algebraMap ℂ upperEndMeroField (Real.pi : ℂ)) * shiftedRotGammaRealMero lam := by
  have hshift : shiftedRotGammaRealMero (lam + 1) =
      upperEndTranslationMeroEquiv (Complex.I * lam)
        (upperEndTranslationMeroEquiv Complex.I rotGammaRealMero) := by
    rw [shiftedRotGammaRealMero, upperEndTranslationMeroEquiv_add,
      show Complex.I * (lam + 1) = Complex.I * lam + Complex.I by ring]
  rw [hshift, rotGammaRealMero_shift, map_mul, map_div₀,
    upperEndTranslate_dirCoordMero_gen, upperEndTranslate_algebraMap_complex_gen]
  rfl

theorem shiftedRotGammaReal_add_one_div_mem (lam : ℂ) :
    shiftedRotGammaRealMero (lam + 1) / shiftedRotGammaRealMero lam ∈ dirZetaBase := by
  have heq : shiftedRotGammaRealMero (lam + 1) / shiftedRotGammaRealMero lam =
      (dirCoordMero + algebraMap ℂ upperEndMeroField lam) /
        algebraMap ℂ upperEndMeroField (Real.pi : ℂ) := by
    rw [shiftedRotGammaReal_add_one]
    field_simp [shiftedRotGammaRealMero_ne_zero]
  rw [heq]
  exact div_mem (add_mem dirCoordMero_mem_dirZetaBase (dirZetaBase.algebraMap_mem _))
    (dirZetaBase.algebraMap_mem _)

theorem shiftedRotGammaReal_add_nat_div_mem (lam : ℂ) (n : ℕ) :
    shiftedRotGammaRealMero (lam + (n : ℂ)) / shiftedRotGammaRealMero lam ∈ dirZetaBase := by
  induction n with
  | zero =>
      rw [Nat.cast_zero, add_zero, div_self (shiftedRotGammaRealMero_ne_zero lam)]
      exact one_mem _
  | succ n ih =>
      rw [show lam + ((n + 1 : ℕ) : ℂ) = (lam + (n : ℂ)) + 1 by push_cast; ring]
      have heq : shiftedRotGammaRealMero ((lam + (n : ℂ)) + 1) / shiftedRotGammaRealMero lam =
          (shiftedRotGammaRealMero ((lam + (n : ℂ)) + 1) /
            shiftedRotGammaRealMero (lam + (n : ℂ))) *
          (shiftedRotGammaRealMero (lam + (n : ℂ)) / shiftedRotGammaRealMero lam) := by
        field_simp [shiftedRotGammaRealMero_ne_zero]
      rw [heq]
      exact mul_mem (shiftedRotGammaReal_add_one_div_mem _) ih

theorem shiftedRotGammaReal_add_int_div_mem (lam : ℂ) (n : ℤ) :
    shiftedRotGammaRealMero (lam + (n : ℂ)) / shiftedRotGammaRealMero lam ∈ dirZetaBase := by
  cases n with
  | ofNat n => exact shiftedRotGammaReal_add_nat_div_mem lam n
  | negSucc n =>
      have h := shiftedRotGammaReal_add_nat_div_mem
        (lam + ((Int.negSucc n : ℤ) : ℂ)) (n + 1)
      have harg : lam + ((Int.negSucc n : ℤ) : ℂ) + ((n + 1 : ℕ) : ℂ) = lam := by
        push_cast
        ring
      rw [harg] at h
      convert inv_mem h using 1
      field_simp [shiftedRotGammaRealMero_ne_zero]

/-- On a shared archimedean pole orbit the quotient of the actual completed functions belongs
to the arithmetic coefficient field. -/
theorem completedDirichletUpperMero_div_mem_of_same_orbit
    {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]
    (chi₁ : DirichletCharacter ℂ q₁) (chi₂ : DirichletCharacter ℂ q₂)
    (b₁ b₂ : ℂ) (n : ℤ)
    (horbit : dirichletCompletionShift chi₁ b₁ - dirichletCompletionShift chi₂ b₂ = (n : ℂ)) :
    completedDirichletUpperMero chi₁ b₁ / completedDirichletUpperMero chi₂ b₂ ∈ dirZetaBase := by
  have hg : shiftedRotGammaRealMero (dirichletCompletionShift chi₁ b₁) /
      shiftedRotGammaRealMero (dirichletCompletionShift chi₂ b₂) ∈ dirZetaBase := by
    rw [show dirichletCompletionShift chi₁ b₁ = dirichletCompletionShift chi₂ b₂ + (n : ℂ) by
      linear_combination horbit]
    exact shiftedRotGammaReal_add_int_div_mem _ n
  have heq : completedDirichletUpperMero chi₁ b₁ / completedDirichletUpperMero chi₂ b₂ =
      (shiftedRotGammaRealMero (dirichletCompletionShift chi₁ b₁) /
        shiftedRotGammaRealMero (dirichletCompletionShift chi₂ b₂)) *
      (translatedDoubleDirichletMero chi₁ b₁ / translatedDoubleDirichletMero chi₂ b₂) := by
    rw [completedDirichletUpperMero, completedDirichletUpperMero]
    field_simp [shiftedRotGammaRealMero_ne_zero, translatedDoubleDirichletMero_ne_zero]
    <;> ring
  rw [heq]
  exact mul_mem hg (div_mem (translatedDoubleDirichletMero_mem chi₁ b₁)
    (translatedDoubleDirichletMero_mem chi₂ b₂))

end

end RHTower
