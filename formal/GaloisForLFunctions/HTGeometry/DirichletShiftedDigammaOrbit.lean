import GaloisForLFunctions.HTGeometry.ShiftedDigammaOverDirichletBase
import GaloisForLFunctions.HTGeometry.DirichletBaseDifferential

/-!
# Exact integer-orbit classification of shifted digammas over Dirichlet coefficients

Integer translates differ by rational germs. Distinct integer pole orbits give free jet
families even over the field of all convergent Dirichlet series, so these are exactly the
collisions that destroy differential independence.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance dirichletDigammaOrbitDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance dirichletDigammaOrbitDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential
local instance dirichletDigammaOrbitComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra
local instance dirichletDigammaOrbitBaseDifferential : Differential dirZetaBase := dirZetaBaseDifferential
local instance dirichletDigammaOrbitBaseDifferentialAlgebra : DifferentialAlgebra dirZetaBase upperEndMeroField where
  deriv_algebraMap _ := rfl

theorem shiftedRotDigamma_add_one (lam : ℂ) :
    shiftedRotDigammaMero (lam + 1) =
      shiftedRotDigammaMero lam + dirDefectAt (-lam) 0 := by
  have hshift : shiftedRotDigammaMero (lam + 1) =
      upperEndTranslationMeroEquiv Complex.I (shiftedRotDigammaMero lam) := by
    simp only [shiftedRotDigammaMero, upperEndTranslationMeroEquiv_add]
    rw [show Complex.I * (lam + 1) = Complex.I + Complex.I * lam by ring]
  rw [hshift]
  exact shiftedRotDigammaJet_shift lam 0

theorem shiftedRotDigamma_add_one_sub_mem (lam : ℂ) :
    shiftedRotDigammaMero (lam + 1) - shiftedRotDigammaMero lam ∈ dirZetaBase := by
  rw [shiftedRotDigamma_add_one, add_sub_cancel_left, dirDefectAt_zero, dirCoordAt]
  exact inv_mem (sub_mem dirCoordMero_mem_dirZetaBase (dirZetaBase.algebraMap_mem _))

theorem shiftedRotDigamma_add_nat_sub_mem (lam : ℂ) (n : ℕ) :
    shiftedRotDigammaMero (lam + (n : ℂ)) - shiftedRotDigammaMero lam ∈ dirZetaBase := by
  induction n with
  | zero => simp only [Nat.cast_zero, add_zero, sub_self]; exact zero_mem _
  | succ n ih =>
      rw [show lam + ((n + 1 : ℕ) : ℂ) = (lam + (n : ℂ)) + 1 by push_cast; ring]
      have heq : shiftedRotDigammaMero ((lam + (n : ℂ)) + 1) - shiftedRotDigammaMero lam =
          (shiftedRotDigammaMero ((lam + (n : ℂ)) + 1) -
            shiftedRotDigammaMero (lam + (n : ℂ))) +
          (shiftedRotDigammaMero (lam + (n : ℂ)) - shiftedRotDigammaMero lam) := by ring
      rw [heq]
      exact add_mem (shiftedRotDigamma_add_one_sub_mem _) ih

/-- The exact surviving relation on an integer shift orbit has coefficients in the arithmetic
coefficient field. -/
theorem shiftedRotDigamma_add_int_sub_mem (lam : ℂ) (n : ℤ) :
    shiftedRotDigammaMero (lam + (n : ℂ)) - shiftedRotDigammaMero lam ∈ dirZetaBase := by
  cases n with
  | ofNat n => exact shiftedRotDigamma_add_nat_sub_mem lam n
  | negSucc n =>
      have h := shiftedRotDigamma_add_nat_sub_mem
        (lam + ((Int.negSucc n : ℤ) : ℂ)) (n + 1)
      have harg : lam + ((Int.negSucc n : ℤ) : ℂ) + ((n + 1 : ℕ) : ℂ) = lam := by
        push_cast
        ring
      rw [harg] at h
      convert neg_mem h using 1
      ring

/-- The complete relative differential-independence criterion is separation modulo integers. -/
theorem differentialIndependent_shiftedRotDigamma_over_dirZetaBase_iff
    {r : ℕ} (lam : Fin r → ℂ) :
    DifferentialIndependent (dirZetaBase : Type _) (fun i => shiftedRotDigammaMero (lam i)) ↔
      ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ) := by
  classical
  constructor
  · intro h i j hij n hrel
    have hm : shiftedRotDigammaMero (lam i) - shiftedRotDigammaMero (lam j) ∈ dirZetaBase := by
      rw [show lam i = lam j + (n : ℂ) by linear_combination hrel]
      exact shiftedRotDigamma_add_int_sub_mem (lam j) n
    let c : Fin r → dirZetaBase := fun k =>
      if k = j then ⟨shiftedRotDigammaMero (lam i) - shiftedRotDigammaMero (lam j), hm⟩ else 0
    have hg := h.addBase c
    apply hij
    apply hg.injective
    simp only [c, if_neg hij, if_pos rfl, map_zero, add_zero]
    change shiftedRotDigammaMero (lam i) = shiftedRotDigammaMero (lam j) +
      (shiftedRotDigammaMero (lam i) - shiftedRotDigammaMero (lam j))
    ring
  · exact differentialIndependent_shiftedRotDigamma_over_dirZetaBase lam

end

end GaloisForLFunctions.HTGeometry
