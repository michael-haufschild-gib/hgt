import GaloisForLFunctions.RHTower.CompletedDirichletOrbitIndependence
import GaloisForLFunctions.RHTower.SymmetricShiftDirichletExample
import GaloisForLFunctions.HTGeometry.ExplicitDigammaHerglotzPalette

/-!
# Explicit completed arithmetic families attaining the relative orbit classification

Every Dirichlet character supplies arbitrarily large independent translated families. The
unshifted even and odd channels are both attained by the completed zeta and conductor-four
quadratic L-functions.
-/

open scoped Differential Classical

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance completedDirichletPaletteDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance completedDirichletPaletteDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential
local instance completedDirichletPaletteComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- A closed-form family of pairwise distinct completed-function pole orbits. -/
def completedDirichletPaletteShift (n : ℕ) : ℂ :=
  2 * (explicitDigammaPalettePoint n : ℂ)

/-- For every actual character and every finite size, these explicit translated completions
are independent over the field containing all convergent Dirichlet series. -/
theorem completedDirichlet_explicitPalette_differentialIndependent
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (r : ℕ) :
    DifferentialIndependent (dirZetaBase : Type _)
      (fun i : Fin r => completedDirichletUpperMero chi (completedDirichletPaletteShift i)) := by
  letI : ∀ _i : Fin r, NeZero q := fun _ => inferInstance
  apply (completedDirichlet_differentialIndependent_iff (fun _ : Fin r => q)
    (fun _ => chi) (fun i => completedDirichletPaletteShift i)).mpr
  intro i j hij n hrel
  have heq : dirichletCompletionShift chi (completedDirichletPaletteShift i) -
      dirichletCompletionShift chi (completedDirichletPaletteShift j) =
      ((explicitDigammaPalettePoint i - explicitDigammaPalettePoint j : ℝ) : ℂ) := by
    simp only [dirichletCompletionShift, completedDirichletPaletteShift, Complex.ofReal_sub]
    ring
  rw [heq] at hrel
  have hreal : explicitDigammaPalettePoint i - explicitDigammaPalettePoint j = (n : ℝ) := by
    exact_mod_cast hrel
  exact explicitDigammaPalettePoint_sub_ne_int
    (fun h => hij (Fin.ext h)) n hreal

def completedDirichletZetaBetaModulus (i : Fin 2) : ℕ := if i = 0 then 1 else 4

instance completedDirichletZetaBetaModulus_neZero (i : Fin 2) :
    NeZero (completedDirichletZetaBetaModulus i) := by
  fin_cases i
  · change NeZero 1
    infer_instance
  · change NeZero 4
    infer_instance

def completedDirichletZetaBetaCharacter (i : Fin 2) :
    DirichletCharacter ℂ (completedDirichletZetaBetaModulus i) :=
  Fin.cases (motive := fun i : Fin 2 =>
    DirichletCharacter ℂ (completedDirichletZetaBetaModulus i))
    (1 : DirichletCharacter ℂ 1)
    (fun j => Fin.cases (motive := fun j : Fin 1 =>
      DirichletCharacter ℂ (completedDirichletZetaBetaModulus j.succ))
      quadraticCharacterFour (fun k => Fin.elim0 k) j) i

theorem completedDirichletZetaBetaCharacter_zero_parity :
    dirichletArchParity (completedDirichletZetaBetaCharacter 0) = 0 := by
  change dirichletArchParity (1 : DirichletCharacter ℂ 1) = 0
  have heven : (1 : DirichletCharacter ℂ 1).Even := by
    change (1 : DirichletCharacter ℂ 1) (-1 : ZMod 1) = 1
    rw [Subsingleton.elim (-1 : ZMod 1) 1, map_one]
  simp [dirichletArchParity, heven]

theorem completedDirichletZetaBetaCharacter_one_parity :
    dirichletArchParity (completedDirichletZetaBetaCharacter 1) = 1 := by
  change dirichletArchParity quadraticCharacterFour = 1
  simp [dirichletArchParity, quadraticCharacterFour_odd.not_even]

/-- Both unshifted parity channels occur in actual completed arithmetic functions. -/
theorem completedDirichlet_zeta_beta_differentialIndependent :
    DifferentialIndependent (dirZetaBase : Type _)
      (fun i : Fin 2 => completedDirichletUpperMero (completedDirichletZetaBetaCharacter i) 0) := by
  letI : ∀ i : Fin 2, NeZero (completedDirichletZetaBetaModulus i) :=
    completedDirichletZetaBetaModulus_neZero
  apply (completedDirichlet_unshifted_differentialIndependent_iff_parity_injective
    completedDirichletZetaBetaModulus completedDirichletZetaBetaCharacter).mpr
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · change dirichletArchParity (completedDirichletZetaBetaCharacter 0) =
      dirichletArchParity (completedDirichletZetaBetaCharacter 1) at hij
    rw [completedDirichletZetaBetaCharacter_zero_parity,
      completedDirichletZetaBetaCharacter_one_parity] at hij
    omega
  · change dirichletArchParity (completedDirichletZetaBetaCharacter 1) =
      dirichletArchParity (completedDirichletZetaBetaCharacter 0) at hij
    rw [completedDirichletZetaBetaCharacter_one_parity,
      completedDirichletZetaBetaCharacter_zero_parity] at hij
    omega
  · rfl

end

end RHTower
