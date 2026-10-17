import GaloisForLFunctions.RHTower.CompletedDirichletUpperEnd
import GaloisForLFunctions.HTGeometry.DirichletShiftedDigammaOrbit
import GaloisForLFunctions.HTGeometry.BaseGaugeDifferentialIndependence
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# Exact differential independence of actual completed Dirichlet families

After adjoining every convergent Dirichlet series, the only remaining free differential
coordinates are the archimedean pole orbits. The criterion applies to arbitrary characters,
positive moduli and complex translations, with all arithmetic admissions discharged.
-/

open scoped Differential

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance completedDirichletIndependenceDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance completedDirichletIndependenceDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential
local instance completedDirichletIndependenceComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra
local instance completedDirichletIndependenceCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective
local instance completedDirichletIndependenceBaseDifferential : Differential dirZetaBase :=
  dirZetaBaseDifferential
local instance completedDirichletIndependenceDifferentialAlgebra :
    DifferentialAlgebra dirZetaBase upperEndMeroField where
  deriv_algebraMap _ := rfl

/-- Logarithmic derivatives of actual translated completions are independent precisely when
their archimedean pole labels are distinct modulo integers. -/
theorem completedDirichlet_logDeriv_differentialIndependent_iff
    {r : ℕ} (q : Fin r → ℕ) [∀ i, NeZero (q i)]
    (chi : ∀ i, DirichletCharacter ℂ (q i)) (b : Fin r → ℂ) :
    DifferentialIndependent (dirZetaBase : Type _)
        (fun i => (completedDirichletUpperMero (chi i) (b i))′ /
          completedDirichletUpperMero (chi i) (b i)) ↔
      ∀ i j, i ≠ j → ∀ n : ℤ,
        dirichletCompletionShift (chi i) (b i) -
          dirichletCompletionShift (chi j) (b j) ≠ (n : ℂ) := by
  classical
  let x : Fin r → upperEndMeroField :=
    fun i => shiftedRotDigammaMero (dirichletCompletionShift (chi i) (b i))
  let a : Fin r → dirZetaBase := fun _ => algebraMap ℂ dirZetaBase (-Complex.I)
  let c : Fin r → dirZetaBase := fun i => completedDirichletLogCorrection (chi i) (b i)
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have hz : (-Complex.I : ℂ) = 0 := (algebraMap ℂ dirZetaBase).injective
      (h.trans (map_zero (algebraMap ℂ dirZetaBase)).symm)
    exact (neg_ne_zero.mpr Complex.I_ne_zero) hz
  have hfun : (fun i => (completedDirichletUpperMero (chi i) (b i))′ /
      completedDirichletUpperMero (chi i) (b i)) =
      fun i => algebraMap dirZetaBase upperEndMeroField (a i) * x i +
        algebraMap dirZetaBase upperEndMeroField (c i) := by
    funext i
    exact completedDirichletUpperMero_logDeriv_affine (chi i) (b i)
  rw [hfun]
  exact (GaloisForLFunctions.HTGeometry.differentialIndependent_affineBase_iff x a c ha).trans
    (differentialIndependent_shiftedRotDigamma_over_dirZetaBase_iff _)

/-- **Exact relative orbit classification for completed arithmetic functions.** The family of
actual germs `completedLFunction chi_i (2s+b_i)` is differentially independent over all
convergent Dirichlet series exactly when `(b_i+parity(chi_i))/2` have distinct integer orbits. -/
theorem completedDirichlet_differentialIndependent_iff
    {r : ℕ} (q : Fin r → ℕ) [∀ i, NeZero (q i)]
    (chi : ∀ i, DirichletCharacter ℂ (q i)) (b : Fin r → ℂ) :
    DifferentialIndependent (dirZetaBase : Type _)
        (fun i => completedDirichletUpperMero (chi i) (b i)) ↔
      ∀ i j, i ≠ j → ∀ n : ℤ,
        dirichletCompletionShift (chi i) (b i) -
          dirichletCompletionShift (chi j) (b j) ≠ (n : ℂ) := by
  cases r with
  | zero =>
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        exact algebraicIndependent_empty_type_iff.mpr (algebraMap dirZetaBase upperEndMeroField).injective
  | succ n =>
      rw [differentialIndependent_deriv_div_self_fin_succ_iff]
      exact completedDirichlet_logDeriv_differentialIndependent_iff q chi b

/-- The unshifted completed family has exactly the parity channels. -/
theorem completedDirichlet_unshifted_differentialIndependent_iff_parity_injective
    {r : ℕ} (q : Fin r → ℕ) [∀ i, NeZero (q i)]
    (chi : ∀ i, DirichletCharacter ℂ (q i)) :
    DifferentialIndependent (dirZetaBase : Type _)
        (fun i => completedDirichletUpperMero (chi i) 0) ↔
      Function.Injective (fun i => dirichletArchParity (chi i)) := by
  rw [completedDirichlet_differentialIndependent_iff q chi (fun _ => 0)]
  constructor
  · intro h i j hpar
    by_contra hij
    apply h i j hij 0
    simp [dirichletCompletionShift, hpar]
  · intro h i j hij n hrel
    have hpar : dirichletArchParity (chi i) ≠ dirichletArchParity (chi j) :=
      fun heq => hij (h heq)
    rcases dirichletArchParity_zero_or_one (chi i) with hi | hi <;>
      rcases dirichletArchParity_zero_or_one (chi j) with hj | hj
    · exact hpar (hi.trans hj.symm)
    · have hreal := congrArg Complex.re hrel
      norm_num [dirichletCompletionShift, hi, hj] at hreal
      have hlow : (-1 : ℝ) < (n : ℝ) := by linarith
      have hhigh : (n : ℝ) < 0 := by linarith
      have hlow' : (-1 : ℤ) < n := by exact_mod_cast hlow
      have hhigh' : n < 0 := by exact_mod_cast hhigh
      omega
    · have hreal := congrArg Complex.re hrel
      norm_num [dirichletCompletionShift, hi, hj] at hreal
      have hlow : (0 : ℝ) < (n : ℝ) := by linarith
      have hhigh : (n : ℝ) < 1 := by linarith
      have hlow' : (0 : ℤ) < n := by exact_mod_cast hlow
      have hhigh' : n < 1 := by exact_mod_cast hhigh
      omega
    · exact hpar (hi.trans hj.symm)

end

end RHTower
