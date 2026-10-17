import GaloisForLFunctions.RHTower.CompletedDirichletArithmeticSource
import GaloisForLFunctions.RHTower.CompletedDirichletGammaCarrier

/-!
# Literal completed Dirichlet germs and their relative logarithmic coordinates

Every translated completion has one shifted archimedean coordinate and an explicit correction
in the field of all convergent Dirichlet series. The carrier is identified with Mathlib's actual
completed L-function on a sufficiently far right half-plane.
-/

open Filter Set
open scoped Differential Classical

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance completedDirichletUpperDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance completedDirichletUpperDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential
local instance completedDirichletUpperComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra
local instance completedDirichletUpperInteger : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

variable {q : ℕ}

def dirichletArchParity (chi : DirichletCharacter ℂ q) : ℕ := if chi.Even then 0 else 1

theorem dirichletArchParity_zero_or_one (chi : DirichletCharacter ℂ q) :
    dirichletArchParity chi = 0 ∨ dirichletArchParity chi = 1 := by
  unfold dirichletArchParity
  split <;> simp

theorem gammaFactor_eq_dirichletArchParity (chi : DirichletCharacter ℂ q) (s : ℂ) :
    chi.gammaFactor s = Complex.Gammaℝ (s + (dirichletArchParity chi : ℂ)) := by
  by_cases h : chi.Even <;> simp [DirichletCharacter.gammaFactor, dirichletArchParity, h]

/-- The pole-orbit label of a translated doubled completion. -/
def dirichletCompletionShift (chi : DirichletCharacter ℂ q) (b : ℂ) : ℂ :=
  (b + (dirichletArchParity chi : ℂ)) / 2

def completedDirichletUpperAnalytic (chi : DirichletCharacter ℂ q) (b : ℂ) :
    upperEndAnalyticSubring :=
  shiftedRotGammaRealAnalytic (dirichletCompletionShift chi b) * translatedDoubleDirichletAnalytic chi b

/-- This is the actual completed function, with no source-admission premise. -/
theorem completedDirichletUpperAnalytic_coe [NeZero q] (chi : DirichletCharacter ℂ q) (b : ℂ) :
    (completedDirichletUpperAnalytic chi b : Germ upperEndFilter ℂ) =
      Germ.coeRingHom upperEndFilter
        (fun z => DirichletCharacter.completedLFunction chi (2 * (-Complex.I * z) + b)) := by
  change (shiftedRotGammaRealAnalytic (dirichletCompletionShift chi b) : Germ upperEndFilter ℂ) *
    (translatedDoubleDirichletAnalytic chi b : Germ upperEndFilter ℂ) = _
  rw [shiftedRotGammaRealAnalytic_coe, translatedDoubleDirichletAnalytic_coe, ← map_mul]
  apply Germ.coe_eq.mpr
  change ∀ᶠ z in upperEndFilter,
    Complex.Gammaℝ (2 * (-Complex.I * z + dirichletCompletionShift chi b)) *
      DirichletCharacter.LFunction chi (2 * (-Complex.I * z) + b) =
        DirichletCharacter.completedLFunction chi (2 * (-Complex.I * z) + b)
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨1 + |b.re|, trivial, fun z hz => ?_⟩
  have hs : 1 < (2 * (-Complex.I * z) + b).re := by
    have hz' : 1 + |b.re| < z.im := hz
    have hb := neg_abs_le b.re
    have hre : (2 * (-Complex.I * z) + b).re = 2 * z.im + b.re := by
      norm_num [Complex.mul_re]
    rw [hre]
    linarith [abs_nonneg b.re]
  have hs0 : 2 * (-Complex.I * z) + b ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hg : Complex.Gammaℝ (2 * (-Complex.I * z) + b + (dirichletArchParity chi : ℂ)) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.natCast_re]
    simp only [Complex.add_re] at hs
    have ha : (0 : ℝ) ≤ (dirichletArchParity chi : ℝ) := Nat.cast_nonneg _
    linarith
  change Complex.Gammaℝ (2 * (-Complex.I * z + dirichletCompletionShift chi b)) *
    DirichletCharacter.LFunction chi (2 * (-Complex.I * z) + b) = _
  rw [show 2 * (-Complex.I * z + dirichletCompletionShift chi b) =
    2 * (-Complex.I * z) + b + (dirichletArchParity chi : ℂ) by
      rw [dirichletCompletionShift]; ring]
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi _ (Or.inl hs0),
    gammaFactor_eq_dirichletArchParity]
  rw [mul_comm, div_mul_cancel₀ _ hg]

/-- The actual translated completion in the upper-end meromorphic field. -/
def completedDirichletUpperMero (chi : DirichletCharacter ℂ q) (b : ℂ) : upperEndMeroField :=
  shiftedRotGammaRealMero (dirichletCompletionShift chi b) * translatedDoubleDirichletMero chi b

theorem completedDirichletUpperMero_eq_algebraMap (chi : DirichletCharacter ℂ q) (b : ℂ) :
    completedDirichletUpperMero chi b =
      algebraMap upperEndAnalyticSubring upperEndMeroField (completedDirichletUpperAnalytic chi b) := by
  rw [completedDirichletUpperMero, completedDirichletUpperAnalytic, map_mul,
    shiftedRotGammaRealMero_eq_algebraMap]
  rfl

theorem completedDirichletUpperMero_ne_zero (chi : DirichletCharacter ℂ q) (b : ℂ) :
    completedDirichletUpperMero chi b ≠ 0 :=
  mul_ne_zero (shiftedRotGammaRealMero_ne_zero _) (translatedDoubleDirichletMero_ne_zero chi b)

theorem completedDirichletUpperMero_logDeriv (chi : DirichletCharacter ℂ q) (b : ℂ) :
    (completedDirichletUpperMero chi b)′ / completedDirichletUpperMero chi b =
      algebraMap ℂ upperEndMeroField (-Complex.I) *
        shiftedRotDigammaMero (dirichletCompletionShift chi b) +
      algebraMap ℂ upperEndMeroField (Complex.I * (Real.log Real.pi : ℂ)) +
      (translatedDoubleDirichletMero chi b)′ / translatedDoubleDirichletMero chi b := by
  rw [completedDirichletUpperMero,
    Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    deriv_shiftedRotGammaRealMero]
  field_simp [shiftedRotGammaRealMero_ne_zero, translatedDoubleDirichletMero_ne_zero]
  ring

/-- The explicitly arithmetic part of the logarithmic coordinate. -/
def completedDirichletLogCorrection (chi : DirichletCharacter ℂ q) (b : ℂ) : dirZetaBase :=
  ⟨algebraMap ℂ upperEndMeroField (Complex.I * (Real.log Real.pi : ℂ)) +
      (translatedDoubleDirichletMero chi b)′ / translatedDoubleDirichletMero chi b,
    add_mem (dirZetaBase.algebraMap_mem _) (translatedDoubleDirichletMero_logDeriv_mem chi b)⟩

theorem completedDirichletUpperMero_logDeriv_affine (chi : DirichletCharacter ℂ q) (b : ℂ) :
    (completedDirichletUpperMero chi b)′ / completedDirichletUpperMero chi b =
      algebraMap ℂ upperEndMeroField (-Complex.I) *
        shiftedRotDigammaMero (dirichletCompletionShift chi b) +
      algebraMap dirZetaBase upperEndMeroField (completedDirichletLogCorrection chi b) := by
  rw [completedDirichletUpperMero_logDeriv]
  exact add_assoc _ _ _

end

end RHTower
