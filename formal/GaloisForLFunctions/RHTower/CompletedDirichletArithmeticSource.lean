import GaloisForLFunctions.HTGeometry.DirichletBaseDifferential
import GaloisForLFunctions.HTGeometry.PrimePowerAnalyticDilation
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Actual translated Dirichlet L-functions in the arithmetic coefficient field

Arbitrary complex translations and doubling of the argument preserve the finite-abscissa
Dirichlet algebra. The coefficient at one is exactly one, so every realized source is nonzero.
-/

open Filter Set
open scoped Differential

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance completedDirichletArithmeticDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance completedDirichletArithmeticDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential
local instance completedDirichletArithmeticComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

variable {q : ℕ}

/-- The character coefficients with the unused coefficient at zero set to zero. -/
def dirichletCharacterArithmeticSource (chi : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else chi (n : ZMod q), by simp⟩

theorem dirichletCharacterArithmeticSource_apply (chi : DirichletCharacter ℂ q)
    {n : ℕ} (hn : n ≠ 0) :
    dirichletCharacterArithmeticSource chi n = chi (n : ZMod q) := by
  simp [dirichletCharacterArithmeticSource, hn]

def dirichletCharacterFiniteAbscissaSource (chi : DirichletCharacter ℂ q) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨dirichletCharacterArithmeticSource chi, 1, fun y hy => ?_⟩
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
  · intro n hn
    rw [dirichletCharacterArithmeticSource_apply chi hn]
    exact DirichletCharacter.norm_le_one chi _
  · simpa using hy

/-- The source supported on squares for the literal function `L(chi,2s+b)`. -/
def translatedDoubleDirichletSource (chi : DirichletCharacter ℂ q) (b : ℂ) :
    finiteAbscissaArithmeticSubalgebra :=
  finiteAbscissaPrimePowerDilation 1
    (finiteAbscissaDirichletShift b (dirichletCharacterFiniteAbscissaSource chi))

theorem translatedDoubleDirichletSource_one (chi : DirichletCharacter ℂ q) (b : ℂ) :
    (translatedDoubleDirichletSource chi b).1 1 = 1 := by
  change mPart 2 (finiteAbscissaDirichletShift b
    (dirichletCharacterFiniteAbscissaSource chi)).1 (1 ^ 2) = 1
  rw [mPart_apply_pow (by decide : 2 ≠ 0), finiteAbscissaDirichletShift_apply]
  simp [cpowWeight, dirichletCharacterFiniteAbscissaSource,
    dirichletCharacterArithmeticSource]

theorem LSeries_translatedDoubleDirichletSource
    (chi : DirichletCharacter ℂ q) (b s : ℂ) :
    LSeries (fun n => (translatedDoubleDirichletSource chi b).1 n) s =
      LSeries (fun n => chi (n : ZMod q)) (2 * s + b) := by
  change LSeries (fun n => mPart 2
    (finiteAbscissaDirichletShift b (dirichletCharacterFiniteAbscissaSource chi)).1 n) s = _
  rw [LSeries_mPart (by decide : 2 ≠ 0)]
  change LSeries (fun n => dirichletShift b (dirichletCharacterArithmeticSource chi) n)
    (2 * s) = _
  rw [LSeries_dirichletShift]
  exact LSeries_congr (fun hn => dirichletCharacterArithmeticSource_apply chi hn) _

def translatedDoubleDirichletAnalytic (chi : DirichletCharacter ℂ q) (b : ℂ) :
    upperEndAnalyticSubring :=
  finiteAbscissaLSeriesUpperEndAnalyticElement (translatedDoubleDirichletSource chi b)

theorem translatedDoubleDirichletAnalytic_coe [NeZero q] (chi : DirichletCharacter ℂ q) (b : ℂ) :
    (translatedDoubleDirichletAnalytic chi b : Germ upperEndFilter ℂ) =
      Germ.coeRingHom upperEndFilter
        (fun z => DirichletCharacter.LFunction chi (2 * (-Complex.I * z) + b)) := by
  change (Germ.coeRingHom upperEndFilter
    (fun z => LSeries (fun n => (translatedDoubleDirichletSource chi b).1 n)
      (-Complex.I * z))) = _
  apply Germ.coe_eq.mpr
  change ∀ᶠ z in upperEndFilter,
    LSeries (fun n => (translatedDoubleDirichletSource chi b).1 n) (-Complex.I * z) =
      DirichletCharacter.LFunction chi (2 * (-Complex.I * z) + b)
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨1 + |b.re|, trivial, fun z hz => ?_⟩
  rw [LSeries_translatedDoubleDirichletSource]
  symm
  apply DirichletCharacter.LFunction_eq_LSeries
  have hz' : 1 + |b.re| < z.im := hz
  have hb := neg_abs_le b.re
  have hre : (2 * (-Complex.I * z) + b).re = 2 * z.im + b.re := by
    norm_num [Complex.mul_re]
  rw [hre]
  linarith [abs_nonneg b.re]

def translatedDoubleDirichletMero (chi : DirichletCharacter ℂ q) (b : ℂ) : upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero (translatedDoubleDirichletSource chi b)

theorem translatedDoubleDirichletMero_ne_zero (chi : DirichletCharacter ℂ q) (b : ℂ) :
    translatedDoubleDirichletMero chi b ≠ 0 := by
  intro h
  have hs : translatedDoubleDirichletSource chi b = 0 :=
    finiteAbscissaLSeriesToUpperEndMero_injective
      (h.trans (map_zero finiteAbscissaLSeriesToUpperEndMero).symm)
  have h1 := congrArg (fun f : finiteAbscissaArithmeticSubalgebra => f.1 1) hs
  have h10 : (1 : ℂ) = 0 := by
    simpa only [translatedDoubleDirichletSource_one,
      ZeroMemClass.coe_zero, ArithmeticFunction.zero_apply] using h1
  exact one_ne_zero h10

theorem translatedDoubleDirichletMero_mem (chi : DirichletCharacter ℂ q) (b : ℂ) :
    translatedDoubleDirichletMero chi b ∈ dirZetaBase :=
  lseries_mem_dirZetaBase _

theorem translatedDoubleDirichletMero_logDeriv_mem (chi : DirichletCharacter ℂ q) (b : ℂ) :
    (translatedDoubleDirichletMero chi b)′ / translatedDoubleDirichletMero chi b ∈ dirZetaBase :=
  div_mem (derivationClosed_dirZetaBase (translatedDoubleDirichletMero_mem chi b))
    (translatedDoubleDirichletMero_mem chi b)

end

end RHTower
