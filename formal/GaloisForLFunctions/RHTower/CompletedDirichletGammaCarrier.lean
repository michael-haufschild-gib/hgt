import GaloisForLFunctions.HTGeometry.DirichletShiftedDigammaCarrier
import GaloisForLFunctions.RHTower.ArchEnvelope

/-!
# The literal doubled real Gamma factor at the upper end

The Gamma factor is `GammaR(2s)` with `s=-I*z`, including its pi normalization.
Its translated logarithmic derivative is the corresponding shifted digamma plus a constant.
-/

open Filter Set
open scoped Differential

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

local instance completedDirichletGammaDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring
local instance completedDirichletGammaDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential
local instance completedDirichletGammaComplex : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

def rotGammaRealFun (z : ℂ) : ℂ := Complex.Gammaℝ (2 * (-Complex.I * z))

theorem doubled_rot_re_pos {z : ℂ} (hz : z ∈ upperTail 0) :
    0 < (2 * (-Complex.I * z)).re := by
  have hz' : 0 < z.im := hz
  have hre : (2 * (-Complex.I * z)).re = 2 * z.im := by
    norm_num [Complex.mul_re]
  rw [hre]
  linarith

theorem analyticOnNhd_rotGammaRealFun : AnalyticOnNhd ℂ rotGammaRealFun (upperTail 0) := by
  intro z hz
  have hlin : AnalyticAt ℂ (fun w : ℂ => 2 * (-Complex.I * w)) z :=
    analyticAt_const.mul (analyticAt_const.mul analyticAt_id)
  exact AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun w : ℂ => 2 * (-Complex.I * w))
    (Gammaℝ_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos (doubled_rot_re_pos hz))) hlin

def rotGammaRealAnalytic : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter rotGammaRealFun,
    rotGammaRealFun, 0, analyticOnNhd_rotGammaRealFun, rfl⟩

def rotGammaRealInvAnalytic : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (fun z => (rotGammaRealFun z)⁻¹),
    (fun z => (rotGammaRealFun z)⁻¹), 0,
    analyticOnNhd_rotGammaRealFun.inv
      (fun _ hz => Complex.Gammaℝ_ne_zero_of_re_pos (doubled_rot_re_pos hz)), rfl⟩

def rotGammaRealMero : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField rotGammaRealAnalytic

theorem rotGammaRealAnalytic_mul_inv : rotGammaRealAnalytic * rotGammaRealInvAnalytic = 1 := by
  apply Subtype.ext
  change (Germ.coeRingHom upperEndFilter rotGammaRealFun) *
    (Germ.coeRingHom upperEndFilter (fun z => (rotGammaRealFun z)⁻¹)) = 1
  rw [← map_mul]
  apply Germ.coe_eq.mpr
  change ∀ᶠ z in upperEndFilter, rotGammaRealFun z * (rotGammaRealFun z)⁻¹ = 1
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨0, trivial, fun z hz => ?_⟩
  exact mul_inv_cancel₀ (Complex.Gammaℝ_ne_zero_of_re_pos (doubled_rot_re_pos hz))

theorem rotGammaRealMero_ne_zero : rotGammaRealMero ≠ 0 := by
  intro h
  have hm : rotGammaRealMero *
      algebraMap upperEndAnalyticSubring upperEndMeroField rotGammaRealInvAnalytic = 1 := by
    rw [rotGammaRealMero, ← map_mul, rotGammaRealAnalytic_mul_inv, map_one]
  rw [h, zero_mul] at hm
  exact zero_ne_one hm

theorem deriv_rotGammaRealFun {z : ℂ} (hz : z ∈ upperTail 0) :
    deriv rotGammaRealFun z =
      (-Complex.I * rotDigammaFun z + Complex.I * (Real.log Real.pi : ℂ)) * rotGammaRealFun z := by
  have hinner : HasDerivAt (fun w : ℂ => 2 * (-Complex.I * w)) (2 * (-Complex.I)) z := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id z).const_mul (-Complex.I)).const_mul 2
  have h := (hasDerivAt_Gammaℝ_of_re_pos (doubled_rot_re_pos hz)).comp z hinner
  have hd : deriv rotGammaRealFun z =
      (Complex.Gammaℝ (2 * (-Complex.I * z)) *
        (Complex.digamma ((2 * (-Complex.I * z)) / 2) / 2 - (Real.log Real.pi : ℂ) / 2)) *
          (2 * (-Complex.I)) := h.deriv
  rw [hd, show (2 * (-Complex.I * z)) / 2 = -Complex.I * z by ring]
  simp only [rotDigammaFun, Complex.digamma_def, logDeriv_apply, rotGammaRealFun]
  ring

theorem upperEndAnalyticDeriv_rotGammaRealAnalytic :
    upperEndAnalyticDeriv rotGammaRealAnalytic =
      (upperEndPolyToAnalytic (Polynomial.C (-Complex.I)) * rotDigammaAnalytic +
        upperEndPolyToAnalytic (Polynomial.C (Complex.I * (Real.log Real.pi : ℂ)))) *
          rotGammaRealAnalytic := by
  apply Subtype.ext
  rw [upperEndAnalyticDeriv_coe]
  have hc (c : ℂ) :
      ((upperEndPolyToAnalytic (Polynomial.C c) : upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
        Germ.coeRingHom upperEndFilter (fun _ : ℂ => c) := by
    exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => by simp)
  change upperEndGermDeriv (Germ.coeRingHom upperEndFilter rotGammaRealFun) =
    (((upperEndPolyToAnalytic (Polynomial.C (-Complex.I)) : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) * (Germ.coeRingHom upperEndFilter rotDigammaFun) +
      ((upperEndPolyToAnalytic (Polynomial.C (Complex.I * (Real.log Real.pi : ℂ))) :
        upperEndAnalyticSubring) : Germ upperEndFilter ℂ)) *
          (Germ.coeRingHom upperEndFilter rotGammaRealFun)
  rw [hc, hc, ← map_mul, ← map_add, ← map_mul]
  apply Germ.coe_eq.mpr
  change ∀ᶠ z in upperEndFilter, deriv rotGammaRealFun z =
    (-Complex.I * rotDigammaFun z + Complex.I * (Real.log Real.pi : ℂ)) * rotGammaRealFun z
  rw [upperEndFilter_basis.eventually_iff]
  exact ⟨0, trivial, fun _ hz => deriv_rotGammaRealFun hz⟩

theorem deriv_rotGammaRealMero :
    (rotGammaRealMero)′ =
      (algebraMap ℂ upperEndMeroField (-Complex.I) * rotDigammaMero +
        algebraMap ℂ upperEndMeroField (Complex.I * (Real.log Real.pi : ℂ))) * rotGammaRealMero := by
  rw [rotGammaRealMero, upperEndMeroFieldDifferential_algebraMap,
    upperEndAnalyticDeriv_rotGammaRealAnalytic, map_mul, map_add, map_mul]
  rfl

def shiftedRotGammaRealAnalytic (lam : ℂ) : upperEndAnalyticSubring :=
  upperEndTranslationAnalyticEquiv (Complex.I * lam) rotGammaRealAnalytic

def shiftedRotGammaRealMero (lam : ℂ) : upperEndMeroField :=
  upperEndTranslationMeroEquiv (Complex.I * lam) rotGammaRealMero

theorem shiftedRotGammaRealMero_eq_algebraMap (lam : ℂ) :
    shiftedRotGammaRealMero lam =
      algebraMap upperEndAnalyticSubring upperEndMeroField (shiftedRotGammaRealAnalytic lam) := by
  rw [shiftedRotGammaRealMero, rotGammaRealMero, upperEndTranslationMeroEquiv_algebraMap]
  rfl

theorem shiftedRotGammaRealMero_ne_zero (lam : ℂ) : shiftedRotGammaRealMero lam ≠ 0 := by
  intro h
  exact rotGammaRealMero_ne_zero ((upperEndTranslationMeroEquiv (Complex.I * lam)).injective
    (h.trans (map_zero _).symm))

theorem shiftedRotGammaRealAnalytic_coe (lam : ℂ) :
    (shiftedRotGammaRealAnalytic lam : Germ upperEndFilter ℂ) =
      Germ.coeRingHom upperEndFilter (fun z => Complex.Gammaℝ (2 * (-Complex.I * z + lam))) := by
  change upperEndTranslateGerm (Complex.I * lam) (Germ.coeRingHom upperEndFilter rotGammaRealFun) = _
  apply Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  change Complex.Gammaℝ (2 * (-Complex.I * (z + Complex.I * lam))) =
    Complex.Gammaℝ (2 * (-Complex.I * z + lam))
  have hI : -Complex.I * Complex.I = (1 : ℂ) := by norm_num
  rw [mul_add, ← mul_assoc (-Complex.I) Complex.I lam, hI, one_mul]

theorem deriv_shiftedRotGammaRealMero (lam : ℂ) :
    (shiftedRotGammaRealMero lam)′ =
      (algebraMap ℂ upperEndMeroField (-Complex.I) * shiftedRotDigammaMero lam +
        algebraMap ℂ upperEndMeroField (Complex.I * (Real.log Real.pi : ℂ))) *
          shiftedRotGammaRealMero lam := by
  rw [shiftedRotGammaRealMero, ← upperEndTranslationMeroEquiv_deriv,
    deriv_rotGammaRealMero, map_mul, map_add, map_mul,
    upperEndTranslate_algebraMap_complex_gen, upperEndTranslate_algebraMap_complex_gen]
  rfl

end

end RHTower
