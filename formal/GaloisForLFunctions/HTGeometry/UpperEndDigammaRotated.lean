import GaloisForLFunctions.HTGeometry.UpperEndDigammaShift
import Mathlib

/-!
# The digamma in the Dirichlet coordinate

The corpus realises Dirichlet translation as `upperEndTranslationMeroEquiv (I * a)`, so the Dirichlet
variable is `s = -I z` and the natural shift on upper-end germs is by `I`.  The digamma must
therefore be pulled back along `z -> -I z` before it can share a shift with the Dirichlet germs.

`rotDigammaFun z = psi (-I z)` is analytic on every upper half-plane, because `Re (-I z) = Im z` is
large there and so the argument stays away from the poles of `Gamma`.  Its difference equation
becomes

`rotDigammaFun (z + I) = rotDigammaFun z + I / z`,

since `-I (z + I) = -I z + 1`.  The defect is again rational, so the whole descent applies with the
shift constant `I` in place of `1`.
-/

open Filter Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance upperEndRotDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance upperEndRotDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- The digamma in the Dirichlet coordinate. -/
def rotDigammaFun : ℂ → ℂ :=
  fun z => deriv Complex.Gamma (-Complex.I * z) / Complex.Gamma (-Complex.I * z)

/-- On an upper half-plane the rotated argument has positive real part. -/
theorem rot_re_pos {z : ℂ} (hz : z ∈ upperTail 0) : 0 < (-Complex.I * z).re := by
  simp only [upperTail, mem_setOf_eq] at hz
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  linarith

theorem rot_ne_negNat {z : ℂ} (hz : z ∈ upperTail 0) (n : ℕ) :
    (-Complex.I * z) ≠ -(n : ℂ) := by
  intro h
  have hpos := rot_re_pos hz
  rw [h] at hpos
  simp only [Complex.neg_re, Complex.natCast_re] at hpos
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem analyticOnNhd_rot : AnalyticOnNhd ℂ (fun z : ℂ => -Complex.I * z) (upperTail 0) :=
  fun _z _ => (analyticAt_const.mul analyticAt_id)

theorem rightHalf_ne_negNat {w : ℂ} (hw : 0 < w.re) (n : ℕ) : w ≠ -(n : ℂ) := by
  intro h
  rw [h] at hw
  simp only [Complex.neg_re, Complex.natCast_re] at hw
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem isOpen_rightHalf : IsOpen {w : ℂ | 0 < w.re} :=
  isOpen_lt continuous_const Complex.continuous_re

theorem analyticOnNhd_Gamma_rightHalf :
    AnalyticOnNhd ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_rightHalf
  intro w hw
  exact (Complex.differentiableAt_Gamma w (rightHalf_ne_negNat hw)).differentiableWithinAt

theorem rot_maps_rightHalf : ∀ z ∈ upperTail 0, (-Complex.I * z) ∈ {w : ℂ | 0 < w.re} :=
  fun _z hz => rot_re_pos hz

theorem analyticOnNhd_rotDigamma : AnalyticOnNhd ℂ rotDigammaFun (upperTail 0) := by
  have hG := analyticOnNhd_Gamma_rightHalf
  have hD : AnalyticOnNhd ℂ (deriv Complex.Gamma) {w : ℂ | 0 < w.re} :=
    fun w hw => (hG w hw).deriv
  have hGz : AnalyticOnNhd ℂ (fun z : ℂ => Complex.Gamma (-Complex.I * z)) (upperTail 0) :=
    hG.comp analyticOnNhd_rot rot_maps_rightHalf
  have hDz : AnalyticOnNhd ℂ (fun z : ℂ => deriv Complex.Gamma (-Complex.I * z))
      (upperTail 0) := hD.comp analyticOnNhd_rot rot_maps_rightHalf
  refine AnalyticOnNhd.div hDz hGz ?_
  intro z hz
  exact Complex.Gamma_ne_zero (rot_ne_negNat hz)

/-- **The difference equation in the Dirichlet coordinate.** -/
theorem rotDigamma_recurrence {z : ℂ} (hz : z ∈ upperTail 0) :
    rotDigammaFun (z + Complex.I) = rotDigammaFun z + Complex.I / z := by
  have hrot : -Complex.I * (z + Complex.I) = -Complex.I * z + 1 := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination -hI
  have hz0 : z ≠ 0 := ne_zero_of_mem_upperTail hz
  have hrec := digamma_recurrence (-Complex.I * z) (rot_ne_negNat hz)
  show deriv Complex.Gamma (-Complex.I * (z + Complex.I))
      / Complex.Gamma (-Complex.I * (z + Complex.I)) = _
  rw [hrot, hrec]
  show _ = deriv Complex.Gamma (-Complex.I * z) / Complex.Gamma (-Complex.I * z)
      + Complex.I / z
  congr 1
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hIne : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  rw [Complex.I_sq]

/-- The rotated defect `I / z`. -/
def rotDefectFun : ℂ → ℂ := fun z => Complex.I / z

theorem analyticOnNhd_rotDefect : AnalyticOnNhd ℂ rotDefectFun (upperTail 0) := by
  refine AnalyticOnNhd.div analyticOnNhd_const analyticOnNhd_id ?_
  intro z hz
  exact ne_zero_of_mem_upperTail hz

/-- The rotated digamma as an upper-end analytic germ. -/
def rotDigammaAnalytic : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter rotDigammaFun),
    ⟨rotDigammaFun, 0, analyticOnNhd_rotDigamma, rfl⟩⟩

/-- The rotated defect as an upper-end analytic germ. -/
def rotDefectAnalytic : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter rotDefectFun),
    ⟨rotDefectFun, 0, analyticOnNhd_rotDefect, rfl⟩⟩

def rotDigammaMero : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField rotDigammaAnalytic

def rotDefectMero : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField rotDefectAnalytic

/-- **The rotated difference equation, as an identity of upper-end germs.** -/
theorem upperEndTranslate_rotDigammaAnalytic :
    upperEndTranslationAnalyticEquiv Complex.I rotDigammaAnalytic
      = rotDigammaAnalytic + rotDefectAnalytic := by
  apply Subtype.ext
  change upperEndTranslateGerm Complex.I (Germ.coeRingHom upperEndFilter rotDigammaFun)
    = (Germ.coeRingHom upperEndFilter rotDigammaFun)
      + (Germ.coeRingHom upperEndFilter rotDefectFun)
  have hev : ∀ᶠ z : ℂ in upperEndFilter,
      rotDigammaFun (z + Complex.I) = rotDigammaFun z + rotDefectFun z := by
    rw [upperEndFilter_basis.eventually_iff]
    exact ⟨0, trivial, fun z hz => rotDigamma_recurrence hz⟩
  exact Germ.coe_eq.mpr hev

theorem upperEndTranslate_rotDigammaMero :
    upperEndTranslationMeroEquiv Complex.I rotDigammaMero
      = rotDigammaMero + rotDefectMero := by
  rw [rotDigammaMero, upperEndTranslationMeroEquiv_algebraMap,
    upperEndTranslate_rotDigammaAnalytic, map_add]
  rfl

/-- The `n`-th rotated digamma jet. -/
def rotDigammaJetMero (n : ℕ) : upperEndMeroField := differentialJet n rotDigammaMero

/-- The `n`-th rotated defect. -/
def rotDefectJetMero (n : ℕ) : upperEndMeroField := differentialJet n rotDefectMero

/-- **All rotated jets inherit the shift relation.** -/
theorem upperEndTranslate_rotDigammaJetMero (n : ℕ) :
    upperEndTranslationMeroEquiv Complex.I (rotDigammaJetMero n)
      = rotDigammaJetMero n + rotDefectJetMero n := by
  induction n with
  | zero =>
      simpa [rotDigammaJetMero, rotDefectJetMero] using upperEndTranslate_rotDigammaMero
  | succ n ih =>
      rw [rotDigammaJetMero, rotDefectJetMero, differentialJet_succ, differentialJet_succ,
        upperEndTranslationMeroEquiv_deriv]
      rw [show differentialJet n rotDigammaMero = rotDigammaJetMero n from rfl, ih]
      rw [show differentialJet n rotDefectMero = rotDefectJetMero n from rfl]
      exact map_add _ _ _

end

end GaloisForLFunctions.HTGeometry
