import GaloisForLFunctions.HTGeometry.UpperEndDigammaRotated
import GaloisForLFunctions.HTGeometry.ShiftRationalBase
import Mathlib

/-!
# The Dirichlet coordinate at the upper end

Upper-end translation by `I` acts on the Dirichlet variable `s = -I z` as `s ↦ s + 1`.  The germ
`dirCoordMero` of `z ↦ -I z` is therefore the coordinate in which the analytic shift and the
coefficient-side Dirichlet shift are the *same* unit shift.

In this coordinate the rotated digamma difference equation `psiTilde (z + I) = psiTilde z + I / z`
has defects `delta^n (I / z)`, and `delta^n (I / z) * dirCoordMero ^ (n+1)` is a nonzero constant.
The unit-shift rational-base descent then gives Hölder's theorem in the Dirichlet coordinate.
-/

open Filter Set Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance upperEndDirDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance upperEndDirDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance upperEndDirComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- The Dirichlet variable `s = -I z` as a function. -/
def dirCoordFun : ℂ → ℂ := fun z => -Complex.I * z

theorem analyticOnNhd_dirCoordFun : AnalyticOnNhd ℂ dirCoordFun (upperTail 0) :=
  fun _ _ => analyticAt_const.mul analyticAt_id

/-- The Dirichlet variable as an upper-end analytic germ. -/
def dirCoordAnalytic : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter dirCoordFun),
    ⟨dirCoordFun, 0, analyticOnNhd_dirCoordFun, rfl⟩⟩

/-- The Dirichlet variable in the upper-end meromorphic field. -/
def dirCoordMero : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField dirCoordAnalytic

theorem dirCoordAnalytic_eq :
    dirCoordAnalytic = upperEndPolyToAnalytic (Polynomial.C (-Complex.I)) * coordAnalytic := by
  apply Subtype.ext
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  simp [dirCoordFun]

theorem dirCoordMero_eq :
    dirCoordMero = algebraMap ℂ upperEndMeroField (-Complex.I) * coordMero := by
  rw [dirCoordMero, dirCoordAnalytic_eq, map_mul]
  rfl

/-- **The Dirichlet variable is transcendental over the constants.** -/
theorem transcendental_dirCoordMero : Transcendental ℂ dirCoordMero := by
  rw [dirCoordMero_eq]
  exact _root_.HTGeometry.transcendental_const_mul transcendental_coordMero
    (by simp)

/-- Translation fixes the constants. -/
theorem upperEndTranslate_algebraMap_complex_gen (h a : ℂ) :
    upperEndTranslationMeroEquiv h (algebraMap ℂ upperEndMeroField a)
      = algebraMap ℂ upperEndMeroField a := by
  have hdef : (algebraMap ℂ upperEndMeroField a)
      = algebraMap upperEndAnalyticSubring upperEndMeroField
          (upperEndPolyToAnalytic (Polynomial.C a)) := rfl
  rw [hdef, upperEndTranslationMeroEquiv_algebraMap]
  congr 1
  apply Subtype.ext
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  simp

/-- **Translation by `I` is the unit shift of the Dirichlet variable.** -/
theorem upperEndTranslate_dirCoordAnalytic :
    upperEndTranslationAnalyticEquiv Complex.I dirCoordAnalytic = dirCoordAnalytic + 1 := by
  apply Subtype.ext
  change upperEndTranslateGerm Complex.I (Germ.coeRingHom upperEndFilter dirCoordFun)
    = (Germ.coeRingHom upperEndFilter dirCoordFun) + 1
  have h1 : (1 : Germ upperEndFilter ℂ)
      = Germ.coeRingHom upperEndFilter (fun _ : ℂ => (1 : ℂ)) := rfl
  rw [h1, ← map_add]
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  show -Complex.I * (z + Complex.I) = -Complex.I * z + 1
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination -hI

theorem upperEndTranslate_dirCoordMero :
    upperEndTranslationMeroEquiv Complex.I dirCoordMero = dirCoordMero + 1 := by
  rw [dirCoordMero, upperEndTranslationMeroEquiv_algebraMap,
    upperEndTranslate_dirCoordAnalytic, map_add, map_one]

/-- Translation by `I` as a `C`-algebra automorphism. -/
def dirTranslationAlgEquiv : upperEndMeroField ≃ₐ[ℂ] upperEndMeroField :=
  AlgEquiv.ofRingEquiv (f := upperEndTranslationMeroEquiv Complex.I)
    (fun a => upperEndTranslate_algebraMap_complex_gen Complex.I a)

theorem dirTranslationAlgEquiv_apply (u : upperEndMeroField) :
    dirTranslationAlgEquiv u = upperEndTranslationMeroEquiv Complex.I u := rfl

/-! ## The rotated defect jets in closed form -/

/-- The `n`-th derivative of `I / z`. -/
def rotInvPowFun (n : ℕ) : ℂ → ℂ :=
  fun z => Complex.I * ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (z ^ (n + 1))⁻¹

theorem rotInvPowFun_zero : rotInvPowFun 0 = rotDefectFun := by
  funext z; simp [rotInvPowFun, rotDefectFun, div_eq_mul_inv]

theorem deriv_rotInvPowFun (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    deriv (rotInvPowFun n) z = rotInvPowFun (n + 1) z := by
  have hpow : (z : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ hz
  have hd : HasDerivAt (fun w : ℂ => w ^ (n + 1)) ((n + 1 : ℕ) * z ^ n) z := by
    simpa using (hasDerivAt_pow (n + 1) z)
  have hinv : HasDerivAt (fun w : ℂ => (w ^ (n + 1))⁻¹)
      (-((n + 1 : ℕ) * z ^ n) / (z ^ (n + 1)) ^ 2) z := hd.inv hpow
  have hfull : HasDerivAt (rotInvPowFun n)
      ((Complex.I * ((-1 : ℂ) ^ n * (n.factorial : ℂ))) *
        (-((n + 1 : ℕ) * z ^ n) / (z ^ (n + 1)) ^ 2)) z :=
    hinv.const_mul (Complex.I * ((-1 : ℂ) ^ n * (n.factorial : ℂ)))
  rw [hfull.deriv]
  show _ = Complex.I * ((-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ)) * (z ^ (n + 1 + 1))⁻¹
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem analyticOnNhd_rotInvPowFun (n : ℕ) :
    AnalyticOnNhd ℂ (rotInvPowFun n) (upperTail 0) := by
  refine AnalyticOnNhd.mul analyticOnNhd_const (AnalyticOnNhd.inv (analyticOnNhd_id.pow _) ?_)
  intro z hz
  exact pow_ne_zero _ (ne_zero_of_mem_upperTail hz)

/-- The `n`-th rotated defect as an upper-end analytic germ. -/
def rotInvPowAnalytic (n : ℕ) : upperEndAnalyticSubring :=
  ⟨(Germ.coeRingHom upperEndFilter (rotInvPowFun n)),
    ⟨rotInvPowFun n, 0, analyticOnNhd_rotInvPowFun n, rfl⟩⟩

theorem rotInvPowAnalytic_zero : rotInvPowAnalytic 0 = rotDefectAnalytic := by
  apply Subtype.ext
  change (Germ.coeRingHom upperEndFilter (rotInvPowFun 0))
    = (Germ.coeRingHom upperEndFilter rotDefectFun)
  rw [rotInvPowFun_zero]

theorem upperEndAnalyticDeriv_rotInvPowAnalytic (n : ℕ) :
    upperEndAnalyticDeriv (rotInvPowAnalytic n) = rotInvPowAnalytic (n + 1) := by
  apply Subtype.ext
  rw [upperEndAnalyticDeriv_coe]
  show upperEndGermDeriv (Germ.coeRingHom upperEndFilter (rotInvPowFun n))
    = (Germ.coeRingHom upperEndFilter (rotInvPowFun (n + 1)))
  have hev : ∀ᶠ z : ℂ in upperEndFilter, deriv (rotInvPowFun n) z = rotInvPowFun (n + 1) z := by
    rw [upperEndFilter_basis.eventually_iff]
    exact ⟨0, trivial, fun z hz => deriv_rotInvPowFun n (ne_zero_of_mem_upperTail hz)⟩
  exact Germ.coe_eq.mpr hev

/-- **The rotated defect jets are the explicit reciprocal powers.** -/
theorem rotDefectJetMero_eq (n : ℕ) :
    rotDefectJetMero n
      = algebraMap upperEndAnalyticSubring upperEndMeroField (rotInvPowAnalytic n) := by
  induction n with
  | zero => rw [rotDefectJetMero, differentialJet_zero, rotInvPowAnalytic_zero, rotDefectMero]
  | succ n ih =>
      rw [rotDefectJetMero, differentialJet_succ,
        show differentialJet n rotDefectMero = rotDefectJetMero n from rfl, ih,
        upperEndMeroFieldDifferential_algebraMap, upperEndAnalyticDeriv_rotInvPowAnalytic]

/-- The rotated defect constants. -/
def rotDefectConst (n : ℕ) : ℂ :=
  Complex.I * ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (-Complex.I) ^ (n + 1)

theorem rotDefectConst_ne_zero (n : ℕ) : rotDefectConst n ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero Complex.I_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_)) (pow_ne_zero _ ?_)
  · exact_mod_cast Nat.factorial_ne_zero n
  · simp

/-- **The defect jets scaled by a power of the Dirichlet variable are constants.** -/
theorem rotDefectJetMero_mul_dirCoordMero_pow (n : ℕ) :
    rotDefectJetMero n * dirCoordMero ^ (n + 1)
      = algebraMap ℂ upperEndMeroField (rotDefectConst n) := by
  rw [rotDefectJetMero_eq, dirCoordMero, ← map_pow, ← map_mul]
  have hmul : rotInvPowAnalytic n * dirCoordAnalytic ^ (n + 1)
      = upperEndPolyToAnalytic (Polynomial.C (rotDefectConst n)) := by
    apply Subtype.ext
    change (Germ.coeRingHom upperEndFilter (rotInvPowFun n))
        * ((Germ.coeRingHom upperEndFilter dirCoordFun) ^ (n + 1)) = _
    rw [← map_pow, ← map_mul]
    have hev : ∀ᶠ z : ℂ in upperEndFilter,
        rotInvPowFun n z * dirCoordFun z ^ (n + 1) = rotDefectConst n := by
      rw [upperEndFilter_basis.eventually_iff]
      refine ⟨0, trivial, fun z hz => ?_⟩
      have hz0 : z ≠ 0 := ne_zero_of_mem_upperTail hz
      have hzp : z ^ (n + 1) ≠ 0 := pow_ne_zero _ hz0
      rw [rotInvPowFun, dirCoordFun, rotDefectConst, mul_pow]
      field_simp
    refine (Germ.coe_eq.mpr hev).trans ?_
    refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
    simp
  rw [hmul]
  rfl

/-! ## Hölder's theorem in the Dirichlet coordinate -/

/-- **Hölder's theorem in the Dirichlet coordinate.**  Every rotated digamma jet is transcendental
over the field generated by `C(s)` and its predecessors. -/
theorem rot_digamma_jets_transcendental (n : ℕ) :
    Transcendental
      (_root_.HTGeometry.jetTower (_root_.HTGeometry.coordBase dirCoordMero)
        rotDigammaJetMero n) (rotDigammaJetMero n) :=
  _root_.HTGeometry.coordBase_jetTower_transcendental
    transcendental_dirCoordMero rotDefectConst_ne_zero
    rotDefectJetMero_mul_dirCoordMero_pow
    dirTranslationAlgEquiv upperEndTranslate_dirCoordMero
    upperEndTranslate_rotDigammaJetMero n

end

end GaloisForLFunctions.HTGeometry
