import GaloisForLFunctions.RHTower.ConnesSchwartzHadamard
import GaloisForLFunctions.HTGeometry.FrechetClosedRange
import GaloisForLFunctions.HTGeometry.SchwartzComplete
import GaloisForLFunctions.HTGeometry.HermiteOrthogonality
import GaloisForLFunctions.HTGeometry.SchwartzTranslation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZParityTemperedDistributionLocalProbeNoGo

/-!
# FZZ puncture tempered scalar occurrence no-go

The FZZ-P generalized-spectrum fallback asks whether a scalar puncture equation

`(x - E) T = S`

on a rigged carrier can make generalized-state occurrence select the real energies attached to the
Mellin divisor.  This module closes that entire scalar tempered-distribution class.  Multiplication
by `x` on Schwartz tests is injective with closed codimension-one range, because the range is exactly
the kernel of evaluation at zero.  Corpus Hadamard division and Schwartz completeness make the
inverse on that range continuous.  A Gaussian projection then gives an explicit continuous right
inverse on all tests.

Consequently every tempered source is divisible by `x-E` in `𝓢'` at every real `E`.  The full
solution set is an affine line with homogeneous fibre `ℂ · δ_E`.  Thus mere generalized scalar
occurrence is identically true on `ℝ` and cannot be the missing FZZ divisor-incidence law.

This does not kill the corpus's fixed nonlocal theta-source Fredholm occurrence, singular domain
extensions, matrix/interacting carriers, or a source-derived boundary functional that fixes the
free Dirac coefficient.  The generic division theorem is classical distribution theory; the new
route conclusion is the exact FZZ-P scalar-tempered no-go and its sharp Dirac-fibre survivor.

Tags: [NEW] [FZZ-P] [ROUTE KILL] [CLASSIFICATION] [POSITIVE SURVIVOR]
-/

open Complex MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.RHTower

theorem mulXCLM_injective : Function.Injective mulXCLM := by
  intro φ ψ h
  apply SchwartzMap.ext
  intro x
  by_cases hx : x = 0
  · subst x
    have hd := congrArg derivSCLM h
    rw [derivSCLM_mulXCLM, derivSCLM_mulXCLM] at hd
    have h0 := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) hd
    simpa using h0
  · have hpoint := congrArg (fun f : 𝓢(ℝ, ℂ) => f x) h
    rw [mulXCLM_apply, mulXCLM_apply] at hpoint
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hx) hpoint

theorem mulXCLM_range_eq_diracKer :
    LinearMap.range mulXCLM.toLinearMap =
      LinearMap.ker (fzzCigarParityTemperedDirac 0).toLinearMap := by
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩
    change (fzzCigarParityTemperedDirac 0) (mulXCLM ψ) = 0
    rw [fzzCigarParityTemperedDirac_apply, mulXCLM_apply]
    norm_num
  · intro hφ
    have h0 : φ 0 = 0 := by
      change (fzzCigarParityTemperedDirac 0) φ = 0 at hφ
      rw [fzzCigarParityTemperedDirac_apply] at hφ
      exact hφ
    refine ⟨connesHadamardQuotient φ h0, ?_⟩
    apply SchwartzMap.ext
    intro x
    change mulXCLM (connesHadamardQuotient φ h0) x = φ x
    rw [mulXCLM_apply]
    exact (connes_schwartz_hadamard φ h0 x).symm

theorem mulXCLM_range_isClosed :
    IsClosed (LinearMap.range mulXCLM.toLinearMap : Set 𝓢(ℝ, ℂ)) := by
  rw [mulXCLM_range_eq_diracKer]
  exact (fzzCigarParityTemperedDirac 0).isClosed_ker

noncomputable def mulXRangeInverseCLM :
    ↥(LinearMap.range mulXCLM.toLinearMap) →L[ℂ] 𝓢(ℝ, ℂ) where
  toLinearMap := (frechetRangeEquiv mulXCLM.toLinearMap mulXCLM_injective).symm
  cont := continuous_frechetRangeEquiv_symm_of_isClosed mulXCLM.toLinearMap
    mulXCLM.continuous mulXCLM_injective mulXCLM_range_isClosed

def zeroProjectionCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ContinuousLinearMap.id ℂ _ -
    (fzzCigarParityTemperedDirac 0).smulRight gaussianSchwartz

theorem zeroProjectionCLM_apply (φ : 𝓢(ℝ, ℂ)) :
    zeroProjectionCLM φ = φ - φ 0 • gaussianSchwartz := by
  rfl

theorem zeroProjectionCLM_zero (φ : 𝓢(ℝ, ℂ)) :
    zeroProjectionCLM φ 0 = 0 := by
  rw [zeroProjectionCLM_apply]
  simp [gaussianSchwartz_apply, gaussReal]

def zeroProjectionRangeCLM :
    𝓢(ℝ, ℂ) →L[ℂ] ↥(LinearMap.range mulXCLM.toLinearMap) :=
  zeroProjectionCLM.codRestrict (LinearMap.range mulXCLM.toLinearMap) fun φ => by
    rw [mulXCLM_range_eq_diracKer]
    change (fzzCigarParityTemperedDirac 0) (zeroProjectionCLM φ) = 0
    rw [fzzCigarParityTemperedDirac_apply, zeroProjectionCLM_zero]

noncomputable def mulXRightInverseCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  mulXRangeInverseCLM.comp zeroProjectionRangeCLM

def mulXRangeValue (φ : 𝓢(ℝ, ℂ)) :
    ↥(LinearMap.range mulXCLM.toLinearMap) :=
  ⟨mulXCLM φ, ⟨φ, rfl⟩⟩

theorem zeroProjectionRangeCLM_mulXCLM (φ : 𝓢(ℝ, ℂ)) :
    zeroProjectionRangeCLM (mulXCLM φ) = mulXRangeValue φ := by
  apply Subtype.ext
  change zeroProjectionCLM (mulXCLM φ) = mulXCLM φ
  rw [zeroProjectionCLM_apply]
  simp [mulXCLM_apply]

theorem mulXRightInverseCLM_mulXCLM (φ : 𝓢(ℝ, ℂ)) :
    mulXRightInverseCLM (mulXCLM φ) = φ := by
  rw [mulXRightInverseCLM, ContinuousLinearMap.comp_apply,
    zeroProjectionRangeCLM_mulXCLM]
  exact (frechetRangeEquiv mulXCLM.toLinearMap mulXCLM_injective).symm_apply_apply φ

theorem mulXCLM_mulXRightInverseCLM (φ : 𝓢(ℝ, ℂ)) :
    mulXCLM (mulXRightInverseCLM φ) = zeroProjectionCLM φ := by
  have h := (frechetRangeEquiv mulXCLM.toLinearMap mulXCLM_injective).apply_symm_apply
    (zeroProjectionRangeCLM φ)
  exact congrArg Subtype.val h

def temperedCoordinateMul (T : 𝓢'(ℝ, ℂ)) : 𝓢'(ℝ, ℂ) :=
  T.comp mulXCLM

noncomputable def temperedCoordinateDivisionSolution (S : 𝓢'(ℝ, ℂ)) : 𝓢'(ℝ, ℂ) :=
  S.comp mulXRightInverseCLM

theorem temperedCoordinateMul_divisionSolution (S : 𝓢'(ℝ, ℂ)) :
    temperedCoordinateMul (temperedCoordinateDivisionSolution S) = S := by
  ext φ
  exact congrArg S (mulXRightInverseCLM_mulXCLM φ)

@[simp] theorem temperedCoordinateMul_add (T U : 𝓢'(ℝ, ℂ)) :
    temperedCoordinateMul (T + U) = temperedCoordinateMul T + temperedCoordinateMul U := by
  rfl

@[simp] theorem temperedCoordinateMul_sub (T U : 𝓢'(ℝ, ℂ)) :
    temperedCoordinateMul (T - U) = temperedCoordinateMul T - temperedCoordinateMul U := by
  rfl

@[simp] theorem temperedCoordinateMul_smul (c : ℂ) (T : 𝓢'(ℝ, ℂ)) :
    temperedCoordinateMul (c • T) = c • temperedCoordinateMul T := by
  rfl

@[simp] theorem temperedCoordinateMul_dirac_zero :
    temperedCoordinateMul (fzzCigarParityTemperedDirac 0) = 0 := by
  ext φ
  change (fzzCigarParityTemperedDirac 0) (mulXCLM φ) = 0
  rw [fzzCigarParityTemperedDirac_apply, mulXCLM_apply]
  norm_num

/-- The homogeneous fibre is exactly the Dirac line. -/
theorem temperedCoordinateMul_eq_zero_iff (T : 𝓢'(ℝ, ℂ)) :
    temperedCoordinateMul T = 0 ↔
      ∃ c : ℂ, T = c • fzzCigarParityTemperedDirac 0 := by
  constructor
  · intro hT
    refine ⟨T gaussianSchwartz, ?_⟩
    ext φ
    have hmul : T (mulXCLM (mulXRightInverseCLM φ)) = 0 := by
      have h := congrArg (fun U : 𝓢'(ℝ, ℂ) => U (mulXRightInverseCLM φ)) hT
      exact h
    calc
      T φ = T (zeroProjectionCLM φ + φ 0 • gaussianSchwartz) := by
        rw [zeroProjectionCLM_apply, sub_add_cancel]
      _ = T (zeroProjectionCLM φ) + T (φ 0 • gaussianSchwartz) := by rw [map_add]
      _ = T (mulXCLM (mulXRightInverseCLM φ)) + T (φ 0 • gaussianSchwartz) := by
        rw [mulXCLM_mulXRightInverseCLM]
      _ = T (φ 0 • gaussianSchwartz) := by rw [hmul, zero_add]
      _ = (T gaussianSchwartz • fzzCigarParityTemperedDirac 0) φ := by
        rw [map_smul]
        change φ 0 * T gaussianSchwartz = T gaussianSchwartz * φ 0
        ring
  · rintro ⟨c, rfl⟩
    rw [temperedCoordinateMul_smul, temperedCoordinateMul_dirac_zero, smul_zero]

/-- Every inhomogeneous solution differs from the canonical division solution by one Dirac mass. -/
theorem temperedCoordinateMul_eq_source_iff (T S : 𝓢'(ℝ, ℂ)) :
    temperedCoordinateMul T = S ↔
      ∃ c : ℂ,
        T = temperedCoordinateDivisionSolution S +
          c • fzzCigarParityTemperedDirac 0 := by
  constructor
  · intro hT
    have hk : temperedCoordinateMul (T - temperedCoordinateDivisionSolution S) = 0 := by
      rw [temperedCoordinateMul_sub, hT, temperedCoordinateMul_divisionSolution, sub_self]
    obtain ⟨c, hc⟩ := (temperedCoordinateMul_eq_zero_iff _).mp hk
    refine ⟨c, ?_⟩
    calc
      T = (T - temperedCoordinateDivisionSolution S) +
          temperedCoordinateDivisionSolution S := by module
      _ = c • fzzCigarParityTemperedDirac 0 +
          temperedCoordinateDivisionSolution S := by rw [hc]
      _ = temperedCoordinateDivisionSolution S +
          c • fzzCigarParityTemperedDirac 0 := add_comm _ _
  · rintro ⟨c, rfl⟩
    rw [temperedCoordinateMul_add, temperedCoordinateMul_divisionSolution,
      temperedCoordinateMul_smul, temperedCoordinateMul_dirac_zero, smul_zero, add_zero]

/-- Multiplication by `x-E`, obtained by conjugating coordinate multiplication by translation. -/
def shiftedCoordinateMulCLM (E : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.translateCLM ℂ (-E)).comp
    (mulXCLM.comp (SchwartzMap.translateCLM ℂ E))

@[simp] theorem shiftedCoordinateMulCLM_apply (E x : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    shiftedCoordinateMulCLM E φ x = ((x - E : ℝ) : ℂ) * φ x := by
  simp only [shiftedCoordinateMulCLM, ContinuousLinearMap.comp_apply,
    SchwartzMap.translateCLM_apply, mulXCLM_apply]
  push_cast
  ring_nf

/-- Distributional multiplication by the shifted puncture coordinate. -/
def shiftedTemperedCoordinateMul (E : ℝ) (T : 𝓢'(ℝ, ℂ)) : 𝓢'(ℝ, ℂ) :=
  T.comp (shiftedCoordinateMulCLM E)

/-- Canonical tempered solution transported from the centered division operator. -/
noncomputable def shiftedTemperedDivisionSolution (E : ℝ) (S : 𝓢'(ℝ, ℂ)) : 𝓢'(ℝ, ℂ) :=
  (temperedCoordinateDivisionSolution
      (S.comp (SchwartzMap.translateCLM ℂ (-E)))).comp
    (SchwartzMap.translateCLM ℂ E)

/-- Every tempered source is divisible by `x-E` in tempered distributions. -/
theorem shiftedTemperedCoordinateMul_divisionSolution (E : ℝ) (S : 𝓢'(ℝ, ℂ)) :
    shiftedTemperedCoordinateMul E (shiftedTemperedDivisionSolution E S) = S := by
  ext φ
  change temperedCoordinateDivisionSolution (S.comp (SchwartzMap.translateCLM ℂ (-E)))
      (SchwartzMap.translateCLM ℂ E
        (SchwartzMap.translateCLM ℂ (-E)
          (mulXCLM (SchwartzMap.translateCLM ℂ E φ)))) = S φ
  rw [SchwartzMap.translateCLM_neg_right]
  have h := congrArg (fun U : 𝓢'(ℝ, ℂ) => U (SchwartzMap.translateCLM ℂ E φ))
    (temperedCoordinateMul_divisionSolution
      (S.comp (SchwartzMap.translateCLM ℂ (-E))))
  change temperedCoordinateDivisionSolution (S.comp (SchwartzMap.translateCLM ℂ (-E)))
      (mulXCLM (SchwartzMap.translateCLM ℂ E φ)) =
        S (SchwartzMap.translateCLM ℂ (-E) (SchwartzMap.translateCLM ℂ E φ)) at h
  rw [SchwartzMap.translateCLM_neg_left] at h
  exact h

@[simp] theorem shiftedTemperedCoordinateMul_add (E : ℝ) (T U : 𝓢'(ℝ, ℂ)) :
    shiftedTemperedCoordinateMul E (T + U) =
      shiftedTemperedCoordinateMul E T + shiftedTemperedCoordinateMul E U := by
  rfl

@[simp] theorem shiftedTemperedCoordinateMul_sub (E : ℝ) (T U : 𝓢'(ℝ, ℂ)) :
    shiftedTemperedCoordinateMul E (T - U) =
      shiftedTemperedCoordinateMul E T - shiftedTemperedCoordinateMul E U := by
  rfl

@[simp] theorem shiftedTemperedCoordinateMul_smul (E : ℝ) (c : ℂ) (T : 𝓢'(ℝ, ℂ)) :
    shiftedTemperedCoordinateMul E (c • T) =
      c • shiftedTemperedCoordinateMul E T := by
  rfl

@[simp] theorem shiftedTemperedCoordinateMul_dirac (E : ℝ) :
    shiftedTemperedCoordinateMul E (fzzCigarParityTemperedDirac E) = 0 := by
  ext φ
  change (fzzCigarParityTemperedDirac E) (shiftedCoordinateMulCLM E φ) = 0
  rw [fzzCigarParityTemperedDirac_apply, shiftedCoordinateMulCLM_apply]
  simp

/-- At energy `E`, the homogeneous fibre is exactly the Dirac mass at `E`. -/
theorem shiftedTemperedCoordinateMul_eq_zero_iff (E : ℝ) (T : 𝓢'(ℝ, ℂ)) :
    shiftedTemperedCoordinateMul E T = 0 ↔
      ∃ c : ℂ, T = c • fzzCigarParityTemperedDirac E := by
  constructor
  · intro hT
    let U : 𝓢'(ℝ, ℂ) := T.comp (SchwartzMap.translateCLM ℂ (-E))
    have hU : temperedCoordinateMul U = 0 := by
      ext φ
      have h := congrArg (fun V : 𝓢'(ℝ, ℂ) =>
        V (SchwartzMap.translateCLM ℂ (-E) φ)) hT
      change T (SchwartzMap.translateCLM ℂ (-E) (mulXCLM φ)) = 0
      change T (SchwartzMap.translateCLM ℂ (-E)
        (mulXCLM (SchwartzMap.translateCLM ℂ E
          (SchwartzMap.translateCLM ℂ (-E) φ)))) = 0 at h
      rw [SchwartzMap.translateCLM_neg_right] at h
      exact h
    obtain ⟨c, hc⟩ := (temperedCoordinateMul_eq_zero_iff U).mp hU
    refine ⟨c, ?_⟩
    ext φ
    have h := congrArg (fun V : 𝓢'(ℝ, ℂ) =>
      V (SchwartzMap.translateCLM ℂ E φ)) hc
    change T (SchwartzMap.translateCLM ℂ (-E)
        (SchwartzMap.translateCLM ℂ E φ)) =
      (c • fzzCigarParityTemperedDirac 0) (SchwartzMap.translateCLM ℂ E φ) at h
    rw [SchwartzMap.translateCLM_neg_left] at h
    change T φ = c * φ E
    simpa [fzzCigarParityTemperedDirac_apply] using h
  · rintro ⟨c, rfl⟩
    rw [shiftedTemperedCoordinateMul_smul,
      shiftedTemperedCoordinateMul_dirac, smul_zero]

/-- Complete affine classification at every real puncture energy. -/
theorem shiftedTemperedCoordinateMul_eq_source_iff
    (E : ℝ) (T S : 𝓢'(ℝ, ℂ)) :
    shiftedTemperedCoordinateMul E T = S ↔
      ∃ c : ℂ,
        T = shiftedTemperedDivisionSolution E S +
          c • fzzCigarParityTemperedDirac E := by
  constructor
  · intro hT
    have hk : shiftedTemperedCoordinateMul E
        (T - shiftedTemperedDivisionSolution E S) = 0 := by
      rw [shiftedTemperedCoordinateMul_sub, hT,
        shiftedTemperedCoordinateMul_divisionSolution, sub_self]
    obtain ⟨c, hc⟩ := (shiftedTemperedCoordinateMul_eq_zero_iff E _).mp hk
    refine ⟨c, ?_⟩
    calc
      T = (T - shiftedTemperedDivisionSolution E S) +
          shiftedTemperedDivisionSolution E S := by module
      _ = c • fzzCigarParityTemperedDirac E +
          shiftedTemperedDivisionSolution E S := by rw [hc]
      _ = shiftedTemperedDivisionSolution E S +
          c • fzzCigarParityTemperedDirac E := add_comm _ _
  · rintro ⟨c, rfl⟩
    rw [shiftedTemperedCoordinateMul_add,
      shiftedTemperedCoordinateMul_divisionSolution,
      shiftedTemperedCoordinateMul_smul,
      shiftedTemperedCoordinateMul_dirac, smul_zero, add_zero]

/-- The Dirac coefficient in the affine classification is unique. -/
theorem shiftedTemperedCoordinateMul_eq_source_iff_existsUnique
    (E : ℝ) (T S : 𝓢'(ℝ, ℂ)) :
    shiftedTemperedCoordinateMul E T = S ↔
      ∃! c : ℂ,
        T = shiftedTemperedDivisionSolution E S +
          c • fzzCigarParityTemperedDirac E := by
  constructor
  · intro hT
    obtain ⟨c, hc⟩ := (shiftedTemperedCoordinateMul_eq_source_iff E T S).mp hT
    refine ⟨c, hc, ?_⟩
    intro d hd
    have hcd : c • fzzCigarParityTemperedDirac E =
        d • fzzCigarParityTemperedDirac E := by
      calc
        c • fzzCigarParityTemperedDirac E =
            T - shiftedTemperedDivisionSolution E S := by rw [hc]; module
        _ = d • fzzCigarParityTemperedDirac E := by rw [hd]; module
    let gE : 𝓢(ℝ, ℂ) := SchwartzMap.translateCLM ℂ (-E) gaussianSchwartz
    have hval := congrArg (fun V : 𝓢'(ℝ, ℂ) => V gE) hcd
    change c * gE E = d * gE E at hval
    have hgE : gE E = 1 := by
      simp [gE, gaussianSchwartz_apply, gaussReal]
    symm
    simpa [hgE] using hval
  · rintro ⟨c, hc, _⟩
    exact (shiftedTemperedCoordinateMul_eq_source_iff E T S).mpr ⟨c, hc⟩

/-- Generalized scalar occurrence for a fixed tempered source at energy `E`. -/
def FZZPunctureTemperedScalarOccurrence (S : 𝓢'(ℝ, ℂ)) (E : ℝ) : Prop :=
  ∃ T : 𝓢'(ℝ, ℂ), shiftedTemperedCoordinateMul E T = S

/-- Generalized scalar occurrence is universal in energy for every tempered source. -/
theorem fzzPunctureTemperedScalarOccurrence_all_energy (S : 𝓢'(ℝ, ℂ)) :
    ∀ E : ℝ, FZZPunctureTemperedScalarOccurrence S E := by
  intro E
  exact ⟨shiftedTemperedDivisionSolution E S,
    shiftedTemperedCoordinateMul_divisionSolution E S⟩

/-- **FZZ-P generalized-scalar occurrence route kill.** The occurrence set is all of `ℝ`, so
mere existence of a tempered scalar puncture solution cannot select Mellin-divisor ordinates. -/
theorem fzzPunctureTemperedScalarOccurrence_set_eq_univ (S : 𝓢'(ℝ, ℂ)) :
    {E : ℝ | FZZPunctureTemperedScalarOccurrence S E} = Set.univ := by
  exact Set.eq_univ_of_forall (fzzPunctureTemperedScalarOccurrence_all_energy S)

end
end RHTower
