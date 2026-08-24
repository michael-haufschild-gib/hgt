import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful

/-!
# Analytic Hasse principle for Burnol's co-Poisson quotient

Completed Mellin evaluations at all points of the open right critical strip separate Burnol's actual
co-Poisson quotient.  This file packages those evaluations as linear local probes, proves their
simultaneous kernel is zero, identifies quotient vectors with their realized strip profiles, and
extracts a single detecting strip point for every nonzero vector.

This is a literal analytic local-to-global interface for Connes--Tate/Burnol routes.  It supplies
faithfulness, not source realization: an arithmetic argument must still construct or identify the
quotient vector whose local evaluations are relevant.
-/

noncomputable section

namespace RHTower

/-- Points of the open right critical strip used as completed-Mellin local probes. -/
abbrev BurnolRightStrip :=
  {w : ℂ // 1 / 2 < w.re ∧ w.re < 1}

/-- Canonical inclusion of the co-Poisson quotient into the extended Sonine space. -/
def burnolCoPoissonToExtendedLinearMap (b : ℝ) :
    burnolCoPoissonQuotientSpace b →ₗ[ℂ] soninExtendedSpace b where
  toFun f := ⟨(f : evenSubspace), f.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Completed-Mellin evaluation at one strip point as a linear local probe. -/
def burnolCoPoissonStripEvaluationLinearMap
    (b : Set.Ioi (0 : ℝ)) (w : BurnolRightStrip) :
    burnolCoPoissonQuotientSpace (b : ℝ) →ₗ[ℂ] ℂ :=
  (burnolExtendedSoninEvaluationLinearMap (w : ℂ) (b : ℝ)
      w.property.1 w.property.2 b.property).comp
    (burnolCoPoissonToExtendedLinearMap (b : ℝ))

/-- Complete strip-evaluation profile of a co-Poisson quotient vector. -/
def burnolCoPoissonMellinProfile
    (b : Set.Ioi (0 : ℝ))
    (f : burnolCoPoissonQuotientSpace (b : ℝ)) :
    BurnolRightStrip → ℂ :=
  fun w ↦ burnolCoPoissonStripEvaluationLinearMap b w f

@[simp]
theorem burnolCoPoissonMellinProfile_apply
    (b : Set.Ioi (0 : ℝ))
    (f : burnolCoPoissonQuotientSpace (b : ℝ)) (w : BurnolRightStrip) :
    burnolCoPoissonMellinProfile b f w =
      soninMellinEvaluation (w : ℂ)
        ((((f : evenSubspace) : SoninL2)) : ℝ → ℂ) := rfl

/-- A co-Poisson quotient vector vanishes iff every right-strip Mellin probe vanishes. -/
theorem burnolCoPoissonQuotient_eq_zero_mellin_hasse_iff
    (b : Set.Ioi (0 : ℝ))
    (f : burnolCoPoissonQuotientSpace (b : ℝ)) :
    f = 0 ↔ ∀ w : BurnolRightStrip, burnolCoPoissonMellinProfile b f w = 0 := by
  constructor
  · rintro rfl
    intro w
    exact (burnolCoPoissonStripEvaluationLinearMap b w).map_zero
  · intro h
    apply burnolCoPoissonQuotientEvaluation_separates b.property f
    intro w hlo hhi
    exact h ⟨w, hlo, hhi⟩

/-- The complete right-strip Mellin profile is faithful on the actual quotient. -/
theorem burnolCoPoissonMellinProfile_injective
    (b : Set.Ioi (0 : ℝ)) :
    Function.Injective (burnolCoPoissonMellinProfile b) := by
  intro f g h
  apply sub_eq_zero.mp
  apply (burnolCoPoissonQuotient_eq_zero_mellin_hasse_iff b (f - g)).2
  intro w
  change burnolCoPoissonStripEvaluationLinearMap b w (f - g) = 0
  rw [map_sub]
  have hw := congrFun h w
  change burnolCoPoissonStripEvaluationLinearMap b w f =
    burnolCoPoissonStripEvaluationLinearMap b w g at hw
  exact sub_eq_zero.mpr hw

/-- Quotient vectors are equivalent to the strip Mellin profiles they realize. -/
noncomputable def burnolCoPoissonMellinProfileHasseEquivRange
    (b : Set.Ioi (0 : ℝ)) :
    burnolCoPoissonQuotientSpace (b : ℝ) ≃
      Set.range (burnolCoPoissonMellinProfile b) :=
  Equiv.ofInjective (burnolCoPoissonMellinProfile b)
    (burnolCoPoissonMellinProfile_injective b)

/-- Two quotient vectors agree iff all right-strip Mellin probes agree. -/
theorem burnolCoPoissonQuotient_congr_mellin_hasse_iff
    (b : Set.Ioi (0 : ℝ))
    (f g : burnolCoPoissonQuotientSpace (b : ℝ)) :
    f = g ↔ ∀ w : BurnolRightStrip,
      burnolCoPoissonMellinProfile b f w = burnolCoPoissonMellinProfile b g w := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    exact burnolCoPoissonMellinProfile_injective b (funext h)

/-- Every nonzero quotient vector is detected by one right-strip Mellin probe. -/
theorem exists_burnolRightStrip_mellin_ne_zero_of_ne_zero
    (b : Set.Ioi (0 : ℝ))
    (f : burnolCoPoissonQuotientSpace (b : ℝ)) (hf : f ≠ 0) :
    ∃ w : BurnolRightStrip, burnolCoPoissonMellinProfile b f w ≠ 0 := by
  by_contra h
  push Not at h
  exact hf ((burnolCoPoissonQuotient_eq_zero_mellin_hasse_iff b f).2 h)

end RHTower
