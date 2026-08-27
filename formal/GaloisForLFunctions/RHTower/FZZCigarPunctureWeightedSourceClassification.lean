import GaloisForLFunctions.RHTower.FZZCigarPunctureCriticalLogNodalThreshold

/-!
# FZZ puncture weighted-source classification

The scalar puncture equation

`(x - E) f(x) + v(x) = 0`

has at most one almost-everywhere solution.  Its canonical solution is the weighted
quotient `-v(x) / (x - E)`, and a nonzero `L²` point mode exists exactly when this
quotient belongs to `L²` and the source is nonzero almost everywhere.

This closes the local occurrence problem for arbitrary sources, subsuming the
fractional and critical-log threshold families.  It does not identify the literal
FZZ/GFZZ source map or supply the remaining global zeta-selective node law.

Tags: [NEW] [CLASSIFICATION] [UNIVERSAL BOUNDARY] [POSITIVE SURVIVOR]
-/

open Complex MeasureTheory Set
open scoped ENNReal

namespace RHTower
noncomputable section

/-- Canonical solution of the scalar weighted puncture equation at energy `E`. -/
def fzzPunctureWeightedResolventState (E : ℝ) (v : ℝ → ℂ) (x : ℝ) : ℂ :=
  -v x / ((x - E : ℝ) : ℂ)

/-- The scalar puncture equation together with the required `L²` state condition. -/
def fzzPunctureWeightedSourceEigenEquation
    (E : ℝ) (v f : ℝ → ℂ) : Prop :=
  MemLp f 2 volume ∧
    ∀ᵐ x : ℝ ∂volume,
      (((x - E : ℝ) : ℂ) * f x) + v x = 0

/-- The canonical weighted quotient solves the puncture equation almost everywhere. -/
theorem fzzPunctureWeightedResolventState_equation_ae (E : ℝ) (v : ℝ → ℂ) :
    ∀ᵐ x : ℝ ∂volume,
      (((x - E : ℝ) : ℂ) * fzzPunctureWeightedResolventState E v x) + v x = 0 := by
  filter_upwards [(volume : Measure ℝ).ae_ne E] with x hx
  have hcoef : (((x - E : ℝ) : ℂ)) ≠ 0 :=
    ofReal_ne_zero.mpr (sub_ne_zero.mpr hx)
  have hcoef' : (x : ℂ) - (E : ℂ) ≠ 0 := by
    simpa using hcoef
  unfold fzzPunctureWeightedResolventState
  push_cast
  field_simp
  ring

/-- Every `L²` solution equals the canonical weighted quotient almost everywhere. -/
theorem fzzPunctureWeightedSourceEigenEquation_state_unique
    (E : ℝ) (v f : ℝ → ℂ)
    (h : fzzPunctureWeightedSourceEigenEquation E v f) :
    f =ᵐ[volume] fzzPunctureWeightedResolventState E v := by
  filter_upwards [h.2, (volume : Measure ℝ).ae_ne E] with x hxeq hx
  have hcoef : (((x - E : ℝ) : ℂ)) ≠ 0 :=
    ofReal_ne_zero.mpr (sub_ne_zero.mpr hx)
  apply (eq_div_iff hcoef).2
  have hprod : (((x - E : ℝ) : ℂ)) * f x = -v x := by
    linear_combination hxeq
  simpa [fzzPunctureWeightedResolventState, mul_comm] using hprod

/-- The canonical state vanishes almost everywhere exactly when its source does. -/
theorem fzzPunctureWeightedResolventState_ae_zero_iff (E : ℝ) (v : ℝ → ℂ) :
    fzzPunctureWeightedResolventState E v =ᵐ[volume] (0 : ℝ → ℂ) ↔
      v =ᵐ[volume] (0 : ℝ → ℂ) := by
  constructor
  · intro hstate
    filter_upwards [hstate, (volume : Measure ℝ).ae_ne E] with x hxstate hx
    have hcoef : (((x - E : ℝ) : ℂ)) ≠ 0 :=
      ofReal_ne_zero.mpr (sub_ne_zero.mpr hx)
    have hcoef' : (x : ℂ) - (E : ℂ) ≠ 0 := by
      simpa using hcoef
    simp [fzzPunctureWeightedResolventState] at hxstate
    rcases hxstate with hv | hden
    · simpa using hv
    · exact (hcoef' hden).elim
  · intro hv
    filter_upwards [hv] with x hx
    simp [fzzPunctureWeightedResolventState, hx]

/-- Existence of a nonzero `L²` scalar puncture mode for source `v` at energy `E`. -/
def FZZPunctureWeightedSourcePointMode (E : ℝ) (v : ℝ → ℂ) : Prop :=
  ∃ f : ℝ → ℂ,
    fzzPunctureWeightedSourceEigenEquation E v f ∧
      ¬ f =ᵐ[volume] (0 : ℝ → ℂ)

/--
Universal weighted-source classification: a nonzero scalar puncture mode exists
exactly when the canonical quotient is `L²` and the source is nonzero a.e.
-/
theorem fzzPunctureWeightedSourcePointMode_iff (E : ℝ) (v : ℝ → ℂ) :
    FZZPunctureWeightedSourcePointMode E v ↔
      MemLp (fzzPunctureWeightedResolventState E v) 2 volume ∧
        ¬ v =ᵐ[volume] (0 : ℝ → ℂ) := by
  constructor
  · rintro ⟨f, heq, hf⟩
    have hstate := fzzPunctureWeightedSourceEigenEquation_state_unique E v f heq
    refine ⟨(memLp_congr_ae hstate).mp heq.1, ?_⟩
    intro hv
    apply hf
    exact hstate.trans ((fzzPunctureWeightedResolventState_ae_zero_iff E v).mpr hv)
  · rintro ⟨hmem, hv⟩
    refine ⟨fzzPunctureWeightedResolventState E v,
      ⟨hmem, fzzPunctureWeightedResolventState_equation_ae E v⟩, ?_⟩
    exact fun hzero => hv ((fzzPunctureWeightedResolventState_ae_zero_iff E v).mp hzero)

/-- Zero source never produces a nonzero scalar puncture mode. -/
theorem not_fzzPunctureWeightedSourcePointMode_zero (E : ℝ) :
    ¬ FZZPunctureWeightedSourcePointMode E (0 : ℝ → ℂ) := by
  rw [fzzPunctureWeightedSourcePointMode_iff]
  simp

/-- The universal classification recovers the fractional nodal threshold. -/
theorem fzzPunctureWeightedSourcePointMode_fractional_iff (alpha : ℝ) :
    FZZPunctureWeightedSourcePointMode 0 (fzzPunctureFractionalFormFactor alpha) ↔
      1 / 2 < alpha := by
  simpa [FZZPunctureWeightedSourcePointMode, fzzPunctureWeightedSourceEigenEquation,
    FZZPunctureFractionalPointMode, fzzPunctureFractionalEigenEquation] using
      fzzPunctureFractionalPointMode_iff alpha

/-- The universal classification recovers the critical logarithmic threshold. -/
theorem fzzPunctureWeightedSourcePointMode_criticalLog_iff (beta : ℝ) :
    FZZPunctureWeightedSourcePointMode 0 (fzzPunctureCriticalLogFormFactor beta) ↔
      1 / 2 < beta := by
  simpa [FZZPunctureWeightedSourcePointMode, fzzPunctureWeightedSourceEigenEquation,
    FZZPunctureCriticalLogPointMode, fzzPunctureCriticalLogEigenEquation] using
      fzzPunctureCriticalLogPointMode_iff beta

end
end RHTower
