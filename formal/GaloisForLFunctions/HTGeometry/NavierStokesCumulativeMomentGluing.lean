import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cumulative-moment gluing

Lemma 4.4 of the supplied Navier--Stokes paper joins two radial profiles at a
radius after matching five cumulative moments.  Its core is a general prefix
integral principle: equality at the join propagates to every later radius when
the integrands agree on the intervening tail.

This file proves that principle for normed-space-valued integrands and applies
it simultaneously to the five integrands `(U, H, UH, U²-E²/2, E²/(2X))` from
equation (4.15).
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesCumulativeMomentGluing

open MeasureTheory Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Prefix-integral equality propagates past a join where the integrands agree. -/
theorem intervalIntegral_prefix_eq_of_eqOn_tail
    {f g : ℝ → E} {join X : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hjoinX : join ≤ X)
    (hprefix : (∫ x in (0 : ℝ)..join, f x) = ∫ x in (0 : ℝ)..join, g x)
    (htail : Set.EqOn f g (Set.Icc join X)) :
    (∫ x in (0 : ℝ)..X, f x) = ∫ x in (0 : ℝ)..X, g x := by
  have htailIntegral : (∫ x in join..X, f x) = ∫ x in join..X, g x := by
    apply intervalIntegral.integral_congr
    simpa [Set.uIcc_of_le hjoinX] using htail
  calc
    (∫ x in (0 : ℝ)..X, f x) =
        (∫ x in (0 : ℝ)..join, f x) + ∫ x in join..X, f x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 join) (hf.intervalIntegrable join X)).symm
    _ = (∫ x in (0 : ℝ)..join, g x) + ∫ x in join..X, g x := by
      rw [hprefix, htailIntegral]
    _ = ∫ x in (0 : ℝ)..X, g x :=
      intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable 0 join) (hg.intervalIntegrable join X)

/-- The five cumulative radial moments from equation (4.15). -/
inductive RadialMomentKind
  | mass
  | angular
  | mixed
  | energy
  | pressure
  deriving DecidableEq, Fintype

/-- Pair of axial and azimuthal profiles used by the cumulative moments. -/
structure RadialProfile where
  U : ℝ → ℝ
  E : ℝ → ℝ

/-- Integrands `(U, H, UH, U²-E²/2, E²/(2X))` from equation (4.15). -/
def radialMomentIntegrand (profile : RadialProfile) : RadialMomentKind → ℝ → ℝ
  | .mass, x => profile.U x
  | .angular, x => Real.sqrt (2 * x) * profile.E x
  | .mixed, x => profile.U x * (Real.sqrt (2 * x) * profile.E x)
  | .energy, x => profile.U x ^ (2 : ℕ) - profile.E x ^ (2 : ℕ) / 2
  | .pressure, x => profile.E x ^ (2 : ℕ) / (2 * x)

/-- Cumulative radial moment based at the cylindrical axis. -/
def cumulativeRadialMoment (profile : RadialProfile) (kind : RadialMomentKind) (X : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..X, radialMomentIntegrand profile kind x

theorem radialMomentIntegrand_eqOn_of_profile_eqOn
    {first second : RadialProfile} {s : Set ℝ} (kind : RadialMomentKind)
    (hU : Set.EqOn first.U second.U s) (hE : Set.EqOn first.E second.E s) :
    Set.EqOn (radialMomentIntegrand first kind) (radialMomentIntegrand second kind) s := by
  intro x hx
  cases kind <;> simp [radialMomentIntegrand, hU hx, hE hx]

/-- Five-moment preservation core of Lemma 4.4. -/
theorem cumulativeRadialMoments_eq_of_profile_gluing
    {first second : RadialProfile} {join X : ℝ} (hjoinX : join ≤ X)
    (hcontinuousFirst : ∀ kind, Continuous (radialMomentIntegrand first kind))
    (hcontinuousSecond : ∀ kind, Continuous (radialMomentIntegrand second kind))
    (hjoin : ∀ kind,
      cumulativeRadialMoment first kind join = cumulativeRadialMoment second kind join)
    (hU : Set.EqOn first.U second.U (Set.Icc join X))
    (hE : Set.EqOn first.E second.E (Set.Icc join X)) :
    ∀ kind, cumulativeRadialMoment first kind X = cumulativeRadialMoment second kind X := by
  intro kind
  exact intervalIntegral_prefix_eq_of_eqOn_tail
    (hcontinuousFirst kind) (hcontinuousSecond kind) hjoinX (hjoin kind)
      (radialMomentIntegrand_eqOn_of_profile_eqOn kind hU hE)

end

end GaloisForLFunctions.HTGeometry.NavierStokesCumulativeMomentGluing
