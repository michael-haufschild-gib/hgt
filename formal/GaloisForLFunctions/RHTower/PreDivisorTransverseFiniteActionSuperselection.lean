import GaloisForLFunctions.RHTower.PreDivisorTransverseRamificationRoosTransgression

/-!
# Pointwise finite-action superselection for transverse Xi geometry

One ordinary-prime Euler--Fisher coordinate is already coefficient-faithful on the transverse
Gamma Bockstein.  This module identifies the exact pointwise finite-action sector: a fixed Xi
divisor copy admits a cofinally recurrent source-marked replay with finite total transverse action
if and only if its transverse dual-number arc is formally unramified, equivalently its derived
Roos class vanishes.  The terminal multiplicity jet remains nonzero throughout.

The statement is falsifiable at one off-line divisor.  Such a divisor forces every cofinally
recurrent source replay at every ordinary-prime coordinate to have nonsummable action.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Pointwise finite-action sector at one ordinary-prime source coordinate. -/
def XiTransverseFiniteActionSectorAt (n : ℕ) (q : XiZeroCopy) : Prop :=
  ∃ history : ℕ → RouteRTraceSequence × RouteRTraceSequence,
    Summable (fun j => collisionTransverseAction
      (routeRTraceCoordinateMarker n).toAddMonoidHom (history j)) ∧
    IsCofinalCollisionChargeRecurrent
      (routeRTraceCoordinateMarker n).toAddMonoidHom history
      (routeRPrimeGammaBocksteinSequence
        (primeDepthBVWoldXiCenteredRate q.1), 0)

/-- Finite-action recurrence at one source coordinate forces the selected Xi copy onto the wall. -/
theorem xiTransverseFiniteActionSectorAt_re_eq_half
    (n : ℕ) (q : XiZeroCopy)
    (hfinite : XiTransverseFiniteActionSectorAt n q) :
    (q.1 : ℂ).re = 1 / 2 := by
  obtain ⟨history, hsummable, hrecurrent⟩ := hfinite
  have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 := by
    by_contra hne
    exact no_routeRPrimeGammaBockstein_summableCoordinateReplay
      n hne history hsummable hrecurrent
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mp hrate

/-- A wall copy has the constant zero replay, so it belongs to the finite-action sector. -/
theorem xiTransverseFiniteActionSectorAt_of_re_eq_half
    (n : ℕ) (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    XiTransverseFiniteActionSectorAt n q := by
  let history : ℕ → RouteRTraceSequence × RouteRTraceSequence := fun _ => (0, 0)
  have hrate : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
    (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mpr hline
  refine ⟨history, ?_, ?_⟩
  · simp [history, collisionTransverseAction, collisionTransverseCharge]
  · intro ε hε N
    refine ⟨N, le_rfl, ?_⟩
    simp [history, hrate, collisionTransverseCharge,
      routeRPrimeGammaBocksteinSequence, hε]

/-- Exact pointwise selector: finite total action plus cofinal marked recurrence is the critical
line, at every ordinary-prime coordinate. -/
theorem xiTransverseFiniteActionSectorAt_iff_re_eq_half
    (n : ℕ) (q : XiZeroCopy) :
    XiTransverseFiniteActionSectorAt n q ↔ (q.1 : ℂ).re = 1 / 2 := by
  exact ⟨xiTransverseFiniteActionSectorAt_re_eq_half n q,
    xiTransverseFiniteActionSectorAt_of_re_eq_half n q⟩

/-- Finite-action superselection is exactly formal unramifiedness of the transverse arc. -/
theorem xiTransverseFiniteActionSectorAt_iff_formallyUnramified
    (n : ℕ) (q : XiZeroCopy) :
    XiTransverseFiniteActionSectorAt n q ↔
      Algebra.FormallyUnramified ℂ (PreDivisorTransverseArcAlgebra (q.1 : ℂ)) := by
  rw [xiTransverseFiniteActionSectorAt_iff_re_eq_half,
    preDivisorTransverseArcAlgebra_formallyUnramified_iff]

/-- Finite-action superselection is exactly derived Roos exactness. -/
theorem xiTransverseFiniteActionSectorAt_iff_derivedCompletionClass_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    XiTransverseFiniteActionSectorAt n q ↔
      preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) = 0 := by
  rw [xiTransverseFiniteActionSectorAt_iff_re_eq_half,
    preDivisorTransverseDerivedCompletionClass_eq_zero_iff]

/-- Protected two-sector law: multiplicity survives, while central holonomy, formal ramification,
derived completion, and finite-action source replay select one transverse neutral sector. -/
theorem xiProtectedMultiplicityFiniteActionSuperselection
    {m : ℕ} (hm : 2 ≤ m) (n : ℕ) (q : XiZeroCopy) :
    xiThetaTerminalMultiplicityCutJet q.1 0 ≠ 0 ∧
      (GaloisForLFunctions.IrregularStokes.centralHolonomyDefect m (q.1 : ℂ)
          (thetaInternalJetLeadingSourceCoefficient q.1) = 0 ↔
        XiTransverseFiniteActionSectorAt n q) ∧
      (Algebra.FormallyUnramified ℂ
          (PreDivisorTransverseArcAlgebra (q.1 : ℂ)) ↔
        XiTransverseFiniteActionSectorAt n q) ∧
      (preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) = 0 ↔
        XiTransverseFiniteActionSectorAt n q) := by
  refine ⟨xiThetaTerminalMultiplicityCutJet_ne_zero q.1 0, ?_, ?_, ?_⟩
  · exact (xiCentralHolonomyDefect_eq_zero_iff_transverseDerivedCompletionClass_eq_zero
      hm q).trans
        (xiTransverseFiniteActionSectorAt_iff_derivedCompletionClass_eq_zero n q).symm
  · exact (xiTransverseFiniteActionSectorAt_iff_formallyUnramified n q).symm
  · exact (xiTransverseFiniteActionSectorAt_iff_derivedCompletionClass_eq_zero n q).symm

/-- Exact falsifier: an off-line Xi copy makes every cofinally recurrent source replay have
nonsummable total transverse action at every ordinary-prime coordinate. -/
theorem xiOffLine_forces_nonsummable_transverseAction
    (n : ℕ) (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (history : ℕ → RouteRTraceSequence × RouteRTraceSequence)
    (hrecurrent : IsCofinalCollisionChargeRecurrent
      (routeRTraceCoordinateMarker n).toAddMonoidHom history
      (routeRPrimeGammaBocksteinSequence
        (primeDepthBVWoldXiCenteredRate q.1), 0)) :
    ¬ Summable (fun j => collisionTransverseAction
      (routeRTraceCoordinateMarker n).toAddMonoidHom (history j)) := by
  intro hsummable
  apply no_routeRPrimeGammaBockstein_summableCoordinateReplay
    n ((primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).not.mpr hoff)
    history hsummable hrecurrent

end

end RHTower
