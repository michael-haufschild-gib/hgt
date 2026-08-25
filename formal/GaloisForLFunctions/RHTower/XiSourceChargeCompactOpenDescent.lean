import GaloisForLFunctions.RHTower.XiSourceMatchedChargedBubble

/-!
# Source charge does not descend through compact-open continuation

The completed entire function forgets arithmetic provenance at the noncompact height boundary.
This file makes that statement exact.  A canonical source-matched bubble attached to an off-line
Xi divisor converges locally uniformly back to Xi, while retaining the divisor's nonzero absolute
Noether charge.  Therefore no scalar reporter can be both compact-open sequentially continuous
and exactly source-charge faithful on that bubble.

Globally, existence of one compact-open continuous scalar reporter representing every canonical
divisor charge is equivalent to RH.  This is a topology theorem, not an RH proof: it rules out
ordinary compact-open entire-function topology as the carrier of the missing arithmetic law.
Any producer must retain a stronger proper/source-marked topology or use a nonscalar singular
object whose boundary value is not forced through compact-open scalar descent.
-/

open Complex Filter MeasureTheory Real Set
open scoped Differential Topology

namespace RHTower

noncomputable section

/-- A scalar reporter continuous for locally uniform convergence of entire sources. -/
def CompactOpenSequentialReporter (Q : (ℂ → ℂ) → ℝ) : Prop :=
  ∀ (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    TendstoLocallyUniformly F f atTop →
      Tendsto (fun n => Q (F n)) atTop (nhds (Q f))

/-- Canonical multiplicity-matched bubble sequence attached to one Xi divisor point. -/
def xiSourceMatchedBubble (rho : XiDivisorSupport) (n : ℕ) : ℂ → ℂ :=
  multiplicityEscapingQuartetGaugedXi
    (xiDivisorBubbleDisplacement rho)
    (analyticOrderAt xi (rho : ℂ)).toNat n

/-- Exact source charge is represented by one compact-open reporter on all canonical bubbles. -/
def XiSourceChargeCompactOpenDescent : Prop :=
  ∃ Q : (ℂ → ℂ) → ℝ,
    CompactOpenSequentialReporter Q ∧
      Q xi = 0 ∧
      ∀ (rho : XiDivisorSupport) (n : ℕ),
        Q (xiSourceMatchedBubble rho n) =
          |routeRPrimeGammaXiNoetherOrientationCharge rho|

/-- Off-line source-matched bubbles converge locally uniformly back to Xi. -/
theorem xiSourceMatchedBubble_tendstoLocallyUniformly
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    TendstoLocallyUniformly (xiSourceMatchedBubble rho) xi atTop := by
  have h := (offLineXiDivisor_sourceMatchedChargedBubble rho hoff).2.2.1 0
  change TendstoLocallyUniformly
    (fun n => multiplicityEscapingQuartetGaugedXi
      (xiDivisorBubbleDisplacement rho)
      (analyticOrderAt xi (rho : ℂ)).toNat n) xi atTop
  exact h

/-- Compact-open continuity and exact source-charge faithfulness are incompatible at an off-line
divisor.  Hence the charge cannot be a scalar continuous invariant of the completed entire
function alone. -/
theorem offLineXiDivisor_no_compactOpen_sourceChargeReporter
    (Q : (ℂ → ℂ) → ℝ) (hQ : CompactOpenSequentialReporter Q)
    (hXi : Q xi = 0) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ¬ ∀ n : ℕ, Q (xiSourceMatchedBubble rho n) =
      |routeRPrimeGammaXiNoetherOrientationCharge rho| := by
  intro hfaithful
  have htoXi : Tendsto (fun n => Q (xiSourceMatchedBubble rho n)) atTop (nhds (Q xi)) :=
    hQ _ _ (xiSourceMatchedBubble_tendstoLocallyUniformly rho hoff)
  have htoZero : Tendsto (fun n => Q (xiSourceMatchedBubble rho n)) atTop (nhds 0) := by
    simpa [hXi] using htoXi
  have htoCharge :
      Tendsto (fun n => Q (xiSourceMatchedBubble rho n)) atTop
        (nhds |routeRPrimeGammaXiNoetherOrientationCharge rho|) := by
    simpa only [hfaithful] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => |routeRPrimeGammaXiNoetherOrientationCharge rho|)
        atTop (nhds |routeRPrimeGammaXiNoetherOrientationCharge rho|))
  have hzeroAbs : |routeRPrimeGammaXiNoetherOrientationCharge rho| = 0 :=
    tendsto_nhds_unique htoCharge htoZero
  have hcharge : routeRPrimeGammaXiNoetherOrientationCharge rho = 0 :=
    abs_eq_zero.mp hzeroAbs
  exact hoff
    ((routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_re_eq_half rho).1 hcharge)

/-- Source Noether charge descends to compact-open entire-function topology exactly when RH
holds.  Under RH the zero reporter realizes the now-vanishing charge; off line the canonical
charged bubble contradicts uniqueness of limits in `ℝ`. -/
theorem xiSourceChargeCompactOpenDescent_iff_riemannHypothesis :
    XiSourceChargeCompactOpenDescent ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨Q, hQ, hXi, hfaithful⟩
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    let rho : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
    by_contra hoff
    exact offLineXiDivisor_no_compactOpen_sourceChargeReporter
      Q hQ hXi rho hoff (hfaithful rho)
  · intro hRH
    refine ⟨fun _ => 0, ?_, rfl, ?_⟩
    · intro F f hF
      exact tendsto_const_nhds
    · intro rho n
      simp only
      exact (abs_eq_zero.mpr
        ((routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_re_eq_half rho).2
          (xi_divisor_support_re_eq_half_of_rh hRH rho))).symm

end

end RHTower
