import GaloisForLFunctions.RHTower.XiHeightAdaptiveHedenmalmCensusCollision
import GaloisForLFunctions.RHTower.XiHeightAdaptiveLinearQuadraticCensusCollision

/-!
# Exact closure of the height-adaptive Xi interfaces

The height-adaptive ladder, regional Kummer-root, and divisor-census hypotheses were introduced as
sufficient conditions for RH.  Their converse directions are forced by the existing corpus:

* RH makes every right-half divisor ladder vacuous;
* the global analytic roots supplied by `rhLadder_iff_root` restrict to every regional root window;
* RH empties every right-half box, so each linear, quadratic, predecessor, cancelled-source, and
  Hedenmalm census is zero.

Consequently every interface at the canonical unconditional zero-count envelope is exactly
equivalent to RH.  More generally, the equivalences hold for any constant satisfying the displayed
Xi zero-count bound.  The linear--quadratic route is classified with its necessary first ladder
rung as a paired interface.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-! ## Converse constructions under RH -/

/-- Every real threshold is strictly dominated by a dyadic natural number. -/
theorem exists_nat_two_pow_gt_real (x : ℝ) :
    ∃ k : ℕ, x < ((2 ^ k : ℕ) : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_gt x
  refine ⟨k, hk.trans ?_⟩
  exact_mod_cast Nat.lt_two_pow_self

/-- Under RH, every height-adaptive regional divisor ladder holds, independently of the proposed
envelope constant. -/
theorem xiHeightAdaptiveDiscLadder_of_riemannHypothesis
    (C : ℝ) (hRH : RiemannHypothesis) :
    XiHeightAdaptiveDiscLadder C := by
  intro r _hr
  obtain ⟨k, hk⟩ :=
    exists_nat_two_pow_gt_real (C * (1 + r) * Real.log (2 + r))
  refine ⟨k, hk, ?_⟩
  intro ρ hρ _hρball hzero
  exact absurd hzero ((rh_iff_xi_ne_zero_right.mp hRH) ρ hρ)

/-- Under RH, the global depth-`k` analytic Kummer root restricts to any regional root window. -/
theorem xiDiscKummerRoot_of_riemannHypothesis
    (k : ℕ) (r : ℝ) (hRH : RiemannHypothesis) :
    XiDiscKummerRoot k r := by
  obtain ⟨g, hg, hpow⟩ :=
    (rhLadder_iff_root k).mp ((rh_iff_forall_ladder.mp hRH) k)
  refine ⟨g, hg.mono ?_, ?_⟩
  · intro z hz
    exact hz.1
  · intro z hz
    exact hpow z hz.1

/-- Under RH, the global dyadic Kummer root at a chosen depth restricts to every regional root
window.  Thus every height-adaptive regional-root interface is inhabited. -/
theorem xiHeightAdaptiveDiscKummerRoots_of_riemannHypothesis
    (C : ℝ) (hRH : RiemannHypothesis) :
    XiHeightAdaptiveDiscKummerRoots C := by
  intro r _hr
  obtain ⟨k, hk⟩ :=
    exists_nat_two_pow_gt_real (C * (1 + r) * Real.log (2 + r))
  exact ⟨k, hk, xiDiscKummerRoot_of_riemannHypothesis k r hRH⟩

/-- RH supplies the countable integer-disc version of the regional Kummer-root interface. -/
theorem xiNatHeightAdaptiveDiscKummerRoots_of_riemannHypothesis
    (C : ℝ) (hRH : RiemannHypothesis) :
    XiNatHeightAdaptiveDiscKummerRoots C := by
  intro n hn
  exact xiHeightAdaptiveDiscKummerRoots_of_riemannHypothesis C hRH
    (n : ℝ) (by exact_mod_cast hn)

/-- RH empties every box, so every height-adaptive linear divisor census vanishes. -/
theorem xiNatHeightAdaptiveBoxCensus_of_riemannHypothesis
    (C : ℝ) (hRH : RiemannHypothesis) :
    XiNatHeightAdaptiveBoxCensus C := by
  intro n _hn
  obtain ⟨k, hk⟩ := exists_nat_two_pow_gt_real
    (C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2)))
  have hsum : boxOrderSum (n : ℝ) = 0 :=
    (boxOrderSum_eq_zero_iff_boxZeros_empty _).2
      ((rh_iff_forall_boxZeros_empty.mp hRH) _)
  refine ⟨k, hk, ?_⟩
  simp [discCensusH, hsum]

/-- RH makes both terms of the cancelled-source adjacent census zero. -/
theorem xiNatHeightAdaptiveAdjacentCensus_of_riemannHypothesis
    (C : ℝ) (hRH : RiemannHypothesis) :
    XiNatHeightAdaptiveAdjacentCensus C := by
  intro n _hn
  obtain ⟨k, hk⟩ := exists_nat_two_pow_gt_real
    (C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2)))
  have hsum : boxOrderSum (n : ℝ) = 0 :=
    (boxOrderSum_eq_zero_iff_boxZeros_empty _).2
      ((rh_iff_forall_boxZeros_empty.mp hRH) _)
  have hpred : boxPredOrderSum (n : ℝ) = 0 := by
    have hdecomp := boxOrderSum_eq_pred_add_distinct (n : ℝ)
    omega
  refine ⟨k, hk, ?_⟩
  rw [cancelledSourceCommonCensusH_eq_pred, discCensusH, predDiscCensusH,
    hsum, hpred]

/-- RH makes both terms of the Hedenmalm adjacent census zero. -/
theorem xiNatHeightAdaptiveHedenmalmAdjacentCensus_of_riemannHypothesis
    (C : ℝ) (hRH : RiemannHypothesis) :
    XiNatHeightAdaptiveHedenmalmAdjacentCensus C := by
  intro n _hn
  obtain ⟨k, hk⟩ := exists_nat_two_pow_gt_real
    (C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2)))
  have hsum : boxOrderSum (n : ℝ) = 0 :=
    (boxOrderSum_eq_zero_iff_boxZeros_empty _).2
      ((rh_iff_forall_boxZeros_empty.mp hRH) _)
  have hpred : boxPredOrderSum (n : ℝ) = 0 := by
    have hdecomp := boxOrderSum_eq_pred_add_distinct (n : ℝ)
    omega
  refine ⟨k, hk, ?_⟩
  rw [hedenmalmCommonCensusH_eq_pred, discCensusH, predDiscCensusH,
    hsum, hpred]

/-- RH makes both the linear and quadratic box censuses zero. -/
theorem xiNatHeightAdaptiveLinearQuadraticCensus_of_riemannHypothesis
    (C : ℝ) (hRH : RiemannHypothesis) :
    XiNatHeightAdaptiveLinearQuadraticCensus C := by
  intro n _hn
  obtain ⟨k, hk⟩ := exists_nat_two_pow_gt_real
    ((C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2))) ^ 2)
  have hsum : boxOrderSum (n : ℝ) = 0 :=
    (boxOrderSum_eq_zero_iff_boxZeros_empty _).2
      ((rh_iff_forall_boxZeros_empty.mp hRH) _)
  have hsquare : boxSquareOrderSum (n : ℝ) = 0 := by
    have hle := boxSquareOrderSum_le_sq_boxOrderSum (n : ℝ)
    rw [hsum] at hle
    exact Nat.eq_zero_of_le_zero (by simpa using hle)
  refine ⟨k, hk, ?_⟩
  rw [quadraticDiscCensusH, discCensusH, hsquare, hsum]

/-! ## Exact classifications for an arbitrary valid zero-count envelope -/

/-- For any valid Xi zero-count envelope, its height-adaptive regional divisor ladder is
equivalent to RH. -/
theorem xiHeightAdaptiveDiscLadder_iff_riemannHypothesis_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r)) :
    XiHeightAdaptiveDiscLadder C ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiHeightAdaptiveDiscLadder_of_zeroCountBound hcount,
    xiHeightAdaptiveDiscLadder_of_riemannHypothesis C⟩

/-- For any valid Xi zero-count envelope, the regional Kummer-root interface is equivalent to RH. -/
theorem xiHeightAdaptiveDiscKummerRoots_iff_riemannHypothesis_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r)) :
    XiHeightAdaptiveDiscKummerRoots C ↔ RiemannHypothesis := by
  constructor
  · intro hroots
    exact riemannHypothesis_of_xiHeightAdaptiveDiscLadder_of_zeroCountBound hcount
      (xiHeightAdaptiveDiscLadder_of_kummerRoots hroots)
  · exact xiHeightAdaptiveDiscKummerRoots_of_riemannHypothesis C

/-- For any valid Xi zero-count envelope, the integer-disc Kummer-root interface is equivalent to
RH. -/
theorem xiNatHeightAdaptiveDiscKummerRoots_iff_riemannHypothesis_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r)) :
    XiNatHeightAdaptiveDiscKummerRoots C ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiNatHeightAdaptiveDiscKummerRoots_of_zeroCountBound hcount,
    xiNatHeightAdaptiveDiscKummerRoots_of_riemannHypothesis C⟩

/-- For any valid Xi zero-count envelope, the height-adaptive linear box census is equivalent to
RH. -/
theorem xiNatHeightAdaptiveBoxCensus_iff_riemannHypothesis_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r)) :
    XiNatHeightAdaptiveBoxCensus C ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiNatHeightAdaptiveBoxCensus_of_zeroCountBound hcount,
    xiNatHeightAdaptiveBoxCensus_of_riemannHypothesis C⟩

/-- For any valid Xi zero-count envelope, the cancelled-source adjacent census is equivalent to
RH. -/
theorem xiNatHeightAdaptiveAdjacentCensus_iff_riemannHypothesis_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r)) :
    XiNatHeightAdaptiveAdjacentCensus C ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiNatHeightAdaptiveAdjacentCensus_of_zeroCountBound hcount,
    xiNatHeightAdaptiveAdjacentCensus_of_riemannHypothesis C⟩

/-- For any valid Xi zero-count envelope, the Hedenmalm adjacent census is equivalent to RH. -/
theorem xiNatHeightAdaptiveHedenmalmAdjacentCensus_iff_riemannHypothesis_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r)) :
    XiNatHeightAdaptiveHedenmalmAdjacentCensus C ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_xiNatHeightAdaptiveAdjacentCensus_of_zeroCountBound hcount
      (xiNatHeightAdaptiveAdjacentCensus_of_hedenmalm h)
  · exact xiNatHeightAdaptiveHedenmalmAdjacentCensus_of_riemannHypothesis C

/-- The linear--quadratic census together with the first divisor rung is exactly RH for every
valid Xi zero-count envelope. -/
theorem xiNatHeightAdaptiveLinearQuadraticCensus_and_rhLadder_one_iff_riemannHypothesis_of_zeroCountBound
    {C : ℝ}
    (hcount : ∀ r : ℝ, 1 ≤ r →
      ((xiBallOrderSum (2 : ℂ) r : ℤ) : ℝ) ≤
        C * (1 + r) * Real.log (2 + r)) :
    (XiNatHeightAdaptiveLinearQuadraticCensus C ∧ RHLadder 1) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hcensus, hladder⟩
    exact
      riemannHypothesis_of_rhLadder_one_of_xiNatHeightAdaptiveLinearQuadraticCensus_of_zeroCountBound
        hcount hcensus hladder
  · intro hRH
    exact ⟨xiNatHeightAdaptiveLinearQuadraticCensus_of_riemannHypothesis C hRH,
      (rh_iff_forall_ladder.mp hRH) 1⟩

/-! ## Canonical unconditional-envelope equivalences -/

theorem xiHeightAdaptiveDiscLadder_iff_riemannHypothesis :
    XiHeightAdaptiveDiscLadder xiZeroCountEnvelopeConstant ↔ RiemannHypothesis :=
  xiHeightAdaptiveDiscLadder_iff_riemannHypothesis_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope

theorem xiHeightAdaptiveDiscKummerRoots_iff_riemannHypothesis :
    XiHeightAdaptiveDiscKummerRoots xiZeroCountEnvelopeConstant ↔ RiemannHypothesis :=
  xiHeightAdaptiveDiscKummerRoots_iff_riemannHypothesis_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope

theorem xiNatHeightAdaptiveDiscKummerRoots_iff_riemannHypothesis :
    XiNatHeightAdaptiveDiscKummerRoots xiZeroCountEnvelopeConstant ↔ RiemannHypothesis :=
  xiNatHeightAdaptiveDiscKummerRoots_iff_riemannHypothesis_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope

theorem xiNatHeightAdaptiveBoxCensus_iff_riemannHypothesis :
    XiNatHeightAdaptiveBoxCensus xiZeroCountEnvelopeConstant ↔ RiemannHypothesis :=
  xiNatHeightAdaptiveBoxCensus_iff_riemannHypothesis_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope

theorem xiNatHeightAdaptiveAdjacentCensus_iff_riemannHypothesis :
    XiNatHeightAdaptiveAdjacentCensus xiZeroCountEnvelopeConstant ↔ RiemannHypothesis :=
  xiNatHeightAdaptiveAdjacentCensus_iff_riemannHypothesis_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope

theorem xiNatHeightAdaptiveHedenmalmAdjacentCensus_iff_riemannHypothesis :
    XiNatHeightAdaptiveHedenmalmAdjacentCensus xiZeroCountEnvelopeConstant ↔
      RiemannHypothesis :=
  xiNatHeightAdaptiveHedenmalmAdjacentCensus_iff_riemannHypothesis_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope

theorem xiNatHeightAdaptiveLinearQuadraticCensus_and_rhLadder_one_iff_riemannHypothesis :
    (XiNatHeightAdaptiveLinearQuadraticCensus xiZeroCountEnvelopeConstant ∧
      RHLadder 1) ↔ RiemannHypothesis :=
  xiNatHeightAdaptiveLinearQuadraticCensus_and_rhLadder_one_iff_riemannHypothesis_of_zeroCountBound
    xiBallOrderSum_le_zeroCountEnvelope

end

end RHTower
