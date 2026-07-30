import GaloisForLFunctions.RHTower.XiHeightAdaptiveAdjacentCensusCollision
import GaloisForLFunctions.RHTower.XiHedenmalmKummerCollision

/-!
# Height-adaptive Hedenmalm adjacent-census collision

At every zero of `XiC` of order `m`, the source-defined Hedenmalm function

`E_Xi = XiC + I * XiC'`

has order exactly `m - 1`.  Summing this local relation over a bounded right-half Xi box turns
the Hedenmalm common-divisor census into the predecessor census already used by the sharp-prime
adjacent-collision theorem.

Consequently the common Kummer-root hypothesis can be weakened drastically: at every positive
integer height it is enough to know one dyadic congruence between the Xi divisor census and the
Hedenmalm common-divisor census, at a modulus above the unconditional zero-count envelope.  Their
difference is the number of distinct right-half zeros, so the box must be empty.

The result is a top-down reduction.  It proves no source boundary congruence and assumes no
analytic root, RH ladder, zero simplicity, or zero enumeration.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- Affine centering preserves analytic order between `xi` and `XiC`. -/
theorem analyticOrderAt_XiC_centeredCoordinate (z : ℂ) :
    analyticOrderAt XiC ((z - 1 / 2) * (-I)) = analyticOrderAt xi z := by
  let a : ℂ := (z - 1 / 2) * (-I)
  let g : ℂ → ℂ := fun w => 1 / 2 + w * I
  have hga : g a = z := by
    dsimp only [g, a]
    have hI : (-I) * I = (1 : ℂ) := by
      rw [neg_mul, I_mul_I]
      ring
    rw [mul_assoc, hI, mul_one]
    ring
  have hgAnalytic : AnalyticAt ℂ g a := by
    dsimp only [g]
    fun_prop
  have hgDeriv : deriv g a ≠ 0 := by
    have hg' : HasDerivAt g I a := by
      dsimp only [g]
      convert (hasDerivAt_const (x := a) (c := (1 / 2 : ℂ))).add
        ((hasDerivAt_id a).mul_const I) using 1
      all_goals try rfl
      all_goals ring
    rw [hg'.deriv]
    exact I_ne_zero
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := xi) hgAnalytic hgDeriv
  rw [show XiC = xi ∘ g by rfl, hcomp, hga]

/-- On a right-half Xi box fibre, `E_Xi` has exactly the predecessor of the Xi multiplicity. -/
theorem xiHedenmalm_order_eq_pred_of_mem_boxFinset
    {T : ℝ} {z : ℂ} (hz : z ∈ boxFinset T) :
    (analyticOrderAt xiHedenmalmDeBrangesE
        ((z - 1 / 2) * (-I))).toNat =
      (analyticOrderAt xi z).toNat - 1 := by
  have hzbox := mem_boxFinset.mp hz
  let support : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hzbox.2⟩
  have hpos := xi_divisor_pos_on_support support
  have hn : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (support : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨support, ⟨0, hn⟩⟩
  have hzero : XiC ((z - 1 / 2) * (-I)) = 0 := by
    simpa [q, support, xiSpectralPoint] using
      XiC_xiSpectralPoint_eq_zero q
  obtain ⟨k, hXiOrder, hEOrder⟩ :=
    analyticOrderAt_xiHedenmalmDeBrangesE_eq_pred_of_XiC_zero hzero
  have hbridge := analyticOrderAt_XiC_centeredCoordinate z
  have hXiNat : (analyticOrderAt xi z).toNat = k + 1 := by
    rw [← hbridge, hXiOrder]
    rfl
  have hENat :
      (analyticOrderAt xiHedenmalmDeBrangesE
        ((z - 1 / 2) * (-I))).toNat = k := by
    rw [hEOrder]
    rfl
  rw [hENat, hXiNat]
  omega

/-- The common-divisor order of `XiC` and `E_Xi`, read over the right-half Xi box. -/
def boxHedenmalmCommonOrderSum (T : ℝ) : ℕ :=
  (boxFinset T).sum fun z =>
    (analyticOrderAt xiHedenmalmDeBrangesE
      ((z - 1 / 2) * (-I))).toNat

/-- The Hedenmalm common-divisor census is exactly the predecessor-order census. -/
theorem boxHedenmalmCommonOrderSum_eq_pred (T : ℝ) :
    boxHedenmalmCommonOrderSum T = boxPredOrderSum T := by
  apply Finset.sum_congr rfl
  intro z hz
  exact xiHedenmalm_order_eq_pred_of_mem_boxFinset hz

/-- The Hedenmalm common-divisor order reduced modulo the height-adapted dyadic modulus. -/
def hedenmalmCommonCensusH (k : ℕ) (T : ℝ) : ZMod (2 ^ k) :=
  (boxHedenmalmCommonOrderSum T : ZMod (2 ^ k))

theorem hedenmalmCommonCensusH_eq_pred (k : ℕ) (T : ℝ) :
    hedenmalmCommonCensusH k T = predDiscCensusH k T := by
  rw [hedenmalmCommonCensusH, predDiscCensusH,
    boxHedenmalmCommonOrderSum_eq_pred]

/-- At every integer height, one sufficiently deep dyadic congruence between the Xi census and
the common-divisor census of the source-defined pair `(XiC, E_Xi)`. -/
def XiNatHeightAdaptiveHedenmalmAdjacentCensus (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ,
      C * (1 + ((n : ℝ) + 2)) * Real.log (2 + ((n : ℝ) + 2)) <
        (2 ^ k : ℕ) ∧
      discCensusH k (n : ℝ) = hedenmalmCommonCensusH k (n : ℝ)

/-- The Hedenmalm census condition supplies the generic predecessor-census collision. -/
theorem xiNatHeightAdaptiveAdjacentCensus_of_hedenmalm
    {C : ℝ} (h : XiNatHeightAdaptiveHedenmalmAdjacentCensus C) :
    XiNatHeightAdaptiveAdjacentCensus C := by
  intro n hn
  obtain ⟨k, hk, hcensus⟩ := h n hn
  refine ⟨k, hk, ?_⟩
  calc
    discCensusH k (n : ℝ) = hedenmalmCommonCensusH k (n : ℝ) := hcensus
    _ = predDiscCensusH k (n : ℝ) := hedenmalmCommonCensusH_eq_pred k (n : ℝ)
    _ = cancelledSourceCommonCensusH k (n : ℝ) :=
      (cancelledSourceCommonCensusH_eq_pred k (n : ℝ)).symm

/-- **Height-adaptive Hedenmalm adjacent-census chain to RH.**  No common Kummer root or
multiplicity ladder is required. -/
theorem riemannHypothesis_of_xiNatHeightAdaptiveHedenmalmAdjacentCensus
    (h : XiNatHeightAdaptiveHedenmalmAdjacentCensus
      xiZeroCountEnvelopeConstant) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiNatHeightAdaptiveAdjacentCensus
    (xiNatHeightAdaptiveAdjacentCensus_of_hedenmalm h)

end

end RHTower
