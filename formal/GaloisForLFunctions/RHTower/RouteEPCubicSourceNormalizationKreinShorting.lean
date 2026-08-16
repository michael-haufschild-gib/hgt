import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerBoundarySpectralShellNoGo
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaFiniteApertureHiddenBudget

/-!
# Route E/P source-normalization Krein shorting law

P-G102 closes every scalar resolvent channel of the current positive physical operator as a
producer of SP-E's amplitude-eight fourth-depth correction.  This file classifies the smallest
operator-changing alternative.

A positive parent pivot `w` can only subtract the cross square from depleted energy `w/64`, so no
positive Schur complement can restore `w`.  Replacing parent pivot by oriented polar pivot `-w`
reverses the sign of shorting correction.  Exact restoration then holds precisely when cross
coupling has square `(63/64)w²`.  Its unique nonnegative value is

```text
(sqrt 63 / 8) w.
```

At this coupling, two-channel block determinant is exactly `-w²`, hence strictly negative for
every literal primitive source weight.  One negative direction is therefore not optional
bookkeeping: it is exact algebraic price of coefficient-faithful normalization debt.  Naive full
cross `w` produces `65w/64`, exactly same value as uncorrected coefficient-faithful pair trace; the
required completion is its precise attenuation to `(sqrt 63 / 8)w`.  This gives a source-specific
construction target, not existence of required Gamma/co-Poisson cross term.

No RH premise, Xi-zero computation, numerical estimate, or added axiom enters.
-/

namespace RHTower

noncomputable section

/-- Fourth-depth energy after shorting through a positive parent pivot. -/
def routeEPCubicPositivePivotShortedFourthDepthEnergy (w cross : ℝ) : ℝ :=
  w / 64 - cross ^ 2 / w

/-- Fourth-depth energy after shorting through an oriented negative polar pivot. -/
def routeEPCubicPolarPivotShortedFourthDepthEnergy (w cross : ℝ) : ℝ :=
  w / 64 - cross ^ 2 / (-w)

/-- Unique nonnegative cross-coupling scale predicted by the `63/64` trace debt. -/
def routeEPCubicFourthDepthQuantizedPolarCross (w : ℝ) : ℝ :=
  Real.sqrt 63 / 8 * w

/-- Positive shorting only depletes the already contracted fourth-depth leg. -/
theorem routeEPCubicPositivePivotShortedFourthDepthEnergy_le
    (w cross : ℝ) (hw : 0 < w) :
    routeEPCubicPositivePivotShortedFourthDepthEnergy w cross ≤ w / 64 := by
  unfold routeEPCubicPositivePivotShortedFourthDepthEnergy
  have hnonneg : 0 ≤ cross ^ 2 / w := div_nonneg (sq_nonneg cross) hw.le
  linarith

/-- No positive-pivot Schur complement can restore the parent energy. -/
theorem routeEPCubicPositivePivotShortedFourthDepthEnergy_ne_parent
    (w cross : ℝ) (hw : 0 < w) :
    routeEPCubicPositivePivotShortedFourthDepthEnergy w cross ≠ w := by
  intro h
  have hle := routeEPCubicPositivePivotShortedFourthDepthEnergy_le w cross hw
  rw [h] at hle
  nlinarith

/-- Negative-pivot shorting restores the parent exactly iff cross square pays `63/64` debt. -/
theorem routeEPCubicPolarPivotShortedFourthDepthEnergy_eq_parent_iff
    (w cross : ℝ) (hw : 0 < w) :
    routeEPCubicPolarPivotShortedFourthDepthEnergy w cross = w ↔
      cross ^ 2 = 63 / 64 * w ^ 2 := by
  unfold routeEPCubicPolarPivotShortedFourthDepthEnergy
  constructor <;> intro h
  · field_simp [hw.ne'] at h
    nlinarith
  · field_simp [hw.ne']
    nlinarith

/-- The quantized polar cross has exactly debt-matching square. -/
theorem routeEPCubicFourthDepthQuantizedPolarCross_sq (w : ℝ) :
    routeEPCubicFourthDepthQuantizedPolarCross w ^ 2 =
      63 / 64 * w ^ 2 := by
  have hsqrt : Real.sqrt 63 ^ 2 = 63 := Real.sq_sqrt (by norm_num)
  unfold routeEPCubicFourthDepthQuantizedPolarCross
  nlinarith

/-- Quantized negative-pivot shorting restores full parent energy. -/
theorem routeEPCubicPolarPivotShortedFourthDepthEnergy_quantized
    (w : ℝ) (hw : 0 < w) :
    routeEPCubicPolarPivotShortedFourthDepthEnergy w
        (routeEPCubicFourthDepthQuantizedPolarCross w) = w := by
  exact
    (routeEPCubicPolarPivotShortedFourthDepthEnergy_eq_parent_iff w
      (routeEPCubicFourthDepthQuantizedPolarCross w) hw).2
        (routeEPCubicFourthDepthQuantizedPolarCross_sq w)

/-- Among nonnegative cross terms, debt-matching polar shorting has unique coupling. -/
theorem routeEPCubicFourthDepthQuantizedPolarCross_unique
    (w cross : ℝ) (hw : 0 < w) (hcross : 0 ≤ cross)
    (hshort : routeEPCubicPolarPivotShortedFourthDepthEnergy w cross = w) :
    cross = routeEPCubicFourthDepthQuantizedPolarCross w := by
  have hcrossSq :=
    (routeEPCubicPolarPivotShortedFourthDepthEnergy_eq_parent_iff w cross hw).1 hshort
  have hquantizedSq := routeEPCubicFourthDepthQuantizedPolarCross_sq w
  have hquantized : 0 ≤ routeEPCubicFourthDepthQuantizedPolarCross w := by
    unfold routeEPCubicFourthDepthQuantizedPolarCross
    positivity
  nlinarith

/-- Debt-matching two-channel block has determinant exactly `-w²`. -/
theorem routeEPCubicPolarBlockDet_quantized (w : ℝ) :
    (-w) * (w / 64) - routeEPCubicFourthDepthQuantizedPolarCross w ^ 2 =
      -w ^ 2 := by
  rw [routeEPCubicFourthDepthQuantizedPolarCross_sq]
  ring

/-- Using the full parent amplitude as polar cross overshoots balanced energy to `65w/64`. -/
theorem routeEPCubicPolarPivotShortedFourthDepthEnergy_fullCross
    (w : ℝ) (hw : w ≠ 0) :
    routeEPCubicPolarPivotShortedFourthDepthEnergy w w = 65 / 64 * w := by
  unfold routeEPCubicPolarPivotShortedFourthDepthEnergy
  field_simp [hw]
  ring

/-- Full polar cross reproduces, rather than repairs, coefficient-faithful pair trace `65w/64`.
This identifies exact attenuation from `w` to `(sqrt 63 / 8)w` that completion must supply. -/
theorem routePPrimitiveFourthDepth_sourceFaithful_pairTrace_eq_fullPolarShort
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveBaseCauchyCubicWeight pe +
        routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
          routePPrimitiveFourthDepthModularGain pe ^ 2 =
      routeEPCubicPolarPivotShortedFourthDepthEnergy
        (routePPrimitiveBaseCauchyCubicWeight pe)
        (routePPrimitiveBaseCauchyCubicWeight pe) := by
  rw [routePPrimitiveFourthDepth_sourceFaithful_pairTrace,
    routeEPCubicPolarPivotShortedFourthDepthEnergy_fullCross _
      (routePPrimitiveBaseCauchyCubicWeight_pos pe).ne']

/-- **P-G103 Krein shorting capstone.**  For every literal primitive source weight, positive
shorting cannot rebalance fourth depth, while unique nonnegative polar shorting does and forces a
strictly indefinite two-channel determinant. -/
theorem routePPrimitiveFourthDepth_sourceNormalizationKreinShorting_classification
    (pe : Nat.Primes × ℕ) :
    let w := routePPrimitiveBaseCauchyCubicWeight pe
    routeEPCubicPositivePivotShortedFourthDepthEnergy w 0 ≠ w ∧
      routeEPCubicPolarPivotShortedFourthDepthEnergy w
          (routeEPCubicFourthDepthQuantizedPolarCross w) = w ∧
      (-w) * (w / 64) - routeEPCubicFourthDepthQuantizedPolarCross w ^ 2 = -w ^ 2 ∧
      -w ^ 2 < 0 := by
  dsimp
  have hw := routePPrimitiveBaseCauchyCubicWeight_pos pe
  exact
    ⟨routeEPCubicPositivePivotShortedFourthDepthEnergy_ne_parent _ _ hw,
      routeEPCubicPolarPivotShortedFourthDepthEnergy_quantized _ hw,
      routeEPCubicPolarBlockDet_quantized _,
      neg_lt_zero.mpr (sq_pos_of_pos hw)⟩

end

end RHTower
