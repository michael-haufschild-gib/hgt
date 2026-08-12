import GaloisForLFunctions.HTGeometry.HausdorffQuadratureWeights

/-!
# The Hausdorff quadrature measures

The level-`N` weights, carried by the nodes `k/N`, assemble into a finite positive measure on the
unit interval of total mass `b 0`.  Its moments are the weighted node powers, and the exact
falling-factorial identity of the weight layer says that the *falling-factorial* moments are exactly
`b m`.  The elementary comparison between `(k/N)^m` and `(k)_m/(N)_m` then makes the ordinary
moments converge to `b m`.
-/

open MeasureTheory Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Integration against a finite weighted Dirac family -/

/-- Integration against a finite weighted Dirac family on any measurable space with measurable
singletons. -/
theorem integral_finsetWeightedDirac_general {ι X E : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (t : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ t, 0 ≤ w i) (x : ι → X) (f : X → E) :
    ∫ y, f y ∂(∑ i ∈ t, ENNReal.ofReal (w i) • Measure.dirac (x i))
      = ∑ i ∈ t, w i • f (x i) := by
  classical
  have hint : ∀ i ∈ t, Integrable f (ENNReal.ofReal (w i) • Measure.dirac (x i)) := by
    intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)
  rw [integral_finsetSum_measure hint]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i hi)]

/-! ## The nodes -/

/-- The level-`N` quadrature node `k/N`, clamped into the unit interval. -/
def hausdorffNode (N k : ℕ) : HausdorffSourceSpace :=
  ⟨max 0 (min 1 ((k : ℝ) / (N : ℝ))),
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

theorem hausdorffNode_coe {N k : ℕ} (hk : k ≤ N) :
    ((hausdorffNode N k : HausdorffSourceSpace) : ℝ) = (k : ℝ) / (N : ℝ) := by
  have hdiv : (0 : ℝ) ≤ (k : ℝ) / (N : ℝ) := by positivity
  have hle : (k : ℝ) / (N : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp
    · rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast hk
  show max 0 (min 1 ((k : ℝ) / (N : ℝ))) = (k : ℝ) / (N : ℝ)
  rw [min_eq_right hle, max_eq_right hdiv]

/-! ## The measures -/

/-- The level-`N` Hausdorff quadrature measure. -/
def hausdorffQuadrature (b : ℕ → ℝ) (N : ℕ) : Measure HausdorffSourceSpace :=
  ∑ k ∈ range (N + 1),
    ENNReal.ofReal (hausdorffWeight b N k) • Measure.dirac (hausdorffNode N k)

instance (b : ℕ → ℝ) (N : ℕ) : IsFiniteMeasure (hausdorffQuadrature b N) := by
  refine ⟨?_⟩
  rw [hausdorffQuadrature, Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.mpr fun k _ => ?_
  simp [ENNReal.ofReal_lt_top]

/-- **Integration against the level-`N` quadrature.** -/
theorem integral_hausdorffQuadrature {b : ℕ → ℝ} (hb : HausdorffCompletelyMonotone b) (N : ℕ)
    (f : HausdorffSourceSpace → ℝ) :
    ∫ y, f y ∂(hausdorffQuadrature b N)
      = ∑ k ∈ range (N + 1), hausdorffWeight b N k * f (hausdorffNode N k) := by
  rw [hausdorffQuadrature,
    integral_finsetWeightedDirac_general _ _ (fun k _ => hausdorffWeight_nonneg hb N k) _ f]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- **The total mass of every level is `b 0`.** -/
theorem hausdorffQuadrature_mass {b : ℕ → ℝ} (hb : HausdorffCompletelyMonotone b) (N : ℕ) :
    ∫ _y, (1 : ℝ) ∂(hausdorffQuadrature b N) = b 0 := by
  rw [integral_hausdorffQuadrature hb N]
  simpa using sum_hausdorffWeight b N

/-- **The moments of the level-`N` quadrature are the weighted node powers.** -/
theorem hausdorffMoment_hausdorffQuadrature {b : ℕ → ℝ} (hb : HausdorffCompletelyMonotone b)
    (N m : ℕ) :
    hausdorffMoment (hausdorffQuadrature b N) m
      = ∑ k ∈ range (N + 1),
          hausdorffWeight b N k * ((hausdorffNode N k : HausdorffSourceSpace) : ℝ) ^ m := by
  rw [hausdorffMoment, integral_hausdorffQuadrature hb N]

end

end GaloisForLFunctions.HTGeometry
