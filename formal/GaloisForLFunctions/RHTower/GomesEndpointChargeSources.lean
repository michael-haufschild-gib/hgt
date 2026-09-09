import GaloisForLFunctions.RHTower.GomesEndpointChargeFiniteness

/-!
# Actual measures of integer tensor charges

The scalar tensor character construction of arXiv:2509.25276v7 section 5.2 is now realized on
actual corpus measures. Tensoring is literal density reweighting and dual charges cancel back
to uniform volume, even when an intermediate measure has infinite mass. The finite charges
and their Clark realizations inherit the exact inequalities already proved for endpoint powers.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- The measure of any integer tensor charge, without concealing potentially infinite mass. -/
def gomesEndpointChargeMeasure (b : ℝ) (n : ℤ) : Measure HausdorffSourceSpace :=
  (gomesHausdorffUniformSource : Measure HausdorffSourceSpace).withDensity
    (fun y => ENNReal.ofReal (gomesEndpointTensorDensity b n y))

/-- Exact finiteness classification for the actual charge measure. -/
theorem gomesEndpointChargeMeasure_finite_iff (b : ℝ) (n : ℤ) :
    IsFiniteMeasure (gomesEndpointChargeMeasure b n) ↔ n ∈ gomesEndpointFiniteCharges b := by
  have h : Integrable (fun _ : HausdorffSourceSpace => (1 : ℝ)) (gomesEndpointChargeMeasure b n) ↔
      Integrable (gomesEndpointTensorDensity b n)
        (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
    change Integrable (fun _ : HausdorffSourceSpace => (1 : ℝ))
      ((gomesHausdorffUniformSource : Measure HausdorffSourceSpace).withDensity
        (fun y => ENNReal.ofReal (gomesEndpointTensorDensity b n y))) ↔ _
    dsimp only [gomesEndpointTensorDensity]
    rw [integrable_withDensity_iff_integrable_smul'
      (gomesClarkEndpointDensity_measurable ((n : ℝ) * b)).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (gomesClarkEndpointDensity_nonneg ((n : ℝ) * b) _),
      smul_eq_mul, mul_one]
  exact (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).symm.trans
    (h.trans (gomesEndpointFiniteCharges_mem_iff b n).symm)

/-- The nonadmissible half-lattice gives infinite total mass, including its threshold. -/
theorem gomesEndpointChargeMeasure_infinite_iff (b : ℝ) (n : ℤ) :
    gomesEndpointChargeMeasure b n Set.univ = ∞ ↔ (n : ℝ) * b ≤ -1 := by
  rw [← not_isFiniteMeasure_iff, gomesEndpointChargeMeasure_finite_iff]
  change ¬ (-1 < (n : ℝ) * b) ↔ _
  exact not_lt

/-- The neutral charge gives the uniform probability measure. -/
theorem gomesEndpointChargeMeasure_zero (b : ℝ) :
    gomesEndpointChargeMeasure b 0 = (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
  rw [gomesEndpointChargeMeasure, gomesEndpointTensorDensity_zero]
  simp only [Pi.one_apply, ENNReal.ofReal_one]
  exact withDensity_one

/-- Reweighting by another charged density realizes tensor addition on the actual measures. -/
theorem gomesEndpointChargeMeasure_tensor (b : ℝ) (m n : ℤ) :
    (gomesEndpointChargeMeasure b m).withDensity
      (fun y => ENNReal.ofReal (gomesEndpointTensorDensity b n y)) =
        gomesEndpointChargeMeasure b (m + n) := by
  rw [gomesEndpointChargeMeasure]
  dsimp only [gomesEndpointTensorDensity]
  rw [← withDensity_mul _
    (gomesClarkEndpointDensity_measurable ((m : ℝ) * b)).ennreal_ofReal
    (gomesClarkEndpointDensity_measurable ((n : ℝ) * b)).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [gomesEndpointTensorDensity_add_ae b m n] with y hy
  simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (gomesClarkEndpointDensity_nonneg ((m : ℝ) * b) y)]
  exact congrArg ENNReal.ofReal hy.symm

/-- Dual cancellation restores uniform volume even if an intermediate charged measure is infinite. -/
theorem gomesEndpointChargeMeasure_dual_cancel (b : ℝ) (n : ℤ) :
    (gomesEndpointChargeMeasure b n).withDensity
      (fun y => ENNReal.ofReal (gomesEndpointTensorDensity b (-n) y)) =
        (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) := by
  rw [gomesEndpointChargeMeasure_tensor, add_neg_cancel, gomesEndpointChargeMeasure_zero]

/-- Simultaneous finiteness of a measure and its dual is exactly the unit exponent window. -/
theorem gomesEndpointChargeMeasure_dual_finite_iff (b : ℝ) (n : ℤ) :
    (IsFiniteMeasure (gomesEndpointChargeMeasure b n) ∧
      IsFiniteMeasure (gomesEndpointChargeMeasure b (-n))) ↔ |(n : ℝ) * b| < 1 := by
  rw [gomesEndpointChargeMeasure_finite_iff, gomesEndpointChargeMeasure_finite_iff,
    gomesEndpointFiniteCharges_dual_pair]

/-- All actual charged measures are finite only for the trivial generating density. -/
theorem gomesEndpointChargeMeasure_all_finite_iff (b : ℝ) :
    (∀ n : ℤ, IsFiniteMeasure (gomesEndpointChargeMeasure b n)) ↔ b = 0 := by
  simp only [gomesEndpointChargeMeasure_finite_iff]
  exact gomesEndpointFiniteCharges_all_iff b

/-- Exact failure of finite-measure closure under literal tensor reweighting. -/
theorem gomesEndpointChargeMeasure_tensor_failure_iff (b : ℝ) :
    (∃ m n : ℤ, IsFiniteMeasure (gomesEndpointChargeMeasure b m) ∧
      IsFiniteMeasure (gomesEndpointChargeMeasure b n) ∧
      ¬ IsFiniteMeasure ((gomesEndpointChargeMeasure b m).withDensity
        (fun y => ENNReal.ofReal (gomesEndpointTensorDensity b n y)))) ↔ b ≠ 0 ∧ |b| < 1 := by
  simp only [gomesEndpointChargeMeasure_tensor, gomesEndpointChargeMeasure_finite_iff]
  exact gomesEndpointFiniteCharges_tensor_failure_iff b

/-- An admissible integer charge, packaged as data for the finite-source constructor. -/
abbrev GomesEndpointAdmissibleCharge (b : ℝ) := {n : ℤ // n ∈ gomesEndpointFiniteCharges b}

/-- The existing finite power source realizing an admissible charge. -/
def gomesEndpointChargeSource (b : ℝ) (n : GomesEndpointAdmissibleCharge b) :
    FiniteMeasure HausdorffSourceSpace :=
  gomesClarkEndpointPowerSource ⟨(n.val : ℝ) * b, n.property⟩

/-- The finite constructor is precisely the raw charged measure, with no alteration. -/
theorem gomesEndpointChargeSource_measure (b : ℝ) (n : GomesEndpointAdmissibleCharge b) :
    (gomesEndpointChargeSource b n : Measure HausdorffSourceSpace) =
      gomesEndpointChargeMeasure b n := rfl

/-- Every admissible charged source remains atom-free. -/
theorem gomesEndpointChargeSource_singleton (b : ℝ) (n : GomesEndpointAdmissibleCharge b)
    (y : HausdorffSourceSpace) :
    (gomesEndpointChargeSource b n : Measure HausdorffSourceSpace) {y} = 0 :=
  gomesClarkEndpointPowerSource_singleton _ y

/-- The collapsed anchor can realize exactly the strictly positive admissible charges. -/
theorem gomesEndpointChargeSource_collapsed_range_iff (b : ℝ) (n : GomesEndpointAdmissibleCharge b) :
    gomesEndpointChargeSource b n ∈ Set.range (gomesClarkWeightedSource 0) ↔ 0 < (n.val : ℝ) * b :=
  gomesClarkEndpointPowerSource_range_iff _

/-- Exact global realization boundary for every admissible charge and arbitrary real anchor. -/
theorem gomesEndpointChargeSource_anchor_realizable_iff (c b : ℝ) (n : GomesEndpointAdmissibleCharge b) :
    (∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkAnchorRecord c μ = gomesClarkReciprocalRecord (gomesEndpointChargeSource b n)) ↔
      c ≠ 0 ∨ 0 < (n.val : ℝ) * b :=
  gomesClarkEndpointPowerSource_anchor_realizable_iff c _

/-- The same charge boundary is already forced by arbitrarily local observation data. -/
theorem gomesEndpointChargeSource_local_realizable_iff (r : Set.Ioc (0 : ℝ) 1) (c b : ℝ)
    (n : GomesEndpointAdmissibleCharge b) :
    (∃ μ : FiniteMeasure HausdorffSourceSpace,
      gomesClarkGerm r (gomesClarkAnchorRecord c μ) =
        gomesClarkGerm r (gomesClarkReciprocalRecord (gomesEndpointChargeSource b n))) ↔
      c ≠ 0 ∨ 0 < (n.val : ℝ) * b :=
  gomesClarkEndpointPowerSource_local_anchor_realizable_iff r c _

/-- Finiteness of every actual measure in a symmetric charge window has the exact same budget. -/
theorem gomesEndpointChargeMeasure_window_finite_iff (b : ℝ) (N : ℕ) :
    (∀ n : ℤ, |n| ≤ (N : ℤ) → IsFiniteMeasure (gomesEndpointChargeMeasure b n)) ↔
      (N : ℝ) * |b| < 1 := by
  simp only [gomesEndpointChargeMeasure_finite_iff]
  exact gomesEndpointFiniteCharges_window_iff b N

end RHTower
