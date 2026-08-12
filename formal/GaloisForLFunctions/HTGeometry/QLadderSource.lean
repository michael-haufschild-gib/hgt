import GaloisForLFunctions.HTGeometry.CddShellRadius

/-!
# The geometric q-ladder source

The couplings `B_j = C q^{-j}` with `C > 1` and `0 < q < 1` have shell radii `r_j` dominated by
`q^j/C`, so the atomic family `∑_j r_j δ_{r_j²}` is a finite positive source carried by the *open*
unit interval.  Its moments are therefore an interior point of the Hausdorff cone: every
finite-difference inequality is strict.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C q : ℝ}

/-- The `j`-th coupling of the geometric ladder. -/
def qLadderCoupling (C q : ℝ) (j : ℕ) : ℝ := C * q ^ (-(j : ℤ))

theorem one_lt_qLadderCoupling (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    1 < qLadderCoupling C q j := by
  have hqj : (0 : ℝ) < q ^ j := pow_pos hq0 j
  have hpow : q ^ (-(j : ℤ)) = (q ^ j)⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [qLadderCoupling, hpow]
  have hqle : q ^ j ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have hge : (1 : ℝ) ≤ (q ^ j)⁻¹ := by
    rw [le_inv_comm₀ one_pos hqj]
    simpa using hqle
  nlinarith

/-- The `j`-th shell radius of the geometric ladder. -/
def qLadderRadius (C q : ℝ) (j : ℕ) : ℝ := shellRadius (qLadderCoupling C q j)

theorem qLadderRadius_pos (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    0 < qLadderRadius C q j :=
  shellRadius_pos (one_lt_qLadderCoupling hC hq0 hq1 j)

theorem qLadderRadius_lt_one (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    qLadderRadius C q j < 1 :=
  shellRadius_lt_one (one_lt_qLadderCoupling hC hq0 hq1 j)

theorem qLadderRadius_le (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    qLadderRadius C q j ≤ q ^ j / C :=
  shellRadius_geometric_le hC hq0 hq1 j

theorem summable_qLadderRadius (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (qLadderRadius C q) := by
  refine Summable.of_nonneg_of_le (fun j => (qLadderRadius_pos hC hq0 hq1 j).le)
    (fun j => qLadderRadius_le hC hq0 hq1 j) ?_
  exact (summable_geometric_of_lt_one hq0.le hq1).div_const C

/-- The `j`-th atom of the geometric ladder, at `r_j²`, clamped into the unit interval. -/
def qLadderAtom (C q : ℝ) (j : ℕ) : HausdorffSourceSpace :=
  ⟨max 0 (min 1 ((qLadderRadius C q j) ^ 2)),
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

theorem qLadderAtom_coe (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    ((qLadderAtom C q j : HausdorffSourceSpace) : ℝ) = (qLadderRadius C q j) ^ 2 := by
  have hpos := qLadderRadius_pos hC hq0 hq1 j
  have hlt := qLadderRadius_lt_one hC hq0 hq1 j
  have hsq0 : (0 : ℝ) ≤ (qLadderRadius C q j) ^ 2 := sq_nonneg _
  have hsq1 : (qLadderRadius C q j) ^ 2 ≤ 1 := by nlinarith
  show max 0 (min 1 ((qLadderRadius C q j) ^ 2)) = (qLadderRadius C q j) ^ 2
  rw [min_eq_right hsq1, max_eq_right hsq0]

theorem qLadderAtom_mem_open (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    0 < ((qLadderAtom C q j : HausdorffSourceSpace) : ℝ) ∧
      ((qLadderAtom C q j : HausdorffSourceSpace) : ℝ) < 1 := by
  have hpos := qLadderRadius_pos hC hq0 hq1 j
  have hlt := qLadderRadius_lt_one hC hq0 hq1 j
  rw [qLadderAtom_coe hC hq0 hq1 j]
  constructor
  · positivity
  · nlinarith

/-- **The geometric q-ladder source.** -/
def qLadderSource (C q : ℝ) : Measure HausdorffSourceSpace :=
  Measure.sum fun j : ℕ =>
    ENNReal.ofReal (qLadderRadius C q j) • Measure.dirac (qLadderAtom C q j)

theorem qLadderSource_univ (C q : ℝ) :
    qLadderSource C q Set.univ = ∑' j : ℕ, ENNReal.ofReal (qLadderRadius C q j) := by
  rw [qLadderSource, Measure.sum_apply _ MeasurableSet.univ]
  refine tsum_congr fun j => ?_
  rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]

theorem isFiniteMeasure_qLadderSource (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) :
    IsFiniteMeasure (qLadderSource C q) := by
  refine ⟨?_⟩
  rw [qLadderSource_univ]
  have hsum := summable_qLadderRadius hC hq0 hq1
  have hnn : ∀ j, 0 ≤ qLadderRadius C q j := fun j => (qLadderRadius_pos hC hq0 hq1 j).le
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  exact ENNReal.ofReal_lt_top

/-- **The q-ladder source is carried by the open interval.** -/
theorem qLadderSource_ae_mem_open (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1) :
    ∀ᵐ y : HausdorffSourceSpace ∂(qLadderSource C q),
      0 < (y : ℝ) ∧ (y : ℝ) < 1 := by
  have hmeas : MeasurableSet {x : HausdorffSourceSpace | 0 < (x : ℝ) ∧ (x : ℝ) < 1} :=
    (measurableSet_lt measurable_const measurable_subtype_coe).inter
      (measurableSet_lt measurable_subtype_coe measurable_const)
  rw [qLadderSource, MeasureTheory.Measure.ae_sum_iff' hmeas]
  intro j
  have hbad : Measure.dirac (qLadderAtom C q j)
      {x : HausdorffSourceSpace | 0 < (x : ℝ) ∧ (x : ℝ) < 1}ᶜ = 0 := by
    rw [Measure.dirac_apply' _ hmeas.compl,
      Set.indicator_of_notMem (by simpa using qLadderAtom_mem_open hC hq0 hq1 j)]
  rw [MeasureTheory.ae_iff, Measure.smul_apply, smul_eq_mul]
  have hcompl : {x : HausdorffSourceSpace | ¬(0 < (x : ℝ) ∧ (x : ℝ) < 1)}
      = {x : HausdorffSourceSpace | 0 < (x : ℝ) ∧ (x : ℝ) < 1}ᶜ := rfl
  rw [hcompl, hbad, mul_zero]

/-- **The q-ladder is an interior point of the Hausdorff cone.**  Every signed iterated difference
of its moment sequence is strictly positive. -/
theorem qLadder_strict_completelyMonotone (hC : 1 < C) (hq0 : 0 < q) (hq1 : q < 1)
    (hne : 0 < qLadderSource C q Set.univ) (m k : ℕ) :
    0 < (-1) ^ k * ((fwdDiff 1)^[k] (hausdorffMoment (qLadderSource C q)) m) := by
  haveI := isFiniteMeasure_qLadderSource hC hq0 hq1
  exact hausdorffMoment_strict_completelyMonotone (qLadderSource C q) hne
    (qLadderSource_ae_mem_open hC hq0 hq1) m k

end

end GaloisForLFunctions.HTGeometry
