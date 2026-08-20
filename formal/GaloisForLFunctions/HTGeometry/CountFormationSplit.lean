import GaloisForLFunctions.HTGeometry.CountableRelativeEntropyValue
import GaloisForLFunctions.HTGeometry.ConstitutiveApertureInformationProjection
import GaloisForLFunctions.HTGeometry.PoissonOccupancyHistorySplit

/-!
# The count formation split and its information conservation law

A count is not identified with its occupancy.  It splits, without loss, into a Boolean occupancy
report and, conditionally on nonvacuum, an excess-arrival history.  The split is a bijection onto
`{0} ⊔ ({1} × ℕ)`, and relative information obeys an exact horizontal--vertical conservation law:
the relative entropy of two count laws is the relative entropy of their occupancy reports plus the
occupancy-weighted relative entropy of their excess histories.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory Real
open scoped ENNReal NNReal

noncomputable section

/-! ## The bijection -/

/-- The formation split of a count into occupancy and excess history. -/
def formationSplit (n : ℕ) : Bool × ℕ := (decide (n ≠ 0), n - 1)

/-- The common recovery law. -/
def formationRecovery (bh : Bool × ℕ) : ℕ := if bh.1 then bh.2 + 1 else 0

@[simp] theorem formationSplit_zero : formationSplit 0 = (false, 0) := by simp [formationSplit]

@[simp] theorem formationSplit_succ (n : ℕ) : formationSplit (n + 1) = (true, n) := by
  simp [formationSplit]

/-- The recovery law inverts the formation split. -/
theorem formationRecovery_formationSplit (n : ℕ) : formationRecovery (formationSplit n) = n := by
  cases n with
  | zero => simp [formationRecovery]
  | succ k => simp [formationRecovery]

/-- Marked Boolean--history packets determine the count. -/
theorem formationSplit_injective : Function.Injective formationSplit :=
  Function.LeftInverse.injective formationRecovery_formationSplit

/-- The image of the formation split is the marked vacuum--history sum. -/
theorem range_formationSplit :
    Set.range formationSplit = {(false, 0)} ∪ {q : Bool × ℕ | q.1 = true} := by
  ext ⟨b, h⟩
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
        left
        rw [← hn, formationSplit_zero]
        simp
    | succ k =>
        right
        rw [← hn, formationSplit_succ]
        simp
  · rintro (hq | hq)
    · simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      exact ⟨0, by simp⟩
    · simp only [Set.mem_setOf_eq] at hq
      subst hq
      exact ⟨h + 1, by simp⟩

/-! ## Occupancy and excess history of a count law -/

/-- Occupancy of a count law. -/
def countOccupancy (P : Measure ℕ) : ℝ := 1 - (P {0}).toReal

/-- Excess-history atoms of a count law. -/
def countExcessWeight (P : Measure ℕ) (n : ℕ) : ℝ := (P {n + 1}).toReal / countOccupancy P

/-- Excess-history law of a count law, conditional on nonvacuum. -/
def countExcessLaw (P : Measure ℕ) : Measure ℕ :=
  Measure.sum fun n => ENNReal.ofReal (countExcessWeight P n) • Measure.dirac n

theorem tsum_measure_singleton {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P : Measure α) [IsProbabilityMeasure P] :
    ∑' n : α, P {n} = 1 := by
  have h := lintegral_countable' (μ := P) (fun _ => (1 : ℝ≥0∞))
  simpa using h.symm

theorem hasSum_measure_singleton_toReal {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (P : Measure α) [IsProbabilityMeasure P] :
    HasSum (fun n : α => (P {n}).toReal) 1 := by
  have hne : ∑' n : α, P {n} ≠ ⊤ := by
    rw [tsum_measure_singleton]
    exact ENNReal.one_ne_top
  have hs := ENNReal.summable_toReal hne
  have hval : ∑' n : α, (P {n}).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq fun n => measure_ne_top P _, tsum_measure_singleton]
    simp
  exact hval ▸ hs.hasSum

theorem countOccupancy_pos {P : Measure ℕ} [IsProbabilityMeasure P] (hP0 : ∀ n, P {n} ≠ 0) :
    0 < countOccupancy P := by
  have hdisj : P {0} + P {1} ≤ 1 := by
    have hsub : ({0} ∪ {1} : Set ℕ) ⊆ Set.univ := Set.subset_univ _
    have hadd : P ({0} ∪ {1} : Set ℕ) = P {0} + P {1} := by
      refine measure_union ?_ (MeasurableSet.singleton 1)
      simp
    calc P {0} + P {1} = P ({0} ∪ {1} : Set ℕ) := hadd.symm
      _ ≤ P Set.univ := measure_mono hsub
      _ = 1 := measure_univ
  have h1 : 0 < (P {1}).toReal := by
    refine ENNReal.toReal_pos (hP0 1) (measure_ne_top P _)
  have h0 : (P {0}).toReal + (P {1}).toReal ≤ 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)]
    calc (P {0} + P {1}).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top hdisj
      _ = 1 := by simp
  rw [countOccupancy]
  linarith

theorem countOccupancy_le_one (P : Measure ℕ) : countOccupancy P ≤ 1 := by
  rw [countOccupancy]
  have : (0 : ℝ) ≤ (P {0}).toReal := ENNReal.toReal_nonneg
  linarith

/-- Occupancy of a count law as a point of the unit interval. -/
def countOccupancyUnit (P : Measure ℕ) [IsProbabilityMeasure P] (hP0 : ∀ n, P {n} ≠ 0) :
    unitInterval :=
  ⟨countOccupancy P, ⟨(countOccupancy_pos hP0).le, countOccupancy_le_one P⟩⟩

@[simp] theorem coe_countOccupancyUnit (P : Measure ℕ) [IsProbabilityMeasure P]
    (hP0 : ∀ n, P {n} ≠ 0) : (countOccupancyUnit P hP0 : ℝ) = countOccupancy P := rfl

theorem countOccupancy_lt_one {P : Measure ℕ} [IsProbabilityMeasure P] (hP0 : ∀ n, P {n} ≠ 0) :
    countOccupancy P < 1 := by
  have h0 : 0 < (P {0}).toReal := ENNReal.toReal_pos (hP0 0) (measure_ne_top P _)
  rw [countOccupancy]
  linarith

theorem countExcessWeight_pos {P : Measure ℕ} [IsProbabilityMeasure P] (hP0 : ∀ n, P {n} ≠ 0)
    (n : ℕ) : 0 < countExcessWeight P n := by
  have hq := countOccupancy_pos hP0
  have hn : 0 < (P {n + 1}).toReal := ENNReal.toReal_pos (hP0 (n + 1)) (measure_ne_top P _)
  rw [countExcessWeight]
  positivity

theorem hasSum_countExcessWeight {P : Measure ℕ} [IsProbabilityMeasure P]
    (hP0 : ∀ n, P {n} ≠ 0) : HasSum (countExcessWeight P) 1 := by
  have hq := countOccupancy_pos hP0
  have htotal := hasSum_measure_singleton_toReal P
  have hshift : HasSum (fun n : ℕ => (P {n + 1}).toReal) (countOccupancy P) := by
    have h := (hasSum_nat_add_iff' (f := fun n : ℕ => (P {n}).toReal) 1).2 htotal
    simpa [countOccupancy] using h
  have := hshift.div_const (countOccupancy P)
  rw [div_self hq.ne'] at this
  exact this

theorem isProbabilityMeasure_countExcessLaw {P : Measure ℕ} [IsProbabilityMeasure P]
    (hP0 : ∀ n, P {n} ≠ 0) : IsProbabilityMeasure (countExcessLaw P) :=
  (hasSum_countExcessWeight hP0).isProbabilityMeasure_sum_dirac
    fun n => (countExcessWeight_pos hP0 n).le

theorem countExcessLaw_singleton (P : Measure ℕ) (n : ℕ) :
    countExcessLaw P {n} = ENNReal.ofReal (countExcessWeight P n) := by
  rw [countExcessLaw, Measure.sum_smul_dirac_singleton]

theorem countExcessLaw_singleton_toReal {P : Measure ℕ} [IsProbabilityMeasure P]
    (hP0 : ∀ n, P {n} ≠ 0) (n : ℕ) :
    (countExcessLaw P {n}).toReal = countExcessWeight P n := by
  rw [countExcessLaw_singleton, ENNReal.toReal_ofReal (countExcessWeight_pos hP0 n).le]

theorem countExcessLaw_singleton_ne_zero {P : Measure ℕ} [IsProbabilityMeasure P]
    (hP0 : ∀ n, P {n} ≠ 0) (n : ℕ) : countExcessLaw P {n} ≠ 0 := by
  rw [countExcessLaw_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact countExcessWeight_pos hP0 n

/-! ## Information conservation -/

theorem measure_singleton_succ_toReal {P : Measure ℕ} [IsProbabilityMeasure P]
    (hP0 : ∀ n, P {n} ≠ 0) (n : ℕ) :
    (P {n + 1}).toReal = countOccupancy P * countExcessWeight P n := by
  have hq : countOccupancy P ≠ 0 := (countOccupancy_pos hP0).ne'
  rw [countExcessWeight]
  field_simp

theorem log_succ_ratio {P Q : Measure ℕ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP0 : ∀ n, P {n} ≠ 0) (hQ0 : ∀ n, Q {n} ≠ 0) (n : ℕ) :
    Real.log ((P {n + 1}).toReal / (Q {n + 1}).toReal)
      = Real.log (countOccupancy P / countOccupancy Q)
        + Real.log (countExcessWeight P n / countExcessWeight Q n) := by
  have hqP := countOccupancy_pos hP0
  have hqQ := countOccupancy_pos hQ0
  have hkP := countExcessWeight_pos hP0 n
  have hkQ := countExcessWeight_pos hQ0 n
  rw [measure_singleton_succ_toReal hP0, measure_singleton_succ_toReal hQ0,
    show countOccupancy P * countExcessWeight P n / (countOccupancy Q * countExcessWeight Q n)
      = (countOccupancy P / countOccupancy Q) *
        (countExcessWeight P n / countExcessWeight Q n) from by
      field_simp,
    Real.log_mul (by positivity) (by positivity)]

theorem summable_countExcess_abs_logRatio {P Q : Measure ℕ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP0 : ∀ n, P {n} ≠ 0) (hQ0 : ∀ n, Q {n} ≠ 0)
    (hfin : klDiv P Q ≠ ⊤) :
    Summable fun n : ℕ => (countExcessLaw P {n}).toReal *
      |Real.log ((countExcessLaw P {n}).toReal / (countExcessLaw Q {n}).toReal)| := by
  haveI := isProbabilityMeasure_countExcessLaw hP0
  haveI := isProbabilityMeasure_countExcessLaw hQ0
  have hqP := countOccupancy_pos hP0
  have hsum : Summable fun n : ℕ =>
      (P {n}).toReal * |Real.log ((P {n}).toReal / (Q {n}).toReal)| :=
    summable_log_singleton_ratio_of_klDiv_ne_top hQ0 hfin
  have hshift : Summable fun n : ℕ =>
      (P {n + 1}).toReal * |Real.log ((P {n + 1}).toReal / (Q {n + 1}).toReal)| :=
    (summable_nat_add_iff 1).2 hsum
  have hkP : Summable (countExcessWeight P) := (hasSum_countExcessWeight hP0).summable
  have hmajor : Summable fun n : ℕ =>
      (countOccupancy P)⁻¹ * ((P {n + 1}).toReal *
        |Real.log ((P {n + 1}).toReal / (Q {n + 1}).toReal)|)
      + |Real.log (countOccupancy P / countOccupancy Q)| * countExcessWeight P n :=
    (hshift.mul_left _).add (hkP.mul_left _)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmajor
  rw [countExcessLaw_singleton_toReal hP0, countExcessLaw_singleton_toReal hQ0]
  have hkPn := countExcessWeight_pos hP0 n
  have habs : |Real.log (countExcessWeight P n / countExcessWeight Q n)|
      ≤ |Real.log ((P {n + 1}).toReal / (Q {n + 1}).toReal)|
        + |Real.log (countOccupancy P / countOccupancy Q)| := by
    rw [log_succ_ratio hP0 hQ0 n]
    have hid : (Real.log (countOccupancy P / countOccupancy Q)
          + Real.log (countExcessWeight P n / countExcessWeight Q n))
        - Real.log (countOccupancy P / countOccupancy Q)
        = Real.log (countExcessWeight P n / countExcessWeight Q n) := by ring
    calc |Real.log (countExcessWeight P n / countExcessWeight Q n)|
        = |(Real.log (countOccupancy P / countOccupancy Q)
            + Real.log (countExcessWeight P n / countExcessWeight Q n))
          - Real.log (countOccupancy P / countOccupancy Q)| := by rw [hid]
      _ ≤ |Real.log (countOccupancy P / countOccupancy Q)
            + Real.log (countExcessWeight P n / countExcessWeight Q n)|
          + |Real.log (countOccupancy P / countOccupancy Q)| := abs_sub _ _
  calc countExcessWeight P n * |Real.log (countExcessWeight P n / countExcessWeight Q n)|
      ≤ countExcessWeight P n * (|Real.log ((P {n + 1}).toReal / (Q {n + 1}).toReal)|
          + |Real.log (countOccupancy P / countOccupancy Q)|) :=
        mul_le_mul_of_nonneg_left habs hkPn.le
    _ = (countOccupancy P)⁻¹ * ((P {n + 1}).toReal *
          |Real.log ((P {n + 1}).toReal / (Q {n + 1}).toReal)|)
        + |Real.log (countOccupancy P / countOccupancy Q)| * countExcessWeight P n := by
        rw [measure_singleton_succ_toReal hP0]
        field_simp

/-- **Formation split and information conservation.**  The relative entropy of two full-support
count laws is the relative entropy of their Boolean occupancy reports plus the occupancy-weighted
relative entropy of their excess-arrival histories. -/
theorem toReal_klDiv_formationSplit {P Q : Measure ℕ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP0 : ∀ n, P {n} ≠ 0) (hQ0 : ∀ n, Q {n} ≠ 0)
    (hfin : klDiv P Q ≠ ⊤) :
    (klDiv P Q).toReal
      = (klDiv Ber(true, false, countOccupancyUnit P hP0)
          Ber(true, false, countOccupancyUnit Q hQ0)).toReal
        + countOccupancy P * (klDiv (countExcessLaw P) (countExcessLaw Q)).toReal := by
  haveI := isProbabilityMeasure_countExcessLaw hP0
  haveI := isProbabilityMeasure_countExcessLaw hQ0
  have hqP := countOccupancy_pos hP0
  have hqQ := countOccupancy_pos hQ0
  have hqQ1 := countOccupancy_lt_one hQ0
  have hsum : Summable fun n : ℕ =>
      (P {n}).toReal * |Real.log ((P {n}).toReal / (Q {n}).toReal)| :=
    summable_log_singleton_ratio_of_klDiv_ne_top hQ0 hfin
  have hsig : Summable fun n : ℕ =>
      (P {n}).toReal * Real.log ((P {n}).toReal / (Q {n}).toReal) := by
    refine Summable.of_abs (hsum.congr fun n => ?_)
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have hexcSum := summable_countExcess_abs_logRatio hP0 hQ0 hfin
  have hexcSig : Summable fun n : ℕ => countExcessWeight P n *
      Real.log (countExcessWeight P n / countExcessWeight Q n) := by
    refine Summable.of_abs (hexcSum.congr fun n => ?_)
    rw [countExcessLaw_singleton_toReal hP0, countExcessLaw_singleton_toReal hQ0, abs_mul,
      abs_of_nonneg (countExcessWeight_pos hP0 n).le]
  have hkP : Summable (countExcessWeight P) := (hasSum_countExcessWeight hP0).summable
  rw [toReal_klDiv_of_countable hQ0 hsum, hsig.tsum_eq_zero_add,
    toReal_klDiv_bernoulli_baseline_interior _ _ hqQ hqQ1,
    toReal_klDiv_of_countable (fun n => countExcessLaw_singleton_ne_zero hQ0 n) hexcSum]
  have htail : ∑' n : ℕ, (P {n + 1}).toReal * Real.log ((P {n + 1}).toReal / (Q {n + 1}).toReal)
      = countOccupancy P * Real.log (countOccupancy P / countOccupancy Q)
        + countOccupancy P * ∑' n : ℕ, countExcessWeight P n *
            Real.log (countExcessWeight P n / countExcessWeight Q n) := by
    have hterm : ∀ n : ℕ,
        (P {n + 1}).toReal * Real.log ((P {n + 1}).toReal / (Q {n + 1}).toReal)
          = countOccupancy P * Real.log (countOccupancy P / countOccupancy Q) *
              countExcessWeight P n
            + countOccupancy P * (countExcessWeight P n *
              Real.log (countExcessWeight P n / countExcessWeight Q n)) := by
      intro n
      rw [log_succ_ratio hP0 hQ0 n, measure_singleton_succ_toReal hP0]
      ring
    rw [tsum_congr hterm, (hkP.mul_left _).tsum_add (hexcSig.mul_left _),
      tsum_mul_left, tsum_mul_left, (hasSum_countExcessWeight hP0).tsum_eq]
    ring
  rw [htail]
  have hzero : (P {0}).toReal = 1 - countOccupancy P := by
    rw [countOccupancy]; ring
  have hzeroQ : (Q {0}).toReal = 1 - countOccupancy Q := by
    rw [countOccupancy]; ring
  rw [hzero, hzeroQ, coe_countOccupancyUnit, coe_countOccupancyUnit]
  have hexcVal : ∑' n : ℕ, (countExcessLaw P {n}).toReal *
      Real.log ((countExcessLaw P {n}).toReal / (countExcessLaw Q {n}).toReal)
      = ∑' n : ℕ, countExcessWeight P n *
        Real.log (countExcessWeight P n / countExcessWeight Q n) := by
    refine tsum_congr fun n => ?_
    rw [countExcessLaw_singleton_toReal hP0, countExcessLaw_singleton_toReal hQ0]
  rw [hexcVal]
  ring

/-- Symmetrized formation conservation: the Boolean occupancy work plus the two-sided history
reserve erased by Boolean support projection. -/
theorem toReal_klDiv_formationSplit_symm {P Q : Measure ℕ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP0 : ∀ n, P {n} ≠ 0) (hQ0 : ∀ n, Q {n} ≠ 0)
    (hPQ : klDiv P Q ≠ ⊤) (hQP : klDiv Q P ≠ ⊤) :
    (klDiv P Q).toReal + (klDiv Q P).toReal
      = ((klDiv Ber(true, false, countOccupancyUnit P hP0)
            Ber(true, false, countOccupancyUnit Q hQ0)).toReal
          + (klDiv Ber(true, false, countOccupancyUnit Q hQ0)
            Ber(true, false, countOccupancyUnit P hP0)).toReal)
        + (countOccupancy P * (klDiv (countExcessLaw P) (countExcessLaw Q)).toReal
          + countOccupancy Q * (klDiv (countExcessLaw Q) (countExcessLaw P)).toReal) := by
  rw [toReal_klDiv_formationSplit hP0 hQ0 hPQ, toReal_klDiv_formationSplit hQ0 hP0 hQP]
  ring

/-- **Reconstruction.**  The marked occupancy--history packet determines the count law. -/
theorem measure_eq_of_split_eq {P Q : Measure ℕ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP0 : ∀ n, P {n} ≠ 0) (hQ0 : ∀ n, Q {n} ≠ 0)
    (hocc : countOccupancy P = countOccupancy Q) (hexc : countExcessLaw P = countExcessLaw Q) :
    P = Q := by
  refine Measure.ext_of_singleton fun n => ?_
  cases n with
  | zero =>
      have h : (P {0}).toReal = (Q {0}).toReal := by
        rw [countOccupancy, countOccupancy] at hocc
        linarith
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P _) (measure_ne_top Q _)).1 h
  | succ k =>
      have hw : countExcessWeight P k = countExcessWeight Q k := by
        have h := congrArg (fun μ : Measure ℕ => (μ {k}).toReal) hexc
        simpa [countExcessLaw_singleton_toReal hP0, countExcessLaw_singleton_toReal hQ0] using h
      have h : (P {k + 1}).toReal = (Q {k + 1}).toReal := by
        rw [measure_singleton_succ_toReal hP0, measure_singleton_succ_toReal hQ0, hocc, hw]
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P _) (measure_ne_top Q _)).1 h

/-! ## The Poisson instance -/

open ProbabilityTheory in
theorem countOccupancy_poissonMeasure (r : ℝ≥0) :
    countOccupancy Po(r) = (poissonOccupancyUnit r : ℝ) := by
  rw [countOccupancy, poissonMeasure_singleton_toReal, coe_poissonOccupancyUnit]
  norm_num

open ProbabilityTheory in
theorem countExcessWeight_poissonMeasure {r : ℝ≥0} (hr : 0 < r) (n : ℕ) :
    countExcessWeight Po(r) n = excessCountWeight (r : ℝ) n := by
  have hr' : (0 : ℝ) < (r : ℝ) := hr
  have hexp : (0 : ℝ) < Real.exp (r : ℝ) := Real.exp_pos _
  have hone : Real.exp (-(r : ℝ)) * Real.exp (r : ℝ) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsub : (0 : ℝ) < Real.exp (r : ℝ) - 1 := exp_sub_one_pos hr'
  have hocc : countOccupancy Po(r) = 1 - Real.exp (-(r : ℝ)) := by
    rw [countOccupancy_poissonMeasure, coe_poissonOccupancyUnit]
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  have hoccpos : (0 : ℝ) < 1 - Real.exp (-(r : ℝ)) := by
    have : Real.exp (-(r : ℝ)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have hkey : Real.exp (-(r : ℝ)) / (1 - Real.exp (-(r : ℝ)))
      = 1 / (Real.exp (r : ℝ) - 1) := by
    rw [div_eq_div_iff hoccpos.ne' hsub.ne']
    linear_combination hone
  rw [countExcessWeight, hocc, poissonMeasure_singleton_toReal, excessCountWeight,
    show Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (((n + 1).factorial : ℕ) : ℝ) /
        (1 - Real.exp (-(r : ℝ)))
      = ((r : ℝ) ^ (n + 1) / (((n + 1).factorial : ℕ) : ℝ)) *
        (Real.exp (-(r : ℝ)) / (1 - Real.exp (-(r : ℝ)))) from by ring, hkey,
    div_mul_div_comm, mul_one]

open ProbabilityTheory in
/-- The Poisson count law splits into its occupancy report and the shifted zero-truncated
Poisson excess history. -/
theorem countExcessLaw_poissonMeasure {r : ℝ≥0} (hr : 0 < r) :
    countExcessLaw Po(r) = excessCountMeasure (r : ℝ) := by
  rw [countExcessLaw, excessCountMeasure]
  congr 1
  funext n
  rw [countExcessWeight_poissonMeasure hr]

end

end GaloisForLFunctions.HTGeometry
