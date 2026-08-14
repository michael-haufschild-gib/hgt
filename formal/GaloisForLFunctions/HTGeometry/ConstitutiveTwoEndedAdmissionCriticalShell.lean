import GaloisForLFunctions.HTGeometry.ConstitutiveBoundedAlternation
import GaloisForLFunctions.HTGeometry.ConstitutiveOneEndedAdmissionCriticalShell
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace HTGeometry

noncomputable section

open Filter Set Topology
open scoped Topology

/-!
# Two-ended analytic-admission critical shell

`TwoEndedInt` is an exact topological copy of `ℤ ∪ {-∞,+∞}`: the left one-point ray represents
`-1,-2,...,-∞`, and the right ray represents `0,1,...,+∞`.  Adjacent-pair retractions alternate
across every integer and fix both ends.  Their algebraic join has exactly three classes, while
continuous Hausdorff admission collapses all three.
-/

/-- Exact two-ended compactification of the integers, split into negative and nonnegative rays. -/
abbrev TwoEndedInt := OnePoint ℕ ⊕ OnePoint ℕ

/-- Negative end. -/
def twoEndedNegInfinity : TwoEndedInt := Sum.inl OnePoint.infty

/-- Positive end. -/
def twoEndedPosInfinity : TwoEndedInt := Sum.inr OnePoint.infty

/-- Integer embedding: `-(n+1)` is on the left ray and `n` is on the right ray. -/
def twoEndedIntOfInt : ℤ → TwoEndedInt
  | Int.ofNat n => Sum.inr (n : OnePoint ℕ)
  | Int.negSucc n => Sum.inl (n : OnePoint ℕ)

theorem twoEndedIntOfInt_injective : Function.Injective twoEndedIntOfInt := by
  intro m n h
  cases m <;> cases n <;> simp [twoEndedIntOfInt] at h
  all_goals cases h
  all_goals rfl

/-- Left-ray index retraction pairing `0,1`, `2,3`, ... at the odd endpoint. -/
def upperOddIndex (n : ℕ) : ℕ := lowerEven n + 1

/-- Right-ray index retraction fixing `0` and pairing `1,2`, `3,4`, ... at the even endpoint. -/
def upperEvenIndex (n : ℕ) : ℕ := 2 * ((n + 1) / 2)

@[simp] theorem upperEvenIndex_zero : upperEvenIndex 0 = 0 := rfl

@[simp] theorem upperOddIndex_two_mul (k : ℕ) :
    upperOddIndex (2 * k) = 2 * k + 1 := by
  simp [upperOddIndex, lowerEven_two_mul]

@[simp] theorem upperOddIndex_two_mul_add_one (k : ℕ) :
    upperOddIndex (2 * k + 1) = 2 * k + 1 := by
  simp [upperOddIndex, lowerEven_two_mul_add_one]

@[simp] theorem upperEvenIndex_two_mul (k : ℕ) :
    upperEvenIndex (2 * k) = 2 * k := by
  unfold upperEvenIndex
  rw [Nat.mul_add_div (m := 2) (by linarith) k 1]
  simp

@[simp] theorem upperEvenIndex_two_mul_add_one (k : ℕ) :
    upperEvenIndex (2 * k + 1) = 2 * k + 2 := by
  unfold upperEvenIndex
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by rfl]
  rw [Nat.mul_add_div (m := 2) (by linarith) k 2]
  ring

theorem le_upperOddIndex (n : ℕ) : n ≤ upperOddIndex n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [upperOddIndex_two_mul]
    exact Nat.le_succ _
  · rw [upperOddIndex_two_mul_add_one]

theorem le_upperEvenIndex (n : ℕ) : n ≤ upperEvenIndex n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [upperEvenIndex_two_mul]
  · rw [upperEvenIndex_two_mul_add_one]
    exact Nat.le_succ _

instance : Filter.TendstoCofinite upperOddIndex := by
  rw [Filter.tendstoCofinite_iff_finite_preimage_singleton]
  intro b
  apply (Set.finite_le_nat b).subset
  intro n hn
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hn
  subst b
  exact le_upperOddIndex n

instance : Filter.TendstoCofinite upperEvenIndex := by
  rw [Filter.tendstoCofinite_iff_finite_preimage_singleton]
  intro b
  apply (Set.finite_le_nat b).subset
  intro n hn
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hn
  subst b
  exact le_upperEvenIndex n

theorem tendsto_coe_upperOddIndex :
    Tendsto (fun n : ℕ => (upperOddIndex n : OnePoint ℕ))
      cofinite (𝓝 OnePoint.infty) := by
  have hcoe : Tendsto (fun n : ℕ => (n : OnePoint ℕ))
      cofinite (𝓝 OnePoint.infty) := by
    simpa [Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))
  exact hcoe.comp (Filter.TendstoCofinite.tendsto_cofinite upperOddIndex)

theorem tendsto_coe_upperEvenIndex :
    Tendsto (fun n : ℕ => (upperEvenIndex n : OnePoint ℕ))
      cofinite (𝓝 OnePoint.infty) := by
  have hcoe : Tendsto (fun n : ℕ => (n : OnePoint ℕ))
      cofinite (𝓝 OnePoint.infty) := by
    simpa [Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))
  exact hcoe.comp (Filter.TendstoCofinite.tendsto_cofinite upperEvenIndex)

theorem upperOddIndex_idempotent (n : ℕ) :
    upperOddIndex (upperOddIndex n) = upperOddIndex n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [upperOddIndex_two_mul, upperOddIndex_two_mul_add_one]
  · rw [upperOddIndex_two_mul_add_one, upperOddIndex_two_mul_add_one]

theorem upperEvenIndex_idempotent (n : ℕ) :
    upperEvenIndex (upperEvenIndex n) = upperEvenIndex n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [upperEvenIndex_two_mul, upperEvenIndex_two_mul]
  · rw [upperEvenIndex_two_mul_add_one]
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, upperEvenIndex_two_mul]

theorem lowerEven_idempotent (n : ℕ) : lowerEven (lowerEven n) = lowerEven n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [lowerEven_two_mul, lowerEven_two_mul]
  · rw [lowerEven_two_mul_add_one, lowerEven_two_mul]

theorem lowerOdd_idempotent (n : ℕ) : lowerOdd (lowerOdd n) = lowerOdd n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · cases k with
      | zero => exact (hn rfl).elim
      | succ k =>
          rw [show 2 * (k + 1) = 2 * k + 2 by ring,
            lowerOdd_two_mul_add_two, lowerOdd_two_mul_add_one]
    · rw [lowerOdd_two_mul_add_one, lowerOdd_two_mul_add_one]

theorem lowerOdd_ne_zero {n : ℕ} (hn : n ≠ 0) : lowerOdd n ≠ 0 := by
  simp [lowerOdd, hn]

/-- Even-pair retraction on the left ray. -/
def twoEndedEvenLeftRay : C(OnePoint ℕ, TwoEndedInt) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => Sum.inl (upperOddIndex n : OnePoint ℕ))
    twoEndedNegInfinity
    (by
      simpa [Function.comp_def, twoEndedNegInfinity] using
        (continuous_inl.tendsto OnePoint.infty).comp tendsto_coe_upperOddIndex)

/-- Even-pair retraction on the right ray. -/
def twoEndedEvenRightRay : C(OnePoint ℕ, TwoEndedInt) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => Sum.inr (lowerEven n : OnePoint ℕ))
    twoEndedPosInfinity
    (by
      simpa [Function.comp_def, twoEndedPosInfinity] using
        (continuous_inr.tendsto OnePoint.infty).comp tendsto_coe_lowerEven)

/-- Odd-pair retraction on the left ray, including the bridge `-1 ↦ 0`. -/
def twoEndedOddLeftRay : C(OnePoint ℕ, TwoEndedInt) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => if n = 0 then Sum.inr ((0 : ℕ) : OnePoint ℕ)
      else Sum.inl (lowerOdd n : OnePoint ℕ))
    twoEndedNegInfinity
    (by
      have hbase : Tendsto
          (fun n : ℕ => Sum.inl (lowerOdd n : OnePoint ℕ))
          cofinite (𝓝 twoEndedNegInfinity) := by
        simpa [Function.comp_def, twoEndedNegInfinity] using
          (continuous_inl.tendsto OnePoint.infty).comp tendsto_coe_lowerOdd
      apply hbase.congr'
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ne_atTop 0] with n hn
      simp [hn])

/-- Odd-pair retraction on the right ray. -/
def twoEndedOddRightRay : C(OnePoint ℕ, TwoEndedInt) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => Sum.inr (upperEvenIndex n : OnePoint ℕ))
    twoEndedPosInfinity
    (by
      simpa [Function.comp_def, twoEndedPosInfinity] using
        (continuous_inr.tendsto OnePoint.infty).comp tendsto_coe_upperEvenIndex)

/-- Continuous even-pair formation fixing both ends. -/
def twoEndedEvenFormation : C(TwoEndedInt, TwoEndedInt) :=
  ⟨Sum.elim twoEndedEvenLeftRay twoEndedEvenRightRay,
    twoEndedEvenLeftRay.continuous.sumElim twoEndedEvenRightRay.continuous⟩

/-- Continuous odd-pair formation fixing both ends and joining `-1` to `0`. -/
def twoEndedOddFormation : C(TwoEndedInt, TwoEndedInt) :=
  ⟨Sum.elim twoEndedOddLeftRay twoEndedOddRightRay,
    twoEndedOddLeftRay.continuous.sumElim twoEndedOddRightRay.continuous⟩

@[simp] theorem twoEndedEvenFormation_negInfinity :
    twoEndedEvenFormation twoEndedNegInfinity = twoEndedNegInfinity := rfl

@[simp] theorem twoEndedEvenFormation_posInfinity :
    twoEndedEvenFormation twoEndedPosInfinity = twoEndedPosInfinity := rfl

@[simp] theorem twoEndedOddFormation_negInfinity :
    twoEndedOddFormation twoEndedNegInfinity = twoEndedNegInfinity := rfl

@[simp] theorem twoEndedOddFormation_posInfinity :
    twoEndedOddFormation twoEndedPosInfinity = twoEndedPosInfinity := rfl

@[simp] theorem twoEndedEvenFormation_left (n : ℕ) :
    twoEndedEvenFormation (Sum.inl (n : OnePoint ℕ)) =
      Sum.inl (upperOddIndex n : OnePoint ℕ) := rfl

@[simp] theorem twoEndedEvenFormation_right (n : ℕ) :
    twoEndedEvenFormation (Sum.inr (n : OnePoint ℕ)) =
      Sum.inr (lowerEven n : OnePoint ℕ) := rfl

@[simp] theorem twoEndedOddFormation_left_zero :
    twoEndedOddFormation (Sum.inl ((0 : ℕ) : OnePoint ℕ)) =
      Sum.inr ((0 : ℕ) : OnePoint ℕ) := rfl

@[simp] theorem twoEndedOddFormation_left_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    twoEndedOddFormation (Sum.inl (n : OnePoint ℕ)) =
      Sum.inl (lowerOdd n : OnePoint ℕ) := by
  change (if n = 0 then Sum.inr ((0 : ℕ) : OnePoint ℕ)
    else Sum.inl (lowerOdd n : OnePoint ℕ)) = _
  rw [if_neg hn]

@[simp] theorem twoEndedOddFormation_right (n : ℕ) :
    twoEndedOddFormation (Sum.inr (n : OnePoint ℕ)) =
      Sum.inr (upperEvenIndex n : OnePoint ℕ) := rfl

theorem twoEndedEvenFormation_idempotent (x : TwoEndedInt) :
    twoEndedEvenFormation (twoEndedEvenFormation x) = twoEndedEvenFormation x := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n => simp [upperOddIndex_idempotent]
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n => simp [lowerEven_idempotent]

theorem twoEndedOddFormation_idempotent (x : TwoEndedInt) :
    twoEndedOddFormation (twoEndedOddFormation x) = twoEndedOddFormation x := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases hn : n = 0
        · subst n
          simp
        · simp [twoEndedOddFormation_left_of_ne_zero hn,
            twoEndedOddFormation_left_of_ne_zero (lowerOdd_ne_zero hn),
            lowerOdd_idempotent]
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n => simp [upperEvenIndex_idempotent]

/-- Closed even-fibre equivalence. -/
def twoEndedEvenSetoid : Setoid TwoEndedInt := Setoid.ker twoEndedEvenFormation

/-- Closed odd-fibre equivalence. -/
def twoEndedOddSetoid : Setoid TwoEndedInt := Setoid.ker twoEndedOddFormation

theorem twoEndedEvenSetoid_isClosed :
    IsClosedAdmissionSetoid twoEndedEvenSetoid := by
  change IsClosed {p : TwoEndedInt × TwoEndedInt |
    twoEndedEvenFormation p.1 = twoEndedEvenFormation p.2}
  exact isClosed_eq
    (twoEndedEvenFormation.continuous.comp continuous_fst)
    (twoEndedEvenFormation.continuous.comp continuous_snd)

theorem twoEndedOddSetoid_isClosed :
    IsClosedAdmissionSetoid twoEndedOddSetoid := by
  change IsClosed {p : TwoEndedInt × TwoEndedInt |
    twoEndedOddFormation p.1 = twoEndedOddFormation p.2}
  exact isClosed_eq
    (twoEndedOddFormation.continuous.comp continuous_fst)
    (twoEndedOddFormation.continuous.comp continuous_snd)

/-- Primitive relation generated by unitizing either formation. -/
def twoEndedJoinedUnitization (x y : TwoEndedInt) : Prop :=
  y = twoEndedEvenFormation x ∨ y = twoEndedOddFormation x

theorem twoEnded_jointlyUnitizing_right_adjacent
    {Y : Type*} (q : TwoEndedInt → Y)
    (he : ∀ x, q (twoEndedEvenFormation x) = q x)
    (ho : ∀ x, q (twoEndedOddFormation x) = q x)
    (n : ℕ) :
    q (Sum.inr (n : OnePoint ℕ)) =
      q (Sum.inr (n + 1 : ℕ)) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have h := he (Sum.inr ((2 * k + 1 : ℕ) : OnePoint ℕ))
    rw [twoEndedEvenFormation_right, lowerEven_two_mul_add_one] at h
    simpa using h
  · simpa using
      (ho (Sum.inr ((2 * k + 1 : ℕ) : OnePoint ℕ))).symm

theorem twoEnded_jointlyUnitizing_left_adjacent
    {Y : Type*} (q : TwoEndedInt → Y)
    (he : ∀ x, q (twoEndedEvenFormation x) = q x)
    (ho : ∀ x, q (twoEndedOddFormation x) = q x)
    (n : ℕ) :
    q (Sum.inl (n : OnePoint ℕ)) =
      q (Sum.inl (n + 1 : ℕ)) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · simpa using (he (Sum.inl ((2 * k : ℕ) : OnePoint ℕ))).symm
  · have h := ho (Sum.inl ((2 * k + 2 : ℕ) : OnePoint ℕ))
    rw [twoEndedOddFormation_left_of_ne_zero, lowerOdd_two_mul_add_two] at h
    · simpa using h
    · exact Nat.succ_ne_zero _

theorem twoEnded_jointlyUnitizing_bridge
    {Y : Type*} (q : TwoEndedInt → Y)
    (ho : ∀ x, q (twoEndedOddFormation x) = q x) :
    q (Sum.inl ((0 : ℕ) : OnePoint ℕ)) =
      q (Sum.inr ((0 : ℕ) : OnePoint ℕ)) := by
  simpa using (ho (Sum.inl ((0 : ℕ) : OnePoint ℕ))).symm

theorem twoEnded_jointlyUnitizing_finite_constant
    {Y : Type*} (q : TwoEndedInt → Y)
    (he : ∀ x, q (twoEndedEvenFormation x) = q x)
    (ho : ∀ x, q (twoEndedOddFormation x) = q x) :
    (∀ n : ℕ, q (Sum.inr (n : OnePoint ℕ)) =
      q (Sum.inr ((0 : ℕ) : OnePoint ℕ))) ∧
    (∀ n : ℕ, q (Sum.inl (n : OnePoint ℕ)) =
      q (Sum.inr ((0 : ℕ) : OnePoint ℕ))) := by
  constructor
  · intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        exact (twoEnded_jointlyUnitizing_right_adjacent q he ho n).symm.trans ih
  · intro n
    have hbridge := twoEnded_jointlyUnitizing_bridge q ho
    induction n with
    | zero => exact hbridge
    | succ n ih =>
        exact (twoEnded_jointlyUnitizing_left_adjacent q he ho n).symm.trans ih

theorem tendsto_twoEnded_left_coe :
    Tendsto (fun n : ℕ => Sum.inl (n : OnePoint ℕ))
      cofinite (𝓝 twoEndedNegInfinity) := by
  have hcoe : Tendsto (fun n : ℕ => (n : OnePoint ℕ))
      cofinite (𝓝 OnePoint.infty) := by
    simpa [Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))
  simpa [Function.comp_def, twoEndedNegInfinity] using
    (continuous_inl.tendsto OnePoint.infty).comp hcoe

theorem tendsto_twoEnded_right_coe :
    Tendsto (fun n : ℕ => Sum.inr (n : OnePoint ℕ))
      cofinite (𝓝 twoEndedPosInfinity) := by
  have hcoe : Tendsto (fun n : ℕ => (n : OnePoint ℕ))
      cofinite (𝓝 OnePoint.infty) := by
    simpa [Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))
  simpa [Function.comp_def, twoEndedPosInfinity] using
    (continuous_inr.tendsto OnePoint.infty).comp hcoe

/-- Every continuous Hausdorff-valued jointly unitizing observer is constant on the full
two-ended compactification. -/
theorem continuous_twoEnded_jointlyUnitizing_constant
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (q : C(TwoEndedInt, Y))
    (he : ∀ x, q (twoEndedEvenFormation x) = q x)
    (ho : ∀ x, q (twoEndedOddFormation x) = q x) :
    ∀ x y, q x = q y := by
  obtain ⟨hright, hleft⟩ := twoEnded_jointlyUnitizing_finite_constant q he ho
  have hnegLim : Tendsto (fun n : ℕ => q (Sum.inl (n : OnePoint ℕ)))
      cofinite (𝓝 (q twoEndedNegInfinity)) := by
    simpa [Function.comp_def] using
      (q.continuous.tendsto twoEndedNegInfinity).comp tendsto_twoEnded_left_coe
  have hposLim : Tendsto (fun n : ℕ => q (Sum.inr (n : OnePoint ℕ)))
      cofinite (𝓝 (q twoEndedPosInfinity)) := by
    simpa [Function.comp_def] using
      (q.continuous.tendsto twoEndedPosInfinity).comp tendsto_twoEnded_right_coe
  have hconstLeft : Tendsto (fun n : ℕ => q (Sum.inl (n : OnePoint ℕ)))
      cofinite (𝓝 (q (Sum.inr ((0 : ℕ) : OnePoint ℕ)))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    exact (hleft n).symm
  have hconstRight : Tendsto (fun n : ℕ => q (Sum.inr (n : OnePoint ℕ)))
      cofinite (𝓝 (q (Sum.inr ((0 : ℕ) : OnePoint ℕ)))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    exact (hright n).symm
  have hneg : q twoEndedNegInfinity =
      q (Sum.inr ((0 : ℕ) : OnePoint ℕ)) :=
    tendsto_nhds_unique hnegLim hconstLeft
  have hpos : q twoEndedPosInfinity =
      q (Sum.inr ((0 : ℕ) : OnePoint ℕ)) :=
    tendsto_nhds_unique hposLim hconstRight
  have hall : ∀ x, q x = q (Sum.inr ((0 : ℕ) : OnePoint ℕ)) := by
    intro x
    rcases x with x | x
    · induction x using OnePoint.rec with
      | infty => exact hneg
      | coe n => exact hleft n
    · induction x using OnePoint.rec with
      | infty => exact hpos
      | coe n => exact hright n
  intro x y
  exact (hall x).trans (hall y).symm

/-- Analytic admission of the two limiting formations is total. -/
theorem twoEnded_analyticAdmission_total (x y : TwoEndedInt) :
    analyticAdmissionRel twoEndedJoinedUnitization x y := by
  rw [analyticAdmissionRel_iff_continuous_real_observers]
  intro f hf
  apply continuous_twoEnded_jointlyUnitizing_constant f
  · intro z
    exact (hf z (twoEndedEvenFormation z) (Or.inl rfl)).symm
  · intro z
    exact (hf z (twoEndedOddFormation z) (Or.inr rfl)).symm

/-- Algebraic reporter: `0` at the negative end, `1/2` on every integer, `1` at the positive end. -/
def twoEndedSetReporter : TwoEndedInt → ℝ
  | Sum.inl OnePoint.infty => 0
  | Sum.inl (_ : ℕ) => 1 / 2
  | Sum.inr OnePoint.infty => 1
  | Sum.inr (_ : ℕ) => 1 / 2

theorem twoEndedSetReporter_even (x : TwoEndedInt) :
    twoEndedSetReporter (twoEndedEvenFormation x) = twoEndedSetReporter x := by
  rcases x with x | x <;> induction x using OnePoint.rec <;> rfl

theorem twoEndedSetReporter_odd (x : TwoEndedInt) :
    twoEndedSetReporter (twoEndedOddFormation x) = twoEndedSetReporter x := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases hn : n = 0
        · subst n
          rw [twoEndedOddFormation_left_zero]
          rfl
        · rw [twoEndedOddFormation_left_of_ne_zero hn]
          rfl
  · induction x using OnePoint.rec <;> rfl

theorem twoEndedSetReporter_distinguishes_ends :
    twoEndedSetReporter twoEndedNegInfinity ≠
      twoEndedSetReporter twoEndedPosInfinity := by
  intro h
  change (0 : ℝ) = 1 at h
  linarith

theorem twoEndedSetReporter_not_continuous :
    ¬ Continuous twoEndedSetReporter := by
  intro h
  let q : C(TwoEndedInt, ℝ) := ⟨twoEndedSetReporter, h⟩
  exact twoEndedSetReporter_distinguishes_ends
    (continuous_twoEnded_jointlyUnitizing_constant q
      twoEndedSetReporter_even twoEndedSetReporter_odd
      twoEndedNegInfinity twoEndedPosInfinity)

theorem twoEnded_joinedUnitization_finite_connected_right (n : ℕ) :
    Relation.EqvGen twoEndedJoinedUnitization
      (Sum.inr (n : OnePoint ℕ))
      (Sum.inr ((0 : ℕ) : OnePoint ℕ)) := by
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
      have hadj : Relation.EqvGen twoEndedJoinedUnitization
          (Sum.inr (n + 1 : ℕ)) (Sum.inr (n : OnePoint ℕ)) := by
        rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
        · apply Relation.EqvGen.rel
          left
          rw [twoEndedEvenFormation_right, lowerEven_two_mul_add_one]
        · apply Relation.EqvGen.symm
          apply Relation.EqvGen.rel
          right
          rw [twoEndedOddFormation_right, upperEvenIndex_two_mul_add_one]
      exact Relation.EqvGen.trans _ _ _ hadj ih

theorem twoEnded_joinedUnitization_finite_connected_left (n : ℕ) :
    Relation.EqvGen twoEndedJoinedUnitization
      (Sum.inl (n : OnePoint ℕ))
      (Sum.inr ((0 : ℕ) : OnePoint ℕ)) := by
  have hbridge : Relation.EqvGen twoEndedJoinedUnitization
      (Sum.inl ((0 : ℕ) : OnePoint ℕ))
      (Sum.inr ((0 : ℕ) : OnePoint ℕ)) :=
    Relation.EqvGen.rel _ _ (Or.inr rfl)
  induction n with
  | zero => exact hbridge
  | succ n ih =>
      have hadj : Relation.EqvGen twoEndedJoinedUnitization
          (Sum.inl (n + 1 : ℕ)) (Sum.inl (n : OnePoint ℕ)) := by
        rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
        · apply Relation.EqvGen.symm
          apply Relation.EqvGen.rel
          left
          rw [twoEndedEvenFormation_left, upperOddIndex_two_mul]
        · apply Relation.EqvGen.rel
          right
          rw [twoEndedOddFormation_left_of_ne_zero]
          · rw [lowerOdd_two_mul_add_two]
          · exact Nat.succ_ne_zero _
      exact Relation.EqvGen.trans _ _ _ hadj ih

/-- Predicate selecting the embedded integer locus. -/
def IsTwoEndedFinite : TwoEndedInt → Prop
  | Sum.inl OnePoint.infty => False
  | Sum.inl (_ : ℕ) => True
  | Sum.inr OnePoint.infty => False
  | Sum.inr (_ : ℕ) => True

/-- The algebraic join has exactly three classes: all integers and the two singleton ends. -/
theorem twoEnded_joinedUnitization_eqvGen_iff (x y : TwoEndedInt) :
    Relation.EqvGen twoEndedJoinedUnitization x y ↔
      (IsTwoEndedFinite x ∧ IsTwoEndedFinite y) ∨
      (x = twoEndedNegInfinity ∧ y = twoEndedNegInfinity) ∨
      (x = twoEndedPosInfinity ∧ y = twoEndedPosInfinity) := by
  constructor
  · intro hxy
    have hreport : twoEndedSetReporter x = twoEndedSetReporter y :=
      eqvGen_observer_eq twoEndedSetReporter
        (fun a b hab => hab.elim
          (fun h => h ▸ (twoEndedSetReporter_even a).symm)
          (fun h => h ▸ (twoEndedSetReporter_odd a).symm)) x y hxy
    rcases x with x | x <;> rcases y with y | y
    all_goals induction x using OnePoint.rec <;> induction y using OnePoint.rec
    all_goals simp [IsTwoEndedFinite, twoEndedNegInfinity, twoEndedPosInfinity,
      twoEndedSetReporter] at hreport ⊢
  · rintro (⟨hx, hy⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rcases x with x | x <;> rcases y with y | y
      all_goals induction x using OnePoint.rec <;> induction y using OnePoint.rec
      all_goals simp [IsTwoEndedFinite] at hx hy
      all_goals first
        | exact Relation.EqvGen.trans _ _ _
            (twoEnded_joinedUnitization_finite_connected_left _)
            (Relation.EqvGen.symm _ _
              (twoEnded_joinedUnitization_finite_connected_left _))
        | exact Relation.EqvGen.trans _ _ _
            (twoEnded_joinedUnitization_finite_connected_left _)
            (Relation.EqvGen.symm _ _
              (twoEnded_joinedUnitization_finite_connected_right _))
        | exact Relation.EqvGen.trans _ _ _
            (twoEnded_joinedUnitization_finite_connected_right _)
            (Relation.EqvGen.symm _ _
              (twoEnded_joinedUnitization_finite_connected_left _))
        | exact Relation.EqvGen.trans _ _ _
            (twoEnded_joinedUnitization_finite_connected_right _)
            (Relation.EqvGen.symm _ _
              (twoEnded_joinedUnitization_finite_connected_right _))
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.refl _

/-! ## Exact finite truncations -/

theorem upperOddIndex_div_two (n : ℕ) :
    upperOddIndex n / 2 = n / 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [upperOddIndex_two_mul]
    simp [Nat.mul_add_div (m := 2) (by linarith) k 1]
  · rw [upperOddIndex_two_mul_add_one]

theorem lowerEven_div_two (n : ℕ) : lowerEven n / 2 = n / 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [lowerEven_two_mul]
  · rw [lowerEven_two_mul_add_one]
    simp [Nat.mul_add_div (m := 2) (by linarith) k 1]

theorem lowerOdd_pred_div_two {n : ℕ} (hn : n ≠ 0) :
    (lowerOdd n - 1) / 2 = (n - 1) / 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · cases k with
    | zero => exact (hn rfl).elim
    | succ k =>
        rw [show 2 * (k + 1) = 2 * k + 2 by ring,
          lowerOdd_two_mul_add_two]
        simp [Nat.mul_add_div (m := 2) (by linarith) k 1]
  · rw [lowerOdd_two_mul_add_one]

theorem upperEven_pred_div_two {n : ℕ} (hn : n ≠ 0) :
    (upperEvenIndex n - 1) / 2 = (n - 1) / 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · cases k with
    | zero => exact (hn rfl).elim
    | succ k =>
        rw [upperEvenIndex_two_mul]
  · rw [upperEvenIndex_two_mul_add_one]
    simp [Nat.mul_add_div (m := 2) (by linarith) k 1]

theorem upperEvenIndex_ne_zero {n : ℕ} (hn : n ≠ 0) :
    upperEvenIndex n ≠ 0 := by
  intro h
  have := le_upperEvenIndex n
  rw [h] at this
  exact hn (Nat.eq_zero_of_le_zero this)

theorem eventually_not_div_two_lt (B : ℕ) :
    ∀ᶠ n : ℕ in cofinite, ¬ n / 2 < B := by
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (2 * B)] with n hn
  intro hdiv
  have hnlt : n < B * 2 :=
    (Nat.div_lt_iff_lt_mul (by linarith : 0 < 2)).mp hdiv
  exact (not_lt_of_ge (by simpa [Nat.mul_comm] using hn)) hnlt

theorem eventually_not_pred_div_two_lt (B : ℕ) :
    ∀ᶠ n : ℕ in cofinite, n ≠ 0 ∧ ¬ (n - 1) / 2 < B := by
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (2 * B + 1)] with n hn
  have hn0 : n ≠ 0 := by
    intro hzero
    subst n
    exact (by linarith : ¬ 2 * B + 1 ≤ 0) hn
  refine ⟨hn0, ?_⟩
  intro hdiv
  have hpredlt : n - 1 < B * 2 :=
    (Nat.div_lt_iff_lt_mul (by linarith : 0 < 2)).mp hdiv
  have hpredge : B * 2 ≤ n - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.mul_comm, Nat.add_comm] using hn
  exact (not_lt_of_ge hpredge) hpredlt

/-- Finite even formation on the negative ray. -/
def finiteEvenLeftIndex (N n : ℕ) : ℕ :=
  if n / 2 < N then upperOddIndex n else n

/-- Finite even formation on the nonnegative ray. -/
def finiteEvenRightIndex (N n : ℕ) : ℕ :=
  if n / 2 < N + 1 then lowerEven n else n

/-- Finite odd formation on a nonzero negative-ray index. -/
def finiteOddLeftIndex (N n : ℕ) : ℕ :=
  if (n - 1) / 2 < N then lowerOdd n else n

/-- Finite odd formation on the nonnegative ray. -/
def finiteOddRightIndex (N n : ℕ) : ℕ :=
  if n = 0 then 0
  else if (n - 1) / 2 < N then upperEvenIndex n else n

theorem finiteEvenLeftIndex_idempotent (N n : ℕ) :
    finiteEvenLeftIndex N (finiteEvenLeftIndex N n) = finiteEvenLeftIndex N n := by
  by_cases h : n / 2 < N
  · simp [finiteEvenLeftIndex, h, upperOddIndex_div_two,
      upperOddIndex_idempotent]
  · simp [finiteEvenLeftIndex, h]

theorem finiteEvenRightIndex_idempotent (N n : ℕ) :
    finiteEvenRightIndex N (finiteEvenRightIndex N n) = finiteEvenRightIndex N n := by
  by_cases h : n / 2 < N + 1
  · simp [finiteEvenRightIndex, h, lowerEven_div_two,
      lowerEven_idempotent]
  · simp [finiteEvenRightIndex, h]

theorem finiteOddLeftIndex_idempotent
    (N : ℕ) {n : ℕ} (hn : n ≠ 0) :
    finiteOddLeftIndex N (finiteOddLeftIndex N n) = finiteOddLeftIndex N n := by
  by_cases h : (n - 1) / 2 < N
  · simp [finiteOddLeftIndex, h, lowerOdd_pred_div_two hn,
      lowerOdd_idempotent]
  · simp [finiteOddLeftIndex, h]

theorem finiteOddRightIndex_idempotent (N n : ℕ) :
    finiteOddRightIndex N (finiteOddRightIndex N n) = finiteOddRightIndex N n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · by_cases h : (n - 1) / 2 < N
    · simp [finiteOddRightIndex, hn, h, upperEven_pred_div_two hn,
        upperEvenIndex_ne_zero hn, upperEvenIndex_idempotent]
    · simp [finiteOddRightIndex, hn, h]

def finiteTwoEndedEvenLeftRay (N : ℕ) : C(OnePoint ℕ, TwoEndedInt) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => Sum.inl (finiteEvenLeftIndex N n : OnePoint ℕ))
    twoEndedNegInfinity
    (by
      apply tendsto_twoEnded_left_coe.congr'
      filter_upwards [eventually_not_div_two_lt N] with n hn
      simp [finiteEvenLeftIndex, hn])

def finiteTwoEndedEvenRightRay (N : ℕ) : C(OnePoint ℕ, TwoEndedInt) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => Sum.inr (finiteEvenRightIndex N n : OnePoint ℕ))
    twoEndedPosInfinity
    (by
      apply tendsto_twoEnded_right_coe.congr'
      filter_upwards [eventually_not_div_two_lt (N + 1)] with n hn
      simp [finiteEvenRightIndex, hn])

def finiteTwoEndedOddLeftRay (N : ℕ) : C(OnePoint ℕ, TwoEndedInt) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => if n = 0 then Sum.inr ((0 : ℕ) : OnePoint ℕ)
      else Sum.inl (finiteOddLeftIndex N n : OnePoint ℕ))
    twoEndedNegInfinity
    (by
      apply tendsto_twoEnded_left_coe.congr'
      filter_upwards [eventually_not_pred_div_two_lt N] with n hn
      simp [finiteOddLeftIndex, hn.1, hn.2])

def finiteTwoEndedOddRightRay (N : ℕ) : C(OnePoint ℕ, TwoEndedInt) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => Sum.inr (finiteOddRightIndex N n : OnePoint ℕ))
    twoEndedPosInfinity
    (by
      apply tendsto_twoEnded_right_coe.congr'
      filter_upwards [eventually_not_pred_div_two_lt N] with n hn
      simp [finiteOddRightIndex, hn.1, hn.2])

/-- Exact finite even formation: only pairs with `|k| ≤ N` are active. -/
def finiteTwoEndedEvenFormation (N : ℕ) : C(TwoEndedInt, TwoEndedInt) :=
  ⟨Sum.elim (finiteTwoEndedEvenLeftRay N) (finiteTwoEndedEvenRightRay N),
    (finiteTwoEndedEvenLeftRay N).continuous.sumElim
      (finiteTwoEndedEvenRightRay N).continuous⟩

/-- Exact finite odd formation: only pairs with `|k| ≤ N` are active. -/
def finiteTwoEndedOddFormation (N : ℕ) : C(TwoEndedInt, TwoEndedInt) :=
  ⟨Sum.elim (finiteTwoEndedOddLeftRay N) (finiteTwoEndedOddRightRay N),
    (finiteTwoEndedOddLeftRay N).continuous.sumElim
      (finiteTwoEndedOddRightRay N).continuous⟩

@[simp] theorem finiteTwoEndedEvenFormation_negInfinity (N : ℕ) :
    finiteTwoEndedEvenFormation N twoEndedNegInfinity = twoEndedNegInfinity := rfl

@[simp] theorem finiteTwoEndedEvenFormation_posInfinity (N : ℕ) :
    finiteTwoEndedEvenFormation N twoEndedPosInfinity = twoEndedPosInfinity := rfl

@[simp] theorem finiteTwoEndedOddFormation_negInfinity (N : ℕ) :
    finiteTwoEndedOddFormation N twoEndedNegInfinity = twoEndedNegInfinity := rfl

@[simp] theorem finiteTwoEndedOddFormation_posInfinity (N : ℕ) :
    finiteTwoEndedOddFormation N twoEndedPosInfinity = twoEndedPosInfinity := rfl

@[simp] theorem finiteTwoEndedEvenFormation_left (N n : ℕ) :
    finiteTwoEndedEvenFormation N (Sum.inl (n : OnePoint ℕ)) =
      Sum.inl (finiteEvenLeftIndex N n : OnePoint ℕ) := rfl

@[simp] theorem finiteTwoEndedEvenFormation_right (N n : ℕ) :
    finiteTwoEndedEvenFormation N (Sum.inr (n : OnePoint ℕ)) =
      Sum.inr (finiteEvenRightIndex N n : OnePoint ℕ) := rfl

@[simp] theorem finiteTwoEndedOddFormation_left_zero (N : ℕ) :
    finiteTwoEndedOddFormation N (Sum.inl ((0 : ℕ) : OnePoint ℕ)) =
      Sum.inr ((0 : ℕ) : OnePoint ℕ) := rfl

@[simp] theorem finiteTwoEndedOddFormation_left_of_ne_zero
    (N : ℕ) {n : ℕ} (hn : n ≠ 0) :
    finiteTwoEndedOddFormation N (Sum.inl (n : OnePoint ℕ)) =
      Sum.inl (finiteOddLeftIndex N n : OnePoint ℕ) := by
  change (if n = 0 then Sum.inr ((0 : ℕ) : OnePoint ℕ)
    else Sum.inl (finiteOddLeftIndex N n : OnePoint ℕ)) = _
  rw [if_neg hn]

@[simp] theorem finiteTwoEndedOddFormation_right (N n : ℕ) :
    finiteTwoEndedOddFormation N (Sum.inr (n : OnePoint ℕ)) =
      Sum.inr (finiteOddRightIndex N n : OnePoint ℕ) := rfl

theorem finiteTwoEndedEvenFormation_idempotent (N : ℕ) (x : TwoEndedInt) :
    finiteTwoEndedEvenFormation N (finiteTwoEndedEvenFormation N x) =
      finiteTwoEndedEvenFormation N x := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n => simp [finiteEvenLeftIndex_idempotent]
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n => simp [finiteEvenRightIndex_idempotent]

theorem finiteTwoEndedOddFormation_idempotent (N : ℕ) (x : TwoEndedInt) :
    finiteTwoEndedOddFormation N (finiteTwoEndedOddFormation N x) =
      finiteTwoEndedOddFormation N x := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases hn : n = 0
        · subst n
          rfl
        · have hout : finiteOddLeftIndex N n ≠ 0 := by
            by_cases h : (n - 1) / 2 < N
            · simpa [finiteOddLeftIndex, h] using lowerOdd_ne_zero hn
            · simpa [finiteOddLeftIndex, h] using hn
          rw [finiteTwoEndedOddFormation_left_of_ne_zero N hn,
            finiteTwoEndedOddFormation_left_of_ne_zero N hout,
            finiteOddLeftIndex_idempotent N hn]
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n => simp [finiteOddRightIndex_idempotent]

/-! ## Finite reporters and exact analytic gap -/

def finiteTwoEndedReporterLeft (N : ℕ) : C(OnePoint ℕ, ℝ) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => if n ≤ 2 * N then 1 / 2 else 0) 0 (by
      rw [Nat.cofinite_eq_atTop]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (2 * N)] with n hn
      simp [Nat.not_le.mpr hn])

def finiteTwoEndedReporterRight (N : ℕ) : C(OnePoint ℕ, ℝ) :=
  OnePoint.continuousMapMkDiscrete
    (fun n => if n ≤ 2 * N + 1 then 1 / 2 else 1) 1 (by
      rw [Nat.cofinite_eq_atTop]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (2 * N + 1)] with n hn
      simp [Nat.not_le.mpr hn])

/-- Exact finite-stage endpoint reporter from the paper. -/
def finiteTwoEndedReporter (N : ℕ) : C(TwoEndedInt, ℝ) :=
  ⟨Sum.elim (finiteTwoEndedReporterLeft N) (finiteTwoEndedReporterRight N),
    (finiteTwoEndedReporterLeft N).continuous.sumElim
      (finiteTwoEndedReporterRight N).continuous⟩

@[simp] theorem finiteTwoEndedReporter_negInfinity (N : ℕ) :
    finiteTwoEndedReporter N twoEndedNegInfinity = 0 := rfl

@[simp] theorem finiteTwoEndedReporter_posInfinity (N : ℕ) :
    finiteTwoEndedReporter N twoEndedPosInfinity = 1 := rfl

@[simp] theorem finiteTwoEndedReporter_left (N n : ℕ) :
    finiteTwoEndedReporter N (Sum.inl (n : OnePoint ℕ)) =
      if n ≤ 2 * N then 1 / 2 else 0 := rfl

@[simp] theorem finiteTwoEndedReporter_right (N n : ℕ) :
    finiteTwoEndedReporter N (Sum.inr (n : OnePoint ℕ)) =
      if n ≤ 2 * N + 1 then 1 / 2 else 1 := rfl

theorem finiteEvenLeftIndex_central
    {N n : ℕ} (h : n / 2 < N) :
    n ≤ 2 * N ∧ finiteEvenLeftIndex N n ≤ 2 * N := by
  have hraw : n < N * 2 :=
    (Nat.div_lt_iff_lt_mul (by linarith : 0 < 2)).mp h
  have hn : n ≤ 2 * N := by
    simpa [Nat.mul_comm] using Nat.le_of_lt hraw
  have hsucc : n / 2 + 1 ≤ N := Nat.succ_le_iff.mpr h
  have hmul := Nat.mul_le_mul_left 2 hsucc
  have hout : upperOddIndex n ≤ 2 * N := by
    change 2 * (n / 2) + 1 ≤ 2 * N
    linarith
  exact ⟨hn, by simp [finiteEvenLeftIndex, h, hout]⟩

theorem finiteEvenRightIndex_central
    {N n : ℕ} (h : n / 2 < N + 1) :
    n ≤ 2 * N + 1 ∧ finiteEvenRightIndex N n ≤ 2 * N + 1 := by
  have hraw : n < (N + 1) * 2 :=
    (Nat.div_lt_iff_lt_mul (by linarith : 0 < 2)).mp h
  have hn : n ≤ 2 * N + 1 := by linarith
  refine ⟨hn, ?_⟩
  rw [finiteEvenRightIndex, if_pos h]
  exact (lowerEven_le n).trans hn

theorem finiteOddLeftIndex_central
    {N n : ℕ} (hn : n ≠ 0) (h : (n - 1) / 2 < N) :
    n ≤ 2 * N ∧ finiteOddLeftIndex N n ≤ 2 * N := by
  have hraw : n - 1 < N * 2 :=
    (Nat.div_lt_iff_lt_mul (by linarith : 0 < 2)).mp h
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)
  have hnle : n ≤ 2 * N := by linarith
  refine ⟨hnle, ?_⟩
  rw [finiteOddLeftIndex, if_pos h]
  exact (lowerOdd_le n).trans hnle

theorem upperEvenIndex_le_succ (n : ℕ) : upperEvenIndex n ≤ n + 1 := by
  unfold upperEvenIndex
  simpa [Nat.mul_comm] using Nat.div_mul_le_self (n + 1) 2

theorem finiteOddRightIndex_central
    {N n : ℕ} (hn : n ≠ 0) (h : (n - 1) / 2 < N) :
    n ≤ 2 * N + 1 ∧ finiteOddRightIndex N n ≤ 2 * N + 1 := by
  have hraw : n - 1 < N * 2 :=
    (Nat.div_lt_iff_lt_mul (by linarith : 0 < 2)).mp h
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)
  have hnle : n ≤ 2 * N := by linarith
  have hout : upperEvenIndex n ≤ 2 * N + 1 := by
    exact (upperEvenIndex_le_succ n).trans (by linarith)
  refine ⟨hnle.trans (Nat.le_add_right (2 * N) 1), ?_⟩
  rw [finiteOddRightIndex, if_neg hn, if_pos h]
  exact hout

theorem finiteTwoEndedReporter_unitizes_even (N : ℕ) (x : TwoEndedInt) :
    finiteTwoEndedReporter N (finiteTwoEndedEvenFormation N x) =
      finiteTwoEndedReporter N x := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases h : n / 2 < N
        · obtain ⟨hn, hout⟩ := finiteEvenLeftIndex_central h
          have hactual : upperOddIndex n ≤ 2 * N := by
            simpa [finiteEvenLeftIndex, h] using hout
          rw [finiteTwoEndedEvenFormation_left,
            finiteTwoEndedReporter_left, finiteTwoEndedReporter_left,
            finiteEvenLeftIndex, if_pos h, if_pos hn, if_pos hactual]
        · simp [finiteEvenLeftIndex, h]
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases h : n / 2 < N + 1
        · obtain ⟨hn, hout⟩ := finiteEvenRightIndex_central h
          have hactual : lowerEven n ≤ 2 * N + 1 := by
            simpa [finiteEvenRightIndex, h] using hout
          rw [finiteTwoEndedEvenFormation_right,
            finiteTwoEndedReporter_right, finiteTwoEndedReporter_right,
            finiteEvenRightIndex, if_pos h, if_pos hn, if_pos hactual]
        · simp [finiteEvenRightIndex, h]

theorem finiteTwoEndedReporter_unitizes_odd (N : ℕ) (x : TwoEndedInt) :
    finiteTwoEndedReporter N (finiteTwoEndedOddFormation N x) =
      finiteTwoEndedReporter N x := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases hn : n = 0
        · subst n
          simp
        · by_cases h : (n - 1) / 2 < N
          · obtain ⟨hnle, hout⟩ := finiteOddLeftIndex_central hn h
            have hactual : lowerOdd n ≤ 2 * N := by
              simpa [finiteOddLeftIndex, h] using hout
            rw [finiteTwoEndedOddFormation_left_of_ne_zero N hn,
              finiteTwoEndedReporter_left, finiteTwoEndedReporter_left,
              finiteOddLeftIndex, if_pos h, if_pos hnle, if_pos hactual]
          · simp [finiteTwoEndedOddFormation_left_of_ne_zero N hn,
              finiteOddLeftIndex, h]
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases hn : n = 0
        · subst n
          simp [finiteOddRightIndex]
        · by_cases h : (n - 1) / 2 < N
          · obtain ⟨hnle, hout⟩ := finiteOddRightIndex_central hn h
            have hactual : upperEvenIndex n ≤ 2 * N + 1 := by
              simpa [finiteOddRightIndex, hn, h] using hout
            rw [finiteTwoEndedOddFormation_right,
              finiteTwoEndedReporter_right, finiteTwoEndedReporter_right,
              finiteOddRightIndex, if_neg hn, if_pos h, if_pos hnle, if_pos hactual]
          · simp [finiteOddRightIndex, hn, h]

theorem finiteTwoEndedReporter_exact_margin (N : ℕ) :
    finiteTwoEndedReporter N twoEndedPosInfinity -
      finiteTwoEndedReporter N twoEndedNegInfinity = 1 := by
  rw [finiteTwoEndedReporter_posInfinity, finiteTwoEndedReporter_negInfinity]
  ring

theorem finiteTwoEndedReporter_eventually_eq_setReporter_left (n : ℕ) :
    ∀ N ≥ n,
      finiteTwoEndedReporter N (Sum.inl (n : OnePoint ℕ)) =
        twoEndedSetReporter (Sum.inl (n : OnePoint ℕ)) := by
  intro N hN
  have hNtwo : n ≤ 2 * N := by
    calc
      n ≤ N := hN
      _ ≤ N + N := Nat.le_add_right N N
      _ = 2 * N := by ring
  simp [hNtwo, twoEndedSetReporter]

theorem finiteTwoEndedReporter_eventually_eq_setReporter_right (n : ℕ) :
    ∀ N ≥ n,
      finiteTwoEndedReporter N (Sum.inr (n : OnePoint ℕ)) =
        twoEndedSetReporter (Sum.inr (n : OnePoint ℕ)) := by
  intro N hN
  have hNtwo : n ≤ 2 * N + 1 := by
    calc
      n ≤ N := hN
      _ ≤ N + N := Nat.le_add_right N N
      _ = 2 * N := by ring
      _ ≤ 2 * N + 1 := Nat.le_add_right (2 * N) 1
  simp [hNtwo, twoEndedSetReporter]

theorem finiteTwoEndedReporter_eq_setReporter_negInfinity (N : ℕ) :
    finiteTwoEndedReporter N twoEndedNegInfinity =
      twoEndedSetReporter twoEndedNegInfinity := rfl

theorem finiteTwoEndedReporter_eq_setReporter_posInfinity (N : ℕ) :
    finiteTwoEndedReporter N twoEndedPosInfinity =
      twoEndedSetReporter twoEndedPosInfinity := rfl

/-- Three-value uniform error; this equals the full supremum error because the reporter has exactly
these three values. -/
def twoEndedReporterUniformError (c : ℝ) : ℝ :=
  max |twoEndedSetReporter twoEndedNegInfinity - c|
    (max |twoEndedSetReporter (Sum.inr ((0 : ℕ) : OnePoint ℕ)) - c|
      |twoEndedSetReporter twoEndedPosInfinity - c|)

theorem twoEndedReporter_abs_error_le_uniformError (c : ℝ) (x : TwoEndedInt) :
    |twoEndedSetReporter x - c| ≤ twoEndedReporterUniformError c := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => exact le_max_left _ _
    | coe n => exact (le_max_left _ _).trans (le_max_right _ _)
  · induction x using OnePoint.rec with
    | infty => exact (le_max_right _ _).trans (le_max_right _ _)
    | coe n => exact (le_max_left _ _).trans (le_max_right _ _)

theorem twoEndedReporterUniformError_lower (c : ℝ) :
    (1 / 2 : ℝ) ≤ twoEndedReporterUniformError c := by
  have htri : (1 : ℝ) ≤ |(0 : ℝ) - c| + |(1 : ℝ) - c| := by
    calc
      (1 : ℝ) = |(-1 : ℝ)| := by simp
      _ = |((0 : ℝ) - c) + (c - 1)| := by
        congr 1
        ring
      _ ≤ |(0 : ℝ) - c| + |c - 1| := abs_add_le _ _
      _ = |(0 : ℝ) - c| + |(1 : ℝ) - c| := by rw [abs_sub_comm c 1]
  have h0 : |(0 : ℝ) - c| ≤ twoEndedReporterUniformError c :=
    le_max_left _ _
  have h1 : |(1 : ℝ) - c| ≤ twoEndedReporterUniformError c :=
    (le_max_right _ _).trans (le_max_right _ _)
  change |(0 : ℝ) - c| ≤ max |(0 : ℝ) - c|
    (max |(1 / 2 : ℝ) - c| |(1 : ℝ) - c|) at h0
  change |(1 : ℝ) - c| ≤ max |(0 : ℝ) - c|
    (max |(1 / 2 : ℝ) - c| |(1 : ℝ) - c|) at h1
  change (1 / 2 : ℝ) ≤ max |(0 : ℝ) - c|
    (max |(1 / 2 : ℝ) - c| |(1 : ℝ) - c|)
  linarith

theorem twoEndedReporterUniformError_half :
    twoEndedReporterUniformError (1 / 2 : ℝ) = 1 / 2 := by
  have h0 : |(0 : ℝ) - 1 / 2| = 1 / 2 := by
    rw [abs_of_nonpos (by linarith)]
    ring
  have hm : |(1 / 2 : ℝ) - 1 / 2| = 0 := by
    rw [sub_self, abs_zero]
  have h1 : |(1 : ℝ) - 1 / 2| = 1 / 2 := by
    rw [abs_of_nonneg (by linarith)]
    ring
  change max |(0 : ℝ) - 1 / 2|
    (max |(1 / 2 : ℝ) - 1 / 2| |(1 : ℝ) - 1 / 2|) = 1 / 2
  rw [h0, hm, h1]
  simp

/-- Exact boxed infimum law from the paper. -/
theorem twoEndedReporterUniformError_sInf :
    sInf (Set.range twoEndedReporterUniformError) = 1 / 2 := by
  have hleast : IsLeast (Set.range twoEndedReporterUniformError) (1 / 2 : ℝ) := by
    constructor
    · exact ⟨1 / 2, twoEndedReporterUniformError_half⟩
    · rintro _ ⟨c, rfl⟩
      exact twoEndedReporterUniformError_lower c
  exact hleast.csInf_eq

theorem finiteTwoEndedReporter_not_equicontinuousAt_posInfinity :
    ¬ EquicontinuousAt (fun N : ℕ => (finiteTwoEndedReporter N : TwoEndedInt → ℝ))
      twoEndedPosInfinity := by
  intro hEq
  rw [Metric.equicontinuousAt_iff_right] at hEq
  have hnear := hEq (1 / 4) (by linarith)
  have hseq := tendsto_twoEnded_right_coe.eventually hnear
  obtain ⟨n, hn⟩ := hseq.exists
  have hspec := hn n
  have hnle : n ≤ 2 * n + 1 := by
    calc
      n ≤ n + n := Nat.le_add_right n n
      _ = 2 * n := by ring
      _ ≤ 2 * n + 1 := Nat.le_add_right (2 * n) 1
  change dist (1 : ℝ) (if n ≤ 2 * n + 1 then 1 / 2 else 1) < 1 / 4 at hspec
  rw [if_pos hnle, Real.dist_eq] at hspec
  have habs : |(1 : ℝ) - 1 / 2| = 1 / 2 := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [habs] at hspec
  linarith

theorem finiteTwoEndedReporter_not_equicontinuousAt_negInfinity :
    ¬ EquicontinuousAt (fun N : ℕ => (finiteTwoEndedReporter N : TwoEndedInt → ℝ))
      twoEndedNegInfinity := by
  intro hEq
  rw [Metric.equicontinuousAt_iff_right] at hEq
  have hnear := hEq (1 / 4) (by linarith)
  have hseq := tendsto_twoEnded_left_coe.eventually hnear
  obtain ⟨n, hn⟩ := hseq.exists
  have hspec := hn n
  have hnle : n ≤ 2 * n := by
    simp [two_mul]
  change dist (0 : ℝ) (if n ≤ 2 * n then 1 / 2 else 0) < 1 / 4 at hspec
  rw [if_pos hnle, Real.dist_eq] at hspec
  have habs : |(0 : ℝ) - 1 / 2| = 1 / 2 := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [habs] at hspec
  linarith

/-! ## Exact finite joined classes -/

/-- Fibre equivalence of the finite even formation. -/
def finiteTwoEndedEvenSetoid (N : ℕ) : Setoid TwoEndedInt :=
  Setoid.ker (finiteTwoEndedEvenFormation N)

/-- Fibre equivalence of the finite odd formation. -/
def finiteTwoEndedOddSetoid (N : ℕ) : Setoid TwoEndedInt :=
  Setoid.ker (finiteTwoEndedOddFormation N)

theorem finiteTwoEndedEvenSetoid_isClosed (N : ℕ) :
    IsClosedAdmissionSetoid (finiteTwoEndedEvenSetoid N) := by
  change IsClosed {p : TwoEndedInt × TwoEndedInt |
    finiteTwoEndedEvenFormation N p.1 = finiteTwoEndedEvenFormation N p.2}
  exact isClosed_eq
    ((finiteTwoEndedEvenFormation N).continuous.comp continuous_fst)
    ((finiteTwoEndedEvenFormation N).continuous.comp continuous_snd)

theorem finiteTwoEndedOddSetoid_isClosed (N : ℕ) :
    IsClosedAdmissionSetoid (finiteTwoEndedOddSetoid N) := by
  change IsClosed {p : TwoEndedInt × TwoEndedInt |
    finiteTwoEndedOddFormation N p.1 = finiteTwoEndedOddFormation N p.2}
  exact isClosed_eq
    ((finiteTwoEndedOddFormation N).continuous.comp continuous_fst)
    ((finiteTwoEndedOddFormation N).continuous.comp continuous_snd)

/-- The exact finite interval `I_N = {-2N-1, ..., 2N+1}` in split-ray coordinates. -/
def IsFiniteTwoEndedCentral (N : ℕ) : TwoEndedInt → Prop
  | Sum.inl OnePoint.infty => False
  | Sum.inl (n : ℕ) => n ≤ 2 * N
  | Sum.inr OnePoint.infty => False
  | Sum.inr (n : ℕ) => n ≤ 2 * N + 1

theorem isFiniteTwoEndedCentral_iff_reporter_half (N : ℕ) (x : TwoEndedInt) :
    IsFiniteTwoEndedCentral N x ↔ finiteTwoEndedReporter N x = 1 / 2 := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty =>
        change False ↔ (0 : ℝ) = 1 / 2
        constructor <;> intro h
        · exact h.elim
        · linarith
    | coe n => simp [IsFiniteTwoEndedCentral]
  · induction x using OnePoint.rec with
    | infty =>
        change False ↔ (1 : ℝ) = 1 / 2
        constructor <;> intro h
        · exact h.elim
        · linarith
    | coe n => simp [IsFiniteTwoEndedCentral]

theorem finiteTwoEndedEvenFormation_eq_self_of_not_central
    (N : ℕ) {x : TwoEndedInt} (hx : ¬ IsFiniteTwoEndedCentral N x) :
    finiteTwoEndedEvenFormation N x = x := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases h : n / 2 < N
        · exact (hx (by
            simp only [IsFiniteTwoEndedCentral]
            exact (finiteEvenLeftIndex_central h).1)).elim
        · simp [finiteEvenLeftIndex, h]
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases h : n / 2 < N + 1
        · exact (hx (by
            simp only [IsFiniteTwoEndedCentral]
            exact (finiteEvenRightIndex_central h).1)).elim
        · simp [finiteEvenRightIndex, h]

theorem finiteTwoEndedOddFormation_eq_self_of_not_central
    (N : ℕ) {x : TwoEndedInt} (hx : ¬ IsFiniteTwoEndedCentral N x) :
    finiteTwoEndedOddFormation N x = x := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases hn : n = 0
        · subst n
          exact (hx (by simp [IsFiniteTwoEndedCentral])).elim
        · by_cases h : (n - 1) / 2 < N
          · exact (hx (by
              simp only [IsFiniteTwoEndedCentral]
              exact (finiteOddLeftIndex_central hn h).1)).elim
          · simp [finiteTwoEndedOddFormation_left_of_ne_zero N hn,
              finiteOddLeftIndex, h]
  · induction x using OnePoint.rec with
    | infty => rfl
    | coe n =>
        by_cases hn : n = 0
        · subst n
          simp [finiteOddRightIndex]
        · by_cases h : (n - 1) / 2 < N
          · exact (hx (by
              simp only [IsFiniteTwoEndedCentral]
              exact (finiteOddRightIndex_central hn h).1)).elim
          · simp [finiteOddRightIndex, hn, h]

theorem finiteTwoEndedSetoid_union_eq_or_central
    (N : ℕ) {x y : TwoEndedInt}
    (hxy : finiteTwoEndedEvenSetoid N x y ∨ finiteTwoEndedOddSetoid N x y) :
    x = y ∨ (IsFiniteTwoEndedCentral N x ∧ IsFiniteTwoEndedCentral N y) := by
  have classify
      (f : TwoEndedInt → TwoEndedInt)
      (hunit : ∀ z, finiteTwoEndedReporter N (f z) = finiteTwoEndedReporter N z)
      (hfix : ∀ {z}, ¬ IsFiniteTwoEndedCentral N z → f z = z)
      (hker : f x = f y) :
      x = y ∨ (IsFiniteTwoEndedCentral N x ∧ IsFiniteTwoEndedCentral N y) := by
    have hreport : finiteTwoEndedReporter N x = finiteTwoEndedReporter N y :=
      (hunit x).symm.trans ((congrArg (finiteTwoEndedReporter N) hker).trans (hunit y))
    by_cases hx : IsFiniteTwoEndedCentral N x
    · right
      refine ⟨hx, (isFiniteTwoEndedCentral_iff_reporter_half N y).2 ?_⟩
      exact hreport.symm.trans ((isFiniteTwoEndedCentral_iff_reporter_half N x).1 hx)
    · by_cases hy : IsFiniteTwoEndedCentral N y
      · exact (hx ((isFiniteTwoEndedCentral_iff_reporter_half N x).2
          (hreport.trans ((isFiniteTwoEndedCentral_iff_reporter_half N y).1 hy)))).elim
      · left
        exact (hfix hx).symm.trans (hker.trans (hfix hy))
  rcases hxy with he | ho
  · exact classify (finiteTwoEndedEvenFormation N)
      (finiteTwoEndedReporter_unitizes_even N)
      (finiteTwoEndedEvenFormation_eq_self_of_not_central N) he
  · exact classify (finiteTwoEndedOddFormation N)
      (finiteTwoEndedReporter_unitizes_odd N)
      (finiteTwoEndedOddFormation_eq_self_of_not_central N) ho

theorem finiteTwoEndedSetoid_union_right_adjacent
    (N n : ℕ) (hn : n ≤ 2 * N) :
    finiteTwoEndedEvenSetoid N
        (Sum.inr (n : OnePoint ℕ)) (Sum.inr (n + 1 : ℕ)) ∨
      finiteTwoEndedOddSetoid N
        (Sum.inr (n : OnePoint ℕ)) (Sum.inr (n + 1 : ℕ)) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    have hk : k < N + 1 := by linarith
    have hk' : k ≤ N := Nat.lt_succ_iff.mp hk
    change finiteTwoEndedEvenFormation N (Sum.inr ((2 * k : ℕ) : OnePoint ℕ)) =
      finiteTwoEndedEvenFormation N (Sum.inr ((2 * k + 1 : ℕ) : OnePoint ℕ))
    rw [finiteTwoEndedEvenFormation_right, finiteTwoEndedEvenFormation_right]
    congr 2
    simp only [finiteEvenRightIndex]
    rw [if_pos (by simpa using hk), if_pos (by
      simpa [Nat.mul_add_div (m := 2) (by linarith) k 1] using hk)]
    rw [lowerEven_two_mul, lowerEven_two_mul_add_one]
  · right
    have hk : k < N := by linarith
    change finiteTwoEndedOddFormation N (Sum.inr ((2 * k + 1 : ℕ) : OnePoint ℕ)) =
      finiteTwoEndedOddFormation N (Sum.inr ((2 * k + 1 + 1 : ℕ) : OnePoint ℕ))
    rw [finiteTwoEndedOddFormation_right, finiteTwoEndedOddFormation_right]
    congr 2
    simp [finiteOddRightIndex, hk,
      show 2 * k + 1 + 1 = 2 * (k + 1) by ring]

theorem finiteTwoEndedSetoid_union_left_adjacent
    (N n : ℕ) (hn : n < 2 * N) :
    finiteTwoEndedEvenSetoid N
        (Sum.inl (n + 1 : ℕ)) (Sum.inl (n : OnePoint ℕ)) ∨
      finiteTwoEndedOddSetoid N
        (Sum.inl (n + 1 : ℕ)) (Sum.inl (n : OnePoint ℕ)) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    have hk : k < N := by linarith
    change finiteTwoEndedEvenFormation N (Sum.inl ((2 * k + 1 : ℕ) : OnePoint ℕ)) =
      finiteTwoEndedEvenFormation N (Sum.inl ((2 * k : ℕ) : OnePoint ℕ))
    rw [finiteTwoEndedEvenFormation_left, finiteTwoEndedEvenFormation_left]
    congr 2
    simp [finiteEvenLeftIndex, hk]
  · right
    have hk : k < N := by linarith
    have hkdiv : (2 * k + 1) / 2 < N := by
      simpa [Nat.mul_add_div (m := 2) (by linarith) k 1] using hk
    have hne : 2 * k + 1 + 1 ≠ 0 := by linarith
    have hne' : 2 * k + 1 ≠ 0 := by linarith
    change finiteTwoEndedOddFormation N (Sum.inl ((2 * k + 1 + 1 : ℕ) : OnePoint ℕ)) =
      finiteTwoEndedOddFormation N (Sum.inl ((2 * k + 1 : ℕ) : OnePoint ℕ))
    rw [finiteTwoEndedOddFormation_left_of_ne_zero N hne,
      finiteTwoEndedOddFormation_left_of_ne_zero N hne']
    congr 2
    simp [finiteOddLeftIndex, hk, hkdiv,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring]
    rw [lowerOdd_two_mul_add_two, lowerOdd_two_mul_add_one]

theorem finiteTwoEndedSetoid_union_bridge (N : ℕ) :
    finiteTwoEndedEvenSetoid N
        (Sum.inl ((0 : ℕ) : OnePoint ℕ)) (Sum.inr ((0 : ℕ) : OnePoint ℕ)) ∨
      finiteTwoEndedOddSetoid N
        (Sum.inl ((0 : ℕ) : OnePoint ℕ)) (Sum.inr ((0 : ℕ) : OnePoint ℕ)) := by
  right
  rfl

theorem finiteTwoEnded_join_connected_right
    (N n : ℕ) (hn : n ≤ 2 * N + 1) :
    Relation.EqvGen
      (fun x y => finiteTwoEndedEvenSetoid N x y ∨ finiteTwoEndedOddSetoid N x y)
      (Sum.inr (n : OnePoint ℕ)) (Sum.inr ((0 : ℕ) : OnePoint ℕ)) := by
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
      have hn' : n ≤ 2 * N := by linarith
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ (finiteTwoEndedSetoid_union_right_adjacent N n hn')))
        (ih (by linarith))

theorem finiteTwoEnded_join_connected_left
    (N n : ℕ) (hn : n ≤ 2 * N) :
    Relation.EqvGen
      (fun x y => finiteTwoEndedEvenSetoid N x y ∨ finiteTwoEndedOddSetoid N x y)
      (Sum.inl (n : OnePoint ℕ)) (Sum.inr ((0 : ℕ) : OnePoint ℕ)) := by
  have hbridge : Relation.EqvGen
      (fun x y => finiteTwoEndedEvenSetoid N x y ∨ finiteTwoEndedOddSetoid N x y)
      (Sum.inl ((0 : ℕ) : OnePoint ℕ)) (Sum.inr ((0 : ℕ) : OnePoint ℕ)) :=
    Relation.EqvGen.rel _ _ (finiteTwoEndedSetoid_union_bridge N)
  induction n with
  | zero => exact hbridge
  | succ n ih =>
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.rel _ _
          (finiteTwoEndedSetoid_union_left_adjacent N n (by linarith)))
        (ih (by linarith))

theorem finiteTwoEnded_join_connected_base
    (N : ℕ) {x : TwoEndedInt} (hx : IsFiniteTwoEndedCentral N x) :
    Relation.EqvGen
      (fun a b => finiteTwoEndedEvenSetoid N a b ∨ finiteTwoEndedOddSetoid N a b)
      x (Sum.inr ((0 : ℕ) : OnePoint ℕ)) := by
  rcases x with x | x <;> induction x using OnePoint.rec
  · simp [IsFiniteTwoEndedCentral] at hx
  · exact finiteTwoEnded_join_connected_left N _ hx
  · simp [IsFiniteTwoEndedCentral] at hx
  · exact finiteTwoEnded_join_connected_right N _ hx

/-- Exact finite-stage class law: `I_N` is the sole non-singleton class. -/
theorem finiteTwoEnded_join_eqvGen_iff (N : ℕ) (x y : TwoEndedInt) :
    Relation.EqvGen
        (fun a b => finiteTwoEndedEvenSetoid N a b ∨ finiteTwoEndedOddSetoid N a b) x y ↔
      x = y ∨ (IsFiniteTwoEndedCentral N x ∧ IsFiniteTwoEndedCentral N y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel x y hxy => exact finiteTwoEndedSetoid_union_eq_or_central N hxy
    | refl x => exact Or.inl rfl
    | symm x y _ ih =>
        exact ih.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2, h.1⟩)
    | trans x y z _ _ ihxy ihyz =>
        rcases ihxy with hxy | ⟨hx, hy⟩
        · subst y
          exact ihyz
        · rcases ihyz with hyz | ⟨-, hz⟩
          · subst z
            exact Or.inr ⟨hx, hy⟩
          · exact Or.inr ⟨hx, hz⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.trans _ _ _
        (finiteTwoEnded_join_connected_base N hx)
        (Relation.EqvGen.symm _ _ (finiteTwoEnded_join_connected_base N hy))

/-- The exact finite joined relation is closed, not merely observer-separable. -/
theorem finiteTwoEnded_join_isClosed (N : ℕ) :
    IsClosed (admissionRelationGraph
      (Relation.EqvGen
        (fun a b => finiteTwoEndedEvenSetoid N a b ∨ finiteTwoEndedOddSetoid N a b))) := by
  have hdiag : IsClosed {p : TwoEndedInt × TwoEndedInt | p.1 = p.2} :=
    isClosed_eq continuous_fst continuous_snd
  have hleft : IsClosed {p : TwoEndedInt × TwoEndedInt |
      finiteTwoEndedReporter N p.1 = (1 / 2 : ℝ)} :=
    isClosed_eq ((finiteTwoEndedReporter N).continuous.comp continuous_fst) continuous_const
  have hright : IsClosed {p : TwoEndedInt × TwoEndedInt |
      finiteTwoEndedReporter N p.2 = (1 / 2 : ℝ)} :=
    isClosed_eq ((finiteTwoEndedReporter N).continuous.comp continuous_snd) continuous_const
  rw [show admissionRelationGraph
      (Relation.EqvGen
        (fun a b => finiteTwoEndedEvenSetoid N a b ∨ finiteTwoEndedOddSetoid N a b)) =
      {p : TwoEndedInt × TwoEndedInt | p.1 = p.2} ∪
        ({p | finiteTwoEndedReporter N p.1 = (1 / 2 : ℝ)} ∩
          {p | finiteTwoEndedReporter N p.2 = (1 / 2 : ℝ)}) by
    ext p
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_inter_iff]
    change Relation.EqvGen
        (fun a b => finiteTwoEndedEvenSetoid N a b ∨ finiteTwoEndedOddSetoid N a b)
        p.1 p.2 ↔ _
    rw [finiteTwoEnded_join_eqvGen_iff,
      isFiniteTwoEndedCentral_iff_reporter_half,
      isFiniteTwoEndedCentral_iff_reporter_half]
    ]
  exact hdiag.union (hleft.inter hright)

/-! ## Exact alternating depth in the global model -/

/-- Symmetric primitive `E/F` edge relation used to measure alternating depth. -/
def twoEndedAlternationEdge (x y : TwoEndedInt) : Prop :=
  twoEndedEvenSetoid x y ∨ twoEndedOddSetoid x y

/-- Integer coordinate on the finite locus; endpoint values are irrelevant because every primitive
edge fixes each endpoint. -/
def twoEndedIntegerCoordinate : TwoEndedInt → ℤ
  | Sum.inl OnePoint.infty => 0
  | Sum.inl (n : ℕ) => -((n : ℤ) + 1)
  | Sum.inr OnePoint.infty => 0
  | Sum.inr (n : ℕ) => n

theorem twoEndedIntegerCoordinate_even_bounds (x : TwoEndedInt) :
    twoEndedIntegerCoordinate (twoEndedEvenFormation x) ≤ twoEndedIntegerCoordinate x ∧
      twoEndedIntegerCoordinate x ≤
        twoEndedIntegerCoordinate (twoEndedEvenFormation x) + 1 := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty =>
        change twoEndedIntegerCoordinate (twoEndedEvenFormation twoEndedNegInfinity) ≤ 0 ∧
          0 ≤ twoEndedIntegerCoordinate (twoEndedEvenFormation twoEndedNegInfinity) + 1
        rw [twoEndedEvenFormation_negInfinity]
        simp [twoEndedIntegerCoordinate, twoEndedNegInfinity]
    | coe n =>
        rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
        · rw [twoEndedEvenFormation_left, upperOddIndex_two_mul]
          change -(((2 * k + 1 : ℕ) : ℤ) + 1) ≤ -(((2 * k : ℕ) : ℤ) + 1) ∧
            -(((2 * k : ℕ) : ℤ) + 1) ≤ -(((2 * k + 1 : ℕ) : ℤ) + 1) + 1
          push_cast
          constructor <;> linarith
        · rw [twoEndedEvenFormation_left, upperOddIndex_two_mul_add_one]
          change -(((2 * k + 1 : ℕ) : ℤ) + 1) ≤ -(((2 * k + 1 : ℕ) : ℤ) + 1) ∧
            -(((2 * k + 1 : ℕ) : ℤ) + 1) ≤ -(((2 * k + 1 : ℕ) : ℤ) + 1) + 1
          constructor <;> linarith
  · induction x using OnePoint.rec with
    | infty =>
        change twoEndedIntegerCoordinate (twoEndedEvenFormation twoEndedPosInfinity) ≤ 0 ∧
          0 ≤ twoEndedIntegerCoordinate (twoEndedEvenFormation twoEndedPosInfinity) + 1
        rw [twoEndedEvenFormation_posInfinity]
        simp [twoEndedIntegerCoordinate, twoEndedPosInfinity]
    | coe n =>
        rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
        · rw [twoEndedEvenFormation_right, lowerEven_two_mul]
          change ((2 * k : ℕ) : ℤ) ≤ (2 * k : ℤ) ∧
            (2 * k : ℤ) ≤ ((2 * k : ℕ) : ℤ) + 1
          push_cast
          constructor <;> linarith
        · rw [twoEndedEvenFormation_right, lowerEven_two_mul_add_one]
          change ((2 * k : ℕ) : ℤ) ≤ ((2 * k + 1 : ℕ) : ℤ) ∧
            ((2 * k + 1 : ℕ) : ℤ) ≤ ((2 * k : ℕ) : ℤ) + 1
          push_cast
          constructor <;> linarith

theorem twoEndedIntegerCoordinate_odd_bounds (x : TwoEndedInt) :
    twoEndedIntegerCoordinate x ≤ twoEndedIntegerCoordinate (twoEndedOddFormation x) ∧
      twoEndedIntegerCoordinate (twoEndedOddFormation x) ≤
        twoEndedIntegerCoordinate x + 1 := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty =>
        change 0 ≤ twoEndedIntegerCoordinate (twoEndedOddFormation twoEndedNegInfinity) ∧
          twoEndedIntegerCoordinate (twoEndedOddFormation twoEndedNegInfinity) ≤ 1
        rw [twoEndedOddFormation_negInfinity]
        simp [twoEndedIntegerCoordinate, twoEndedNegInfinity]
    | coe n =>
        rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
        · cases k with
          | zero =>
              rw [twoEndedOddFormation_left_zero]
              change (-1 : ℤ) ≤ 0 ∧ 0 ≤ -1 + 1
              constructor <;> linarith
          | succ k =>
              rw [show 2 * (k + 1) = 2 * k + 2 by ring]
              rw [twoEndedOddFormation_left_of_ne_zero (by linarith),
                lowerOdd_two_mul_add_two]
              change -(((2 * k + 2 : ℕ) : ℤ) + 1) ≤
                  -(((2 * k + 1 : ℕ) : ℤ) + 1) ∧
                -(((2 * k + 1 : ℕ) : ℤ) + 1) ≤
                  -(((2 * k + 2 : ℕ) : ℤ) + 1) + 1
              push_cast
              constructor <;> linarith
        · rw [twoEndedOddFormation_left_of_ne_zero (by linarith),
            lowerOdd_two_mul_add_one]
          change -(((2 * k + 1 : ℕ) : ℤ) + 1) ≤ -(((2 * k + 1 : ℕ) : ℤ) + 1) ∧
            -(((2 * k + 1 : ℕ) : ℤ) + 1) ≤ -(((2 * k + 1 : ℕ) : ℤ) + 1) + 1
          constructor <;> linarith
  · induction x using OnePoint.rec with
    | infty =>
        change 0 ≤ twoEndedIntegerCoordinate (twoEndedOddFormation twoEndedPosInfinity) ∧
          twoEndedIntegerCoordinate (twoEndedOddFormation twoEndedPosInfinity) ≤ 1
        rw [twoEndedOddFormation_posInfinity]
        simp [twoEndedIntegerCoordinate, twoEndedPosInfinity]
    | coe n =>
        rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
        · rw [twoEndedOddFormation_right, upperEvenIndex_two_mul]
          change (2 * k : ℤ) ≤ ((2 * k : ℕ) : ℤ) ∧
            ((2 * k : ℕ) : ℤ) ≤ (2 * k : ℤ) + 1
          push_cast
          constructor <;> linarith
        · rw [twoEndedOddFormation_right, upperEvenIndex_two_mul_add_one]
          change ((2 * k + 1 : ℕ) : ℤ) ≤ ((2 * k + 2 : ℕ) : ℤ) ∧
            ((2 * k + 2 : ℕ) : ℤ) ≤ ((2 * k + 1 : ℕ) : ℤ) + 1
          push_cast
          constructor <;> linarith

/-- Every primitive alternating edge changes integer coordinate by at most one. -/
theorem twoEndedAlternationEdge_coordinate_bounds
    {x y : TwoEndedInt} (hxy : twoEndedAlternationEdge x y) :
    twoEndedIntegerCoordinate y ≤ twoEndedIntegerCoordinate x + 1 ∧
      twoEndedIntegerCoordinate x ≤ twoEndedIntegerCoordinate y + 1 := by
  rcases hxy with he | ho
  · change twoEndedEvenFormation x = twoEndedEvenFormation y at he
    have hcoord := congrArg twoEndedIntegerCoordinate he
    obtain ⟨hex, hxe⟩ := twoEndedIntegerCoordinate_even_bounds x
    obtain ⟨hey, hye⟩ := twoEndedIntegerCoordinate_even_bounds y
    constructor <;> linarith
  · change twoEndedOddFormation x = twoEndedOddFormation y at ho
    have hcoord := congrArg twoEndedIntegerCoordinate ho
    obtain ⟨hxo, hox⟩ := twoEndedIntegerCoordinate_odd_bounds x
    obtain ⟨hyo, hoy⟩ := twoEndedIntegerCoordinate_odd_bounds y
    constructor <;> linarith

theorem twoEndedAlternationEdge_right_adjacent (n : ℕ) :
    twoEndedAlternationEdge
      (Sum.inr (n : OnePoint ℕ)) (Sum.inr (n + 1 : ℕ)) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    change twoEndedEvenFormation (Sum.inr ((2 * k : ℕ) : OnePoint ℕ)) =
      twoEndedEvenFormation (Sum.inr ((2 * k + 1 : ℕ) : OnePoint ℕ))
    rw [twoEndedEvenFormation_right, twoEndedEvenFormation_right]
    congr 2
    rw [lowerEven_two_mul, lowerEven_two_mul_add_one]
  · right
    change twoEndedOddFormation (Sum.inr ((2 * k + 1 : ℕ) : OnePoint ℕ)) =
      twoEndedOddFormation (Sum.inr ((2 * k + 1 + 1 : ℕ) : OnePoint ℕ))
    rw [twoEndedOddFormation_right, twoEndedOddFormation_right]
    congr 2
    simp [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]

theorem twoEndedAlternationEdge_left_adjacent (n : ℕ) :
    twoEndedAlternationEdge
      (Sum.inl (n + 1 : ℕ)) (Sum.inl (n : OnePoint ℕ)) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    change twoEndedEvenFormation (Sum.inl ((2 * k + 1 : ℕ) : OnePoint ℕ)) =
      twoEndedEvenFormation (Sum.inl ((2 * k : ℕ) : OnePoint ℕ))
    rw [twoEndedEvenFormation_left, twoEndedEvenFormation_left]
    congr 2
    simp
  · right
    have hne : 2 * k + 1 + 1 ≠ 0 := by linarith
    have hne' : 2 * k + 1 ≠ 0 := by linarith
    change twoEndedOddFormation (Sum.inl ((2 * k + 1 + 1 : ℕ) : OnePoint ℕ)) =
      twoEndedOddFormation (Sum.inl ((2 * k + 1 : ℕ) : OnePoint ℕ))
    rw [twoEndedOddFormation_left_of_ne_zero hne,
      twoEndedOddFormation_left_of_ne_zero hne']
    congr 2
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by ring,
      lowerOdd_two_mul_add_two, lowerOdd_two_mul_add_one]

theorem twoEndedAlternationEdge_bridge :
    twoEndedAlternationEdge
      (Sum.inl ((0 : ℕ) : OnePoint ℕ)) (Sum.inr ((0 : ℕ) : OnePoint ℕ)) := by
  right
  rfl

theorem twoEndedAlternationPower_right (n : ℕ) :
    admissionRelationPower twoEndedAlternationEdge n
      (Sum.inr ((0 : ℕ) : OnePoint ℕ)) (Sum.inr (n : OnePoint ℕ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact ⟨Sum.inr (n : OnePoint ℕ), ih, twoEndedAlternationEdge_right_adjacent n⟩

theorem twoEndedAlternationPower_left (n : ℕ) :
    admissionRelationPower twoEndedAlternationEdge n
      (Sum.inl (n : OnePoint ℕ)) (Sum.inl ((0 : ℕ) : OnePoint ℕ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hone : admissionRelationPower twoEndedAlternationEdge 1
          (Sum.inl (n + 1 : ℕ)) (Sum.inl (n : OnePoint ℕ)) :=
        (admissionRelationPower_one _ _ _).2 (twoEndedAlternationEdge_left_adjacent n)
      simpa [Nat.add_comm] using admissionRelationPower_add hone ih

/-- A path of `n` primitive edges can increase integer coordinate by at most `n`. -/
theorem twoEndedAlternationPower_coordinate_le
    {n : ℕ} {x y : TwoEndedInt}
    (hxy : admissionRelationPower twoEndedAlternationEdge n x y) :
    twoEndedIntegerCoordinate y ≤ twoEndedIntegerCoordinate x + (n : ℤ) := by
  induction n generalizing y with
  | zero =>
      subst y
      simp
  | succ n ih =>
      rcases hxy with ⟨z, hxz, hzy⟩
      have hpath := ih hxz
      have hedge := (twoEndedAlternationEdge_coordinate_bounds hzy).1
      push_cast
      linarith

/-- Exact existence half of the paper's `(-m,m)` depth law, in split-ray coordinates. -/
theorem twoEndedAlternationPower_exact_exists (m : ℕ) (hm : 0 < m) :
    admissionRelationPower twoEndedAlternationEdge (2 * m)
      (Sum.inl (m - 1 : ℕ)) (Sum.inr (m : OnePoint ℕ)) := by
  have hleft := twoEndedAlternationPower_left (m - 1)
  have hbridge : admissionRelationPower twoEndedAlternationEdge 1
      (Sum.inl ((0 : ℕ) : OnePoint ℕ)) (Sum.inr ((0 : ℕ) : OnePoint ℕ)) :=
    (admissionRelationPower_one _ _ _).2 twoEndedAlternationEdge_bridge
  have hright := twoEndedAlternationPower_right m
  have hpath := admissionRelationPower_add (admissionRelationPower_add hleft hbridge) hright
  simpa only [Nat.sub_add_cancel hm, two_mul] using hpath

/-- Exact lower half of the depth law: no path from `-m` to `m` uses fewer than `2m` edges. -/
theorem twoEndedAlternationPower_exact_lower
    {m n : ℕ} (hm : 0 < m)
    (hpath : admissionRelationPower twoEndedAlternationEdge n
      (Sum.inl (m - 1 : ℕ)) (Sum.inr (m : OnePoint ℕ))) :
    2 * m ≤ n := by
  have hcoord := twoEndedAlternationPower_coordinate_le hpath
  change (m : ℤ) ≤ -(((m - 1 : ℕ) : ℤ) + 1) + (n : ℤ) at hcoord
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm))] at hcoord
  simp only [Nat.cast_one] at hcoord
  have hint : ((2 * m : ℕ) : ℤ) ≤ (n : ℤ) := by
    push_cast
    linarith
  exact Int.ofNat_le.mp hint

/-- The minimal alternating depth of `(-m,m)` is exactly `2m`. -/
theorem twoEndedAlternationPower_exact (m : ℕ) (hm : 0 < m) :
    admissionRelationPower twoEndedAlternationEdge (2 * m)
        (Sum.inl (m - 1 : ℕ)) (Sum.inr (m : OnePoint ℕ)) ∧
      ∀ n, admissionRelationPower twoEndedAlternationEdge n
          (Sum.inl (m - 1 : ℕ)) (Sum.inr (m : OnePoint ℕ)) → 2 * m ≤ n :=
  ⟨twoEndedAlternationPower_exact_exists m hm,
    fun _ => twoEndedAlternationPower_exact_lower hm⟩

@[simp] theorem twoEndedIntOfInt_ofNat (m : ℕ) :
    twoEndedIntOfInt (Int.ofNat m) = Sum.inr (m : OnePoint ℕ) :=
  rfl

theorem twoEndedIntOfInt_neg_of_pos (m : ℕ) (hm : 0 < m) :
    twoEndedIntOfInt (-(m : ℤ)) = Sum.inl ((m - 1 : ℕ) : OnePoint ℕ) := by
  cases m with
  | zero => exact (Nat.lt_asymm hm hm).elim
  | succ k =>
      change twoEndedIntOfInt (Int.negSucc k) = Sum.inl (k : OnePoint ℕ)
      rfl

/-- Exact depth law in the paper's literal embedded-integer notation. -/
theorem twoEndedAlternationPower_exact_int (m : ℕ) (hm : 0 < m) :
    admissionRelationPower twoEndedAlternationEdge (2 * m)
        (twoEndedIntOfInt (-(m : ℤ))) (twoEndedIntOfInt (m : ℤ)) ∧
      ∀ n, admissionRelationPower twoEndedAlternationEdge n
          (twoEndedIntOfInt (-(m : ℤ))) (twoEndedIntOfInt (m : ℤ)) → 2 * m ≤ n := by
  rw [twoEndedIntOfInt_neg_of_pos m hm]
  exact twoEndedAlternationPower_exact m hm

/-- The exact-depth witnesses converge to the critical endpoint pair. -/
theorem tendsto_twoEndedAlternationDepth_pairs :
    Tendsto
      (fun n : ℕ =>
        ((Sum.inl (n : OnePoint ℕ) : TwoEndedInt),
          (Sum.inr (n + 1 : ℕ) : TwoEndedInt)))
      cofinite (𝓝 (twoEndedNegInfinity, twoEndedPosInfinity)) := by
  have hsucc : Tendsto (fun n : ℕ => n + 1) cofinite cofinite :=
    Function.Injective.tendsto_cofinite
      (fun _ _ h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  exact tendsto_twoEnded_left_coe.prodMk_nhds
    (tendsto_twoEnded_right_coe.comp hsucc)

/-- Finite endpoint reporters converge pointwise to the discontinuous algebraic reporter. -/
theorem finiteTwoEndedReporter_tendsto_setReporter (x : TwoEndedInt) :
    Tendsto (fun N : ℕ => finiteTwoEndedReporter N x) atTop
      (𝓝 (twoEndedSetReporter x)) := by
  rcases x with x | x
  · induction x using OnePoint.rec with
    | infty =>
        change Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)
        exact tendsto_const_nhds
    | coe n =>
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop n] with N hN
        exact (finiteTwoEndedReporter_eventually_eq_setReporter_left n N hN).symm
  · induction x using OnePoint.rec with
    | infty =>
        change Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)
        exact tendsto_const_nhds
    | coe n =>
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop n] with N hN
        exact (finiteTwoEndedReporter_eventually_eq_setReporter_right n N hN).symm

theorem twoEnded_endpoints_analyticCriticalShell :
    analyticCriticalShell twoEndedJoinedUnitization
      twoEndedNegInfinity twoEndedPosInfinity := by
  refine ⟨twoEnded_analyticAdmission_total _ _, ?_⟩
  rw [twoEnded_joinedUnitization_eqvGen_iff]
  simp [IsTwoEndedFinite, twoEndedNegInfinity, twoEndedPosInfinity]

theorem twoEnded_endpoints_dirac_totalVariation :
    finitelySupportedTotalVariation
      (finitelySupportedDirac twoEndedNegInfinity)
      (finitelySupportedDirac twoEndedPosInfinity) = 1 :=
  analyticCriticalShell_dirac_totalVariation twoEnded_endpoints_analyticCriticalShell

theorem twoEnded_endpoints_analyticAdmission_pushforward_totalVariation :
    finitelySupportedTotalVariation
      ((finitelySupportedDirac twoEndedNegInfinity).mapDomain
        (analyticAdmissionMk twoEndedJoinedUnitization))
      ((finitelySupportedDirac twoEndedPosInfinity).mapDomain
        (analyticAdmissionMk twoEndedJoinedUnitization)) = 0 :=
  finitelySupportedDirac_pushforward_totalVariation_zero _
    (twoEnded_analyticAdmission_total _ _)

/-- Bundled unconditional capstone for the full two-ended finite/global mechanism. -/
theorem twoEndedAdmissionCriticalShell_capstone :
    analyticCriticalShell twoEndedJoinedUnitization
        twoEndedNegInfinity twoEndedPosInfinity ∧
    finitelySupportedTotalVariation
        (finitelySupportedDirac twoEndedNegInfinity)
        (finitelySupportedDirac twoEndedPosInfinity) = 1 ∧
    finitelySupportedTotalVariation
        ((finitelySupportedDirac twoEndedNegInfinity).mapDomain
          (analyticAdmissionMk twoEndedJoinedUnitization))
        ((finitelySupportedDirac twoEndedPosInfinity).mapDomain
          (analyticAdmissionMk twoEndedJoinedUnitization)) = 0 ∧
    (∀ N,
      IsClosed (admissionRelationGraph
        (Relation.EqvGen
          (fun a b => finiteTwoEndedEvenSetoid N a b ∨ finiteTwoEndedOddSetoid N a b))) ∧
      (∀ x y, Relation.EqvGen
          (fun a b => finiteTwoEndedEvenSetoid N a b ∨ finiteTwoEndedOddSetoid N a b) x y ↔
        x = y ∨ (IsFiniteTwoEndedCentral N x ∧ IsFiniteTwoEndedCentral N y)) ∧
      (∀ x, finiteTwoEndedReporter N (finiteTwoEndedEvenFormation N x) =
        finiteTwoEndedReporter N x) ∧
      (∀ x, finiteTwoEndedReporter N (finiteTwoEndedOddFormation N x) =
        finiteTwoEndedReporter N x) ∧
      finiteTwoEndedReporter N twoEndedPosInfinity -
        finiteTwoEndedReporter N twoEndedNegInfinity = 1) ∧
    (∀ x, Tendsto (fun N : ℕ => finiteTwoEndedReporter N x) atTop
      (𝓝 (twoEndedSetReporter x))) ∧
    ¬ EquicontinuousAt (fun N : ℕ => (finiteTwoEndedReporter N : TwoEndedInt → ℝ))
      twoEndedPosInfinity ∧
    ¬ EquicontinuousAt (fun N : ℕ => (finiteTwoEndedReporter N : TwoEndedInt → ℝ))
      twoEndedNegInfinity ∧
    sInf (Set.range twoEndedReporterUniformError) = 1 / 2 ∧
    (∀ m, 0 < m →
      admissionRelationPower twoEndedAlternationEdge (2 * m)
          (twoEndedIntOfInt (-(m : ℤ))) (twoEndedIntOfInt (m : ℤ)) ∧
        ∀ n, admissionRelationPower twoEndedAlternationEdge n
            (twoEndedIntOfInt (-(m : ℤ))) (twoEndedIntOfInt (m : ℤ)) → 2 * m ≤ n) := by
  refine ⟨twoEnded_endpoints_analyticCriticalShell,
    twoEnded_endpoints_dirac_totalVariation,
    twoEnded_endpoints_analyticAdmission_pushforward_totalVariation, ?_,
    finiteTwoEndedReporter_tendsto_setReporter,
    finiteTwoEndedReporter_not_equicontinuousAt_posInfinity,
    finiteTwoEndedReporter_not_equicontinuousAt_negInfinity,
    twoEndedReporterUniformError_sInf, ?_⟩
  · intro N
    exact ⟨finiteTwoEnded_join_isClosed N, finiteTwoEnded_join_eqvGen_iff N,
      finiteTwoEndedReporter_unitizes_even N, finiteTwoEndedReporter_unitizes_odd N,
      finiteTwoEndedReporter_exact_margin N⟩
  · exact twoEndedAlternationPower_exact_int

end

end HTGeometry
