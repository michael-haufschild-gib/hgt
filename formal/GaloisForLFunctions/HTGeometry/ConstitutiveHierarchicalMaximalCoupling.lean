import GaloisForLFunctions.HTGeometry.ConstitutivePositiveOverlapDefect

open scoped BigOperators NNReal

namespace HTGeometry

noncomputable section

/-!
# Hierarchical maximal-coupling faces

Finite nonnegative profiles are represented over `ℝ≥0`.  This file develops the observer capacity,
coupling upper bound, and constructive block-coupling step used by hierarchical consensus faces.
-/

def nnFiberMass {X K : Type*} [Fintype X] [DecidableEq K]
    (u : X → ℝ≥0) (kappa : X → K) (k : K) : ℝ≥0 :=
  ∑ x, if kappa x = k then u x else 0

def nnObserverCapacity {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) : ℝ≥0 :=
  ∑ k, min (nnFiberMass u kappa k) (nnFiberMass v kappa k)

structure FiniteNNCoupling {X : Type*} [Fintype X]
    (u v : X → ℝ≥0) where
  plan : X → X → ℝ≥0
  row : ∀ x, ∑ y, plan x y = u x
  col : ∀ y, ∑ x, plan x y = v y

def nnCouplingBlockMass {X K : Type*} [Fintype X] [DecidableEq K]
    (gamma : X → X → ℝ≥0) (kappa : X → K) (k : K) : ℝ≥0 :=
  ∑ x, if kappa x = k then
    ∑ y, if kappa y = k then gamma x y else 0
  else 0

def nnCouplingAgreementMass {X K : Type*} [Fintype X] [Fintype K]
    [DecidableEq K] (gamma : X → X → ℝ≥0) (kappa : X → K) : ℝ≥0 :=
  ∑ k, nnCouplingBlockMass gamma kappa k

theorem nnCouplingBlockMass_le_left
    {X K : Type*} [Fintype X] [DecidableEq K]
    {u v : X → ℝ≥0} (gamma : FiniteNNCoupling u v)
    (kappa : X → K) (k : K) :
    nnCouplingBlockMass gamma.plan kappa k ≤ nnFiberMass u kappa k := by
  classical
  unfold nnCouplingBlockMass nnFiberMass
  apply Finset.sum_le_sum
  intro x hx
  by_cases hkx : kappa x = k
  · simp only [hkx, if_true]
    calc
      (∑ y, if kappa y = k then gamma.plan x y else 0) ≤
          ∑ y, gamma.plan x y := by
        apply Finset.sum_le_sum
        intro y hy
        split <;> simp
      _ = u x := gamma.row x
  · simp [hkx]

theorem nnCouplingBlockMass_le_right
    {X K : Type*} [Fintype X] [DecidableEq K]
    {u v : X → ℝ≥0} (gamma : FiniteNNCoupling u v)
    (kappa : X → K) (k : K) :
    nnCouplingBlockMass gamma.plan kappa k ≤ nnFiberMass v kappa k := by
  classical
  unfold nnCouplingBlockMass nnFiberMass
  calc
    (∑ x, if kappa x = k then
        ∑ y, if kappa y = k then gamma.plan x y else 0 else 0) =
        ∑ x, ∑ y,
          if kappa x = k ∧ kappa y = k then gamma.plan x y else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hkx : kappa x = k
      · simp [hkx]
      · simp [hkx]
    _ = ∑ y, ∑ x,
          if kappa x = k ∧ kappa y = k then gamma.plan x y else 0 := by
      rw [Finset.sum_comm]
    _ =
        ∑ y, if kappa y = k then
          ∑ x, if kappa x = k then gamma.plan x y else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hky : kappa y = k
      · simp [hky]
      · simp [hky]
    _ ≤ ∑ y, if kappa y = k then v y else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hky : kappa y = k
      · simp only [hky, if_true]
        calc
          (∑ x, if kappa x = k then gamma.plan x y else 0) ≤
              ∑ x, gamma.plan x y := by
            apply Finset.sum_le_sum
            intro x hx
            split <;> simp
          _ = v y := gamma.col y
      · simp [hky]

theorem nnCouplingAgreementMass_le_capacity
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    {u v : X → ℝ≥0} (gamma : FiniteNNCoupling u v) (kappa : X → K) :
    nnCouplingAgreementMass gamma.plan kappa ≤ nnObserverCapacity u v kappa := by
  unfold nnCouplingAgreementMass nnObserverCapacity
  apply Finset.sum_le_sum
  intro k hk
  exact le_min (nnCouplingBlockMass_le_left gamma kappa k)
    (nnCouplingBlockMass_le_right gamma kappa k)

/-- The amount removed from the left profile in one observer block. -/
def nnObserverRemovedLeft {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (x : X) : ℝ≥0 :=
  u x * min (nnFiberMass u kappa (kappa x)) (nnFiberMass v kappa (kappa x)) /
    nnFiberMass u kappa (kappa x)

/-- The amount removed from the right profile in one observer block. -/
def nnObserverRemovedRight {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (y : X) : ℝ≥0 :=
  v y * min (nnFiberMass u kappa (kappa y)) (nnFiberMass v kappa (kappa y)) /
    nnFiberMass v kappa (kappa y)

/-- Product coupling of the maximal common mass inside each observer block. -/
def nnObserverBlockPlan {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (x y : X) : ℝ≥0 :=
  if kappa x = kappa y then
    min (nnFiberMass u kappa (kappa x)) (nnFiberMass v kappa (kappa x)) *
      (u x / nnFiberMass u kappa (kappa x)) *
      (v y / nnFiberMass v kappa (kappa x))
  else 0

theorem nnFiberMass_eq_zero_iff
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u : X → ℝ≥0) (kappa : X → K) (k : K) :
    nnFiberMass u kappa k = 0 ↔ ∀ x, kappa x = k → u x = 0 := by
  classical
  rw [nnFiberMass, Finset.sum_eq_zero_iff_of_nonneg (fun i hi => by positivity)]
  simp

theorem nnObserverBlockPlan_row
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (x : X) :
    (∑ y, nnObserverBlockPlan u v kappa x y) =
      nnObserverRemovedLeft u v kappa x := by
  classical
  let A := nnFiberMass u kappa (kappa x)
  let B := nnFiberMass v kappa (kappa x)
  by_cases hA : A = 0
  · have hux : u x = 0 :=
      (nnFiberMass_eq_zero_iff u kappa (kappa x)).mp hA x rfl
    simp [nnObserverBlockPlan, nnObserverRemovedLeft, A, hA, hux]
  · by_cases hB : B = 0
    · have hv : ∀ y, kappa y = kappa x → v y = 0 :=
        (nnFiberMass_eq_zero_iff v kappa (kappa x)).mp hB
      simp only [nnObserverBlockPlan, nnObserverRemovedLeft]
      rw [show nnFiberMass u kappa (kappa x) = A from rfl,
        show nnFiberMass v kappa (kappa x) = B from rfl]
      simp [hB]
    · simp only [nnObserverBlockPlan, nnObserverRemovedLeft]
      rw [show nnFiberMass u kappa (kappa x) = A from rfl,
        show nnFiberMass v kappa (kappa x) = B from rfl]
      calc
        (∑ y, if kappa x = kappa y then
            min A B * (u x / A) * (v y / B) else 0) =
            ∑ y, min A B * (u x / A) *
              ((if kappa y = kappa x then v y else 0) / B) := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hxy : kappa y = kappa x
          · rw [if_pos hxy.symm, if_pos hxy]
          · rw [if_neg (Ne.symm hxy), if_neg hxy]
            simp
        _ = min A B * (u x / A) *
            ((∑ y, if kappa y = kappa x then v y else 0) / B) := by
          rw [Finset.sum_div, Finset.mul_sum]
        _ = min A B * (u x / A) * (B / B) := by
          rw [show (∑ y, if kappa y = kappa x then v y else 0) = B from rfl]
        _ = u x * min A B / A := by
          rw [div_self hB, mul_one]
          simp only [div_eq_mul_inv]
          ac_rfl

theorem nnObserverBlockPlan_col
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (y : X) :
    (∑ x, nnObserverBlockPlan u v kappa x y) =
      nnObserverRemovedRight u v kappa y := by
  classical
  let A := nnFiberMass u kappa (kappa y)
  let B := nnFiberMass v kappa (kappa y)
  by_cases hA : A = 0
  · have hu : ∀ x, kappa x = kappa y → u x = 0 :=
      (nnFiberMass_eq_zero_iff u kappa (kappa y)).mp hA
    have hsum : ∑ x, nnObserverBlockPlan u v kappa x y = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hxy : kappa x = kappa y
      · simp [nnObserverBlockPlan, hxy, hu x hxy]
      · simp [nnObserverBlockPlan, hxy]
    rw [hsum]
    simp [nnObserverRemovedRight, A, hA]
  · by_cases hB : B = 0
    · have hvy : v y = 0 :=
        (nnFiberMass_eq_zero_iff v kappa (kappa y)).mp hB y rfl
      have hsum : ∑ x, nnObserverBlockPlan u v kappa x y = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        by_cases hxy : kappa x = kappa y
        · simp [nnObserverBlockPlan, hxy, hvy]
        · simp [nnObserverBlockPlan, hxy]
      rw [hsum]
      simp [nnObserverRemovedRight, B, hB, hvy]
    · simp only [nnObserverBlockPlan, nnObserverRemovedRight]
      rw [show nnFiberMass u kappa (kappa y) = A from rfl,
        show nnFiberMass v kappa (kappa y) = B from rfl]
      calc
        (∑ x, if kappa x = kappa y then
            min (nnFiberMass u kappa (kappa x))
                (nnFiberMass v kappa (kappa x)) *
              (u x / nnFiberMass u kappa (kappa x)) *
              (v y / nnFiberMass v kappa (kappa x)) else 0) =
            ∑ x, min A B *
              ((if kappa x = kappa y then u x else 0) / A) *
              (v y / B) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxy : kappa x = kappa y
          · simp [hxy, A, B]
          · simp [hxy]
        _ = min A B * ((∑ x, if kappa x = kappa y then u x else 0) / A) *
              (v y / B) := by
          rw [Finset.sum_div, Finset.mul_sum]
          rw [Finset.sum_mul]
        _ = min A B * (A / A) * (v y / B) := by
          rw [show (∑ x, if kappa x = kappa y then u x else 0) = A from rfl]
        _ = v y * min A B / B := by
          rw [div_self hA, mul_one]
          simp only [div_eq_mul_inv]
          ac_rfl

/-- Residual left mass after maximal within-block coupling. -/
def nnObserverResidualLeft {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (x : X) : ℝ≥0 :=
  let A := nnFiberMass u kappa (kappa x)
  let B := nnFiberMass v kappa (kappa x)
  if A ≤ B then 0 else u x * (A - B) / A

/-- Residual right mass after maximal within-block coupling. -/
def nnObserverResidualRight {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (y : X) : ℝ≥0 :=
  let A := nnFiberMass u kappa (kappa y)
  let B := nnFiberMass v kappa (kappa y)
  if B ≤ A then 0 else v y * (B - A) / B

theorem nnObserverBlockPlan_row_add_residual
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (x : X) :
    (∑ y, nnObserverBlockPlan u v kappa x y) +
      nnObserverResidualLeft u v kappa x = u x := by
  rw [nnObserverBlockPlan_row]
  let A := nnFiberMass u kappa (kappa x)
  let B := nnFiberMass v kappa (kappa x)
  rw [nnObserverRemovedLeft, nnObserverResidualLeft]
  change u x * min A B / A + (if A ≤ B then 0 else u x * (A - B) / A) = u x
  by_cases hAB : A ≤ B
  · rw [if_pos hAB, add_zero, min_eq_left hAB]
    by_cases hA : A = 0
    · have hux : u x = 0 :=
        (nnFiberMass_eq_zero_iff u kappa (kappa x)).mp hA x rfl
      simp [hux]
    · exact mul_div_cancel_right₀ (u x) hA
  · rw [if_neg hAB, min_eq_right (le_of_not_ge hAB)]
    have hBA : B ≤ A := le_of_not_ge hAB
    have hA : A ≠ 0 := ne_of_gt
      (lt_of_le_of_lt (show 0 ≤ B from bot_le) (lt_of_not_ge hAB))
    rw [← add_div, ← mul_add, add_tsub_cancel_of_le hBA]
    exact mul_div_cancel_right₀ (u x) hA

theorem nnObserverBlockPlan_col_add_residual
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (y : X) :
    (∑ x, nnObserverBlockPlan u v kappa x y) +
      nnObserverResidualRight u v kappa y = v y := by
  rw [nnObserverBlockPlan_col]
  let A := nnFiberMass u kappa (kappa y)
  let B := nnFiberMass v kappa (kappa y)
  rw [nnObserverRemovedRight, nnObserverResidualRight]
  change v y * min A B / B + (if B ≤ A then 0 else v y * (B - A) / B) = v y
  by_cases hBA : B ≤ A
  · rw [if_pos hBA, add_zero, min_eq_right hBA]
    by_cases hB : B = 0
    · have hvy : v y = 0 :=
        (nnFiberMass_eq_zero_iff v kappa (kappa y)).mp hB y rfl
      simp [hvy]
    · exact mul_div_cancel_right₀ (v y) hB
  · rw [if_neg hBA, min_eq_left (le_of_not_ge hBA)]
    have hAB : A ≤ B := le_of_not_ge hBA
    have hB : B ≠ 0 := ne_of_gt
      (lt_of_le_of_lt (show 0 ≤ A from bot_le) (lt_of_not_ge hBA))
    rw [← add_div, ← mul_add, add_tsub_cancel_of_le hAB]
    exact mul_div_cancel_right₀ (v y) hB

theorem nnObserverResidual_oneSided
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (k : K) :
    nnFiberMass (nnObserverResidualLeft u v kappa) kappa k = 0 ∨
      nnFiberMass (nnObserverResidualRight u v kappa) kappa k = 0 := by
  classical
  let A := nnFiberMass u kappa k
  let B := nnFiberMass v kappa k
  by_cases hAB : A ≤ B
  · left
    apply (nnFiberMass_eq_zero_iff _ kappa k).mpr
    intro x hx
    simp [nnObserverResidualLeft, hx, A, B, hAB]
  · right
    have hBA : B ≤ A := le_of_not_ge hAB
    apply (nnFiberMass_eq_zero_iff _ kappa k).mpr
    intro y hy
    simp [nnObserverResidualRight, hy, A, B, hBA]

theorem nnObserverBlockPlan_avoids_refinedBlock
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : X → L)
    {x y : X} (hxy : kappa x = kappa y) :
    nnObserverBlockPlan
      (nnObserverResidualLeft u v kappa)
      (nnObserverResidualRight u v kappa) lambda x y = 0 := by
  classical
  rcases nnObserverResidual_oneSided u v kappa (kappa x) with hleft | hright
  · have hxzero : nnObserverResidualLeft u v kappa x = 0 :=
      (nnFiberMass_eq_zero_iff _ kappa (kappa x)).mp hleft x rfl
    simp [nnObserverBlockPlan, hxzero]
  · have hyzero : nnObserverResidualRight u v kappa y = 0 :=
      (nnFiberMass_eq_zero_iff _ kappa (kappa x)).mp hright y hxy.symm
    simp [nnObserverBlockPlan, hyzero]

def nnProfileMass {X : Type*} [Fintype X] (u : X → ℝ≥0) : ℝ≥0 :=
  ∑ x, u x

/-- Product coupling for two profiles with equal total mass. -/
def nnProductPlan {X : Type*} [Fintype X]
    (u v : X → ℝ≥0) (x y : X) : ℝ≥0 :=
  if nnProfileMass u = 0 then 0 else u x * v y / nnProfileMass u

theorem nnProductPlan_row
    {X : Type*} [Fintype X] (u v : X → ℝ≥0)
    (hmass : nnProfileMass u = nnProfileMass v) (x : X) :
    ∑ y, nnProductPlan u v x y = u x := by
  classical
  by_cases hzero : nnProfileMass u = 0
  · have hux : u x = 0 := by
      rw [nnProfileMass, Finset.sum_eq_zero_iff_of_nonneg (fun i hi => by positivity)] at hzero
      exact hzero x (Finset.mem_univ x)
    simp [nnProductPlan, hzero, hux]
  · simp only [nnProductPlan, hzero, if_false]
    calc
      (∑ y, u x * v y / nnProfileMass u) =
          u x * (∑ y, v y) / nnProfileMass u := by
        rw [Finset.mul_sum, Finset.sum_div]
      _ = u x * nnProfileMass u / nnProfileMass u := by
        rw [← nnProfileMass, hmass]
      _ = u x := mul_div_cancel_right₀ _ hzero

theorem nnProductPlan_col
    {X : Type*} [Fintype X] (u v : X → ℝ≥0)
    (hmass : nnProfileMass u = nnProfileMass v) (y : X) :
    ∑ x, nnProductPlan u v x y = v y := by
  classical
  by_cases hzero : nnProfileMass u = 0
  · have hvzero : nnProfileMass v = 0 := hmass ▸ hzero
    have hvy : v y = 0 := by
      rw [nnProfileMass, Finset.sum_eq_zero_iff_of_nonneg (fun i hi => by positivity)] at hvzero
      exact hvzero y (Finset.mem_univ y)
    simp [nnProductPlan, hzero, hvy]
  · simp only [nnProductPlan, hzero, if_false]
    calc
      (∑ x, u x * v y / nnProfileMass u) =
          (∑ x, u x) * v y / nnProfileMass u := by
        rw [Finset.sum_mul, Finset.sum_div]
      _ = nnProfileMass u * v y / nnProfileMass u := by rw [nnProfileMass]
      _ = v y := mul_div_cancel_left₀ _ hzero

theorem nnObserverResidual_mass_eq
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K)
    (hmass : nnProfileMass u = nnProfileMass v) :
    nnProfileMass (nnObserverResidualLeft u v kappa) =
      nnProfileMass (nnObserverResidualRight u v kappa) := by
  classical
  have hrow :
      (∑ x, ∑ y, nnObserverBlockPlan u v kappa x y) +
          nnProfileMass (nnObserverResidualLeft u v kappa) = nnProfileMass u := by
    rw [nnProfileMass, nnProfileMass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    exact nnObserverBlockPlan_row_add_residual u v kappa x
  have hcol :
      (∑ x, ∑ y, nnObserverBlockPlan u v kappa x y) +
          nnProfileMass (nnObserverResidualRight u v kappa) = nnProfileMass v := by
    rw [Finset.sum_comm]
    rw [nnProfileMass, nnProfileMass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    exact nnObserverBlockPlan_col_add_residual u v kappa y
  rw [hmass] at hrow
  exact add_left_cancel (hrow.trans hcol.symm)

theorem nnObserverRemovedLeft_fiberMass
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (k : K) :
    nnFiberMass (nnObserverRemovedLeft u v kappa) kappa k =
      min (nnFiberMass u kappa k) (nnFiberMass v kappa k) := by
  classical
  let A := nnFiberMass u kappa k
  let B := nnFiberMass v kappa k
  by_cases hA : A = 0
  · have hu : ∀ x, kappa x = k → u x = 0 :=
      (nnFiberMass_eq_zero_iff u kappa k).mp hA
    have hleft : nnFiberMass (nnObserverRemovedLeft u v kappa) kappa k = 0 := by
      apply (nnFiberMass_eq_zero_iff _ kappa k).mpr
      intro x hx
      simp [nnObserverRemovedLeft, hx, hu x hx]
    rw [hleft]
    change 0 = min A B
    simp [hA]
  · rw [nnFiberMass]
    calc
      (∑ x, if kappa x = k then nnObserverRemovedLeft u v kappa x else 0) =
          ∑ x, (if kappa x = k then u x else 0) * min A B / A := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hkx : kappa x = k
        · simp [nnObserverRemovedLeft, hkx, A, B]
        · simp [hkx]
      _ = (∑ x, if kappa x = k then u x else 0) * min A B / A := by
        rw [Finset.sum_mul, Finset.sum_div]
      _ = A * min A B / A := by
        rw [show (∑ x, if kappa x = k then u x else 0) = A from rfl]
      _ = min A B := mul_div_cancel_left₀ _ hA

theorem nnObserverBlockPlan_blockMass
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (k : K) :
    nnCouplingBlockMass (nnObserverBlockPlan u v kappa) kappa k =
      min (nnFiberMass u kappa k) (nnFiberMass v kappa k) := by
  classical
  rw [← nnObserverRemovedLeft_fiberMass u v kappa k]
  unfold nnCouplingBlockMass nnFiberMass
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hkx : kappa x = k
  · simp only [hkx, if_true]
    rw [← nnObserverBlockPlan_row]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hky : kappa y = k
    · rw [if_pos hky]
    · rw [if_neg hky]
      have hne : kappa x ≠ kappa y := fun h => hky (h.symm.trans hkx)
      simp [nnObserverBlockPlan, hne]
  · simp [hkx]

def nnObserverMaximalPlan {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) (x y : X) : ℝ≥0 :=
  nnObserverBlockPlan u v kappa x y +
    nnProductPlan
      (nnObserverResidualLeft u v kappa)
      (nnObserverResidualRight u v kappa) x y

theorem nnProductPlan_residual_avoidsBlock
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) {x y : X}
    (hxy : kappa x = kappa y) :
    nnProductPlan
      (nnObserverResidualLeft u v kappa)
      (nnObserverResidualRight u v kappa) x y = 0 := by
  classical
  rcases nnObserverResidual_oneSided u v kappa (kappa x) with hleft | hright
  · have hxzero : nnObserverResidualLeft u v kappa x = 0 :=
      (nnFiberMass_eq_zero_iff _ kappa (kappa x)).mp hleft x rfl
    simp [nnProductPlan, hxzero]
  · have hyzero : nnObserverResidualRight u v kappa y = 0 :=
      (nnFiberMass_eq_zero_iff _ kappa (kappa x)).mp hright y hxy.symm
    simp [nnProductPlan, hyzero]

/-- Every finite observer admits a maximal-agreement coupling. -/
def nnObserverMaximalCoupling
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K)
    (hmass : nnProfileMass u = nnProfileMass v) : FiniteNNCoupling u v where
  plan := nnObserverMaximalPlan u v kappa
  row := by
    intro x
    change (∑ y, (nnObserverBlockPlan u v kappa x y +
      nnProductPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa) x y)) = u x
    rw [Finset.sum_add_distrib,
      nnObserverBlockPlan_row, nnProductPlan_row]
    · rw [← nnObserverBlockPlan_row u v kappa x]
      exact nnObserverBlockPlan_row_add_residual u v kappa x
    · exact nnObserverResidual_mass_eq u v kappa hmass
  col := by
    intro y
    change (∑ x, (nnObserverBlockPlan u v kappa x y +
      nnProductPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa) x y)) = v y
    rw [Finset.sum_add_distrib,
      nnObserverBlockPlan_col, nnProductPlan_col]
    · rw [← nnObserverBlockPlan_col u v kappa y]
      exact nnObserverBlockPlan_col_add_residual u v kappa y
    · exact nnObserverResidual_mass_eq u v kappa hmass

theorem nnCouplingBlockMass_add
    {X K : Type*} [Fintype X] [DecidableEq K]
    (gamma delta : X → X → ℝ≥0) (kappa : X → K) (k : K) :
    nnCouplingBlockMass (fun x y => gamma x y + delta x y) kappa k =
      nnCouplingBlockMass gamma kappa k + nnCouplingBlockMass delta kappa k := by
  classical
  unfold nnCouplingBlockMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hkx : kappa x = k
  · simp only [hkx, if_true]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hky : kappa y = k <;> simp [hky]
  · simp [hkx]

theorem nnCouplingBlockMass_eq_min_of_balanced_oneSided
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v a b : X → ℝ≥0) (gamma : X → X → ℝ≥0) (kappa : X → K)
    (hrow : ∀ x, (∑ y, gamma x y) + a x = u x)
    (hcol : ∀ y, (∑ x, gamma x y) + b y = v y)
    (hsupport : ∀ x y, gamma x y ≠ 0 → kappa x = kappa y)
    (hone : ∀ k,
      nnFiberMass a kappa k = 0 ∨ nnFiberMass b kappa k = 0)
    (k : K) :
    nnCouplingBlockMass gamma kappa k =
      min (nnFiberMass u kappa k) (nnFiberMass v kappa k) := by
  classical
  let G := nnCouplingBlockMass gamma kappa k
  let A := nnFiberMass a kappa k
  let B := nnFiberMass b kappa k
  let U := nnFiberMass u kappa k
  let V := nnFiberMass v kappa k
  have hGleft :
      G = ∑ x, if kappa x = k then ∑ y, gamma x y else 0 := by
    change nnCouplingBlockMass gamma kappa k = _
    rw [nnCouplingBlockMass]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hkx : kappa x = k
    · simp only [hkx, if_true]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hky : kappa y = k
      · rw [if_pos hky]
      · rw [if_neg hky]
        have hzero : gamma x y = 0 := by
          by_contra hne
          exact hky ((hsupport x y hne).symm.trans hkx)
        exact hzero.symm
    · simp [hkx]
  have hGright :
      G = ∑ y, if kappa y = k then ∑ x, gamma x y else 0 := by
    change nnCouplingBlockMass gamma kappa k = _
    rw [nnCouplingBlockMass]
    calc
      (∑ x, if kappa x = k then
          ∑ y, if kappa y = k then gamma x y else 0 else 0) =
          ∑ x, ∑ y, if kappa x = k ∧ kappa y = k then gamma x y else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hkx : kappa x = k <;> simp [hkx]
      _ = ∑ y, ∑ x, if kappa x = k ∧ kappa y = k then gamma x y else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ y, if kappa y = k then ∑ x, gamma x y else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hky : kappa y = k
        · simp only [hky, and_true, if_true]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hkx : kappa x = k
          · rw [if_pos hkx]
          · rw [if_neg hkx]
            have hzero : gamma x y = 0 := by
              by_contra hne
              exact hkx ((hsupport x y hne).trans hky)
            exact hzero.symm
        · simp [hky]
  have hU : G + A = U := by
    rw [hGleft]
    change (∑ x, if kappa x = k then ∑ y, gamma x y else 0) +
      nnFiberMass a kappa k = nnFiberMass u kappa k
    rw [nnFiberMass, nnFiberMass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hkx : kappa x = k
    · simp only [hkx, if_true]
      exact hrow x
    · simp [hkx]
  have hV : G + B = V := by
    rw [hGright]
    change (∑ y, if kappa y = k then ∑ x, gamma x y else 0) +
      nnFiberMass b kappa k = nnFiberMass v kappa k
    rw [nnFiberMass, nnFiberMass]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hky : kappa y = k
    · simp only [hky, if_true]
      exact hcol y
    · simp [hky]
  rcases hone k with hA | hB
  · change A = 0 at hA
    have hUG : U = G := by simpa [hA] using hU.symm
    have hGV : G ≤ V := by
      rw [← hV]
      exact le_add_right le_rfl
    change G = min U V
    rw [hUG, min_eq_left hGV]
  · change B = 0 at hB
    have hVG : V = G := by simpa [hB] using hV.symm
    have hGU : G ≤ U := by
      rw [← hU]
      exact le_add_right le_rfl
    change G = min U V
    rw [hVG, min_eq_right hGU]

theorem nnObserverMaximalCoupling_agreement
    {X K : Type*} [Fintype X] [Fintype K] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K)
    (hmass : nnProfileMass u = nnProfileMass v) :
    nnCouplingAgreementMass
        (nnObserverMaximalCoupling u v kappa hmass).plan kappa =
      nnObserverCapacity u v kappa := by
  classical
  unfold nnCouplingAgreementMass nnObserverCapacity
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (nnObserverMaximalCoupling u v kappa hmass).plan =
    nnObserverMaximalPlan u v kappa from rfl]
  rw [show nnObserverMaximalPlan u v kappa = fun x y =>
    nnObserverBlockPlan u v kappa x y +
      nnProductPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa) x y from rfl]
  rw [nnCouplingBlockMass_add]
  have hproduct :
      (∑ x, if kappa x = k then
        ∑ y, if kappa y = k then
          nnProductPlan
            (nnObserverResidualLeft u v kappa)
            (nnObserverResidualRight u v kappa) x y else 0 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hkx : kappa x = k
    · simp only [hkx, if_true]
      apply Finset.sum_eq_zero
      intro y hy
      by_cases hky : kappa y = k
      · rw [if_pos hky]
        exact nnProductPlan_residual_avoidsBlock u v kappa (hkx.trans hky.symm)
      · simp [hky]
    · simp [hkx]
  have hproduct' :
      nnCouplingBlockMass
        (nnProductPlan
          (nnObserverResidualLeft u v kappa)
          (nnObserverResidualRight u v kappa)) kappa k = 0 := by
    simpa [nnCouplingBlockMass] using hproduct
  rw [hproduct', add_zero]
  exact nnObserverBlockPlan_blockMass u v kappa k

theorem nnObserverResidualLeft_eq_zero_of_eq_zero
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) {x : X} (hx : u x = 0) :
    nnObserverResidualLeft u v kappa x = 0 := by
  simp [nnObserverResidualLeft, hx]

theorem nnObserverResidualRight_eq_zero_of_eq_zero
    {X K : Type*} [Fintype X] [DecidableEq K]
    (u v : X → ℝ≥0) (kappa : X → K) {y : X} (hy : v y = 0) :
    nnObserverResidualRight u v kappa y = 0 := by
  simp [nnObserverResidualRight, hy]

/-- Internal transport accumulated through two nested observer levels. -/
def nnNestedInternalPlan
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L) (x y : X) : ℝ≥0 :=
  nnObserverBlockPlan u v kappa x y +
    nnObserverBlockPlan
      (nnObserverResidualLeft u v kappa)
      (nnObserverResidualRight u v kappa)
      (lambda ∘ kappa) x y

def nnNestedResidualLeft
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L) : X → ℝ≥0 :=
  nnObserverResidualLeft
    (nnObserverResidualLeft u v kappa)
    (nnObserverResidualRight u v kappa)
    (lambda ∘ kappa)

def nnNestedResidualRight
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L) : X → ℝ≥0 :=
  nnObserverResidualRight
    (nnObserverResidualLeft u v kappa)
    (nnObserverResidualRight u v kappa)
    (lambda ∘ kappa)

def nnNestedMaximalPlan
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L) (x y : X) : ℝ≥0 :=
  nnNestedInternalPlan u v kappa lambda x y +
    nnProductPlan
      (nnNestedResidualLeft u v kappa lambda)
      (nnNestedResidualRight u v kappa lambda) x y

theorem nnNestedInternalPlan_row_add_residual
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L) (x : X) :
    (∑ y, nnNestedInternalPlan u v kappa lambda x y) +
      nnNestedResidualLeft u v kappa lambda x = u x := by
  change (∑ y, (nnObserverBlockPlan u v kappa x y +
      nnObserverBlockPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa)
        (lambda ∘ kappa) x y)) +
      nnNestedResidualLeft u v kappa lambda x = u x
  rw [Finset.sum_add_distrib]
  change (∑ y, nnObserverBlockPlan u v kappa x y) +
      (∑ y, nnObserverBlockPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa)
        (lambda ∘ kappa) x y) +
      nnNestedResidualLeft u v kappa lambda x = u x
  rw [nnNestedResidualLeft, add_assoc, nnObserverBlockPlan_row_add_residual]
  exact nnObserverBlockPlan_row_add_residual u v kappa x

theorem nnNestedInternalPlan_col_add_residual
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L) (y : X) :
    (∑ x, nnNestedInternalPlan u v kappa lambda x y) +
      nnNestedResidualRight u v kappa lambda y = v y := by
  change (∑ x, (nnObserverBlockPlan u v kappa x y +
      nnObserverBlockPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa)
        (lambda ∘ kappa) x y)) +
      nnNestedResidualRight u v kappa lambda y = v y
  rw [Finset.sum_add_distrib]
  change (∑ x, nnObserverBlockPlan u v kappa x y) +
      (∑ x, nnObserverBlockPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa)
        (lambda ∘ kappa) x y) +
      nnNestedResidualRight u v kappa lambda y = v y
  rw [nnNestedResidualRight, add_assoc, nnObserverBlockPlan_col_add_residual]
  exact nnObserverBlockPlan_col_add_residual u v kappa y

theorem nnNestedResidual_mass_eq
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L)
    (hmass : nnProfileMass u = nnProfileMass v) :
    nnProfileMass (nnNestedResidualLeft u v kappa lambda) =
      nnProfileMass (nnNestedResidualRight u v kappa lambda) := by
  apply nnObserverResidual_mass_eq
  exact nnObserverResidual_mass_eq u v kappa hmass

theorem nnNestedInternalPlan_supported_coarse
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L)
    {x y : X} (hne : nnNestedInternalPlan u v kappa lambda x y ≠ 0) :
    (lambda ∘ kappa) x = (lambda ∘ kappa) y := by
  classical
  rw [nnNestedInternalPlan] at hne
  have hor : nnObserverBlockPlan u v kappa x y ≠ 0 ∨
      nnObserverBlockPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa)
        (lambda ∘ kappa) x y ≠ 0 := by
    by_cases hfirst : nnObserverBlockPlan u v kappa x y = 0
    · right
      intro hsecond
      exact hne (by simp [hfirst, hsecond])
    · exact Or.inl hfirst
  rcases hor with hfirst | hsecond
  · have hk : kappa x = kappa y := by
      by_contra hxy
      exact hfirst (by simp [nnObserverBlockPlan, hxy])
    exact congrArg lambda hk
  · by_contra hxy
    rw [nnObserverBlockPlan, if_neg hxy] at hsecond
    exact hsecond rfl

theorem nnNestedInternalPlan_blockMass_coarse
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L) (l : L) :
    nnCouplingBlockMass (nnNestedInternalPlan u v kappa lambda)
        (lambda ∘ kappa) l =
      min (nnFiberMass u (lambda ∘ kappa) l)
        (nnFiberMass v (lambda ∘ kappa) l) := by
  apply nnCouplingBlockMass_eq_min_of_balanced_oneSided
    u v
    (nnNestedResidualLeft u v kappa lambda)
    (nnNestedResidualRight u v kappa lambda)
    (nnNestedInternalPlan u v kappa lambda)
    (lambda ∘ kappa)
  · exact nnNestedInternalPlan_row_add_residual u v kappa lambda
  · exact nnNestedInternalPlan_col_add_residual u v kappa lambda
  · intro x y
    exact nnNestedInternalPlan_supported_coarse u v kappa lambda
  · exact nnObserverResidual_oneSided
      (nnObserverResidualLeft u v kappa)
      (nnObserverResidualRight u v kappa) (lambda ∘ kappa)

theorem nnProductPlan_nestedResidual_avoids_coarse
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L)
    {x y : X} (hxy : (lambda ∘ kappa) x = (lambda ∘ kappa) y) :
    nnProductPlan
      (nnNestedResidualLeft u v kappa lambda)
      (nnNestedResidualRight u v kappa lambda) x y = 0 := by
  exact nnProductPlan_residual_avoidsBlock
    (nnObserverResidualLeft u v kappa)
    (nnObserverResidualRight u v kappa)
    (lambda ∘ kappa) hxy

/-- Two nested finite observers admit one coupling maximal at both levels. -/
def nnNestedMaximalCoupling
    {X K L : Type*} [Fintype X] [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L)
    (hmass : nnProfileMass u = nnProfileMass v) : FiniteNNCoupling u v where
  plan := nnNestedMaximalPlan u v kappa lambda
  row := by
    intro x
    change (∑ y, (nnNestedInternalPlan u v kappa lambda x y +
      nnProductPlan
        (nnNestedResidualLeft u v kappa lambda)
        (nnNestedResidualRight u v kappa lambda) x y)) = u x
    rw [Finset.sum_add_distrib, nnProductPlan_row]
    · exact nnNestedInternalPlan_row_add_residual u v kappa lambda x
    · exact nnNestedResidual_mass_eq u v kappa lambda hmass
  col := by
    intro y
    change (∑ x, (nnNestedInternalPlan u v kappa lambda x y +
      nnProductPlan
        (nnNestedResidualLeft u v kappa lambda)
        (nnNestedResidualRight u v kappa lambda) x y)) = v y
    rw [Finset.sum_add_distrib, nnProductPlan_col]
    · exact nnNestedInternalPlan_col_add_residual u v kappa lambda y
    · exact nnNestedResidual_mass_eq u v kappa lambda hmass

theorem nnNestedMaximalCoupling_coarseAgreement
    {X K L : Type*} [Fintype X] [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L)
    (hmass : nnProfileMass u = nnProfileMass v) :
    nnCouplingAgreementMass
        (nnNestedMaximalCoupling u v kappa lambda hmass).plan
        (lambda ∘ kappa) =
      nnObserverCapacity u v (lambda ∘ kappa) := by
  classical
  unfold nnCouplingAgreementMass nnObserverCapacity
  apply Finset.sum_congr rfl
  intro l hl
  rw [show (nnNestedMaximalCoupling u v kappa lambda hmass).plan =
    nnNestedMaximalPlan u v kappa lambda from rfl]
  rw [show nnNestedMaximalPlan u v kappa lambda = fun x y =>
    nnNestedInternalPlan u v kappa lambda x y +
      nnProductPlan
        (nnNestedResidualLeft u v kappa lambda)
        (nnNestedResidualRight u v kappa lambda) x y from rfl]
  rw [nnCouplingBlockMass_add]
  have hproduct :
      nnCouplingBlockMass
        (nnProductPlan
          (nnNestedResidualLeft u v kappa lambda)
          (nnNestedResidualRight u v kappa lambda))
        (lambda ∘ kappa) l = 0 := by
    unfold nnCouplingBlockMass
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hlx : (lambda ∘ kappa) x = l
    · simp only [hlx, if_true]
      apply Finset.sum_eq_zero
      intro y hy
      by_cases hly : (lambda ∘ kappa) y = l
      · rw [if_pos hly]
        exact nnProductPlan_nestedResidual_avoids_coarse
          u v kappa lambda (hlx.trans hly.symm)
      · rw [if_neg hly]
    · rw [if_neg hlx]
  rw [hproduct, add_zero]
  exact nnNestedInternalPlan_blockMass_coarse u v kappa lambda l

theorem nnProductPlan_nestedResidual_avoids_fine
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L)
    {x y : X} (hxy : kappa x = kappa y) :
    nnProductPlan
      (nnNestedResidualLeft u v kappa lambda)
      (nnNestedResidualRight u v kappa lambda) x y = 0 := by
  classical
  rcases nnObserverResidual_oneSided u v kappa (kappa x) with hleft | hright
  · have hx₁ : nnObserverResidualLeft u v kappa x = 0 :=
      (nnFiberMass_eq_zero_iff _ kappa (kappa x)).mp hleft x rfl
    have hx₂ : nnNestedResidualLeft u v kappa lambda x = 0 := by
      exact nnObserverResidualLeft_eq_zero_of_eq_zero
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa)
        (lambda ∘ kappa) hx₁
    simp [nnProductPlan, hx₂]
  · have hy₁ : nnObserverResidualRight u v kappa y = 0 :=
      (nnFiberMass_eq_zero_iff _ kappa (kappa x)).mp hright y hxy.symm
    have hy₂ : nnNestedResidualRight u v kappa lambda y = 0 := by
      exact nnObserverResidualRight_eq_zero_of_eq_zero
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa)
        (lambda ∘ kappa) hy₁
    simp [nnProductPlan, hy₂]

theorem nnNestedSecondPlan_blockMass_fine_eq_zero
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L) (k : K) :
    nnCouplingBlockMass
      (nnObserverBlockPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa)
        (lambda ∘ kappa)) kappa k = 0 := by
  classical
  unfold nnCouplingBlockMass
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hkx : kappa x = k
  · rw [if_pos hkx]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases hky : kappa y = k
    · rw [if_pos hky]
      exact nnObserverBlockPlan_avoids_refinedBlock
        u v kappa (lambda ∘ kappa) (hkx.trans hky.symm)
    · rw [if_neg hky]
  · rw [if_neg hkx]

theorem nnNestedProductPlan_blockMass_fine_eq_zero
    {X K L : Type*} [Fintype X] [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L) (k : K) :
    nnCouplingBlockMass
      (nnProductPlan
        (nnNestedResidualLeft u v kappa lambda)
        (nnNestedResidualRight u v kappa lambda)) kappa k = 0 := by
  classical
  unfold nnCouplingBlockMass
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hkx : kappa x = k
  · rw [if_pos hkx]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases hky : kappa y = k
    · rw [if_pos hky]
      exact nnProductPlan_nestedResidual_avoids_fine
        u v kappa lambda (hkx.trans hky.symm)
    · rw [if_neg hky]
  · rw [if_neg hkx]

theorem nnNestedMaximalCoupling_fineAgreement
    {X K L : Type*} [Fintype X] [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L)
    (hmass : nnProfileMass u = nnProfileMass v) :
    nnCouplingAgreementMass
        (nnNestedMaximalCoupling u v kappa lambda hmass).plan kappa =
      nnObserverCapacity u v kappa := by
  classical
  unfold nnCouplingAgreementMass nnObserverCapacity
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (nnNestedMaximalCoupling u v kappa lambda hmass).plan =
    nnNestedMaximalPlan u v kappa lambda from rfl]
  rw [show nnNestedMaximalPlan u v kappa lambda = fun x y =>
    (nnObserverBlockPlan u v kappa x y +
      nnObserverBlockPlan
        (nnObserverResidualLeft u v kappa)
        (nnObserverResidualRight u v kappa)
        (lambda ∘ kappa) x y) +
      nnProductPlan
        (nnNestedResidualLeft u v kappa lambda)
        (nnNestedResidualRight u v kappa lambda) x y from rfl]
  rw [nnCouplingBlockMass_add, nnCouplingBlockMass_add,
    nnNestedSecondPlan_blockMass_fine_eq_zero,
    nnNestedProductPlan_blockMass_fine_eq_zero, add_zero, add_zero]
  exact nnObserverBlockPlan_blockMass u v kappa k

/-- Certified simultaneous-maximality package for the first nontrivial hierarchy. -/
theorem exists_coupling_simultaneously_maximal_for_two_nested_observers
    {X K L : Type*} [Fintype X] [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (u v : X → ℝ≥0) (kappa : X → K) (lambda : K → L)
    (hmass : nnProfileMass u = nnProfileMass v) :
    ∃ gamma : FiniteNNCoupling u v,
      nnCouplingAgreementMass gamma.plan kappa = nnObserverCapacity u v kappa ∧
      nnCouplingAgreementMass gamma.plan (lambda ∘ kappa) =
        nnObserverCapacity u v (lambda ∘ kappa) := by
  exact ⟨nnNestedMaximalCoupling u v kappa lambda hmass,
    nnNestedMaximalCoupling_fineAgreement u v kappa lambda hmass,
    nnNestedMaximalCoupling_coarseAgreement u v kappa lambda hmass⟩

end

end HTGeometry
