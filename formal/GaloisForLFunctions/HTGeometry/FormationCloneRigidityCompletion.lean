import GaloisForLFunctions.HTGeometry.FormationCloneRigidityLaw
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def finiteFormationSqrtVector {X : Type*} [Fintype X]
    (p : X → ℝ) : EuclideanSpace ℝ X :=
  (EuclideanSpace.equiv X ℝ).symm (fun x ↦ Real.sqrt (p x))

/-- Root Hellinger distance as Euclidean distance between square-root packets. -/
def finiteFormationHellinger {X : Type*} [Fintype X]
    (p q : X → ℝ) : ℝ :=
  dist (finiteFormationSqrtVector p) (finiteFormationSqrtVector q)

theorem finiteFormationHellinger_triangle {X : Type*} [Fintype X]
    (p q r : X → ℝ) :
    finiteFormationHellinger p r ≤
      finiteFormationHellinger p q + finiteFormationHellinger q r :=
  dist_triangle _ _ _

theorem finiteFormationHellinger_sq
    {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    finiteFormationHellinger p q ^ 2 = 2 - 2 * finiteFormationAffinity p q := by
  rw [finiteFormationHellinger, EuclideanSpace.dist_sq_eq]
  change (∑ i, dist (Real.sqrt (p i)) (Real.sqrt (q i)) ^ 2) = _
  simp_rw [Real.dist_eq, sq_abs]
  unfold finiteFormationAffinity
  calc
    (∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2) =
        ∑ i, (p i + q i - 2 * (Real.sqrt (p i) * Real.sqrt (q i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 =
            Real.sqrt (p i) ^ 2 + Real.sqrt (q i) ^ 2 -
              2 * (Real.sqrt (p i) * Real.sqrt (q i)) := by ring
        _ = p i + q i - 2 * (Real.sqrt (p i) * Real.sqrt (q i)) := by
          rw [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
    _ = 2 - 2 * ∑ i, Real.sqrt (p i) * Real.sqrt (q i) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
        hpsum, hqsum]
      ring

theorem finiteFormationHellinger_eq_sqrt
    {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    finiteFormationHellinger p q =
      Real.sqrt (2 - 2 * finiteFormationAffinity p q) := by
  rw [← finiteFormationHellinger_sq p q hp hq hpsum hqsum]
  exact (Real.sqrt_sq (dist_nonneg : 0 ≤ finiteFormationHellinger p q)).symm

theorem finiteSplitRecovery_nonneg
    {X H : Type*} (p : X → ℝ) (kappa : X → H → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x h, 0 ≤ kappa x h) :
    ∀ z, 0 ≤ finiteSplitRecovery p kappa z := by
  intro z
  exact mul_nonneg (hp z.1) (hk z.1 z.2)

theorem finiteSplitRecovery_sum
    {X H : Type*} [Fintype X] [Fintype H]
    (p : X → ℝ) (kappa : X → H → ℝ)
    (hpsum : ∑ x, p x = 1) (hrow : ∀ x, ∑ h, kappa x h = 1) :
    ∑ z, finiteSplitRecovery p kappa z = 1 := by
  unfold finiteSplitRecovery
  rw [Fintype.sum_prod_type]
  calc
    (∑ x, ∑ h, p x * kappa x h) = ∑ x, p x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.mul_sum, hrow x, mul_one]
    _ = 1 := hpsum

/-- Common split recovery retains the base coordinate and is exactly Hellinger-isometric. -/
theorem finiteFormationHellinger_splitRecovery
    {X H : Type*} [Fintype X] [Fintype H]
    (p q : X → ℝ) (kappa : X → H → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    (hk : ∀ x h, 0 ≤ kappa x h)
    (hrow : ∀ x, ∑ h, kappa x h = 1) :
    finiteFormationHellinger (finiteSplitRecovery p kappa)
        (finiteSplitRecovery q kappa) = finiteFormationHellinger p q := by
  have hpLift := finiteSplitRecovery_nonneg p kappa hp hk
  have hqLift := finiteSplitRecovery_nonneg q kappa hq hk
  have hpLiftSum := finiteSplitRecovery_sum p kappa hpsum hrow
  have hqLiftSum := finiteSplitRecovery_sum q kappa hqsum hrow
  have hLift := finiteFormationHellinger_sq
    (finiteSplitRecovery p kappa) (finiteSplitRecovery q kappa)
    hpLift hqLift hpLiftSum hqLiftSum
  have hBase := finiteFormationHellinger_sq p q hp hq hpsum hqsum
  rw [finiteFormationAffinity_splitRecovery p q kappa hp hq hk hrow] at hLift
  nlinarith [show 0 ≤ finiteFormationHellinger
      (finiteSplitRecovery p kappa) (finiteSplitRecovery q kappa) from dist_nonneg,
    show 0 ≤ finiteFormationHellinger p q from dist_nonneg]

theorem finiteFormationHellinger_markovDataProcessing
    {X Y : Type*} [Fintype X] [Fintype Y]
    (K : FiniteMarkovKernel X Y) (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    finiteFormationHellinger
        (K.toFinitePositiveKernel.applyReal p)
        (K.toFinitePositiveKernel.applyReal q) ≤
      finiteFormationHellinger p q := by
  let P := K.toFinitePositiveKernel.applyReal p
  let Q := K.toFinitePositiveKernel.applyReal q
  have hP : ∀ y, 0 ≤ P y := fun y ↦
    Finset.sum_nonneg fun x _ ↦ mul_nonneg (K.nonneg y x) (hp x)
  have hQ : ∀ y, 0 ≤ Q y := fun y ↦
    Finset.sum_nonneg fun x _ ↦ mul_nonneg (K.nonneg y x) (hq x)
  have hPsum : ∑ y, P y = 1 := by
    unfold P FinitePositiveKernel.applyReal
    rw [Finset.sum_comm]
    calc
      (∑ x, ∑ y, K.weight y x * p x) = ∑ x, p x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.sum_mul, K.column_sum x, one_mul]
      _ = 1 := hpsum
  have hQsum : ∑ y, Q y = 1 := by
    unfold Q FinitePositiveKernel.applyReal
    rw [Finset.sum_comm]
    calc
      (∑ x, ∑ y, K.weight y x * q x) = ∑ x, q x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.sum_mul, K.column_sum x, one_mul]
      _ = 1 := hqsum
  rw [finiteFormationHellinger_eq_sqrt P Q hP hQ hPsum hQsum,
    finiteFormationHellinger_eq_sqrt p q hp hq hpsum hqsum]
  apply Real.sqrt_le_sqrt
  nlinarith [finiteFormationAffinity_markovDataProcessing K p q hp hq]

/-- Independent `d`-fold packet formation. -/
def finiteIndependentPower {X : Type*} (p : X → ℝ) (d : ℕ) : (Fin d → X) → ℝ :=
  fun z ↦ ∏ i, p (z i)

theorem finiteIndependentPower_nonneg {X : Type*}
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (d : ℕ) (z : Fin d → X) :
    0 ≤ finiteIndependentPower p d z := by
  exact Finset.prod_nonneg fun i hi ↦ hp (z i)

theorem finiteIndependentPower_sum
    {X : Type*} [Fintype X] (p : X → ℝ) (d : ℕ) :
    ∑ z : Fin d → X, finiteIndependentPower p d z = (∑ x, p x) ^ d := by
  simp only [finiteIndependentPower]
  simpa using (Finset.sum_pow' (Finset.univ : Finset X) p d).symm

theorem finiteFormationAffinity_independentPower
    {X : Type*} [Fintype X] (p q : X → ℝ) (d : ℕ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    finiteFormationAffinity (finiteIndependentPower p d) (finiteIndependentPower q d) =
      finiteFormationAffinity p q ^ d := by
  unfold finiteFormationAffinity finiteIndependentPower
  calc
    (∑ z : Fin d → X,
        Real.sqrt (∏ i, p (z i)) * Real.sqrt (∏ i, q (z i))) =
        ∑ z : Fin d → X, ∏ i,
          (Real.sqrt (p (z i)) * Real.sqrt (q (z i))) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Real.sqrt_prod Finset.univ (fun i _ ↦ hp (z i)),
        Real.sqrt_prod Finset.univ (fun i _ ↦ hq (z i)),
        Finset.prod_mul_distrib]
    _ = (∑ x, Real.sqrt (p x) * Real.sqrt (q x)) ^ d := by
      simpa using (Finset.sum_pow' (Finset.univ : Finset X)
        (fun x ↦ Real.sqrt (p x) * Real.sqrt (q x)) d).symm

/-- **Unavoidable independent-formation defect.** Every common Markov formation attempt pays the
paper's exact Hellinger wall. -/
theorem finiteFormationHellinger_cloneDefect_lowerBound
    {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    (d : ℕ) (K : FiniteMarkovKernel X (Fin d → X)) :
    Real.sqrt (2 - 2 * finiteFormationAffinity p q ^ d) -
        Real.sqrt (2 - 2 * finiteFormationAffinity p q) ≤
      finiteFormationHellinger
          (K.toFinitePositiveKernel.applyReal p) (finiteIndependentPower p d) +
        finiteFormationHellinger
          (K.toFinitePositiveKernel.applyReal q) (finiteIndependentPower q d) := by
  let P := finiteIndependentPower p d
  let Q := finiteIndependentPower q d
  let r := K.toFinitePositiveKernel.applyReal p
  let s := K.toFinitePositiveKernel.applyReal q
  have hP : ∀ z, 0 ≤ P z := finiteIndependentPower_nonneg p hp d
  have hQ : ∀ z, 0 ≤ Q z := finiteIndependentPower_nonneg q hq d
  have hPsum : ∑ z, P z = 1 := by
    rw [finiteIndependentPower_sum, hpsum, one_pow]
  have hQsum : ∑ z, Q z = 1 := by
    rw [finiteIndependentPower_sum, hqsum, one_pow]
  have htriangle : finiteFormationHellinger P Q ≤
      finiteFormationHellinger r P + finiteFormationHellinger r s +
        finiteFormationHellinger s Q := by
    calc
      finiteFormationHellinger P Q ≤
          finiteFormationHellinger P r + finiteFormationHellinger r Q :=
        finiteFormationHellinger_triangle P r Q
      _ ≤ finiteFormationHellinger P r +
          (finiteFormationHellinger r s + finiteFormationHellinger s Q) :=
        by simpa [add_comm] using
          add_le_add_left (finiteFormationHellinger_triangle r s Q)
            (finiteFormationHellinger P r)
      _ = finiteFormationHellinger r P + finiteFormationHellinger r s +
          finiteFormationHellinger s Q := by
        rw [show finiteFormationHellinger P r = finiteFormationHellinger r P by
          exact dist_comm _ _]
        ring
  have hdp : finiteFormationHellinger r s ≤ finiteFormationHellinger p q :=
    finiteFormationHellinger_markovDataProcessing K p q hp hq hpsum hqsum
  have hformulaPQ := finiteFormationHellinger_eq_sqrt P Q hP hQ hPsum hQsum
  rw [finiteFormationAffinity_independentPower p q d hp hq] at hformulaPQ
  have hformulapq := finiteFormationHellinger_eq_sqrt p q hp hq hpsum hqsum
  rw [hformulaPQ] at htriangle
  rw [hformulapq] at hdp
  dsimp only [P, Q, r, s] at htriangle ⊢
  linarith

theorem finiteFormationHellinger_cloneWall_pos
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) {d : ℕ} (hd : 2 ≤ d) :
    0 < Real.sqrt (2 - 2 * a ^ d) - Real.sqrt (2 - 2 * a) := by
  have hpow : a ^ d < a := pow_lt_self_of_lt_one₀ ha0 ha1 (by omega)
  have hbase : 0 ≤ 2 - 2 * a := by linarith
  have hrad : 2 - 2 * a < 2 - 2 * a ^ d := by linarith
  exact sub_pos.mpr (Real.sqrt_lt_sqrt hbase hrad)

/-- Pointwise mutual singularity for finite nonnegative packets. -/
def FiniteFormationSingular {X : Type*} (p q : X → ℝ) : Prop :=
  ∀ x, p x = 0 ∨ q x = 0

theorem finiteFormationAffinity_eq_zero_iff_singular
    {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) :
    finiteFormationAffinity p q = 0 ↔ FiniteFormationSingular p q := by
  constructor
  · intro hzero x
    unfold finiteFormationAffinity at hzero
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi ↦ by positivity)).mp
      hzero x (Finset.mem_univ x)
    rcases mul_eq_zero.mp hterm with h | h
    · exact Or.inl ((Real.sqrt_eq_zero (hp x)).mp h)
    · exact Or.inr ((Real.sqrt_eq_zero (hq x)).mp h)
  · intro hsing
    unfold finiteFormationAffinity
    apply Finset.sum_eq_zero
    intro x hx
    rcases hsing x with h | h <;> simp [h]

theorem finiteFormationAffinity_eq_one_iff_eq
    {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    finiteFormationAffinity p q = 1 ↔ p = q := by
  constructor
  · intro hone
    have hsq := finiteFormationHellinger_sq p q hp hq hpsum hqsum
    rw [hone] at hsq
    have hzero : finiteFormationHellinger p q = 0 := by
      have hnonneg : 0 ≤ finiteFormationHellinger p q := dist_nonneg
      nlinarith
    have hv : finiteFormationSqrtVector p = finiteFormationSqrtVector q :=
      dist_eq_zero.mp hzero
    funext x
    apply (Real.sqrt_inj (hp x) (hq x)).mp
    have := congrArg (fun v : EuclideanSpace ℝ X ↦
      (EuclideanSpace.equiv X ℝ v) x) hv
    simpa [finiteFormationSqrtVector] using this
  · intro hpq
    subst q
    unfold finiteFormationAffinity
    simpa [Real.sq_sqrt, hp] using hpsum

/-- General-depth exact cloning can only occur in the identical or singular chambers. -/
theorem finiteFormationClone_classification_forward
    {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    {d : ℕ} (hd : 2 ≤ d) (K : FiniteMarkovKernel X (Fin d → X))
    (hclonep : K.toFinitePositiveKernel.applyReal p = finiteIndependentPower p d)
    (hcloneq : K.toFinitePositiveKernel.applyReal q = finiteIndependentPower q d) :
    p = q ∨ FiniteFormationSingular p q := by
  let a := finiteFormationAffinity p q
  have ha0 : 0 ≤ a := finiteFormationAffinity_nonneg p q
  have ha1 : a ≤ 1 := finiteFormationAffinity_le_one p q hp hq hpsum hqsum
  have hle : a ≤ a ^ d := by
    have hdp := finiteFormationAffinity_markovDataProcessing K p q hp hq
    rw [hclonep, hcloneq, finiteFormationAffinity_independentPower p q d hp hq] at hdp
    exact hdp
  have hextreme : a = 0 ∨ a = 1 := by
    rcases ha0.eq_or_lt with ha | ha
    · exact Or.inl ha.symm
    by_cases hne : a = 1
    · exact Or.inr hne
    have halt : a < 1 := lt_of_le_of_ne ha1 hne
    have hpow := pow_lt_self_of_lt_one₀ ha halt (by omega : 1 < d)
    linarith
  rcases hextreme with hzero | hone
  · exact Or.inr ((finiteFormationAffinity_eq_zero_iff_singular p q hp hq).mp hzero)
  · exact Or.inl ((finiteFormationAffinity_eq_one_iff_eq
      p q hp hq hpsum hqsum).mp hone)

/-- A Markov kernel which ignores its input and prepares one fixed probability packet. -/
def finitePreparationKernel {X Y : Type*} [Fintype X] [Fintype Y]
    (r : Y → ℝ) (hr : ∀ y, 0 ≤ r y) (hrsum : ∑ y, r y = 1) :
    FiniteMarkovKernel X Y where
  weight y _ := r y
  nonneg y _ := hr y
  column_sum _ := hrsum

theorem finitePreparationKernel_applyReal
    {X Y : Type*} [Fintype X] [Fintype Y]
    (r : Y → ℝ) (hr : ∀ y, 0 ≤ r y) (hrsum : ∑ y, r y = 1)
    (p : X → ℝ) (hpsum : ∑ x, p x = 1) :
    (finitePreparationKernel r hr hrsum).toFinitePositiveKernel.applyReal p = r := by
  funext y
  unfold FinitePositiveKernel.applyReal finitePreparationKernel
  rw [← Finset.mul_sum, hpsum, mul_one]

/-- One common kernel which recognizes pointwise-disjoint supports and prepares the corresponding
independent product packet. -/
def finiteSingularCloneKernel
    {X : Type*} [Fintype X] (p q : X → ℝ) (d : ℕ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    FiniteMarkovKernel X (Fin d → X) where
  weight z x :=
    if p x = 0 then
      if q x = 0 then finiteIndependentPower p d z else finiteIndependentPower q d z
    else finiteIndependentPower p d z
  nonneg z x := by
    split
    · split
      · exact finiteIndependentPower_nonneg p hp d z
      · exact finiteIndependentPower_nonneg q hq d z
    · exact finiteIndependentPower_nonneg p hp d z
  column_sum x := by
    by_cases hpx : p x = 0
    · by_cases hqx : q x = 0
      · simp only [hpx, hqx, if_true]
        rw [finiteIndependentPower_sum, hpsum, one_pow]
      · simp only [hpx, hqx, if_true, if_false]
        rw [finiteIndependentPower_sum, hqsum, one_pow]
    · simp only [hpx, if_false]
      rw [finiteIndependentPower_sum, hpsum, one_pow]

theorem finiteSingularCloneKernel_apply_left
    {X : Type*} [Fintype X] (p q : X → ℝ) (d : ℕ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    (finiteSingularCloneKernel p q d hp hq hpsum hqsum).toFinitePositiveKernel.applyReal p =
      finiteIndependentPower p d := by
  funext z
  unfold FinitePositiveKernel.applyReal finiteSingularCloneKernel
  calc
    (∑ x, (if p x = 0 then
        if q x = 0 then finiteIndependentPower p d z else finiteIndependentPower q d z
      else finiteIndependentPower p d z) * p x) =
        ∑ x, finiteIndependentPower p d z * p x := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hpx : p x = 0 <;> simp [hpx]
    _ = finiteIndependentPower p d z * ∑ x, p x := by rw [Finset.mul_sum]
    _ = finiteIndependentPower p d z := by rw [hpsum, mul_one]

theorem finiteSingularCloneKernel_apply_right
    {X : Type*} [Fintype X] (p q : X → ℝ) (d : ℕ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    (hsing : FiniteFormationSingular p q) :
    (finiteSingularCloneKernel p q d hp hq hpsum hqsum).toFinitePositiveKernel.applyReal q =
      finiteIndependentPower q d := by
  funext z
  unfold FinitePositiveKernel.applyReal finiteSingularCloneKernel
  calc
    (∑ x, (if p x = 0 then
        if q x = 0 then finiteIndependentPower p d z else finiteIndependentPower q d z
      else finiteIndependentPower p d z) * q x) =
        ∑ x, finiteIndependentPower q d z * q x := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hpx : p x = 0
      · by_cases hqx : q x = 0 <;> simp [hpx, hqx]
      · have hqx : q x = 0 := (hsing x).resolve_left hpx
        simp [hpx, hqx]
    _ = finiteIndependentPower q d z * ∑ x, q x := by rw [Finset.mul_sum]
    _ = finiteIndependentPower q d z := by rw [hqsum, mul_one]

/-- **Exact general-depth cloning classification.** One common independent `d`-formation exists
iff the two packets are identical or pointwise singular. -/
theorem finiteFormationClone_exists_iff
    {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    {d : ℕ} (hd : 2 ≤ d) :
    (∃ K : FiniteMarkovKernel X (Fin d → X),
        K.toFinitePositiveKernel.applyReal p = finiteIndependentPower p d ∧
        K.toFinitePositiveKernel.applyReal q = finiteIndependentPower q d) ↔
      p = q ∨ FiniteFormationSingular p q := by
  constructor
  · rintro ⟨K, hclonep, hcloneq⟩
    exact finiteFormationClone_classification_forward
      p q hp hq hpsum hqsum hd K hclonep hcloneq
  · intro h
    rcases h with hpq | hsing
    · subst q
      let P := finiteIndependentPower p d
      have hP : ∀ z, 0 ≤ P z := finiteIndependentPower_nonneg p hp d
      have hPsum : ∑ z, P z = 1 := by
        rw [finiteIndependentPower_sum, hpsum, one_pow]
      exact ⟨finitePreparationKernel P hP hPsum,
        finitePreparationKernel_applyReal P hP hPsum p hpsum,
        finitePreparationKernel_applyReal P hP hPsum p hpsum⟩
    · exact ⟨finiteSingularCloneKernel p q d hp hq hpsum hqsum,
        finiteSingularCloneKernel_apply_left p q d hp hq hpsum hqsum,
        finiteSingularCloneKernel_apply_right p q d hp hq hpsum hqsum hsing⟩

/-- **Cofinal formation properness.** Vanishing approximate-cloning error along unbounded replica
depth forces the identical or singular chamber. -/
theorem finiteFormationClone_cofinalProperness
    {X : Type*} [Fintype X] (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1)
    (d : ℕ → ℕ) (K : ∀ n, FiniteMarkovKernel X (Fin (d n) → X))
    (hd : Filter.Tendsto d Filter.atTop Filter.atTop)
    (herror : Filter.Tendsto
      (fun n ↦
        finiteFormationHellinger
            ((K n).toFinitePositiveKernel.applyReal p) (finiteIndependentPower p (d n)) +
          finiteFormationHellinger
            ((K n).toFinitePositiveKernel.applyReal q) (finiteIndependentPower q (d n)))
      Filter.atTop (nhds 0)) :
    p = q ∨ FiniteFormationSingular p q := by
  by_contra hconclusion
  have hpne : p ≠ q := fun h ↦ hconclusion (Or.inl h)
  have hnsing : ¬ FiniteFormationSingular p q := fun h ↦ hconclusion (Or.inr h)
  let a := finiteFormationAffinity p q
  have ha0 : 0 ≤ a := finiteFormationAffinity_nonneg p q
  have ha1 : a ≤ 1 := finiteFormationAffinity_le_one p q hp hq hpsum hqsum
  have hane0 : a ≠ 0 := fun h ↦
    hnsing ((finiteFormationAffinity_eq_zero_iff_singular p q hp hq).mp h)
  have hane1 : a ≠ 1 := fun h ↦
    hpne ((finiteFormationAffinity_eq_one_iff_eq p q hp hq hpsum hqsum).mp h)
  have ha0' : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hane0)
  have ha1' : a < 1 := lt_of_le_of_ne ha1 hane1
  let wall := Real.sqrt (2 - 2 * a ^ 2) - Real.sqrt (2 - 2 * a)
  have hwall : 0 < wall := finiteFormationHellinger_cloneWall_pos a ha0' ha1' le_rfl
  have hdepth : ∀ᶠ n in Filter.atTop, 2 ≤ d n :=
    (Filter.tendsto_atTop.1 hd) 2
  have hsmall : ∀ᶠ n in Filter.atTop,
      finiteFormationHellinger
            ((K n).toFinitePositiveKernel.applyReal p) (finiteIndependentPower p (d n)) +
          finiteFormationHellinger
            ((K n).toFinitePositiveKernel.applyReal q) (finiteIndependentPower q (d n)) < wall :=
    (tendsto_order.1 herror).2 wall hwall
  obtain ⟨n, hdn, hnsmall⟩ := (hdepth.and hsmall).exists
  have hpow : a ^ d n ≤ a ^ 2 :=
    pow_le_pow_of_le_one ha0 ha1 hdn
  have hsqrt : Real.sqrt (2 - 2 * a ^ 2) ≤
      Real.sqrt (2 - 2 * a ^ d n) :=
    Real.sqrt_le_sqrt (by linarith)
  have hwall_le : wall ≤
      Real.sqrt (2 - 2 * a ^ d n) - Real.sqrt (2 - 2 * a) :=
    sub_le_sub_right hsqrt _
  have hdefect := finiteFormationHellinger_cloneDefect_lowerBound
    p q hp hq hpsum hqsum (d n) (K n)
  dsimp only [a] at hdefect hwall_le
  exact (not_lt_of_ge (hwall_le.trans hdefect)) hnsmall

/-- Reflected-family selector: common support eliminates the singular branch, so a common clone
forces the neutral parameter. -/
theorem finiteFormationClone_reflectedSelection
    {I X : Type*} [AddGroup I] [Fintype X]
    (packet : I → X → ℝ)
    (hp : ∀ a x, 0 ≤ packet a x)
    (hsum : ∀ a, ∑ x, packet a x = 1)
    (hident : ∀ a, packet a = packet (-a) ↔ a = 0)
    (hcommon : ∀ a, ¬ FiniteFormationSingular (packet a) (packet (-a)))
    {d : ℕ} (hd : 2 ≤ d) (a : I)
    (K : FiniteMarkovKernel X (Fin d → X))
    (hclonep : K.toFinitePositiveKernel.applyReal (packet a) =
      finiteIndependentPower (packet a) d)
    (hcloneq : K.toFinitePositiveKernel.applyReal (packet (-a)) =
      finiteIndependentPower (packet (-a)) d) :
    a = 0 := by
  rcases finiteFormationClone_classification_forward
      (packet a) (packet (-a)) (hp a) (hp (-a)) (hsum a) (hsum (-a))
      hd K hclonep hcloneq with heq | hsing
  · exact (hident a).mp heq
  · exact (hcommon a hsing).elim

/-- Paper-facing selection corollary: one atom with positive mass in both reflected packets
eliminates the singular branch. -/
theorem finiteFormationClone_reflectedSelection_of_commonPositive
    {I X : Type*} [AddGroup I] [Fintype X]
    (packet : I → X → ℝ)
    (hp : ∀ a x, 0 ≤ packet a x)
    (hsum : ∀ a, ∑ x, packet a x = 1)
    (hident : ∀ a, packet a = packet (-a) ↔ a = 0)
    (hcommonPositive : ∀ a, ∃ x, 0 < packet a x ∧ 0 < packet (-a) x)
    {d : ℕ} (hd : 2 ≤ d) (a : I)
    (K : FiniteMarkovKernel X (Fin d → X))
    (hclonep : K.toFinitePositiveKernel.applyReal (packet a) =
      finiteIndependentPower (packet a) d)
    (hcloneq : K.toFinitePositiveKernel.applyReal (packet (-a)) =
      finiteIndependentPower (packet (-a)) d) :
    a = 0 := by
  apply finiteFormationClone_reflectedSelection packet hp hsum hident
    (fun b hsing ↦ ?_) hd a K hclonep hcloneq
  obtain ⟨x, hx, hreflect⟩ := hcommonPositive b
  rcases hsing x with h | h
  · exact (ne_of_gt hx h).elim
  · exact (ne_of_gt hreflect h).elim

/-- Push a finite packet forward along a bijective reflection/relabeling. -/
def finitePacketReindex {X : Type*} (R : X ≃ X) (p : X → ℝ) : X → ℝ :=
  fun x ↦ p (R.symm x)

theorem finitePacketReindex_sum {X : Type*} [Fintype X]
    (R : X ≃ X) (p : X → ℝ) :
    ∑ x, finitePacketReindex R p x = ∑ x, p x := by
  exact Equiv.sum_comp R.symm p

/-- Hellinger affinity is invariant under every common bijective reflection. -/
theorem finiteFormationAffinity_reindex
    {X : Type*} [Fintype X] (R : X ≃ X) (p q : X → ℝ) :
    finiteFormationAffinity (finitePacketReindex R p) (finitePacketReindex R q) =
      finiteFormationAffinity p q := by
  unfold finiteFormationAffinity finitePacketReindex
  exact Equiv.sum_comp R.symm
    (fun x ↦ Real.sqrt (p x) * Real.sqrt (q x))

theorem finiteFormationHellinger_reindex
    {X : Type*} [Fintype X] (R : X ≃ X) (p q : X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    finiteFormationHellinger (finitePacketReindex R p) (finitePacketReindex R q) =
      finiteFormationHellinger p q := by
  have hRp : ∀ x, 0 ≤ finitePacketReindex R p x := fun x ↦ hp (R.symm x)
  have hRq : ∀ x, 0 ≤ finitePacketReindex R q x := fun x ↦ hq (R.symm x)
  have hRpsum : ∑ x, finitePacketReindex R p x = 1 :=
    (finitePacketReindex_sum R p).trans hpsum
  have hRqsum : ∑ x, finitePacketReindex R q x = 1 :=
    (finitePacketReindex_sum R q).trans hqsum
  rw [finiteFormationHellinger_eq_sqrt
      (finitePacketReindex R p) (finitePacketReindex R q) hRp hRq hRpsum hRqsum,
    finiteFormationHellinger_eq_sqrt p q hp hq hpsum hqsum,
    finiteFormationAffinity_reindex]

/-- Coordinatewise reindexing of a product packet. -/
def finitePowerReindex {X : Type*} (R : X ≃ X) {d : ℕ}
    (r : (Fin d → X) → ℝ) : (Fin d → X) → ℝ :=
  fun z ↦ r (fun i ↦ R.symm (z i))

theorem finiteIndependentPower_reindex
    {X : Type*} (R : X ≃ X) (p : X → ℝ) (d : ℕ) :
    finitePowerReindex R (finiteIndependentPower p d) =
      finiteIndependentPower (finitePacketReindex R p) d := by
  rfl

/-- Deterministic diagonal broadcast on a `d`-fold product. -/
def finiteDiagonalKernel {X : Type*} [Fintype X] [DecidableEq X] (d : ℕ) :
    FiniteMarkovKernel X (Fin d → X) where
  weight z x := if z = fun _ ↦ x then 1 else 0
  nonneg z x := by split <;> positivity
  column_sum x := by
    classical
    simp

def finiteDiagonalPower {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (d : ℕ) : (Fin d → X) → ℝ :=
  (finiteDiagonalKernel d).toFinitePositiveKernel.applyReal p

theorem finiteDiagonalPower_apply
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (d : ℕ) (z : Fin d → X) :
    finiteDiagonalPower p d z = ∑ x, if z = fun _ ↦ x then p x else 0 := by
  classical
  unfold finiteDiagonalPower finiteDiagonalKernel FinitePositiveKernel.applyReal
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : z = fun _ ↦ x <;> simp [h]

theorem finiteDiagonalPower_const
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) {d : ℕ} (hd : 0 < d) (x : X) :
    finiteDiagonalPower p d (fun _ ↦ x) = p x := by
  classical
  rw [finiteDiagonalPower_apply]
  calc
    (∑ y, if (fun _ : Fin d ↦ x) = (fun _ ↦ y) then p y else 0) =
        (if (fun _ : Fin d ↦ x) = (fun _ ↦ x) then p x else 0) := by
      apply Finset.sum_eq_single x
      · intro y hy hyx
        have hfun : (fun _ : Fin d ↦ x) ≠ fun _ ↦ y := by
          intro h
          exact hyx (congrFun h ⟨0, hd⟩).symm
        simp [hfun]
      · simp
    _ = p x := by simp

theorem finiteDiagonalPower_eq_zero_of_nonconstant
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) {d : ℕ} (z : Fin d → X)
    (hz : ∀ x, z ≠ fun _ ↦ x) :
    finiteDiagonalPower p d z = 0 := by
  classical
  rw [finiteDiagonalPower_apply]
  apply Finset.sum_eq_zero
  intro x hx
  simp [hz x]

/-- Every coordinate marginal of diagonal broadcast is the source packet. -/
theorem finiteDiagonalPower_marginal
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) {d : ℕ} (i : Fin d) (x : X) :
    ∑ z, (if z i = x then finiteDiagonalPower p d z else 0) = p x := by
  classical
  simp_rw [finiteDiagonalPower_apply]
  calc
    (∑ z, if z i = x then
        ∑ y, if z = fun _ ↦ y then p y else 0 else 0) =
        ∑ z, ∑ y, if z i = x then (
          if z = fun _ ↦ y then p y else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hzx : z i = x <;> simp [hzx]
    _ = ∑ y, if y = x then p y else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ z, if z i = x then
            (if z = (fun _ : Fin d ↦ y) then p y else 0) else 0) =
            (if (fun _ : Fin d ↦ y) i = x then
              (if (fun _ : Fin d ↦ y) = (fun _ ↦ y) then p y else 0) else 0) := by
          apply Finset.sum_eq_single (fun _ : Fin d ↦ y)
          · intro z hz hne
            simp [hne]
          · simp
        _ = if y = x then p y else 0 := by simp
    _ = p x := by simp

/-- Exact diagonal/product affinity before rewriting it as a Rényi entropy. -/
theorem finiteFormationAffinity_diagonalPower
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) {d : ℕ} (hd : 0 < d) :
    finiteFormationAffinity (finiteDiagonalPower p d) (finiteIndependentPower p d) =
      ∑ x, Real.sqrt (p x) * Real.sqrt (p x ^ d) := by
  classical
  let c : X → (Fin d → X) := fun x _ ↦ x
  let f : (Fin d → X) → ℝ := fun z ↦
    Real.sqrt (finiteDiagonalPower p d z) * Real.sqrt (finiteIndependentPower p d z)
  have hc : Function.Injective c := by
    intro x y hxy
    exact congrFun hxy ⟨0, hd⟩
  have hsubset : Finset.univ.image c ⊆ (Finset.univ : Finset (Fin d → X)) :=
    Finset.subset_univ _
  have hout : ∀ z ∈ (Finset.univ : Finset (Fin d → X)), z ∉ Finset.univ.image c →
      f z = 0 := by
    intro z hz hnot
    have hnconst : ∀ x, z ≠ fun _ ↦ x := by
      intro x hzx
      apply hnot
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, by simpa [c] using hzx.symm⟩
    dsimp only [f]
    rw [show finiteDiagonalPower p d z = 0 from
      finiteDiagonalPower_eq_zero_of_nonconstant p z hnconst]
    simp
  change ∑ z, f z = _
  calc
    (∑ z, f z) = ∑ z ∈ Finset.univ.image c, f z :=
      (Finset.sum_subset hsubset hout).symm
    _ = ∑ x, f (c x) := by
      rw [Finset.sum_image]
      exact fun x hx y hy hxy ↦ hc hxy
    _ = ∑ x, Real.sqrt (p x) * Real.sqrt (p x ^ d) := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp only [f]
      rw [show finiteDiagonalPower p d (c x) = p x by
        exact finiteDiagonalPower_const p hd x]
      simp [c, finiteIndependentPower]

theorem sqrt_mul_sqrt_pow_eq_rpow
    (x : ℝ) (hx : 0 ≤ x) {d : ℕ} (hd : 0 < d) :
    Real.sqrt x * Real.sqrt (x ^ d) = x ^ (((d : ℝ) + 1) / 2) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  rw [← Real.rpow_add_of_nonneg hx (by positivity) (by positivity)]
  congr 2
  ring

/-- Paper formula `A(Δ_*p,p^⊛oxtimes d)=∑_x p(x)^((d+1)/2)`. -/
theorem finiteFormationAffinity_diagonalPower_eq_sum_rpow
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) {d : ℕ} (hd : 0 < d) :
    finiteFormationAffinity (finiteDiagonalPower p d) (finiteIndependentPower p d) =
      ∑ x, p x ^ (((d : ℝ) + 1) / 2) := by
  rw [finiteFormationAffinity_diagonalPower p hd]
  apply Finset.sum_congr rfl
  intro x hx
  exact sqrt_mul_sqrt_pow_eq_rpow (p x) (hp x) hd

theorem finiteDiagonalPower_reindex
    {X : Type*} [Fintype X] [DecidableEq X]
    (R : X ≃ X) (p : X → ℝ) (d : ℕ) :
    finitePowerReindex R (finiteDiagonalPower p d) =
      finiteDiagonalPower (finitePacketReindex R p) d := by
  funext z
  rw [finitePowerReindex, finiteDiagonalPower_apply, finiteDiagonalPower_apply]
  rw [← Equiv.sum_comp R.symm
    (fun y ↦ if (fun i ↦ R.symm (z i)) = (fun _ ↦ y) then p y else 0)]
  apply Finset.sum_congr rfl
  intro x hx
  have hcond :
      ((fun i ↦ R.symm (z i)) = (fun _ ↦ R.symm x)) ↔ z = (fun _ ↦ x) := by
    constructor
    · intro h
      funext i
      exact R.symm.injective (congrFun h i)
    · intro h
      subst z
      rfl
  simp only [hcond, finitePacketReindex]

/-- Finite Rényi entropy, in the normalization used by the paper card. -/
def finiteRenyiEntropy {X : Type*} [Fintype X]
    (p : X → ℝ) (alpha : ℝ) : ℝ :=
  Real.log (∑ x, p x ^ alpha) / (1 - alpha)

/-- Exact Rényi rewrite of the diagonal/product fracture. -/
theorem finiteFormationAffinity_diagonalPower_eq_exp_renyi
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hpsum : ∑ x, p x = 1)
    {d : ℕ} (hd : 2 ≤ d) :
    finiteFormationAffinity (finiteDiagonalPower p d) (finiteIndependentPower p d) =
      Real.exp (-(((d : ℝ) - 1) / 2) *
        finiteRenyiEntropy p (((d : ℝ) + 1) / 2)) := by
  let alpha : ℝ := ((d : ℝ) + 1) / 2
  let beta : ℝ := ((d : ℝ) - 1) / 2
  let S : ℝ := ∑ x, p x ^ alpha
  have hsumne : ∑ x, p x ≠ 0 := by rw [hpsum]; exact one_ne_zero
  obtain ⟨x, hxmem, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have hpx : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hx)
  have hS : 0 < S := by
    unfold S
    apply Finset.sum_pos'
    · intro y hy
      exact Real.rpow_nonneg (hp y) _
    · exact ⟨x, Finset.mem_univ x, Real.rpow_pos_of_pos hpx _⟩
  have hbeta : beta ≠ 0 := by
    have hdreal : (1 : ℝ) < (d : ℝ) := by
      exact_mod_cast (show 1 < d by omega)
    apply ne_of_gt
    dsimp only [beta]
    positivity
  have halpha : 1 - alpha = -beta := by
    dsimp only [alpha, beta]
    ring
  have hcoeff : -beta * (Real.log S / (1 - alpha)) = Real.log S := by
    rw [halpha]
    field_simp
  rw [finiteFormationAffinity_diagonalPower_eq_sum_rpow p hp (by omega)]
  change S = _
  rw [finiteRenyiEntropy]
  change S = Real.exp (-beta * (Real.log S / (1 - alpha)))
  rw [hcoeff, Real.exp_log hS]

def FiniteFormationDirac {X : Type*} (p : X → ℝ) : Prop :=
  ∃ x, p x = 1 ∧ ∀ y, y ≠ x → p y = 0

/-- Diagonal broadcast equals fresh independent formation exactly for a Dirac packet. -/
theorem finiteDiagonalPower_eq_independentPower_iff_dirac
    {X : Type*} [Fintype X] [DecidableEq X]
    (p : X → ℝ) (hpsum : ∑ x, p x = 1) {d : ℕ} (hd : 2 ≤ d) :
    finiteDiagonalPower p d = finiteIndependentPower p d ↔ FiniteFormationDirac p := by
  constructor
  · intro heq
    have hsupport : ∀ x y, p x ≠ 0 → p y ≠ 0 → x = y := by
      intro x y hpx hpy
      by_contra hxy
      let i0 : Fin d := ⟨0, by omega⟩
      let i1 : Fin d := ⟨1, by omega⟩
      let z : Fin d → X := fun i ↦ if i = i1 then y else x
      have hi : i0 ≠ i1 := by
        intro h
        have hv : (0 : ℕ) = 1 := by
          simpa [i0, i1] using congrArg Fin.val h
        omega
      have hz0 : z i0 = x := by simp [z, hi]
      have hz1 : z i1 = y := by simp [z]
      have hnconst : ∀ a, z ≠ fun _ ↦ a := by
        intro a ha
        have hxa : x = a := hz0.symm.trans (congrFun ha i0)
        have hya : y = a := hz1.symm.trans (congrFun ha i1)
        exact hxy (hxa.trans hya.symm)
      have hdiag : finiteDiagonalPower p d z = 0 :=
        finiteDiagonalPower_eq_zero_of_nonconstant p z hnconst
      have hprod : finiteIndependentPower p d z ≠ 0 := by
        unfold finiteIndependentPower
        apply Finset.prod_ne_zero_iff.mpr
        intro i hiuniv
        by_cases hi1 : i = i1
        · simpa [z, hi1] using hpy
        · simpa [z, hi1] using hpx
      have hz := congrFun heq z
      rw [hdiag] at hz
      exact hprod hz.symm
    have hsumne : ∑ x, p x ≠ 0 := by rw [hpsum]; exact one_ne_zero
    obtain ⟨x, hxmem, hpx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
    have hzero : ∀ y, y ≠ x → p y = 0 := by
      intro y hy
      by_contra hpy
      exact hy (hsupport y x hpy hpx)
    have hpxone : p x = 1 := by
      rw [← hpsum]
      symm
      apply Finset.sum_eq_single x
      · intro y hymem hyx
        exact hzero y hyx
      · exact fun h ↦ (h hxmem).elim
    exact ⟨x, hpxone, hzero⟩
  · rintro ⟨x, hpx, hzero⟩
    funext z
    by_cases hz : z = fun _ ↦ x
    · subst z
      rw [finiteDiagonalPower_const p (by omega) x, hpx]
      simp [finiteIndependentPower, hpx]
    · have hi : ∃ i, z i ≠ x := by
        by_contra h
        apply hz
        funext i
        by_contra hix
        exact h ⟨i, hix⟩
      obtain ⟨i, hi⟩ := hi
      have hpower : finiteIndependentPower p d z = 0 := by
        unfold finiteIndependentPower
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact hzero (z i) hi
      rw [hpower]
      rw [finiteDiagonalPower_apply]
      apply Finset.sum_eq_zero
      intro y hy
      by_cases hyx : y = x
      · subst y
        simp [hz]
      · simp [hzero y hyx]

end


end GaloisForLFunctions.HTGeometry
