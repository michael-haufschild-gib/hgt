import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BernoulliBooleanGibbs
import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue

/-!
# Finite biased Walsh interaction mechanics

The finite product Bernoulli source carries a normalized biased Walsh basis indexed by interaction
supports. This module proves orthonormality, exact reconstruction, Parseval conservation, passive
degree observation, exact composition of observation defects, the multiplicative-parity
coefficients, and their covariance-form pure-state quantum Fisher value.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open HTGeometry.ConstraintFrameRelativity

noncomputable section

/-- Local Bernoulli variance. -/
def biasedBernoulliVariance {I : Type*} (q : I → ℝ) (i : I) : ℝ :=
  q i * (1 - q i)

/-- Normalized centered Bernoulli coordinate on the subset model of the Boolean cube. -/
def biasedWalshCoordinate {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (i : I) (X : Finset I) : ℝ :=
  if i ∈ X then (1 - q i) / Real.sqrt (biasedBernoulliVariance q i)
  else -q i / Real.sqrt (biasedBernoulliVariance q i)

/-- Product character attached to interaction support `S`. -/
def biasedWalshCharacter {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (S X : Finset I) : ℝ :=
  (∏ i ∈ X,
      if i ∈ S then (1 - q i) / Real.sqrt (biasedBernoulliVariance q i) else 1) *
    ∏ i ∈ Xᶜ,
      if i ∈ S then -q i / Real.sqrt (biasedBernoulliVariance q i) else 1

/-- Biased Walsh coefficient against the product Bernoulli source. -/
def biasedWalshCoefficient {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (f : Finset I → ℝ) (S : Finset I) : ℝ :=
  bernoulliExp q (fun X => f X * biasedWalshCharacter q S X)

/-- Empty-support coefficient is source expectation. -/
theorem biasedWalshCoefficient_empty
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (f : Finset I → ℝ) :
    biasedWalshCoefficient q f ∅ = bernoulliExp q f := by
  simp [biasedWalshCoefficient, biasedWalshCharacter]

private theorem biasedBernoulliVariance_pos
    {I : Type*} {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (i : I) :
    0 < biasedBernoulliVariance q i := by
  unfold biasedBernoulliVariance
  exact mul_pos (hq0 i) (sub_pos.mpr (hq1 i))

private theorem biasedWalsh_sqrt_sq
    {I : Type*} {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (i : I) :
    Real.sqrt (biasedBernoulliVariance q i) ^ 2 = biasedBernoulliVariance q i := by
  exact Real.sq_sqrt (biasedBernoulliVariance_pos hq0 hq1 i).le

private theorem biasedWalsh_local_inner
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (S T : Finset I) (i : I) :
    q i *
          (if i ∈ S then (1 - q i) / Real.sqrt (biasedBernoulliVariance q i) else 1) *
          (if i ∈ T then (1 - q i) / Real.sqrt (biasedBernoulliVariance q i) else 1) +
        (1 - q i) *
          (if i ∈ S then -q i / Real.sqrt (biasedBernoulliVariance q i) else 1) *
          (if i ∈ T then -q i / Real.sqrt (biasedBernoulliVariance q i) else 1) =
      if (i ∈ S ↔ i ∈ T) then 1 else 0 := by
  have hsqrt : Real.sqrt (biasedBernoulliVariance q i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (biasedBernoulliVariance_pos hq0 hq1 i))
  have hsq := biasedWalsh_sqrt_sq hq0 hq1 i
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · simp [hiS, hiT]
    field_simp [hsqrt]
    rw [hsq, biasedBernoulliVariance]
    ring
  · simp [hiS, hiT]
    field_simp [hsqrt]
    ring
  · simp [hiS, hiT]
    field_simp [hsqrt]
    ring
  · simp [hiS, hiT]

/-- The normalized product characters are orthonormal under the Bernoulli source law. -/
theorem biasedWalsh_orthonormal
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (S T : Finset I) :
    bernoulliExp q
        (fun X => biasedWalshCharacter q S X * biasedWalshCharacter q T X) =
      if S = T then 1 else 0 := by
  let sf : I → ℝ := fun i =>
    (if i ∈ S then (1 - q i) / Real.sqrt (biasedBernoulliVariance q i) else 1) *
      (if i ∈ T then (1 - q i) / Real.sqrt (biasedBernoulliVariance q i) else 1)
  let sg : I → ℝ := fun i =>
    (if i ∈ S then -q i / Real.sqrt (biasedBernoulliVariance q i) else 1) *
      (if i ∈ T then -q i / Real.sqrt (biasedBernoulliVariance q i) else 1)
  have hobs : ∀ X : Finset I,
      biasedWalshCharacter q S X * biasedWalshCharacter q T X =
        (∏ i ∈ X, sf i) * ∏ i ∈ Xᶜ, sg i := by
    intro X
    unfold biasedWalshCharacter sf sg
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  rw [congrArg (bernoulliExp q) (funext hobs), bernoulliExp_prod]
  by_cases hST : S = T
  · subst T
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i hi
    have hlocal := biasedWalsh_local_inner hq0 hq1 S S i
    simp only [iff_self, if_true] at hlocal
    unfold sf sg
    convert hlocal using 1
    all_goals ring
  · rw [if_neg hST]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra h
      push Not at h
      exact hST (Finset.ext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hlocal := biasedWalsh_local_inner hq0 hq1 S T i
    rw [if_neg hi] at hlocal
    unfold sf sg
    convert hlocal using 1
    all_goals ring

/-- Split-product and support-product formulas for a biased Walsh character agree. -/
theorem biasedWalshCharacter_eq_prod_coordinate
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (S X : Finset I) :
    biasedWalshCharacter q S X = ∏ i ∈ S, biasedWalshCoordinate q i X := by
  classical
  unfold biasedWalshCharacter biasedWalshCoordinate
  rw [Finset.prod_ite_mem, Finset.prod_ite_mem]
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun i => i ∈ X)]
  congr 1
  · apply Finset.prod_congr
    · ext i
      simp [and_comm]
    · intro i hi
      simp [(Finset.mem_filter.mp hi).2]
  · apply Finset.prod_congr
    · ext i
      simp [and_comm]
    · intro i hi
      simp [(Finset.mem_filter.mp hi).2]

private theorem biasedWalsh_local_weighted_dual
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (X Y : Finset I) (i : I) :
    (if i ∈ Y then q i else 1 - q i) *
        (1 + biasedWalshCoordinate q i X * biasedWalshCoordinate q i Y) =
      if (i ∈ X ↔ i ∈ Y) then 1 else 0 := by
  have hsqrt : Real.sqrt (biasedBernoulliVariance q i) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (biasedBernoulliVariance_pos hq0 hq1 i))
  have hsq := biasedWalsh_sqrt_sq hq0 hq1 i
  by_cases hiX : i ∈ X <;> by_cases hiY : i ∈ Y
  · simp [biasedWalshCoordinate, hiX, hiY]
    field_simp [hsqrt]
    rw [hsq, biasedBernoulliVariance]
    ring
  · simp [biasedWalshCoordinate, hiX, hiY]
    field_simp [hsqrt]
    rw [hsq, biasedBernoulliVariance]
    ring_nf
    simp
  · simp [biasedWalshCoordinate, hiX, hiY]
    field_simp [hsqrt]
    rw [hsq, biasedBernoulliVariance]
    ring_nf
    simp
  · simp [biasedWalshCoordinate, hiX, hiY]
    field_simp [hsqrt]
    rw [hsq, biasedBernoulliVariance]
    ring

/-- Weighted completeness kernel of the finite biased Walsh family. -/
theorem biasedWalsh_weighted_dual_kernel
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (X Y : Finset I) :
    bernoulliWeight q Y *
        (∑ S : Finset I,
          biasedWalshCharacter q S Y * biasedWalshCharacter q S X) =
      if X = Y then 1 else 0 := by
  have hkernel :
      (∑ S : Finset I,
          biasedWalshCharacter q S Y * biasedWalshCharacter q S X) =
        ∏ i, (biasedWalshCoordinate q i Y * biasedWalshCoordinate q i X + 1) := by
    simpa only [biasedWalshCharacter_eq_prod_coordinate,
      ← Finset.prod_mul_distrib, Finset.prod_const_one, mul_one] using
      (Fintype.prod_add
        (fun i => biasedWalshCoordinate q i Y * biasedWalshCoordinate q i X)
        (fun _i => (1 : ℝ))).symm
  rw [hkernel]
  have hweight : bernoulliWeight q Y =
      ∏ i, if i ∈ Y then q i else 1 - q i := by
    unfold bernoulliWeight
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ Y)]
    congr 1
    · apply Finset.prod_congr
      · ext i
        simp
      · intro i hi
        simp [(Finset.mem_filter.mp hi).2]
    · apply Finset.prod_congr
      · ext i
        simp
      · intro i hi
        simp [(Finset.mem_filter.mp hi).2]
  rw [hweight, ← Finset.prod_mul_distrib]
  by_cases hXY : X = Y
  · subst Y
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i hi
    have hlocal := biasedWalsh_local_weighted_dual hq0 hq1 X X i
    simp only [iff_self, if_true] at hlocal
    convert hlocal using 1
    all_goals ring
  · rw [if_neg hXY]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ X ↔ i ∈ Y) := by
      by_contra h
      push Not at h
      exact hXY (Finset.ext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hlocal := biasedWalsh_local_weighted_dual hq0 hq1 X Y i
    rw [if_neg hi] at hlocal
    convert hlocal using 1
    all_goals ring

/-- Exact reconstruction in the finite biased Walsh basis. -/
theorem biasedWalsh_reconstruction
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (f : Finset I → ℝ) (X : Finset I) :
    (∑ S : Finset I,
      biasedWalshCoefficient q f S * biasedWalshCharacter q S X) = f X := by
  unfold biasedWalshCoefficient bernoulliExp
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    ∑ Y : Finset I, ∑ S : Finset I,
        bernoulliWeight q Y * (f Y * biasedWalshCharacter q S Y) *
          biasedWalshCharacter q S X =
        ∑ Y : Finset I, bernoulliWeight q Y * f Y *
          (∑ S : Finset I,
            biasedWalshCharacter q S Y * biasedWalshCharacter q S X) := by
      apply Finset.sum_congr rfl
      intro Y hY
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      ring
    _ = f X := by
      calc
        ∑ Y : Finset I, bernoulliWeight q Y * f Y *
            (∑ S : Finset I,
              biasedWalshCharacter q S Y * biasedWalshCharacter q S X) =
            bernoulliWeight q X * f X *
              (∑ S : Finset I,
                biasedWalshCharacter q S X * biasedWalshCharacter q S X) := by
          apply Fintype.sum_eq_single X
          intro Y hYX
          have hkernel := biasedWalsh_weighted_dual_kernel hq0 hq1 X Y
          rw [if_neg (Ne.symm hYX)] at hkernel
          calc
            bernoulliWeight q Y * f Y *
                (∑ S : Finset I,
                  biasedWalshCharacter q S Y * biasedWalshCharacter q S X) =
                f Y * (bernoulliWeight q Y *
                  (∑ S : Finset I,
                    biasedWalshCharacter q S Y * biasedWalshCharacter q S X)) := by ring
            _ = 0 := by rw [hkernel, mul_zero]
        _ = f X := by
          have hkernel := biasedWalsh_weighted_dual_kernel hq0 hq1 X X
          rw [if_pos rfl] at hkernel
          calc
            bernoulliWeight q X * f X *
                (∑ S : Finset I,
                  biasedWalshCharacter q S X * biasedWalshCharacter q S X) =
                f X * (bernoulliWeight q X *
                  (∑ S : Finset I,
                    biasedWalshCharacter q S X * biasedWalshCharacter q S X)) := by ring
            _ = f X := by rw [hkernel, mul_one]

/-- Squared `L²` norm under the finite product Bernoulli law. -/
def biasedWalshNormSq {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (f : Finset I → ℝ) : ℝ :=
  bernoulliExp q (fun X => f X ^ 2)

/-- Parseval conservation for the complete biased Walsh packet. -/
theorem biasedWalsh_parseval
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (f : Finset I → ℝ) :
    biasedWalshNormSq q f =
      ∑ S : Finset I, (biasedWalshCoefficient q f S) ^ 2 := by
  unfold biasedWalshNormSq biasedWalshCoefficient bernoulliExp
  calc
    ∑ X : Finset I, bernoulliWeight q X * f X ^ 2 =
        ∑ X : Finset I, bernoulliWeight q X * f X *
          (∑ S : Finset I,
            biasedWalshCoefficient q f S * biasedWalshCharacter q S X) := by
      apply Finset.sum_congr rfl
      intro X hX
      rw [biasedWalsh_reconstruction hq0 hq1 f X]
      ring
    _ = ∑ S : Finset I, (biasedWalshCoefficient q f S) ^ 2 := by
      rw [show ∑ X : Finset I, bernoulliWeight q X * f X *
          (∑ S : Finset I,
            biasedWalshCoefficient q f S * biasedWalshCharacter q S X) =
          ∑ X : Finset I, ∑ S : Finset I,
            bernoulliWeight q X * f X *
              (biasedWalshCoefficient q f S * biasedWalshCharacter q S X) by
        apply Finset.sum_congr rfl
        intro X hX
        rw [Finset.mul_sum]]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S hS
      calc
        ∑ X : Finset I, bernoulliWeight q X * f X *
            (biasedWalshCoefficient q f S * biasedWalshCharacter q S X) =
            biasedWalshCoefficient q f S *
              (∑ X : Finset I,
                bernoulliWeight q X * (f X * biasedWalshCharacter q S X)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro X hX
          ring
        _ = (biasedWalshCoefficient q f S) ^ 2 := by
          unfold biasedWalshCoefficient bernoulliExp
          ring

/-- Orthogonal observation through interaction degree at most `D`. -/
def biasedWalshProjection {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (f : Finset I → ℝ) (D : ℕ) (X : Finset I) : ℝ :=
  ∑ S : Finset I,
    if S.card ≤ D then
      biasedWalshCoefficient q f S * biasedWalshCharacter q S X else 0

/-- Projection preserves exactly the coefficients of degree at most `D`. -/
theorem biasedWalshCoefficient_projection
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (f : Finset I → ℝ) (D : ℕ) (T : Finset I) :
    biasedWalshCoefficient q (biasedWalshProjection q f D) T =
      if T.card ≤ D then biasedWalshCoefficient q f T else 0 := by
  unfold biasedWalshCoefficient biasedWalshProjection
  have hobs : (fun X : Finset I =>
      (∑ S : Finset I,
        if S.card ≤ D then
          biasedWalshCoefficient q f S * biasedWalshCharacter q S X else 0) *
          biasedWalshCharacter q T X) =
      fun X => ∑ S : Finset I,
        if S.card ≤ D then
          biasedWalshCoefficient q f S *
            (biasedWalshCharacter q S X * biasedWalshCharacter q T X) else 0 := by
    funext X
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hSD : S.card ≤ D <;> simp [hSD]
    ring
  rw [hobs]
  rw [show bernoulliExp q (fun X => ∑ S : Finset I,
      if S.card ≤ D then
        biasedWalshCoefficient q f S *
          (biasedWalshCharacter q S X * biasedWalshCharacter q T X) else 0) =
      ∑ S : Finset I, bernoulliExp q (fun X =>
        if S.card ≤ D then
          biasedWalshCoefficient q f S *
            (biasedWalshCharacter q S X * biasedWalshCharacter q T X) else 0) by
    simpa only using bernoulliExp_sum q Finset.univ (fun S X =>
      if S.card ≤ D then
        biasedWalshCoefficient q f S *
          (biasedWalshCharacter q S X * biasedWalshCharacter q T X) else 0)]
  simp_rw [show ∀ S : Finset I,
      bernoulliExp q (fun X =>
        if S.card ≤ D then
          biasedWalshCoefficient q f S *
            (biasedWalshCharacter q S X * biasedWalshCharacter q T X) else 0) =
        if S.card ≤ D then
          biasedWalshCoefficient q f S *
            bernoulliExp q
              (fun X => biasedWalshCharacter q S X * biasedWalshCharacter q T X) else 0 by
    intro S
    by_cases hSD : S.card ≤ D
    · simp only [hSD, if_true]
      exact bernoulliExp_smul q (biasedWalshCoefficient q f S)
        (fun X => biasedWalshCharacter q S X * biasedWalshCharacter q T X)
    · simp [hSD, bernoulliExp]]
  simp_rw [biasedWalsh_orthonormal hq0 hq1]
  by_cases hTD : T.card ≤ D
  · rw [if_pos hTD]
    calc
      (∑ S : Finset I,
          if S.card ≤ D then
            biasedWalshCoefficient q f S * (if S = T then 1 else 0) else 0) =
          biasedWalshCoefficient q f T := by
        calc
          (∑ S : Finset I,
              if S.card ≤ D then
                biasedWalshCoefficient q f S * (if S = T then 1 else 0) else 0) =
              if T.card ≤ D then
                biasedWalshCoefficient q f T * (if T = T then 1 else 0) else 0 := by
            apply Fintype.sum_eq_single T
            intro S hST
            simp [hST]
          _ = biasedWalshCoefficient q f T := by simp [hTD]
      _ = bernoulliExp q (fun X => f X * biasedWalshCharacter q T X) := rfl
  · rw [if_neg hTD]
    apply Finset.sum_eq_zero
    intro S hS
    by_cases hST : S = T
    · subst S
      simp [hTD]
    · simp [hST]

/-- Exact visible coefficient energy after degree observation. -/
theorem biasedWalshNormSq_projection
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (f : Finset I → ℝ) (D : ℕ) :
    biasedWalshNormSq q (biasedWalshProjection q f D) =
      ∑ S : Finset I,
        if S.card ≤ D then (biasedWalshCoefficient q f S) ^ 2 else 0 := by
  rw [biasedWalsh_parseval hq0 hq1]
  apply Finset.sum_congr rfl
  intro S hS
  rw [biasedWalshCoefficient_projection hq0 hq1]
  by_cases hSD : S.card ≤ D <;> simp [hSD]

/-- Work hidden above observation degree `D`. -/
def biasedWalshHiddenWork {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (f : Finset I → ℝ) (D : ℕ) : ℝ :=
  ∑ S : Finset I,
    if D < S.card then (biasedWalshCoefficient q f S) ^ 2 else 0

/-- Parseval splits total energy into observed energy and exact hidden work. -/
theorem biasedWalshNormSq_sub_projection_eq_hiddenWork
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (f : Finset I → ℝ) (D : ℕ) :
    biasedWalshNormSq q f - biasedWalshNormSq q (biasedWalshProjection q f D) =
      biasedWalshHiddenWork q f D := by
  rw [biasedWalsh_parseval hq0 hq1, biasedWalshNormSq_projection hq0 hq1]
  unfold biasedWalshHiddenWork
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hSD : S.card ≤ D
  · simp [hSD, Nat.not_lt_of_ge hSD]
  · have hDS : D < S.card := Nat.lt_of_not_ge hSD
    simp [hSD, hDS]

theorem biasedWalshCoefficient_sub
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (f g : Finset I → ℝ) (S : Finset I) :
    biasedWalshCoefficient q (fun X => f X - g X) S =
      biasedWalshCoefficient q f S - biasedWalshCoefficient q g S := by
  unfold biasedWalshCoefficient bernoulliExp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro X hX
  ring

/-- Energy in the degree band opened between two nested observers. -/
theorem biasedWalshNormSq_projection_sub_projection
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (f : Finset I → ℝ) {D E : ℕ} (hDE : D ≤ E) :
    biasedWalshNormSq q
        (fun X => biasedWalshProjection q f E X - biasedWalshProjection q f D X) =
      ∑ S : Finset I,
        if D < S.card ∧ S.card ≤ E then
          (biasedWalshCoefficient q f S) ^ 2 else 0 := by
  rw [biasedWalsh_parseval hq0 hq1]
  apply Finset.sum_congr rfl
  intro S hS
  rw [biasedWalshCoefficient_sub,
    biasedWalshCoefficient_projection hq0 hq1,
    biasedWalshCoefficient_projection hq0 hq1]
  by_cases hSD : S.card ≤ D
  · have hSE : S.card ≤ E := hSD.trans hDE
    simp [hSD, hSE, Nat.not_lt_of_ge hSD]
  · have hDS : D < S.card := Nat.lt_of_not_ge hSD
    by_cases hSE : S.card ≤ E
    · simp [hSD, hDS, hSE]
    · simp [hSD, hDS, hSE]

/-- Exact composition of passive work defects along the interaction filtration. -/
theorem biasedWalshHiddenWork_eq_add_projectionBand
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (f : Finset I → ℝ) {D E : ℕ} (hDE : D < E) :
    biasedWalshHiddenWork q f D = biasedWalshHiddenWork q f E +
      biasedWalshNormSq q
        (fun X => biasedWalshProjection q f E X - biasedWalshProjection q f D X) := by
  rw [biasedWalshNormSq_projection_sub_projection hq0 hq1 f hDE.le]
  unfold biasedWalshHiddenWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hES : E < S.card
  · have hDS : D < S.card := hDE.trans hES
    have hnotSE : ¬ S.card ≤ E := Nat.not_le_of_gt hES
    simp [hES, hDS, hnotSE]
  · have hSE : S.card ≤ E := Nat.le_of_not_gt hES
    by_cases hDS : D < S.card
    · simp [hES, hDS, hSE]
    · simp [hES, hDS]

/-- Orthogonal interaction observation is passive. -/
theorem biasedWalshProjection_normSq_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (f : Finset I → ℝ) (D : ℕ) :
    biasedWalshNormSq q (biasedWalshProjection q f D) ≤ biasedWalshNormSq q f := by
  have hdefect := biasedWalshNormSq_sub_projection_eq_hiddenWork hq0 hq1 f D
  have hhidden : 0 ≤ biasedWalshHiddenWork q f D := by
    unfold biasedWalshHiddenWork
    exact Finset.sum_nonneg fun S hS => by
      by_cases hDS : D < S.card <;>
        simp [hDS, sq_nonneg (biasedWalshCoefficient q f S)]
  linarith

/-- Multiplicative parity on the finite Boolean cube. -/
def biasedWalshParity {I : Type*} [Fintype I] [DecidableEq I]
    (X : Finset I) : ℝ :=
  (∏ _i ∈ X, (-1 : ℝ)) * ∏ _i ∈ Xᶜ, (1 : ℝ)

/-- Multiplicative parity has unit source norm. -/
theorem biasedWalshNormSq_parity
    {I : Type*} [Fintype I] [DecidableEq I] (q : I → ℝ) :
    biasedWalshNormSq q (biasedWalshParity : Finset I → ℝ) = 1 := by
  unfold biasedWalshNormSq
  rw [show (fun X : Finset I => biasedWalshParity X ^ 2) = fun _X => (1 : ℝ) by
    funext X
    unfold biasedWalshParity
    rw [Finset.prod_const_one, mul_one]
    simp only [Finset.prod_const]
    change ((-1 : ℝ) ^ X.card) ^ 2 = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num]
  exact bernoulliExp_one q

/-- Exact biased-Walsh coefficient of multiplicative parity. -/
theorem biasedWalshCoefficient_parity
    {I : Type*} [Fintype I] [DecidableEq I]
    {q : I → ℝ} (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1)
    (S : Finset I) :
    biasedWalshCoefficient q biasedWalshParity S =
      (∏ i ∈ S, -2 * Real.sqrt (biasedBernoulliVariance q i)) *
        ∏ i ∈ Sᶜ, (1 - 2 * q i) := by
  let sf : I → ℝ := fun i =>
    -(if i ∈ S then
      (1 - q i) / Real.sqrt (biasedBernoulliVariance q i) else 1)
  let sg : I → ℝ := fun i =>
    if i ∈ S then -q i / Real.sqrt (biasedBernoulliVariance q i) else 1
  have hobs : ∀ X : Finset I,
      biasedWalshParity X * biasedWalshCharacter q S X =
        (∏ i ∈ X, sf i) * ∏ i ∈ Xᶜ, sg i := by
    intro X
    unfold biasedWalshParity biasedWalshCharacter sf sg
    rw [Finset.prod_const_one, mul_one, ← mul_assoc]
    congr 1
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  unfold biasedWalshCoefficient
  rw [congrArg (bernoulliExp q) (funext hobs), bernoulliExp_prod]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ S)]
  congr 1
  · apply Finset.prod_congr
    · ext i
      simp
    · intro i hi
      have hiS : i ∈ S := hi
      have hsqrt : Real.sqrt (biasedBernoulliVariance q i) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (biasedBernoulliVariance_pos hq0 hq1 i))
      have hsq := biasedWalsh_sqrt_sq hq0 hq1 i
      simp only [sf, sg, hiS, if_true]
      field_simp [hsqrt]
      rw [hsq, biasedBernoulliVariance]
      ring
  · apply Finset.prod_congr
    · ext i
      simp
    · intro i hi
      have hiS : i ∉ S := Finset.mem_compl.mp hi
      simp [sf, sg, hiS]
      ring

/-- Pure-state QFI of a real diagonal generator under the Bernoulli source state. -/
def biasedWalshPureStateQFI {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (g : Finset I → ℝ) : ℝ :=
  HTGeometry.pureStateQuantumFisherValue 1
    (bernoulliExp q g) (bernoulliExp q fun X => g X ^ 2)

/-- Pure-state QFI is four times Bernoulli variance. -/
theorem biasedWalshPureStateQFI_eq_four_mul_variance
    {I : Type*} [Fintype I] [DecidableEq I]
    (q : I → ℝ) (g : Finset I → ℝ) :
    biasedWalshPureStateQFI q g =
      4 * (biasedWalshNormSq q g - (bernoulliExp q g) ^ 2) := by
  unfold biasedWalshPureStateQFI HTGeometry.pureStateQuantumFisherValue
    HTGeometry.projectiveQuantumTangentValue biasedWalshNormSq
  ring

end

end GaloisForLFunctions.HTGeometry
