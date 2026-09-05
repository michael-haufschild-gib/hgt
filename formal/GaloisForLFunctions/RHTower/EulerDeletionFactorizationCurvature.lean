import GaloisForLFunctions.RHTower.EulerDeletionFactorizationGraded

noncomputable section

open scoped BigOperators

namespace RHTower

/-- Finite same-clock weighted pairing of two coefficient streams. -/
def deletionWeightedPairingPrefix
    (α : ℝ) (N : ℕ) (x y : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, x n * y n * deletionDirichletWeight α n

theorem deletionWeightedPairingPrefix_add_left
    (α : ℝ) (N : ℕ) (x y z : ℕ → ℝ) :
    deletionWeightedPairingPrefix α N (x + y) z =
      deletionWeightedPairingPrefix α N x z +
        deletionWeightedPairingPrefix α N y z := by
  rw [deletionWeightedPairingPrefix, deletionWeightedPairingPrefix,
    deletionWeightedPairingPrefix, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Pi.add_apply]
  ring

theorem deletionWeightedPairingPrefix_add_right
    (α : ℝ) (N : ℕ) (x y z : ℕ → ℝ) :
    deletionWeightedPairingPrefix α N x (y + z) =
      deletionWeightedPairingPrefix α N x y +
        deletionWeightedPairingPrefix α N x z := by
  rw [deletionWeightedPairingPrefix, deletionWeightedPairingPrefix,
    deletionWeightedPairingPrefix, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Pi.add_apply]
  ring

/-- Every additive factorization-tree associator made only from the weighted pairing is flat. -/
theorem deletionWeightedPairingPrefix_additive_associator_zero
    (α : ℝ) (N : ℕ) (x y z : ℕ → ℝ) :
    deletionWeightedPairingPrefix α N x y +
          deletionWeightedPairingPrefix α N (x + y) z -
          deletionWeightedPairingPrefix α N y z -
          deletionWeightedPairingPrefix α N x (y + z) = 0 := by
  rw [deletionWeightedPairingPrefix_add_left,
    deletionWeightedPairingPrefix_add_right]
  ring

/-- Multiplicative factorization-tree curvature of the Mellin grade-mixing defect. -/
noncomputable def deletionFactorizationGradeCurvature
    (α : ℝ) (p q r : ℕ) : ℝ :=
  deletionFactorizationGradeCross α p q +
    deletionFactorizationGradeCross α (p * q) r -
    deletionFactorizationGradeCross α q r -
    deletionFactorizationGradeCross α p (q * r)

/-- Exact third-order defect left by the two multiplicative factorization trees. -/
theorem deletionFactorizationGradeCurvature_eq_of_pairwise_coprime
    {α : ℝ} (hα : 1 < α) {p q r : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) :
    deletionFactorizationGradeCurvature α p q r =
      deletionDirichletMass α * ((q : ℝ) * (q : ℝ) ^ (-α)) *
        (1 - (p : ℝ) * (p : ℝ) ^ (-α)) * ((q : ℝ) - 1) *
          (1 - (r : ℝ) ^ (2 - α)) := by
  have hpqr : Nat.Coprime (p * q) r := Nat.Coprime.mul_left hpr hqr
  have hp_qr : Nat.Coprime p (q * r) := Nat.Coprime.mul_right hpq hpr
  have hpqpow :
      (((p : ℝ) * (q : ℝ)) ^ (-α)) =
        (p : ℝ) ^ (-α) * (q : ℝ) ^ (-α) := by
    rw [Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q)]
  have hqrpow :
      (((q : ℝ) * (r : ℝ)) ^ (-α)) =
        (q : ℝ) ^ (-α) * (r : ℝ) ^ (-α) := by
    rw [Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg r)]
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrpow :
      (r : ℝ) * ((r : ℝ) * (r : ℝ) ^ (-α)) =
        (r : ℝ) ^ (2 - α) := by
    calc
      (r : ℝ) * ((r : ℝ) * (r : ℝ) ^ (-α)) =
          (r : ℝ) ^ 2 * (r : ℝ) ^ (-α) := by ring
      _ = (r : ℝ) ^ (2 : ℝ) * (r : ℝ) ^ (-α) := by rw [Real.rpow_two]
      _ = (r : ℝ) ^ ((2 : ℝ) + (-α)) :=
        (Real.rpow_add hrR (2 : ℝ) (-α)).symm
      _ = (r : ℝ) ^ (2 - α) := by ring_nf
  rw [deletionFactorizationGradeCurvature,
    deletionFactorizationGradeCross_eq_of_coprime hα hp hq hpq,
    deletionFactorizationGradeCross_eq_of_coprime hα (Nat.mul_pos hp hq) hr hpqr,
    deletionFactorizationGradeCross_eq_of_coprime hα hq hr hqr,
    deletionFactorizationGradeCross_eq_of_coprime hα hp (Nat.mul_pos hq hr) hp_qr]
  push_cast
  rw [hpqpow, hqrpow, ← hrpow]
  ring

/-- Inside the doubled critical strip, the multiplicative curvature is strictly negative. -/
theorem deletionFactorizationGradeCurvature_neg_of_pairwise_coprime
    {α : ℝ} (hα : 1 < α) (hα2 : α < 2) {p q r : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) :
    deletionFactorizationGradeCurvature α p q r < 0 := by
  rw [deletionFactorizationGradeCurvature_eq_of_pairwise_coprime hα
    (by omega : 0 < p) (by omega : 0 < q) (by omega : 0 < r) hpq hpr hqr]
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrpow : 1 < (r : ℝ) ^ (2 - α) :=
    (Real.one_lt_rpow_iff_of_pos hrR).2 (Or.inl ⟨hr1, by linarith⟩)
  have hqpow : 0 < (q : ℝ) * (q : ℝ) ^ (-α) :=
    mul_pos hqR (Real.rpow_pos_of_pos hqR _)
  have hpmean : 0 < 1 - (p : ℝ) * (p : ℝ) ^ (-α) :=
    deletionDirichletMean_pos hα hp
  have hqsub : 0 < (q : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hq)
  have hpositive :
      0 < deletionDirichletMass α * ((q : ℝ) * (q : ℝ) ^ (-α)) *
        (1 - (p : ℝ) * (p : ℝ) ^ (-α)) * ((q : ℝ) - 1) := by
    exact mul_pos (mul_pos (mul_pos (deletionDirichletMass_pos hα) hqpow) hpmean) hqsub
  exact mul_neg_of_pos_of_neg hpositive (sub_neg.mpr hrpow)

/-- At exponent two the factorization curvature vanishes. -/
theorem deletionFactorizationGradeCurvature_eq_zero_two
    {p q r : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) :
    deletionFactorizationGradeCurvature 2 p q r = 0 := by
  rw [deletionFactorizationGradeCurvature_eq_of_pairwise_coprime (by norm_num)
    hp hq hr hpq hpr hqr]
  norm_num

/-- Above exponent two the multiplicative curvature is strictly positive. -/
theorem deletionFactorizationGradeCurvature_pos_of_two_lt
    {α : ℝ} (hα2 : 2 < α) {p q r : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) :
    0 < deletionFactorizationGradeCurvature α p q r := by
  have hα : 1 < α := lt_trans one_lt_two hα2
  rw [deletionFactorizationGradeCurvature_eq_of_pairwise_coprime hα
    (by omega : 0 < p) (by omega : 0 < q) (by omega : 0 < r) hpq hpr hqr]
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hrpow : (r : ℝ) ^ (2 - α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hr1 (by linarith)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqpow : 0 < (q : ℝ) * (q : ℝ) ^ (-α) :=
    mul_pos hqR (Real.rpow_pos_of_pos hqR _)
  have hpmean : 0 < 1 - (p : ℝ) * (p : ℝ) ^ (-α) :=
    deletionDirichletMean_pos hα hp
  have hqsub : 0 < (q : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hq)
  exact mul_pos
    (mul_pos (mul_pos (mul_pos (deletionDirichletMass_pos hα) hqpow) hpmean) hqsub)
    (sub_pos.mpr hrpow)

/-- In its convergence chamber the curvature vanishes exactly at the upper exponent wall. -/
theorem deletionFactorizationGradeCurvature_eq_zero_iff
    {α : ℝ} (hα : 1 < α) {p q r : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) :
    deletionFactorizationGradeCurvature α p q r = 0 ↔ α = 2 := by
  constructor
  · intro hzero
    rcases lt_trichotomy α 2 with hlt | heq | hgt
    · exact False.elim
        ((ne_of_lt (deletionFactorizationGradeCurvature_neg_of_pairwise_coprime
          hα hlt hp hq hr hpq hpr hqr)) hzero)
    · exact heq
    · exact False.elim
        ((ne_of_gt (deletionFactorizationGradeCurvature_pos_of_two_lt
          hgt hp hq hr hpq hpr hqr)) hzero)
  · intro hαeq
    subst α
    exact deletionFactorizationGradeCurvature_eq_zero_two
      (by omega) (by omega) (by omega) hpq hpr hqr

/-- A hypothetical right-half critical-strip abscissa lies in the negative-curvature chamber. -/
theorem deletionFactorizationGradeCurvature_neg_of_half_lt_sigma_lt_one
    {σ : ℝ} (hhalf : 1 / 2 < σ) (hone : σ < 1) {p q r : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) :
    deletionFactorizationGradeCurvature (2 * σ) p q r < 0 := by
  exact deletionFactorizationGradeCurvature_neg_of_pairwise_coprime
    (by linarith) (by linarith) hp hq hr hpq hpr hqr

end RHTower
