import GaloisForLFunctions.RHTower.EulerDeletionFactorizationCurvature

noncomputable section

open scoped BigOperators

namespace RHTower

/-- Pointwise coefficient whose Dirichlet-weighted sum is the factorization curvature. -/
def deletionFactorizationCurvatureCoefficient
    (p q r n : ℕ) : ℤ :=
  blockDeletionCoefficient p n * blockDeletionCoefficient q n ^ 2 +
    blockDeletionCoefficient (p * q) n * blockDeletionCoefficient r n ^ 2 -
    blockDeletionCoefficient q n * blockDeletionCoefficient r n ^ 2 -
    blockDeletionCoefficient p n * blockDeletionCoefficient (q * r) n ^ 2

/-- The curvature coefficient is a linear combination of original deletion channels. -/
theorem deletionFactorizationCurvatureCoefficient_normal_form
    {p q r : ℕ} (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) (n : ℕ) :
    deletionFactorizationCurvatureCoefficient p q r n =
      ((q : ℤ) - 1) *
        (blockDeletionCoefficient (p * q) n - blockDeletionCoefficient q n +
          (r : ℤ) * (blockDeletionCoefficient (q * r) n -
            blockDeletionCoefficient (p * q * r) n)) := by
  have hpqr : Nat.Coprime (p * q) r := Nat.Coprime.mul_left hpr hqr
  have hp_qr : Nat.Coprime p (q * r) := Nat.Coprime.mul_right hpq hpr
  have hpq_id := blockDeletionCoefficient_mul_eq_add_sub_product_of_coprime hpq n
  have hpqr_id := blockDeletionCoefficient_mul_eq_add_sub_product_of_coprime hpqr n
  have hqr_id := blockDeletionCoefficient_mul_eq_add_sub_product_of_coprime hqr n
  have hp_qr_id :
      blockDeletionCoefficient p n * blockDeletionCoefficient (q * r) n =
        blockDeletionCoefficient p n + blockDeletionCoefficient (q * r) n -
          blockDeletionCoefficient (p * q * r) n := by
    simpa only [mul_assoc] using
      blockDeletionCoefficient_mul_eq_add_sub_product_of_coprime hp_qr n
  rw [deletionFactorizationCurvatureCoefficient,
    blockDeletionCoefficient_sq_eq q n,
    blockDeletionCoefficient_sq_eq r n,
    blockDeletionCoefficient_sq_eq (q * r) n]
  push_cast
  linear_combination
    (2 - (q : ℤ)) * hpq_id +
    (2 - (r : ℤ)) * hpqr_id -
    (2 - (r : ℤ)) * hqr_id -
    (2 - (q : ℤ) * (r : ℤ)) * hp_qr_id

/-- Every deletion channel has zero uniform endpoint on each period it divides. -/
theorem sum_blockDeletionCoefficient_eq_zero_of_dvd
    {d L : ℕ} (hdL : d ∣ L) :
    ∑ n ∈ Finset.range L, blockDeletionCoefficient d (n + 1) = 0 := by
  obtain ⟨k, rfl⟩ := hdL
  exact sum_blockDeletionCoefficient_product_block_eq_zero

/-- The curvature coefficient has zero uniform endpoint on its common product period. -/
theorem sum_deletionFactorizationCurvatureCoefficient_product_period_eq_zero
    {p q r : ℕ} (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) :
    ∑ n ∈ Finset.range (p * q * r),
      deletionFactorizationCurvatureCoefficient p q r (n + 1) = 0 := by
  have hpqsum :
      ∑ n ∈ Finset.range (p * q * r),
        blockDeletionCoefficient (p * q) (n + 1) = 0 :=
    sum_blockDeletionCoefficient_eq_zero_of_dvd ⟨r, rfl⟩
  have hqsum :
      ∑ n ∈ Finset.range (p * q * r),
        blockDeletionCoefficient q (n + 1) = 0 := by
    apply sum_blockDeletionCoefficient_eq_zero_of_dvd
    refine ⟨p * r, ?_⟩
    ac_rfl
  have hqrsum :
      ∑ n ∈ Finset.range (p * q * r),
        blockDeletionCoefficient (q * r) (n + 1) = 0 := by
    apply sum_blockDeletionCoefficient_eq_zero_of_dvd
    refine ⟨p, ?_⟩
    ac_rfl
  have hpqrsum :
      ∑ n ∈ Finset.range (p * q * r),
        blockDeletionCoefficient (p * q * r) (n + 1) = 0 :=
    sum_blockDeletionCoefficient_eq_zero_of_dvd (dvd_refl _)
  simp_rw [deletionFactorizationCurvatureCoefficient_normal_form hpq hpr hqr]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib, hpqsum, hqsum, hqrsum, hpqrsum]
  ring

/-- Linear observation of two copies with opposite amplitude perturbations. -/
def deletionBalancedLinearObservation
    (L : ℕ) (f h : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range L,
    (f n * (1 + h n) + f n * (1 - h n))

/-- Quadratic observation of the same two perturbed copies. -/
def deletionBalancedQuadraticObservation
    (L : ℕ) (f h : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range L,
    (f n * (1 + h n) ^ 2 + f n * (1 - h n) ^ 2)

theorem deletionBalancedLinearObservation_eq
    (L : ℕ) (f h : ℕ → ℝ) :
    deletionBalancedLinearObservation L f h =
      2 * ∑ n ∈ Finset.range L, f n := by
  rw [deletionBalancedLinearObservation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem deletionBalancedQuadraticObservation_eq
    (L : ℕ) (f h : ℕ → ℝ) :
    deletionBalancedQuadraticObservation L f h =
      2 * (∑ n ∈ Finset.range L, f n) +
        2 * ∑ n ∈ Finset.range L, f n * h n ^ 2 := by
  rw [deletionBalancedQuadraticObservation, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- A half-amplitude perturbation concentrated at one residue. -/
def deletionBalancedSinglePerturbation (k n : ℕ) : ℝ :=
  if n = k then 1 / 2 else 0

theorem deletionBalancedSinglePerturbation_weights_pos (k n : ℕ) :
    0 < 1 + deletionBalancedSinglePerturbation k n ∧
      0 < 1 - deletionBalancedSinglePerturbation k n := by
  by_cases hnk : n = k
  · norm_num [deletionBalancedSinglePerturbation, hnk]
  · norm_num [deletionBalancedSinglePerturbation, hnk]

/-- Every divisor channel of the thirty-cell period keeps zero linear endpoint under one shared
opposite two-copy perturbation. -/
theorem deletionBalancedLinearObservation_divisor_thirty_eq_zero
    (d : ℕ) (hd : d ∣ 30) :
    deletionBalancedLinearObservation 30
      (fun n => (blockDeletionCoefficient d (n + 1) : ℝ))
      (deletionBalancedSinglePerturbation 2) = 0 := by
  rw [deletionBalancedLinearObservation_eq]
  have hsumZ := sum_blockDeletionCoefficient_eq_zero_of_dvd hd
  have hsumR :
      ∑ n ∈ Finset.range 30,
        (blockDeletionCoefficient d (n + 1) : ℝ) = 0 := by
    exact_mod_cast hsumZ
  rw [hsumR]
  norm_num

/-- The same shared perturbation makes the `2 x 3 x 5` quadratic curvature nonzero. -/
theorem deletionBalancedQuadraticObservation_curvature_two_three_five_ne_zero :
    deletionBalancedQuadraticObservation 30
      (fun n => (deletionFactorizationCurvatureCoefficient 2 3 5 (n + 1) : ℝ))
      (deletionBalancedSinglePerturbation 2) ≠ 0 := by
  rw [deletionBalancedQuadraticObservation_eq]
  have hsumZ :=
    sum_deletionFactorizationCurvatureCoefficient_product_period_eq_zero
      (p := 2) (q := 3) (r := 5) (by norm_num) (by norm_num) (by norm_num)
  have hsumR :
      ∑ n ∈ Finset.range 30,
        (deletionFactorizationCurvatureCoefficient 2 3 5 (n + 1) : ℝ) = 0 := by
    norm_num at hsumZ ⊢
    exact_mod_cast hsumZ
  rw [hsumR]
  have hpert :
      ∑ n ∈ Finset.range 30,
          (deletionFactorizationCurvatureCoefficient 2 3 5 (n + 1) : ℝ) *
            deletionBalancedSinglePerturbation 2 n ^ 2 = 3 / 2 := by
    rw [Finset.sum_eq_single 2]
    · norm_num [deletionBalancedSinglePerturbation,
        deletionFactorizationCurvatureCoefficient, blockDeletionCoefficient]
    · intro n hn hne
      simp [deletionBalancedSinglePerturbation, hne]
    · simp
  rw [hpert]
  norm_num

/-- Closed finite countermodel: all divisor-channel linear endpoints close under one common pair
of positive amplitudes, while the corresponding quadratic curvature remains nonzero. -/
theorem exists_positive_balanced_period_curvature_countermodel :
    ∃ h : ℕ → ℝ,
      (∀ n, 0 < 1 + h n ∧ 0 < 1 - h n) ∧
      (∀ d, d ∣ 30 →
        deletionBalancedLinearObservation 30
          (fun n => (blockDeletionCoefficient d (n + 1) : ℝ)) h = 0) ∧
      deletionBalancedQuadraticObservation 30
        (fun n => (deletionFactorizationCurvatureCoefficient 2 3 5 (n + 1) : ℝ)) h ≠ 0 := by
  refine ⟨deletionBalancedSinglePerturbation 2,
    deletionBalancedSinglePerturbation_weights_pos 2, ?_,
    deletionBalancedQuadraticObservation_curvature_two_three_five_ne_zero⟩
  intro d hd
  exact deletionBalancedLinearObservation_divisor_thirty_eq_zero d hd

end RHTower
