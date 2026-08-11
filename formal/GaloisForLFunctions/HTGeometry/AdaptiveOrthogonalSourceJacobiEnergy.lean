import GaloisForLFunctions.HTGeometry.FiniteOrthogonalMomentPolynomials

/-!
# Adaptive orthogonal source as Jacobi energy

For a positive real moment form, let `Pₙ` be its monic orthogonal polynomial and write the monic
Jacobi recurrence as

`X Pₙ = Pₙ₊₁ + αₙ Pₙ + βₙ Pₙ₋₁`.

This file proves that the literal adaptive mixed amplitude

`(X Pₙ) X (X Pₙ' + Pₙ)`

has moment equal to `‖Pₙ‖²` times an explicit positive Jacobi-compression energy.  No support,
asymptotic, inverse-Hankel, or zero-location hypothesis occurs.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

/-- Squared moment norm of the monic orthogonal polynomial. -/
noncomputable def monicOrthoNorm (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentInner s (monicOrtho s n) (monicOrtho s n)

/-- Diagonal Jacobi coefficient in degree `n`. -/
noncomputable def monicOrthoAlpha (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  momentInner s (Polynomial.X * monicOrtho s n) (monicOrtho s n) /
    monicOrthoNorm s n

/-- Lower monic Jacobi coefficient, with the unused degree-zero value set to zero. -/
noncomputable def monicOrthoBeta (s : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => monicOrthoNorm s (n + 1) / monicOrthoNorm s n

/-- Literal source-first adaptive mixed amplitude. -/
noncomputable def adaptiveOrthoSourcePolynomial (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  (Polynomial.X * monicOrtho s n) *
    (Polynomial.X * (Polynomial.X * (monicOrtho s n).derivative + monicOrtho s n))

/-- Polynomial paired with `Pₙ` after commuting the adaptive source factors. -/
noncomputable def adaptiveOrthoCompanion (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  Polynomial.X ^ 2 * monicOrtho s n +
    Polynomial.X ^ 3 * (monicOrtho s n).derivative

/-- Completed-square Jacobi energy carried by the adaptive source. -/
noncomputable def adaptiveOrthoJacobiEnergy (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n,
      (monicOrthoAlpha s j + monicOrthoAlpha s n / 2) ^ 2) +
    (3 * (n : ℝ) / 4 + 1) * monicOrthoAlpha s n ^ 2 +
    2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) +
    (n + 1 : ℝ) * (monicOrthoBeta s n + monicOrthoBeta s (n + 1))

theorem monicOrthoNorm_pos {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    0 < monicOrthoNorm s n := by
  exact monicOrtho_inner_self_pos h n

theorem monicOrthoBeta_pos {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ}
    (hn : 0 < n) : 0 < monicOrthoBeta s n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact div_pos (monicOrthoNorm_pos h (k + 1)) (monicOrthoNorm_pos h k)

theorem monicOrthoBeta_nonneg {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    0 ≤ monicOrthoBeta s n := by
  rcases n with _ | n
  · simp [monicOrthoBeta]
  · exact (monicOrthoBeta_pos h (Nat.succ_pos n)).le

theorem natDegree_monicOrtho (s : ℕ → ℝ) (n : ℕ) :
    (monicOrtho s n).natDegree = n := by
  have hd := monicOrtho_degree s n
  rw [Polynomial.degree_eq_natDegree (monicOrtho_ne_zero s n)] at hd
  exact_mod_cast hd

@[simp] theorem coeff_monicOrtho_self (s : ℕ → ℝ) (n : ℕ) :
    (monicOrtho s n).coeff n = 1 := by
  have hm := (monicOrtho_monic s n).coeff_natDegree
  rwa [natDegree_monicOrtho s n] at hm

/-- Uniform three-term recurrence, including the degree-zero endpoint. -/
theorem X_mul_monicOrtho {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    Polynomial.X * monicOrtho s n =
      monicOrtho s (n + 1) + monicOrthoAlpha s n • monicOrtho s n +
        monicOrthoBeta s n • monicOrtho s (n - 1) := by
  rcases n with _ | n
  · rw [monicOrtho_eq s 1]
    simp [monicOrthoAlpha, monicOrthoBeta, monicOrthoNorm,
      Polynomial.smul_eq_C_mul]
  · simpa [monicOrthoAlpha, monicOrthoBeta, monicOrthoNorm] using
      monicOrtho_three_term h n

/-- First subleading coefficient of `Pₙ`, with its absent degree-zero value set to zero. -/
noncomputable def monicOrthoFirstCoeff (s : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (monicOrtho s (n + 1)).coeff n

/-- Second subleading coefficient of `Pₙ`, with absent values set to zero. -/
noncomputable def monicOrthoSecondCoeff (s : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n + 2 => (monicOrtho s (n + 2)).coeff n

theorem monicOrthoFirstCoeff_succ {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    monicOrthoFirstCoeff s (n + 1) =
      monicOrthoFirstCoeff s n - monicOrthoAlpha s n := by
  have hr := congrArg (fun p : Polynomial ℝ => p.coeff n) (X_mul_monicOrtho h n)
  rcases n with _ | n
  · simp [monicOrthoFirstCoeff, monicOrthoBeta] at hr ⊢
    linarith
  · have hlow : (monicOrtho s n).coeff (n + 1) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [natDegree_monicOrtho s n]
      omega
    simp [monicOrthoFirstCoeff, Polynomial.coeff_X_mul, hlow] at hr ⊢
    linarith

theorem monicOrthoFirstCoeff_eq_neg_sum {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    monicOrthoFirstCoeff s n =
      -(∑ j ∈ Finset.range n, monicOrthoAlpha s j) := by
  induction n with
  | zero => simp [monicOrthoFirstCoeff]
  | succ n ih =>
      rw [monicOrthoFirstCoeff_succ h n, ih, Finset.sum_range_succ]
      ring

theorem monicOrthoSecondCoeff_succ {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    monicOrthoSecondCoeff s (n + 1) =
      monicOrthoSecondCoeff s n -
        monicOrthoAlpha s n * monicOrthoFirstCoeff s n - monicOrthoBeta s n := by
  rcases n with _ | _ | n
  · simp [monicOrthoSecondCoeff, monicOrthoFirstCoeff, monicOrthoBeta]
  · have hr := congrArg (fun p : Polynomial ℝ => p.coeff 0) (X_mul_monicOrtho h 1)
    simp [monicOrthoSecondCoeff, monicOrthoFirstCoeff] at hr ⊢
    linarith
  · have hr := congrArg (fun p : Polynomial ℝ => p.coeff (n + 1))
      (X_mul_monicOrtho h (n + 2))
    simp [monicOrthoSecondCoeff, monicOrthoFirstCoeff, Polynomial.coeff_X_mul] at hr ⊢
    linarith

/-- Exact quadratic invariant of the first two coefficient jets. -/
theorem monicOrtho_coeffJet_energy {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    monicOrthoFirstCoeff s n ^ 2 - 2 * monicOrthoSecondCoeff s n =
      (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ 2) +
        2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) := by
  induction n with
  | zero => simp [monicOrthoFirstCoeff, monicOrthoSecondCoeff]
  | succ n ih =>
      rw [monicOrthoFirstCoeff_succ h n, monicOrthoSecondCoeff_succ h n,
        Finset.sum_range_succ, Finset.sum_range_succ]
      linear_combination (norm := ring_nf) ih

theorem adaptiveOrthoCompanion_coeff_add_two (s : ℕ → ℝ) (n : ℕ) :
    (adaptiveOrthoCompanion s n).coeff (n + 2) = (n + 1 : ℝ) := by
  rcases n with _ | n
  · simp [adaptiveOrthoCompanion]
  · simp [adaptiveOrthoCompanion, Polynomial.coeff_X_pow_mul',
      Polynomial.coeff_derivative]
    ring

theorem adaptiveOrthoCompanion_coeff_add_one (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (adaptiveOrthoCompanion s n).coeff (n + 1) =
      (n : ℝ) * monicOrthoFirstCoeff s n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rcases k with _ | k
  · simp [adaptiveOrthoCompanion, Polynomial.coeff_X_pow_mul', monicOrthoFirstCoeff]
  · simp [adaptiveOrthoCompanion, Polynomial.coeff_X_pow_mul',
      Polynomial.coeff_derivative, monicOrthoFirstCoeff]
    ring

theorem adaptiveOrthoCompanion_coeff_self (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (adaptiveOrthoCompanion s n).coeff n =
      ((n - 1 : ℕ) : ℝ) * monicOrthoSecondCoeff s n := by
  rcases n with _ | _ | n
  · omega
  · simp [adaptiveOrthoCompanion, Polynomial.coeff_X_pow_mul', monicOrthoSecondCoeff]
  · rcases n with _ | n
    · simp [adaptiveOrthoCompanion, Polynomial.coeff_X_pow_mul', monicOrthoSecondCoeff]
    · simp [adaptiveOrthoCompanion, Polynomial.coeff_X_pow_mul',
        Polynomial.coeff_derivative, monicOrthoSecondCoeff]
      ring

/-- Coefficient cancelling the `Pₙ₊₁` jet of the adaptive companion. -/
noncomputable def adaptiveOrthoUpperCoeff (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * monicOrthoFirstCoeff s n -
    (n + 1 : ℝ) * monicOrthoFirstCoeff s (n + 2)

/-- Coefficient of `Pₙ` in the adaptive companion modulo polynomials of degree `<n`. -/
noncomputable def adaptiveOrthoProjectionCoeff (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n - 1 : ℕ) : ℝ) * monicOrthoSecondCoeff s n -
    (n + 1 : ℝ) * monicOrthoSecondCoeff s (n + 2) -
    adaptiveOrthoUpperCoeff s n * monicOrthoFirstCoeff s (n + 1)

theorem adaptiveOrthoProjectionCoeff_eq_coeffJet {s : ℕ → ℝ}
    (h : PositiveMomentForm s) {n : ℕ} (hn : 0 < n) :
    adaptiveOrthoProjectionCoeff s n =
      monicOrthoFirstCoeff s n ^ 2 - 2 * monicOrthoSecondCoeff s n -
        monicOrthoAlpha s n * monicOrthoFirstCoeff s n +
        (n + 1 : ℝ) * monicOrthoAlpha s n ^ 2 +
        (n + 1 : ℝ) * (monicOrthoBeta s n + monicOrthoBeta s (n + 1)) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have hc : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      norm_cast
      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hn)
    linarith
  rw [adaptiveOrthoProjectionCoeff, adaptiveOrthoUpperCoeff, hcast,
    monicOrthoSecondCoeff_succ h (n + 1), monicOrthoSecondCoeff_succ h n,
    monicOrthoFirstCoeff_succ h (n + 1), monicOrthoFirstCoeff_succ h n]
  ring

theorem adaptiveOrthoJacobiEnergy_eq_coeffJet {s : ℕ → ℝ}
    (h : PositiveMomentForm s) (n : ℕ) :
    adaptiveOrthoJacobiEnergy s n =
      monicOrthoFirstCoeff s n ^ 2 - 2 * monicOrthoSecondCoeff s n -
        monicOrthoAlpha s n * monicOrthoFirstCoeff s n +
        (n + 1 : ℝ) * monicOrthoAlpha s n ^ 2 +
        (n + 1 : ℝ) * (monicOrthoBeta s n + monicOrthoBeta s (n + 1)) := by
  have hsquares :
      (∑ j ∈ Finset.range n,
          (monicOrthoAlpha s j + monicOrthoAlpha s n / 2) ^ 2) =
        (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ 2) +
          monicOrthoAlpha s n * (∑ j ∈ Finset.range n, monicOrthoAlpha s j) +
          (n : ℝ) * monicOrthoAlpha s n ^ 2 / 4 := by
    have hpoint (j : ℕ) :
        (monicOrthoAlpha s j + monicOrthoAlpha s n / 2) ^ 2 =
          monicOrthoAlpha s j ^ 2 +
            monicOrthoAlpha s n * monicOrthoAlpha s j +
            monicOrthoAlpha s n ^ 2 / 4 := by ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hjet := monicOrtho_coeffJet_energy h n
  rw [monicOrthoFirstCoeff_eq_neg_sum h n] at hjet
  rw [adaptiveOrthoJacobiEnergy, hsquares, monicOrthoFirstCoeff_eq_neg_sum h n]
  ring_nf at hjet ⊢
  linarith

theorem adaptiveOrthoProjectionCoeff_eq_energy {s : ℕ → ℝ}
    (h : PositiveMomentForm s) {n : ℕ} (hn : 0 < n) :
    adaptiveOrthoProjectionCoeff s n = adaptiveOrthoJacobiEnergy s n := by
  rw [adaptiveOrthoProjectionCoeff_eq_coeffJet h hn,
    adaptiveOrthoJacobiEnergy_eq_coeffJet h n]

theorem coeff_monicOrtho_eq_zero_of_lt (s : ℕ → ℝ) {n k : ℕ} (hnk : n < k) :
    (monicOrtho s n).coeff k = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rwa [natDegree_monicOrtho s n]

theorem adaptiveOrthoCompanion_coeff_eq_zero_of_add_two_lt
    (s : ℕ → ℝ) {n k : ℕ} (hnk : n + 2 < k) :
    (adaptiveOrthoCompanion s n).coeff k = 0 := by
  have h2 : 2 ≤ k := by omega
  have h3 : 3 ≤ k := by omega
  have hnsub : n < k - 2 := by omega
  have hp : (monicOrtho s n).coeff (k - 2) = 0 :=
    coeff_monicOrtho_eq_zero_of_lt s hnsub
  rw [adaptiveOrthoCompanion, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', if_pos h2,
    Polynomial.coeff_X_pow_mul', if_pos h3,
    Polynomial.coeff_derivative]
  rw [show k - 3 + 1 = k - 2 by omega, hp]
  ring

/-- The part of the adaptive companion below the `Pₙ` projection. -/
noncomputable def adaptiveOrthoRemainder (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  adaptiveOrthoCompanion s n -
      (n + 1 : ℝ) • monicOrtho s (n + 2) -
    adaptiveOrthoUpperCoeff s n • monicOrtho s (n + 1) -
    adaptiveOrthoProjectionCoeff s n • monicOrtho s n

theorem adaptiveOrthoRemainder_coeff_add_two (s : ℕ → ℝ) (n : ℕ) :
    (adaptiveOrthoRemainder s n).coeff (n + 2) = 0 := by
  have h1 : (monicOrtho s (n + 1)).coeff (n + 2) = 0 :=
    coeff_monicOrtho_eq_zero_of_lt s (by omega)
  have h0 : (monicOrtho s n).coeff (n + 2) = 0 :=
    coeff_monicOrtho_eq_zero_of_lt s (by omega)
  simp [adaptiveOrthoRemainder, adaptiveOrthoCompanion_coeff_add_two, h1, h0]

theorem adaptiveOrthoRemainder_coeff_add_one (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (adaptiveOrthoRemainder s n).coeff (n + 1) = 0 := by
  have h0 : (monicOrtho s n).coeff (n + 1) = 0 :=
    coeff_monicOrtho_eq_zero_of_lt s (by omega)
  rw [adaptiveOrthoRemainder, Polynomial.coeff_sub, Polynomial.coeff_sub,
    Polynomial.coeff_sub, Polynomial.coeff_smul, Polynomial.coeff_smul,
    Polynomial.coeff_smul, adaptiveOrthoCompanion_coeff_add_one s hn]
  simp [monicOrthoFirstCoeff, h0, adaptiveOrthoUpperCoeff]

theorem adaptiveOrthoRemainder_coeff_self (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (adaptiveOrthoRemainder s n).coeff n = 0 := by
  rw [adaptiveOrthoRemainder, Polynomial.coeff_sub, Polynomial.coeff_sub,
    Polynomial.coeff_sub, Polynomial.coeff_smul, Polynomial.coeff_smul,
    Polynomial.coeff_smul, adaptiveOrthoCompanion_coeff_self s hn]
  have hn2 : (monicOrtho s (n + 2)).coeff n = monicOrthoSecondCoeff s (n + 2) := by
    rfl
  have hn1 : (monicOrtho s (n + 1)).coeff n = monicOrthoFirstCoeff s (n + 1) := by
    rfl
  rw [hn2, hn1, coeff_monicOrtho_self]
  unfold adaptiveOrthoProjectionCoeff
  ring

theorem degree_adaptiveOrthoRemainder_lt (s : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    (adaptiveOrthoRemainder s n).degree < (n : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hnk
  by_cases hhigh : n + 2 < k
  · have hn2 : (monicOrtho s (n + 2)).coeff k = 0 :=
      coeff_monicOrtho_eq_zero_of_lt s hhigh
    have hn1 : (monicOrtho s (n + 1)).coeff k = 0 :=
      coeff_monicOrtho_eq_zero_of_lt s (by omega)
    have hn0 : (monicOrtho s n).coeff k = 0 :=
      coeff_monicOrtho_eq_zero_of_lt s (by omega)
    simp [adaptiveOrthoRemainder,
      adaptiveOrthoCompanion_coeff_eq_zero_of_add_two_lt s hhigh, hn2, hn1, hn0]
  · rcases (by omega : k = n ∨ k = n + 1 ∨ k = n + 2) with rfl | rfl | rfl
    · exact adaptiveOrthoRemainder_coeff_self s hn
    · exact adaptiveOrthoRemainder_coeff_add_one s hn
    · exact adaptiveOrthoRemainder_coeff_add_two s n

theorem adaptiveOrthoCompanion_decomposition (s : ℕ → ℝ) (n : ℕ) :
    adaptiveOrthoCompanion s n =
      (n + 1 : ℝ) • monicOrtho s (n + 2) +
        adaptiveOrthoUpperCoeff s n • monicOrtho s (n + 1) +
        adaptiveOrthoProjectionCoeff s n • monicOrtho s n +
        adaptiveOrthoRemainder s n := by
  unfold adaptiveOrthoRemainder
  module

theorem adaptiveOrthoSourcePolynomial_eq_mul_companion (s : ℕ → ℝ) (n : ℕ) :
    adaptiveOrthoSourcePolynomial s n =
      monicOrtho s n * adaptiveOrthoCompanion s n := by
  unfold adaptiveOrthoSourcePolynomial adaptiveOrthoCompanion
  ring

/-- Exact arithmetic source law: adaptive mixed amplitude is norm times Jacobi energy. -/
theorem momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy
    {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ} (hn : 0 < n) :
    momentFunctional s (adaptiveOrthoSourcePolynomial s n) =
      monicOrthoNorm s n * adaptiveOrthoJacobiEnergy s n := by
  have hhigh2 : momentInner s (monicOrtho s n) (monicOrtho s (n + 2)) = 0 :=
    monicOrtho_inner_eq_zero h (by omega)
  have hhigh1 : momentInner s (monicOrtho s n) (monicOrtho s (n + 1)) = 0 :=
    monicOrtho_inner_eq_zero h (by omega)
  have hrem : momentInner s (monicOrtho s n) (adaptiveOrthoRemainder s n) = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt h n n le_rfl _
      (degree_adaptiveOrthoRemainder_lt s hn)
  rw [adaptiveOrthoSourcePolynomial_eq_mul_companion, ← momentInner_def,
    adaptiveOrthoCompanion_decomposition, momentInner_add_right,
    momentInner_add_right, momentInner_add_right, momentInner_smul_right,
    momentInner_smul_right, momentInner_smul_right, hhigh2, hhigh1, hrem,
    adaptiveOrthoProjectionCoeff_eq_energy h hn]
  simp [monicOrthoNorm]
  ring

/-- The completed Jacobi energy is strictly positive in every positive degree. -/
theorem adaptiveOrthoJacobiEnergy_pos {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ}
    (hn : 0 < n) : 0 < adaptiveOrthoJacobiEnergy s n := by
  have hsquares :
      0 ≤ ∑ j ∈ Finset.range n,
        (monicOrthoAlpha s j + monicOrthoAlpha s n / 2) ^ 2 := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag :
      0 ≤ (3 * (n : ℝ) / 4 + 1) * monicOrthoAlpha s n ^ 2 := by
    positivity
  have hinterior :
      0 ≤ 2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => monicOrthoBeta_nonneg h j)
  have hboundary :
      0 < (n + 1 : ℝ) * (monicOrthoBeta s n + monicOrthoBeta s (n + 1)) := by
    exact mul_pos (by positivity)
      (add_pos (monicOrthoBeta_pos h hn)
        (monicOrthoBeta_pos h (by omega : 0 < n + 1)))
  unfold adaptiveOrthoJacobiEnergy
  linarith

/-- Universal strict positivity of the literal adaptive mixed arithmetic source. -/
theorem momentFunctional_adaptiveOrthoSourcePolynomial_pos
    {s : ℕ → ℝ} (h : PositiveMomentForm s) {n : ℕ} (hn : 0 < n) :
    0 < momentFunctional s (adaptiveOrthoSourcePolynomial s n) := by
  rw [momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy h hn]
  exact mul_pos (monicOrthoNorm_pos h n) (adaptiveOrthoJacobiEnergy_pos h hn)

/-! ## Finite Hankel-block localization -/

theorem monicOrthoNorm_pos_below {s : ℕ → ℝ} {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n < N) :
    0 < monicOrthoNorm s n := by
  exact monicOrtho_inner_self_pos_below h hnN

theorem monicOrthoBeta_pos_below {s : ℕ → ℝ} {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hn : 0 < n) (hnN : n < N) :
    0 < monicOrthoBeta s n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact div_pos (monicOrthoNorm_pos_below h hnN)
    (monicOrthoNorm_pos_below h (by omega))

theorem X_mul_monicOrtho_below {s : ℕ → ℝ} {N n : ℕ}
    (h : PositiveMomentFormBelow s N) (hnN : n + 1 ≤ N) :
    Polynomial.X * monicOrtho s n =
      monicOrtho s (n + 1) + monicOrthoAlpha s n • monicOrtho s n +
        monicOrthoBeta s n • monicOrtho s (n - 1) := by
  rcases n with _ | n
  · rw [monicOrtho_eq s 1]
    simp [monicOrthoAlpha, monicOrthoBeta, monicOrthoNorm,
      Polynomial.smul_eq_C_mul]
  · simpa [monicOrthoAlpha, monicOrthoBeta, monicOrthoNorm] using
      monicOrtho_three_term_below h hnN

theorem monicOrthoFirstCoeff_succ_below {s : ℕ → ℝ} {N : ℕ}
    (h : PositiveMomentFormBelow s N) {n : ℕ} (hnN : n + 1 ≤ N) :
    monicOrthoFirstCoeff s (n + 1) =
      monicOrthoFirstCoeff s n - monicOrthoAlpha s n := by
  have hr := congrArg (fun p : Polynomial ℝ => p.coeff n)
    (X_mul_monicOrtho_below h hnN)
  rcases n with _ | n
  · simp [monicOrthoFirstCoeff, monicOrthoBeta] at hr ⊢
    linarith
  · have hlow : (monicOrtho s n).coeff (n + 1) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [natDegree_monicOrtho]
      omega
    simp [monicOrthoFirstCoeff, Polynomial.coeff_X_mul, hlow] at hr ⊢
    linarith

theorem monicOrthoFirstCoeff_eq_neg_sum_below {s : ℕ → ℝ} {N : ℕ}
    (h : PositiveMomentFormBelow s N) {n : ℕ} (hnN : n ≤ N) :
    monicOrthoFirstCoeff s n =
      -(∑ j ∈ Finset.range n, monicOrthoAlpha s j) := by
  induction n with
  | zero => simp [monicOrthoFirstCoeff]
  | succ n ih =>
      rw [monicOrthoFirstCoeff_succ_below h hnN, ih (by omega),
        Finset.sum_range_succ]
      ring

theorem monicOrthoSecondCoeff_succ_below {s : ℕ → ℝ} {N : ℕ}
    (h : PositiveMomentFormBelow s N) {n : ℕ} (hnN : n + 1 ≤ N) :
    monicOrthoSecondCoeff s (n + 1) =
      monicOrthoSecondCoeff s n -
        monicOrthoAlpha s n * monicOrthoFirstCoeff s n - monicOrthoBeta s n := by
  rcases n with _ | _ | n
  · simp [monicOrthoSecondCoeff, monicOrthoFirstCoeff, monicOrthoBeta]
  · have hr := congrArg (fun p : Polynomial ℝ => p.coeff 0)
      (X_mul_monicOrtho_below h hnN)
    simp [monicOrthoSecondCoeff, monicOrthoFirstCoeff] at hr ⊢
    linarith
  · have hr := congrArg (fun p : Polynomial ℝ => p.coeff (n + 1))
      (X_mul_monicOrtho_below h hnN)
    simp [monicOrthoSecondCoeff, monicOrthoFirstCoeff, Polynomial.coeff_X_mul] at hr ⊢
    linarith

theorem monicOrtho_coeffJet_energy_below {s : ℕ → ℝ} {N : ℕ}
    (h : PositiveMomentFormBelow s N) {n : ℕ} (hnN : n ≤ N) :
    monicOrthoFirstCoeff s n ^ 2 - 2 * monicOrthoSecondCoeff s n =
      (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ 2) +
        2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) := by
  induction n with
  | zero => simp [monicOrthoFirstCoeff, monicOrthoSecondCoeff]
  | succ n ih =>
      rw [monicOrthoFirstCoeff_succ_below h hnN,
        monicOrthoSecondCoeff_succ_below h hnN,
        Finset.sum_range_succ, Finset.sum_range_succ]
      linear_combination (norm := ring_nf) ih (by omega)

theorem adaptiveOrthoProjectionCoeff_eq_coeffJet_below
    {s : ℕ → ℝ} {N : ℕ} (h : PositiveMomentFormBelow s N)
    {n : ℕ} (hn : 0 < n) (hnN : n + 2 ≤ N) :
    adaptiveOrthoProjectionCoeff s n =
      monicOrthoFirstCoeff s n ^ 2 - 2 * monicOrthoSecondCoeff s n -
        monicOrthoAlpha s n * monicOrthoFirstCoeff s n +
        (n + 1 : ℝ) * monicOrthoAlpha s n ^ 2 +
        (n + 1 : ℝ) * (monicOrthoBeta s n + monicOrthoBeta s (n + 1)) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have hc : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      norm_cast
      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hn)
    linarith
  rw [adaptiveOrthoProjectionCoeff, adaptiveOrthoUpperCoeff, hcast,
    monicOrthoSecondCoeff_succ_below h (by omega : n + 2 ≤ N),
    monicOrthoSecondCoeff_succ_below h (by omega : n + 1 ≤ N),
    monicOrthoFirstCoeff_succ_below h (by omega : n + 2 ≤ N),
    monicOrthoFirstCoeff_succ_below h (by omega : n + 1 ≤ N)]
  ring

theorem adaptiveOrthoJacobiEnergy_eq_coeffJet_below
    {s : ℕ → ℝ} {N : ℕ} (h : PositiveMomentFormBelow s N)
    {n : ℕ} (hnN : n ≤ N) :
    adaptiveOrthoJacobiEnergy s n =
      monicOrthoFirstCoeff s n ^ 2 - 2 * monicOrthoSecondCoeff s n -
        monicOrthoAlpha s n * monicOrthoFirstCoeff s n +
        (n + 1 : ℝ) * monicOrthoAlpha s n ^ 2 +
        (n + 1 : ℝ) * (monicOrthoBeta s n + monicOrthoBeta s (n + 1)) := by
  have hsquares :
      (∑ j ∈ Finset.range n,
          (monicOrthoAlpha s j + monicOrthoAlpha s n / 2) ^ 2) =
        (∑ j ∈ Finset.range n, monicOrthoAlpha s j ^ 2) +
          monicOrthoAlpha s n * (∑ j ∈ Finset.range n, monicOrthoAlpha s j) +
          (n : ℝ) * monicOrthoAlpha s n ^ 2 / 4 := by
    have hpoint (j : ℕ) :
        (monicOrthoAlpha s j + monicOrthoAlpha s n / 2) ^ 2 =
          monicOrthoAlpha s j ^ 2 +
            monicOrthoAlpha s n * monicOrthoAlpha s j +
            monicOrthoAlpha s n ^ 2 / 4 := by ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hjet := monicOrtho_coeffJet_energy_below h hnN
  rw [monicOrthoFirstCoeff_eq_neg_sum_below h hnN] at hjet
  rw [adaptiveOrthoJacobiEnergy, hsquares,
    monicOrthoFirstCoeff_eq_neg_sum_below h hnN]
  ring_nf at hjet ⊢
  linarith

theorem adaptiveOrthoProjectionCoeff_eq_energy_below
    {s : ℕ → ℝ} {N : ℕ} (h : PositiveMomentFormBelow s N)
    {n : ℕ} (hn : 0 < n) (hnN : n + 2 ≤ N) :
    adaptiveOrthoProjectionCoeff s n = adaptiveOrthoJacobiEnergy s n := by
  rw [adaptiveOrthoProjectionCoeff_eq_coeffJet_below h hn hnN,
    adaptiveOrthoJacobiEnergy_eq_coeffJet_below h (by omega : n ≤ N)]

theorem adaptiveOrthoJacobiEnergy_pos_below
    {s : ℕ → ℝ} {N : ℕ} (h : PositiveMomentFormBelow s N)
    {n : ℕ} (hn : 0 < n) (hnN : n + 2 ≤ N) :
    0 < adaptiveOrthoJacobiEnergy s n := by
  have hsquares :
      0 ≤ ∑ j ∈ Finset.range n,
        (monicOrthoAlpha s j + monicOrthoAlpha s n / 2) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdiag :
      0 ≤ (3 * (n : ℝ) / 4 + 1) * monicOrthoAlpha s n ^ 2 := by
    positivity
  have hinterior :
      0 ≤ 2 * (∑ j ∈ Finset.range n, monicOrthoBeta s j) := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [monicOrthoBeta]
    · exact (monicOrthoBeta_pos_below h (Nat.succ_pos j) (by
        have hjn := Finset.mem_range.mp hj
        omega)).le
  have hboundary :
      0 < (n + 1 : ℝ) * (monicOrthoBeta s n + monicOrthoBeta s (n + 1)) := by
    exact mul_pos (by positivity)
      (add_pos
        (monicOrthoBeta_pos_below h hn (by omega))
        (monicOrthoBeta_pos_below h (by omega) (by omega)))
  unfold adaptiveOrthoJacobiEnergy
  linarith

/-- Exact adaptive source law from one finite positive Hankel block. -/
theorem momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below
    {s : ℕ → ℝ} {N : ℕ} (h : PositiveMomentFormBelow s N)
    {n : ℕ} (hn : 0 < n) (hnN : n + 2 ≤ N) :
    momentFunctional s (adaptiveOrthoSourcePolynomial s n) =
      monicOrthoNorm s n * adaptiveOrthoJacobiEnergy s n := by
  have hhigh2 : momentInner s (monicOrtho s n) (monicOrtho s (n + 2)) = 0 :=
    monicOrtho_inner_eq_zero_below h (by omega) hnN (by omega)
  have hhigh1 : momentInner s (monicOrtho s n) (monicOrtho s (n + 1)) = 0 :=
    monicOrtho_inner_eq_zero_below h (by omega) (by omega) (by omega)
  have hrem : momentInner s (monicOrtho s n) (adaptiveOrthoRemainder s n) = 0 :=
    monicOrtho_inner_eq_zero_of_degree_lt_below h (by omega)
      (degree_adaptiveOrthoRemainder_lt s hn)
  rw [adaptiveOrthoSourcePolynomial_eq_mul_companion, ← momentInner_def,
    adaptiveOrthoCompanion_decomposition, momentInner_add_right,
    momentInner_add_right, momentInner_add_right, momentInner_smul_right,
    momentInner_smul_right, momentInner_smul_right, hhigh2, hhigh1, hrem,
    adaptiveOrthoProjectionCoeff_eq_energy_below h hn hnN]
  simp [monicOrthoNorm]
  ring

theorem momentFunctional_adaptiveOrthoSourcePolynomial_pos_below
    {s : ℕ → ℝ} {N : ℕ} (h : PositiveMomentFormBelow s N)
    {n : ℕ} (hn : 0 < n) (hnN : n + 2 ≤ N) :
    0 < momentFunctional s (adaptiveOrthoSourcePolynomial s n) := by
  rw [momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below h hn hnN]
  exact mul_pos (monicOrthoNorm_pos_below h (by omega))
    (adaptiveOrthoJacobiEnergy_pos_below h hn hnN)

/-- Matrix form: the `(n+2) × (n+2)` positive Hankel block alone forces source positivity. -/
theorem momentFunctional_adaptiveOrthoSourcePolynomial_pos_of_hankelPosDef
    {s : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (h : (momentHankelMatrix s (n + 2)).PosDef) :
    0 < momentFunctional s (adaptiveOrthoSourcePolynomial s n) := by
  exact momentFunctional_adaptiveOrthoSourcePolynomial_pos_below
    (positiveMomentFormBelow_of_hankelPosDef h) hn le_rfl

end HTGeometry
