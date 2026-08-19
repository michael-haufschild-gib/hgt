import GaloisForLFunctions.HTGeometry.InverseSeriesLadder

/-!
# The first nonvanishing coefficient of the forced series

The ladder of `InverseSeriesLadder` produces one coefficient per order.  If every one of them
vanishes, the residual is the truncated logarithmic-derivative series itself, and its divisibility
forces every `D_m` to vanish.  So a nonzero `D` produces a first nonzero coefficient, and up to that
order the truncation is `1 + c X^{m}`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

theorem coeff_lamPoly (D : ℕ → ℂ) {N m : ℕ} (h : m ≤ N) :
    (lamPoly D N).coeff (m + 1) = -D m := by
  rw [lamPoly, Polynomial.coeff_neg, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have : m + 1 ≠ j + 1 := by omega
    rw [if_neg this, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega : m < N + 1)) hmem

theorem natDegree_expPoly_le (D : ℕ → ℂ) (N : ℕ) : (expPoly D N).natDegree ≤ N := by
  induction N with
  | zero =>
      have : expPoly D 0 = 1 := rfl
      rw [this]
      simp
  | succ n ih =>
      have hstep : expPoly D (n + 1)
          = expPoly D n + C (expLadderCoeffOf D (expPoly D n) n) * X ^ (n + 1) := rfl
      rw [hstep]
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      refine max_le (by omega) ?_
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_X_pow]

/-- The coefficient produced at order `n`. -/
def expCoeffSeq (D : ℕ → ℂ) (n : ℕ) : ℂ := (expPoly D n).coeff n

theorem expPoly_succ_eq (D : ℕ → ℂ) (N : ℕ) :
    expPoly D (N + 1) = expPoly D N + C (expCoeffSeq D (N + 1)) * X ^ (N + 1) := by
  have hstep : expPoly D (N + 1)
      = expPoly D N + C (expLadderCoeffOf D (expPoly D N) N) * X ^ (N + 1) := rfl
  have hc : expCoeffSeq D (N + 1) = expLadderCoeffOf D (expPoly D N) N := by
    rw [expCoeffSeq, hstep, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    have hz : (expPoly D N).coeff (N + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by have := natDegree_expPoly_le D N; omega)
    rw [hz, zero_add]
  rw [hc]
  exact hstep

theorem expPoly_eq_one_of_coeffs (D : ℕ → ℂ) (N : ℕ)
    (h : ∀ n, 1 ≤ n → n ≤ N → expCoeffSeq D n = 0) : expPoly D N = 1 := by
  induction N with
  | zero => rfl
  | succ n ih =>
      rw [expPoly_succ_eq, ih (fun m hm1 hmn => h m hm1 (by omega)),
        h (n + 1) (by omega) le_rfl]
      simp

theorem forall_eq_zero_of_expPoly_eq_one (D : ℕ → ℂ) (hD0 : D 0 = 0)
    (h : ∀ N, expPoly D N = 1) : ∀ m, D m = 0 := by
  intro m
  have hres : resPoly D m = lamPoly D m := by
    rw [resPoly, h m]
    simp
  have hdvd : (X : ℂ[X]) ^ (m + 2) ∣ lamPoly D m := by
    rw [← hres]
    exact X_pow_dvd_resPoly D hD0 m
  have hzero := (Polynomial.X_pow_dvd_iff.mp hdvd) (m + 1) (by omega)
  rw [coeff_lamPoly D (le_refl m)] at hzero
  exact neg_eq_zero.mp hzero

/-- **A nonzero moment sequence produces a first nonzero ladder coefficient.** -/
theorem exists_first_expCoeffSeq_ne_zero (D : ℕ → ℂ) (hD0 : D 0 = 0)
    (hD : ∃ m, D m ≠ 0) :
    ∃ M : ℕ, expCoeffSeq D (M + 1) ≠ 0 ∧ expPoly D M = 1 := by
  classical
  have hex : ∃ n : ℕ, expCoeffSeq D (n + 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ N, expPoly D N = 1 := by
      intro N
      refine expPoly_eq_one_of_coeffs D N fun n hn1 _ => ?_
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
      exact hcon j
    obtain ⟨m, hm⟩ := hD
    exact hm (forall_eq_zero_of_expPoly_eq_one D hD0 hall m)
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  refine expPoly_eq_one_of_coeffs D (Nat.find hex) fun n hn1 hnle => ?_
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  by_contra hne
  have hle := Nat.find_min' hex hne
  omega

end

end GaloisForLFunctions.HTGeometry
