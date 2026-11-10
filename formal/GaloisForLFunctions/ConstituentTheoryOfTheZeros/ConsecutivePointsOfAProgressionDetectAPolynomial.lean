import GaloisForLFunctions.HTGeometry.PowerSumTuranWeightedLowerBound
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicExpSum
import GaloisForLFunctions.InfiniteRankPurityTheory.TheZerosContainNoClassOfOneFrobenius

/-!
# Consecutive points of a progression detect a polynomial

Along a vertical arithmetic progression `s₀ + iνd` an exponential polynomial
`F(s) = Σ_{k < N} a_k e^{λ_k s}` with real frequencies is a power sum
`Σ_k b_k z_k^ν` with unimodular nodes `z_k = e^{iλ_k d}`. Turán's theorem on power sums, which
needs no separation of the nodes, gives:

* **Two-sided detection** (`exists_le_norm_expSum_progression`): among any `N` consecutive points
  of the progression at distance `M` from `s₀` there is one where
  `‖F‖ ≥ ‖F(s₀)‖ / C(N, M)`, with a constant that depends on the number of terms and the distance
  only, not on the frequencies or the coefficients.
* **Rigidity** (`expSum_eq_zero_on_progression`): if `F` vanishes at `N` consecutive points of a
  vertical progression, it vanishes at every point of the progression, in both directions.
* **Constituents** (`exists_zero_expSum_not_xi_zero_on_progression`): such an `F` has, on that
  progression, a zero that is not a zero of `ξ`, because the zeros of `ξ` contain no vertical
  progression. A polynomial of `N` terms whose zeros in a set are zeros of `ξ` turns `N`
  consecutive zeros on a progression into zeros of `ξ` at every point of the progression in the
  set (`xi_eq_zero_on_progression_of_consecutive`).
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.InfiniteRankPurityTheory

variable {n : ℕ}

/-- Turán's constant for `N` terms at distance `M`. -/
def turanConstant (N M : ℕ) : ℝ :=
  2 * (Real.exp 1 * (N : ℝ) * (6 * ((N : ℝ) + 1) * ((M : ℝ) + 2 * (N : ℝ) + 2)) ^ N)

theorem turanConstant_pos {N : ℕ} (hN : 0 < N) (M : ℕ) : 0 < turanConstant N M := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  unfold turanConstant
  positivity

/-- Along a vertical progression an exponential polynomial is a power sum with the unimodular
nodes `e^{iλ_k d}`. -/
theorem expSum_progression (a : Fin n → ℂ) (lam : Fin n → ℝ) (s₀ : ℂ) (d : ℝ) (ν : ℕ) :
    expSum a lam (s₀ + ((ν * d : ℝ) : ℂ) * I) =
      ∑ k, (a k * exp ((lam k : ℂ) * s₀)) * exp (((lam k * d : ℝ) : ℂ) * I) ^ ν := by
  unfold expSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Two-sided detection without separation.** Among the points `s₀ + iνd`,
`M + 1 ≤ ν ≤ M + N`, of a vertical progression there is one at which an exponential polynomial of
`N` terms is at least `‖F(s₀)‖ / C(N, M)`. -/
theorem exists_le_norm_expSum_progression (hn : 0 < n) (a : Fin n → ℂ) (lam : Fin n → ℝ)
    (s₀ : ℂ) (d : ℝ) (M : ℕ) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + n ∧
      ‖expSum a lam s₀‖ / turanConstant n M ≤ ‖expSum a lam (s₀ + ((ν * d : ℝ) : ℂ) * I)‖ := by
  by_cases h0 : expSum a lam s₀ = 0
  · exact ⟨M + 1, le_rfl, by omega, by rw [h0, norm_zero, zero_div]; exact norm_nonneg _⟩
  have hz1 : ∀ k : Fin n, ‖exp (((lam k * d : ℝ) : ℂ) * I)‖ = 1 := fun k =>
    Complex.norm_exp_ofReal_mul_I _
  obtain ⟨ν, h1, h2, h3⟩ := HTGeometry.exists_norm_weightedPowerSum_ge Finset.univ
    (fun k : Fin n => exp (((lam k * d : ℝ) : ℂ) * I)) (fun k => a k * exp ((lam k : ℂ) * s₀))
    ⟨⟨0, hn⟩, Finset.mem_univ _, (hz1 _).ge⟩ M (norm_pos_iff.mpr h0) (fun t _ ht1 => by
      rw [Finset.filter_true_of_mem fun k _ => by rw [hz1 k]; exact ht1]
      exact le_of_eq rfl)
  rw [Finset.card_univ, Fintype.card_fin] at h2 h3
  refine ⟨ν, h1, h2, ?_⟩
  rw [expSum_progression]
  exact h3

/-- **Rigidity along a progression.** An exponential polynomial of `N` terms that vanishes at `N`
consecutive points of a vertical arithmetic progression vanishes at every point of it. -/
theorem expSum_eq_zero_on_progression (hn : 0 < n) (a : Fin n → ℂ) (lam : Fin n → ℝ) (s₀ : ℂ)
    (d : ℝ) (K : ℤ)
    (h : ∀ j : ℕ, j < n → expSum a lam (s₀ + (((K + 1 + j : ℤ) * d : ℝ) : ℂ) * I) = 0) (ν : ℤ) :
    expSum a lam (s₀ + ((ν * d : ℝ) : ℂ) * I) = 0 := by
  have hwin : ∀ μ : ℤ, K + 1 ≤ μ → μ ≤ K + n →
      expSum a lam (s₀ + ((μ * d : ℝ) : ℂ) * I) = 0 := by
    intro μ h1 h2
    obtain ⟨j, hj⟩ : ∃ j : ℕ, μ = K + 1 + j := ⟨(μ - K - 1).toNat, by omega⟩
    rw [hj]
    exact h j (by omega)
  by_cases h1 : ν ≤ K
  · -- a base point before the window, step `d`
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = K - ν := ⟨(K - ν).toNat, by omega⟩
    obtain ⟨μ, hμ1, hμ2, hμ3⟩ :=
      exists_le_norm_expSum_progression hn a lam (s₀ + ((ν * d : ℝ) : ℂ) * I) d M
    have hpt : s₀ + ((ν * d : ℝ) : ℂ) * I + ((μ * d : ℝ) : ℂ) * I =
        s₀ + ((((ν + μ : ℤ) : ℝ) * d : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [hpt, hwin (ν + μ) (by omega) (by omega), norm_zero,
      div_le_iff₀ (turanConstant_pos hn M), zero_mul] at hμ3
    exact norm_le_zero_iff.mp hμ3
  · by_cases h2 : ν ≤ K + n
    · exact hwin ν (by omega) h2
    · -- a base point after the window, step `−d`
      obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = ν - K - n - 1 := ⟨(ν - K - n - 1).toNat, by omega⟩
      obtain ⟨μ, hμ1, hμ2, hμ3⟩ :=
        exists_le_norm_expSum_progression hn a lam (s₀ + ((ν * d : ℝ) : ℂ) * I) (-d) M
      have hpt : s₀ + ((ν * d : ℝ) : ℂ) * I + ((μ * -d : ℝ) : ℂ) * I =
          s₀ + ((((ν - μ : ℤ) : ℝ) * d : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [hpt, hwin (ν - μ) (by omega) (by omega), norm_zero,
        div_le_iff₀ (turanConstant_pos hn M), zero_mul] at hμ3
      exact norm_le_zero_iff.mp hμ3

/-- **A progression of zeros of a polynomial is not a progression of zeros of `ξ`.** An
exponential polynomial of `N` terms that vanishes at `N` consecutive points of a vertical
arithmetic progression has on that progression a zero that is not a zero of `ξ`. -/
theorem exists_zero_expSum_not_xi_zero_on_progression (hn : 0 < n) (a : Fin n → ℂ)
    (lam : Fin n → ℝ) (s₀ : ℂ) {d : ℝ} (hd : 0 < d) (K : ℤ)
    (h : ∀ j : ℕ, j < n → expSum a lam (s₀ + (((K + 1 + j : ℤ) * d : ℝ) : ℂ) * I) = 0) :
    ∃ ν : ℤ, expSum a lam (s₀ + ((ν * d : ℝ) : ℂ) * I) = 0 ∧
      xi (s₀ + ((ν * d : ℝ) : ℂ) * I) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact not_forall_xi_progression s₀ hd fun k =>
    hcon k (expSum_eq_zero_on_progression hn a lam s₀ d K h k)

/-- **A constituent of `N` terms propagates progressions.** If the zeros of an exponential
polynomial of `N` terms in a set `B` are zeros of `ξ`, and it vanishes at `N` consecutive points
of a vertical progression, then `ξ` vanishes at every point of the progression in `B`. -/
theorem xi_eq_zero_on_progression_of_consecutive (hn : 0 < n) (a : Fin n → ℂ) (lam : Fin n → ℝ)
    (s₀ : ℂ) (d : ℝ) (K : ℤ)
    (h : ∀ j : ℕ, j < n → expSum a lam (s₀ + (((K + 1 + j : ℤ) * d : ℝ) : ℂ) * I) = 0)
    {B : Set ℂ} (hB : ∀ z ∈ B, expSum a lam z = 0 → xi z = 0) {ν : ℤ}
    (hν : s₀ + ((ν * d : ℝ) : ℂ) * I ∈ B) : xi (s₀ + ((ν * d : ℝ) : ℂ) * I) = 0 :=
  hB _ hν (expSum_eq_zero_on_progression hn a lam s₀ d K h ν)

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
