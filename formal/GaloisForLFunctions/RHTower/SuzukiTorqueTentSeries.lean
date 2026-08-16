import GaloisForLFunctions.RHTower.SuzukiWeilPositionTorqueCurvature

/-!
# The prime tent sum as an infinite series

Suzuki's visible prime layer is a *finite* sum whose range grows with the aperture; written with the
positive part `(L − log n)⁺` it is an infinite series whose terms vanish before their birth point.
That rewriting is what lets the Laplace transform be taken term by term: each term is a single tent,
whose transform the corpus already computes, and every term is nonnegative.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- The weight Suzuki's finite-aperture kernel attaches to the `n`-th prime power. -/
def suzukiTentCoeff (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * Real.log n * Real.sinh (Real.log n)

/-- The `n`-th tent of the visible prime layer. -/
def suzukiTentTerm (n : ℕ) (L : ℝ) : ℝ := suzukiTentCoeff n * max (L - Real.log n) 0

theorem suzukiTentCoeff_nonneg (n : ℕ) : 0 ≤ suzukiTentCoeff n := by
  rw [suzukiTentCoeff]
  rcases le_or_gt (n : ℝ) 1 with hn | hn
  · rcases Nat.lt_or_ge n 1 with h | h
    · have : n = 0 := by omega
      subst this
      simp
    · have hn1 : n = 1 := by
        by_contra hne
        have : 2 ≤ n := by omega
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
        linarith
      subst hn1
      simp
  · have hlog : 0 < Real.log n := Real.log_pos hn
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hsinh : 0 ≤ Real.sinh (Real.log n) := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr hlog.le
    positivity

theorem suzukiTentTerm_nonneg (n : ℕ) (L : ℝ) : 0 ≤ suzukiTentTerm n L := by
  rw [suzukiTentTerm]
  exact mul_nonneg (suzukiTentCoeff_nonneg n) (le_max_right _ _)

/-- Past its birth point the tent has not yet opened. -/
theorem suzukiTentTerm_eq_zero_of_lt {n : ℕ} {L : ℝ} (h : L < Real.log n) :
    suzukiTentTerm n L = 0 := by
  rw [suzukiTentTerm, max_eq_right (by linarith), mul_zero]

/-- **The visible prime layer is the tent series.**  Only the tents already born contribute, and
those are exactly the indices of Suzuki's finite window. -/
theorem suzukiFreePrimePositionTorque_eq_tsum (L : ℝ) :
    suzukiFreePrimePositionTorque L = ∑' n : ℕ, suzukiTentTerm n L := by
  have hvanish : ∀ n : ℕ, n ∉ suzukiVisibleWeilIndices L → suzukiTentTerm n L = 0 := by
    intro n hn
    rw [suzukiVisibleWeilIndices, Finset.mem_Icc, not_and_or] at hn
    rcases hn with h | h
    · have hn1 : n ≤ 1 := by omega
      have : suzukiTentCoeff n = 0 := by
        interval_cases n <;> simp [suzukiTentCoeff]
      rw [suzukiTentTerm, this, zero_mul]
    · have hnf : ⌊Real.exp L⌋₊ < n := by omega
      have hexp : Real.exp L < (n : ℝ) := by
        have h1 : Real.exp L < (⌊Real.exp L⌋₊ : ℝ) + 1 :=
          Nat.lt_floor_add_one (Real.exp L)
        have h2 : (⌊Real.exp L⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnf
        linarith
      refine suzukiTentTerm_eq_zero_of_lt ?_
      have := Real.log_lt_log (Real.exp_pos L) hexp
      rwa [Real.log_exp] at this
  rw [tsum_eq_sum hvanish, suzukiFreePrimePositionTorque_eq]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [suzukiVisibleWeilIndices, Finset.mem_Icc] at hn
  have hnf : (n : ℝ) ≤ Real.exp L := by
    have h1 : (n : ℝ) ≤ (⌊Real.exp L⌋₊ : ℝ) := by exact_mod_cast hn.2
    have h2 : (⌊Real.exp L⌋₊ : ℝ) ≤ Real.exp L := by
      rcases Nat.eq_zero_or_pos ⌊Real.exp L⌋₊ with h | h
      · rw [h]
        simp [(Real.exp_pos L).le]
      · exact Nat.floor_le (Real.exp_pos L).le
    linarith
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℕ) ≤ n := hn.1
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have hlog : Real.log n ≤ L := by
    have := Real.log_le_log hn0 hnf
    rwa [Real.log_exp] at this
  rw [suzukiTentTerm, suzukiTentCoeff, max_eq_left (by linarith)]
  ring

end RHTower
