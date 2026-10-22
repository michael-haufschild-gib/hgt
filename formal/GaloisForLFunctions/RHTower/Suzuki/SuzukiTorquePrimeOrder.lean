import GaloisForLFunctions.RHTower.Suzuki.SuzukiTorqueArchLaplace

/-!
# `(17)`: continuity and exponential order of the visible prime layer

On any bounded interval only finitely many tents have been born, so the layer agrees there with a
finite sum of continuous functions — that is its continuity, and it is why no limit theorem is
needed.  Its size is bounded by the crudest possible estimates: `Λ(n) ≤ log n ≤ L`, `√n ≤ e^{L/2}`,
`sinh(log n) ≤ n/2 ≤ e^{L}/2`, and at most `e^{L}` terms.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- Below a fixed height the layer is a fixed finite sum. -/
theorem suzukiFreePrimePositionTorque_eq_finset {M L : ℝ} (h : L ≤ M) :
    suzukiFreePrimePositionTorque L
      = ∑ n ∈ Finset.Icc 2 ⌊Real.exp M⌋₊, suzukiTentTerm n L := by
  rw [suzukiFreePrimePositionTorque_eq_tsum]
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_Icc, not_and_or] at hn
  rcases hn with h1 | h1
  · have hn1 : n ≤ 1 := by omega
    have hcoef : suzukiTentCoeff n = 0 := by
      interval_cases n <;> simp [suzukiTentCoeff]
    rw [suzukiTentTerm, hcoef, zero_mul]
  · have hnf : ⌊Real.exp M⌋₊ < n := by omega
    have hexp : Real.exp M < (n : ℝ) := by
      have ha : Real.exp M < (⌊Real.exp M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp M)
      have hb : (⌊Real.exp M⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnf
      linarith
    refine suzukiTentTerm_eq_zero_of_lt ?_
    have hlt := Real.log_lt_log (Real.exp_pos M) hexp
    rw [Real.log_exp] at hlt
    linarith

/-- **The visible prime layer is continuous.** -/
theorem continuous_suzukiFreePrimePositionTorque :
    Continuous suzukiFreePrimePositionTorque := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hfin : Continuous fun L : ℝ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (x + 1)⌋₊,
      suzukiTentTerm n L := by
    refine continuous_finsetSum _ fun n _ => ?_
    have : Continuous fun L : ℝ => suzukiTentCoeff n * max (L - Real.log n) 0 :=
      continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const)
    exact this
  refine (hfin.continuousAt (x := x)).congr ?_
  filter_upwards [Iio_mem_nhds (by linarith : x < x + 1)] with L hL
  exact (suzukiFreePrimePositionTorque_eq_finset (le_of_lt hL)).symm

/-- **`(17)`: the layer's exponential order.** -/
theorem suzukiFreePrimePositionTorque_le {L : ℝ} (hL : 1 ≤ L) :
    suzukiFreePrimePositionTorque L ≤ 1 / 2 * L ^ (3 : ℕ) * Real.exp (3 * L / 2) := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hsqrtexp : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    have hmul : Real.exp (L / 2) * Real.exp (L / 2) = Real.exp L := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hmul, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hbound : ∀ n ∈ suzukiVisibleWeilIndices L,
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * Real.log n * (L - Real.log n)
          * Real.sinh (Real.log n)
        ≤ 1 / 2 * L ^ (3 : ℕ) * Real.exp (L / 2) := by
    intro n hn
    rw [suzukiVisibleWeilIndices, Finset.mem_Icc] at hn
    have hn2 : 2 ≤ n := hn.1
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hnf : (n : ℝ) ≤ Real.exp L := by
      have h1 : (n : ℝ) ≤ (⌊Real.exp L⌋₊ : ℝ) := by exact_mod_cast hn.2
      have h2 : (⌊Real.exp L⌋₊ : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
      linarith
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hlogL : Real.log n ≤ L := by
      have := Real.log_le_log hnpos hnf
      rwa [Real.log_exp] at this
    have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    have hΛ0 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hsqrtpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hsqrtsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnpos.le
    have hsqrtle : Real.sqrt n ≤ Real.exp (L / 2) := by
      rw [← hsqrtexp]
      exact Real.sqrt_le_sqrt hnf
    have hsinh : Real.sinh (Real.log n) ≤ (n : ℝ) / 2 := by
      rw [Real.sinh_eq, Real.exp_log hnpos]
      have hinv : (0 : ℝ) < Real.exp (-Real.log n) := Real.exp_pos _
      linarith
    have hsinhnn : (0 : ℝ) ≤ Real.sinh (Real.log n) := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr hlogn.le
    have hΛq : (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
        ≤ Real.log n / Real.sqrt n := by
      exact div_le_div_of_nonneg_right hΛ hsqrtpos.le
    have hqnn : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n := by positivity
    have hpair : (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * Real.sinh (Real.log n)
        ≤ (Real.log n / Real.sqrt n) * ((n : ℝ) / 2) :=
      mul_le_mul hΛq hsinh hsinhnn (by positivity)
    have hdiv : (n : ℝ) / Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) := by
      rw [eq_comm, eq_div_iff (ne_of_gt hsqrtpos)]
      exact hsqrtsq
    have hns : (Real.log n / Real.sqrt n) * ((n : ℝ) / 2)
        = Real.log n * Real.sqrt n / 2 := by
      rw [show (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) * ((n : ℝ) / 2)
          = Real.log (n : ℝ) * ((n : ℝ) / Real.sqrt (n : ℝ)) / 2 by ring, hdiv]
    have hfront : Real.log n * (L - Real.log n) ≤ L * L :=
      mul_le_mul hlogL (by linarith) (by linarith) (by linarith)
    have hfrontnn : (0 : ℝ) ≤ Real.log n * (L - Real.log n) :=
      mul_nonneg hlogn.le (by linarith)
    have hback : Real.log n * Real.sqrt n / 2 ≤ L * Real.exp (L / 2) / 2 := by
      have := mul_le_mul hlogL hsqrtle hsqrtpos.le (by linarith)
      linarith
    have hbacknn : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
        * Real.sinh (Real.log n) := mul_nonneg hqnn hsinhnn
    calc (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * Real.log n * (L - Real.log n)
          * Real.sinh (Real.log n)
        = (Real.log n * (L - Real.log n))
          * ((ArithmeticFunction.vonMangoldt n / Real.sqrt n) * Real.sinh (Real.log n)) := by
          ring
      _ ≤ (L * L) * (L * Real.exp (L / 2) / 2) := by
          refine mul_le_mul hfront ?_ hbacknn (by positivity)
          exact hpair.trans (le_of_eq hns) |>.trans hback
      _ = 1 / 2 * L ^ (3 : ℕ) * Real.exp (L / 2) := by ring
  have hsum := Finset.sum_le_card_nsmul _ _ _ hbound
  rw [suzukiFreePrimePositionTorque_eq]
  refine hsum.trans ?_
  have hcard : ((suzukiVisibleWeilIndices L).card : ℝ) ≤ Real.exp L := by
    have hc : (suzukiVisibleWeilIndices L).card ≤ ⌊Real.exp L⌋₊ := by
      rw [suzukiVisibleWeilIndices, Nat.card_Icc]
      omega
    have h1 : ((suzukiVisibleWeilIndices L).card : ℝ) ≤ (⌊Real.exp L⌋₊ : ℝ) := by
      exact_mod_cast hc
    have h2 : (⌊Real.exp L⌋₊ : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
    linarith
  rw [nsmul_eq_mul]
  have hpos : (0 : ℝ) ≤ 1 / 2 * L ^ (3 : ℕ) * Real.exp (L / 2) := by positivity
  have hexp : Real.exp L * (1 / 2 * L ^ (3 : ℕ) * Real.exp (L / 2))
      = 1 / 2 * L ^ (3 : ℕ) * Real.exp (3 * L / 2) := by
    rw [show Real.exp (3 * L / 2) = Real.exp L * Real.exp (L / 2) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  calc ((suzukiVisibleWeilIndices L).card : ℝ) * (1 / 2 * L ^ (3 : ℕ) * Real.exp (L / 2))
      ≤ Real.exp L * (1 / 2 * L ^ (3 : ℕ) * Real.exp (L / 2)) :=
        mul_le_mul_of_nonneg_right hcard hpos
    _ = 1 / 2 * L ^ (3 : ℕ) * Real.exp (3 * L / 2) := hexp

end RHTower
