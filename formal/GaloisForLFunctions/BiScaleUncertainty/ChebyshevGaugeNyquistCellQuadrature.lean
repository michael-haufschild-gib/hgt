import GaloisForLFunctions.BiScaleUncertainty.HyperbolicGaugeChebyshevEnergyRepresentation

/-!
# Nyquist-cell quadrature of the Chebyshev gauge energy

On the Nyquist cell `[log n, log(n+1))` the Chebyshev function `ψ(e^t)` is the constant `ψ(n)`, so the
normalized Chebyshev error `Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)` has the explicit cell energy

`∫_{log n}^{log(n+1)} Ẽ(t)² dt = ψ(n)²/(n(n+1)) − 2 ψ(n) log((n+1)/n) + 1`.

Completing the square gives the exact cell law

`∫_{log n}^{log(n+1)} Ẽ² = (ψ(n) − m_n)²/(n(n+1)) + c_n`,
`m_n = n(n+1) log((n+1)/n) ∈ [n, n+1]`,  `c_n = 1 − n(n+1) log²((n+1)/n) ∈ [0, 2/(n(n+1))]`,

where `c_n = ∫_{log n}^{log(n+1)} e^{−t}(m_n − e^t)² dt` is the energy of the optimally centred cell.
Summing over the cells `1 ≤ n < M`,

`Σ_{n<M} (ψ(n) − m_n)²/(n(n+1)) ≤ ∫_0^{log M} Ẽ(t)² dt ≤ Σ_{n<M} (ψ(n) − m_n)²/(n(n+1)) + 2`.

Thus the mean-square normalized Chebyshev error, which controls the signed prime–polar packet energy of
every compact `C¹` source, is a discrete weighted mean square of the centred Chebyshev values `ψ(n) − m_n`
with the critical-line weights `1/(n(n+1))`, up to a universal constant.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

/-- The cell length `log((n+1)/n)`. -/
def cellLength (n : ℕ) : ℝ := Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)

/-- The optimal cell centre `m_n = n(n+1) log((n+1)/n)`. -/
def cellCenter (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + 1) * cellLength n

/-- The centred cell energy `c_n = 1 − n(n+1) log²((n+1)/n)`. -/
def cellFloor (n : ℕ) : ℝ := 1 - (n : ℝ) * ((n : ℝ) + 1) * cellLength n ^ 2

theorem cellLength_eq {n : ℕ} (hn : 1 ≤ n) :
    cellLength n = Real.log (1 + 1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cellLength
  rw [← Real.log_div (by positivity) hn0.ne']
  congr 1
  field_simp

theorem cellLength_le {n : ℕ} (hn : 1 ≤ n) : cellLength n ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cellLength_eq hn]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / n by positivity)
  linarith

theorem inv_succ_le_cellLength {n : ℕ} (hn : 1 ≤ n) : 1 / ((n : ℝ) + 1) ≤ cellLength n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cellLength_eq hn]
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 1 / n by positivity)
  have : 1 - (1 + 1 / (n : ℝ))⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
  linarith

theorem cellLength_pos {n : ℕ} (hn : 1 ≤ n) : 0 < cellLength n :=
  lt_of_lt_of_le (by positivity) (inv_succ_le_cellLength hn)

theorem le_cellCenter {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) ≤ cellCenter n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cellCenter
  have h := inv_succ_le_cellLength hn
  calc (n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by field_simp
    _ ≤ (n : ℝ) * ((n : ℝ) + 1) * cellLength n :=
        mul_le_mul_of_nonneg_left h (by positivity)

theorem cellCenter_le {n : ℕ} (hn : 1 ≤ n) : cellCenter n ≤ (n : ℝ) + 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cellCenter
  have h := cellLength_le hn
  calc (n : ℝ) * ((n : ℝ) + 1) * cellLength n ≤ (n : ℝ) * ((n : ℝ) + 1) * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (n : ℝ) + 1 := by field_simp

/-! ## The cell integral of the gauge square -/

/-- The gauge square of a constant over a Nyquist cell:
`∫_{log n}^{log(n+1)} e^{−t}(c − e^t)² dt = c²/(n(n+1)) − 2c log((n+1)/n) + 1`. -/
theorem integral_cell_gauge_sq (c : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), Real.exp (-t) * (c - Real.exp t) ^ 2) =
      c ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) - 2 * c * cellLength n + 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : ∀ t : ℝ, HasDerivAt (fun t => -c ^ 2 * Real.exp (-t) - 2 * c * t + Real.exp t)
      (Real.exp (-t) * (c - Real.exp t) ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -c ^ 2 * Real.exp (-t)) (-c ^ 2 * (Real.exp (-t) * (-1))) t :=
      ((hasDerivAt_neg t).exp).const_mul (-c ^ 2)
    have h2 : HasDerivAt (fun t : ℝ => 2 * c * t) (2 * c) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * c)
    have h3 := (h1.sub h2).add (Real.hasDerivAt_exp t)
    refine h3.congr_deriv ?_
    have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    have h2' : Real.exp (-t) * Real.exp t ^ 2 = Real.exp t := by
      rw [sq, ← mul_assoc, he, one_mul]
    linear_combination (2 * c) * he - h2'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (((Real.continuous_exp.comp continuous_neg).mul
      ((continuous_const.sub Real.continuous_exp).pow 2)).intervalIntegrable _ _)]
  rw [Real.exp_neg, Real.exp_neg, Real.exp_log hn0, Real.exp_log (by positivity)]
  unfold cellLength
  field_simp
  ring

/-- `⌊e^t⌋₊ = n` on the Nyquist cell `[log n, log(n+1))`. -/
theorem floor_exp_eq_of_mem_cell {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht : t ∈ Ico (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) : ⌊Real.exp t⌋₊ = n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.floor_eq_iff (Real.exp_pos t).le]
  constructor
  · calc (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hn0).symm
      _ ≤ Real.exp t := Real.exp_le_exp.2 ht.1
  · calc Real.exp t < Real.exp (Real.log ((n : ℝ) + 1)) := Real.exp_lt_exp.2 ht.2
      _ = (n : ℝ) + 1 := Real.exp_log (by positivity)

/-- On the Nyquist cell the normalized error square is `e^{−t}(ψ(n) − e^t)²`. -/
theorem normalizedLogError_sq_eq_on_cell {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht : t ∈ Ico (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) :
    normalizedLogError t ^ 2 = Real.exp (-t) * (Chebyshev.psi (n : ℝ) - Real.exp t) ^ 2 := by
  unfold normalizedLogError SignedPrimePolar.logError
  rw [Chebyshev.psi_eq_psi_coe_floor (Real.exp t), floor_exp_eq_of_mem_cell hn ht]
  have he : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [mul_pow, he]

/-- **Cell energy of the normalized Chebyshev error.** -/
theorem integral_cell_normalizedLogError_sq {n : ℕ} (hn : 1 ≤ n) :
    (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), normalizedLogError t ^ 2) =
      Chebyshev.psi (n : ℝ) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) -
        2 * Chebyshev.psi (n : ℝ) * cellLength n + 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
  rw [← integral_cell_gauge_sq (Chebyshev.psi (n : ℝ)) hn]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ Real.log ((n : ℝ) + 1) := by
    rw [ae_iff]; simp
  filter_upwards [hne] with t ht hmem
  rw [uIoc_of_le hle] at hmem
  exact normalizedLogError_sq_eq_on_cell hn ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ht⟩

/-! ## Completing the square: centre and floor -/

/-- The exact completed square of the cell energy. -/
theorem cell_energy_eq_center_sq_add_floor (ψ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ψ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) - 2 * ψ * cellLength n + 1 =
      (ψ - cellCenter n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) + cellFloor n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cellCenter cellFloor
  field_simp
  ring

/-- The floor is the energy of the optimally centred cell. -/
theorem cellFloor_eq_integral {n : ℕ} (hn : 1 ≤ n) :
    cellFloor n = ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
      Real.exp (-t) * (cellCenter n - Real.exp t) ^ 2 := by
  rw [integral_cell_gauge_sq (cellCenter n) hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cellCenter cellFloor
  field_simp
  ring

theorem cellFloor_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ cellFloor n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cellFloor_eq_integral hn]
  exact intervalIntegral.integral_nonneg (Real.log_le_log hn0 (by linarith))
    fun t _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- `c_n ≤ 2/(n(n+1))`: the centred cell energy is summable with total at most `2`. -/
theorem cellFloor_le {n : ℕ} (hn : 1 ≤ n) : cellFloor n ≤ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
  rw [cellFloor_eq_integral hn]
  -- the integrand is at most `1/n` on the cell
  have hbound : ∀ t ∈ Icc (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1)),
      Real.exp (-t) * (cellCenter n - Real.exp t) ^ 2 ≤ 1 / (n : ℝ) := by
    intro t ht
    have h1 : (n : ℝ) ≤ Real.exp t := by
      calc (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hn0).symm
        _ ≤ Real.exp t := Real.exp_le_exp.2 ht.1
    have h2 : Real.exp t ≤ (n : ℝ) + 1 := by
      calc Real.exp t ≤ Real.exp (Real.log ((n : ℝ) + 1)) := Real.exp_le_exp.2 ht.2
        _ = (n : ℝ) + 1 := Real.exp_log (by positivity)
    have hc1 := le_cellCenter hn
    have hc2 := cellCenter_le hn
    have hsq : (cellCenter n - Real.exp t) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]; constructor <;> linarith
    have hexp : Real.exp (-t) ≤ 1 / (n : ℝ) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le hn0 h1
    calc Real.exp (-t) * (cellCenter n - Real.exp t) ^ 2 ≤ Real.exp (-t) * 1 :=
          mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = Real.exp (-t) := mul_one _
      _ ≤ 1 / (n : ℝ) := hexp
  have hint : (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
      Real.exp (-t) * (cellCenter n - Real.exp t) ^ 2) ≤
      ∫ _t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (1 / (n : ℝ)) :=
    intervalIntegral.integral_mono_on hle
      (((Real.continuous_exp.comp continuous_neg).mul
        ((continuous_const.sub Real.continuous_exp).pow 2)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hlen : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := cellLength_le hn
  calc _ ≤ (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) * (1 / (n : ℝ)) := hint
    _ ≤ (1 / (n : ℝ)) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_right hlen (by positivity)
    _ ≤ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hn1]

/-! ## Summation over the cells -/

/-- The normalized error square is bounded on every bounded interval, hence interval integrable. -/
theorem intervalIntegrable_normalizedLogError_sq (a b : ℝ) :
    IntervalIntegrable (fun t => normalizedLogError t ^ 2) volume a b := by
  have hm : Measurable fun t => normalizedLogError t ^ 2 :=
    measurable_normalizedLogError.pow_const 2
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ t ∈ Set.uIoc a b, normalizedLogError t ^ 2 ≤ B := by
    set m := max |a| |b| with hm
    refine ⟨(Real.exp (m / 2) * (Chebyshev.psi (Real.exp m) + Real.exp m)) ^ 2, fun t ht => ?_⟩
    have htm : |t| ≤ m := by
      rw [abs_le]
      constructor
      · have h1 : min a b ≤ t := ht.1.le
        have h2 : -m ≤ min a b := by
          rcases min_choice a b with h | h <;> rw [h]
          · linarith [neg_abs_le a, le_max_left |a| |b|]
          · linarith [neg_abs_le b, le_max_right |a| |b|]
        linarith
      · have h1 : t ≤ max a b := ht.2
        have h2 : max a b ≤ m := by
          rcases max_choice a b with h | h <;> rw [h]
          · exact (le_abs_self a).trans (le_max_left _ _)
          · exact (le_abs_self b).trans (le_max_right _ _)
        linarith
    have htle : t ≤ m := (le_abs_self t).trans htm
    have hneg : -t ≤ m := (neg_le_abs t).trans htm
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    unfold normalizedLogError
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hE := abs_logError_le (le_refl t)
    have hψ : Chebyshev.psi (Real.exp t) ≤ Chebyshev.psi (Real.exp m) :=
      Chebyshev.psi_mono (Real.exp_le_exp.2 htle)
    have hexp : Real.exp t ≤ Real.exp m := Real.exp_le_exp.2 htle
    have hexp2 : Real.exp (-t / 2) ≤ Real.exp (m / 2) := Real.exp_le_exp.2 (by linarith)
    have hpos : 0 ≤ Chebyshev.psi (Real.exp t) + Real.exp t :=
      add_nonneg (Chebyshev.psi_nonneg _) (Real.exp_pos _).le
    calc Real.exp (-t / 2) * |SignedPrimePolar.logError t|
        ≤ Real.exp (m / 2) * (Chebyshev.psi (Real.exp t) + Real.exp t) :=
          mul_le_mul hexp2 hE (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (m / 2) * (Chebyshev.psi (Real.exp m) + Real.exp m) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  refine IntervalIntegrable.mono_fun' (g := fun _ => B) (intervalIntegrable_const)
    hm.aestronglyMeasurable ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hB t ht

/-- **Cell-sum quadrature of the Chebyshev gauge energy.**  For an integer `M ≥ 1`,
`∫_0^{log M} Ẽ² = Σ_{k < M−1} [ψ(k+1)²/((k+1)(k+2)) − 2 ψ(k+1) log((k+2)/(k+1)) + 1]`. -/
theorem integral_normalizedLogError_sq_eq_sum_cells {M : ℕ} (hM : 1 ≤ M) :
    (∫ t in Icc 0 (Real.log (M : ℝ)), normalizedLogError t ^ 2) =
      ∑ k ∈ Finset.range (M - 1),
        (Chebyshev.psi ((k + 1 : ℕ) : ℝ) ^ 2 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) -
          2 * Chebyshev.psi ((k + 1 : ℕ) : ℝ) * cellLength (k + 1) + 1) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hL0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t => normalizedLogError t ^ 2) (μ := volume)
    (a := fun k : ℕ => Real.log ((k : ℝ) + 1)) (n := M - 1)
    (fun k _ => intervalIntegrable_normalizedLogError_sq _ _)
  have ha0 : Real.log ((0 : ℕ) + 1 : ℝ) = 0 := by simp
  have haM : Real.log (((M - 1 : ℕ) : ℝ) + 1) = Real.log (M : ℝ) := by
    congr 1
    have : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM, Nat.cast_one]
    rw [this]; ring
  rw [ha0, haM] at hsum
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL0, ← hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [← integral_cell_normalizedLogError_sq hk, hcast]

/-- **Centred cell-sum law.** -/
theorem integral_normalizedLogError_sq_eq_sum_center_add_floor {M : ℕ} (hM : 1 ≤ M) :
    (∫ t in Icc 0 (Real.log (M : ℝ)), normalizedLogError t ^ 2) =
      (∑ k ∈ Finset.range (M - 1),
        (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) +
      ∑ k ∈ Finset.range (M - 1), cellFloor (k + 1) := by
  rw [integral_normalizedLogError_sq_eq_sum_cells hM, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact cell_energy_eq_center_sq_add_floor _ (Nat.succ_le_succ (Nat.zero_le k))

/-- The total centred-cell energy is at most `2`. -/
theorem sum_cellFloor_le_two (M : ℕ) : (∑ k ∈ Finset.range M, cellFloor (k + 1)) ≤ 2 := by
  have h1 : ∀ k ∈ Finset.range M, cellFloor (k + 1) ≤
      2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
    intro k _
    have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    refine (cellFloor_le hk).trans (le_of_eq ?_)
    push_cast
    field_simp
    ring
  calc (∑ k ∈ Finset.range M, cellFloor (k + 1))
      ≤ ∑ k ∈ Finset.range M, 2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) :=
        Finset.sum_le_sum h1
    _ = 2 * (1 - 1 / ((M : ℝ) + 1)) := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + 1)) M
        simp only [Nat.cast_succ] at this
        rw [show (∑ k ∈ Finset.range M, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))) =
          ∑ k ∈ Finset.range M, (1 / ((k : ℝ) + 1) - 1 / (((k : ℝ) + 1) + 1)) from
          Finset.sum_congr rfl fun k _ => by ring_nf, this]
        simp
    _ ≤ 2 := by
        have : 0 ≤ 1 / ((M : ℝ) + 1) := by positivity
        linarith

/-- **Two-sided discrete form of the Chebyshev gauge energy:**
`Σ_{n<M} (ψ(n) − m_n)²/(n(n+1)) ≤ ∫_0^{log M} Ẽ² ≤ Σ_{n<M} (ψ(n) − m_n)²/(n(n+1)) + 2`. -/
theorem sum_center_sq_le_integral_le {M : ℕ} (hM : 1 ≤ M) :
    (∑ k ∈ Finset.range (M - 1),
        (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) ≤
      (∫ t in Icc 0 (Real.log (M : ℝ)), normalizedLogError t ^ 2) ∧
    (∫ t in Icc 0 (Real.log (M : ℝ)), normalizedLogError t ^ 2) ≤
      (∑ k ∈ Finset.range (M - 1),
        (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) + 2 := by
  rw [integral_normalizedLogError_sq_eq_sum_center_add_floor hM]
  constructor
  · have : 0 ≤ ∑ k ∈ Finset.range (M - 1), cellFloor (k + 1) :=
      Finset.sum_nonneg fun k _ => cellFloor_nonneg (Nat.succ_le_succ (Nat.zero_le k))
    linarith
  · have := sum_cellFloor_le_two (M - 1)
    linarith

/-! ## Dyadic-window law and comparison with the classical discrete mean square -/

/-- **Dyadic-window law.**  The gauge energy on the Nyquist window `[log N, log 2N]` is the cell sum
over the `N` cells `[log(N+k), log(N+k+1))`. -/
theorem integral_window_normalizedLogError_sq_eq {N : ℕ} (hN : 1 ≤ N) :
    (∫ t in Real.log (N : ℝ)..Real.log ((2 * N : ℕ) : ℝ), normalizedLogError t ^ 2) =
      ∑ k ∈ Finset.range N,
        ((Chebyshev.psi ((N + k : ℕ) : ℝ) - cellCenter (N + k)) ^ 2 /
          (((N + k : ℕ) : ℝ) * (((N + k : ℕ) : ℝ) + 1)) + cellFloor (N + k)) := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t => normalizedLogError t ^ 2) (μ := volume)
    (a := fun k : ℕ => Real.log (((N + k : ℕ) : ℝ))) (n := N)
    (fun k _ => intervalIntegrable_normalizedLogError_sq _ _)
  simp only [Nat.add_zero] at hsum
  rw [show ((N + N : ℕ) : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; ring] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : 1 ≤ N + k := le_add_right hN
  rw [← cell_energy_eq_center_sq_add_floor _ hk, ← integral_cell_normalizedLogError_sq hk]
  congr 2
  push_cast; ring

/-- The centre lies within one of the integer `n`. -/
theorem abs_cellCenter_sub_le {n : ℕ} (hn : 1 ≤ n) : |cellCenter n - n| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [le_cellCenter hn, cellCenter_le hn]

/-- **Comparison with the classical discrete Chebyshev mean square.**  With `E(n) = ψ(n) − n`,
`½ Σ_{n<M} E(n)²/(n(n+1)) − 1 ≤ ∫_0^{log M} Ẽ² ≤ 2 Σ_{n<M} E(n)²/(n(n+1)) + 4`. -/
theorem chebyshev_discrete_mean_square_comparison {M : ℕ} (hM : 1 ≤ M) :
    (1 / 2) * (∑ k ∈ Finset.range (M - 1),
        (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) - 1 ≤
      (∫ t in Icc 0 (Real.log (M : ℝ)), normalizedLogError t ^ 2) ∧
    (∫ t in Icc 0 (Real.log (M : ℝ)), normalizedLogError t ^ 2) ≤
      2 * (∑ k ∈ Finset.range (M - 1),
        (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) + 4 := by
  obtain ⟨hlow, hup⟩ := sum_center_sq_le_integral_le hM
  -- the telescoping weight sum `Σ 1/(n(n+1)) ≤ 1`
  have hweight : (∑ k ∈ Finset.range (M - 1),
      1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) ≤ 1 := by
    have h := Finset.sum_range_sub' (fun k : ℕ => 1 / ((k : ℝ) + 1)) (M - 1)
    have hterm : ∀ k ∈ Finset.range (M - 1),
        1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) =
          1 / ((k : ℝ) + 1) - 1 / (((k + 1 : ℕ) : ℝ) + 1) := by
      intro k _
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, h]
    simp only [Nat.cast_zero, zero_add, div_one]
    have : 0 ≤ 1 / (((M - 1 : ℕ) : ℝ) + 1) := by positivity
    linarith
  -- pointwise comparison of the centred and classical squares
  have hpt : ∀ k ∈ Finset.range (M - 1),
      (1 / 2) * ((Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) -
        1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) ≤
      (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) ∧
      (Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) ≤
      2 * ((Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) ^ 2 /
          (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) +
        2 * (1 / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1))) := by
    intro k _
    have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hd : 0 < ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) := by positivity
    have hc := abs_cellCenter_sub_le hk
    set E := Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) with hE
    set d := cellCenter (k + 1) - ((k + 1 : ℕ) : ℝ) with hd'
    have hdec : Chebyshev.psi ((k + 1 : ℕ) : ℝ) - cellCenter (k + 1) = E - d := by
      rw [hE, hd']; ring
    rw [hdec]
    have hd1 : d ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]; exact hc
    set D := ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) + 1) with hD
    constructor
    · have key : E ^ 2 / 2 - 1 ≤ (E - d) ^ 2 := by nlinarith [sq_nonneg (E - 2 * d), hd1]
      calc (1 / 2) * (E ^ 2 / D) - 1 / D = (E ^ 2 / 2 - 1) / D := by ring
        _ ≤ (E - d) ^ 2 / D := div_le_div_of_nonneg_right key hd.le
    · have key : (E - d) ^ 2 ≤ 2 * E ^ 2 + 2 := by nlinarith [sq_nonneg (E + d), hd1]
      calc (E - d) ^ 2 / D ≤ (2 * E ^ 2 + 2) / D := div_le_div_of_nonneg_right key hd.le
        _ = 2 * (E ^ 2 / D) + 2 * (1 / D) := by ring
  have hsumlow := Finset.sum_le_sum fun k hk => (hpt k hk).1
  have hsumup := Finset.sum_le_sum fun k hk => (hpt k hk).2
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsumlow
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsumup
  constructor
  · linarith
  · linarith

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
