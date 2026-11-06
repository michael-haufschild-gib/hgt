import GaloisForLFunctions.ArithmeticInnerFunctionTheory.EchoTrainsOnIndependentReflectors
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# Amplitudes correlated with the height

In `S(a, b) = Σ_N τ_b(N) A(N; a, b)` the amplitude depends on the same `b` as the phases, so fixed-amplitude locking does not apply. This is the one place left for phase locking to act. Here is exactly how much room there is.

* **An amplitude with a limit at height infinity gains nothing** (`torusSum_nonneg_of_locked_of_tendsto`). If `A_b → A_∞` under a trace-summable majorant, and the locked sums are nonnegative at all large heights, then
  `A_∞` is torus-positive. Conversely a negative torus value of the limit gives negative locked sums at arbitrarily large heights (`exists_large_height_neg`).
* **Oscillating amplitudes can gain** (`exists_correlated_train`). With `A_b(0) = 1`, `A_b(1) = U₁(cos bℓ)`, the locked sum is `1 + U₁(cos bℓ)² ≥ 0` at every height, while the fixed amplitude `A_b` has a negative torus value at every height where `|cos bℓ| > ¼`.

So correlation produces positivity only through amplitudes that oscillate with the height to the end, at a rate tied to the phases. A proof through `S` must exhibit that oscillation in `A`.
-/

open Filter Topology Set Metric
open scoped Real

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CompletedArithmeticForms (cosSum)

noncomputable section

variable {n : ℕ}

/-- **Large recurrence.** Locked phases reach every point of the torus at arbitrarily large heights. -/
theorem exists_large_locked {ℓ : Fin n → ℝ} (hℓ : IsKroneckerFamily ℓ) (z : Fin n → Circle) {ε : ℝ}
    (hε : 0 < ε) (B : ℝ) : ∃ b : ℝ, B ≤ b ∧ dist (fun i => Circle.exp (b * ℓ i)) z < ε := by
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.mp (mem_closure_locked hℓ z) (ε / 2) (by positivity)
  obtain ⟨b₁, rfl⟩ := hy
  -- recurrence to the identity at a large height
  have hπ := Real.pi_pos
  obtain ⟨Q, hQ⟩ := exists_nat_gt (2 * (2 * π) / ε)
  have hQ0 : 0 < Q := by
    have : (0 : ℝ) < Q := lt_trans (by positivity) hQ
    exact_mod_cast this
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  set h : ℝ := max (B - b₁) 1 with hh
  have hh1 : 1 ≤ h := le_max_right _ _
  let β : Fin n → ℝ := fun i => h * ℓ i / (2 * π)
  obtain ⟨q, hq1, -, hclose⟩ := HTGeometry.exists_simultaneous_dirichlet β hQ0
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  refine ⟨b₁ + q * h, ?_, ?_⟩
  · have : B - b₁ ≤ h := le_max_left _ _
    nlinarith
  · have hbound : dist (fun i => Circle.exp ((b₁ + q * h) * ℓ i)) (fun i => Circle.exp (b₁ * ℓ i)) < ε / 2 := by
      rw [dist_pi_lt_iff (by positivity)]
      intro i
      obtain ⟨k, hk⟩ := hclose i
      set y : ℝ := (q : ℝ) * β i - k with hy
      have hrot : (q * h) * ℓ i = 2 * π * y + k * (2 * π) := by
        simp only [hy, β]
        field_simp
        ring
      have e : Circle.exp ((b₁ + q * h) * ℓ i) = Circle.exp (b₁ * ℓ i) * Circle.exp (2 * π * y) := by
        have e1 : (b₁ + q * h) * ℓ i = b₁ * ℓ i + (2 * π * y + k * (2 * π)) := by
          rw [← hrot]
          ring
        rw [e1, Circle.exp_add, Circle.exp_add]
        have e2 : Circle.exp (k * (2 * π)) = 1 := by
          have := Circle.exp_two_pi
          rw [show (k : ℝ) * (2 * π) = (k : ℝ) • (2 * π) by simp]
          exact (Circle.periodic_exp.int_mul k 0).trans Circle.exp_zero |> fun h' => by
            simpa using h'
        rw [e2, mul_one]
      rw [e]
      change dist ((Circle.exp (b₁ * ℓ i) * Circle.exp (2 * π * y) : Circle) : ℂ)
        ((Circle.exp (b₁ * ℓ i) : Circle) : ℂ) < ε / 2
      rw [Circle.coe_mul, dist_eq_norm, ← mul_sub_one, norm_mul, Circle.norm_coe, one_mul, Circle.coe_exp]
      have hle := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * y)
      rw [Complex.norm_real, Real.norm_eq_abs] at hle
      have e3 : ((2 * π * y : ℝ) : ℂ) * Complex.I = Complex.I * ((2 * π * y : ℝ) : ℂ) := mul_comm _ _
      rw [e3]
      refine lt_of_le_of_lt hle ?_
      have hk2 : |y| < 1 / ((Q : ℕ) : ℝ) := hk
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have h4 : 2 * (2 * π) < ε * Q := by
        rw [div_lt_iff₀ hε] at hQ
        linarith
      have h5 : 2 * π * |y| < 2 * π * (1 / (Q : ℝ)) := mul_lt_mul_of_pos_left hk2 (by positivity)
      have h6 : 2 * π * (1 / (Q : ℝ)) < ε / 2 := by
        rw [mul_one_div, div_lt_iff₀ hQr]
        linarith
      linarith
    have hd2 : dist (fun i => Circle.exp (b₁ * ℓ i)) z < ε / 2 := by
      have := hd
      rwa [dist_comm] at this
    calc _ ≤ dist (fun i => Circle.exp ((b₁ + q * h) * ℓ i)) (fun i => Circle.exp (b₁ * ℓ i)) +
          dist (fun i => Circle.exp (b₁ * ℓ i)) z := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hbound hd2
      _ = ε := by ring

/-- **An amplitude with a limit at height infinity gains nothing from locking.** -/
theorem torusSum_nonneg_of_locked_of_tendsto {A : ℝ → (Fin n → ℕ) → ℝ} {a M : (Fin n → ℕ) → ℝ}
    (hM : Summable fun k => M k * chiSize k) (hbd : ∀ b k, |A b k| ≤ M k)
    (hlim : ∀ k, Tendsto (fun b => A b k) atTop (𝓝 (a k))) {ℓ : Fin n → ℝ} (hℓ : IsKroneckerFamily ℓ)
    {b₀ : ℝ} (hpos : ∀ b, b₀ ≤ b → 0 ≤ torusSum (A b) fun i => b * ℓ i) (θ : Fin n → ℝ) :
    0 ≤ torusSum a θ := by
  set z : Fin n → Circle := fun i => Circle.exp (θ i) with hz
  -- heights tending to infinity whose phases tend to `θ`
  choose b hb1 hb2 using fun j : ℕ => exists_large_locked hℓ z
    (ε := 1 / ((j : ℝ) + 1)) (by positivity) (max b₀ j)
  have hbt : Tendsto b atTop atTop :=
    tendsto_atTop_mono (fun j => (le_max_right _ _).trans (hb1 j)) tendsto_natCast_atTop_atTop
  have hzt : Tendsto (fun j => (fun i => Circle.exp (b j * ℓ i) : Fin n → Circle)) atTop (𝓝 z) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun j => (hb2 j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hval : Tendsto (fun j => torusSum (A (b j)) fun i => b j * ℓ i) atTop (𝓝 (torusSum a θ)) := by
    have hrw : ∀ j, torusSum (A (b j)) (fun i => b j * ℓ i) =
        ∑' k, A (b j) k * ∏ i, chiCircle (k i) (Circle.exp (b j * ℓ i)) := fun j =>
      (torusSumCircle_exp (A (b j)) _).symm
    have hrw2 : torusSum a θ = ∑' k, a k * ∏ i, chiCircle (k i) (z i) :=
      (torusSumCircle_exp a θ).symm
    simp only [hrw]
    rw [hrw2]
    refine tendsto_tsum_of_dominated_convergence hM (fun k => ?_) (Eventually.of_forall fun j k => ?_)
    · refine ((hlim k).comp hbt).mul ?_
      refine tendsto_finset_prod _ fun i _ => ?_
      exact (continuous_chiCircle (k i)).continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hzt) i)
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Finset.abs_prod]
      refine mul_le_mul (hbd _ k) ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        ((abs_nonneg _).trans (hbd 0 k))
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => abs_chiCircle_le _ _
  exact ge_of_tendsto' hval fun j => hpos _ ((le_max_left _ _).trans (hb1 j))

/-- **A negative torus value of the limit amplitude is reached at arbitrarily large locked heights.** -/
theorem exists_large_height_neg {A : ℝ → (Fin n → ℕ) → ℝ} {a M : (Fin n → ℕ) → ℝ}
    (hM : Summable fun k => M k * chiSize k) (hbd : ∀ b k, |A b k| ≤ M k)
    (hlim : ∀ k, Tendsto (fun b => A b k) atTop (𝓝 (a k))) {ℓ : Fin n → ℝ} (hℓ : IsKroneckerFamily ℓ)
    {θ : Fin n → ℝ} (hneg : torusSum a θ < 0) (b₀ : ℝ) :
    ∃ b, b₀ ≤ b ∧ torusSum (A b) (fun i => b * ℓ i) < 0 := by
  by_contra hcon
  push Not at hcon
  exact absurd (torusSum_nonneg_of_locked_of_tendsto hM hbd hlim hℓ hcon θ) (not_le.mpr hneg)

/-- The two-term amplitude on one column: `1 + c χ₁`. -/
def twoTerm (c : ℝ) (k : Fin 1 → ℕ) : ℝ := if k 0 = 0 then 1 else if k 0 = 1 then c else 0

/-- The torus sum of the two-term amplitude. -/
theorem torusSum_twoTerm (c : ℝ) (θ : Fin 1 → ℝ) : torusSum (twoTerm c) θ = 1 + c * (2 * Real.cos (θ 0)) := by
  classical
  have hsupp : ∀ k ∉ ({(fun _ => 0), (fun _ => 1)} : Finset (Fin 1 → ℕ)), twoTerm c k * chiProd θ k = 0 := by
    intro k hk
    have h0 : k 0 ≠ 0 := fun h => hk (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      funext i
      rw [Subsingleton.elim i 0, h])
    have h1 : k 0 ≠ 1 := fun h => hk (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      funext i
      rw [Subsingleton.elim i 0, h])
    simp [twoTerm, h0, h1]
  rw [torusSum, tsum_eq_sum hsupp, Finset.sum_pair (by
    intro h
    have := congrFun h 0
    simp at this)]
  simp only [twoTerm, chiProd, Fin.prod_univ_one]
  have hc0 : cosSum (θ 0) 0 = 1 := by simp [cosSum]
  have hc1 : cosSum (θ 0) 1 = 2 * Real.cos (θ 0) := by
    simp only [cosSum, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Real.cos_neg]
    ring
  simp [hc0, hc1]

/-- **Oscillating amplitudes can gain.** On one column, an amplitude tied to the height has a nonnegative locked sum at every height, and at every height with
`|cos bℓ| > ¼` it has a negative torus value. -/
theorem exists_correlated_train (ℓ : ℝ) :
    ∃ A : ℝ → (Fin 1 → ℕ) → ℝ, (∀ b, 0 ≤ torusSum (A b) fun _ => b * ℓ) ∧
      ∀ b : ℝ, 1 / 4 < |Real.cos (b * ℓ)| → ∃ θ, torusSum (A b) θ < 0 := by
  refine ⟨fun b => twoTerm (2 * Real.cos (b * ℓ)), fun b => ?_, fun b hb => ?_⟩
  · rw [torusSum_twoTerm]
    nlinarith [sq_nonneg (Real.cos (b * ℓ))]
  · refine ⟨fun _ => if 0 ≤ Real.cos (b * ℓ) then π else 0, ?_⟩
    rw [torusSum_twoTerm]
    by_cases h : 0 ≤ Real.cos (b * ℓ)
    · simp only [h, if_true, Real.cos_pi]
      rw [abs_of_nonneg h] at hb
      nlinarith
    · simp only [h, if_false, Real.cos_zero]
      have h' := not_le.mp h
      rw [abs_of_neg h'] at hb
      nlinarith

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
