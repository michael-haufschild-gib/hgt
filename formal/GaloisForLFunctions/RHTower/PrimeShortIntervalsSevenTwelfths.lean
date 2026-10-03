import GaloisForLFunctions.RHTower.PrimeShortIntervalsTwentyThirtyThirds
import GaloisForLFunctions.RHTower.PrimeDeletionTwentySixThirtyThirds
import GaloisForLFunctions.RHTower.ZetaZeroDensityTwelveFifths

/-!
# Huxley's prime-gap theorem: primes in every interval `(x, x + x^α]`, `α > 7/12`

The zero-density exponent `12/5 + ε` (`exists_zeroHeightBox_ncard_le_twelve_fifths`) makes the
weighted zero sum vanish for every `u < 5/12`: with `ε = min(1, (1/u - 12/5)/2)` one has
`u(12/5 + ε) ≤ (1 + 12u/5)/2 < 1`.  The ψ/θ window steps of `PrimeShortIntervalsTwentyThirtyThirds`
then give, for every `7/12 < α < 1`,

`θ(y + L) - θ(y) ≥ (L - (y + L)^α)/2`   (`y ≥ X`, `L ≥ 0`),

a prime in `(x, x + x^α]` for all large `x`, and the greedy prime-deletion half-dimension
uncertainty for every `κ ∈ (1/2, 5/6)` (`α = 19/24 - κ/4`).
-/

noncomputable section

namespace RHTower

open Filter Topology RHTower.Sieve

/-- **The weighted zero sum vanishes below the exponent `5/12`.** -/
theorem tendsto_tsum_zeroShortWeight_seven_twelfths {u c : ℝ} (hu : 0 < u) (hu' : u < 5 / 12)
    (hc : 1 ≤ c) :
    Tendsto (fun x : ℝ => ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ))
      atTop (𝓝 0) := by
  set ε : ℝ := min 1 ((1 / u - 12 / 5) / 2) with hε
  have hgap : 0 < 1 / u - 12 / 5 := by
    rw [sub_pos, lt_div_iff₀ hu]
    linarith
  have hε0 : 0 < ε := lt_min one_pos (by linarith)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεle : ε ≤ (1 / u - 12 / 5) / 2 := min_le_right _ _
  obtain ⟨D, hD, T₀, -, hdens⟩ := exists_zeroHeightBox_ncard_le_twelve_fifths hε0 hε1
  have huA : u * (12 / 5 + ε) < 1 := by
    have h1 : u * (12 / 5 + ε) ≤ u * (12 / 5 + (1 / u - 12 / 5) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hu.le
    have h2 : u * (12 / 5 + (1 / u - 12 / 5) / 2) = (1 + 12 * u / 5) / 2 := by
      field_simp
      ring
    linarith
  exact tendsto_tsum_zeroShortWeight_of_density (by positivity) (by linarith) hu (by linarith)
    huA hc hD hdens

/-- **Prime mass in every short window, exponent `7/12`.**  For every `7/12 < α < 1` there is
`X ≥ 1` with `θ(y + L) - θ(y) ≥ (L - (y + L)^α)/2` for all `y ≥ X` and `L ≥ 0`. -/
theorem exists_theta_window_lower_seven_twelfths {α : ℝ} (hα : 7 / 12 < α) (hα1 : α < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 2 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y := by
  have hzero := tendsto_tsum_zeroShortWeight_seven_twelfths (u := 1 - α) (c := 512)
    (by linarith) (by linarith) (by norm_num)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1
    (eventually_theta_short_window_of_tendsto (by linarith) hα1 hzero)
  refine ⟨max X₀ 1, le_max_right _ _, ?_⟩
  exact theta_window_lower_of_step (by linarith) (by norm_num) (le_max_right _ _)
    (fun z hz => hX₀ z (le_trans (le_max_left _ _) hz))

/-- **Huxley's prime-gap theorem.**  For every `7/12 < α < 1`, every large `x` has a prime in
`(x, x + x^α]`. -/
theorem eventually_exists_prime_short_interval_seven_twelfths {α : ℝ} (hα : 7 / 12 < α)
    (hα1 : α < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ α := by
  set α' : ℝ := (7 / 12 + α) / 2 with hα'
  have hα'1 : 7 / 12 < α' := by rw [hα']; linarith
  have hα'2 : α' < α := by rw [hα']; linarith
  obtain ⟨X, hX1, hX⟩ := exists_theta_window_lower_seven_twelfths hα'1 (by linarith)
  have hgap : ∀ᶠ x : ℝ in atTop, 2 * x ^ α' < x ^ α := by
    filter_upwards [(tendsto_rpow_atTop (show 0 < α - α' by linarith)).eventually_gt_atTop 2,
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hsplit : x ^ α = x ^ α' * x ^ (α - α') := by rw [← Real.rpow_add hx0]; ring_nf
    rw [hsplit]
    have hpos : 0 < x ^ α' := Real.rpow_pos_of_pos hx0 _
    nlinarith
  filter_upwards [hgap, eventually_ge_atTop X] with x hgx hxX
  have hx1 : 1 ≤ x := le_trans hX1 hxX
  have hx0 : 0 < x := by linarith
  have hxa0 : 0 ≤ x ^ α := Real.rpow_nonneg hx0.le _
  have hle : x ^ α ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 hα1.le
    rwa [Real.rpow_one] at this
  have hθ := hX x (x ^ α) hxX hxa0
  have h2 : (2 : ℝ) ^ α' ≤ 2 := by
    calc (2 : ℝ) ^ α' ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hpow : (x + x ^ α) ^ α' ≤ 2 * x ^ α' := by
    calc (x + x ^ α) ^ α' ≤ (2 * x) ^ α' :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ = 2 ^ α' * x ^ α' := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 * x ^ α' := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le _)
  have hpos : 0 < Chebyshev.theta (x + x ^ α) - Chebyshev.theta x := by linarith
  rw [Sieve.theta_sub_eq_sum_Ioc (by linarith)] at hpos
  obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨p, hp.2, ?_, ?_⟩
  · have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hp.1.1
    linarith [Nat.lt_floor_add_one x]
  · have h1 : (p : ℝ) ≤ (⌊x + x ^ α⌋₊ : ℝ) := by exact_mod_cast hp.1.2
    linarith [Nat.floor_le (show 0 ≤ x + x ^ α by linarith)]

namespace PrimeDeletion

/-- **A concrete half-dimension uncertainty for every `κ ∈ (1/2, 5/6)`.** -/
theorem exists_prime_deletion_half_dimension_uncertainty_five_sixths {κ : ℝ}
    (hκ : 1 / 2 < κ) (hκ' : κ < 5 / 6) :
    ∃ Q : Set ℕ, (∀ q ∈ Q, q.Prime) ∧
      (∃ η < κ / 2, (fun x : ℝ => deletedChebyshev Q x - (1 / κ) * (x ^ κ + x ^ (κ / 2)))
        =O[atTop] fun x => x ^ η) ∧
      ∀ a θ : ℝ, 0 ≤ θ → θ < κ / 2 →
        ¬(fun x : ℝ => qFreeCount Q x - a * x) =O[atTop] fun x => x ^ θ := by
  set α : ℝ := 19 / 24 - κ / 4 with hαdef
  have hα : (7 / 12 : ℝ) < α := by rw [hαdef]; linarith
  have hα1 : α < 1 := by rw [hαdef]; linarith
  have hακ : κ - 1 + α < κ / 2 := by rw [hαdef]; linarith
  have he : 0 ≤ κ - 1 + α := by rw [hαdef]; linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : κ < 1 := by linarith
  obtain ⟨X, hX1, hwin⟩ := exists_theta_window_lower_seven_twelfths hα hα1
  obtain ⟨η, hη, hO⟩ := greedy_chebyshev_expansion hκ0 hκ1 hα1 he hακ (by norm_num : (0 : ℝ) < 2)
    (by linarith : (0 : ℝ) ≤ X) hwin
  refine ⟨greedyDeletion κ, fun q hq => hq.1, ⟨η, hη, hO⟩, ?_⟩
  intro a θ hθ hθκ
  refine not_isBigO_qFreeCount_of_odd (greedyDeletion κ) (l := 1) odd_one hθ hθκ hη hκ0 hκ1 ?_
  simpa using hO

end PrimeDeletion

end RHTower
