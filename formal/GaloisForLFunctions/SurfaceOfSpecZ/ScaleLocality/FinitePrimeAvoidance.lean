import GaloisForLFunctions.SurfaceOfSpecZ.AlmostAllPrimesAndTheStepanovBoundary

/-! Short-interval prime mass gives prime avoidance uniformly over finite
exception sets whose cardinality has a fixed power saving. -/

open Filter Topology Set
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The starting height is uniform over all finite exception sets of the
specified cardinality, rather than depending on the set itself. -/
theorem eventually_prime_avoids_small_finset {γ β C : ℝ}
    (hγβ : γ < β) (hβ : 7 / 12 < β) (hβ1 : β < 1) :
    ∀ᶠ y : ℝ in atTop, ∀ E : Finset ℕ, (E.card : ℝ) ≤ C * y ^ γ →
      ∃ p : ℕ, p.Prime ∧ p ∉ E ∧ y < p ∧ (p : ℝ) ≤ y + y ^ β := by
  classical
  have hmass := (tendsto_theta_short_window_div_seven_twelfths hβ hβ1).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hlo := isLittleO_log_rpow_rpow_atTop (1 : ℝ)
    (show 0 < β - γ by linarith only [hγβ])
  have hlim : Tendsto (fun y : ℝ => (2 * C) * (Real.log y / y ^ (β - γ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_zero] using hlo.tendsto_div_nhds_zero.const_mul (2 * C)
  filter_upwards [hmass,
    hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (2 : ℝ)] with y hmass hsmall hy2
  intro E hE
  have hy0 : 0 < y := by linarith only [hy2]
  have hy1 : 1 ≤ y := by linarith only [hy2]
  have hyβ : 0 < y ^ β := Real.rpow_pos_of_pos hy0 β
  rw [lt_div_iff₀ hyβ] at hmass
  have htot : 1 / 2 * y ^ β <
      ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊y + y ^ β⌋₊).filter Nat.Prime, Real.log (p : ℝ) := by
    rwa [← RHTower.Sieve.theta_sub_eq_sum_Ioc (by linarith only [hyβ])]
  let S : Finset ℕ := (Finset.Ioc ⌊y⌋₊ ⌊y + y ^ β⌋₊).filter Nat.Prime
  have hpbound {p : ℕ} (hp : p ∈ S) : p.Prime ∧ y < p ∧ (p : ℝ) ≤ y + y ^ β := by
    have hh := Finset.mem_filter.mp hp
    have hi := Finset.mem_Ioc.mp hh.1
    exact ⟨hh.2, (Nat.floor_lt hy0.le).mp hi.1,
      (Nat.cast_le.mpr hi.2).trans (Nat.floor_le (by positivity))⟩
  by_contra hnone
  have hsub : S ⊆ E := by
    intro p hp
    have hh := hpbound hp
    by_contra hpE
    exact hnone ⟨p, hh.1, hpE, hh.2⟩
  have hyβle : y ^ β ≤ y := by
    calc _ ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 hβ1.le
      _ = y := Real.rpow_one y
  have hlog (p : ℕ) (hp : p ∈ S) : Real.log (p : ℝ) ≤ 2 * Real.log y := by
    have hh := hpbound hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hh.1.pos
    calc
      _ ≤ Real.log (y * y) := Real.log_le_log hp0
        (by linarith only [hh.2.2, hyβle, mul_le_mul_of_nonneg_right hy2 hy0.le])
      _ = 2 * Real.log y := by rw [Real.log_mul hy0.ne' hy0.ne']; ring
  have hcard : (S.card : ℝ) ≤ C * y ^ γ :=
    (show (S.card : ℝ) ≤ E.card by exact_mod_cast Finset.card_le_card hsub).trans hE
  have hsplit : y ^ γ * y ^ (β - γ) = y ^ β := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  have hsum : (∑ p ∈ S, Real.log (p : ℝ)) ≤ 1 / 2 * y ^ β := by
    calc
      _ ≤ ∑ _p ∈ S, 2 * Real.log y := Finset.sum_le_sum hlog
      _ = (S.card : ℝ) * (2 * Real.log y) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C * y ^ γ) * (2 * Real.log y) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (by norm_num) (Real.log_nonneg hy1))
      _ = ((2 * C) * (Real.log y / y ^ (β - γ))) * y ^ β := by
        rw [← hsplit]
        have hn : y ^ (β - γ) ≠ 0 := (Real.rpow_pos_of_pos hy0 _).ne'
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hyβ.le
  exact (not_lt_of_ge hsum) htot

#print axioms eventually_prime_avoids_small_finset

/-- A uniform finite exceptional set leaves a prime just below every large
point whenever its cardinality grows at a smaller power than the gap. -/
theorem eventually_prime_below_avoids_small_finset {γ β C : ℝ}
    (hγ : 0 ≤ γ) (hγβ : γ < β) (hβ : 7 / 12 < β) (hβ1 : β < 1) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ E : Finset ℕ, (E.card : ℝ) ≤ C * x ^ γ →
      ∃ p : ℕ, p.Prime ∧ p ∉ E ∧ (p : ℝ) ≤ x ∧ x - p ≤ x ^ β := by
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (eventually_prime_avoids_small_finset (C := C * (2 : ℝ) ^ γ) hγβ hβ hβ1)
  filter_upwards [
    (tendsto_rpow_atTop (show 0 < 1 - β by linarith only [hβ1])).eventually_ge_atTop 2,
    eventually_ge_atTop (2 * max Y 0), eventually_gt_atTop (0 : ℝ)] with x hx2 hxY hx0
  intro E hE
  have hsplit : x = x ^ β * x ^ (1 - β) := by
    rw [← Real.rpow_add hx0, show β + (1 - β) = 1 by ring, Real.rpow_one]
  have hxβ0 : 0 < x ^ β := Real.rpow_pos_of_pos hx0 β
  have hxβ : 2 * x ^ β ≤ x := by
    calc _ ≤ x ^ (1 - β) * x ^ β := mul_le_mul_of_nonneg_right hx2 hxβ0.le
      _ = x := by rw [mul_comm, ← hsplit]
  let y : ℝ := x - x ^ β
  have hyY : Y ≤ y := by dsimp [y]; linarith only [hxY, hxβ, le_max_left Y 0]
  have hy0 : 0 ≤ y := by dsimp [y]; linarith only [hxβ, hx0]
  have hx2y : x ≤ 2 * y := by dsimp [y]; linarith only [hxβ]
  have hEy : (E.card : ℝ) ≤ (C * (2 : ℝ) ^ γ) * y ^ γ := by
    calc _ ≤ C * x ^ γ := hE
      _ ≤ C * (2 * y) ^ γ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hx0.le hx2y hγ) hC
      _ = _ := by rw [Real.mul_rpow (by norm_num) hy0]; ring
  obtain ⟨p, hp, hpE, hyp, hpy⟩ := hY y hyY E hEy
  have hyβ : y ^ β ≤ x ^ β := Real.rpow_le_rpow hy0
    (by dsimp [y]; linarith only [hxβ0]) (by linarith only [hβ])
  refine ⟨p, hp, hpE, ?_, ?_⟩
  · dsimp [y] at hpy hyβ
    linarith only [hpy, hyβ]
  · dsimp [y] at hyp
    linarith only [hyp]

#print axioms eventually_prime_below_avoids_small_finset

/-- Logarithmic prime approximation is uniform in every finite exception set
of cardinality at most `C exp(γu)`, for `γ<β<1`. -/
theorem exists_log_prime_avoiding_small_finset {γ β C : ℝ}
    (hγ : 0 ≤ γ) (hγβ : γ < β) (hβ : 7 / 12 < β) (hβ1 : β < 1) (hC : 0 ≤ C) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u → ∀ E : Finset ℕ,
      (E.card : ℝ) ≤ C * Real.exp (γ * u) →
      ∃ p : ℕ, p.Prime ∧ p ∉ E ∧ 0 ≤ Real.log p ∧ Real.log p ≤ u ∧
        u - Real.log p ≤ 2 * Real.exp ((β - 1) * u) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (eventually_prime_below_avoids_small_finset hγ hγβ hβ hβ1 hC)
  let U : ℝ := max (max (Real.log (max X 1)) (Real.log 3 / (1 - β))) 0
  refine ⟨U, le_max_right _ _, fun u hu E hE => ?_⟩
  have hxX : X ≤ Real.exp u := by
    have hh : Real.log (max X 1) ≤ u := (le_max_left _ _).trans ((le_max_left _ _).trans hu)
    have hx : max X 1 ≤ Real.exp u := by
      rw [← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right X 1))]
      exact Real.exp_le_exp.mpr hh
    exact (le_max_left _ _).trans hx
  have hEx : (E.card : ℝ) ≤ C * (Real.exp u) ^ γ := by
    rwa [← Real.exp_mul, mul_comm u γ]
  obtain ⟨p, hp, hpE, hple, hgap⟩ := hX (Real.exp u) hxX E hEx
  rw [← Real.exp_mul, mul_comm u β] at hgap
  have hsmall : Real.exp (β * u) ≤ Real.exp u / 2 := by
    have hh : Real.log 3 / (1 - β) ≤ u :=
      (le_max_right _ _).trans ((le_max_left _ _).trans hu)
    have hl : Real.log 3 ≤ (1 - β) * u := by
      rw [div_le_iff₀ (by linarith only [hβ1])] at hh
      linarith only [hh]
    have he : 3 ≤ Real.exp ((1 - β) * u) := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      exact Real.exp_le_exp.mpr hl
    have hx : Real.exp u = Real.exp ((1 - β) * u) * Real.exp (β * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hx]
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (β * u)).le
    linarith only [hm, Real.exp_pos (β * u)]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine ⟨p, hp, hpE, Real.log_nonneg hp1,
    by rw [← Real.log_exp u]; exact Real.log_le_log hp0 hple, ?_⟩
  have hl : u - Real.log p = Real.log (Real.exp u / p) := by
    rw [Real.log_div (Real.exp_pos u).ne' hp0.ne', Real.log_exp]
  have hlog := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos u) hp0)
  have hdiv : Real.exp u / p - 1 = (Real.exp u - p) / p := by field_simp
  have hratio : (Real.exp u - p) / p ≤ Real.exp (β * u) * (2 / Real.exp u) := by
    rw [div_le_iff₀ hp0]
    have hh : 1 ≤ 2 / Real.exp u * p := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (Real.exp_pos u)]
      linarith only [hgap, hsmall]
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (β * u)).le
    nlinarith only [hgap, hm]
  have he : Real.exp (β * u) * (2 / Real.exp u) = 2 * Real.exp ((β - 1) * u) := by
    rw [show (β - 1) * u = β * u - u by ring, Real.exp_sub]
    ring
  linarith only [hl, hlog, hdiv, hratio, he]

#print axioms exists_log_prime_avoiding_small_finset
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
