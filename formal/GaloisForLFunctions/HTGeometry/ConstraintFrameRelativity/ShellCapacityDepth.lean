import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.SchurCapacity

/-!
# Depth response of the Boolean shell capacity

An ordered prime aperture `p_0 < p_1 < ⋯ < p_{d-1}` carries, at inverse temperature `σ`, the
Bernoulli occupation `q_i = p_i^{-σ}/(1 + p_i^{-σ})` with variance `w_i = q_i(1-q_i)` and clock
`λ_i = log p_i`.  Its parity--energy Schur capacity `D(σ)` obeys

* `Aperture.capacity_pos` — strict positivity;
* `Aperture.capacity_le_sum_fug` — the crude bound `π² ∑ p_i^{-σ}`, hence `π² d p_0^{-σ}`;
* `Aperture.tendsto_capacity_atTop` — `D(σ) → 0`;
* `Aperture.exists_depth_capacity_lt` — a sufficiently deep power event strictly decreases the
  capacity.

The elementary input is `occVar x = x/(1+x)²`, which lies between `x/4` and `x` on `(0,1]` and is
nondecreasing there.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

/-! ## The Bernoulli occupation variance of a fugacity -/

/-- Occupation probability of a fugacity `x`. -/
noncomputable def occProb (x : ℝ) : ℝ := x / (1 + x)

/-- Occupation variance of a fugacity `x`. -/
noncomputable def occVar (x : ℝ) : ℝ := occProb x * (1 - occProb x)

theorem occVar_eq {x : ℝ} (hx : 0 ≤ x) : occVar x = x / (1 + x) ^ 2 := by
  have h : (0 : ℝ) < 1 + x := by linarith
  rw [occVar, occProb]
  field_simp
  ring

theorem occVar_pos {x : ℝ} (hx : 0 < x) : 0 < occVar x := by
  rw [occVar_eq hx.le]
  have h : (0 : ℝ) < 1 + x := by linarith
  positivity

theorem occVar_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ occVar x := by
  rw [occVar_eq hx]
  have h : (0 : ℝ) < 1 + x := by linarith
  positivity

theorem occVar_le {x : ℝ} (hx : 0 ≤ x) : occVar x ≤ x := by
  rw [occVar_eq hx]
  have h : (0 : ℝ) < 1 + x := by linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg x, mul_nonneg (mul_nonneg hx hx) hx]

theorem occVar_ge {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x / 4 ≤ occVar x := by
  rw [occVar_eq hx]
  have h : (0 : ℝ) < 1 + x := by linarith
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1), mul_nonneg (mul_nonneg hx hx) hx]

theorem occVar_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    occVar x ≤ occVar y := by
  rw [occVar_eq hx, occVar_eq (hx.trans hxy)]
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : (0 : ℝ) < 1 + y := by linarith
  have hxy1 : x * y ≤ 1 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hxy1)]

/-! ## Ordered prime apertures -/

/-- An ordered aperture of at least two primes. -/
structure Aperture where
  /-- The number of marked primes. -/
  card : ℕ
  /-- At least two primes are marked. -/
  two_le_card : 2 ≤ card
  /-- The marked primes, listed in increasing order. -/
  prime : Fin card → ℕ
  /-- Every marked label is at least two. -/
  two_le : ∀ i, 2 ≤ prime i
  /-- The listing is strictly increasing. -/
  strictMono : StrictMono prime

namespace Aperture

variable (F : Aperture)

/-- The least marked prime. -/
def least : Fin F.card := ⟨0, by have := F.two_le_card; omega⟩

/-- The second marked prime. -/
def second : Fin F.card := ⟨1, by have := F.two_le_card; omega⟩

/-- The greatest marked prime. -/
def greatest : Fin F.card := ⟨F.card - 1, by have := F.two_le_card; omega⟩

theorem least_le (i : Fin F.card) : F.least ≤ i := by
  simp [least, Fin.le_def]

theorem le_greatest (i : Fin F.card) : i ≤ F.greatest := by
  have h := i.isLt
  simp only [greatest, Fin.le_def]
  omega

theorem least_lt_second : F.least < F.second := by
  simp [least, second, Fin.lt_def]

/-- Fugacity of a marked prime. -/
noncomputable def fug (i : Fin F.card) (σ : ℝ) : ℝ := (F.prime i : ℝ) ^ (-σ)

/-- Bernoulli variance of a marked prime. -/
noncomputable def wt (i : Fin F.card) (σ : ℝ) : ℝ := occVar (F.fug i σ)

/-- Logarithmic clock of a marked prime. -/
noncomputable def clock (i : Fin F.card) : ℝ := Real.log (F.prime i)

theorem one_lt_prime (i : Fin F.card) : (1 : ℝ) < (F.prime i : ℝ) := by
  have h : (2 : ℝ) ≤ (F.prime i : ℝ) := by exact_mod_cast F.two_le i
  linarith

theorem prime_pos (i : Fin F.card) : (0 : ℝ) < (F.prime i : ℝ) :=
  lt_trans zero_lt_one (F.one_lt_prime i)

theorem fug_pos (i : Fin F.card) (σ : ℝ) : 0 < F.fug i σ :=
  Real.rpow_pos_of_pos (F.prime_pos i) _

theorem fug_le_one (i : Fin F.card) {σ : ℝ} (hσ : 0 ≤ σ) : F.fug i σ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (F.one_lt_prime i).le (by linarith)

theorem fug_antitone {i j : Fin F.card} (hij : i ≤ j) {σ : ℝ} (hσ : 0 ≤ σ) :
    F.fug j σ ≤ F.fug i σ := by
  have hp : (F.prime i : ℝ) ≤ (F.prime j : ℝ) := by
    exact_mod_cast F.strictMono.monotone hij
  have hi := F.prime_pos i
  rw [fug, fug, Real.rpow_neg hi.le, Real.rpow_neg (F.prime_pos j).le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hi _) (Real.rpow_le_rpow hi.le hp hσ)

theorem wt_pos (i : Fin F.card) (σ : ℝ) : 0 < F.wt i σ := occVar_pos (F.fug_pos i σ)

theorem wt_le_fug (i : Fin F.card) (σ : ℝ) : F.wt i σ ≤ F.fug i σ :=
  occVar_le (F.fug_pos i σ).le

theorem fug_div_four_le_wt (i : Fin F.card) {σ : ℝ} (hσ : 0 ≤ σ) :
    F.fug i σ / 4 ≤ F.wt i σ :=
  occVar_ge (F.fug_pos i σ).le (F.fug_le_one i hσ)

theorem wt_le_wt_least (i : Fin F.card) {σ : ℝ} (hσ : 0 ≤ σ) :
    F.wt i σ ≤ F.wt F.least σ :=
  occVar_mono (F.fug_pos i σ).le (F.fug_antitone (F.least_le i) hσ) (F.fug_le_one _ hσ)

theorem clock_pos (i : Fin F.card) : 0 < F.clock i := Real.log_pos (F.one_lt_prime i)

theorem clock_le_greatest (i : Fin F.card) : F.clock i ≤ F.clock F.greatest := by
  have hp : (F.prime i : ℝ) ≤ (F.prime F.greatest : ℝ) := by
    exact_mod_cast F.strictMono.monotone (F.le_greatest i)
  exact Real.log_le_log (F.prime_pos i) hp

theorem clock_least_lt_second : F.clock F.least < F.clock F.second := by
  have hp : (F.prime F.least : ℝ) < (F.prime F.second : ℝ) := by
    exact_mod_cast F.strictMono F.least_lt_second
  exact Real.log_lt_log (F.prime_pos _) hp

/-! ## The shell capacity -/

/-- The parity--energy Schur capacity of the marked aperture at inverse temperature `σ`. -/
noncomputable def capacity (σ : ℝ) : ℝ :=
  schurCapacity (fun i => F.wt i σ) F.clock

theorem energy_moment_pos (σ : ℝ) : 0 < capC (fun i => F.wt i σ) F.clock :=
  capC_pos (fun i => F.wt_pos i σ) (p₀ := F.least) (F.clock_pos F.least).ne'

theorem capacity_pos (σ : ℝ) : 0 < F.capacity σ :=
  schurCapacity_pos (fun i => F.wt_pos i σ) (F.clock_least_lt_second).ne

/-- **Crude capacity bound.**  `D(σ) ≤ π² ∑ p_i^{-σ}`. -/
theorem capacity_le_sum_fug (σ : ℝ) :
    F.capacity σ ≤ Real.pi ^ 2 * ∑ i, F.fug i σ := by
  refine le_trans (schurCapacity_le_pi_sq_mul_capA (F.energy_moment_pos σ)) ?_
  have hA : capA (fun i => F.wt i σ) ≤ ∑ i, F.fug i σ :=
    Finset.sum_le_sum fun i _ => F.wt_le_fug i σ
  exact mul_le_mul_of_nonneg_left hA (by positivity)

/-- **Crude capacity bound, uniform form.**  `D(σ) ≤ π² d p_0^{-σ}`. -/
theorem capacity_le_card_mul_fug_least {σ : ℝ} (hσ : 0 ≤ σ) :
    F.capacity σ ≤ Real.pi ^ 2 * ((F.card : ℝ) * F.fug F.least σ) := by
  refine le_trans (F.capacity_le_sum_fug σ) ?_
  have hsum : ∑ i, F.fug i σ ≤ (F.card : ℝ) * F.fug F.least σ := by
    have h : ∑ i, F.fug i σ ≤ ∑ _i : Fin F.card, F.fug F.least σ :=
      Finset.sum_le_sum fun i _ => F.fug_antitone (F.least_le i) hσ
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The fugacity of a fixed prime tends to zero as the temperature drops. -/
theorem tendsto_fug_atTop (i : Fin F.card) :
    Filter.Tendsto (fun σ => F.fug i σ) Filter.atTop (nhds 0) := by
  have hlog : 0 < Real.log (F.prime i) := F.clock_pos i
  have hrw : (fun σ => F.fug i σ)
      = fun σ : ℝ => (Real.exp (σ * Real.log (F.prime i)))⁻¹ := by
    funext σ
    rw [fug, Real.rpow_def_of_pos (F.prime_pos i), ← Real.exp_neg]
    congr 1
    ring
  rw [hrw]
  have hmul : Filter.Tendsto (fun σ : ℝ => σ * Real.log (F.prime i))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hlog Filter.tendsto_id
  exact (Real.tendsto_exp_atTop.comp hmul).inv_tendsto_atTop

/-- **The capacity vanishes at low temperature.** -/
theorem tendsto_capacity_atTop :
    Filter.Tendsto F.capacity Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto
      (fun σ : ℝ => Real.pi ^ 2 * ((F.card : ℝ) * F.fug F.least σ))
      Filter.atTop (nhds 0) := by
    have h := (F.tendsto_fug_atTop F.least).const_mul ((F.card : ℝ))
    have h2 := h.const_mul (Real.pi ^ 2)
    simpa using h2
  refine squeeze_zero' (g := fun σ => Real.pi ^ 2 * ((F.card : ℝ) * F.fug F.least σ))
    (Filter.Eventually.of_forall fun σ => (F.capacity_pos σ).le) ?_ hg
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with σ hσ
  exact F.capacity_le_card_mul_fug_least hσ

/-- **A sufficiently deep power event strictly decreases the capacity.** -/
theorem exists_depth_capacity_lt {m : ℕ} (hm : m ≠ 0) {τ : ℝ} (hτ : 0 < τ) :
    ∃ r : ℕ, 2 ≤ r ∧ F.capacity ((r : ℝ) * (m : ℝ) * τ) < F.capacity ((m : ℝ) * τ) := by
  have hpos := F.capacity_pos ((m : ℝ) * τ)
  have hev := F.tendsto_capacity_atTop.eventually_lt_const hpos
  obtain ⟨σ₀, hσ₀⟩ := Filter.eventually_atTop.mp hev
  have hmτ : 0 < (m : ℝ) * τ := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    positivity
  obtain ⟨r, hr⟩ := exists_nat_gt (max 2 (σ₀ / ((m : ℝ) * τ)))
  have h2 : (2 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hr2 : 2 ≤ r := by exact_mod_cast h2.le
  have hgt : σ₀ / ((m : ℝ) * τ) < r := lt_of_le_of_lt (le_max_right _ _) hr
  have hlt : σ₀ < (r : ℝ) * ((m : ℝ) * τ) := (div_lt_iff₀ hmτ).mp hgt
  rw [← mul_assoc] at hlt
  exact ⟨r, hr2, hσ₀ _ hlt.le⟩

end Aperture

end HTGeometry.ConstraintFrameRelativity
