import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetBoundary

/-!
# The Hawking–Page table of classical gravity in the corpus boundary thermodynamics

At zero Gauss–Bonnet coupling and zero charge the corpus five-dimensional boundary thermodynamics
is that of Schwarzschild–AdS₅: energy `3(x⁴ + x²)`, entropy `4πx³`, temperature
`T(x) = (2x² + 1)/(2πx)` and free energy `F_t(x) = 3x⁴ + 3x² − 4πt x³ = x²(3x² − 4πt x + 3)`,
with thermal AdS at `x = 0`. Its saddles reproduce the first three rows of the weak-coupling
Polyakov-loop table:

* black holes exist exactly for `t ≥ T_min = √2/π`, attained at `x = 1/√2`; the small branch
  `x < 1/√2` has negative specific heat (unstable saddle);
* on shell `F = x²(1 − x²)`, so the large black hole takes over at `x = 1`, `T_HP = 3/(2π)`;
  exactly: thermal AdS is the global minimum iff `t ≤ 3/(2π)`;
* thermal AdS is a strict local minimum at every temperature: classical gravity has no analogue of
  the Hagedorn row, where the confined saddle itself becomes unstable.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.HagedornBootstrap

open HTGeometry.AdSGaussBonnet

theorem potential_einstein (t z x : ℝ) :
    potential t z 0 0 x = x ^ 2 * (3 * x ^ 2 - 4 * π * t * x + 3) := by
  unfold potential energy entropy
  simp
  ring

theorem temperature_einstein {x : ℝ} (hx : 0 < x) :
    temperature 0 0 x = (2 * x ^ 2 + 1) / (2 * π * x) := by
  unfold temperature
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **Exact Hawking–Page point:** thermal AdS is the global minimum iff `t ≤ 3/(2π)`. -/
theorem potential_einstein_nonneg_iff {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    (∀ x, 0 ≤ potential t z 0 0 x) ↔ t ≤ 3 / (2 * π) := by
  have hπ := Real.pi_pos
  constructor
  · intro h
    have h1 := h 1
    rw [potential_einstein] at h1
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · intro htc x
    rw [potential_einstein]
    have h2 : 2 * π * t ≤ 3 := by rw [le_div_iff₀ (by positivity)] at htc; linarith
    have key : 3 * x ^ 2 - 4 * π * t * x + 3 = 3 * (x - 2 * π * t / 3) ^ 2 + (9 - (2 * π * t) ^ 2) / 3 := by
      ring
    have h0 : 0 ≤ 2 * π * t := by positivity
    have : 0 ≤ 9 - (2 * π * t) ^ 2 := by nlinarith [mul_le_mul h2 h2 h0 (by norm_num)]
    have : 0 ≤ 3 * x ^ 2 - 4 * π * t * x + 3 := by rw [key]; positivity
    positivity

/-- Above `T_HP = 3/(2π)` the black hole of radius one already beats thermal AdS. -/
theorem largeBlackHole_dominates {t : ℝ} (ht : 3 / (2 * π) < t) (z : ℝ) :
    potential t z 0 0 1 < 0 := by
  rw [potential_einstein]
  have hπ := Real.pi_pos
  rw [div_lt_iff₀ (by positivity)] at ht
  nlinarith

/-- On shell the free energy is `x²(1 − x²)`. -/
theorem potential_onShell {x : ℝ} (hx : 0 < x) (z : ℝ) :
    potential (temperature 0 0 x) z 0 0 x = x ^ 2 * (1 - x ^ 2) := by
  rw [potential_einstein, temperature_einstein hx]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem hawkingPage_temperature : temperature 0 0 1 = 3 / (2 * π) := by
  rw [temperature_einstein one_pos]; ring

/-- Small black holes (`x < 1`) lose to thermal AdS on shell; large ones (`x > 1`) win. -/
theorem onShell_sign {x : ℝ} (hx : 0 < x) (z : ℝ) :
    (x < 1 → 0 < potential (temperature 0 0 x) z 0 0 x) ∧
      (1 < x → potential (temperature 0 0 x) z 0 0 x < 0) := by
  rw [potential_onShell hx]
  constructor
  · intro h; have : 0 < 1 - x ^ 2 := by nlinarith
    positivity
  · intro h; have : 1 - x ^ 2 < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg (by positivity) this

/-- **Minimal temperature:** `T(x) ≥ √2/π`, with equality at `x = 1/√2`. -/
theorem minimalTemperature_le {x : ℝ} (hx : 0 < x) : √2 / π ≤ temperature 0 0 x := by
  rw [temperature_einstein hx, div_le_div_iff₀ Real.pi_pos (by positivity)]
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e : (2 * x ^ 2 + 1) * π - √2 * (2 * π * x) = π * (√2 * x - 1) ^ 2 := by
    linear_combination (-π * x ^ 2) * h2
  have := mul_nonneg Real.pi_pos.le (sq_nonneg (√2 * x - 1))
  linarith

theorem minimalTemperature_attained : temperature 0 0 (1 / √2) = √2 / π := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < √2 := by positivity
  rw [temperature_einstein (by positivity)]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  nlinarith

/-- Black-hole saddles exist exactly from `T_min = √2/π` on. -/
theorem blackHole_exists_iff {t : ℝ} (ht : 0 < t) :
    (∃ x, 0 < x ∧ temperature 0 0 x = t) ↔ √2 / π ≤ t := by
  constructor
  · rintro ⟨x, hx, rfl⟩; exact minimalTemperature_le hx
  · intro h
    have hπ := Real.pi_pos
    have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hd : 0 ≤ (π * t) ^ 2 - 2 := by
      rw [div_le_iff₀ hπ] at h
      have : √2 ≤ π * t := by linarith
      nlinarith [Real.sqrt_nonneg 2]
    set s := √((π * t) ^ 2 - 2) with hs
    have hs2 : s ^ 2 = (π * t) ^ 2 - 2 := Real.sq_sqrt hd
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    refine ⟨(π * t + s) / 2, by positivity, ?_⟩
    rw [temperature_einstein (by positivity)]
    rw [div_eq_iff (by positivity)]
    nlinarith

/-- `T'(x) = (2x² − 1)/(2πx²)`: the small branch `x < 1/√2` has negative specific heat. -/
theorem hasDerivAt_temperature_einstein {x : ℝ} (hx : 0 < x) :
    HasDerivAt (temperature 0 0) ((2 * x ^ 2 - 1) / (2 * π * x ^ 2)) x := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hev : temperature 0 0 =ᶠ[nhds x] fun y => y / π + 1 / (2 * π) * y⁻¹ := by
    filter_upwards [lt_mem_nhds hx] with y hy
    rw [temperature_einstein hy]
    field_simp
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  refine (((hasDerivAt_id x).div_const π).add ((hasDerivAt_inv hx.ne').const_mul (1 / (2 * π)))).congr_deriv ?_
  field_simp
  ring

theorem smallBlackHole_negative_specificHeat {x : ℝ} (hx : 0 < x) (hs : x < 1 / √2) :
    (2 * x ^ 2 - 1) / (2 * π * x ^ 2) < 0 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsx : √2 * x < 1 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < √2)).mp hs; linarith
  have hsq : (√2 * x) ^ 2 < 1 := pow_lt_one₀ (by positivity) hsx (by norm_num)
  have : 2 * x ^ 2 < 1 := by rw [mul_pow, h2] at hsq; exact hsq
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- **No Hagedorn row in gravity:** thermal AdS is a strict local minimum at every temperature. -/
theorem thermalAdS_locally_stable (t z : ℝ) :
    ∃ δ > 0, ∀ x, 0 < x → x < δ → 0 < potential t z 0 0 x := by
  refine ⟨1 / (2 * π * |t| + 1), by positivity, fun x hx hxδ => ?_⟩
  rw [potential_einstein]
  have hπ := Real.pi_pos
  have h1 : x * (2 * π * |t| + 1) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hxδ; linarith
  have h2 : 4 * π * t * x ≤ 4 * π * |t| * x := by
    have := mul_le_mul_of_nonneg_left (le_abs_self t) (le_of_lt (by positivity : 0 < 4 * π * x))
    linarith
  have h3 : 4 * π * |t| * x < 2 := by nlinarith [abs_nonneg t]
  have : 0 < 3 * x ^ 2 - 4 * π * t * x + 3 := by nlinarith
  positivity

/-- The Hawking–Page temperature lies above the minimal one: `T_HP/T_min = 3/(2√2)`. -/
theorem hawkingPage_over_minimal : (3 / (2 * π)) / (√2 / π) = 3 / (2 * √2) ∧ √2 / π < 3 / (2 * π) := by
  have hπ := Real.pi_pos
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < √2 := by positivity
  constructor
  · field_simp
  · rw [div_lt_div_iff₀ hπ (by positivity)]
    nlinarith

end GaloisForLFunctions.HagedornBootstrap
