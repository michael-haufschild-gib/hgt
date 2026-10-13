import GaloisForLFunctions.HTGeometry.CircleQuadraturePositiveWolffMeasure
import GaloisForLFunctions.RHTower.WeilLagSingleBaseWolffConfiguration

/-!
# Single-base blindness survives every zero-density bound, with positive weights

**Theorem** (`exists_positive_lag_configuration_density_blind`). For every spacing
`ℓ > 2 log 10` there is a countable configuration `ρ_i` with positive weights `c_i` such that
* the points are distinct and lie in `½ < Re ρ < 1`;
* the weights match the Weil size: `c_i^{−1/2} ≤ Im ρ_i < c_i^{−1/2} + 4π/ℓ`;
* `Σ_i (Im ρ_i)^{−p} < ∞` for every `p > 0`, so only `O(T^p)` ordinates lie below `T`, for every
  `p > 0`;
* the ordinates are locally finite;
* every single-base sample vanishes: `Σ_i c_i e^{mℓ(ρ_i − ½)} = 0` for all `m ≥ 1`.

So a single-base lag receiver cannot use any zero-density estimate, however strong short of
finiteness, nor positivity of the weights, nor their size `≍ |ρ|^{−2}`, to see a configuration off
the critical line.

**Proof.** Take the positive measure of `exists_positive_wolff_measure_pSummable` (nodes `x_i` in
`5/4 ≤ |x| ≤ 10`, `Σ c_i^p < ∞` for all `p > 0`, moments `m ≥ 1` zero) and lift each node to
`ρ_i = ½ + (log x_i + 2πi n_i)/ℓ`, so that `e^{mℓ(ρ_i − ½)} = x_i^m`. The integer `n_i` is chosen with
`2πn_i ≥ ℓ c_i^{−1/2} − arg x_i` minimal, which puts `Im ρ_i` in `[c_i^{−1/2}, c_i^{−1/2} + 4π/ℓ)`.
Then `(Im ρ_i)^{−p} ≤ c_i^{p/2}`.
-/

open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry.CircleQuadraturePositive

/-- The lift index `n = ⌈(ℓ c^{−1/2} + π)/(2π)⌉₊`. -/
def densityLiftIndex (ℓ c : ℝ) : ℕ := ⌈(ℓ * c ^ (-(1 / 2 : ℝ)) + Real.pi) / (2 * Real.pi)⌉₊

theorem densityLift_im_mem {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (x : ℂ) :
    c ^ (-(1 / 2 : ℝ)) ≤ (Complex.arg x + 2 * Real.pi * densityLiftIndex ℓ c) / ℓ ∧
      (Complex.arg x + 2 * Real.pi * densityLiftIndex ℓ c) / ℓ <
        c ^ (-(1 / 2 : ℝ)) + 4 * Real.pi / ℓ := by
  have hπ := Real.pi_pos
  set y := (ℓ * c ^ (-(1 / 2 : ℝ)) + Real.pi) / (2 * Real.pi) with hy
  have hc0 : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc.le _
  have hy0 : 0 ≤ y := by positivity
  have hn1 : y ≤ (densityLiftIndex ℓ c : ℝ) := Nat.le_ceil y
  have hn2 : (densityLiftIndex ℓ c : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have ha1 := Complex.neg_pi_lt_arg x
  have ha2 := Complex.arg_le_pi x
  have h2π : 2 * Real.pi * y = ℓ * c ^ (-(1 / 2 : ℝ)) + Real.pi := by rw [hy]; field_simp
  constructor
  · rw [le_div_iff₀ hℓ]
    nlinarith
  · rw [div_lt_iff₀ hℓ, add_mul, div_mul_cancel₀ _ hℓ.ne']
    nlinarith

/-- **Density-blind positive single-base configurations.** -/
theorem exists_positive_lag_configuration_density_blind {ℓ : ℝ} (hℓ : 2 * Real.log 10 < ℓ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℝ), Function.Injective ρ ∧
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1) ∧ (∀ i, 0 < c i) ∧
      (∀ i, c i ^ (-(1 / 2 : ℝ)) ≤ (ρ i).im ∧ (ρ i).im < c i ^ (-(1 / 2 : ℝ)) + 4 * Real.pi / ℓ) ∧
      (∀ p : ℝ, 0 < p → Summable fun i => (ρ i).im ^ (-p)) ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧
      ∀ m : ℕ, 1 ≤ m →
        HasSum (fun i => (c i : ℂ) * Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))) 0 := by
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨ι, hι, x, c, hinj, hx, hc, hsum, hmom⟩ := exists_positive_wolff_measure_pSummable
  have hx0 : ∀ i, x i ≠ 0 := fun i h => by
    have := (hx i).1; rw [h, norm_zero] at this; norm_num at this
  set ρ : ι → ℂ := fun i =>
    1 / 2 + (Complex.log (x i) + 2 * Real.pi * I * (densityLiftIndex ℓ (c i) : ℕ)) / ℓ with hρ
  have hexp : ∀ i (m : ℕ), Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2)) = x i ^ m :=
    fun i m => exp_mul_wolffLift ℓ hℓ0.ne' (x i) (hx0 i) _ m
  have him : ∀ i, (ρ i).im = (Complex.arg (x i) + 2 * Real.pi * densityLiftIndex ℓ (c i)) / ℓ :=
    fun i => im_wolffLift ℓ (x i) _
  have hmem : ∀ i, c i ^ (-(1 / 2 : ℝ)) ≤ (ρ i).im ∧
      (ρ i).im < c i ^ (-(1 / 2 : ℝ)) + 4 * Real.pi / ℓ := fun i => by
    rw [him]; exact densityLift_im_mem hℓ0 (hc i) (x i)
  have himpos : ∀ i, 0 < (ρ i).im := fun i =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (hc i) _) (hmem i).1
  refine ⟨ι, hι, ρ, c, ?_, fun i => ?_, hc, hmem, fun p hp => ?_, fun T => ?_, fun m hm => ?_⟩
  · intro i j hij
    have h := hexp i 1
    rw [hij, hexp j 1, pow_one, pow_one] at h
    exact hinj h.symm
  · have hre : (ρ i).re = 1 / 2 + Real.log ‖x i‖ / ℓ := re_wolffLift ℓ (x i) _
    have hn0 : 0 < ‖x i‖ := by have := (hx i).1; linarith
    have hlo : 0 < Real.log ‖x i‖ := Real.log_pos (by linarith [(hx i).1])
    have hhi : Real.log ‖x i‖ ≤ Real.log 10 := Real.log_le_log hn0 (hx i).2
    rw [hre]
    constructor
    · have : 0 < Real.log ‖x i‖ / ℓ := div_pos hlo hℓ0
      linarith
    · have : Real.log ‖x i‖ / ℓ < 1 / 2 := by
        rw [div_lt_iff₀ hℓ0]; linarith
      linarith
  · refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (himpos i).le _) (fun i => ?_)
      (hsum (p / 2) (by positivity))
    calc (ρ i).im ^ (-p) ≤ (c i ^ (-(1 / 2 : ℝ))) ^ (-p) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (hc i) _) (hmem i).1 (by linarith)
      _ = c i ^ (p / 2) := by
          rw [← Real.rpow_mul (hc i).le]; congr 1; ring
  · rcases le_or_gt T 0 with hT | hT
    · refine (Set.finite_empty).subset fun i hi => ?_
      have := himpos i
      simp only [mem_setOf_eq] at hi
      rw [abs_of_pos this] at hi
      linarith
    · have hfin : {i | T ^ (-(2 : ℝ)) ≤ c i}.Finite := by
        have hε : 0 < T ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hT _
        have := (hsum 1 one_pos).tendsto_cofinite_zero
        simp only [Real.rpow_one] at this
        have h2 := this.eventually (gt_mem_nhds hε)
        simpa [not_lt] using h2
      refine hfin.subset fun i hi => ?_
      simp only [mem_setOf_eq] at hi ⊢
      have h1 := (hmem i).1
      rw [abs_of_pos (himpos i)] at hi
      have h2 : c i ^ (-(1 / 2 : ℝ)) ≤ T := h1.trans hi
      have h3 : (c i ^ (-(1 / 2 : ℝ))) ^ (-(2 : ℝ)) ≥ T ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (hc i) _) h2 (by norm_num)
      rw [← Real.rpow_mul (hc i).le, show (-(1 / 2 : ℝ)) * (-2) = 1 by norm_num,
        Real.rpow_one] at h3
      exact h3
  · have h := hmom m hm
    convert h using 2 with i
    rw [hexp]

end RHTower
