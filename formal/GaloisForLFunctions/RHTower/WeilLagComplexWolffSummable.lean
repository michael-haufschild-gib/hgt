import GaloisForLFunctions.HTGeometry.CircleQuadratureSectorWolffMeasure
import GaloisForLFunctions.RHTower.WeilLagSingleBaseWolffConfiguration

/-!
# Single-base lag samples can vanish with `p`-summable complex weights

For every spacing `ℓ > log 100` there is a countable, injective, locally finite configuration `ρ_i`
in the strip `½ < Re ρ < 1`, with complex weights `c_i` such that `Σ_i |c_i|^p < ∞` for every
`p > 0` and one weight equal to `1`, whose lag samples all vanish:
`Σ_i c_i e^{mℓ(ρ_i − ½)} = 0` for every `m ≥ 0`
(`exists_complex_lag_configuration_vanishing_progression`).

**Proof.** Lift the circle-quadrature annihilating measure
(`CircleQuadratureAnnihilating.exists_annihilating_discrete_measure`), whose nodes lie in
`5/4 ≤ |x| ≤ 10`, by `ρ_x = ½ + (log x + 2πi N_x)/ℓ` with `N` an injection into `ℕ`. Then
`e^{mℓ(ρ_x − ½)} = x^m`, `Re ρ_x − ½ = log|x|/ℓ ∈ (0, ½)`, and the shifts `2πN_x/ℓ` make the
ordinates locally finite.

**Scope.** The positive Wolff configuration
(`exists_positive_lag_configuration_vanishing_progression`) has weights equal to disc areas, so
`Σ √c_i = ∞` (Wesler). Here `Σ |c_i|^p < ∞` for all `p > 0`. So a power-type summability bound
on the weights, such as the bound `Σ_ρ |w_ρ|^{1/2} < ∞` that zero density gives for the high zeros,
cannot by itself make single-base sampling detect off-line zeros. The node series
`Σ_i c_i/(1 − t e^{ℓ(ρ_i − ½)})` vanishes near `t = 0` and has a simple pole at `t = 4/5`
(`CircleQuadratureAnnihilating.tsum_coef_div_eq_zero`,
`CircleQuadratureAnnihilating.norm_tsum_coef_div_ge`), so a Borel-type uniqueness statement for
such series fails without a sign condition.

**Sector-positive form** (`exists_sector_lag_configuration_vanishing_progression`). The sign of the
weights does not help either. Shifting each circle stage by a real multiple of its residual bound
(`CircleQuadratureSector.exists_sector_wolff_measure`) gives weights with `|c_i| ≤ 2 Re c_i`,
arguments tending to `0`, and `Σ|c_i|^p < ∞` for every `p > 0`, while all samples `m ≥ 1` vanish.
The weights `1/(ρ(1 − ρ))` with `0 < Re ρ < 1` and `|Im ρ| ≥ 1` satisfy the same sector condition,
with arguments tending to `0` at large height. So single-base sampling together with zero density
cannot exclude a non-attained top on zero-side grounds; any proof must use more of the arithmetic.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- **Vanishing single-base samples with `p`-summable complex weights.** -/
theorem exists_complex_lag_configuration_vanishing_progression {ℓ : ℝ}
    (hℓ : Real.log 100 < ℓ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℂ), Function.Injective ρ ∧
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1) ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧ (∃ i, c i = 1) ∧
      (∀ p : ℝ, 0 < p → Summable fun i => ‖c i‖ ^ p) ∧
      ∀ m : ℕ, HasSum (fun i => c i * Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))) 0 := by
  obtain ⟨ι, hι, x, c, i₀, hinj, hnorm, -, hc₀, -, -, hp, hmom⟩ :=
    GaloisForLFunctions.HTGeometry.CircleQuadratureAnnihilating.exists_annihilating_discrete_measure
  have hℓ0 : 0 < ℓ := lt_trans (Real.log_pos (by norm_num)) hℓ
  obtain ⟨N, hN⟩ := exists_injective_nat ι
  have hx0 : ∀ i, x i ≠ 0 := fun i h => by
    have := (hnorm i).1; rw [h, norm_zero] at this; norm_num at this
  set ρ : ι → ℂ := fun i => 1 / 2 + (Complex.log (x i) + 2 * Real.pi * I * (N i)) / ℓ with hρdef
  have hexp : ∀ i, ∀ m : ℕ, Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2)) = x i ^ m :=
    fun i m => exp_mul_wolffLift ℓ hℓ0.ne' (x i) (hx0 i) (N i) m
  refine ⟨ι, hι, ρ, c, ?_, ?_, ?_, ⟨i₀, hc₀⟩, hp, fun m => (hmom m).congr_fun fun i => by
    rw [hexp i m]⟩
  · intro a b hab
    have h := hexp a 1
    rw [hab, hexp b 1, pow_one, pow_one] at h
    exact hinj h.symm
  · intro i
    rw [hρdef]
    simp only
    rw [re_wolffLift]
    have h1 := (hnorm i).1
    have h2 := (hnorm i).2
    have hl1 : 0 < Real.log ‖x i‖ := Real.log_pos (by linarith)
    have hl2 : Real.log ‖x i‖ ≤ Real.log 10 := Real.log_le_log (by linarith) h2
    have hlog100 : Real.log 100 = 2 * Real.log 10 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]; norm_num
    constructor
    · have : 0 < Real.log ‖x i‖ / ℓ := div_pos hl1 hℓ0
      linarith
    · have : Real.log ‖x i‖ / ℓ < 1 / 2 := by rw [div_lt_iff₀ hℓ0]; linarith
      linarith
  · intro T
    have hsub : {i : ι | |(ρ i).im| ≤ T} ⊆ N ⁻¹' Set.Iic ⌈(T * ℓ + Real.pi) / (2 * Real.pi)⌉₊ := by
      intro i hi
      simp only [mem_setOf_eq] at hi
      rw [hρdef] at hi
      simp only at hi
      rw [im_wolffLift] at hi
      simp only [mem_preimage, mem_Iic]
      have hπ := Real.pi_pos
      have harg := Complex.neg_pi_lt_arg (x i)
      have hle := (abs_le.mp hi).2
      rw [div_le_iff₀ hℓ0] at hle
      have hN' : (N i : ℝ) ≤ (T * ℓ + Real.pi) / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      exact_mod_cast hN'.trans (Nat.le_ceil _)
    exact ((Set.finite_Iic _).preimage hN.injOn).subset hsub

/-- **Vanishing single-base samples with sector-positive `p`-summable weights.** The weights satisfy
`|c_i| ≤ 2 Re c_i`, their arguments tend to `0`, `Σ|c_i|^p < ∞` for every `p > 0`, and the samples
`Σ_i c_i e^{mℓ(ρ_i − ½)}` vanish for every `m ≥ 1`. -/
theorem exists_sector_lag_configuration_vanishing_progression {ℓ : ℝ}
    (hℓ : Real.log 100 < ℓ) :
    ∃ (ι : Type) (_ : Countable ι) (ρ : ι → ℂ) (c : ι → ℂ), Function.Injective ρ ∧
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1) ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧ (∃ i, c i = 1) ∧
      (∀ i, ‖c i‖ ≤ 2 * (c i).re) ∧ (∀ ε : ℝ, 0 < ε → {i | ε * (c i).re < |(c i).im|}.Finite) ∧
      (∀ p : ℝ, 0 < p → Summable fun i => ‖c i‖ ^ p) ∧
      ∀ m : ℕ, 1 ≤ m →
        HasSum (fun i => c i * Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2))) 0 := by
  obtain ⟨ι, hι, x, c, i₀, hinj, hnorm, -, hc₀, -, hsec, harg, hp, hmom⟩ :=
    GaloisForLFunctions.HTGeometry.CircleQuadratureSector.exists_sector_wolff_measure
  have hℓ0 : 0 < ℓ := lt_trans (Real.log_pos (by norm_num)) hℓ
  obtain ⟨N, hN⟩ := exists_injective_nat ι
  have hx0 : ∀ i, x i ≠ 0 := fun i h => by
    have := (hnorm i).1; rw [h, norm_zero] at this; norm_num at this
  set ρ : ι → ℂ := fun i => 1 / 2 + (Complex.log (x i) + 2 * Real.pi * I * (N i)) / ℓ with hρdef
  have hexp : ∀ i, ∀ m : ℕ, Complex.exp (((m : ℝ) * ℓ : ℝ) * (ρ i - 1 / 2)) = x i ^ m :=
    fun i m => exp_mul_wolffLift ℓ hℓ0.ne' (x i) (hx0 i) (N i) m
  refine ⟨ι, hι, ρ, c, ?_, ?_, ?_, ⟨i₀, hc₀⟩, hsec, harg, hp, fun m hm =>
    (hmom m hm).congr_fun fun i => by rw [hexp i m]⟩
  · intro a b hab
    have h := hexp a 1
    rw [hab, hexp b 1, pow_one, pow_one] at h
    exact hinj h.symm
  · intro i
    rw [hρdef]
    simp only
    rw [re_wolffLift]
    have h1 := (hnorm i).1
    have h2 := (hnorm i).2
    have hl1 : 0 < Real.log ‖x i‖ := Real.log_pos (by linarith)
    have hl2 : Real.log ‖x i‖ ≤ Real.log 10 := Real.log_le_log (by linarith) h2
    have hlog100 : Real.log 100 = 2 * Real.log 10 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]; norm_num
    constructor
    · have : 0 < Real.log ‖x i‖ / ℓ := div_pos hl1 hℓ0
      linarith
    · have : Real.log ‖x i‖ / ℓ < 1 / 2 := by rw [div_lt_iff₀ hℓ0]; linarith
      linarith
  · intro T
    have hsub : {i : ι | |(ρ i).im| ≤ T} ⊆ N ⁻¹' Set.Iic ⌈(T * ℓ + Real.pi) / (2 * Real.pi)⌉₊ := by
      intro i hi
      simp only [mem_setOf_eq] at hi
      rw [hρdef] at hi
      simp only at hi
      rw [im_wolffLift] at hi
      simp only [mem_preimage, mem_Iic]
      have hπ := Real.pi_pos
      have harg' := Complex.neg_pi_lt_arg (x i)
      have hle := (abs_le.mp hi).2
      rw [div_le_iff₀ hℓ0] at hle
      have hN' : (N i : ℝ) ≤ (T * ℓ + Real.pi) / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      exact_mod_cast hN'.trans (Nat.le_ceil _)
    exact ((Set.finite_Iic _).preimage hN.injOn).subset hsub

end

end RHTower
