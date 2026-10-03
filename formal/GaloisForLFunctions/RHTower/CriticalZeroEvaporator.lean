import Mathlib

/-!
# Exact evaporation of a critical zero by a shifted zeta pair

For real `γ`, the Dirichlet series with real weights `n^{-1/2} cos(γ log n)` on `n ≥ 2` equals
`E_γ(s) = (ζ(s + ½ − iγ) + ζ(s + ½ + iγ))/2 − 1` on `Re s > ½`
(`criticalZeroEvaporator_eq_tsum`). The function `E_γ` is holomorphic at `s = 1`
(`differentiableAt_criticalZeroEvaporator_one`) and, for `γ ≠ 0`, has a simple pole of residue `½`
at the critical point `½ + iγ` (`tendsto_mul_criticalZeroEvaporator`).

Consequently, for `0 < β ≤ 2`, adding `β` times these weights to an integer-supported weight system
changes its logarithmic-derivative series by `β E_γ`. That removes exactly the mass `β/2` from a simple
critical atom at `±γ`, introduces no pole at `s = 1`, and stays inside the class of integer-frequency
Dirichlet series.
-/

open Complex Filter Topology

namespace RHTower

/-- The shifted zeta pair `(ζ(s+½−iγ) + ζ(s+½+iγ))/2 − 1`. -/
noncomputable def criticalZeroEvaporator (γ : ℝ) (s : ℂ) : ℂ :=
  (riemannZeta (s + 1 / 2 - γ * I) + riemannZeta (s + 1 / 2 + γ * I)) / 2 - 1

lemma one_div_cexp_shift_pair (L s γ : ℂ) :
    1 / cexp (L * (s + 1 / 2 - γ * I)) + 1 / cexp (L * (s + 1 / 2 + γ * I))
      = 2 * (cexp (-(L / 2)) * cos (γ * L)) * (1 / cexp (L * s)) := by
  have h2 : 2 * (cexp (-(L / 2)) * cos (γ * L)) * (1 / cexp (L * s))
      = cexp (-(L / 2)) * (2 * cos (γ * L)) * (1 / cexp (L * s)) := by ring
  rw [h2, two_cos]
  simp only [one_div, ← exp_neg, mul_add, add_mul, ← exp_add]
  congr 1 <;> congr 1 <;> ring

lemma one_div_natCast_cpow_shift_pair (γ : ℝ) {n : ℕ} (hn : 0 < n) (s : ℂ) :
    1 / (n : ℂ) ^ (s + 1 / 2 - γ * I) + 1 / (n : ℂ) ^ (s + 1 / 2 + γ * I)
      = 2 * (((Real.sqrt n)⁻¹ * Real.cos (γ * Real.log n) : ℝ) : ℂ) * (1 / (n : ℂ) ^ s) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsqrt : (Real.sqrt n)⁻¹ = Real.exp (-(Real.log n / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast hn), Real.exp_neg]
    ring_nf
  rw [cpow_def_of_ne_zero hn0, cpow_def_of_ne_zero hn0, cpow_def_of_ne_zero hn0, hsqrt]
  push_cast
  exact one_div_cexp_shift_pair _ s γ

/-- Dirichlet series of the shifted zeta pair: coefficients `n^{-1/2} cos(γ log n)`. -/
theorem shiftedZetaPair_eq_tsum (γ : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    (riemannZeta (s + 1 / 2 - γ * I) + riemannZeta (s + 1 / 2 + γ * I)) / 2
      = ∑' n : ℕ, (((Real.sqrt n)⁻¹ * Real.cos (γ * Real.log n) : ℝ) : ℂ) * (1 / (n : ℂ) ^ s) := by
  have hre₁ : 1 < (s + 1 / 2 - γ * I).re := by simp; linarith
  have hre₂ : 1 < (s + 1 / 2 + γ * I).re := by simp; linarith
  have h₁ := zeta_eq_tsum_one_div_nat_cpow hre₁
  have h₂ := zeta_eq_tsum_one_div_nat_cpow hre₂
  have hs₁ : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (s + 1 / 2 - γ * I)) :=
    summable_one_div_nat_cpow.mpr hre₁
  have hs₂ : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (s + 1 / 2 + γ * I)) :=
    summable_one_div_nat_cpow.mpr hre₂
  rw [h₁, h₂, ← hs₁.tsum_add hs₂, div_eq_mul_inv, mul_comm, ← tsum_mul_left]
  congr 1
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e₁ : (s + 1 / 2 - γ * I) ≠ 0 := fun h => by rw [h] at hre₁; norm_num at hre₁
    have e₂ : (s + 1 / 2 + γ * I) ≠ 0 := fun h => by rw [h] at hre₂; norm_num at hre₂
    simp only [Nat.cast_zero, zero_cpow e₁, zero_cpow e₂]
    simp
  · rw [one_div_natCast_cpow_shift_pair γ hn s]
    ring

/-- The evaporator is the Dirichlet series with real weights `n^{-1/2} cos(γ log n)` on `n ≥ 2`. -/
theorem criticalZeroEvaporator_eq_tsum (γ : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    criticalZeroEvaporator γ s = ∑' n : ℕ,
      ((if n ≤ 1 then 0 else (Real.sqrt n)⁻¹ * Real.cos (γ * Real.log n) : ℝ) : ℂ) *
        (1 / (n : ℂ) ^ s) := by
  set g : ℕ → ℂ := fun n =>
    (((Real.sqrt n)⁻¹ * Real.cos (γ * Real.log n) : ℝ) : ℂ) * (1 / (n : ℂ) ^ s) with hg
  have hre₁ : 1 < (s + 1 / 2 - γ * I).re := by simp; linarith
  have hre₂ : 1 < (s + 1 / 2 + γ * I).re := by simp; linarith
  have hsum : Summable g := by
    have h := ((summable_one_div_nat_cpow.mpr hre₁).add
      (summable_one_div_nat_cpow.mpr hre₂)).mul_left (1 / 2 : ℂ)
    refine h.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e₁ : (s + 1 / 2 - γ * I) ≠ 0 := fun h => by rw [h] at hre₁; norm_num at hre₁
      have e₂ : (s + 1 / 2 + γ * I) ≠ 0 := fun h => by rw [h] at hre₂; norm_num at hre₂
      simp only [hg, Nat.cast_zero, zero_cpow e₁, zero_cpow e₂]
      simp
    · simp only [hg]
      rw [one_div_natCast_cpow_shift_pair γ hn s]
      ring
  have h1 : g 1 = 1 := by simp [hg]
  unfold criticalZeroEvaporator
  rw [shiftedZetaPair_eq_tsum γ hs, ← hg, hsum.tsum_eq_add_tsum_ite 1, h1, add_sub_cancel_left]
  congr 1
  ext n
  rcases Nat.lt_trichotomy n 1 with h | rfl | h
  · have : n = 0 := by omega
    subst this
    simp [hg]
  · simp
  · have hn : ¬ n ≤ 1 := by omega
    have hn' : n ≠ 1 := by omega
    simp [hg, hn, hn']

/-- `criticalZeroEvaporator` is holomorphic wherever neither shifted argument hits the pole; in
particular at `s = 1`. -/
theorem differentiableAt_criticalZeroEvaporator (γ : ℝ) {s : ℂ}
    (h₁ : s + 1 / 2 - γ * I ≠ 1) (h₂ : s + 1 / 2 + γ * I ≠ 1) :
    DifferentiableAt ℂ (criticalZeroEvaporator γ) s := by
  unfold criticalZeroEvaporator
  have d₁ : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (s + 1 / 2 - γ * I)) s :=
    (differentiableAt_riemannZeta h₁).comp s ((differentiableAt_id.add_const _).sub_const _)
  have d₂ : DifferentiableAt ℂ (fun s : ℂ => riemannZeta (s + 1 / 2 + γ * I)) s :=
    (differentiableAt_riemannZeta h₂).comp s ((differentiableAt_id.add_const _).add_const _)
  exact ((d₁.add d₂).div_const 2).sub_const 1

theorem differentiableAt_criticalZeroEvaporator_one (γ : ℝ) :
    DifferentiableAt ℂ (criticalZeroEvaporator γ) 1 := by
  apply differentiableAt_criticalZeroEvaporator <;> intro h <;>
    have := congrArg Complex.re h <;> norm_num at this

/-- The pole at the critical point `½ + iγ` has residue `½` (so `β · criticalZeroEvaporator`
removes the fraction `β/2` of a simple critical atom). -/
theorem tendsto_mul_criticalZeroEvaporator (γ : ℝ) (hγ : γ ≠ 0) :
    Tendsto (fun s => (s - (1 / 2 + γ * I)) * criticalZeroEvaporator γ s)
      (𝓝[≠] (1 / 2 + γ * I)) (𝓝 (1 / 2)) := by
  set ρ : ℂ := 1 / 2 + γ * I
  -- the shift `w = s + ½ − iγ` sends `ρ` to `1`, punctured to punctured
  have hw : Tendsto (fun s : ℂ => s + 1 / 2 - γ * I) (𝓝[≠] ρ) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℂ => s + 1 / 2 - γ * I) (𝓝 ρ) (𝓝 (ρ + 1 / 2 - γ * I)) :=
        ((continuous_id.add continuous_const).sub continuous_const).tendsto ρ
      have hρ : ρ + 1 / 2 - γ * I = 1 := by simp only [ρ]; ring
      rw [hρ] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs h
      apply hs
      simp only [Set.mem_singleton_iff, ρ] at h ⊢
      linear_combination h
  have hres : Tendsto (fun s : ℂ => (s - ρ) * riemannZeta (s + 1 / 2 - γ * I))
      (𝓝[≠] ρ) (𝓝 1) := by
    have := riemannZeta_residue_one.comp hw
    refine this.congr fun s => ?_
    simp only [Function.comp, ρ]
    ring_nf
  have hcont : Tendsto (fun s : ℂ => riemannZeta (s + 1 / 2 + γ * I)) (𝓝 ρ)
      (𝓝 (riemannZeta (ρ + 1 / 2 + γ * I))) := by
    have hne : ρ + 1 / 2 + γ * I ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp [ρ] at this
      exact hγ (by linarith)
    have hc : Continuous (fun s : ℂ => s + 1 / 2 + γ * I) := by fun_prop
    exact ((differentiableAt_riemannZeta hne).continuousAt.comp
      (f := fun s : ℂ => s + 1 / 2 + γ * I) hc.continuousAt).tendsto
  have hlin : Tendsto (fun s : ℂ => s - ρ) (𝓝 ρ) (𝓝 0) := by
    have := (continuous_sub_right ρ).tendsto ρ
    simpa using this
  have h2 : Tendsto (fun s : ℂ => (s - ρ) * riemannZeta (s + 1 / 2 + γ * I)) (𝓝[≠] ρ) (𝓝 0) := by
    have := (hlin.mul hcont).mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
    simpa using this
  have h3 : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) := hlin.mono_left nhdsWithin_le_nhds
  have := ((hres.add h2).div_const 2).sub h3
  refine (this.congr fun s => ?_).trans ?_
  · simp only [criticalZeroEvaporator]; ring
  · norm_num

end RHTower
