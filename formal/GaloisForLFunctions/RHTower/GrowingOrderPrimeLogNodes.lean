import GaloisForLFunctions.RHTower.ShrinkingWindowPrimeSupply
import GaloisForLFunctions.RHTower.PerronPolyExpAbsorb
import GaloisForLFunctions.RHTower.WeightedEulerPrimeNodeAssembly

/-!
# Growing-order separated prime-log node families

The power-log prime number theorem forces prime logarithms into windows
that shrink at a stretched-exponential rate — far faster than the
`1/(cR)` rate a linearly-growing node count demands.  Hence for every
`c₁ > 0` and every unit interval far enough right there are `⌊c₁R⌋ + 1`
prime logarithms with pairwise separation `1/(4(⌊c₁R⌋+1))`.

This is the node supply for the growing-order Lambert oversampling
transfer (order `⌊cR⌋+1`), whose separated-node demand is provably not
met by the `o(x)` prime number theorem.
-/

noncomputable section

namespace RHTower

open Finset

/-- **Stretched-exponential dominates linear growth**: for `a, b > 0`,
`a·(R+1) ≤ exp(b·R^{1/10})` for all sufficiently large `R`. -/
theorem exists_linear_le_exp_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      a * (R + 1) ≤ Real.exp (b * R ^ ((1 : ℝ) / 10)) := by
  set M : ℝ := a * ((Nat.factorial 10 : ℝ) * (2 / b) ^ 10) + a with hM
  have hM0 : 0 < M := by positivity
  refine ⟨(max 1 ((2 / b) * Real.log M)) ^ (10 : ℕ), by positivity, ?_⟩
  intro R hR
  have hV0 : (0 : ℝ) ≤ max 1 ((2 / b) * Real.log M) :=
    le_trans (by norm_num) (le_max_left _ _)
  have hR0 : (0 : ℝ) ≤ R := le_trans (by positivity) hR
  set u : ℝ := R ^ ((1 : ℝ) / 10) with hu
  have hu0 : (0 : ℝ) ≤ u := Real.rpow_nonneg hR0 _
  -- `u ≥ max 1 ((2/b)·log M)`
  have hVV : ((max 1 ((2 / b) * Real.log M)) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10)
      = max 1 ((2 / b) * Real.log M) := by
    rw [show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ from by norm_num]
    exact Real.pow_rpow_inv_natCast hV0 (by norm_num)
  have huge : max 1 ((2 / b) * Real.log M) ≤ u := by
    have h1 := Real.rpow_le_rpow (by positivity) hR
      (show (0 : ℝ) ≤ (1 : ℝ) / 10 by norm_num)
    rwa [hVV, ← hu] at h1
  -- `M ≤ exp(b·u/2)`
  have hlogM : Real.log M ≤ b * u / 2 := by
    have h1 : (2 / b) * Real.log M ≤ u := le_trans (le_max_right _ _) huge
    have h2 : b * ((2 / b) * Real.log M) ≤ b * u :=
      mul_le_mul_of_nonneg_left h1 hb.le
    rw [show b * ((2 / b) * Real.log M) = 2 * Real.log M from by
      field_simp] at h2
    linarith
  have hMexp : M ≤ Real.exp (b * u / 2) := by
    rw [← Real.exp_log hM0]
    exact Real.exp_le_exp.2 hlogM
  -- `a·R ≤ a·10!·(2/b)^(10 : ℕ)·exp(b·u/2)`
  have hu10 : u ^ (10 : ℕ) = R := by
    rw [hu, show ((1 : ℝ) / 10) = ((10 : ℕ) : ℝ)⁻¹ from by norm_num]
    exact Real.rpow_inv_natCast_pow hR0 (by norm_num)
  have hpow := pow_le_factorial_mul_exp_half hb hu0 10
  rw [hu10] at hpow
  have hexphalf1 : (1 : ℝ) ≤ Real.exp (b * u / 2) :=
    Real.one_le_exp (by positivity)
  -- assemble: `a·(R+1) ≤ M·exp(b·u/2) ≤ exp(b·u)`
  calc a * (R + 1)
      = a * R + a := by ring
    _ ≤ a * ((Nat.factorial 10 : ℝ) * (2 / b) ^ 10
          * Real.exp (b * u / 2))
        + a * Real.exp (b * u / 2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hpow ha.le
        · exact le_mul_of_one_le_right ha.le hexphalf1
    _ = M * Real.exp (b * u / 2) := by rw [hM]; ring
    _ ≤ Real.exp (b * u / 2) * Real.exp (b * u / 2) :=
        mul_le_mul_of_nonneg_right hMexp (Real.exp_nonneg _)
    _ = Real.exp (b * u) := by
        rw [← Real.exp_add]; congr 1; ring

/-- **Growing-order separated prime-log node families**: for every
`c₁ > 0`, all unit intervals far enough right carry `⌊c₁R⌋ + 1` prime
logarithms with pairwise separation `1/(4(⌊c₁R⌋+1))`. -/
theorem exists_separated_primeLog_nodes_growing {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∃ s : Finset ℝ, s.card = ⌊c₁ * R⌋₊ + 1 ∧
        ↑s ⊆ Set.Icc R (R + 1) ∧
        (∀ t ∈ s, ∀ u ∈ s, t ≠ u →
          1 / (4 * ((⌊c₁ * R⌋₊ : ℝ) + 1)) ≤ |t - u|) ∧
        (∀ t ∈ s, ∃ p : ℕ, p.Prime ∧ t = Real.log p) := by
  obtain ⟨c₂, K, y₀, hc₂, hK, hy₀3, hwin⟩ :=
    exists_prime_log_in_shrinking_window
  obtain ⟨Rh, hRh0, hRh⟩ :=
    exists_linear_le_exp_rpow (a := 4 * K * (c₁ + 1)) (b := c₂)
      (by positivity) hc₂
  refine ⟨max y₀ Rh, fun R hR => ?_⟩
  have hRy₀ : y₀ ≤ R := le_trans (le_max_left _ _) hR
  have hRRh : Rh ≤ R := le_trans (le_max_right _ _) hR
  have hR0 : (0 : ℝ) ≤ R := le_trans (by linarith) hRy₀
  set N : ℕ := ⌊c₁ * R⌋₊ with hN
  have hNc : (N : ℝ) ≤ c₁ * R := by
    rw [hN]; exact Nat.floor_le (by positivity)
  have hN10 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set η : ℝ := 1 / (4 * ((N : ℝ) + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]
    have hNn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  -- the master threshold `4K(c₁R+1) ≤ exp(c₂ R^{1/10})`
  have hthresh : 4 * K * (c₁ * R + 1)
      ≤ Real.exp (c₂ * R ^ ((1 : ℝ) / 10)) := by
    have h1 := hRh R hRRh
    have h2 : 4 * K * (c₁ * R + 1)
        ≤ 4 * K * (c₁ + 1) * (R + 1) := by
      have hKpos : (0 : ℝ) ≤ 4 * K := by positivity
      nlinarith [mul_nonneg hKpos hR0, hK.le, hc₁.le, hR0]
    linarith
  -- hence `K·exp(-c₂ R^{1/10}) ≤ 1/(4(c₁R+1))`
  have hKR : K * Real.exp (-(c₂ * R ^ ((1 : ℝ) / 10)))
      ≤ 1 / (4 * (c₁ * R + 1)) := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [hthresh]
  -- `1/(4(c₁R+1)) ≤ η`
  have hηlb : 1 / (4 * (c₁ * R + 1)) ≤ η := by
    rw [hη]
    apply one_div_le_one_div_of_le (by positivity)
    have : (N : ℝ) + 1 ≤ c₁ * R + 1 := by linarith
    linarith
  -- supply a prime in each shrinking window
  have hwindows : ∀ i : Fin (N + 1), ∃ p : ℕ, p.Prime ∧
      R + 4 * (1 / (4 * ((N : ℝ) + 1))) * (i : ℕ) ≤ Real.log p ∧
      Real.log p ≤ R + 4 * (1 / (4 * ((N : ℝ) + 1))) * (i : ℕ)
        + 1 / (4 * ((N : ℝ) + 1)) := by
    intro i
    set yi : ℝ := R + 4 * (1 / (4 * ((N : ℝ) + 1))) * (i : ℕ) with hyi
    have hyi_ge : R ≤ yi := by
      rw [hyi]
      have : (0 : ℝ) ≤ 4 * (1 / (4 * ((N : ℝ) + 1))) * (i : ℕ) := by
        positivity
      linarith
    have hyi_y₀ : y₀ ≤ yi := le_trans hRy₀ hyi_ge
    -- the shrinking-window threshold at `yi`
    have hyipow : R ^ ((1 : ℝ) / 10) ≤ yi ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow hR0 hyi_ge (by norm_num)
    have hEyi : K * Real.exp (-(c₂ * yi ^ ((1 : ℝ) / 10))) ≤ η := by
      have hmono : Real.exp (-(c₂ * yi ^ ((1 : ℝ) / 10)))
          ≤ Real.exp (-(c₂ * R ^ ((1 : ℝ) / 10))) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hyipow hc₂.le
        linarith
      calc K * Real.exp (-(c₂ * yi ^ ((1 : ℝ) / 10)))
          ≤ K * Real.exp (-(c₂ * R ^ ((1 : ℝ) / 10))) :=
            mul_le_mul_of_nonneg_left hmono hK.le
        _ ≤ 1 / (4 * (c₁ * R + 1)) := hKR
        _ ≤ η := hηlb
    have hηyi : K * Real.exp (-(c₂ * yi ^ ((1 : ℝ) / 10)))
        ≤ 1 / (4 * ((N : ℝ) + 1)) := by rw [← hη]; exact hEyi
    obtain ⟨p, hp, h1, h2⟩ := hwin yi (1 / (4 * ((N : ℝ) + 1)))
      hyi_y₀ (by rw [← hη]; exact hη0) (by rw [← hη]; exact hη1) hηyi
    exact ⟨p, hp, h1, h2⟩
  -- assemble via the banked node-assembly theorem
  exact exists_separated_primeLog_nodes hwindows

end RHTower
