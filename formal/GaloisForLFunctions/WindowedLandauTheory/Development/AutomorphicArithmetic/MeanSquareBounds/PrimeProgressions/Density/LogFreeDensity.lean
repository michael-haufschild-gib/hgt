import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.LogFreeCount

/-! The log-free zero-density estimate at one modulus, with multiplicities. -/

open Complex DirichletCharacter Finset WindowedLandauTheory.ZeroFreeDirichlet

namespace QH.PrimeProgressions

theorem log_free_zero_density : ∃ A C η : ℝ, 0 < A ∧ 0 < C ∧ 0 < η ∧ ∀ (q : ℕ) [NeZero q] (T σ : ℝ), 2 ≤ T → 1 - η ≤ σ → σ ≤ 1 →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
      (∀ χ, ∀ ρ ∈ Z χ, σ ≤ ρ.re ∧ |ρ.im| ≤ T ∧ IsLZero χ ρ) →
      ∑ χ : DirichletCharacter ℂ q, (∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ C * ((q : ℝ) * T) ^ (A * (1 - σ)) := by
  obtain ⟨a, D, C, C3, r0, K0, η, ha, hD, hC, hC3, hr0, hη, H⟩ := count_param
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = C3 + |K0| + 4 / a := ⟨_, rfl⟩
  have hK0 := abs_nonneg K0
  have h4a : 0 < 4 / a := by positivity
  have hE0 : 0 < E := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * (E + 1) + 3 := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  refine ⟨6 * B, D * (E + 1) ^ 2 * Real.exp (2 * B), min η (r0 / 2), by positivity, by positivity,
    by positivity, fun q _ T σ hT hσ hσ1 Z hZ => ?_⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have m1 := min_le_left η (r0 / 2)
  have m2 := min_le_right η (r0 / 2)
  have hl0 : 0 ≤ Real.log (q * (T + 3)) := Real.log_nonneg (by nlinarith)
  have hir : 0 < 1 / r0 := by positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (q * (T + 3)) + 1 / r0 := ⟨_, rfl⟩
  have hL0 : 0 < L := by linarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = max (2 * (1 - σ)) (1 / L) := ⟨_, rfl⟩
  have r1 : 2 * (1 - σ) ≤ r := hr ▸ le_max_left _ _
  have r2 : 1 / L ≤ r := hr ▸ le_max_right _ _
  have r3 : 0 < r := lt_of_lt_of_le (by positivity) r2
  have r4 : r ≤ r0 := by
    rw [hr]
    refine max_le (by linarith) ?_
    rw [div_le_comm₀ hL0 hr0]; linarith
  have x1 : 1 ≤ r * L := (div_le_iff₀ hL0).1 r2
  have hlT : Real.log (q * (T + 3)) ≤ 3 * Real.log (q * T) := by
    have hT2 : 4 ≤ T ^ 2 := calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ T ^ 2 := pow_le_pow_left₀ (by norm_num) hT 2
    have h3 : T + 3 ≤ T ^ 3 := calc
      T + 3 ≤ 4 * T := by linarith only [hT]
      _ ≤ T ^ 2 * T := mul_le_mul_of_nonneg_right hT2 (by linarith only [hT])
      _ = _ := by ring
    have h4 : (q : ℝ) ≤ q ^ 3 := le_self_pow₀ hq (by norm_num)
    calc _ ≤ Real.log ((q * T) ^ 3) := by
          refine Real.log_le_log (by positivity) ?_
          rw [mul_pow]; gcongr
      _ = _ := by rw [Real.log_pow]; norm_num
  have x2 : r * L ≤ 2 + 6 * (1 - σ) * Real.log (q * T) := by
    have s0 : 0 ≤ 1 - σ := by linarith
    have s1 : 2 * (1 - σ) * (1 / r0) ≤ 1 := by
      rw [mul_one_div, div_le_one hr0]; linarith
    have s2 := mul_le_mul_of_nonneg_left hlT s0
    have s3 := mul_nonneg s0 hl0
    rcases max_choice (2 * (1 - σ)) (1 / L) with h | h
    · rw [hr, h, hL]; nlinarith
    · rw [hr, h, one_div_mul_cancel hL0.ne']; nlinarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈E * (r * L)⌉₊ := ⟨_, rfl⟩
  have k1 : E * (r * L) ≤ K := hK ▸ Nat.le_ceil _
  have k2 : (K : ℝ) ≤ (E + 1) * (r * L) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ E * (r * L) by positivity)
    rw [← hK] at this
    linarith
  have k3 : 1 ≤ K := by
    have : (0 : ℝ) < K := lt_of_lt_of_le (by positivity) k1
    exact_mod_cast this
  have hN : (2 * q * (T + 1)) ^ 2 ≤ Real.exp (a * K / r) := by
    have n1 : 4 * L ≤ a * K / r := by
      rw [le_div_iff₀ r3]
      have : 4 / a * (r * L) ≤ K := le_trans (by gcongr; linarith) k1
      have := mul_le_mul_of_nonneg_left this ha.le
      calc 4 * L * r = a * (4 / a * (r * L)) := by field_simp
        _ ≤ _ := this
    have n2 : 2 * q * (T + 1) ≤ (q * (T + 3)) ^ 2 := by
      have : (q : ℝ) ≤ q ^ 2 := by nlinarith
      have : 2 * (T + 1) ≤ (T + 3) ^ 2 := by nlinarith
      calc 2 * q * (T + 1) = q * (2 * (T + 1)) := by ring
        _ ≤ q ^ 2 * (T + 3) ^ 2 := by gcongr
        _ = _ := by ring
    calc _ ≤ ((q * (T + 3)) ^ 2) ^ 2 := by gcongr
      _ = Real.exp (Real.log (q * (T + 3))) ^ 4 := by rw [Real.exp_log (by positivity)]; ring
      _ = Real.exp (4 * Real.log (q * (T + 3))) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := Real.exp_le_exp.2 (by linarith)
  have k4 : C3 * (r * L) ≤ K := by
    exact le_trans (by gcongr; linarith) k1
  have k5 : K0 ≤ K := by
    have := le_abs_self K0
    have : E * 1 ≤ E * (r * L) := by gcongr
    linarith
  refine (H q T σ r L K hT (by linarith) r1 r3 r4 x1 (by linarith) k4 k5 k3 hN Z hZ).trans ?_
  generalize r * L = x at *
  have e1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have e2 : x ≤ Real.exp x := by linarith
  have hKexp : (K : ℝ) ≤ (E + 1) * Real.exp x :=
    k2.trans (mul_le_mul_of_nonneg_left e2 (by positivity))
  calc _ ≤ D * Real.exp x * Real.exp (C * ((E + 1) * x)) * ((E + 1) * Real.exp x) ^ 2 := by
        gcongr
    _ = D * (E + 1) ^ 2 * Real.exp (B * x) := by
        rw [show B * x = x + C * ((E + 1) * x) + x + x by rw [hB]; ring]
        simp only [Real.exp_add]; ring
    _ ≤ D * (E + 1) ^ 2 * Real.exp (B * (2 + 6 * (1 - σ) * Real.log (q * T))) := by gcongr
    _ = _ := by
        rw [Real.rpow_def_of_pos (by positivity), mul_assoc _ (Real.exp _), ← Real.exp_add]
        congr 2; ring

end QH.PrimeProgressions
