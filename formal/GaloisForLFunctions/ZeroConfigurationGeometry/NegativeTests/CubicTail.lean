import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindowsVarySlowlyAtTheirTarget

/-!
# Quartic spline order pays cubic-logarithmic isolation

When the logarithm of the inverse isolation radius is cubic in logarithmic
height, a quartic decay order pays the floor and bump normalization. The
remaining absolute Fourier tail is at most one quarter.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- Quartic-logarithmic decay order pays an isolation floor whose logarithm is cubic. -/
theorem camera_cubic_isolation_tail_budget
    {lam β Lη ℓ c K MK ρ α q S'' T u a ε D C₀ η Sg E : ℝ} {z₀ : ℂ} {k m : ℕ}
    (hu1 : 1 ≤ u) (hTu : T = 2 * π * Real.exp u) (hlam0 : 0 < lam)
    (hβlam : β ≤ lam) (hℓ0 : 0 ≤ ℓ)
    (hc : c = 2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + Lη))
    (hK : K = c / 2 + 2) (hMK0 : 0 < MK) (hρ0 : 0 < ρ)
    (hα : α = 1 / (24 * MK * (1 + ρ))) (hα0 : 0 < α)
    (hq : q = max 0 (Real.log α⁻¹)) (hS''1 : 1 ≤ S'')
    (hu_bud : 6 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u)
    (ha : a = lam * (u / 2)) (hε : ε = β * u / 8) (hε0 : 0 < ε)
    (hD1 : 1 ≤ D) (hDup : D ≤ lam * u) (hC₀ℓ : |C₀| ≤ ℓ * D)
    (hlogη : max 0 (Real.log (1 / η)) ≤ Lη * u ^ 3) (hη0 : 0 < η)
    (hkK : K * u ^ 4 ≤ k) (hk1 : 1 ≤ k)
    (hmle : (m : ℝ) ≤ MK * u ^ 4) (hmε : (m : ℝ) / ε ≤ ρ * u ^ 3)
    (hz₀ : |z₀.im - T| ≤ T / 4) (hSg0 : 0 ≤ Sg) (hSgS'' : Sg ≤ S'')
    (htail : E * (1 + T / 4) ^ (2 * k - 2) ≤
      localCameraConst a D C₀ η ε ((4 * (1 + (m : ℝ) / ε)) ^ m) 1 * (1 + |z₀.im|) ^ 2 * Sg) :
    E ≤ 1 / 4 := by
  have hu0 : 0 < u := by linarith only [hu1]
  have hD0 : 0 < D := by linarith only [hD1]
  have hg0 := growthRate_nonneg hℓ0
  have hf0 := floorRate_nonneg hℓ0
  have hq0 : 0 ≤ q := by rw [hq]; exact le_max_left _ _
  have hlS''0 : 0 ≤ Real.log S'' := Real.log_nonneg hS''1
  obtain ⟨Cm, hCm⟩ : ∃ Cm, Cm = (4 * (1 + (m : ℝ) / ε)) ^ m := ⟨_, rfl⟩
  rw [← hCm] at htail
  have hCm0 : 0 < Cm := by rw [hCm]; positivity
  have hu13 : u ≤ u ^ 3 := by
    calc u = u * 1 := by ring
      _ ≤ u * u ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hu1) hu0.le
      _ = u ^ 3 := by ring
  have hu25 : u ^ 2 ≤ u ^ 5 := pow_le_pow_right₀ hu1 (by norm_num)
  have hlogCm : 2 * Real.log Cm ≤ u ^ 5 + 6 * MK * q * u ^ 4 := by
    rw [hCm, Real.log_pow]
    have hc4 : 1 ≤ 4 * (1 + ρ) := by linarith only [hρ0]
    have h4u : 4 * (1 + (m : ℝ) / ε) ≤ (4 * (1 + ρ) * u) ^ 3 := by
      have h1 : 4 * (1 + (m : ℝ) / ε) ≤ 4 * (1 + ρ) * u ^ 3 := by
        have hh := one_le_pow₀ (n := 3) hu1
        linarith only [hmε, hh]
      have h2 : 4 * (1 + ρ) ≤ (4 * (1 + ρ)) ^ 3 := by
        calc 4 * (1 + ρ) = (4 * (1 + ρ)) ^ 1 := by rw [pow_one]
          _ ≤ (4 * (1 + ρ)) ^ 3 := pow_le_pow_right₀ hc4 (by norm_num)
      calc _ ≤ 4 * (1 + ρ) * u ^ 3 := h1
        _ ≤ (4 * (1 + ρ)) ^ 3 * u ^ 3 := mul_le_mul_of_nonneg_right h2 (pow_nonneg hu0.le _)
        _ = _ := (mul_pow _ _ _).symm
    have hlog1 : Real.log (4 * (1 + (m : ℝ) / ε)) ≤ 3 * Real.log (4 * (1 + ρ) * u) := by
      have hh := Real.log_le_log (by positivity) h4u
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    have hlog2 := log_le_mul_add_log_inv (show 0 < 4 * (1 + ρ) * u by positivity) hα0
    have hαmul : α * (4 * (1 + ρ) * u) = u / (6 * MK) := by
      rw [hα]; field_simp; ring
    rw [hαmul] at hlog2
    have hlog3 : Real.log (4 * (1 + (m : ℝ) / ε)) ≤ u / (2 * MK) + 3 * q := by
      have hle_q : Real.log α⁻¹ ≤ q := by rw [hq]; exact le_max_right _ _
      have he : 3 * (u / (6 * MK)) = u / (2 * MK) := by field_simp; ring
      linarith only [hlog1, hlog2, hle_q, he]
    have h1ge : 1 ≤ 4 * (1 + (m : ℝ) / ε) := by
      have hh : 0 ≤ (m : ℝ) / ε := div_nonneg (Nat.cast_nonneg m) hε0.le
      linarith only [hh]
    calc 2 * ((m : ℝ) * Real.log (4 * (1 + (m : ℝ) / ε)))
        ≤ 2 * ((MK * u ^ 4) * (u / (2 * MK) + 3 * q)) := by
          have hh := mul_le_mul hmle hlog3 (Real.log_nonneg h1ge) (by positivity)
          linarith only [hh]
      _ = u ^ 5 + 6 * MK * q * u ^ 4 := by field_simp; ring
  have hGterm : 2 * (growthRate ℓ * D * (1 + Real.log D)) ≤
      2 * growthRate ℓ * lam ^ 2 * u ^ 5 := by
    have h1 : D * (1 + Real.log D) ≤ D ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left (one_add_log_le hD1) hD0.le
    have h2 : D ^ 2 ≤ (lam * u) ^ 2 := pow_le_pow_left₀ hD0.le hDup 2
    have h3 : (lam * u) ^ 2 ≤ lam ^ 2 * u ^ 5 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hu25 (sq_nonneg lam)
    have hh := mul_le_mul_of_nonneg_left ((h1.trans h2).trans h3) hg0
    linarith only [hh]
  have hFterm : 2 * (floorRate ℓ * D * (1 + Real.log D) *
      (1 + Real.log D + max 0 (Real.log (1 / η)))) ≤
      2 * floorRate ℓ * lam ^ 2 * (lam + Lη) * u ^ 5 := by
    have h1 : 1 + Real.log D ≤ lam * u := (one_add_log_le hD1).trans hDup
    have h2 : 1 + Real.log D + max 0 (Real.log (1 / η)) ≤ (lam + Lη) * u ^ 3 := by
      have hh := mul_le_mul_of_nonneg_left hu13 hlam0.le
      linarith only [h1, hlogη, hh]
    have h3 : D * (1 + Real.log D) ≤ lam ^ 2 * u ^ 2 := by
      calc D * (1 + Real.log D) ≤ (lam * u) * (lam * u) :=
            mul_le_mul hDup h1 (by linarith only [Real.log_nonneg hD1]) (by positivity)
        _ = lam ^ 2 * u ^ 2 := by ring
    have h4 : D * (1 + Real.log D) * (1 + Real.log D + max 0 (Real.log (1 / η))) ≤
        lam ^ 2 * (lam + Lη) * u ^ 5 := by
      calc D * (1 + Real.log D) * (1 + Real.log D + max 0 (Real.log (1 / η)))
          ≤ (lam ^ 2 * u ^ 2) * ((lam + Lη) * u ^ 3) :=
            mul_le_mul h3 h2
              (by linarith only [Real.log_nonneg hD1, le_max_left 0 (Real.log (1 / η))])
              (by positivity)
        _ = lam ^ 2 * (lam + Lη) * u ^ 5 := by ring
    have hh := mul_le_mul_of_nonneg_left h4 hf0
    linarith only [hh]
  have hB := localCameraConst_subspacing_le (a := a) (ε := ε) hD1 hC₀ℓ hη0 hCm0
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = 2 * (growthRate ℓ * D * (1 + Real.log D)) +
      2 * Real.log Cm + 2 * ε + a +
      2 * (floorRate ℓ * D * (1 + Real.log D) *
        (1 + Real.log D + max 0 (Real.log (1 / η)))) := ⟨_, rfl⟩
  rw [← hΦ] at hB
  have h2εa : 2 * ε + a ≤ lam * u := by
    rw [hε, ha]
    have hh : β * u ≤ lam * u := mul_le_mul_of_nonneg_right hβlam hu0.le
    linarith only [hh, mul_nonneg hlam0.le hu0.le]
  have hΦle : Φ ≤ (c + 1) * u ^ 5 + 6 * MK * q * u ^ 4 + lam * u := by
    rw [hΦ, hc]
    linarith only [hGterm, hFterm, hlogCm, h2εa]
  have hY := one_add_abs_im_sq_le hu1 hTu hz₀
  have hlog605 : Real.log 605 ≤ 605 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 605)
    linarith only [this]
  have h4prod : 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg) ≤
      Real.exp (Φ + 2 * u + Real.log S'' + Real.log 605) := by
    calc 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg)
        ≤ 4 * (5 / 4 * Real.exp Φ * (121 * Real.exp (2 * u)) * S'') := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul (mul_le_mul hB hY (by positivity) (by positivity)) hSgS'' hSg0
            (by positivity)
      _ = Real.exp (Real.log 605) * Real.exp Φ * Real.exp (2 * u) * Real.exp (Real.log S'') := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 605), Real.exp_log (by linarith only [hS''1])]
          ring
      _ = Real.exp (Φ + 2 * u + Real.log S'' + Real.log 605) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
  have hexp_cmp : Φ + 2 * u + Real.log S'' + Real.log 605 ≤ 2 * ((k : ℝ) - 1) * u := by
    have hk_low : (c + 4) * u ^ 5 - 2 * u ≤ 2 * ((k : ℝ) - 1) * u := by
      have h1 : 2 * (K * u ^ 4 - 1) * u ≤ 2 * ((k : ℝ) - 1) * u :=
        mul_le_mul_of_nonneg_right (by linarith only [hkK]) hu0.le
      rw [hK] at h1
      linarith only [h1]
    have hu2 : u ≤ u ^ 4 := by
      calc u = u ^ 1 := by rw [pow_one]
        _ ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
    have h1u2 : 1 ≤ u ^ 4 := hu1.trans hu2
    have hrem : 6 * MK * q * u ^ 4 + (lam + 4) * u + (Real.log S'' + 605) ≤ u ^ 5 := by
      have hlin1 : (lam + 4) * u ≤ (lam + 4) * u ^ 4 :=
        mul_le_mul_of_nonneg_left hu2 (by positivity)
      have hlin2 : Real.log S'' + 605 ≤ (Real.log S'' + 605) * u ^ 4 :=
        le_mul_of_one_le_right (by positivity) h1u2
      have hsum : (6 * MK * q + (lam + 4) + (Real.log S'' + 605)) * u ^ 4 ≤ u * u ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith only [hu_bud]) (pow_nonneg hu0.le 4)
      linarith only [hlin1, hlin2, hsum]
    linarith only [hΦle, hlog605, hk_low, hrem, pow_nonneg hu0.le 5]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (1 + T / 4) ^ (2 * k - 2) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ, hTu]; positivity
  have h4bound : 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg) ≤ Q := by
    rw [hQ]
    exact (h4prod.trans (Real.exp_le_exp.mpr hexp_cmp)).trans (exp_le_one_add_quarter_pow hTu hk1)
  rw [← hQ] at htail
  have h4tail : 4 * E * Q ≤ 1 * Q := by
    calc 4 * E * Q = 4 * (E * Q) := by ring
      _ ≤ Q := (mul_le_mul_of_nonneg_left htail (by norm_num)).trans h4bound
      _ = 1 * Q := (one_mul Q).symm
  have h4E : 4 * E ≤ 1 := le_of_mul_le_mul_right h4tail hQ0
  linarith only [h4E]


/-- A quartic decay order and the same density-controlled spline order fit a quartic bound. -/
theorem quartic_camera_order_facts {K MK e lam β ρ u ε D W : ℝ} {k m : ℕ}
    (hK1 : 2 ≤ K) (he0 : 0 ≤ e) (hlam0 : 0 < lam) (hβ0 : 0 < β)
    (hMK : MK = e * lam + K + 2) (hρ : ρ = 8 * MK / β)
    (hu1 : 1 ≤ u) (hε : ε = β * u / 8) (hDup : D ≤ lam * u)
    (hW0 : 0 ≤ W) (hWle : W ≤ e * D) (hk : k = ⌈K * u ^ 4⌉₊)
    (hm : m = ⌈W⌉₊ + k) :
    K * u ^ 4 ≤ k ∧ 1 ≤ k ∧ W + (k : ℝ) ≤ m ∧
      (m : ℝ) ≤ MK * u ^ 4 ∧ (m : ℝ) / ε ≤ ρ * u ^ 3 := by
  have hu0 : 0 < u := by linarith only [hu1]
  have hK0 : 0 ≤ K := by linarith only [hK1]
  have hu41 : 1 ≤ u ^ 4 := one_le_pow₀ hu1
  have hu4 : u ≤ u ^ 4 := by
    calc u = u ^ 1 := by rw [pow_one]
      _ ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hkK : K * u ^ 4 ≤ k := by rw [hk]; exact Nat.le_ceil _
  have hkle : (k : ℝ) ≤ K * u ^ 4 + 1 := by
    rw [hk]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : 1 ≤ k := by
    have hh : (1 : ℝ) ≤ K * u ^ 4 :=
      one_le_mul_of_one_le_of_one_le (by linarith only [hK1]) hu41
    exact_mod_cast hh.trans hkK
  have hmle : (m : ℝ) ≤ MK * u ^ 4 := by
    rw [hm, hMK]
    push_cast
    have h1 : (⌈W⌉₊ : ℝ) ≤ W + 1 := (Nat.ceil_lt_add_one hW0).le
    have h2 : e * D ≤ e * (lam * u) := mul_le_mul_of_nonneg_left hDup he0
    have h3 := mul_le_mul_of_nonneg_left hu4 (mul_nonneg he0 hlam0.le)
    linarith only [h1, hWle, h2, h3, hkle, hu41]
  refine ⟨hkK, hk1, ?_, hmle, ?_⟩
  · rw [hm]; push_cast; linarith only [Nat.le_ceil W]
  · have hε0 : 0 < ε := by rw [hε]; positivity
    rw [div_le_iff₀ hε0, hρ, hε]
    have he : 8 * MK / β * u ^ 3 * (β * u / 8) = MK * u ^ 4 := by
      field_simp
    rw [he]
    exact hmle

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.camera_cubic_isolation_tail_budget
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.quartic_camera_order_facts
