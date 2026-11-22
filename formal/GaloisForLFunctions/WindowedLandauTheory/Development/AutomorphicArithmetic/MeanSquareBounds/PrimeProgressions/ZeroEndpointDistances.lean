import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.NoZeroComplex
import GaloisForLFunctions.RHTower.SiegelZeroFree
import GaloisForLFunctions.RHTower.TwistedOrderLawExact

/-! The two denominators of the primitive zero kernel are uniformly separated from zero. -/

open Complex

noncomputable section

namespace QH.PrimeProgressions

open WindowedLandauTheory.ZeroFreeDirichlet

private theorem zero_dist_one :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ),
      χ ≠ 1 → χ.LFunction ρ = 0 → c / N ≤ ‖1 - ρ‖ := by
  obtain ⟨a, ha, hZ⟩ := zFRDirichlet
  obtain ⟨b, hb, hS⟩ := RHTower.siegel_zero_free (ε := 1) one_pos
  let c := min 1 (min (a / 3) b)
  have hc : 0 < c := lt_min one_pos (lt_min (by positivity) hb)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hca : c ≤ a / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, fun N _ χ ρ hχ hρ => ?_⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hN₀ : (0 : ℝ) < N := by linarith
  have hre : 1 - ρ.re ≤ ‖1 - ρ‖ := by
    simpa only [sub_re, one_re] using re_le_norm ((1 : ℂ) - ρ)
  by_cases him : 1 ≤ |ρ.im|
  · have he : |(1 - ρ).im| = |ρ.im| := by simp
    calc c / N ≤ 1 := (div_le_self hc.le hN).trans hc1
      _ ≤ |ρ.im| := him
      _ ≤ ‖1 - ρ‖ := he ▸ abs_im_le_norm ((1 : ℂ) - ρ)
  by_cases hreg : InRegion a N ρ
  · obtain ⟨hχ₂, -, him₀, -, -⟩ := hZ N χ ρ hreg ⟨Or.inl hχ, hρ⟩
    have hρe : ((ρ.re : ℝ) : ℂ) = ρ := Complex.ext (by simp) (by simp [him₀])
    have hβ : ρ.re ≤ 1 - b / N := by
      by_contra! h
      have hβ' : 1 - b * (N : ℝ) ^ (-(1 : ℝ)) < ρ.re := by
        simpa only [Real.rpow_neg_one, div_eq_mul_inv] using h
      exact hS N χ hχ₂ hχ ρ.re hβ' (by rwa [hρe])
    exact (div_le_div_of_nonneg_right hcb hN₀.le).trans ((by linarith : b / N ≤ 1 - ρ.re).trans hre)
  · have hLpos := log_mul_abs_add_two_pos N ρ.im
    have harg : (N : ℝ) * (|ρ.im| + 2) ≤ 3 * N :=
      (mul_le_mul_of_nonneg_left (show |ρ.im| + 2 ≤ (3 : ℝ) by
        linarith only [lt_of_not_ge him]) hN₀.le).trans_eq (mul_comm _ _)
    have hL := Real.log_le_sub_one_of_pos
      (show 0 < (N : ℝ) * (|ρ.im| + 2) by positivity)
    have hL' : Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ 3 * N := by linarith
    have hcut : ρ.re < 1 - a / Real.log ((N : ℝ) * (|ρ.im| + 2)) :=
      lt_of_not_ge hreg
    calc c / N ≤ (a / 3) / N := div_le_div_of_nonneg_right hca hN₀.le
      _ = a / (3 * N) := div_div _ _ _
      _ ≤ a / Real.log ((N : ℝ) * (|ρ.im| + 2)) :=
        div_le_div_of_nonneg_left ha.le hLpos hL'
      _ ≤ 1 - ρ.re := by linarith
      _ ≤ ‖1 - ρ‖ := hre

/-- Reflection transfers the right-endpoint estimate to the left endpoint. -/
theorem primitive_zero_endpoint_distances :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ),
      χ ≠ 1 → χ.IsPrimitive → χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      c / N ≤ ‖ρ‖ ∧ c / N ≤ ‖1 - ρ‖ := by
  obtain ⟨c, hc, h⟩ := zero_dist_one
  refine ⟨c, hc, fun N _ χ ρ hχ hp hρ hρ₀ hρ₁ => ⟨?_, h N χ ρ hχ hρ⟩⟩
  have hρ' := RHTower.LFunction_eq_zero_conj_one_sub hχ hp hρ hρ₀ hρ₁
  have hn := h N χ ((starRingEnd ℂ) (1 - ρ)) hχ hρ'
  have he : (1 : ℂ) - (starRingEnd ℂ) (1 - ρ) = (starRingEnd ℂ) ρ := by
    rw [map_sub, map_one]
    ring
  simpa only [he, Complex.norm_conj] using hn

end QH.PrimeProgressions
