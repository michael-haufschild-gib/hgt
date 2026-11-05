import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheConeIsPinnedAtEveryAtom
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheMarginLawOfTheWindowCone
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowConeCollapses
import GaloisForLFunctions.FrustratedArithmeticDirichletForms.FrustrationCannotBeSwitchedAway

/-!
# The bands of the cone

The band of `λ(n)` over `𝒜(c)` is an interval (`ordConnected_bandSet`), with both widths controlled:

* its width is at least `λ*(c) √n`, the inradius of the cone (`exists_band_width_ge`);
* any two of its points differ by at most `C exp(K n − c/1104)` (`abs_sub_le_of_mem_bandSet`).

So the coordinate maps of the cone are intervals shrinking at an explicit rate, and the margin is bounded by the
band: `λ*(c) √n ≤ C exp(K n − c/1104)` (`exists_bestMargin_mul_sqrt_le`).

The signs of the weights are forced from a finite window on: a prime power has positive weight on every point of
the cone (`exists_forall_ge_weight_pos`). Hence frustration is a property of the whole cone, and not only of `Λ`:
past `½ log 2` every point of `𝒜(c)` is frustrated in every sign gauge in the odd sector
(`exists_odd_frustrated_on_cone`), and past `log ρ` in the even sector, with no weight at all
(`even_frustrated_on_cone`).
-/

open MeasureTheory Filter Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

open _root_.RHTower _root_.RHTower.WeilSpectral FrustratedArithmeticDirichletForms

/-- The band of a coordinate is an interval: the cone is convex. -/
theorem ordConnected_bandSet {c : ℝ} (n : ℕ) : (bandSet c n).OrdConnected := by
  refine ordConnected_iff.mpr ?_
  sorry

/-- **The bands close at a rate.** -/
theorem exists_abs_sub_le_of_mem_bandSet :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (c : ℝ) (n : ℕ), 2 ≤ c → 2 ≤ n →
      (n : ℝ) ≤ Real.exp (2 * (c - 1 / 12)) → ∀ t₁ ∈ bandSet c n, ∀ t₂ ∈ bandSet c n,
        |t₁ - t₂| ≤ C * Real.exp (K * n - c / 1104) := by
  obtain ⟨C, K, hC, hK, h⟩ := exists_abs_sub_le_of_mem_cone
  refine ⟨C, K, hC, hK, fun c n hc hn hin t₁ ht₁ t₂ ht₂ => ?_⟩
  obtain ⟨lam, hlam, rfl⟩ := ht₁
  obtain ⟨lam', hlam', rfl⟩ := ht₂
  exact h c lam lam' hc hlam hlam' n hn hin

/-- **The margin is bounded by the band.** -/
theorem exists_bestMargin_mul_sqrt_le :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (c : ℝ) (n : ℕ), 2 ≤ c → 2 ≤ n →
      (n : ℝ) ≤ Real.exp (2 * (c - 1 / 12)) →
        bestMargin c * Real.sqrt n ≤ C * Real.exp (K * n - c / 1104) := by
  obtain ⟨C, K, hC, hK, h⟩ := exists_abs_sub_le_of_mem_bandSet
  refine ⟨C, K, hC, hK, fun c n hc hn hin => ?_⟩
  have hup : 0 ≤ C * Real.exp (K * n - c / 1104) := by positivity
  by_cases hm : 0 ≤ bestMargin c
  · obtain ⟨lam, hlam⟩ := exists_hasMargin_bestMargin (c := c) (by linarith)
    obtain ⟨t₁, h₁, t₂, h₂, e⟩ := exists_band_width_ge hlam hm hn
    have := h c n hc hn hin t₂ h₂ t₁ h₁
    rw [e] at this
    exact (le_abs_self _).trans this
  · have hq := Real.sqrt_nonneg (n : ℝ)
    have : bestMargin c * Real.sqrt n ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_le.mp hm).le hq
    linarith

/-- **The sign of a prime-power weight is forced.** If `Λ(n) > 0`, every point of `𝒜(c)` has `λ(n) > 0` from a
finite window on. -/
theorem exists_forall_ge_weight_pos {n : ℕ} (hn : 2 ≤ n)
    (hΛ : 0 < (ArithmeticFunction.vonMangoldt n : ℝ)) :
    ∃ c₀ : ℝ, 2 ≤ c₀ ∧ ∀ c, c₀ ≤ c → ∀ lam : ℕ → ℝ, WeilPositiveFullUpTo lam c → 0 < lam n := by
  obtain ⟨C, K, hC, hK, h⟩ := exists_abs_sub_vonMangoldt_le_exp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = max (2 + Real.log n)
      (1104 * (K * n + Real.log (C + 1) - Real.log (ArithmeticFunction.vonMangoldt n : ℝ) + 1)) :=
    ⟨_, rfl⟩
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  refine ⟨c₀, ?_, fun c hc lam hlam => ?_⟩
  · rw [hc₀]
    exact le_trans (by linarith) (le_max_left _ _)
  have hc2 : 2 + Real.log n ≤ c := le_trans (by rw [hc₀]; exact le_max_left _ _) hc
  have hc3 : 1104 * (K * n + Real.log (C + 1) - Real.log (ArithmeticFunction.vonMangoldt n : ℝ) + 1) ≤ c :=
    le_trans (by rw [hc₀]; exact le_max_right _ _) hc
  have hin : (n : ℝ) ≤ Real.exp (2 * (c - 1 / 12)) := by
    rw [← Real.log_le_iff_le_exp (by linarith)]
    linarith
  have hb := h c lam (by linarith) hlam n hn hin
  have hexp : C * Real.exp (K * n - c / 1104) < (ArithmeticFunction.vonMangoldt n : ℝ) := by
    have hC1 : 0 < C + 1 := by linarith
    have h1 : C ≤ C + 1 := by linarith
    have e : (C + 1) * Real.exp (K * n - c / 1104) < (ArithmeticFunction.vonMangoldt n : ℝ) := by
      have h2 : (C + 1) * Real.exp (K * n - c / 1104) =
          Real.exp (Real.log (C + 1) + (K * n - c / 1104)) := by
        rw [Real.exp_add, Real.exp_log hC1]
      rw [h2, ← Real.lt_log_iff_exp_lt hΛ]
      linarith
    have hE := Real.exp_pos (K * n - c / 1104)
    nlinarith
  have := (abs_lt.mp (lt_of_le_of_lt hb hexp)).1
  linarith

/-- **The whole cone is frustrated in the odd sector.** From a finite window on, every point of `𝒜(c)` has a
positive second weight, and every sign gauge is frustrated. -/
theorem exists_odd_frustrated_on_cone :
    ∃ c₀ : ℝ, Real.log 2 / 2 < c₀ ∧ ∀ c, c₀ ≤ c → ∀ lam : ℕ → ℝ, WeilPositiveFullUpTo lam c →
      ∀ σ : ℝ → ℝ, IsSignGauge σ → ∃ u ∈ Ioo (-c) 0, ∃ v ∈ Ioo (-c) 0, u ≠ v ∧
        (σ u * σ v * oddSectorKernel u v < 0 ∨
          (u + v = -Real.log 2 ∧ σ u * σ v * (-(lam 2 / Real.sqrt 2)) < 0)) := by
  have hΛ : 0 < (ArithmeticFunction.vonMangoldt 2 : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact Real.log_pos (by norm_num)
  obtain ⟨c₀, hc₀, h⟩ := exists_forall_ge_weight_pos (le_refl 2) hΛ
  have hl : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  refine ⟨c₀, by linarith, fun c hc lam hlam σ hσ => ?_⟩
  have hw : 0 < lam 2 / Real.sqrt 2 := div_pos (h c hc lam hlam) (by positivity)
  exact odd_frustrated_in_every_sign_gauge (by linarith) hw hσ

/-- The even sector is frustrated past `log ρ`, with no weight at all. -/
theorem even_frustrated_on_cone {c : ℝ} (hc : screwSignThreshold < c) {σ : ℝ → ℝ}
    (hσ : IsSignGauge σ) :
    ∃ u ∈ Icc (-c) 0, ∃ v ∈ Icc (-c) 0, u ≠ v ∧ σ u * σ v * evenSectorKernel u v < 0 :=
  even_frustrated_in_every_sign_gauge hc hσ

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
