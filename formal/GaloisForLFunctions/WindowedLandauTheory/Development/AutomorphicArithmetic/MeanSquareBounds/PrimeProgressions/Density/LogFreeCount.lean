import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.ZeroHeightCover
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.ZeroDetectPrimeMean
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExceptionSelection
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ZeroChangeLevel

/-! Count near-right zeros of one modulus by integrating the detecting prime sums. -/

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Finset
open WindowedLandauTheory.ZeroFreeDirichlet
open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

private theorem principal_height :
    ∃ η : ℝ, 0 < η ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ), 1 - η ≤ s.re →
      IsLZero (1 : DirichletCharacter ℂ q) s → 3 ≤ |s.im| := by
  have hc := cZ_pos
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 2) (cZ / Real.log 5), by positivity, fun q _ s h1 hz => ?_⟩
  have hs : s ≠ 1 := hz.1.resolve_left (by simp)
  have hre : 0 < s.re := by linarith only [h1, min_le_left (1 / 2 : ℝ) (cZ / Real.log 5)]
  have he : (1 : DirichletCharacter ℂ 1).changeLevel (one_dvd q) = 1 :=
    (DirichletCharacter.changeLevel_eq_one_iff _).mpr rfl
  have hz₁ := (zero_changeLevel (one_dvd q) (1 : DirichletCharacter ℂ 1) hre (Or.inr hs)).1.mp
    (he.symm ▸ hz)
  by_contra! ht
  have hlog : Real.log (|s.im| + 2) ≤ Real.log 5 :=
    Real.log_le_log (by positivity) (by linarith only [ht])
  have hpos : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith only [abs_nonneg s.im])
  have hdiv := div_le_div_of_nonneg_left hc.le hpos hlog
  have hr : InRegion cZ 1 s := by
    unfold InRegion
    simp only [Nat.cast_one, one_mul]
    linarith only [h1, min_le_right (1 / 2 : ℝ) (cZ / Real.log 5), hdiv]
  exact (zfr_cZ 1 1 s hr hz₁).2.1 rfl

theorem count_param : ∃ a D C C' r₀ K₀ η : ℝ, 0 < a ∧ 0 < D ∧ 0 < C ∧ 0 < C' ∧ 0 < r₀ ∧ 0 < η ∧
    ∀ (q : ℕ) [NeZero q] (T σ r L : ℝ) (K : ℕ), 2 ≤ T → 1 - η ≤ σ → 2 * (1 - σ) ≤ r → 0 < r →
      r ≤ r₀ → 1 ≤ r * L → Real.log (q * (T + 3)) ≤ L → C' * (r * L) ≤ K → K₀ ≤ K → 1 ≤ K →
      (2 * q * (T + 1)) ^ 2 ≤ Real.exp (a * K / r) →
      ∀ Z : DirichletCharacter ℂ q → Finset ℂ,
      (∀ χ, ∀ ρ ∈ Z χ, σ ≤ ρ.re ∧ |ρ.im| ≤ T ∧ IsLZero χ ρ) →
      ∑ χ : DirichletCharacter ℂ q, (∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
        D * (1 + r * L) * Real.exp (C * K) * (K : ℝ) ^ 2 := by
  obtain ⟨η, hη, H1⟩ := principal_height
  obtain ⟨C2, hC2, H2⟩ := small_disc_zero_count
  obtain ⟨a, b, C4, C3, r0, K0, ha, hab, hC4, hC3, hr0, H3⟩ := zero_detect_prime_mean
  obtain ⟨C5, CM, hC5, hCM, H5⟩ := prime_double_mean_le
  have hb : 0 < b := ha.trans hab
  refine ⟨a, C2 * C5 * (b + CM) * b, C4, C3, min (1 / 25) r0, K0, η, ha, by positivity, hC4, hC3,
    by positivity, hη, ?_⟩
  intro q _ T σ r L K hT hσ hσr hr hrr hL hqL hK3 hK0 hK1 hN Z hZ
  have hr2 : r ≤ 1 / 25 := hrr.trans (min_le_left _ _)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hL0 : 0 ≤ L := (Real.log_nonneg (by nlinarith)).trans hqL
  set N := Real.exp (a * K / r) with hNdef
  set M := Real.exp (b * K / r) with hMdef
  have hN1 : 1 ≤ N := Real.one_le_exp (by positivity)
  have hNM : N ≤ M := Real.exp_le_exp.2 (by gcongr)
  have hmean := H5 q (T + 1) N M (by linarith) hN1 hNM hN
  have hchar : ∀ χ : DirichletCharacter ℂ q,
      Real.exp (-(C4 * K)) / r ^ 3 * (2 * (r / 2)) * (∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
      C2 * (1 + r * L) * ∫ τ in (-(T + 1))..(T + 1), ∫ y in N..M, ‖primeSum χ N y τ‖ ^ 2 / y := by
    intro χ
    refine count_by_height_cover _ _ _ _ _ _ _ (by positivity) (by linarith) (by positivity) (by positivity)
      (fun ρ hρ => ?_) ?_ (fun τ => ?_) (fun ρ hρ τ hτ => ?_)
    · have := (hZ χ ρ hρ).2.1
      linarith
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
      simp only [intervalIntegral.integral_of_le hNM]
      exact (integrable_primeSum χ N M (T + 1) hN1).integral_prod_left
    · exact intervalIntegral.integral_nonneg hNM fun y hy =>
        div_nonneg (by positivity) (by linarith [hy.1])
    · obtain ⟨z1, z3, z4⟩ := hZ χ ρ hρ
      have z2 := re_lt_one_of_isLZero z4
      have t1 := abs_sub_abs_le_abs_sub τ ρ.im
      have t2 := abs_sub_abs_le_abs_sub ρ.im τ
      rw [abs_sub_comm] at t2
      have hc : χ ≠ 1 ∨ 2 ≤ |τ| := by
        by_cases h : χ = 1
        · subst h
          have := H1 q ρ (by linarith only [hσ, z1]) z4
          right; linarith
        · exact Or.inl h
      have hlog : Real.log (q * (|τ| + 2)) ≤ L :=
        (Real.log_le_log (by positivity) (by gcongr ?_ * ?_; linarith)).trans hqL
      refine ⟨H3 q χ τ r L K ρ hc hlog hr hL (hrr.trans (min_le_right _ _)) hK3 hK0 z4
        (zero_near_sampling_line z1 z2 hσr hτ), ?_⟩
      refine (H2 q χ τ r hr hr2 _ ?_).trans ?_
      · intro z hz
        obtain ⟨y0, y5⟩ := Finset.mem_filter.1 hz
        obtain ⟨y1, -, y4⟩ := hZ χ z y0
        exact ⟨zero_near_sampling_line y1 (re_lt_one_of_isLZero y4) hσr y5, y4⟩
      · gcongr
  have hsum := Finset.sum_le_sum fun χ (_ : χ ∈ Finset.univ) => hchar χ
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [hMdef, Real.log_exp] at hmean
  have h6 := hsum.trans (mul_le_mul_of_nonneg_left hmean (by positivity))
  generalize (∑ χ : DirichletCharacter ℂ q, ∑ ρ ∈ Z χ, (analyticOrderNatAt χ.LFunction ρ : ℝ)) = S at h6 ⊢
  have he := Real.exp_pos (C4 * K)
  have h7 := mul_le_mul_of_nonneg_left h6 (show 0 ≤ Real.exp (C4 * K) * r ^ 2 by positivity)
  rw [Real.exp_neg] at h7
  calc S = Real.exp (C4 * K) * r ^ 2 * ((Real.exp (C4 * K))⁻¹ / r ^ 3 * (2 * (r / 2)) * S) := by
        field_simp
    _ ≤ _ := h7
    _ = C2 * C5 * (b * K + CM * r) * b * (1 + r * L) * Real.exp (C4 * K) * K := by
        field_simp
    _ ≤ C2 * C5 * (b * K + CM * K) * b * (1 + r * L) * Real.exp (C4 * K) * K := by
        gcongr; linarith
    _ = _ := by ring

end QH.PrimeProgressions
