import GaloisForLFunctions.RHTower.MassBesselRadiationDivergence

/-!
# The exact scale of the finite radiation apertures

Along the deep-time ray the modulus of the spectral parameter is asymptotically the fourth power of
the logarithm, so the order-`m` radiation remainder has the exact scale `√X (log X)^{-2m-2}`, with a
limiting coefficient that is the extremal Poincaré coefficient times the dyadic prime constant times
the deep-time amplitude.  In particular the coefficient does not vanish.
-/

open Filter ArithmeticFunction HTGeometry
open scoped Topology BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem tendsto_norm_spectralPoint_div (σ : ℝ) :
    Tendsto (fun X : ℝ => ‖apertureSpectralPoint σ (Real.log X ^ 4)‖ / Real.log X ^ 4)
      atTop (𝓝 1) := by
  have hinner : Tendsto (fun X : ℝ => σ ^ 2 / (Real.log X ^ 4) ^ 2 + 1) atTop (𝓝 1) := by
    have hd : Tendsto (fun X : ℝ => (Real.log X ^ 4) ^ 2) atTop atTop := by
      have h4 : Tendsto (fun X : ℝ => Real.log X ^ 4) atTop atTop :=
        (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
      exact (tendsto_pow_atTop (by norm_num)).comp h4
    have hz : Tendsto (fun X : ℝ => σ ^ 2 / (Real.log X ^ 4) ^ 2) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hd
    simpa using hz.add_const 1
  have hsqrt := (Real.continuous_sqrt.tendsto 1).comp hinner
  rw [Real.sqrt_one] at hsqrt
  refine hsqrt.congr' ?_
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with X hL
  have hu : (0 : ℝ) < Real.log X ^ 4 := by positivity
  have hnorm : ‖apertureSpectralPoint σ (Real.log X ^ 4)‖
      = Real.sqrt (σ ^ 2 + (Real.log X ^ 4) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (apertureSpectralPoint σ (Real.log X ^ 4))),
      norm_spectralPoint_sq]
  rw [Function.comp_apply, hnorm]
  rw [show σ ^ 2 / (Real.log X ^ 4) ^ 2 + 1
      = (σ ^ 2 + (Real.log X ^ 4) ^ 2) / (Real.log X ^ 4) ^ 2 by field_simp]
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hu.le]

theorem eventually_massle : ∀ᶠ X : ℝ in atTop,
    dyadicSqrtVonMangoldtMass X ≤ 2 * Real.sqrt X := by
  have hlim := tendsto_dyadicSqrtVonMangoldtMass_div_sqrt
  have hlt : 2 * (Real.sqrt 2 - 1) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hev := Tendsto.eventually_le_const hlt hlim
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with X hX hX1
  have hs : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
  rw [div_le_iff₀ hs] at hX
  linarith

/-- The order-`(m+1)` remainder is eventually smaller than the leading scale by a further
logarithmic square. -/
theorem exists_eventually_norm_radiationRemainder_succ_le (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ)
    (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ X : ℝ in atTop,
      ‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) (m + 1) (Real.log X ^ 4)‖
        ≤ 2 * Real.sqrt X * (D / Real.log X ^ (2 * m + 4)) := by
  obtain ⟨D, hD0, hD⟩ := exists_shellBound_le a σ ha hσ m
  refine ⟨D, hD0, ?_⟩
  filter_upwards [eventually_shellHypotheses a σ ha hσ, eventually_massle,
    eventually_gt_atTop (1 : ℝ)] with X hyp hmass hX1
  obtain ⟨hL3, hu1, hσu, hlogshell, h1, h2, hc, hdefu⟩ := hyp
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hbound := norm_massBesselDyadicRadiationRemainder_le (a := a) (σ := σ) (X := X)
    (u := Real.log X ^ 4) (M := Real.log X + Real.log 2) (c := 1) ha hσ hu1 hσu hlogshell h1 h2 hc
    hdefu m (m + 1)
  have hshell := hD (Real.log X) hL1
  have hsb0 := radiationShellBound_nonneg (a := a) (σ := σ) (c := 1) (u := Real.log X ^ 4)
    (M := Real.log X + Real.log 2) ha zero_le_one (by positivity) m (m + 1)
  have hmass0 := dyadicSqrtVonMangoldtMass_nonneg X
  have hstep := mul_le_mul hmass hshell hsb0 (by positivity)
  linarith

/-- The prime mass of the extremal Poincaré coefficient, in modulus. -/
theorem tendsto_norm_dyadicPoincareMass (a : ℝ) (n' M m : ℕ) :
    Tendsto (fun X : ℝ => ‖dyadicPoincareMass a n' M m X‖
        / (Real.sqrt X * Real.log X ^ (2 * m)))
      atTop (𝓝 (‖(poincareCoeffPoly a n' M m).coeff m‖ * (2 * (Real.sqrt 2 - 1)))) := by
  have hlim := (tendsto_dyadicPoincareMass a n' M m).norm
  have hval : ‖(poincareCoeffPoly a n' M m).coeff m * ((2 * (Real.sqrt 2 - 1) : ℝ) : ℂ)‖
      = ‖(poincareCoeffPoly a n' M m).coeff m‖ * (2 * (Real.sqrt 2 - 1)) := by
    have hs2 : (1 : ℝ) < Real.sqrt 2 := by
      have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [Real.sqrt_nonneg 2]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with X hX1 hL
  have hden : (0 : ℝ) < Real.sqrt X * Real.log X ^ (2 * m) := by
    have : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
    positivity
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hden.le]

/-- The scaled remainder differs from the scaled leading term by at most the scaled error. -/
theorem abs_radiation_scale_sub_le (a σ : ℝ) (m : ℕ) {X : ℝ}
    (hL : 1 < Real.log X) (hX1 : 1 < X) :
    |‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) m (Real.log X ^ 4)‖
        * Real.log X ^ (2 * m + 2) / Real.sqrt X
      - ‖massBesselLeading a (apertureSpectralPoint σ (Real.log X ^ 4))‖ * Real.log X ^ 2
          * (‖dyadicPoincareMass a (m + 1) (m + 1) m X‖
            / (Real.sqrt X * Real.log X ^ (2 * m)))
          * (Real.log X ^ 4 / ‖apertureSpectralPoint σ (Real.log X ^ 4)‖) ^ m|
      ≤ ‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) (m + 1) (Real.log X ^ 4)‖
          * Real.log X ^ (2 * m + 2) / Real.sqrt X := by
  obtain ⟨t, htdef⟩ : ∃ t : ℂ, apertureSpectralPoint σ (Real.log X ^ 4) = t := ⟨_, rfl⟩
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLne : Real.log X ≠ 0 := ne_of_gt hL0
  have hXs : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
  have hnormt : Real.log X ^ 4 ≤ ‖t‖ := by rw [← htdef]; exact le_norm_spectralPoint σ _
  have htpos : (0 : ℝ) < ‖t‖ := by
    have : (0 : ℝ) < Real.log X ^ 4 := by positivity
    linarith
  have hsucc := massBesselDyadicRadiationRemainder_succ a σ X (m + 1) (m + 1) m (Real.log X ^ 4)
  rw [htdef] at hsucc
  have hprodeq : ‖massBesselLeading a t‖ * Real.log X ^ 2
        * (‖dyadicPoincareMass a (m + 1) (m + 1) m X‖ / (Real.sqrt X * Real.log X ^ (2 * m)))
        * (Real.log X ^ 4 / ‖t‖) ^ m
      = ‖massBesselLeading a t * (dyadicPoincareMass a (m + 1) (m + 1) m X * (t⁻¹) ^ m)‖
        * Real.log X ^ (2 * m + 2) / Real.sqrt X := by
    rw [norm_mul, norm_mul, norm_pow, norm_inv, div_pow, ← pow_mul]
    have hsplit : Real.log X ^ (2 * m + 2) = Real.log X ^ (2 * m) * Real.log X ^ 2 := by
      rw [← pow_add]
    have hsplit2 : Real.log X ^ (4 * m) = Real.log X ^ (2 * m) * Real.log X ^ (2 * m) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, hsplit2]
    have htne : ‖t‖ ≠ 0 := ne_of_gt htpos
    have hpm : ‖t‖ ^ m ≠ 0 := pow_ne_zero m htne
    obtain ⟨P, hP⟩ : ∃ P : ℝ, ‖dyadicPoincareMass a (m + 1) (m + 1) m X‖ = P := ⟨_, rfl⟩
    obtain ⟨Lc, hLc⟩ : ∃ Lc : ℝ, ‖massBesselLeading a t‖ = Lc := ⟨_, rfl⟩
    rw [hP, hLc]
    have hcancel : ‖t‖ ^ m * ((1 : ℝ) / ‖t‖) ^ m = 1 := by
      rw [← mul_pow, mul_one_div, div_self htne, one_pow]
    field_simp
    rw [mul_assoc, hcancel, mul_one]
  rw [htdef, hprodeq, ← sub_div, ← sub_mul, abs_div, abs_mul]
  have hc1 : |Real.log X ^ (2 * m + 2)| = Real.log X ^ (2 * m + 2) :=
    abs_of_nonneg (by positivity)
  have hc2 : |Real.sqrt X| = Real.sqrt X := abs_of_nonneg hXs.le
  rw [hc1, hc2]
  refine div_le_div_of_nonneg_right ?_ hXs.le
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [hsucc]
  have habs := abs_norm_sub_norm_le
    (massBesselLeading a t * (dyadicPoincareMass a (m + 1) (m + 1) m X * (t⁻¹) ^ m)
      + massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) (m + 1) (Real.log X ^ 4))
    (massBesselLeading a t * (dyadicPoincareMass a (m + 1) (m + 1) m X * (t⁻¹) ^ m))
  simpa using habs

/-- **The limiting scale coefficient is strictly positive.** -/
theorem radiationScaleConst_pos (a σ : ℝ) (ha : 0 < a) (m : ℕ) :
    0 < Real.sqrt (2 * Real.pi * a) * Real.exp (-(a * σ))
      * (‖(poincareCoeffPoly a (m + 1) (m + 1) m).coeff m‖ * (2 * (Real.sqrt 2 - 1))) := by
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hq : (poincareCoeffPoly a (m + 1) (m + 1) m).coeff m ≠ 0 := by
    rw [coeff_poincareCoeffPoly_self a (by omega) (by omega) (by omega)]
    have hfac : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hane : (-(a : ℂ) / 2) ≠ 0 := by
      simp only [ne_eq, div_eq_zero_iff, neg_eq_zero, Complex.ofReal_eq_zero]
      push Not
      exact ⟨ne_of_gt ha, by norm_num⟩
    exact mul_ne_zero (inv_ne_zero hfac) (pow_ne_zero m hane)
  have hqn : 0 < ‖(poincareCoeffPoly a (m + 1) (m + 1) m).coeff m‖ := norm_pos_iff.2 hq
  have hsa : (0 : ℝ) < Real.sqrt (2 * Real.pi * a) := Real.sqrt_pos.2 (by positivity)
  have hex : (0 : ℝ) < Real.exp (-(a * σ)) := Real.exp_pos _
  have hlast : (0 : ℝ) < 2 * (Real.sqrt 2 - 1) := by linarith
  positivity

set_option maxHeartbeats 1600000 in
/-- **The exact scale of the order-`m` radiation remainder.** -/
theorem tendsto_norm_massBesselDyadicRadiationRemainder_scale (a σ : ℝ) (ha : 0 < a)
    (hσ : 0 < σ) (m : ℕ) :
    Tendsto (fun X : ℝ =>
        ‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) m (Real.log X ^ 4)‖
          * Real.log X ^ (2 * m + 2) / Real.sqrt X)
      atTop (𝓝 (Real.sqrt (2 * Real.pi * a) * Real.exp (-(a * σ))
        * (‖(poincareCoeffPoly a (m + 1) (m + 1) m).coeff m‖ * (2 * (Real.sqrt 2 - 1))))) := by
  obtain ⟨D, hD0, hDev⟩ := exists_eventually_norm_radiationRemainder_succ_le a σ ha hσ m
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, Real.sqrt (2 * Real.pi * a) * Real.exp (-(a * σ)) = A := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      ‖(poincareCoeffPoly a (m + 1) (m + 1) m).coeff m‖ * (2 * (Real.sqrt 2 - 1)) = B := ⟨_, rfl⟩
  rw [hAdef, hBdef]
  have hnt := tendsto_norm_spectralPoint_div σ
  have hlead : Tendsto (fun X : ℝ =>
      ‖massBesselLeading a (apertureSpectralPoint σ (Real.log X ^ 4))‖ * Real.log X ^ 2)
      atTop (𝓝 A) := by
    have hsq := (Real.continuous_sqrt.tendsto 1).comp hnt
    rw [Real.sqrt_one] at hsq
    have hdiv : Tendsto (fun X : ℝ => A / Real.sqrt
        (‖apertureSpectralPoint σ (Real.log X ^ 4)‖ / Real.log X ^ 4)) atTop (𝓝 (A / 1)) :=
      tendsto_const_nhds.div hsq one_ne_zero
    rw [div_one] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with X hL
    have hL0 : (0 : ℝ) < Real.log X := by linarith
    have hu : (0 : ℝ) < Real.log X ^ 4 := by positivity
    have hre : (apertureSpectralPoint σ (Real.log X ^ 4)).re = σ := spectralPoint_re σ _
    have hrepos : 0 < (apertureSpectralPoint σ (Real.log X ^ 4)).re := by rw [hre]; exact hσ
    have hnorm : (0 : ℝ) < ‖apertureSpectralPoint σ (Real.log X ^ 4)‖ := by
      have := le_norm_spectralPoint σ (Real.log X ^ 4)
      linarith
    rw [Real.sqrt_div' _ (by positivity), sqrt_pow_four,
      norm_massBesselLeading a hrepos, hre, hAdef]
    field_simp
  have hratio : Tendsto (fun X : ℝ =>
      (Real.log X ^ 4 / ‖apertureSpectralPoint σ (Real.log X ^ 4)‖) ^ m) atTop (𝓝 1) := by
    have hinv : Tendsto (fun X : ℝ =>
        (‖apertureSpectralPoint σ (Real.log X ^ 4)‖ / Real.log X ^ 4)⁻¹) atTop (𝓝 1) := by
      simpa using hnt.inv₀ one_ne_zero
    have hcong : Tendsto (fun X : ℝ =>
        Real.log X ^ 4 / ‖apertureSpectralPoint σ (Real.log X ^ 4)‖) atTop (𝓝 1) := by
      refine hinv.congr' ?_
      filter_upwards with X
      rw [inv_div]
    simpa using hcong.pow m
  have hmassn := tendsto_norm_dyadicPoincareMass a (m + 1) (m + 1) m
  rw [hBdef] at hmassn
  have hprod := (hlead.mul hmassn).mul hratio
  rw [mul_one] at hprod
  have herr : Tendsto (fun X : ℝ =>
      ‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) (m + 1) (Real.log X ^ 4)‖
        * Real.log X ^ (2 * m + 2) / Real.sqrt X) atTop (𝓝 0) := by
    have hmaj : Tendsto (fun X : ℝ => 2 * D / Real.log X ^ 2) atTop (𝓝 0) := by
      have hpow : Tendsto (fun X : ℝ => Real.log X ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop
      exact Filter.Tendsto.div_atTop tendsto_const_nhds hpow
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [eventually_gt_atTop (1 : ℝ),
        Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with X hX1 hL
      have hs : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
      exact div_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hL.le _)) hs.le
    · filter_upwards [hDev, Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ),
        eventually_gt_atTop (1 : ℝ)] with X hb hL hX1
      have hL0 : (0 : ℝ) < Real.log X := by linarith
      have hXs : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
      have hsplit : Real.log X ^ (2 * m + 4)
          = Real.log X ^ (2 * m + 2) * Real.log X ^ 2 := by rw [← pow_add]
      have hstep : 2 * Real.sqrt X * (D / Real.log X ^ (2 * m + 4))
            * Real.log X ^ (2 * m + 2) / Real.sqrt X = 2 * D / Real.log X ^ 2 := by
        rw [hsplit]
        field_simp
      calc ‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) (m + 1) (Real.log X ^ 4)‖
            * Real.log X ^ (2 * m + 2) / Real.sqrt X
          ≤ 2 * Real.sqrt X * (D / Real.log X ^ (2 * m + 4))
            * Real.log X ^ (2 * m + 2) / Real.sqrt X := by
            refine div_le_div_of_nonneg_right ?_ hXs.le
            exact mul_le_mul_of_nonneg_right hb (by positivity)
        _ = 2 * D / Real.log X ^ 2 := hstep
  have hlow := hprod.sub herr
  have hhigh := hprod.add herr
  rw [sub_zero] at hlow
  rw [add_zero] at hhigh
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ),
      eventually_gt_atTop (1 : ℝ)] with X hL hX1
    have h := abs_le.mp (abs_radiation_scale_sub_le a σ m hL hX1)
    linarith [h.1]
  · filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ),
      eventually_gt_atTop (1 : ℝ)] with X hL hX1
    have h := abs_le.mp (abs_radiation_scale_sub_le a σ m hL hX1)
    linarith [h.2]

end

end RHTower
