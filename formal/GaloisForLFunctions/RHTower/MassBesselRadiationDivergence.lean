import GaloisForLFunctions.RHTower.MassBesselPoincareMass

/-!
# The finite radiation apertures are not uniformly bounded

At the deep-time point `σ + i(log X)^(4 : ℕ)` the order-`m` radiation remainder of a dyadic prime aperture
is the prime mass of the `m`-th Poincaré coefficient times the `m`-th power of the reciprocal
spectral parameter, plus an error smaller by a further power of the logarithm.  Since that leading
term grows like `√X (log X)^{-2m-2}`, no finite number of radiation subtractions bounds the aperture.
-/

open Filter ArithmeticFunction HTGeometry
open scoped Topology BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

theorem tendsto_sqrt_div_log_pow_atTop (p : ℕ) :
    Tendsto (fun X : ℝ => Real.sqrt X / Real.log X ^ p) atTop atTop := by
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 p one_ne_zero
  have h1 : Tendsto (fun y : ℝ => Real.log y ^ p / y) atTop (nhds 0) := by
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y _
    ring_nf
  have hpos : ∀ᶠ y : ℝ in atTop, Real.log y ^ p / y ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
    have hy0 : (0 : ℝ) < y := by linarith
    have hlog : 0 < Real.log y := Real.log_pos (by linarith)
    exact div_pos (by positivity) hy0
  have h2 : Tendsto (fun y : ℝ => Real.log y ^ p / y) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 hpos
  have h3 : Tendsto (fun y : ℝ => (Real.log y ^ p / y)⁻¹) atTop atTop :=
    h2.inv_tendsto_nhdsGT_zero
  have h4 : Tendsto (fun y : ℝ => y / Real.log y ^ p) atTop atTop := by
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
    rw [inv_div]
  have h5 : Tendsto (fun X : ℝ => Real.sqrt X / Real.log (Real.sqrt X) ^ p) atTop atTop :=
    h4.comp Real.tendsto_sqrt_atTop
  have h6 : Tendsto (fun X : ℝ => 2 ^ p * (Real.sqrt X / Real.log X ^ p)) atTop atTop := by
    refine h5.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hlogsqrt : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX.le
    rw [hlogsqrt, div_pow]
    field_simp
  have hcpos : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have h7 := h6.atTop_div_const hcpos
  refine h7.congr' ?_
  filter_upwards with X
  field_simp

theorem carrierTruncConst_nonneg {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (n m : ℕ) :
    0 ≤ carrierTruncConst a c n m := by
  have h1 := one_le_carrierShellConst (a := a) hc n m
  have h2 : (0 : ℝ) ≤ (carrierDegBound a n m : ℝ)
      * (poincareMassSum a n m * max 1 c ^ carrierDegBound a n m) :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (poincareMassSum_nonneg _ _ _)
        (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
  have h3 : (0 : ℝ) ≤ 1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ m := by
    have := pow_nonneg (mul_nonneg ha.le (cbinomAbsCoeff_nonneg ((1 : ℝ) / 2) 1)) m
    linarith
  rw [carrierTruncConst]
  nlinarith

theorem radiationShellBound_nonneg {a σ c u M : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (n' m : ℕ) : 0 ≤ radiationShellBound a σ c n' m u M := by
  rw [radiationShellBound]
  have hC := carrierTruncConst_nonneg ha hc (n' + 1) m
  have hrr := rayRemConst_nonneg (n' + 1)
  have hmax : (0 : ℝ) ≤ max 1 (M ^ 2) ^ m :=
    pow_nonneg (le_trans zero_le_one (le_max_left _ _)) m
  have hau : (0 : ℝ) ≤ a * u := mul_nonneg ha.le hu
  have hterm1 : (0 : ℝ) ≤ ‖massBesselLeading a (apertureSpectralPoint σ u)‖
      * (carrierTruncConst a c (n' + 1) m * max 1 (M ^ 2) ^ m * (u⁻¹) ^ m) :=
    mul_nonneg (norm_nonneg _)
      (mul_nonneg (mul_nonneg hC hmax) (pow_nonneg (inv_nonneg.2 hu) m))
  have hterm2 : (0 : ℝ) ≤ 8 * a * ((((a * u) ^ ((1 : ℝ) / 2))⁻¹)
      * (rayRemConst (n' + 1) / (a * u) ^ (n' + 1))) :=
    mul_nonneg (by positivity)
      (mul_nonneg (inv_nonneg.2 (Real.rpow_nonneg hau _))
        (div_nonneg hrr (pow_nonneg hau _)))
  linarith

theorem sqrt_pow_four (L : ℝ) : Real.sqrt (L ^ 4) = L ^ 2 := by
  rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg L)]

/-- The shell bound decays two logarithmic powers faster than the leading radiation term. -/
theorem exists_shellBound_le (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℝ, 1 ≤ L →
      radiationShellBound a σ 1 m (m + 1) (L ^ 4) (L + Real.log 2)
        ≤ D / L ^ (2 * m + 4) := by
  set A : ℝ := Real.sqrt (2 * Real.pi * a) * Real.exp (-(a * σ)) with hAdef
  set C : ℝ := carrierTruncConst a 1 (m + 1) (m + 1) with hCdef
  set E : ℝ := 8 * a * ((Real.sqrt a)⁻¹ * (rayRemConst (m + 1) * ((a ^ (m + 1))⁻¹))) with hEdef
  have hA0 : 0 ≤ A := by positivity
  have hC0 : (0 : ℝ) ≤ C := by
    have h1 := one_le_carrierShellConst (a := a) (c := (1 : ℝ)) zero_le_one (m + 1) (m + 1)
    have h2 : (0 : ℝ) ≤ (carrierDegBound a (m + 1) (m + 1) : ℝ)
        * (poincareMassSum a (m + 1) (m + 1)
          * max 1 (1 : ℝ) ^ carrierDegBound a (m + 1) (m + 1)) :=
      mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (poincareMassSum_nonneg _ _ _)
          (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _))
    have h3 : (0 : ℝ) ≤ 1 + (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) ^ (m + 1) := by
      have := pow_nonneg (mul_nonneg ha.le (cbinomAbsCoeff_nonneg ((1 : ℝ) / 2) 1)) (m + 1)
      linarith
    rw [hCdef, carrierTruncConst]
    nlinarith
  have hE0 : (0 : ℝ) ≤ E := by
    have := rayRemConst_nonneg (m + 1)
    rw [hEdef]
    positivity
  refine ⟨A * C * 3 ^ (2 * m + 2) + E, by positivity, fun L hL => ?_⟩
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  set u : ℝ := L ^ 4 with hudef
  have hL4 : (0 : ℝ) < u := by rw [hudef]; positivity
  have hu1 : (1 : ℝ) ≤ u := by rw [hudef]; exact one_le_pow₀ hL
  set t : ℂ := apertureSpectralPoint σ u with htdef
  have htre : t.re = σ := by rw [htdef, spectralPoint_re]
  have htrepos : 0 < t.re := by rw [htre]; exact hσ
  have hnormt : u ≤ ‖t‖ := by rw [htdef]; exact le_norm_spectralPoint σ u
  have hsq : Real.sqrt u = L ^ 2 := by rw [hudef]; exact sqrt_pow_four L
  have hsqt : L ^ 2 ≤ Real.sqrt ‖t‖ := by
    rw [← hsq]
    exact Real.sqrt_le_sqrt hnormt
  have hL2 : (0 : ℝ) < L ^ 2 := by positivity
  have hlead : ‖massBesselLeading a t‖ ≤ A / L ^ 2 := by
    rw [norm_massBesselLeading a htrepos, htre, ← hAdef]
    exact div_le_div_of_nonneg_left hA0 hL2 hsqt
  have hmax : max 1 ((L + Real.log 2) ^ 2) ^ (m + 1) ≤ 3 ^ (2 * m + 2) * (L ^ 2) ^ (m + 1) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hM : (L + Real.log 2) ^ 2 ≤ 9 * L ^ 2 := by
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have hone : (1 : ℝ) ≤ 9 * L ^ 2 := by nlinarith
    have hmx : max 1 ((L + Real.log 2) ^ 2) ≤ 9 * L ^ 2 := max_le hone hM
    calc max 1 ((L + Real.log 2) ^ 2) ^ (m + 1)
        ≤ (9 * L ^ 2) ^ (m + 1) :=
          pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hmx (m + 1)
      _ = 3 ^ (2 * m + 2) * (L ^ 2) ^ (m + 1) := by
          rw [mul_pow, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
          congr 2
  have hrpow : ((a * u) ^ ((1 : ℝ) / 2))⁻¹ = (Real.sqrt a * L ^ 2)⁻¹ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul ha.le, hsq]
  have hterm2 : 8 * a * (((a * u) ^ ((1 : ℝ) / 2))⁻¹ * (rayRemConst (m + 1) / (a * u) ^ (m + 1)))
      = E * (L ^ (4 * m + 6))⁻¹ := by
    rw [hrpow, hEdef, hudef, mul_pow, ← pow_mul, div_eq_mul_inv, mul_inv]
    have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
    have hLne : L ≠ 0 := ne_of_gt hL0
    have hane : a ≠ 0 := ne_of_gt ha
    field_simp
    ring
  have hinvpow : ((u⁻¹) ^ (m + 1)) = ((L ^ (4 * m + 4))⁻¹) := by
    rw [hudef, ← inv_pow, ← pow_mul, ← inv_pow]
    congr 2
  have hLpow : ∀ p q : ℕ, p ≤ q → (L ^ q)⁻¹ ≤ (L ^ p)⁻¹ := by
    intro p q hpq
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hL hpq)
  rw [radiationShellBound, ← htdef, hterm2, hinvpow]
  have hfirst : ‖massBesselLeading a t‖ * (C * max 1 ((L + Real.log 2) ^ 2) ^ (m + 1)
      * (L ^ (4 * m + 4))⁻¹) ≤ A * C * 3 ^ (2 * m + 2) * (L ^ (2 * m + 4))⁻¹ := by
    have hinner : C * max 1 ((L + Real.log 2) ^ 2) ^ (m + 1) * (L ^ (4 * m + 4))⁻¹
        ≤ C * (3 ^ (2 * m + 2) * (L ^ 2) ^ (m + 1)) * (L ^ (4 * m + 4))⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hC0) (by positivity)
    have hval : C * (3 ^ (2 * m + 2) * (L ^ 2) ^ (m + 1)) * (L ^ (4 * m + 4))⁻¹
        = C * 3 ^ (2 * m + 2) * (L ^ (2 * m + 2))⁻¹ := by
      rw [← pow_mul]
      have h24 : L ^ (4 * m + 4) = L ^ (2 * m + 2) * L ^ (2 * m + 2) := by
        rw [← pow_add]
        congr 1
        omega
      have hne : L ^ (2 * m + 2) ≠ 0 := by positivity
      rw [h24, mul_inv]
      have hcast : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [hcast]
      field_simp
    have hlast : A * (C * 3 ^ (2 * m + 2) * (L ^ (2 * m + 2))⁻¹) / L ^ 2
        = A * C * 3 ^ (2 * m + 2) * (L ^ (2 * m + 4))⁻¹ := by
      have h24 : L ^ (2 * m + 4) = L ^ (2 * m + 2) * L ^ 2 := by
        rw [← pow_add]
      rw [h24, mul_inv]
      field_simp
    calc ‖massBesselLeading a t‖ * (C * max 1 ((L + Real.log 2) ^ 2) ^ (m + 1)
          * (L ^ (4 * m + 4))⁻¹)
        ≤ ‖massBesselLeading a t‖ * (C * (3 ^ (2 * m + 2) * (L ^ 2) ^ (m + 1))
            * (L ^ (4 * m + 4))⁻¹) := mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
      _ = ‖massBesselLeading a t‖ * (C * 3 ^ (2 * m + 2) * (L ^ (2 * m + 2))⁻¹) := by rw [hval]
      _ ≤ (A / L ^ 2) * (C * 3 ^ (2 * m + 2) * (L ^ (2 * m + 2))⁻¹) :=
          mul_le_mul_of_nonneg_right hlead (by positivity)
      _ = A * (C * 3 ^ (2 * m + 2) * (L ^ (2 * m + 2))⁻¹) / L ^ 2 := by ring
      _ = A * C * 3 ^ (2 * m + 2) * (L ^ (2 * m + 4))⁻¹ := hlast
  have hsecond : E * (L ^ (4 * m + 6))⁻¹ ≤ E * (L ^ (2 * m + 4))⁻¹ :=
    mul_le_mul_of_nonneg_left (hLpow (2 * m + 4) (4 * m + 6) (by omega)) hE0
  have hsum := add_le_add hfirst hsecond
  refine le_trans hsum (le_of_eq ?_)
  rw [div_eq_mul_inv]
  ring

/-- The prime mass of the extremal Poincaré coefficient is eventually at least half its limit. -/
theorem eventually_norm_dyadicPoincareMass_ge {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      ‖(poincareCoeffPoly a (m + 1) (m + 1) m).coeff m‖ * (2 * (Real.sqrt 2 - 1)) / 2
          * (Real.sqrt X * Real.log X ^ (2 * m))
        ≤ ‖dyadicPoincareMass a (m + 1) (m + 1) m X‖ := by
  set q : ℂ := (poincareCoeffPoly a (m + 1) (m + 1) m).coeff m with hqdef
  set B : ℝ := ‖q‖ * (2 * (Real.sqrt 2 - 1)) with hBdef
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hq : q ≠ 0 := by
    rw [hqdef, coeff_poincareCoeffPoly_self a (by omega) (by omega) (by omega)]
    have hfac : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hane : (-(a : ℂ) / 2) ≠ 0 := by
      simp only [ne_eq, div_eq_zero_iff, neg_eq_zero, Complex.ofReal_eq_zero]
      push Not
      exact ⟨ne_of_gt ha, by norm_num⟩
    exact mul_ne_zero (inv_ne_zero hfac) (pow_ne_zero m hane)
  have hB0 : 0 < B := by
    rw [hBdef]
    have : 0 < ‖q‖ := norm_pos_iff.2 hq
    nlinarith
  have hlim := tendsto_dyadicPoincareMass a (m + 1) (m + 1) m
  have hnormlim : Tendsto (fun X : ℝ => ‖dyadicPoincareMass a (m + 1) (m + 1) m X
      / ((Real.sqrt X * Real.log X ^ (2 * m) : ℝ) : ℂ)‖) atTop (𝓝 B) := by
    have hn := hlim.norm
    have hval : ‖q * ((2 * (Real.sqrt 2 - 1) : ℝ) : ℂ)‖ = B := by
      rw [hBdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rwa [hval] at hn
  filter_upwards [Tendsto.eventually_const_le (by linarith : B / 2 < B) hnormlim,
    eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with X hge hX1 hL
  have hXpos : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
  have hden : (0 : ℝ) < Real.sqrt X * Real.log X ^ (2 * m) := by positivity
  have hnormdiv : ‖dyadicPoincareMass a (m + 1) (m + 1) m X
      / ((Real.sqrt X * Real.log X ^ (2 * m) : ℝ) : ℂ)‖
      = ‖dyadicPoincareMass a (m + 1) (m + 1) m X‖ / (Real.sqrt X * Real.log X ^ (2 * m)) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hden.le]
  rw [hnormdiv, le_div_iff₀ hden] at hge
  linarith [hge]

set_option maxHeartbeats 4000000 in
/-- **The finite mass-Bessel radiation apertures are not uniformly bounded.** -/
theorem tendsto_norm_massBesselDyadicRadiationRemainder_atTop (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ)
    (m : ℕ) :
    Tendsto (fun X : ℝ =>
        ‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) m (Real.log X ^ 4)‖)
      atTop atTop := by
  obtain ⟨D, hD0, hD⟩ := exists_shellBound_le a σ ha hσ m
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, (poincareCoeffPoly a (m + 1) (m + 1) m).coeff m = q := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, ‖q‖ * (2 * (Real.sqrt 2 - 1)) = B := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, Real.sqrt (2 * Real.pi * a) * Real.exp (-(a * σ)) = A := ⟨_, rfl⟩
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hq : q ≠ 0 := by
    rw [← hqdef, coeff_poincareCoeffPoly_self a (by omega) (by omega) (by omega)]
    have hfac : ((Nat.factorial m : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hane : (-(a : ℂ) / 2) ≠ 0 := by
      simp only [ne_eq, div_eq_zero_iff, neg_eq_zero, Complex.ofReal_eq_zero]
      push Not
      exact ⟨ne_of_gt ha, by norm_num⟩
    exact mul_ne_zero (inv_ne_zero hfac) (pow_ne_zero m hane)
  have hB0 : 0 < B := by
    rw [← hBdef]
    have : 0 < ‖q‖ := norm_pos_iff.2 hq
    nlinarith
  have hA0 : 0 < A := by
    rw [← hAdef]
    have hs : (0 : ℝ) < Real.sqrt (2 * Real.pi * a) := Real.sqrt_pos.2 (by positivity)
    positivity
  obtain ⟨C₁, hC1def⟩ : ∃ C : ℝ, A * B / (Real.sqrt 2 * 2 ^ (m + 1)) = C := ⟨_, rfl⟩
  have hC10 : 0 < C₁ := by
    rw [← hC1def]
    positivity
  have hgrow := (tendsto_sqrt_div_log_pow_atTop (2 * m + 2)).const_mul_atTop
    (show (0 : ℝ) < C₁ / 2 by linarith)
  refine tendsto_atTop_mono' atTop ?_ hgrow
  have hcb : (0 : ℝ) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) 1 := cbinomAbsCoeff_nonneg _ _
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      3 + σ + 8 * a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 + 4 * Real.sqrt 2 / σ + 4 * D / C₁ = K :=
    ⟨_, rfl⟩
  have hK1 : (0 : ℝ) ≤ 8 * a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 := by positivity
  have hK2 : (0 : ℝ) ≤ 4 * Real.sqrt 2 / σ := by positivity
  have hK3 : (0 : ℝ) ≤ 4 * D / C₁ := by positivity
  have hKge3 : (3 : ℝ) ≤ K := by rw [← hKdef]; linarith
  have hσK : σ ≤ K := by rw [← hKdef]; linarith
  have hKs : 4 * Real.sqrt 2 / σ ≤ K := by rw [← hKdef]; linarith
  have hKa : 8 * a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 ≤ K := by rw [← hKdef]; linarith
  have hKD : 4 * D / C₁ ≤ K := by rw [← hKdef]; linarith
  have hmassle : ∀ᶠ X : ℝ in atTop, dyadicSqrtVonMangoldtMass X ≤ 2 * Real.sqrt X := by
    have hlim := tendsto_dyadicSqrtVonMangoldtMass_div_sqrt
    have hlt : 2 * (Real.sqrt 2 - 1) < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hev := Tendsto.eventually_le_const hlt hlim
    filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hs : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 (by linarith)
    rw [div_le_iff₀ hs] at hX
    linarith
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop K,
    hmassle, eventually_norm_dyadicPoincareMass_ge ha m] with X hX1 hLK hmass hmassm
  have hX0 : (0 : ℝ) < X := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, Real.log X = L := ⟨_, rfl⟩
  rw [hLdef] at hLK hmassm ⊢
  rw [hqdef, hBdef] at hmassm
  have hL3 : (3 : ℝ) ≤ L := le_trans hKge3 hLK
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hMle : (L + Real.log 2) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have hL2sq : (9 : ℝ) ≤ L ^ 2 := by nlinarith
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, L ^ 4 = u := ⟨_, rfl⟩
  rw [hudef]
  have hL4sq : L ^ 4 = L ^ 2 * L ^ 2 := by ring
  have hLL : L ≤ u := by
    rw [← hudef]
    nlinarith
  have hu1 : (1 : ℝ) ≤ u := by rw [← hudef]; nlinarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hσu : σ ≤ u := le_trans (le_trans hσK hLK) hLL
  have hL2ge : L ^ 2 ≤ u := by rw [← hudef]; nlinarith
  have h1 : 2 * (L + Real.log 2) ^ 2 ≤ u := by
    rw [← hudef, hL4sq]
    nlinarith
  have h2 : Real.sqrt 2 * (L + Real.log 2) ^ 2 < σ * u := by
    have hLs : 4 * Real.sqrt 2 / σ ≤ L := le_trans hKs hLK
    have hmul : 4 * Real.sqrt 2 ≤ σ * L := by
      rw [div_le_iff₀ hσ] at hLs
      linarith
    have hσL2 : σ * L ≤ σ * L ^ 2 := by nlinarith
    have hL2u : σ * L ^ 2 ≤ σ * u := by nlinarith [hL2ge, hσ.le]
    nlinarith [hMle, hs2pos]
  have hc : (L + Real.log 2) ^ 2 / u ≤ 1 := by
    rw [div_le_one hu0]
    linarith
  have hdefu : a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * ((L + Real.log 2) ^ 2 / u) ≤ 1 / 2 := by
    have hLa : 8 * a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 ≤ L := le_trans hKa hLK
    have hquot : (L + Real.log 2) ^ 2 / u ≤ 4 / L ^ 2 := by
      rw [div_le_div_iff₀ hu0 (by positivity)]
      nlinarith [hMle, hL2ge, hL1]
    have hpos : (0 : ℝ) ≤ a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 := by positivity
    have hstep : a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * ((L + Real.log 2) ^ 2 / u)
        ≤ a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * (4 / L ^ 2) :=
      mul_le_mul_of_nonneg_left hquot hpos
    have hfin : a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * (4 / L ^ 2) ≤ 1 / 2 := by
      have hre : a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * (4 / L ^ 2)
          = 4 * (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) / L ^ 2 := by ring
      rw [hre, div_le_iff₀ (by positivity)]
      nlinarith [hLa, hpos, mul_nonneg (by linarith : (0 : ℝ) ≤ L - 1)
        (by linarith : (0 : ℝ) ≤ L)]
    linarith
  have hlogshell : ∀ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      Real.log k ^ 2 ≤ (L + Real.log 2) ^ 2 := by
    intro k hk
    obtain ⟨hlow, hhigh⟩ := log_mem_dyadic hX0 hk
    rw [hLdef] at hlow hhigh
    have hnn : (0 : ℝ) ≤ Real.log k := le_trans (by linarith) hlow
    nlinarith
  have hbound := norm_massBesselDyadicRadiationRemainder_le (a := a) (σ := σ) (X := X) (u := u)
    (M := L + Real.log 2) (c := 1) ha hσ hu1 hσu hlogshell h1 h2 hc hdefu m (m + 1)
  have hshell : radiationShellBound a σ 1 m (m + 1) u (L + Real.log 2) ≤ D / L ^ (2 * m + 4) := by
    rw [← hudef]
    exact hD L hL1
  obtain ⟨t, htdef⟩ : ∃ t : ℂ, apertureSpectralPoint σ u = t := ⟨_, rfl⟩
  have htre : t.re = σ := by rw [← htdef, spectralPoint_re]
  have htrepos : 0 < t.re := by rw [htre]; exact hσ
  have hnormt : u ≤ ‖t‖ := by rw [← htdef]; exact le_norm_spectralPoint σ u
  have hnormt2 : ‖t‖ ≤ 2 * u := by rw [← htdef]; exact norm_spectralPoint_le hσ hσu
  have htpos : (0 : ℝ) < ‖t‖ := by linarith
  have hsqrtu : Real.sqrt u = L ^ 2 := by rw [← hudef]; exact sqrt_pow_four L
  have hsqrt2u : Real.sqrt (2 * u) = Real.sqrt 2 * L ^ 2 := by
    rw [Real.sqrt_mul (by norm_num), hsqrtu]
  have hleadge : A / (Real.sqrt 2 * L ^ 2) ≤ ‖massBesselLeading a t‖ := by
    rw [norm_massBesselLeading a htrepos, htre, hAdef]
    refine div_le_div_of_nonneg_left hA0.le (Real.sqrt_pos.2 htpos) ?_
    rw [← hsqrt2u]
    exact Real.sqrt_le_sqrt hnormt2
  have hinvge : ((2 * u)⁻¹) ^ m ≤ ‖(t⁻¹ : ℂ) ^ m‖ := by
    rw [norm_pow, norm_inv]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ htpos hnormt2) m
  have hXs : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 hX0
  have hmain : C₁ * (Real.sqrt X / L ^ (2 * m + 2))
      ≤ ‖massBesselLeading a t * (dyadicPoincareMass a (m + 1) (m + 1) m X * (t⁻¹) ^ m)‖ := by
    rw [norm_mul, norm_mul]
    have hstep1 : A / (Real.sqrt 2 * L ^ 2)
          * (B / 2 * (Real.sqrt X * L ^ (2 * m)) * ((2 * u)⁻¹) ^ m)
        ≤ ‖massBesselLeading a t‖
          * (‖dyadicPoincareMass a (m + 1) (m + 1) m X‖ * ‖(t⁻¹ : ℂ) ^ m‖) := by
      refine mul_le_mul hleadge ?_ (by positivity) (norm_nonneg _)
      exact mul_le_mul hmassm hinvge (by positivity) (norm_nonneg _)
    refine le_trans (le_of_eq ?_) hstep1
    rw [← hC1def, ← hudef]
    have hLne : L ≠ 0 := ne_of_gt hL0
    have hpow : ((2 * L ^ 4)⁻¹) ^ m = (2 ^ m)⁻¹ * (L ^ (4 * m))⁻¹ := by
      rw [mul_inv, mul_pow, inv_pow, inv_pow, ← pow_mul]
    have hsplit : L ^ (2 * m + 2) = L ^ (2 * m) * L ^ 2 := by rw [← pow_add]
    have hsplit2 : L ^ (4 * m) = L ^ (2 * m) * L ^ (2 * m) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, hsplit, hsplit2]
    field_simp
    ring
  have herr : ‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) (m + 1) u‖
      ≤ C₁ / 2 * (Real.sqrt X / L ^ (2 * m + 2)) := by
    have hLD : 4 * D / C₁ ≤ L := le_trans hKD hLK
    have hDL0 : (0 : ℝ) ≤ D / L ^ (2 * m + 4) := by positivity
    have hmass0 := dyadicSqrtVonMangoldtMass_nonneg X
    have hsb0 : (0 : ℝ) ≤ radiationShellBound a σ 1 m (m + 1) u (L + Real.log 2) :=
      radiationShellBound_nonneg ha zero_le_one hu0.le m (m + 1)
    have hstep : dyadicSqrtVonMangoldtMass X
        * radiationShellBound a σ 1 m (m + 1) u (L + Real.log 2)
        ≤ 2 * Real.sqrt X * (D / L ^ (2 * m + 4)) :=
      mul_le_mul hmass hshell hsb0 (by positivity)
    have hsplit : L ^ (2 * m + 4) = L ^ (2 * m + 2) * L ^ 2 := by rw [← pow_add]
    have hL22 : (0 : ℝ) < L ^ (2 * m + 2) := by positivity
    have hL2p : (0 : ℝ) < L ^ 2 := by positivity
    have hDL : 2 * D / L ^ 2 ≤ C₁ / 2 := by
      rw [div_le_div_iff₀ hL2p (by norm_num)]
      rw [div_le_iff₀ hC10] at hLD
      nlinarith [hL1, hD0, hC10.le]
    have hfinal : 2 * Real.sqrt X * (D / L ^ (2 * m + 4))
        ≤ C₁ / 2 * (Real.sqrt X / L ^ (2 * m + 2)) := by
      rw [hsplit]
      have hexp : 2 * Real.sqrt X * (D / (L ^ (2 * m + 2) * L ^ 2))
          = Real.sqrt X * (2 * D / L ^ 2) / L ^ (2 * m + 2) := by
        field_simp
      have hexp2 : C₁ / 2 * (Real.sqrt X / L ^ (2 * m + 2))
          = Real.sqrt X * (C₁ / 2) / L ^ (2 * m + 2) := by
        field_simp
      rw [hexp, hexp2]
      refine div_le_div_of_nonneg_right ?_ hL22.le
      exact mul_le_mul_of_nonneg_left hDL hXs.le
    linarith [hbound, hstep, hfinal]
  have hsucc := massBesselDyadicRadiationRemainder_succ a σ X (m + 1) (m + 1) m u
  rw [htdef] at hsucc
  have hge : ‖massBesselLeading a t * (dyadicPoincareMass a (m + 1) (m + 1) m X * (t⁻¹) ^ m)‖
      - ‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) (m + 1) u‖
      ≤ ‖massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) m u‖ := by
    rw [hsucc]
    have hns := norm_sub_norm_le
      (massBesselLeading a t * (dyadicPoincareMass a (m + 1) (m + 1) m X * (t⁻¹) ^ m))
      (-(massBesselDyadicRadiationRemainder a σ X (m + 1) (m + 1) (m + 1) u))
    rw [norm_neg, sub_neg_eq_add] at hns
    exact hns
  linarith [hmain, herr, hge]


section ShellHypotheses

set_option maxHeartbeats 1600000 in
/-- Along the deep-time ray every hypothesis of the shell-uniform bound holds eventually. -/
theorem eventually_shellHypotheses (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ) :
    ∀ᶠ X : ℝ in atTop,
      (3 : ℝ) ≤ Real.log X ∧ (1 : ℝ) ≤ Real.log X ^ 4 ∧ σ ≤ Real.log X ^ 4 ∧
      (∀ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
        Real.log k ^ 2 ≤ (Real.log X + Real.log 2) ^ 2) ∧
      2 * (Real.log X + Real.log 2) ^ 2 ≤ Real.log X ^ 4 ∧
      Real.sqrt 2 * (Real.log X + Real.log 2) ^ 2 < σ * Real.log X ^ 4 ∧
      (Real.log X + Real.log 2) ^ 2 / Real.log X ^ 4 ≤ 1 ∧
      a * cbinomAbsCoeff ((1 : ℝ) / 2) 1
          * ((Real.log X + Real.log 2) ^ 2 / Real.log X ^ 4) ≤ 1 / 2 := by
  have hcb : (0 : ℝ) ≤ cbinomAbsCoeff ((1 : ℝ) / 2) 1 := cbinomAbsCoeff_nonneg _ _
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      3 + σ + 8 * a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 + 4 * Real.sqrt 2 / σ = K := ⟨_, rfl⟩
  have hK1 : (0 : ℝ) ≤ 8 * a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 := by positivity
  have hK2 : (0 : ℝ) ≤ 4 * Real.sqrt 2 / σ := by positivity
  have hKge3 : (3 : ℝ) ≤ K := by rw [← hKdef]; linarith
  have hσK : σ ≤ K := by rw [← hKdef]; linarith
  have hKs : 4 * Real.sqrt 2 / σ ≤ K := by rw [← hKdef]; linarith
  have hKa : 8 * a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 ≤ K := by rw [← hKdef]; linarith
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop K] with X hX1 hLK
  have hX0 : (0 : ℝ) < X := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, Real.log X = L := ⟨_, rfl⟩
  rw [hLdef] at hLK ⊢
  have hL3 : (3 : ℝ) ≤ L := le_trans hKge3 hLK
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hMle : (L + Real.log 2) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have hL2sq : (9 : ℝ) ≤ L ^ 2 := by nlinarith
  have hL4sq : L ^ 4 = L ^ 2 * L ^ 2 := by ring
  have hLL : L ≤ L ^ 4 := by nlinarith
  have hu1 : (1 : ℝ) ≤ L ^ 4 := by nlinarith
  have hu0 : (0 : ℝ) < L ^ 4 := by linarith
  have hσu : σ ≤ L ^ 4 := le_trans (le_trans hσK hLK) hLL
  have hL2ge : L ^ 2 ≤ L ^ 4 := by nlinarith
  have h1 : 2 * (L + Real.log 2) ^ 2 ≤ L ^ 4 := by rw [hL4sq]; nlinarith
  have h2 : Real.sqrt 2 * (L + Real.log 2) ^ 2 < σ * L ^ 4 := by
    have hLs : 4 * Real.sqrt 2 / σ ≤ L := le_trans hKs hLK
    have hmul : 4 * Real.sqrt 2 ≤ σ * L := by
      rw [div_le_iff₀ hσ] at hLs
      linarith
    have hσL2 : σ * L ≤ σ * L ^ 2 := by nlinarith
    have hL2u : σ * L ^ 2 ≤ σ * L ^ 4 := by nlinarith [hL2ge, hσ.le]
    nlinarith [hMle, hs2pos]
  have hc : (L + Real.log 2) ^ 2 / L ^ 4 ≤ 1 := by
    rw [div_le_one hu0]
    linarith
  have hdefu : a * cbinomAbsCoeff ((1 : ℝ) / 2) 1
      * ((L + Real.log 2) ^ 2 / L ^ 4) ≤ 1 / 2 := by
    have hLa : 8 * a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 ≤ L := le_trans hKa hLK
    have hquot : (L + Real.log 2) ^ 2 / L ^ 4 ≤ 4 / L ^ 2 := by
      rw [div_le_div_iff₀ hu0 (by positivity)]
      nlinarith [hMle, hL2ge, hL1]
    have hpos : (0 : ℝ) ≤ a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 := by positivity
    have hstep : a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * ((L + Real.log 2) ^ 2 / L ^ 4)
        ≤ a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * (4 / L ^ 2) :=
      mul_le_mul_of_nonneg_left hquot hpos
    have hfin : a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * (4 / L ^ 2) ≤ 1 / 2 := by
      have hre : a * cbinomAbsCoeff ((1 : ℝ) / 2) 1 * (4 / L ^ 2)
          = 4 * (a * cbinomAbsCoeff ((1 : ℝ) / 2) 1) / L ^ 2 := by ring
      rw [hre, div_le_iff₀ (by positivity)]
      nlinarith [hLa, hpos, mul_nonneg (by linarith : (0 : ℝ) ≤ L - 1)
        (by linarith : (0 : ℝ) ≤ L)]
    linarith
  have hlogshell : ∀ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      Real.log k ^ 2 ≤ (L + Real.log 2) ^ 2 := by
    intro k hk
    obtain ⟨hlow, hhigh⟩ := log_mem_dyadic hX0 hk
    rw [hLdef] at hlow hhigh
    have hnn : (0 : ℝ) ≤ Real.log k := le_trans (by linarith) hlow
    nlinarith
  exact ⟨hL3, hu1, hσu, hlogshell, h1, h2, hc, hdefu⟩

end ShellHypotheses

end

end RHTower
