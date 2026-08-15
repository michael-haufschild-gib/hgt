import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeSum

/-!
# The mass-uniform prime bound of the rational hard-edge test

The information cone gives an exponential aperture whose constant grows with the degree, so a
single application is not uniform in the mass.  Splitting at the threshold `L_C = 8C + 4` repairs
this: below the threshold the trivial Fourier bound already beats `e^{L_C}/m`, and above it the
cone's exponential gain `e^{-a(L_C·rate(1) − 2C)}` swallows the degree factor `2(N+1)e^{2N}` once
`N ≤ Ca`.  Both regimes are therefore dominated by the single summable majorant

`Λ(m)·m^{-3/2}·(2C+2)·e^{L_C}·‖g‖₂²`,

so the completed prime term is bounded by a constant depending only on the scaled degree `C`,
uniformly over every mass `a ≥ 4` and every coefficient vector.
-/

open MeasureTheory

noncomputable section

namespace RHTower

/-- The uniform prime aperture threshold attached to a scaled degree. -/
def routeUPrimeThreshold (C : ℝ) : ℝ := 8 * C + 4

/-- The absolutely convergent von Mangoldt tail at exponent `3/2`. -/
def routeUVonMangoldtTailThreeHalves : ℝ :=
  ∑' m : ℕ, (ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(3 / 2 : ℝ))

theorem summable_vonMangoldt_threeHalves :
    Summable fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have h := RHTower.Sieve.summable_vonMangoldt_rpow (σ := (3 / 2 : ℝ)) (by norm_num)
  refine h.congr fun m => ?_
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]

theorem routeUVonMangoldtTailThreeHalves_nonneg : 0 ≤ routeUVonMangoldtTailThreeHalves := by
  refine tsum_nonneg fun m => ?_
  have h1 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt m : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have h2 : (0 : ℝ) ≤ (m : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  positivity

/-- The mass-uniform prime constant attached to a scaled degree. -/
def routeUPrimeUniformConst (C : ℝ) : ℝ :=
  (2 * C + 2) * Real.exp (routeUPrimeThreshold C) * routeUVonMangoldtTailThreeHalves

theorem routeUCayleyDecayRate_one_ge : (1 : ℝ) / 4 ≤ routeUCayleyDecayRate 1 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpos : (0 : ℝ) < Real.exp 1 + 1 := by linarith
  rw [routeUCayleyDecayRate, le_div_iff₀ hpos]
  linarith

set_option maxHeartbeats 1600000 in
/-- **The mass-uniform prime aperture, termwise.** -/
theorem norm_routeUHardEdgeFourierTerm_le {C a : ℝ} (hC : 0 < C) (ha : 4 ≤ a)
    (p : Polynomial ℝ) {N : ℕ} (hN : (routeUHardEdgeAngularPoly a p).natDegree ≤ N)
    (hNC : (N : ℝ) ≤ C * a) (m : ℕ) :
    ((ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m)
        * ‖routeUHardEdgeFourierSq a p (Real.log m)‖
      ≤ (2 * C + 2) * Real.exp (routeUPrimeThreshold C)
          * (∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2)
          * ((ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have ha0 : (0 : ℝ) < a := by linarith
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = routeUCayleyDecayRate 1 := ⟨_, rfl⟩
  have ht : (1 : ℝ) / 4 ≤ t := by rw [ht_def]; exact routeUCayleyDecayRate_one_ge
  have ht0 : (0 : ℝ) < t := by linarith
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = routeUPrimeThreshold C := ⟨_, rfl⟩
  have hL0 : (0 : ℝ) < L := by rw [hL_def, routeUPrimeThreshold]; linarith
  have hat : (1 : ℝ) ≤ a * t := by nlinarith
  have hδ : (1 : ℝ) ≤ L * t - 2 * C := by
    rw [hL_def, routeUPrimeThreshold]
    nlinarith
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = (2 * C + 2) * Real.exp L := ⟨_, rfl⟩
  have hexpL : (0 : ℝ) < Real.exp L := Real.exp_pos L
  have hK0 : (0 : ℝ) < K := by rw [hK_def]; positivity
  have hKL : Real.exp L ≤ K := by
    rw [hK_def]
    nlinarith
  obtain ⟨I, hI_def⟩ : ∃ I : ℝ, I = ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := ⟨_, rfl⟩
  have hI0 : (0 : ℝ) ≤ I := by
    rw [hI_def]
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  rw [← hL_def, ← hK_def, ← hI_def]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by simp
    rw [h0]
    simp
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt m : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hℓ0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hmexp : (m : ℝ) = Real.exp (Real.log (m : ℝ)) := (Real.exp_log hmpos).symm
  have hsq : Real.exp (Real.log (m : ℝ) / 2) ^ 2 = (m : ℝ) := by
    rw [sq, ← Real.exp_add, show Real.log (m : ℝ) / 2 + Real.log (m : ℝ) / 2
      = Real.log (m : ℝ) by ring, Real.exp_log hmpos]
  have hsqrt : Real.sqrt (m : ℝ) = Real.exp (Real.log (m : ℝ) / 2) := by
    conv_lhs => rw [← hsq]
    exact Real.sqrt_sq (Real.exp_pos _).le
  have hrpow : (m : ℝ) ^ (-(3 / 2 : ℝ)) = Real.exp (-(3 / 2) * Real.log (m : ℝ)) := by
    rw [Real.rpow_def_of_pos hmpos]
    congr 1
    ring
  have hpre : (ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m
      = (ArithmeticFunction.vonMangoldt m : ℝ) * Real.exp (-(Real.log (m : ℝ) / 2)) := by
    rw [hsqrt, div_eq_mul_inv, ← Real.exp_neg]
  rw [hpre, hrpow]
  have hposE : (0 : ℝ) < Real.exp (-(3 / 2) * Real.log (m : ℝ)) := Real.exp_pos _
  have hposH : (0 : ℝ) < Real.exp (-(Real.log (m : ℝ) / 2)) := Real.exp_pos _
  rcases le_or_gt (m : ℝ) (Real.exp L) with hcase | hcase
  · have htriv := norm_routeUHardEdgeFourierSq_le_l2 a p (Real.log (m : ℝ))
    rw [← hI_def] at htriv
    have hstep : Real.exp (-(Real.log (m : ℝ) / 2)) * I
        ≤ K * I * Real.exp (-(3 / 2) * Real.log (m : ℝ)) := by
      have hexp : Real.exp (-(Real.log (m : ℝ) / 2))
          = Real.exp (Real.log (m : ℝ)) * Real.exp (-(3 / 2) * Real.log (m : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hle : Real.exp (Real.log (m : ℝ)) ≤ K := by
        rw [← hmexp]
        linarith
      rw [hexp]
      calc Real.exp (Real.log (m : ℝ)) * Real.exp (-(3 / 2) * Real.log (m : ℝ)) * I
          ≤ K * Real.exp (-(3 / 2) * Real.log (m : ℝ)) * I := by
            refine mul_le_mul_of_nonneg_right ?_ hI0
            exact mul_le_mul_of_nonneg_right hle hposE.le
        _ = K * I * Real.exp (-(3 / 2) * Real.log (m : ℝ)) := by ring
    calc (ArithmeticFunction.vonMangoldt m : ℝ) * Real.exp (-(Real.log (m : ℝ) / 2))
          * ‖routeUHardEdgeFourierSq a p (Real.log (m : ℝ))‖
        ≤ (ArithmeticFunction.vonMangoldt m : ℝ)
            * (Real.exp (-(Real.log (m : ℝ) / 2)) * I) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hΛ
          exact mul_le_mul_of_nonneg_left htriv hposH.le
      _ ≤ (ArithmeticFunction.vonMangoldt m : ℝ)
            * (K * I * Real.exp (-(3 / 2) * Real.log (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hΛ
      _ = K * I * ((ArithmeticFunction.vonMangoldt m : ℝ)
            * Real.exp (-(3 / 2) * Real.log (m : ℝ))) := by ring
  · have hcone := norm_routeUHardEdgeFourierSq_le ha0 p hN (L := Real.log (m : ℝ)) hℓ0
      (σ := 1) (by norm_num)
    rw [← hI_def, ← ht_def] at hcone
    have hℓL : L ≤ Real.log (m : ℝ) := by
      have h := Real.log_lt_log (Real.exp_pos L) hcase
      rw [Real.log_exp] at h
      linarith
    have hexpN : Real.exp ((N : ℝ) * 1) ^ 2 = Real.exp (2 * (N : ℝ)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hkey : 2 * ((N : ℝ) + 1)
        * Real.exp (2 * (N : ℝ) - a * Real.log (m : ℝ) * t + Real.log (m : ℝ)) ≤ K := by
      have hexpo : 2 * (N : ℝ) - a * Real.log (m : ℝ) * t + Real.log (m : ℝ)
          ≤ 2 * (C * a) - a * L * t + L := by
        have h1 : (2 : ℝ) * (N : ℝ) ≤ 2 * (C * a) := by linarith
        have hcoef : (0 : ℝ) ≤ a * t - 1 := by linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hℓL) hcoef]
      have hgain : 2 * (C * a) - a * L * t + L ≤ -a + L := by
        have hmul := mul_le_mul_of_nonneg_left hδ ha0.le
        nlinarith [hmul]
      have hmono : Real.exp (2 * (N : ℝ) - a * Real.log (m : ℝ) * t + Real.log (m : ℝ))
          ≤ Real.exp (-a + L) := Real.exp_le_exp.mpr (by linarith)
      have hae : a * Real.exp (-a) ≤ 1 := by
        have h := Real.add_one_le_exp a
        have hexp : (0 : ℝ) < Real.exp a := Real.exp_pos a
        rw [Real.exp_neg, mul_inv_le_iff₀ hexp]
        linarith
      have hea : Real.exp (-a) ≤ 1 := by
        have h := Real.add_one_le_exp a
        have hexp : (0 : ℝ) < Real.exp a := Real.exp_pos a
        rw [Real.exp_neg, inv_le_one_iff₀]
        right
        linarith
      have hNle : 2 * ((N : ℝ) + 1) ≤ 2 * (C * a + 1) := by linarith
      have hNnn : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1) := by positivity
      have hsplit : 2 * (C * a + 1) * Real.exp (-a + L)
          = ((2 * C) * (a * Real.exp (-a)) + 2 * Real.exp (-a)) * Real.exp L := by
        rw [Real.exp_add]
        ring
      have hbound : ((2 * C) * (a * Real.exp (-a)) + 2 * Real.exp (-a)) * Real.exp L ≤ K := by
        rw [hK_def]
        have hCnn : (0 : ℝ) ≤ 2 * C := by linarith
        have hin : (2 * C) * (a * Real.exp (-a)) + 2 * Real.exp (-a) ≤ 2 * C + 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hae hCnn]
        exact mul_le_mul_of_nonneg_right hin hexpL.le
      calc 2 * ((N : ℝ) + 1)
            * Real.exp (2 * (N : ℝ) - a * Real.log (m : ℝ) * t + Real.log (m : ℝ))
          ≤ 2 * (C * a + 1) * Real.exp (-a + L) := by
            have hp : (0 : ℝ) ≤ Real.exp (2 * (N : ℝ) - a * Real.log (m : ℝ) * t
              + Real.log (m : ℝ)) := (Real.exp_pos _).le
            have hb : (0 : ℝ) ≤ 2 * (C * a + 1) := by nlinarith
            exact mul_le_mul hNle hmono hp hb
        _ = ((2 * C) * (a * Real.exp (-a)) + 2 * Real.exp (-a)) * Real.exp L := hsplit
        _ ≤ K := hbound
    have hdeg : (2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * 1) ^ 2
          * Real.exp (-(a * Real.log (m : ℝ) * t))) * Real.exp (-(Real.log (m : ℝ) / 2))
        ≤ K * Real.exp (-(3 / 2) * Real.log (m : ℝ)) := by
      have hprod : Real.exp (2 * (N : ℝ)) * Real.exp (-(a * Real.log (m : ℝ) * t))
            * Real.exp (-(Real.log (m : ℝ) / 2))
          = Real.exp (2 * (N : ℝ) - a * Real.log (m : ℝ) * t + Real.log (m : ℝ))
            * Real.exp (-(3 / 2) * Real.log (m : ℝ)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc (2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * 1) ^ 2
            * Real.exp (-(a * Real.log (m : ℝ) * t))) * Real.exp (-(Real.log (m : ℝ) / 2))
          = (2 * ((N : ℝ) + 1)) * (Real.exp (2 * (N : ℝ))
              * Real.exp (-(a * Real.log (m : ℝ) * t))
              * Real.exp (-(Real.log (m : ℝ) / 2))) := by rw [hexpN]; ring
        _ = (2 * ((N : ℝ) + 1)
              * Real.exp (2 * (N : ℝ) - a * Real.log (m : ℝ) * t + Real.log (m : ℝ)))
            * Real.exp (-(3 / 2) * Real.log (m : ℝ)) := by rw [hprod]; ring
        _ ≤ K * Real.exp (-(3 / 2) * Real.log (m : ℝ)) :=
            mul_le_mul_of_nonneg_right hkey hposE.le
    calc (ArithmeticFunction.vonMangoldt m : ℝ) * Real.exp (-(Real.log (m : ℝ) / 2))
          * ‖routeUHardEdgeFourierSq a p (Real.log (m : ℝ))‖
        ≤ (ArithmeticFunction.vonMangoldt m : ℝ) * (Real.exp (-(Real.log (m : ℝ) / 2))
            * ((2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * 1) ^ 2
                * Real.exp (-(a * Real.log (m : ℝ) * t))) * I)) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hΛ
          exact mul_le_mul_of_nonneg_left hcone hposH.le
      _ ≤ (ArithmeticFunction.vonMangoldt m : ℝ)
            * ((K * Real.exp (-(3 / 2) * Real.log (m : ℝ))) * I) := by
          refine mul_le_mul_of_nonneg_left ?_ hΛ
          have hmul := mul_le_mul_of_nonneg_right hdeg hI0
          calc Real.exp (-(Real.log (m : ℝ) / 2))
                * ((2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * 1) ^ 2
                    * Real.exp (-(a * Real.log (m : ℝ) * t))) * I)
              = ((2 * ((N : ℝ) + 1) * Real.exp ((N : ℝ) * 1) ^ 2
                  * Real.exp (-(a * Real.log (m : ℝ) * t)))
                  * Real.exp (-(Real.log (m : ℝ) / 2))) * I := by ring
            _ ≤ (K * Real.exp (-(3 / 2) * Real.log (m : ℝ))) * I := hmul
      _ = K * I * ((ArithmeticFunction.vonMangoldt m : ℝ)
            * Real.exp (-(3 / 2) * Real.log (m : ℝ))) := by ring

theorem summable_routeUHardEdgeFourierNorm {C a : ℝ} (hC : 0 < C) (ha : 4 ≤ a)
    (p : Polynomial ℝ) {N : ℕ} (hN : (routeUHardEdgeAngularPoly a p).natDegree ≤ N)
    (hNC : (N : ℝ) ≤ C * a) :
    Summable fun m : ℕ => ((ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m)
      * ‖routeUHardEdgeFourierSq a p (Real.log m)‖ := by
  refine Summable.of_nonneg_of_le (fun m => ?_)
    (fun m => norm_routeUHardEdgeFourierTerm_le hC ha p hN hNC m)
    (summable_vonMangoldt_threeHalves.mul_left _)
  have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt m : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hs : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  positivity

/-- **The mass-uniform prime aperture.**  Beyond mass four the completed prime term of the rational
hard-edge test is bounded by a constant depending only on the scaled degree. -/
theorem routeUHardEdgePrimeSum_uniform_le {C a : ℝ} (hC : 0 < C) (ha : 4 ≤ a)
    (p : Polynomial ℝ) {N : ℕ} (hN : (routeUHardEdgeAngularPoly a p).natDegree ≤ N)
    (hNC : (N : ℝ) ≤ C * a) :
    (∑' m : ℕ, ((ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m)
        * ‖routeUHardEdgeFourierSq a p (Real.log m)‖)
      ≤ routeUPrimeUniformConst C * ∫ x : ℝ, routeUHardEdgeRationalTest a p x ^ 2 := by
  refine le_trans ((summable_routeUHardEdgeFourierNorm hC ha p hN hNC).tsum_le_tsum
    (fun m => norm_routeUHardEdgeFourierTerm_le hC ha p hN hNC m)
    (summable_vonMangoldt_threeHalves.mul_left _)) ?_
  rw [tsum_mul_left, routeUPrimeUniformConst, ← routeUVonMangoldtTailThreeHalves]
  exact le_of_eq (by ring)

end RHTower

end
