import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistUniformHeight
import GaloisForLFunctions.RHTower.Sieve.PrimePowerDefectBound
import GaloisForLFunctions.RHTower.Sieve.PrimeTwistAbel

/-!
# The Route-T twisted prime sum

The uniform twisted Chebyshev bound is dominated by a monotone envelope in the cutoff.  Summation
by parts against `1/log` then transfers that envelope to the prime-indicator twist, which is the
prime statement of the Vinogradov--Korobov twisted-sum lemma.
-/

namespace RHTower.Sieve

open ArithmeticFunction

/-- The monotone envelope of the Route-T twisted prime sum: the contour term at exponent
`1 − w/3`, the height term at exponent `1 + 2w/3`, and the proper prime-power mass. -/
noncomputable def routeTTwistEnvelope (A delta C τ x : ℝ) : ℝ :=
  C * ((3 * x) ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
          * (routeTTwistHeightFactor A τ + Real.log (2 * x))
        + (3 * x) ^ (1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
            * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|))
    + 2 * Real.sqrt x * Real.log x

/-- The abstract envelope is monotone above one. -/
theorem twistEnvelope_mono {α β Cc Ev t : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hC : 0 ≤ Cc)
    (hEv : 0 ≤ Ev) (ht : 0 ≤ t) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    Cc * ((3 * x) ^ α * (Ev + Real.log (2 * x))
          + (3 * x) ^ β * (1 + (Real.log x) ^ 2 + Ev) / (1 + t))
        + 2 * Real.sqrt x * Real.log x
      ≤ Cc * ((3 * y) ^ α * (Ev + Real.log (2 * y))
          + (3 * y) ^ β * (1 + (Real.log y) ^ 2 + Ev) / (1 + t))
        + 2 * Real.sqrt y * Real.log y := by
  have hy : (1 : ℝ) ≤ y := le_trans hx hxy
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  have h3x : (1 : ℝ) ≤ 3 * x := by linarith
  have hden : (0 : ℝ) < 1 + t := by linarith
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hlog2x : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hlog2xy : Real.log (2 * x) ≤ Real.log (2 * y) :=
    Real.log_le_log (by linarith) (by linarith)
  have hrα : (3 * x) ^ α ≤ (3 * y) ^ α :=
    Real.rpow_le_rpow (by linarith) (by linarith) hα
  have hrβ : (3 * x) ^ β ≤ (3 * y) ^ β :=
    Real.rpow_le_rpow (by linarith) (by linarith) hβ
  have hrα0 : (0 : ℝ) ≤ (3 * x) ^ α := Real.rpow_nonneg (by linarith) _
  have hrβ0 : (0 : ℝ) ≤ (3 * x) ^ β := Real.rpow_nonneg (by linarith) _
  have hfac1 : (3 * x) ^ α * (Ev + Real.log (2 * x))
      ≤ (3 * y) ^ α * (Ev + Real.log (2 * y)) :=
    mul_le_mul hrα (by linarith) (by linarith) (Real.rpow_nonneg (by linarith) _)
  have hsq : (Real.log x) ^ 2 ≤ (Real.log y) ^ 2 := pow_le_pow_left₀ hlogx hlogxy 2
  have hfac2 : (3 * x) ^ β * (1 + (Real.log x) ^ 2 + Ev)
      ≤ (3 * y) ^ β * (1 + (Real.log y) ^ 2 + Ev) :=
    mul_le_mul hrβ (by linarith) (by nlinarith) (Real.rpow_nonneg (by linarith) _)
  have hdiv : (3 * x) ^ β * (1 + (Real.log x) ^ 2 + Ev) / (1 + t)
      ≤ (3 * y) ^ β * (1 + (Real.log y) ^ 2 + Ev) / (1 + t) :=
    div_le_div_of_nonneg_right hfac2 hden.le
  have hsqrt : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hlast : Real.sqrt x * Real.log x ≤ Real.sqrt y * Real.log y :=
    mul_le_mul hsqrt hlogxy hlogx (Real.sqrt_nonneg y)
  have hmain : Cc * ((3 * x) ^ α * (Ev + Real.log (2 * x))
        + (3 * x) ^ β * (1 + (Real.log x) ^ 2 + Ev) / (1 + t))
      ≤ Cc * ((3 * y) ^ α * (Ev + Real.log (2 * y))
        + (3 * y) ^ β * (1 + (Real.log y) ^ 2 + Ev) / (1 + t)) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  linarith

theorem routeTTwistEnvelope_mono {A delta C τ : ℝ} (hdelta : 0 < delta) (hC : 0 ≤ C)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    routeTTwistEnvelope A delta C τ x ≤ routeTTwistEnvelope A delta C τ y := by
  have hw0 : 0 < routeTUniformRegWidth A delta (3 * |τ| / 2) :=
    routeTUniformRegWidth_pos hdelta
  have hwle : routeTUniformRegWidth A delta (3 * |τ| / 2)
      ≤ routeTZeroFreeWidth A (3 * |τ| / 2 + 1) / 2 := routeTUniformRegWidth_le_half
  have hw160 : routeTZeroFreeWidth A (3 * |τ| / 2 + 1) ≤ 1 / 160 :=
    routeTZeroFreeWidth_le_one_sixtieth _ _
  have hα : (0 : ℝ) ≤ 1 - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3 := by linarith
  have hβ : (0 : ℝ) ≤ 1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3 := by linarith
  exact twistEnvelope_mono hα hβ hC (routeTTwistHeightFactor_nonneg A τ) (abs_nonneg τ) hx hxy

theorem routeTTwistEnvelope_nonneg {A delta C τ : ℝ} (hC : 0 ≤ C)
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ routeTTwistEnvelope A delta C τ x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hE : (0 : ℝ) ≤ routeTTwistHeightFactor A τ := routeTTwistHeightFactor_nonneg A τ
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hlog2x : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hden : (0 : ℝ) < 1 + |τ| := by linarith [abs_nonneg τ]
  have hr1 : (0 : ℝ) ≤ (3 * x) ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3) :=
    Real.rpow_nonneg (by linarith) _
  have hr2 : (0 : ℝ) ≤ (3 * x) ^ (1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3) :=
    Real.rpow_nonneg (by linarith) _
  have hsq : (0 : ℝ) ≤ (Real.log x) ^ 2 := by positivity
  have h1 : (0 : ℝ) ≤ (3 * x) ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
      * (routeTTwistHeightFactor A τ + Real.log (2 * x)) := by positivity
  have h2 : (0 : ℝ) ≤ (3 * x) ^ (1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
      * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|) := by positivity
  have h3 : (0 : ℝ) ≤ 2 * Real.sqrt x * Real.log x := by positivity
  rw [routeTTwistEnvelope]
  nlinarith [h1, h2, h3, hC]

theorem norm_vonMangoldtPrimeTwist_le (τ : ℝ) (n : ℕ) :
    ‖vonMangoldtPrimeTwist τ n‖ ≤ (vonMangoldt n : ℝ) := by
  by_cases hp : n.Prime
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
    have h1 : ‖((n : ℕ) : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ = 1 := by
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      simp
    have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    rw [vonMangoldtPrimeTwist, if_pos hp, norm_mul, h1, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog, vonMangoldt_apply_prime hp]
  · rw [vonMangoldtPrimeTwist, if_neg hp, norm_zero]
    exact vonMangoldt_nonneg

theorem norm_partialSum_vonMangoldtPrimeTwist_le_crude (τ : ℝ) (K : ℕ) :
    ‖∑ n ∈ Finset.range (K + 1), vonMangoldtPrimeTwist τ n‖ ≤ 7 * (K : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => norm_vonMangoldtPrimeTwist_le τ n) ?_
  have hch : ∑ n ∈ Finset.range (K + 1), (vonMangoldt n : ℝ) = chebyshevPsi K := by
    rw [sum_range_succ_vonMangoldt_eq_sum_Icc]
    rfl
  rw [hch]
  exact chebyshevPsi_le_seven K

/-- **Lemma 2.3, prime form.**  The Route-T twisted prime-indicator sum obeys the monotone
envelope of the twisted Chebyshev sum, up to the total variation of `1/log`. -/
theorem exists_norm_sum_primeTwist_routeT_le :
    ∃ A delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (N : ℕ) (τ : ℝ),
        ‖∑ n ∈ Finset.range (N + 1), primeTwist τ n‖
          ≤ (routeTTwistEnvelope A delta C τ (max (N : ℝ) 1) + 7 * Real.exp 9)
              * (1 / Real.log 2 + 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  obtain ⟨A, delta, C, hdelta, hC, hbound⟩ :=
    exists_norm_partialSum_vonMangoldtTwist_routeT_uniform
  refine ⟨A, delta, C, hdelta, hC, ?_⟩
  intro N τ
  have hexp9 : (10 : ℝ) ≤ Real.exp 9 := by
    have := Real.add_one_le_exp (9 : ℝ)
    linarith
  have hdom : ∀ K : ℕ, Real.exp 9 ≤ (K : ℝ) →
      ‖∑ n ∈ Finset.range (K + 1), vonMangoldtPrimeTwist τ n‖
        ≤ routeTTwistEnvelope A delta C τ (K : ℝ) := by
    intro K hK
    have hK10 : (10 : ℝ) ≤ (K : ℝ) := le_trans hexp9 hK
    have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
    have hK1 : (1 : ℕ) ≤ K := by exact_mod_cast le_trans (by norm_num : (1:ℝ) ≤ 10) hK10
    have h3K : (1 : ℝ) ≤ 3 * (K : ℝ) := by linarith
    have h3K0 : (0 : ℝ) < 3 * (K : ℝ) := by linarith
    have hden : (0 : ℝ) < 1 + |τ| := by linarith [abs_nonneg τ]
    have hw0 : 0 < routeTUniformRegWidth A delta (3 * |τ| / 2) :=
      routeTUniformRegWidth_pos hdelta
    have hE0 : (0 : ℝ) ≤ routeTTwistHeightFactor A τ := routeTTwistHeightFactor_nonneg A τ
    have hlogK : (0 : ℝ) ≤ Real.log (K : ℝ) := Real.log_nonneg (by linarith)
    have hlog2K : (0 : ℝ) ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
    have hsq : (0 : ℝ) ≤ (Real.log (K : ℝ)) ^ 2 := by positivity
    have hZ0 : (0 : ℝ) < (3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)) :=
      Real.rpow_pos_of_pos h3K0 _
    have hP1 : (1 : ℝ) ≤ (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3) :=
      Real.one_le_rpow h3K (by linarith)
    have hidα : (3 * (K : ℝ)) ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
        = 3 * (K : ℝ)
          * (3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)) := by
      rw [show (1 : ℝ) - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3
          = 1 + -(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3) by ring,
        Real.rpow_add h3K0, Real.rpow_one]
    have hidβ : (3 * (K : ℝ)) ^ (1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
        = 3 * (K : ℝ)
          * (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3) := by
      rw [Real.rpow_add h3K0, Real.rpow_one]
    have hcomp1 : (K : ℝ)
          * ((3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3))
            * (routeTTwistHeightFactor A τ + Real.log (2 * (K : ℝ))))
        ≤ (3 * (K : ℝ)) ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
            * (routeTTwistHeightFactor A τ + Real.log (2 * (K : ℝ))) := by
      rw [hidα]
      have hstep : (0 : ℝ)
          ≤ (3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3))
            * (routeTTwistHeightFactor A τ + Real.log (2 * (K : ℝ))) := by positivity
      linarith [mul_nonneg hK0.le hstep]
    have hcomp2 : (K : ℝ)
          * ((1 + (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
              * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ)) / (1 + |τ|))
        ≤ (3 * (K : ℝ)) ^ (1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
            * (1 + (Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|) := by
      rw [hidβ]
      have hX : (0 : ℝ) ≤ (Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ := by linarith
      have hP0 : (0 : ℝ)
          ≤ (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3) := by
        linarith
      have hKP : (K : ℝ)
          ≤ 3 * (K : ℝ)
            * (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3) := by
        linarith [mul_le_mul_of_nonneg_left hP1 (by linarith : (0 : ℝ) ≤ 3 * (K : ℝ))]
      have hKPX : (0 : ℝ)
          ≤ (K : ℝ) * (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
            * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ) := by positivity
      have hnum : (K : ℝ)
            * (1 + (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
              * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ))
          ≤ 3 * (K : ℝ)
            * (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
            * (1 + (Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ) := by
        linarith [hKP, hKPX]
      calc (K : ℝ)
            * ((1 + (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
                * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ)) / (1 + |τ|))
          = ((K : ℝ)
              * (1 + (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
                * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ))) / (1 + |τ|) := by
            ring
        _ ≤ (3 * (K : ℝ)
              * (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
              * (1 + (Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ)) / (1 + |τ|) :=
            div_le_div_of_nonneg_right hnum hden.le
    have hpp := primePowerDefect_le hK1
    have hstep := norm_partialSum_vonMangoldtPrimeTwist_le τ K (hbound K τ hK)
    have hfin : ‖∑ n ∈ Finset.range (K + 1), vonMangoldtPrimeTwist τ n‖
        ≤ C * (K : ℝ)
            * ((3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3))
                  * (routeTTwistHeightFactor A τ + Real.log (2 * (K : ℝ)))
                + (1 + (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
                      * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ))
                    / (1 + |τ|))
          + 2 * Real.sqrt (K : ℝ) * Real.log (K : ℝ) := by
      linarith [hstep, hpp]
    refine hfin.trans ?_
    rw [routeTTwistEnvelope]
    have hexpand : C * (K : ℝ)
        * ((3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3))
              * (routeTTwistHeightFactor A τ + Real.log (2 * (K : ℝ)))
            + (1 + (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
                  * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ))
                / (1 + |τ|))
        = C * ((K : ℝ)
              * ((3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3))
                * (routeTTwistHeightFactor A τ + Real.log (2 * (K : ℝ))))
            + (K : ℝ)
              * ((1 + (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
                  * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ))
                  / (1 + |τ|))) := by ring
    rw [hexpand]
    have hmul : C * ((K : ℝ)
            * ((3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3))
              * (routeTTwistHeightFactor A τ + Real.log (2 * (K : ℝ))))
          + (K : ℝ)
            * ((1 + (3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
                * ((Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ))
                / (1 + |τ|)))
        ≤ C * ((3 * (K : ℝ)) ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
              * (routeTTwistHeightFactor A τ + Real.log (2 * (K : ℝ)))
            + (3 * (K : ℝ)) ^ (1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
                * (1 + (Real.log (K : ℝ)) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|)) :=
      mul_le_mul_of_nonneg_left (by linarith [hcomp1, hcomp2]) hC.le
    linarith [hmul]
  refine norm_sum_primeTwist_le_of_monotone_bound τ N
    (fun m => routeTTwistEnvelope A delta C τ (max (m : ℝ) 1) + 7 * Real.exp 9) ?_ ?_
  · intro m _
    have hmax1 : (1 : ℝ) ≤ max (m : ℝ) 1 := le_max_right _ _
    have hnn : (0 : ℝ) ≤ routeTTwistEnvelope A delta C τ (max (m : ℝ) 1) :=
      routeTTwistEnvelope_nonneg hC.le hmax1
    rcases le_or_gt (Real.exp 9) (m : ℝ) with hcase | hcase
    · have hmax : max (m : ℝ) 1 = (m : ℝ) := max_eq_left (by linarith [hexp9])
      rw [hmax]
      have hd := hdom m hcase
      have hpos : (0 : ℝ) ≤ 7 * Real.exp 9 := by positivity
      linarith
    · have hcr := norm_partialSum_vonMangoldtPrimeTwist_le_crude τ m
      have h7 : (7 : ℝ) * (m : ℝ) ≤ 7 * Real.exp 9 := by linarith
      linarith
  · intro m hm
    have hmax1 : (1 : ℝ) ≤ max (m : ℝ) 1 := le_max_right _ _
    have hmm : max (m : ℝ) 1 ≤ max (N : ℝ) 1 := by
      have hcast : ((m : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hm
      exact max_le_max hcast le_rfl
    have hmono := routeTTwistEnvelope_mono (A := A) (delta := delta) (C := C) (τ := τ)
      hdelta hC.le hmax1 hmm
    linarith

end RHTower.Sieve
