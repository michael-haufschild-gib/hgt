import GaloisForLFunctions.RHTower.Sieve.ChebyshevMasterInequality
import GaloisForLFunctions.RHTower.Sieve.PerronErrorTotalChebyshev
import GaloisForLFunctions.RHTower.Sieve.PerronHorizontalSide
import GaloisForLFunctions.RHTower.Sieve.PerronIntegrandContinuity

/-!
# The Chebyshev error under the Riemann hypothesis, in closed form

Instantiating the master inequality at `σ₁ = 1/2 + ε/2`, `σ₀ = 1 + ε/2` and truncation height
`T = N + 1/2` makes every one of the four terms a constant times `x^{1/2+ε/2}(1 + log x)^2`:
the Perron error is polylogarithmic, the shifted vertical side carries `x^{σ₁}` and two
logarithms, and each horizontal side is `x^{ε/2} log x` because the height cancels a whole power.
-/

set_option maxHeartbeats 2000000

namespace RHTower.Sieve

open Complex ArithmeticFunction

noncomputable section

/-- **The Chebyshev error at a half-integer cutoff, under RH.**  For every `ε ∈ (0, 1/4]` there is
a constant `C` with `|ψ(N) − N| ≤ C·(N+1/2)^{1/2+ε/2}(1 + log(N+1/2))^2` for all `N ≥ 7`. -/
theorem exists_chebyshev_error_halfInt_bound (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 7 ≤ N →
      |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ)|
        ≤ C * (((N : ℝ) + 1 / 2) ^ (1 / 2 + ε / 2)
            * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hσ₁ : (1 : ℝ) / 2 < 1 / 2 + ε / 2 := by linarith
  have hσ₁1 : (1 : ℝ) / 2 + ε / 2 < 1 := by linarith
  have hσ₀ : (1 : ℝ) < 1 + ε / 2 := by linarith
  have hσ₀2 : (1 : ℝ) + ε / 2 ≤ 2 := by linarith
  have hσ₀98 : (1 : ℝ) + ε / 2 ≤ 9 / 8 := by linarith
  have hσ₁σ₀ : (1 : ℝ) / 2 + ε / 2 ≤ 1 + ε / 2 := by linarith
  have hσ₁0 : (0 : ℝ) < 1 / 2 + ε / 2 := by linarith
  obtain ⟨K, hK0, hK⟩ := exists_logDeriv_zeta_line_bound hRH hσ₁ hσ₁1
  obtain ⟨C, hC0, hC⟩ := exists_logDeriv_zeta_bound_rh hRH
  refine ⟨32 / (Real.pi * Real.log 2 * ε ^ 2) + 192 / Real.pi + 7 * K / Real.pi
      + C / (Real.pi * ε) + 1 / 2, by positivity, ?_⟩
  intro N hN
  have hN7 : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < (N : ℝ) + 1 / 2 := by linarith
  have hx1 : (1 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hx4 : (4 : ℝ) ≤ (N : ℝ) + 1 / 2 := by linarith
  have hlogx0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1 / 2) := Real.log_nonneg hx1
  have hL1 : (1 : ℝ) ≤ 1 + Real.log ((N : ℝ) + 1 / 2) := by linarith
  have hL2 : (1 : ℝ) ≤ (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 := by nlinarith [hL1]
  have hP1 : (1 : ℝ) ≤ ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + ε / 2) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show (0 : ℝ) ≤ 1 / 2 + ε / 2 by linarith)
  have hxrp : ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) + ε / 2)
      = ((N : ℝ) + 1 / 2) * ((N : ℝ) + 1 / 2) ^ (ε / 2) := by
    rw [Real.rpow_add hx0, Real.rpow_one]
  have hxe : ((N : ℝ) + 1 / 2) ^ (ε / 2) ≤ ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hxe0 : (0 : ℝ) ≤ ((N : ℝ) + 1 / 2) ^ (ε / 2) := Real.rpow_nonneg hx0.le _
  -- the target quantity
  set Q : ℝ := ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + ε / 2)
      * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 with hQdef
  have hQ0 : (0 : ℝ) ≤ Q := by
    rw [hQdef]; positivity
  have hQ1 : (1 : ℝ) ≤ Q := by
    rw [hQdef]; nlinarith [hP1, hL2]
  have hQxe : ((N : ℝ) + 1 / 2) ^ (ε / 2) ≤ Q := by
    rw [hQdef]; nlinarith [hxe, hL2, hP1]
  have hQL : (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 ≤ Q := by
    rw [hQdef]; nlinarith [hP1, hL2]
  have hQlogxe : Real.log ((N : ℝ) + 1 / 2) * ((N : ℝ) + 1 / 2) ^ (ε / 2) ≤ Q := by
    rw [hQdef]
    have hlogle : Real.log ((N : ℝ) + 1 / 2) ≤ (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 := by
      nlinarith [hL1, hlogx0]
    have := mul_le_mul hlogle hxe hxe0 (by nlinarith [hL1])
    nlinarith [this]
  -- the master inequality
  have hmaster := norm_chebyshev_sub_halfInt_le (N := N) (σ₁ := 1 / 2 + ε / 2)
    (σ₀ := 1 + ε / 2) (T := (N : ℝ) + 1 / 2) hRH hσ₁ hσ₁1 hσ₀ hx0
  have hE := perron_error_vonMangoldt_total_le (N := N) (σ := 1 + ε / 2)
    (T := (N : ℝ) + 1 / 2) (by omega) hσ₀ hσ₀2 hx0
  have hcont := continuous_perron_integrand_line hRH (x := (N : ℝ) + 1 / 2)
    (σ := 1 / 2 + ε / 2) hx0 hσ₁ hσ₁1
  have hV := norm_vIntegral_perron_le (x := (N : ℝ) + 1 / 2) (σ := 1 / 2 + ε / 2)
    (T := (N : ℝ) + 1 / 2) (K := K) hx0 hσ₁0 hx1 hK0.le hK hcont
  have habs : |(N : ℝ) + 1 / 2| = (N : ℝ) + 1 / 2 := abs_of_pos hx0
  have habsneg : |-((N : ℝ) + 1 / 2)| = (N : ℝ) + 1 / 2 := by rw [abs_neg]; exact habs
  have hHp := norm_hIntegral_perron_le (x := (N : ℝ) + 1 / 2) (σ₁ := 1 / 2 + ε / 2)
    (σ₀ := 1 + ε / 2) (y := (N : ℝ) + 1 / 2) (C := C) hx1 hσ₁ hσ₁σ₀ hσ₀98
    (by rw [habs]; linarith) hC0 hC
  have hHm := norm_hIntegral_perron_le (x := (N : ℝ) + 1 / 2) (σ₁ := 1 / 2 + ε / 2)
    (σ₀ := 1 + ε / 2) (y := -((N : ℝ) + 1 / 2)) (C := C) hx1 hσ₁ hσ₁σ₀ hσ₀98
    (by rw [habsneg]; linarith) hC0 hC
  rw [habs] at hHp
  rw [habsneg] at hHm
  -- the Perron error
  have hcast : ((2 * N + 2 : ℕ) : ℝ) = 2 * (N : ℝ) + 2 := by push_cast; ring
  have hE1 : (1 / (Real.pi * ((N : ℝ) + 1 / 2) * Real.log 2))
        * (((N : ℝ) + 1 / 2) ^ ((1 : ℝ) + ε / 2) * (8 / ((1 + ε / 2) - 1) ^ 2))
      = (32 / (Real.pi * Real.log 2 * ε ^ 2)) * ((N : ℝ) + 1 / 2) ^ (ε / 2) := by
    rw [show ((1 : ℝ) + ε / 2) - 1 = ε / 2 by ring, hxrp]
    field_simp
    ring
  have hlog2x : Real.log (2 * ((N : ℝ) + 1 / 2)) ≤ 1 + Real.log ((N : ℝ) + 1 / 2) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  have hlog2x0 : (0 : ℝ) ≤ Real.log (2 * ((N : ℝ) + 1 / 2)) := Real.log_nonneg (by linarith)
  have hlogN2 : 1 + Real.log ((2 * N + 2 : ℕ) : ℝ) ≤ 3 * (1 + Real.log ((N : ℝ) + 1 / 2)) := by
    rw [hcast]
    have hmono : Real.log (2 * (N : ℝ) + 2) ≤ Real.log (4 * ((N : ℝ) + 1 / 2)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at hmono
    have hl4 : Real.log 4 ≤ Real.log ((N : ℝ) + 1 / 2) := Real.log_le_log (by norm_num) hx4
    linarith
  have hlogN20 : (0 : ℝ) ≤ 1 + Real.log ((2 * N + 2 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ Real.log ((2 * N + 2 : ℕ) : ℝ) := by
      rw [hcast]; exact Real.log_nonneg (by linarith)
    linarith
  have hE2 : (16 * Real.log (2 * ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1 / 2)
        / (Real.pi * ((N : ℝ) + 1 / 2))) * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ)))
      ≤ (192 / Real.pi) * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 := by
    have hid : 16 * Real.log (2 * ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1 / 2)
        / (Real.pi * ((N : ℝ) + 1 / 2))
        * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ)))
        = (64 * Real.log (2 * ((N : ℝ) + 1 / 2)) * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ)))
          / Real.pi := by
      field_simp
      ring
    have hid2 : (192 / Real.pi) * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2
        = (192 * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2) / Real.pi := by ring
    rw [hid, hid2]
    have hnum : 64 * Real.log (2 * ((N : ℝ) + 1 / 2)) * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))
        ≤ 192 * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 := by
      nlinarith [mul_le_mul hlog2x hlogN2 hlogN20 (by linarith : (0:ℝ) ≤ 1 + Real.log ((N : ℝ) + 1 / 2))]
    gcongr
  -- the vertical side
  have hlog3 : Real.log 3 ≤ 1.4 := by
    have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    nlinarith [Real.log_two_lt_d9]
  have hVb : 2 * (1 + Real.log 3) / (1 / 2 + ε / 2)
        + 2 * (1 + Real.log (2 + ((N : ℝ) + 1 / 2))) * Real.log ((N : ℝ) + 1 / 2)
      ≤ 14 * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2 := by
    have h1 : 2 * (1 + Real.log 3) / (1 / 2 + ε / 2) ≤ 10 := by
      rw [div_le_iff₀ hσ₁0]
      nlinarith [hlog3, hε]
    have h2 : 1 + Real.log (2 + ((N : ℝ) + 1 / 2))
        ≤ 2 * (1 + Real.log ((N : ℝ) + 1 / 2)) := by
      have hmono : Real.log (2 + ((N : ℝ) + 1 / 2)) ≤ Real.log (4 * ((N : ℝ) + 1 / 2)) :=
        Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at hmono
      have hl4 : Real.log 4 ≤ Real.log ((N : ℝ) + 1 / 2) := Real.log_le_log (by norm_num) hx4
      linarith
    have h4 : (1 + Real.log (2 + ((N : ℝ) + 1 / 2))) * Real.log ((N : ℝ) + 1 / 2)
        ≤ (2 * (1 + Real.log ((N : ℝ) + 1 / 2))) * (1 + Real.log ((N : ℝ) + 1 / 2)) :=
      mul_le_mul h2 (by linarith) hlogx0 (by linarith)
    nlinarith [h1, h4, hL2]
  have hVfin : ‖VIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
        * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) (1 / 2 + ε / 2)
        (-((N : ℝ) + 1 / 2)) ((N : ℝ) + 1 / 2)‖
      ≤ 14 * K * Q := by
    refine hV.trans ?_
    have hcoef : (0 : ℝ) ≤ K * ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + ε / 2) := by
      have : (0 : ℝ) ≤ ((N : ℝ) + 1 / 2) ^ ((1 : ℝ) / 2 + ε / 2) := Real.rpow_nonneg hx0.le _
      positivity
    have := mul_le_mul_of_nonneg_left hVb hcoef
    rw [hQdef]
    nlinarith [this]
  -- the horizontal sides
  have hHid : (C * Real.log ((N : ℝ) + 1 / 2) / ((1 / 2 + ε / 2) - 1 / 2))
        * (((N : ℝ) + 1 / 2) ^ ((1 : ℝ) + ε / 2) / ((N : ℝ) + 1 / 2))
        * |(1 + ε / 2) - (1 / 2 + ε / 2)|
      = (C / ε) * (Real.log ((N : ℝ) + 1 / 2) * ((N : ℝ) + 1 / 2) ^ (ε / 2)) := by
    rw [show ((1 : ℝ) / 2 + ε / 2) - 1 / 2 = ε / 2 by ring,
      show |((1 : ℝ) + ε / 2) - (1 / 2 + ε / 2)| = 1 / 2 by
        rw [show ((1 : ℝ) + ε / 2) - (1 / 2 + ε / 2) = 1 / 2 by ring]; norm_num,
      hxrp]
    field_simp
  rw [hHid] at hHp hHm
  -- assemble
  have hHq : (C / ε) * (Real.log ((N : ℝ) + 1 / 2) * ((N : ℝ) + 1 / 2) ^ (ε / 2))
      ≤ (C / ε) * Q := mul_le_mul_of_nonneg_left hQlogxe (by positivity)
  have hEq1 : (32 / (Real.pi * Real.log 2 * ε ^ 2)) * ((N : ℝ) + 1 / 2) ^ (ε / 2)
      ≤ (32 / (Real.pi * Real.log 2 * ε ^ 2)) * Q :=
    mul_le_mul_of_nonneg_left hQxe (by positivity)
  have hEq2 : (192 / Real.pi) * (1 + Real.log ((N : ℝ) + 1 / 2)) ^ 2
      ≤ (192 / Real.pi) * Q := mul_le_mul_of_nonneg_left hQL (by positivity)
  rw [hE1] at hE
  have htri : |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - (N : ℝ)|
      ≤ |(∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) - ((N : ℝ) + 1 / 2)| + 1 / 2 := by
    have h1 := abs_sub_le (∑ n ∈ Finset.Icc 1 N, (Λ n : ℝ)) ((N : ℝ) + 1 / 2) (N : ℝ)
    have h2 : |((N : ℝ) + 1 / 2) - (N : ℝ)| = 1 / 2 := by
      rw [show ((N : ℝ) + 1 / 2) - (N : ℝ) = 1 / 2 by ring]
      norm_num
    rw [h2] at h1
    exact h1
  have hhalf : (1 : ℝ) / 2 ≤ 1 / 2 * Q := by nlinarith [hQ1]
  have hexpand : (32 / (Real.pi * Real.log 2 * ε ^ 2) + 192 / Real.pi + 7 * K / Real.pi
        + C / (Real.pi * ε) + 1 / 2) * Q
      = (32 / (Real.pi * Real.log 2 * ε ^ 2)) * Q + (192 / Real.pi) * Q
        + (1 / (2 * Real.pi)) * (14 * K * Q)
        + (1 / (2 * Real.pi)) * ((C / ε) * Q + (C / ε) * Q) + 1 / 2 * Q := by
    field_simp
    ring
  rw [hexpand]
  have hpiinv : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have hsides : ‖VIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
        * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) (1 / 2 + ε / 2)
        (-((N : ℝ) + 1 / 2)) ((N : ℝ) + 1 / 2)‖
      + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
        * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) (1 / 2 + ε / 2) (1 + ε / 2)
        ((N : ℝ) + 1 / 2)‖
      + ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
        * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s / s)) (1 / 2 + ε / 2) (1 + ε / 2)
        (-((N : ℝ) + 1 / 2))‖
      ≤ 14 * K * Q + ((C / ε) * Q + (C / ε) * Q) := by
    linarith [hVfin, hHp.trans hHq, hHm.trans hHq]
  have hscaled := mul_le_mul_of_nonneg_left hsides hpiinv
  linarith [hmaster, hE, hE2, hEq1, hEq2, htri, hhalf, hscaled]

end

end RHTower.Sieve
