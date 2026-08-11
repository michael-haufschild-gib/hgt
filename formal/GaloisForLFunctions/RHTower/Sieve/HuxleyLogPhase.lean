import GaloisForLFunctions.RHTower.Sieve.KuzminLandauInterval
import GaloisForLFunctions.RHTower.Sieve.LogPhaseBlock

/-!
# The two logarithmic-phase estimates behind Huxley's large-values theorem

On a dyadic block `[N,2N)` there are two genuinely different frequency regimes.

* If `0 < t <= 4*pi*N/3`, Kuzmin--Landau sees the derivative of
  `-(t/2*pi) log x` inside the single non-resonant band `[-1+delta,-delta]`, with
  `delta=t/(4*pi*N)`.  This gives the sharp reciprocal bound `6*pi*N/t+1`.
* At larger frequencies the existing second-derivative test gives the exponent-pair
  `(1/2,1/2)` bound.  We retain its exact expression so later large-value arguments can
  compare endpoints without hiding an asymptotic constant.

Together these are the analytic input missing from the Halasz--Montgomery row formalisation.
-/

namespace RHTower.Sieve

open Real

/-- Derivative scale of the logarithmic phase on `[N,2N]`. -/
noncomputable def logDyadicLambda (N : ℕ) (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * (Nat.factorial 1 : ℝ) / (2 * (N : ℝ)) ^ 2

/-- Exact second-derivative envelope returned by `dirichlet_block_bound` at order two. -/
noncomputable def logDyadicSecondBound (N : ℕ) (t : ℝ) : ℝ :=
  256 * ((N : ℝ) * (16 * logDyadicLambda N t) ^ (1 / 2 : ℝ)
    + (logDyadicLambda N t) ^ (-(1 / 2 : ℝ)))

/-- Endpoint envelope for the second-derivative estimate on a frequency window `[U,T]`. -/
noncomputable def logDyadicSecondEnvelope (N : ℕ) (U T : ℝ) : ℝ :=
  256 * ((N : ℝ) * (16 * logDyadicLambda N T) ^ (1 / 2 : ℝ)
    + (logDyadicLambda N U) ^ (-(1 / 2 : ℝ)))

theorem logDyadicLambda_pos {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) :
    0 < logDyadicLambda N t := by
  simp only [logDyadicLambda]
  norm_num
  positivity

theorem logDyadicLambda_mono {N : ℕ} (hN : 1 ≤ N) {u v : ℝ} (huv : u ≤ v) :
    logDyadicLambda N u ≤ logDyadicLambda N v := by
  simp only [logDyadicLambda]
  norm_num
  have hden : 0 < 2 * Real.pi := by positivity
  have hpow : 0 < (2 * (N : ℝ)) ^ 2 := by
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    positivity
  exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right huv hden.le) hpow.le

/-- The order-two bound is controlled by the top endpoint in its increasing term and the bottom
endpoint in its decreasing term. -/
theorem logDyadicSecondBound_le_envelope {N : ℕ} (hN : 1 ≤ N)
    {U u T : ℝ} (hU : 0 < U) (hUu : U ≤ u) (huT : u ≤ T) :
    logDyadicSecondBound N u ≤ logDyadicSecondEnvelope N U T := by
  have hlamU0 : 0 < logDyadicLambda N U := logDyadicLambda_pos hN hU
  have hlamUu : logDyadicLambda N U ≤ logDyadicLambda N u :=
    logDyadicLambda_mono hN hUu
  have hlamu0 : 0 < logDyadicLambda N u :=
    logDyadicLambda_pos hN (lt_of_lt_of_le hU hUu)
  have hlamuT : logDyadicLambda N u ≤ logDyadicLambda N T :=
    logDyadicLambda_mono hN huT
  have hfirst : (16 * logDyadicLambda N u) ^ (1 / 2 : ℝ)
      ≤ (16 * logDyadicLambda N T) ^ (1 / 2 : ℝ) := by
    refine Real.rpow_le_rpow (mul_nonneg (by norm_num) hlamu0.le)
      (mul_le_mul_of_nonneg_left hlamuT (by norm_num)) ?_
    norm_num
  have hsecond : (logDyadicLambda N u) ^ (-(1 / 2 : ℝ))
      ≤ (logDyadicLambda N U) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hlamU0 hlamUu (by norm_num)
  unfold logDyadicSecondBound logDyadicSecondEnvelope
  gcongr

/-- **Kuzmin--Landau for a dyadic logarithmic block.**  Below the first derivative
resonance, the unweighted block has reciprocal-frequency size. -/
theorem norm_logPhase_dyadic_le_kuzminLandau (t : ℝ) (ht : 0 < t) (N : ℕ) (hN : 1 ≤ N)
    (htN : 3 * t ≤ 4 * Real.pi * (N : ℝ)) :
    ‖∑ j ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * logPhase t ((N : ℝ) + j) : ℝ) : ℂ) * Complex.I)‖
      ≤ 6 * Real.pi * (N : ℝ) / t + 1 := by
  let delta : ℝ := t / (4 * Real.pi * (N : ℝ))
  have hpi := Real.pi_pos
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hspan : (N : ℝ) + ((N - 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have hsub : N - 1 ≤ N := Nat.sub_le N 1
    have hsubR : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsub
    linarith
  have hderiv : ∀ x ∈ Set.Icc (N : ℝ) ((N : ℝ) + ((N - 1 : ℕ) : ℝ)),
      HasDerivAt (logPhase t) (logPhaseChain t 1 x) x := by
    intro x hx
    exact logPhaseChain_hasDerivAt t 0 (lt_of_lt_of_le hNR hx.1)
  have hmono : MonotoneOn (logPhaseChain t 1)
      (Set.Icc (N : ℝ) ((N : ℝ) + ((N - 1 : ℕ) : ℝ))) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le hNR hx.1
    have hy0 : 0 < y := lt_of_lt_of_le hNR hy.1
    have hinv : y⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 hxy
    simp only [logPhaseChain]
    norm_num
    have hc : 0 ≤ t / (2 * Real.pi) := by positivity
    nlinarith
  have hlo : ∀ x ∈ Set.Icc (N : ℝ) ((N : ℝ) + ((N - 1 : ℕ) : ℝ)),
      ((-1 : ℤ) : ℝ) + delta ≤ logPhaseChain t 1 x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hNR hx.1
    have hinv : x⁻¹ ≤ ((N : ℝ))⁻¹ := inv_anti₀ hNR hx.1
    simp only [logPhaseChain]
    norm_num
    dsimp [delta]
    have hden : 0 < 4 * Real.pi * (N : ℝ) := by positivity
    have h3delta : 3 * delta ≤ 1 := by
      dsimp [delta]
      have hq := (div_le_one hden).2 (by simpa [mul_assoc] using htN)
      have heqdiv : 3 * (t / (4 * Real.pi * (N : ℝ))) =
          3 * t / (4 * Real.pi * (N : ℝ)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [heqdiv]
      exact hq
    have hc : 0 ≤ t / (2 * Real.pi) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinv hc
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
    have heq : t / (2 * Real.pi) * ((N : ℝ))⁻¹ = 2 * delta := by
      dsimp [delta]
      field_simp [hNne, Real.pi_ne_zero]
      ring
    rw [heq] at hmul
    change delta + t / (2 * Real.pi) * x⁻¹ ≤ 1
    linarith
  have hhi : ∀ x ∈ Set.Icc (N : ℝ) ((N : ℝ) + ((N - 1 : ℕ) : ℝ)),
      logPhaseChain t 1 x ≤ ((-1 : ℤ) : ℝ) + 1 - delta := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hNR hx.1
    have hx2N : x ≤ 2 * (N : ℝ) := hx.2.trans hspan
    have hinv : (2 * (N : ℝ))⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 hx2N
    simp only [logPhaseChain]
    norm_num
    dsimp [delta]
    have hc : 0 ≤ t / (2 * Real.pi) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinv hc
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
    field_simp [hNne]
    nlinarith
  have hmain := kuzminLandau_interval (logPhase t) (logPhaseChain t 1) (N : ℝ)
    (N - 1) (-1) hdelta hderiv hmono hlo hhi
  rw [Nat.sub_add_cancel hN] at hmain
  convert hmain using 1 <;> dsimp [delta]
  field_simp
  <;> ring

/-- The order-two derivative test on the same dyadic block, in its exact endpoint form. -/
theorem norm_logPhase_dyadic_le_secondDerivative (t : ℝ) (ht : 0 < t)
    (N : ℕ) (hN : 1 ≤ N) (hlam : logDyadicLambda N t ≤ 1) :
    ‖∑ j ∈ Finset.range N,
        ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ logDyadicSecondBound N t := by
  have hspan : N + N ≤ 2 * N + 1 := by omega
  have h := dirichlet_block_bound t ht 2 N N (by omega) hN hN hspan
    (by simpa [logDyadicLambda] using hlam)
  norm_num at h
  simpa [logDyadicSecondBound, logDyadicLambda] using h

end RHTower.Sieve
