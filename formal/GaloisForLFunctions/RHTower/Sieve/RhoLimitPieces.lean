import GaloisForLFunctions.RHTower.Sieve.BudgetRhoBound
import GaloisForLFunctions.RHTower.Sieve.RoughRemainderLimit

/-!
# The pieces of the annulus constant, in powers of the logarithm

Each factor of the annulus constant is bounded by an explicit power of `log x`, and the contour
factor by a stretched exponential.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The smoothing width, bounded. -/
theorem eventually_ladderWidth_le {β : ℝ} (hβ0 : 0 < β) :
    ∀ᶠ x : ℝ in atTop, ladderWidth β x ≤ 16 * (Real.log x) ^ (4 * β) := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ0).comp Real.tendsto_log_atTop
  filter_upwards [hpow.eventually_ge_atTop (Real.log 2), Filter.eventually_gt_atTop (1 : ℝ),
    hpow.eventually_ge_atTop (1 : ℝ)] with x hbig hx1 hbig1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hval : Real.log (2 * cardLength β x) = Real.log 2 + (Real.log x) ^ β := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos β x)), log_cardLength]
  have hle : Real.log (2 * cardLength β x) ≤ 2 * (Real.log x) ^ β := by
    rw [hval]
    linarith
  have h0 : (0 : ℝ) ≤ Real.log (2 * cardLength β x) := by
    rw [hval]
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hpow4 : (Real.log (2 * cardLength β x)) ^ 4 ≤ (2 * (Real.log x) ^ β) ^ 4 :=
    pow_le_pow_left₀ h0 hle 4
  have hexp : (2 * (Real.log x) ^ β) ^ 4 = 16 * ((Real.log x) ^ β) ^ 4 := by ring
  have hrpow : ((Real.log x) ^ β) ^ 4 = (Real.log x) ^ (4 * β) := by
    rw [← Real.rpow_natCast ((Real.log x) ^ β) 4, ← Real.rpow_mul hlogx.le]
    congr 1
    push_cast
    ring
  rw [ladderWidth]
  rw [hexp, hrpow] at hpow4
  exact hpow4

/-- The iterated logarithm is below every power of the logarithm. -/
theorem eventually_logLog_sq_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (1 + Real.log (18 + Real.log x)) ^ 2 ≤ (Real.log x) ^ ε := by
  have hsmall := tendsto_logLog_div_logRpow (δ := ε / 4) (by linarith)
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ (ε / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1 / 4) hsmall,
    Filter.eventually_ge_atTop (Real.exp 18), Filter.eventually_gt_atTop (1 : ℝ),
    hpow.eventually_ge_atTop (4 : ℝ)] with x hsm hxe hx1 hbig
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlog18 : (18 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 18) hxe
    rwa [Real.log_exp] at this
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg (by linarith)
  have hpow0 : (0 : ℝ) < (Real.log x) ^ (ε / 4) := Real.rpow_pos_of_pos hlogx _
  rw [div_le_iff₀ hpow0] at hsm
  have hstep : Real.log (18 + Real.log x) ≤ Real.log 2 + Real.log (Real.log x) := by
    have h2 : (18 : ℝ) + Real.log x ≤ 2 * Real.log x := by linarith
    have := Real.log_le_log (by linarith) h2
    rwa [Real.log_mul (by norm_num) (ne_of_gt hlogx)] at this
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hbnd : 1 + Real.log (18 + Real.log x) ≤ (Real.log x) ^ (ε / 4) := by
    have : Real.log (Real.log x) ≤ 1 / 4 * (Real.log x) ^ (ε / 4) := hsm
    linarith [hstep, hl2, hbig]
  have hnn : (0 : ℝ) ≤ 1 + Real.log (18 + Real.log x) := by
    have : (0 : ℝ) ≤ Real.log (18 + Real.log x) := Real.log_nonneg (by linarith)
    linarith
  have hsq : (1 + Real.log (18 + Real.log x)) ^ 2 ≤ ((Real.log x) ^ (ε / 4)) ^ 2 :=
    pow_le_pow_left₀ hnn hbnd 2
  have hid : ((Real.log x) ^ (ε / 4)) ^ 2 = (Real.log x) ^ (ε / 2) := by
    rw [← Real.rpow_natCast ((Real.log x) ^ (ε / 4)) 2, ← Real.rpow_mul hlogx.le]
    congr 1
    push_cast
    ring
  rw [hid] at hsq
  refine hsq.trans ?_
  refine Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- The reciprocal width surrogate, bounded by a power of the logarithm. -/
theorem eventually_budgetWinv_le {A ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      budgetWinv A x
        ≤ 20 * routeTZeroFreeDeltaEnvelopeConstant A * (Real.log x) ^ ((9 : ℝ) / 10 + ε) := by
  filter_upwards [eventually_logLog_sq_le (ε := ε) hε,
    Filter.eventually_ge_atTop (Real.exp 18), Filter.eventually_gt_atTop (1 : ℝ)]
    with x hll hxe hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlog18 : (18 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 18) hxe
    rwa [Real.log_exp] at this
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hZ : budgetZ x ≤ 2 * Real.log x := by
    rw [budgetZ]
    linarith
  have hZ0 : (0 : ℝ) < budgetZ x := by
    rw [budgetZ]
    linarith
  have hpow : (budgetZ x) ^ ((9 : ℝ) / 10) ≤ 2 * (Real.log x) ^ ((9 : ℝ) / 10) := by
    have h1 : (budgetZ x) ^ ((9 : ℝ) / 10) ≤ (2 * Real.log x) ^ ((9 : ℝ) / 10) :=
      Real.rpow_le_rpow hZ0.le hZ (by norm_num)
    have h2 : (2 * Real.log x) ^ ((9 : ℝ) / 10)
        = (2 : ℝ) ^ ((9 : ℝ) / 10) * (Real.log x) ^ ((9 : ℝ) / 10) :=
      Real.mul_rpow (by norm_num) hlogx.le
    have h3 : (2 : ℝ) ^ ((9 : ℝ) / 10) ≤ 2 := by
      calc (2 : ℝ) ^ ((9 : ℝ) / 10) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hp0 : (0 : ℝ) ≤ (Real.log x) ^ ((9 : ℝ) / 10) := Real.rpow_nonneg hlogx.le _
    nlinarith [h1, h2, h3, hp0]
  have hll' : (1 + Real.log (budgetZ x)) ^ 2 ≤ (Real.log x) ^ ε := by
    rw [budgetZ]
    exact hll
  have hpow0 : (0 : ℝ) ≤ (budgetZ x) ^ ((9 : ℝ) / 10) := Real.rpow_nonneg hZ0.le _
  have hsq0 : (0 : ℝ) ≤ (1 + Real.log (budgetZ x)) ^ 2 := sq_nonneg _
  have hprod : (budgetZ x) ^ ((9 : ℝ) / 10) * (1 + Real.log (budgetZ x)) ^ 2
      ≤ 2 * (Real.log x) ^ ((9 : ℝ) / 10) * (Real.log x) ^ ε := by
    refine mul_le_mul hpow hll' hsq0 (by positivity)
  have hcomb : (Real.log x) ^ ((9 : ℝ) / 10) * (Real.log x) ^ ε
      = (Real.log x) ^ ((9 : ℝ) / 10 + ε) := (Real.rpow_add hlogx _ _).symm
  rw [budgetWinv]
  nlinarith [hprod, hcomb, hD]

/-- The reciprocal width surrogate grows. -/
theorem tendsto_budgetWinv {A : ℝ} :
    Tendsto (fun x : ℝ => budgetWinv A x) atTop atTop := by
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hZ : Tendsto (fun x : ℝ => (budgetZ x) ^ ((9 : ℝ) / 10)) atTop atTop := by
    have h : Tendsto (fun x : ℝ => budgetZ x) atTop atTop := by
      have := Filter.tendsto_atTop_add_const_left atTop (18 : ℝ) Real.tendsto_log_atTop
      exact this.congr fun x => rfl
    exact (tendsto_rpow_atTop (by norm_num)).comp h
  have hmul : Tendsto (fun x : ℝ =>
      10 * routeTZeroFreeDeltaEnvelopeConstant A * (budgetZ x) ^ ((9 : ℝ) / 10)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hZ
  refine Filter.tendsto_atTop_mono' _ ?_ hmul
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx1
  have hZ1 : (1 : ℝ) ≤ budgetZ x := one_le_budgetZ hx1
  have hpow0 : (0 : ℝ) ≤ (budgetZ x) ^ ((9 : ℝ) / 10) := Real.rpow_nonneg (by linarith) _
  have hlogZ : (0 : ℝ) ≤ Real.log (budgetZ x) := Real.log_nonneg hZ1
  have hsq : (1 : ℝ) ≤ (1 + Real.log (budgetZ x)) ^ 2 := by nlinarith [hlogZ]
  rw [budgetWinv]
  have h0 : (0 : ℝ) ≤ 10 * routeTZeroFreeDeltaEnvelopeConstant A
      * (budgetZ x) ^ ((9 : ℝ) / 10) := by positivity
  nlinarith [hsq, h0]

/-- **The contour factor beats every polylogarithm.** -/
theorem eventually_exp_mu_q_le {A delta β γ : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hγβ : 9 / 10 < γ * β) (hdelta : 0 < delta) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-(min delta (1 / budgetWinv A x) / 2
          * Real.log ((siftStart (γ * β) x : ℕ) : ℝ)))
        ≤ Real.exp (-((Real.log x) ^ ((γ * β - 9 / 10) / 4))) := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hε : (0 : ℝ) < (γ * β - 9 / 10) / 2 := by linarith
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hbig : Tendsto (fun x : ℝ => (Real.log x) ^ ((γ * β - 9 / 10) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_budgetWinv_le (A := A) hε,
    (tendsto_budgetWinv (A := A)).eventually_ge_atTop (1 / delta),
    Filter.eventually_gt_atTop (1 : ℝ),
    hbig.eventually_ge_atTop (40 * routeTZeroFreeDeltaEnvelopeConstant A),
    Filter.eventually_ge_atTop (Real.exp 1)] with x hW hWbig hx1 hbg hxe
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hW0 : (0 : ℝ) < budgetWinv A x := budgetWinv_pos hx1.le
  have hmin : min delta (1 / budgetWinv A x) = 1 / budgetWinv A x := by
    refine min_eq_right ?_
    rw [div_le_iff₀ hW0]
    rw [div_le_iff₀ hdelta] at hWbig
    linarith
  have hq : (Real.log x) ^ (γ * β) ≤ Real.log ((siftStart (γ * β) x : ℕ) : ℝ) :=
    log_siftStart_ge (γ * β) x
  have hq0 : (0 : ℝ) ≤ Real.log ((siftStart (γ * β) x : ℕ) : ℝ) :=
    le_trans (Real.rpow_nonneg hlogx.le _) hq
  -- the product is at least a power of the logarithm
  have hkey : (Real.log x) ^ ((γ * β - 9 / 10) / 4)
      ≤ min delta (1 / budgetWinv A x) / 2 * Real.log ((siftStart (γ * β) x : ℕ) : ℝ) := by
    rw [hmin]
    have hstep : (1 / budgetWinv A x) / 2 * (Real.log x) ^ (γ * β)
        ≤ (1 / budgetWinv A x) / 2 * Real.log ((siftStart (γ * β) x : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    refine le_trans ?_ hstep
    have hWle : budgetWinv A x
        ≤ 20 * routeTZeroFreeDeltaEnvelopeConstant A
          * (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2) := hW
    have hden0 : (0 : ℝ) < 20 * routeTZeroFreeDeltaEnvelopeConstant A
        * (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2) := by
      have : (0 : ℝ) < (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2) :=
        Real.rpow_pos_of_pos hlogx _
      positivity
    have hlow : 1 / (20 * routeTZeroFreeDeltaEnvelopeConstant A
        * (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2)) ≤ 1 / budgetWinv A x :=
      one_div_le_one_div_of_le hW0 hWle
    have hsplit : (Real.log x) ^ (γ * β)
        / (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2)
        = (Real.log x) ^ ((γ * β - 9 / 10) / 2) := by
      rw [← Real.rpow_sub hlogx]
      congr 1
      ring
    have hstep2 : (Real.log x) ^ ((γ * β - 9 / 10) / 4)
        ≤ 1 / (20 * routeTZeroFreeDeltaEnvelopeConstant A
          * (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2)) / 2
          * (Real.log x) ^ (γ * β) := by
      have hid : 1 / (20 * routeTZeroFreeDeltaEnvelopeConstant A
            * (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2)) / 2
            * (Real.log x) ^ (γ * β)
          = (Real.log x) ^ ((γ * β - 9 / 10) / 2)
            / (40 * routeTZeroFreeDeltaEnvelopeConstant A) := by
        rw [← hsplit]
        field_simp
        ring
      rw [hid]
      rw [le_div_iff₀ (by positivity)]
      have hhalf : (Real.log x) ^ ((γ * β - 9 / 10) / 4)
          * (Real.log x) ^ ((γ * β - 9 / 10) / 4)
          = (Real.log x) ^ ((γ * β - 9 / 10) / 2) := by
        rw [← Real.rpow_add hlogx]
        congr 1
        ring
      nlinarith [hbg, hhalf, Real.rpow_nonneg hlogx.le ((γ * β - 9 / 10) / 4)]
    have hmono : 1 / (20 * routeTZeroFreeDeltaEnvelopeConstant A
          * (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2)) / 2
          * (Real.log x) ^ (γ * β)
        ≤ 1 / budgetWinv A x / 2 * (Real.log x) ^ (γ * β) := by
      have hp0 : (0 : ℝ) ≤ (Real.log x) ^ (γ * β) := Real.rpow_nonneg hlogx.le _
      have hd : 1 / (20 * routeTZeroFreeDeltaEnvelopeConstant A
            * (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2)) / 2
          ≤ 1 / budgetWinv A x / 2 :=
        (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)).mpr hlow
      have := mul_le_mul_of_nonneg_right hd hp0
      linarith [this]
    linarith [hstep2, hmono]
  exact Real.exp_le_exp.2 (by linarith)

/-- The smoothing width, bounded below. -/
theorem eventually_ladderWidth_ge {β : ℝ} (hβ0 : 0 < β) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (4 * β) ≤ ladderWidth β x := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hval : Real.log (2 * cardLength β x) = Real.log 2 + (Real.log x) ^ β := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos β x)), log_cardLength]
  have hge : (Real.log x) ^ β ≤ Real.log (2 * cardLength β x) := by
    rw [hval]
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have h0 : (0 : ℝ) ≤ (Real.log x) ^ β := Real.rpow_nonneg hlogx.le _
  have hpow4 : ((Real.log x) ^ β) ^ 4 ≤ (Real.log (2 * cardLength β x)) ^ 4 :=
    pow_le_pow_left₀ h0 hge 4
  have hrpow : ((Real.log x) ^ β) ^ 4 = (Real.log x) ^ (4 * β) := by
    rw [← Real.rpow_natCast ((Real.log x) ^ β) 4, ← Real.rpow_mul hlogx.le]
    congr 1
    push_cast
    ring
  rw [ladderWidth, ← hrpow]
  exact hpow4

/-- The height cost, bounded by a square of the logarithm. -/
theorem eventually_budgetHmaj_poly {A β γ : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hγβ0 : 9 / 10 < γ * β) (hγβ1 : γ * β < 1) :
    ∀ᶠ x : ℝ in atTop,
      1 + (1 + Real.log x) * budgetWinv A x
        ≤ (1 + 40 * routeTZeroFreeDeltaEnvelopeConstant A) * (Real.log x) ^ (2 : ℝ) := by
  have hε : (0 : ℝ) < (γ * β - 9 / 10) / 2 := by linarith
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  filter_upwards [eventually_budgetWinv_le (A := A) hε, Filter.eventually_ge_atTop (Real.exp 1)]
    with x hW hxe
  have hx1 : (1 : ℝ) < x := by
    have h1 : (1 : ℝ) < Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hexpo : (9 : ℝ) / 10 + (γ * β - 9 / 10) / 2 ≤ 1 := by linarith
  have hstep : (Real.log x) ^ ((9 : ℝ) / 10 + (γ * β - 9 / 10) / 2) ≤ (Real.log x) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog1 hexpo
  rw [Real.rpow_one] at hstep
  have hW' : budgetWinv A x ≤ 20 * routeTZeroFreeDeltaEnvelopeConstant A * Real.log x := by
    have h20 : (0 : ℝ) ≤ 20 * routeTZeroFreeDeltaEnvelopeConstant A := by positivity
    nlinarith [hW, hstep, h20]
  have hsq : (Real.log x) ^ (2 : ℝ) = Real.log x * Real.log x := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hone : (1 : ℝ) ≤ Real.log x * Real.log x := by nlinarith [hlog1]
  have hW0 : (0 : ℝ) ≤ budgetWinv A x := (budgetWinv_pos hx1.le).le
  rw [hsq]
  nlinarith [hW', hlog1, hone, hD]

/-- The designated bottom, bounded below. -/
theorem eventually_siftStart_ge {c : ℝ} :
    ∀ x : ℝ, Real.exp ((Real.log x) ^ c) ≤ ((siftStart c x : ℕ) : ℝ) := by
  intro x
  rw [siftStart]
  exact Nat.le_ceil _

/-- The number of ladder steps, in powers of the logarithm. -/
theorem eventually_ladderSteps_poly {β γ : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ * β < 1) :
    ∀ᶠ x : ℝ in atTop,
      ((ladderSteps β γ x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ (2 * β + 5 / 4 - γ * β) := by
  filter_upwards [ladderSteps_le hβ0 hγ0 hγ1 hγβ, Filter.eventually_gt_atTop (1 : ℝ)]
    with x hL hx1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hid : 2 * (Real.log x) ^ β / ladderEta β γ x
      = 2 * (Real.log x) ^ (2 * β + 5 / 4 - γ * β) := by
    rw [ladderEta, div_eq_mul_inv, ← Real.rpow_neg hlogx.le, mul_assoc,
      ← Real.rpow_add hlogx]
    congr 2
    ring
  rw [← hid]
  exact hL

end

end RHTower.Sieve
