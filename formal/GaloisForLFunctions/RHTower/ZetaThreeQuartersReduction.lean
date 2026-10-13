import GaloisForLFunctions.RHTower.ZetaTraceWide
import GaloisForLFunctions.RHTower.ThmEUniformSeam
import GaloisForLFunctions.RHTower.PairCorrelationExchangeRate
import Zeta23.Final
import Zeta23.Assembly.SeamMult
import GaloisForLFunctions.RHTower.ThmEUniformRates

/-!
# Three quarters of the zeros of ζ on the critical line, from one mean-value inequality

Run the rank–trace certificate for `ζ` at bandwidth `λ = 4/3`, i.e. with prime polynomials of length
`X = (T/2π)^{4/3}`.  Every input of the certificate is unconditional at this bandwidth except the Frobenius
norm of the prime-side Gram matrix:

* the explicit-formula bridge, the block structure and the tail hold at every bandwidth (`ParamsValidFam`);
* the trace is `aLN + O(L(log T + √X))` at every bandwidth (`prop_trace_zeta_wide`), and
  `√X = T^{2/3}` is negligible against `N ≍ T log T`.

So everything reduces to the single prime-side inequality (`FrobeniusFourThirds`)

`tr G̃²(T) ≤ (5/4 + ε) (aL)² · Tℓ₁(T)/2π`   for all large `T`,

a mean-value statement about the density `ν_X = μ + Π_X + P_X` with `X = (T/2π)^{4/3}`.  It gives
(`zeta_three_quarters_of_frobenius`, `zeta_three_quarters_cumulative_of_frobenius`)

`(3/4 − ε) N(T) ≤ N₀*(T)`,

with no hypothesis on the location of the zeros.  The zero-side form (`PairCorrelationFourThirds`: the
normalised pair-correlation sum `‖Ĝ‖_F²` of the zeros at bandwidth `4/3` is at most `(5/4 + ε) N(T,2T)`)
implies the prime-side one (`frobeniusFourThirds_of_pairCorrelation`), hence the same conclusion
(`zeta_three_quarters_of_pair_correlation`).  The certificate runs equally on the multiplicity-aware zero
side, so the same hypothesis gives three quarters of the zeros simple and on the line
(`zeta_three_quarters_simple_of_frobenius`, `zeta_three_quarters_simple_of_pair_correlation`): the
certificate cannot distinguish a double zero on the line from a reflected pair coalescing on it, so the
hypothesis is at least as strong as a three-quarters proportion of simple zeros.  The constant `5/4` is
the exchange rate `c(4/3, 2)`
(`PairCorrelationExchangeRate`); the random-matrix prediction for the left side is `c(4/3, 1) = 19/16`
(`frobenius_target_gue`), so the inequality is a weak form of the pair-correlation conjecture on
`(1, 4/3)` with room to spare.
-/

open MeasureTheory Real Set Filter Topology Zeta23 Zeta23.ThmE Zeta23.PrimeSide Zeta23.Assembly
  RHLinalg

noncomputable section

namespace RHTower

/-- The parameters at bandwidth `4/3`. -/
abbrev params43 : Params := stdParams (4 / 3)

/-- **The bandwidth-`4/3` Frobenius inequality** (prime side). -/
def FrobeniusFourThirds : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    params43.trGtildeSq T ≤ (5 / 4 + ε) * (params43.a T * params43.L T) ^ 2 * (T * ell1 T / (2 * π))

/-- The target constant is the exchange rate at `B = 2`, and the random-matrix value is `19/16`. -/
theorem frobenius_target_gue :
    2 - certValue (4 / 3) 2 = 5 / 4 ∧ 2 - certValue (4 / 3) 1 = 19 / 16 := by
  unfold certValue; constructor <;> norm_num

theorem paramsValidFam_params43 : ParamsValidFam params43 :=
  ⟨taperProfile_stdProfile, show (0:ℝ) < 4 / 3 by norm_num, le_refl (1:ℝ)⟩

theorem ell1_eq_ell1q (T : ℝ) : ell1 T = ell1q 1 T := by
  unfold ell1 ell1q Zeta23.l
  rw [Nat.cast_one, one_mul]

/-- The seam inequality of the rank–trace certificate at bandwidth `4/3`, with a count `Y` on the right:
`Y = N₀*` by the block structure of the zero side, `Y = N₀ˢ` by its multiplicity-aware form. -/
def Seam43 (Y : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∀ θ₀ : ℝ, TailInputs zetaZeroConfig params43 T θ₀ → 0 < params43.a T →
    0 < params43.L T → ZeroSide.PhiHatConj T params43 → ZeroSide.PhiHatReal T params43 →
    ZeroSide.PoissonSq T params43 →
    4 * rtrace (params43.hat T (zetaZeroConfig.Gz params43 T))
      - frobSq (params43.hat T (zetaZeroConfig.Gz params43 T)) - 2 * (zetaZeroConfig.N T (2 * T) : ℝ)
      - 3 * (NII zetaZeroConfig T : ℝ)
      - θ₀ / (params43.a T * params43.L T)
        * (4 + 2 * Real.sqrt (frobSq (params43.hat T (zetaZeroConfig.Gz params43 T)))
          + θ₀ / (params43.a T * params43.L T))
      ≤ Y T

/-- **Three quarters of every count obeying the seam inequality, from the bandwidth-`4/3` Frobenius
inequality.** -/
theorem three_quarters_of_frobenius_seam (hFr : FrobeniusFourThirds) {Y : ℝ → ℝ} (hY : Seam43 Y) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Y T := by
  intro ε hε
  obtain ⟨ε', hε'def⟩ : ∃ x : ℝ, x = min ε 1 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε'def]; exact lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := by rw [hε'def]; exact min_le_right _ _
  have hε'ε : ε' ≤ ε := by rw [hε'def]; exact min_le_left _ _
  have hP := paramsValidFam_params43
  have H := paperInputs_zeta
  obtain ⟨CR, TR, hRvM⟩ := H.RvM.main
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨CN, hNII⟩ := Tail.eventually_NII_le zetaZeroConfig hA₀ hloc
  obtain ⟨Ct, Tt, hCt, htrW⟩ := prop_trace_zeta_wide (cϱ := params43.crho)
    (by norm_num : (0:ℝ) < 4 / 3) |CR|
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hP
  obtain ⟨R, hRdef⟩ : ∃ x : ℝ, x = Taper.l1Deriv2 stdProfile := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; exact MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have hπ := Real.pi_gt_three
  -- the rates
  have e1 := eventually_l_bounds.and (eventually_ge_atTop (max (max TR Tt) (max TL 300)))
  have e2 := Real.tendsto_log_atTop.eventually_ge_atTop (12 : ℝ)
  have e3 := hFr (ε' / 4) (by positivity)
  have e4 := eventually_log_pow_rpow_le 0 (by norm_num : (2:ℝ) / 3 < 1)
    (by positivity : (0:ℝ) ≤ 8 * Ct) (by positivity : (0:ℝ) < ε' / (256 * π))
  have e5 := eventually_ge_atTop (256 * π * (16 * Ct + 4 * |CR|) / ε')
  have e6 := eventually_log_pow_rpow_le 0 (by norm_num : (1:ℝ) / 2 < 1)
    (by positivity : (0:ℝ) ≤ 3 * |CN|) (by positivity : (0:ℝ) < ε' / (256 * π))
  have e7 := eventually_log_pow_rpow_le_const 1 (by norm_num : (4:ℝ) / 3 / 2 - 1 < 0)
    (by positivity : (0:ℝ) ≤ 32 * A₀ * R ^ 2) (by norm_num : (0:ℝ) < 1)
  have e8 := Real.tendsto_log_atTop.eventually_ge_atTop (2048 * 32 * π / ε' ^ 2 + 80 * 32 * π / ε')
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    (((((((e1.and e2).and e3).and e4).and e5).and e6).and e7).and (e8.and hNII))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlog1, hl1, hlo, hhi⟩, hTge⟩, hlogL⟩, hfr⟩, r4⟩, r5⟩, r6⟩, r7⟩, r8, hNIIT⟩ :=
    hT₀ T hT
  have hTR : TR ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hTge)
  have hTt : Tt ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hTge)
  have hTLT : TL ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hTge)
  have hT300 : Tail.T₀ ≤ T := by
    show (300:ℝ) ≤ T; exact (le_max_right _ _).trans ((le_max_right _ _).trans hTge)
  have hT3 : (300:ℝ) ≤ T := hT300
  have hT0 : 0 < T := by linarith only [hT3]
  -- parameters at T
  have hLdef : params43.L T = 4 / 3 * Zeta23.l T := rfl
  have hw : params43.w = 1 := rfl
  have hL8 : 8 ≤ params43.L T := by
    rw [hLdef]; linarith only [hlogL, hlo]
  have hL0 : 0 < params43.L T := by linarith only [hL8]
  have hwL : 8 * params43.w ≤ params43.L T := by rw [hw]; linarith only [hL8]
  have ha2 : 1 / 2 ≤ params43.a T := half_le_a_fam hP hwL
  have ha0 : 0 < params43.a T := by linarith only [ha2]
  have hF := hTL T hTLT
  -- the seam
  set Z := zetaZeroConfig with hZ
  have hTail := tailInputs_fam Z hP hA₀ hloc hT300 (by linarith only [hL8]) hwL
  have hseam := hY T hT0.le _ hTail ha0 hL0 (fun z => GzGp.phiHat_conj params43 T z)
    (fun r => GzGp.phiHat_ofReal params43 T r) (poissonSq_fam hP hwL)
  have hGzGp : Z.Gz params43 T = params43.Gp T := by
    refine Z.Gz_eq_Gp params43 T H.EF hL0 ?_ ?_
    · exact (Complex.ofRealCLM.contDiff.comp
        (Taper.phi_contDiff hP.taper hP.w_pos (hP.two_w_le hwL))).of_le (by norm_num)
    · exact closure_minimal (Taper.phi_support_subset hP.taper hP.w_pos) isClosed_Icc
  rw [hGzGp] at hseam
  rw [rtrace_hat, rtrace_tilde_Gp, frobSq_hat, frobSq_tilde_Gp] at hseam
  -- counts
  obtain ⟨N, hNdef⟩ : ∃ x : ℝ, x = (Ncount T (2 * T) : ℝ) := ⟨_, rfl⟩
  have hZN : (Z.N T (2 * T) : ℝ) = N := by rw [hNdef, hZ, zetaZeroConfig_N]
  rw [hZN] at hseam
  have hRv := hRvM T hTR
  rw [hZN] at hRv
  -- the trace
  have htr := htrW (params43.toSetting T) (params43.localFun T) rfl hTt hF N (by
    have e : (params43.toSetting T).T = T := rfl
    rw [e, ← ell1_eq_ell1q T]
    refine hRv.trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by linarith only [hT3])))
  have htr' : |params43.trGtilde T - params43.a T * params43.L T * N|
      ≤ Ct * (params43.L T * (1 + Real.log T + Real.sqrt (params43.X T))) := htr
  -- normalised quantities
  obtain ⟨aL, haLdef⟩ : ∃ x : ℝ, x = params43.a T * params43.L T := ⟨_, rfl⟩
  have haL0 : 0 < aL := by rw [haLdef]; positivity
  have haL4 : 4 ≤ aL := by rw [haLdef]; nlinarith only [ha2, hL8]
  rw [← haLdef] at hseam htr' hfr
  obtain ⟨tr, htrdef⟩ : ∃ x : ℝ, x = aL⁻¹ * params43.trGtilde T := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ x : ℝ, x = (aL⁻¹) ^ 2 * params43.trGtildeSq T := ⟨_, rfl⟩
  rw [← htrdef, ← hfdef] at hseam
  obtain ⟨M, hMdef⟩ : ∃ x : ℝ, x = T * ell1 T / (2 * π) := ⟨_, rfl⟩
  rw [← hMdef] at hfr
  have hRv' : |N - M| ≤ |CR| * Real.log T := by
    rw [hMdef, show T * ell1 T / (2 * π) = T / (2 * π) * ell1 T by ring]
    exact hRv.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (Real.log_nonneg (by linarith only [hT3])))
  obtain ⟨lT, hlTdef⟩ : ∃ x : ℝ, x = Real.log T := ⟨_, rfl⟩
  rw [← hlTdef] at hlog1 hlo hhi hlogL r4 r6 r7 r8 hRv'
  simp only [pow_zero, mul_one] at r4 r6
  rw [pow_one] at r7
  -- the trace error
  have hsX : Real.sqrt (params43.X T) ≤ T ^ (2 / 3 : ℝ) := by
    have h := sqrt_exp_lam_l_le (lam := 4 / 3) (by norm_num) hT0 (by rw [← hlTdef]; exact hhi)
    have e : (4 / 3 : ℝ) / 2 = 2 / 3 := by norm_num
    rw [e] at h; exact h
  have htrN : N - 2 * Ct * (1 + lT + T ^ (2 / 3 : ℝ)) ≤ tr := by
    have h1 := (abs_le.mp htr').1
    have hW : params43.L T * (1 + Real.log T + Real.sqrt (params43.X T))
        ≤ params43.L T * (1 + lT + T ^ (2 / 3 : ℝ)) := by
      rw [← hlTdef]; exact mul_le_mul_of_nonneg_left (by linarith only [hsX]) hL0.le
    have h2 : aL * N - Ct * (params43.L T * (1 + lT + T ^ (2 / 3 : ℝ))) ≤ params43.trGtilde T := by
      have := mul_le_mul_of_nonneg_left hW hCt
      linarith only [h1, this]
    have hLa : params43.L T ≤ 2 * aL := by rw [haLdef]; nlinarith only [ha2, hL0]
    have hW0 : 0 ≤ 1 + lT + T ^ (2 / 3 : ℝ) := by positivity
    have h3 : Ct * (params43.L T * (1 + lT + T ^ (2 / 3 : ℝ)))
        ≤ aL * (2 * Ct * (1 + lT + T ^ (2 / 3 : ℝ))) := by
      have := mul_le_mul_of_nonneg_right hLa (mul_nonneg hCt hW0)
      linarith only [this]
    rw [htrdef, le_inv_mul_iff₀ haL0]
    have e : aL * (N - 2 * Ct * (1 + lT + T ^ (2 / 3 : ℝ)))
        = aL * N - aL * (2 * Ct * (1 + lT + T ^ (2 / 3 : ℝ))) := by ring
    linarith only [h2, h3, e]
  -- the Frobenius bound
  have hfM : f ≤ (5 / 4 + ε' / 4) * M := by
    rw [hfdef]
    have h := mul_le_mul_of_nonneg_left hfr (sq_nonneg aL⁻¹)
    have e : aL⁻¹ ^ 2 * ((5 / 4 + ε' / 4) * aL ^ 2 * M) = (5 / 4 + ε' / 4) * M := by
      field_simp
    linarith only [h, e]
  -- the size of N
  have hc0 : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
  have hMlow : T * lT / (4 * π) ≤ M := by
    rw [hMdef]
    unfold ell1
    have h1 : T * lT / (4 * π) ≤ T * Zeta23.l T / (2 * π) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left (by linarith only [hlo] : lT ≤ 2 * Zeta23.l T)
        (by positivity : (0:ℝ) ≤ T * (2 * π))
      nlinarith only [this]
    have h2 : T * Zeta23.l T / (2 * π) ≤ T * (Zeta23.l T + 2 * Real.log 2 - 1) / (2 * π) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith only [hc0]) hT0.le
    linarith only [h1, h2]
  have hCRT : |CR| ≤ T / (8 * π) := by
    rw [div_le_iff₀ hε'0] at r5
    have : 256 * π * (4 * |CR|) ≤ T * ε' := by nlinarith only [r5, hCt, abs_nonneg CR, Real.pi_pos]
    have h1 : T * ε' ≤ T := by nlinarith only [hε'1, hT0]
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [this, h1, Real.pi_pos, abs_nonneg CR]
  have hCRlog : |CR| * lT ≤ T * lT / (8 * π) := by
    have := mul_le_mul_of_nonneg_right hCRT (by linarith only [hlog1] : (0:ℝ) ≤ lT)
    have e : T / (8 * π) * lT = T * lT / (8 * π) := by ring
    linarith only [this, e]
  have hNlow : T * lT / (8 * π) ≤ N := by
    have h1 := (abs_le.mp hRv').1
    have e : T * lT / (4 * π) = 2 * (T * lT / (8 * π)) := by ring
    linarith only [h1, hMlow, hCRlog, e]
  have hNlog : lT ≤ N := by
    have : lT ≤ T * lT / (8 * π) := by
      rw [le_div_iff₀ (by positivity)]
      have : 8 * π ≤ T := by nlinarith only [hT3, Real.pi_lt_four]
      nlinarith only [this, hlog1]
    linarith only [this, hNlow]
  -- the error terms
  have hlT0 : 0 < lT := by linarith only [hlog1]
  have hTlT : 0 ≤ T * lT := by positivity
  have hE1 : 4 * (2 * Ct * (1 + lT + T ^ (2 / 3 : ℝ))) ≤ ε' / 16 * N := by
    rw [div_le_iff₀ hε'0] at r5
    have h16 : 16 * Ct ≤ ε' * T / (256 * π) := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [r5, mul_nonneg Real.pi_pos.le (abs_nonneg CR)]
    have ha : 8 * Ct * (1 + lT) ≤ 16 * Ct * lT := by nlinarith only [hCt, hlog1]
    have hb : 16 * Ct * lT ≤ ε' * T / (256 * π) * lT := mul_le_mul_of_nonneg_right h16 hlT0.le
    have hc : ε' / (256 * π) * T ≤ ε' / (256 * π) * T * lT := le_mul_of_one_le_right (by positivity) hlog1
    have e1 : ε' * T / (256 * π) * lT + ε' / (256 * π) * T * lT = ε' / 16 * (T * lT / (8 * π)) := by
      field_simp; ring
    have hN := mul_le_mul_of_nonneg_left hNlow (by positivity : (0:ℝ) ≤ ε' / 16)
    have e2 : 4 * (2 * Ct * (1 + lT + T ^ (2 / 3 : ℝ))) = 8 * Ct * (1 + lT) + 8 * Ct * T ^ (2 / 3 : ℝ) := by
      ring
    linarith only [ha, hb, hc, e1, hN, e2, r4]
  have hE2 : (5 / 4 + ε' / 4) * (|CR| * lT) ≤ ε' / 16 * N := by
    rw [div_le_iff₀ hε'0] at r5
    have h4 : 4 * |CR| ≤ ε' * T / (256 * π) := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [r5, mul_nonneg Real.pi_pos.le hCt]
    have h1 : (5 / 4 + ε' / 4) * (|CR| * lT) ≤ 2 * (|CR| * lT) :=
      mul_le_mul_of_nonneg_right (by linarith only [hε'1]) (by positivity)
    have h2 : 4 * |CR| * lT ≤ ε' * T / (256 * π) * lT := mul_le_mul_of_nonneg_right h4 hlT0.le
    have e1 : ε' * T / (256 * π) * lT = ε' / 32 * (T * lT / (8 * π)) := by field_simp; ring
    have hN := mul_le_mul_of_nonneg_left hNlow (by positivity : (0:ℝ) ≤ ε' / 32)
    have hN0 : 0 ≤ N := le_trans (by positivity) hNlow
    nlinarith only [h1, h2, e1, hN, hN0, hε'0]
  have hE3 : 3 * (NII Z T : ℝ) ≤ ε' / 16 * N := by
    have h1 : (NII Z T : ℝ) ≤ |CN| * T ^ (1 / 2 : ℝ) * lT := by
      refine hNIIT.trans ?_
      rw [← Real.sqrt_eq_rpow]
      have hsT : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
      have hl0 : 0 ≤ Zeta23.l T := by linarith only [hl1]
      calc CN * Real.sqrt T * Zeta23.l T ≤ |CN| * Real.sqrt T * Zeta23.l T :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hsT) hl0
        _ ≤ |CN| * Real.sqrt T * lT :=
            mul_le_mul_of_nonneg_left hhi (mul_nonneg (abs_nonneg _) hsT)
    have h2 := mul_le_mul_of_nonneg_right r6 hlT0.le
    have e1 : ε' / (256 * π) * T * lT = ε' / 32 * (T * lT / (8 * π)) := by field_simp; ring
    have hN := mul_le_mul_of_nonneg_left hNlow (by positivity : (0:ℝ) ≤ ε' / 32)
    have hN0 : 0 ≤ N := le_trans (by positivity) hNlow
    nlinarith only [h1, h2, e1, hN, hN0, hε'0]
  -- the tail
  obtain ⟨B, hBdef⟩ : ∃ x : ℝ, x = Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T / aL :=
    ⟨_, rfl⟩
  rw [← hBdef] at hseam
  have hθ0 := hTail.theta_nonneg
  have hB0 : 0 ≤ B := by rw [hBdef]; exact div_nonneg hθ0 haL0.le
  have hB1 : B ≤ 1 := by
    have hC1 : params43.C1 T ≤ 2 * R := by rw [hRdef]; exact C1_le_fam hP hwL
    have hth := theta0_le_fam hP hT300 (by linarith only [hA₀]) (Tail.C1_nonneg _ T) hC1
    have hl' : Zeta23.l T ≤ lT := hhi
    have hlam : params43.lam / 2 - 1 = (4 / 3 : ℝ) / 2 - 1 := rfl
    rw [hlam] at hth
    have hT13 : 0 ≤ T ^ ((4 / 3 : ℝ) / 2 - 1) := by positivity
    have h2 : 32 * A₀ * R ^ 2 * Zeta23.l T * T ^ ((4 / 3 : ℝ) / 2 - 1)
        ≤ 32 * A₀ * R ^ 2 * lT * T ^ ((4 / 3 : ℝ) / 2 - 1) := by
      apply mul_le_mul_of_nonneg_right _ hT13
      exact mul_le_mul_of_nonneg_left hl' (by have := zero_le_one.trans hA₀; positivity)
    have hθ1 : Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T ≤ 1 := by
      linarith only [hth, h2, r7]
    rw [hBdef, div_le_one haL0]
    linarith only [hθ1, haL4]
  have hf0 : 0 ≤ f := by
    rw [hfdef, ← frobSq_tilde_Gp]; exact mul_nonneg (sq_nonneg _) (frobSq_nonneg _)
  have hN0 : 0 ≤ N := le_trans (by positivity) hNlow
  have hMN : M ≤ N + |CR| * lT := by have := (abs_le.mp hRv').1; linarith only [this]
  have hf3 : f ≤ 3 * N := by
    have h1 : f ≤ (5 / 4 + ε' / 4) * (N + |CR| * lT) :=
      hfM.trans (mul_le_mul_of_nonneg_left hMN (by positivity))
    have h2 : |CR| * lT ≤ N := by
      have : 0 ≤ T * lT / (8 * π) := by positivity
      linarith only [hCRlog, hNlow, this]
    have h3 : (5 / 4 + ε' / 4) * (N + |CR| * lT) ≤ 3 / 2 * (N + |CR| * lT) :=
      mul_le_mul_of_nonneg_right (by linarith only [hε'1]) (by positivity)
    linarith only [h1, h2, h3]
  have hE4 : B * (4 + 2 * Real.sqrt f + B) ≤ ε' / 8 * N := by
    have hsf : Real.sqrt f ≤ 2 * Real.sqrt N := by
      have : Real.sqrt f ≤ Real.sqrt (3 * N) := Real.sqrt_le_sqrt hf3
      rw [Real.sqrt_mul (by norm_num)] at this
      have h3 : Real.sqrt 3 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      nlinarith only [this, h3, Real.sqrt_nonneg N]
    have h1 : B * (4 + 2 * Real.sqrt f + B) ≤ 1 * (4 + 2 * (2 * Real.sqrt N) + 1) :=
      mul_le_mul hB1 (by linarith only [hsf, hB1]) (by positivity) zero_le_one
    have hNbig : 4096 / ε' ^ 2 + 80 / ε' ≤ N := by
      have : 4096 / ε' ^ 2 + 80 / ε' ≤ 2048 * 32 * π / ε' ^ 2 + 80 * 32 * π / ε' := by
        have h1' : 4096 / ε' ^ 2 ≤ 2048 * 32 * π / ε' ^ 2 :=
          div_le_div_of_nonneg_right (by nlinarith only [Real.pi_gt_three]) (by positivity)
        have h2' : 80 / ε' ≤ 80 * 32 * π / ε' :=
          div_le_div_of_nonneg_right (by nlinarith only [Real.pi_gt_three]) hε'0.le
        linarith only [h1', h2']
      linarith only [this, r8, hNlog]
    have hN1 : 80 / ε' ≤ N := by
      have : 0 ≤ 4096 / ε' ^ 2 := by positivity
      linarith only [hNbig, this]
    have hN2 : 4096 / ε' ^ 2 ≤ N := by
      have : 0 ≤ 80 / ε' := by positivity
      linarith only [hNbig, this]
    have h5 : 5 ≤ ε' / 16 * N := by
      rw [div_le_iff₀ hε'0] at hN1
      nlinarith only [hN1]
    have h6 : 4 * Real.sqrt N ≤ ε' / 16 * N := by
      have hsN : 64 / ε' ≤ Real.sqrt N := by
        rw [Real.le_sqrt (by positivity) hN0]
        have e : (64 / ε') ^ 2 = 4096 / ε' ^ 2 := by field_simp; norm_num
        rw [e]; exact hN2
      have hsN0 := Real.sqrt_nonneg N
      have hNsq : N = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0).symm
      rw [div_le_iff₀ hε'0] at hsN
      nlinarith only [hsN, hNsq, hsN0, hε'0]
    linarith only [h1, h5, h6]
  -- conclusion
  have hfin : (3 / 4 - ε') * N ≤ Y T := by
    have hfN : f ≤ (5 / 4 + ε' / 4) * N + (5 / 4 + ε' / 4) * (|CR| * lT) := by
      have := hfM.trans (mul_le_mul_of_nonneg_left hMN (by positivity : (0:ℝ) ≤ 5 / 4 + ε' / 4))
      linarith only [this]
    have hεN : 0 ≤ ε' * N := mul_nonneg hε'0.le hN0
    linarith only [hseam, htrN, hfN, hE1, hE2, hE3, hE4, hεN]
  have hmono : (3 / 4 - ε) * N ≤ (3 / 4 - ε') * N :=
    mul_le_mul_of_nonneg_right (by linarith only [hε'ε]) hN0
  rw [← hNdef]
  exact hmono.trans hfin

/-- The block structure gives the seam inequality for `N₀*`. -/
theorem seam43_N0star : Seam43 (fun T => (N0star T (2 * T) : ℝ)) := by
  intro T hT θ₀ hTl ha hL hconj hreal hPois
  have h := seamA hT (ZeroSide.blockInputsAt zetaZeroConfig params43 T hconj hreal hPois hL
    (mul_pos ha (pow_pos hL 2))) hTl ha hL
  rwa [zetaZeroConfig_N0star] at h

/-- The multiplicity-aware block structure gives it for `N₀ˢ` (simple zeros on the line). -/
theorem seam43_N0simple : Seam43 (fun T => (N0simple T (2 * T) : ℝ)) := by
  intro T hT θ₀ hTl ha hL hconj hreal hPois
  have h := seamA_mult2 hT hconj hreal hPois hTl ha hL
  rwa [zetaZeroConfig_N0s] at h

/-- **Three quarters on the line from the bandwidth-`4/3` Frobenius inequality.** -/
theorem zeta_three_quarters_of_frobenius (hFr : FrobeniusFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) :=
  three_quarters_of_frobenius_seam hFr seam43_N0star

/-- **…and three quarters simple and on the line.** -/
theorem zeta_three_quarters_simple_of_frobenius (hFr : FrobeniusFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  three_quarters_of_frobenius_seam hFr seam43_N0simple

/-- **…and its cumulative form**: `(3/4 − ε) N(T) ≤ N₀*(T)` for all large `T`. -/
theorem zeta_three_quarters_cumulative_of_frobenius (hFr : FrobeniusFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => N0star_add' zetaSeam)
    (zeta_three_quarters_of_frobenius hFr)

/-- **The bandwidth-`4/3` pair-correlation inequality** (zero side): the normalised Gram matrix of the zeros
satisfies `‖Ĝ‖_F² ≤ (5/4 + ε) N(T, 2T)`; for zeros on the line `‖Ĝ‖_F² = Σ_{ρ,ρ'} K(γ − γ')²` with the
bandwidth-`4/3` kernel `K`. -/
def PairCorrelationFourThirds : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    frobSq (params43.hat T (zetaZeroConfig.Gz params43 T)) ≤ (5 / 4 + ε) * (Ncount T (2 * T) : ℝ)

/-- The zero-side inequality implies the prime-side one (explicit-formula bridge and
Riemann–von Mangoldt). -/
theorem frobeniusFourThirds_of_pairCorrelation (h : PairCorrelationFourThirds) :
    FrobeniusFourThirds := by
  intro ε hε
  obtain ⟨ε', hε'def⟩ : ∃ x : ℝ, x = min ε 1 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε'def]; exact lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := by rw [hε'def]; exact min_le_right _ _
  have hε'ε : ε' ≤ ε := by rw [hε'def]; exact min_le_left _ _
  have hP := paramsValidFam_params43
  have H := paperInputs_zeta
  obtain ⟨CR, TR, hRvM⟩ := H.RvM.main
  filter_upwards [h (ε' / 2) (by positivity), eventually_l_bounds,
    eventually_ge_atTop (max TR (max 300 (24 * π * |CR| / ε'))),
    Real.tendsto_log_atTop.eventually_ge_atTop (12 : ℝ)] with T hT ⟨hlog1, hl1, hlo, hhi⟩ hTge hlog12
  have hTR : TR ≤ T := (le_max_left _ _).trans hTge
  have hT3 : (300:ℝ) ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hTge)
  have hTC : 24 * π * |CR| / ε' ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hTge)
  have hT0 : 0 < T := by linarith only [hT3]
  have hLdef : params43.L T = 4 / 3 * Zeta23.l T := rfl
  have hw : params43.w = 1 := rfl
  have hL8 : 8 ≤ params43.L T := by rw [hLdef]; linarith only [hlog12, hlo]
  have hL0 : 0 < params43.L T := by linarith only [hL8]
  have hwL : 8 * params43.w ≤ params43.L T := by rw [hw]; linarith only [hL8]
  have ha0 : 0 < params43.a T := lt_of_lt_of_le (by norm_num) (half_le_a_fam hP hwL)
  have hGzGp : zetaZeroConfig.Gz params43 T = params43.Gp T := by
    refine zetaZeroConfig.Gz_eq_Gp params43 T H.EF hL0 ?_ ?_
    · exact (Complex.ofRealCLM.contDiff.comp
        (Taper.phi_contDiff hP.taper hP.w_pos (hP.two_w_le hwL))).of_le (by norm_num)
    · exact closure_minimal (Taper.phi_support_subset hP.taper hP.w_pos) isClosed_Icc
  rw [hGzGp, frobSq_hat, frobSq_tilde_Gp] at hT
  obtain ⟨aL, haLdef⟩ : ∃ x : ℝ, x = params43.a T * params43.L T := ⟨_, rfl⟩
  have haL0 : 0 < aL := by rw [haLdef]; positivity
  rw [← haLdef] at hT ⊢
  -- the count against Tℓ₁/2π
  obtain ⟨N, hNdef⟩ : ∃ x : ℝ, x = (Ncount T (2 * T) : ℝ) := ⟨_, rfl⟩
  rw [← hNdef] at hT
  have hRv := hRvM T hTR
  rw [zetaZeroConfig_N, ← hNdef] at hRv
  obtain ⟨M, hMdef⟩ : ∃ x : ℝ, x = T * ell1 T / (2 * π) := ⟨_, rfl⟩
  rw [← hMdef]
  have hNM : N ≤ M + |CR| * Real.log T := by
    have h1 := (abs_le.mp hRv).2
    have e : T / (2 * π) * ell1 T = M := by rw [hMdef]; ring
    rw [e] at h1
    have h2 : CR * Real.log T ≤ |CR| * Real.log T :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.log_nonneg (by linarith only [hT3]))
    linarith only [h1, h2]
  have hc0 : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
  have hMlow : T * Real.log T / (4 * π) ≤ M := by
    rw [hMdef]; unfold ell1
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Real.log T ≤ 2 * (Zeta23.l T + 2 * Real.log 2 - 1) := by linarith only [hlo, hc0]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ T * (2 * π))
    nlinarith only [this, hT0, Real.pi_pos]
  have hCR : |CR| * Real.log T ≤ ε' / 6 * M := by
    rw [div_le_iff₀ hε'0] at hTC
    have hlogT : 0 ≤ Real.log T := by linarith only [hlog1]
    have h1 : |CR| * Real.log T * (24 * π) ≤ T * ε' * Real.log T := by
      have := mul_le_mul_of_nonneg_right hTC hlogT
      linarith only [this]
    have h2 : ε' / 6 * (T * Real.log T / (4 * π)) ≤ ε' / 6 * M :=
      mul_le_mul_of_nonneg_left hMlow (by positivity)
    have e : ε' / 6 * (T * Real.log T / (4 * π)) = T * ε' * Real.log T / (24 * π) := by
      field_simp; ring
    rw [e] at h2
    have h3 : |CR| * Real.log T ≤ T * ε' * Real.log T / (24 * π) := by
      rw [le_div_iff₀ (by positivity)]; exact h1
    linarith only [h2, h3]
  -- assemble
  have hTs : params43.trGtildeSq T = aL ^ 2 * ((aL⁻¹) ^ 2 * params43.trGtildeSq T) := by
    field_simp
  rw [hTs]
  have hM0 : 0 ≤ M := le_trans (by positivity) hMlow
  have h1 : (aL⁻¹) ^ 2 * params43.trGtildeSq T ≤ (5 / 4 + ε' / 2) * (M + ε' / 6 * M) :=
    hT.trans (mul_le_mul_of_nonneg_left (hNM.trans (by linarith only [hCR])) (by positivity))
  have h2 : (5 / 4 + ε' / 2) * (M + ε' / 6 * M) ≤ (5 / 4 + ε) * M := by
    have e : (5 / 4 + ε' / 2) * (M + ε' / 6 * M) = (5 / 4 + ε' / 2 + 5 / 24 * ε' + ε' ^ 2 / 12) * M := by
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hM0
    nlinarith only [hε'1, hε'0, hε'ε]
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg aL)
  linarith only [h3]

/-- **Three quarters on the line from the bandwidth-`4/3` pair-correlation inequality.** -/
theorem zeta_three_quarters_of_pair_correlation (h : PairCorrelationFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  zeta_three_quarters_cumulative_of_frobenius (frobeniusFourThirds_of_pairCorrelation h)

/-- Cumulative form for simple zeros on the line. -/
theorem zeta_three_quarters_simple_cumulative_of_frobenius (hFr : FrobeniusFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => N0simple_add' zetaSeam)
    (zeta_three_quarters_simple_of_frobenius hFr)

/-- **The pair-correlation inequality gives three quarters simple and on the line.**  So any proof of
`PairCorrelationFourThirds` also proves that three quarters of the zeros are simple; the certificate cannot
tell a double zero on the line from a reflected pair of zeros that coalesce on it. -/
theorem zeta_three_quarters_simple_of_pair_correlation (h : PairCorrelationFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  zeta_three_quarters_simple_cumulative_of_frobenius (frobeniusFourThirds_of_pairCorrelation h)

end RHTower
