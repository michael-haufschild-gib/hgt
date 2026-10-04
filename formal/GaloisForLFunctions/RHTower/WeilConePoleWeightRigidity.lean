import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity

/-!
# The pole weight of the full Weil cone

**Pole weight one** (`eq_one_of_weilPositiveFull`).  Let `lam` be full-cone Weil-positive (pole
weight `1` in the functional) and `lam = βΛ + e` on `n ≥ 2`, where `(σ − 1)·Σ e(n) n^{−σ} → 0` as
`σ → 1⁺` (for instance `e` with a boundary symbol continuous at `s = 1`, or `Σ |e(n)|/n < ∞`).
Then `β = 1`.  On `σ > 1`, `ξ'/ξ − Φ_lam = (β − 1)·L(Λ) + L(e)`; the left side is holomorphic at
`s = 1`, while `(σ − 1)L(Λ)(σ) → 1`.  So a system `βΛ + e` with `β ≠ 1` and such an `e` is never
full-cone Weil-positive: the full cone fixes the pole weight.

**Low-frequency bound** (`one_sub_mul_re_pole_le`).  For the functional with pole weight `β`,
`W^β_lam(k) = W_lam(k) + (β − 1)(k̂(i/2) + k̂(−i/2))`, and a real test `F` supported in `[−R, R]`
with `2R < log 2`, the autocorrelation `k_F` vanishes at every `±log n`, `n ≥ 2`, so the explicit
formula gives `Re W^β_lam(k_F) = Re W_ζ(F, F) − (1 − β) Re(k̂_F(i/2) + k̂_F(−i/2))`.  Hence
positivity at `k_F` forces `(1 − β)·pole(k_F) ≤ Re W_ζ(F, F)`, and under RH
`Re W_ζ(F, F) = Σ_ρ m_ρ |F̂(γ_ρ)|²` (`one_sub_mul_re_pole_le_zeroSum`): `β ≥ 1 − Σ_ρ K(γ_ρ)/pole(K)`
with `K = |F̂|²`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilPoleWeight

open WeilSpectral WeilHerglotz Zeta23 WeilConditional

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## The residue at `s = 1` -/

theorem tendsto_ofReal_nhdsGT_one :
    Tendsto (fun σ : ℝ => ((σ : ℂ))) (𝓝[>] 1) (𝓝 1) := by
  have h : Tendsto (fun σ : ℝ => ((σ : ℂ))) (𝓝 1) (𝓝 ((1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.tendsto 1
  rw [Complex.ofReal_one] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem continuousAt_logDeriv_xi_one : ContinuousAt (logDeriv xi) 1 := by
  have h1 : ContinuousAt (deriv xi) 1 :=
    ((xi_analyticOnNhd Set.univ).deriv 1 (mem_univ _)).continuousAt
  have h2 : ContinuousAt xi 1 := (xi_differentiable 1).continuousAt
  have hne : xi 1 ≠ 0 := by rw [xi_one]; norm_num
  have : logDeriv xi = fun s => deriv xi s / xi s := funext fun s => logDeriv_apply xi s
  rw [this]
  exact h1.div h2 hne

theorem continuousAt_zetaArchimedeanDatum_one : ContinuousAt zetaArchimedeanDatum 1 := by
  unfold zetaArchimedeanDatum
  have hd : ContinuousAt Complex.digamma ((1 : ℂ) / 2) :=
    (differentiableAt_digamma_of_re_pos (by norm_num)).continuousAt
  have hcomp : ContinuousAt (fun s : ℂ => Complex.digamma (s / 2)) 1 :=
    ContinuousAt.comp (g := Complex.digamma) (f := fun s : ℂ => s / 2) hd (by fun_prop)
  exact ((hcomp.div_const 2).sub continuousAt_const).add (continuousAt_const.div continuousAt_id
    one_ne_zero)

theorem tendsto_sub_one_mul_of_continuousAt {f : ℂ → ℂ} (hf : ContinuousAt f 1) :
    Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * f σ) (𝓝[>] 1) (𝓝 0) := by
  have h := ((tendsto_ofReal_nhdsGT_one.sub_const 1).mul (hf.tendsto.comp tendsto_ofReal_nhdsGT_one))
  rwa [sub_self, zero_mul] at h

/-- `(σ − 1) L(Λ)(σ) → 1` as `σ → 1⁺`. -/
theorem tendsto_sub_one_mul_LSeries_vonMangoldt :
    Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * LSeries (fun n => (Λ n : ℂ)) σ) (𝓝[>] 1) (𝓝 1) := by
  have hd := tendsto_sub_one_mul_of_continuousAt continuousAt_zetaArchimedeanDatum_one
  have hx := tendsto_sub_one_mul_of_continuousAt continuousAt_logDeriv_xi_one
  have h := (hd.add (tendsto_const_nhds (x := (1 : ℂ)))).sub hx
  rw [zero_add, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hne : (σ : ℂ) - 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith [show (1 : ℝ) < σ from hσ]
  have hid := logDeriv_xi_eq_datum hσ1
  rw [hid]
  field_simp
  ring

/-! ## Pole weight one -/

/-- **The full cone fixes the pole weight.**  If `lam` is full-cone Weil-positive and
`lam = βΛ + e` on `n ≥ 2` with `e` vanishing below `2` and `(σ − 1) L(e)(σ) → 0` as `σ → 1⁺`, then
`β = 1`. -/
theorem eq_one_of_weilPositiveFull {lam e : ℕ → ℝ} {β : ℝ} (hW : WeilPositiveFull lam)
    (hdec : ∀ n, 2 ≤ n → lam n = β * Λ n + e n) (he0 : ∀ n, n < 2 → e n = 0)
    (he : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * LSeries (fun n => (e n : ℂ)) σ) (𝓝[>] 1)
      (𝓝 0)) : β = 1 := by
  have hL := tendsto_sub_one_mul_LSeries_vonMangoldt
  have hlhs : Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * (logDeriv xi σ - weilContinuation hW σ))
      (𝓝[>] 1) (𝓝 0) := by
    have hΦ : ContinuousAt (weilContinuation hW) 1 :=
      ((differentiableOn_weilContinuation hW).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num))).continuousAt
    exact tendsto_sub_one_mul_of_continuousAt (continuousAt_logDeriv_xi_one.sub hΦ)
  have hrhs : Tendsto (fun σ : ℝ => ((β : ℂ) - 1) * (((σ : ℂ) - 1) *
      LSeries (fun n => (Λ n : ℂ)) σ) + ((σ : ℂ) - 1) * LSeries (fun n => (e n : ℂ)) σ)
      (𝓝[>] 1) (𝓝 (((β : ℂ) - 1) * 1 + 0)) := (hL.const_mul _).add he
  have hcongr : (fun σ : ℝ => ((σ : ℂ) - 1) * (logDeriv xi σ - weilContinuation hW σ)) =ᶠ[𝓝[>] 1]
      fun σ : ℝ => ((β : ℂ) - 1) * (((σ : ℂ) - 1) * LSeries (fun n => (Λ n : ℂ)) σ) +
        ((σ : ℂ) - 1) * LSeries (fun n => (e n : ℂ)) σ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : 1 < ((σ : ℂ)).re := by simpa using hσ
    have hlam := summable_term_lamC hW hσ1
    have hΛs := ArithmeticFunction.LSeriesSummable_vonMangoldt hσ1
    have hfun : (fun n => (e n : ℂ)) = lamC lam - (β : ℂ) • fun n => (Λ n : ℂ) := by
      funext n
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lamC]
      by_cases hn : 2 ≤ n
      · rw [if_pos hn, hdec n hn]; push_cast; ring
      · rw [if_neg hn, he0 n (by omega),
          WeilOneSided.vonMangoldt_eq_zero_of_lt_two (by omega)]
        simp
    have hLe : LSeries (fun n => (e n : ℂ)) σ =
        LSeries (lamC lam) σ - (β : ℂ) * LSeries (fun n => (Λ n : ℂ)) σ := by
      rw [hfun, LSeries_sub hlam (hΛs.smul _), LSeries_smul]
    rw [logDeriv_xi_sub_weilContinuation_eq hW hσ1, hLe]
    ring
  have hlim := tendsto_nhds_unique (hlhs.congr' hcongr) hrhs
  have : (β : ℂ) - 1 = 0 := by simpa using hlim.symm
  have hβ : (β : ℂ) = 1 := sub_eq_zero.mp this
  exact_mod_cast hβ

/-! ## The low-frequency bound for a general pole weight -/

/-- The Weil functional with pole weight `β`. -/
def weilPoleWeightFunctional (β : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  weilFullFunctional lam k + ((β : ℂ) - 1) * (paperFT k (I / 2) + paperFT k (-I / 2))

/-- The autocorrelation of a test supported in `[−R, R]`, `2R < log 2`, vanishes at every
`±log n`, `n ≥ 2`. -/
theorem atomPairing_lowFrequency (v : ℕ → ℝ) {F : ℝ → ℝ} {R : ℝ}
    (hF : ∀ t, R < |t| → F t = 0) (hR : R + R < Real.log 2) :
    atomPairing v (crossCorr F F) = 0 := by
  unfold atomPairing
  refine (tsum_congr fun n => ?_).trans tsum_zero
  split_ifs with hn
  · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hpos : 0 < Real.log n := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog
    rw [crossCorr_eq_zero hF hF (y := Real.log n) (by rw [abs_of_pos hpos]; linarith),
      crossCorr_eq_zero hF hF (y := -Real.log n) (by rw [abs_neg, abs_of_pos hpos]; linarith)]
    ring
  · ring

/-- **The explicit formula at a low-frequency test, pole weight `β`.** -/
theorem re_weilPoleWeightFunctional_lowFrequency (β : ℝ) (lam : ℕ → ℝ) {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFc : HasCompactSupport F) {R : ℝ}
    (hF : ∀ t, R < |t| → F t = 0) (hR : R + R < Real.log 2) :
    (weilPoleWeightFunctional β lam (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re =
      (zetaZeroConfig.W (fun u => (F u : ℂ)) fun u => (F u : ℂ)).re -
        (1 - β) * (paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) (I / 2) +
          paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) (-I / 2)).re := by
  have h := re_weilFullFunctional_add_eq (fun n => lam n - Λ n) hFd hFc
  simp only [add_sub_cancel] at h
  rw [atomPairing_lowFrequency _ hF hR, sub_zero] at h
  rw [weilPoleWeightFunctional, Complex.add_re, h,
    show ((β : ℂ) - 1) = ((β - 1 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  ring

/-- **Positivity at a low-frequency test bounds the pole weight**:
`(1 − β)·Re(k̂_F(i/2) + k̂_F(−i/2)) ≤ Re W_ζ(F, F)`. -/
theorem one_sub_mul_re_pole_le (β : ℝ) (lam : ℕ → ℝ) {F : ℝ → ℝ}
    (hFd : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFc : HasCompactSupport F) {R : ℝ}
    (hF : ∀ t, R < |t| → F t = 0) (hR : R + R < Real.log 2)
    (hpos : 0 ≤ (weilPoleWeightFunctional β lam
      (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re) :
    (1 - β) * (paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) (I / 2) +
        paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) (-I / 2)).re ≤
      (zetaZeroConfig.W (fun u => (F u : ℂ)) fun u => (F u : ℂ)).re := by
  rw [re_weilPoleWeightFunctional_lowFrequency β lam hFd hFc hF hR] at hpos
  linarith

/-- **Under RH**: `(1 − β)·pole(K) ≤ Σ_ρ m_ρ K(γ_ρ)` with `K = |F̂|²`, i.e.
`β ≥ 1 − Σ_ρ m_ρ K(γ_ρ)/pole(K)`. -/
theorem one_sub_mul_re_pole_le_zeroSum (hRH : RiemannHypothesis) (β : ℝ) (lam : ℕ → ℝ)
    {F : ℝ → ℝ} (hFd : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFc : HasCompactSupport F) {R : ℝ}
    (hF : ∀ t, R < |t| → F t = 0) (hR : R + R < Real.log 2)
    (hpos : 0 ≤ (weilPoleWeightFunctional β lam
      (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re) :
    (1 - β) * (paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) (I / 2) +
        paperFT (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ)) (-I / 2)).re ≤
      ∑' ρ, zeroTerm (fun u => (F u : ℂ)) ρ := by
  rw [← re_W_eq_tsum_zeroTerm hRH hFd (hFc.comp_left Complex.ofReal_zero)]
  exact one_sub_mul_re_pole_le β lam hFd hFc hF hR hpos

end RHTower.WeilPoleWeight
