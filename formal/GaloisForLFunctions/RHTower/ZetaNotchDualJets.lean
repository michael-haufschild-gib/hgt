import GaloisForLFunctions.RHTower.ZetaNotchDualOscillationBound
import GaloisForLFunctions.RHTower.ChiRatioProductJets
import GaloisForLFunctions.HTGeometry.FourierIteratedDerivDecay

/-!
# All-order height jets of the critical dual carrier and `K`-fold oscillation

On the dual contour `w = −(1+iv)` the critical carrier `G_t = G_t(w)` satisfies `G' = G·D`, where
`D = chiIncrementDifference ½ v` is the corpus increment difference at abscissa `½`. The
increment jets `‖D^{(j)}‖ ≤ 10 (j+1)! 2^{j+1}(1+|v|)/t^{j+1}` hold at `σ₀ = ½`. The Leibniz
induction of the Levinson lines then gives

`‖G^{(n)}(t)‖ ≤ n! ‖G(t)‖ (22(1+|v|)/t)^n`   (`t ≥ 4`, `2|v| ≤ t`).

Together with the window jets, `K`-fold integration by parts gives, for `L ≥ 16`, `Y > 0`, `ξ ≠ 0`
(`exists_norm_notchDualOscillation_le_pow`):

`‖∫ ω(t) W_t(Y) e^{−iξt} dt‖ ≤ (C_K/Y)(L^{3−K}/|ξ|^K + L³ e^{−L²/128})`.
-/

noncomputable section

namespace RHTower.ZetaNotch

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

theorem levinsonShift_eq_dual (v : ℝ) :
    levinsonShift v = -(((1 : ℝ) : ℂ) + (v : ℂ) * I) := by
  unfold levinsonShift
  push_cast
  ring

theorem critIncrement_levinsonShift (v t : ℝ) :
    critIncrement t (levinsonShift v) = chiIncrementDifference (1 / 2) v t := by
  unfold critIncrement chiIncrementDifference chiIncrement chiIncrementC linePt
  push_cast
  ring_nf

/-- The critical carrier along the dual contour. -/
def critDualCarrier (v : ℝ) (t : ℝ) : ℂ := critCarrier t (levinsonShift v)

theorem hasDerivAt_critDualCarrier (v t : ℝ) :
    HasDerivAt (critDualCarrier v) (critDualCarrier v t * chiIncrementDifference (1 / 2) v t) t := by
  have h := hasDerivAt_critCarrier_dual t v
  rw [← levinsonShift_eq_dual, critIncrement_levinsonShift] at h
  exact h

theorem analyticAt_critDualCarrier (v u : ℝ) : AnalyticAt ℝ (critDualCarrier v) u := by
  have hline : ∀ σ : ℝ, AnalyticAt ℝ (fun s : ℝ => linePt (σ * s)) u := by
    intro σ
    show AnalyticAt ℝ (fun s : ℝ => ((1 / 2 : ℝ) : ℂ) + ((σ * s : ℝ) : ℂ) * I) u
    have : AnalyticAt ℝ (fun s : ℝ => ((σ * s : ℝ) : ℂ)) u :=
      Complex.ofRealCLM.analyticAt (σ * u) |>.comp (analyticAt_const.mul analyticAt_id)
    exact analyticAt_const.add (this.mul analyticAt_const)
  have hratio : ∀ σ : ℝ, AnalyticAt ℝ (fun s : ℝ =>
      smoothAFEZetaChiShiftRatio (linePt (σ * s)) (levinsonShift v)) u := by
    intro σ
    have hΓ : Gammaℝ (1 - (linePt (σ * u) + levinsonShift v)) ≠ 0 := by
      rw [levinsonShift_eq_dual]; exact gammaR_one_sub_dual_ne_zero _ v
    have hnum : AnalyticAt ℝ (fun s : ℝ => zetaChi (linePt (σ * s) + levinsonShift v)) u :=
      AnalyticAt.comp (g := zetaChi) (f := fun s : ℝ => linePt (σ * s) + levinsonShift v)
        (zetaChi_analyticAt hΓ).restrictScalars ((hline σ).add analyticAt_const)
    have hden : AnalyticAt ℝ (fun s : ℝ => zetaChi (linePt (σ * s))) u :=
      AnalyticAt.comp (g := zetaChi) (f := fun s : ℝ => linePt (σ * s))
        (zetaChi_analyticAt (gammaR_one_sub_linePt_ne_zero _)).restrictScalars (hline σ)
    exact hnum.div hden (zetaChi_line_ne_zero _)
  have h := (hratio 1).mul (hratio (-1))
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Pi.mul_apply, one_mul, neg_one_mul, critDualCarrier, critCarrier]

theorem contDiff_critDualCarrier (v : ℝ) (n : ℕ) : ContDiff ℝ n (critDualCarrier v) :=
  contDiff_iff_contDiffAt.mpr fun u => (analyticAt_critDualCarrier v u).contDiffAt

/-- **All-order height jets of the critical dual carrier.** -/
theorem norm_iteratedDeriv_critDualCarrier_le {v t : ℝ} (ht : 4 ≤ t) (hv : 2 * |v| ≤ t) (n : ℕ) :
    ‖iteratedDeriv n (critDualCarrier v) t‖
      ≤ n.factorial * ‖critDualCarrier v t‖ * (22 * (1 + |v|) / t) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  cases n with
  | zero => simp
  | succ n =>
    have ht0 : (0 : ℝ) < t := by linarith
    have hderiv : deriv (critDualCarrier v) =
        fun s => critDualCarrier v s * chiIncrementDifference (1 / 2) v s :=
      funext fun s => (hasDerivAt_critDualCarrier v s).deriv
    rw [iteratedDeriv_succ', hderiv]
    have hwin := isOpen_levinsonWindow v
    have htw : t ∈ levinsonWindow v := mem_levinsonWindow_of ht hv
    have hFc : ContDiffOn ℝ n (critDualCarrier v) (levinsonWindow v) :=
      (contDiff_critDualCarrier v n).contDiffOn
    have hDc : ContDiffOn ℝ n (chiIncrementDifference (1 / 2) v) (levinsonWindow v) :=
      contDiffOn_chiIncrementDifference (1 / 2) v n
    have hleib := norm_iteratedFDerivWithin_mul_le hFc hDc hwin.uniqueDiffOn htw
      (le_refl ((n : ℕ∞) : WithTop ℕ∞))
    have hconv : ∀ (k : ℕ) (f : ℝ → ℂ),
        iteratedFDerivWithin ℝ k f (levinsonWindow v) t = iteratedFDeriv ℝ k f t :=
      fun k f => iteratedFDerivWithin_of_isOpen k hwin htw
    simp only [hconv, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hleib
    refine hleib.trans ?_
    have hDb : ∀ j, j ≤ n → ‖iteratedDeriv j (chiIncrementDifference (1 / 2) v) t‖
        ≤ 10 * (j + 1).factorial * ((22 * (1 + |v|) / t) / 11) ^ (j + 1) := by
      intro j _
      refine (norm_iteratedDeriv_chiIncrementDifference_le (by norm_num) (by norm_num) ht hv
        j).trans ?_
      rw [show 22 * (1 + |v|) / t / 11 = 2 * (1 + |v|) / t by ring, div_pow, mul_pow]
      have h1v : (1 + |v|) ≤ (1 + |v|) ^ (j + 1) :=
        le_self_pow₀ (by linarith [abs_nonneg v]) (by omega)
      have hrhs : 10 * ((j + 1).factorial : ℝ) * (2 ^ (j + 1) * (1 + |v|) ^ (j + 1) / t ^ (j + 1))
          = (10 * (j + 1).factorial * 2 ^ (j + 1) * (1 + |v|) ^ (j + 1)) / t ^ (j + 1) := by ring
      rw [hrhs]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1v (by positivity))
        (by positivity)
    have hFb : ∀ i, i ≤ n → ‖iteratedDeriv i (critDualCarrier v) t‖
        ≤ i.factorial * ‖critDualCarrier v t‖ * (22 * (1 + |v|) / t) ^ i :=
      fun i hi => ih i (Nat.lt_succ_of_le hi)
    exact leibniz_factorial_sum_le n (norm_nonneg _) (by positivity)
      (fun i => ‖iteratedDeriv i (critDualCarrier v) t‖)
      (fun j => ‖iteratedDeriv j (chiIncrementDifference (1 / 2) v) t‖)
      (fun j => norm_nonneg _) hFb hDb

/-! ## The windowed carrier and its `K`-fold oscillation -/

/-- The windowed critical dual carrier. -/
def notchCarrier (L v : ℝ) (t : ℝ) : ℂ := notchWindow L t * critDualCarrier v t

theorem contDiff_notchCarrier (L v : ℝ) (n : ℕ) : ContDiff ℝ n (notchCarrier L v) :=
  ((contDiff_notchWindow L).of_le (WithTop.coe_le_coe.mpr le_top)).mul
    (contDiff_critDualCarrier v n)

theorem notchCarrier_eq_zero {L v t : ℝ} (hL : 0 < L) (ht : t ∉ Icc (L / 2) (5 * L / 2)) :
    notchCarrier L v t = 0 := by
  unfold notchCarrier
  rw [notchWindow_eq_zero hL ht, zero_mul]

theorem hasCompactSupport_notchCarrier {L v : ℝ} (hL : 0 < L) :
    HasCompactSupport (notchCarrier L v) :=
  HasCompactSupport.of_support_subset_isCompact (K := Icc (L / 2) (5 * L / 2)) isCompact_Icc
    (fun t ht => by
      by_contra hnot
      exact ht (notchCarrier_eq_zero hL hnot))

theorem iteratedDeriv_notchCarrier_eq_zero (n : ℕ) {L v t : ℝ} (hL : 0 < L)
    (ht : t ∉ Icc (L / 2) (5 * L / 2)) : iteratedDeriv n (notchCarrier L v) t = 0 := by
  have hopen : IsOpen (Icc (L / 2) (5 * L / 2))ᶜ := isClosed_Icc.isOpen_compl
  have hev : notchCarrier L v =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact notchCarrier_eq_zero hL hs
  rw [hev.iteratedDeriv_eq n]
  simp

/-- The notch jet constant. -/
def notchJetConst (K : ℕ) (L v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), (K.choose j : ℝ) * (blockWindowConst j / (L / 2) ^ j)
    * ((K - j).factorial * (44 * (1 + |v|) / L) ^ (K - j))

theorem notchJetConst_nonneg (K : ℕ) {L : ℝ} (hL : 0 < L) (v : ℝ) : 0 ≤ notchJetConst K L v :=
  Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (by positivity)
    (div_nonneg (blockWindowConst_nonneg j) (by positivity))) (by positivity)

/-- The notch jet constant is `O_K((1+|v|)^K / L^K)`. -/
theorem notchJetConst_le (K : ℕ) {L : ℝ} (hL : 1 ≤ L) (v : ℝ) :
    notchJetConst K L v ≤
      (∑ j ∈ Finset.range (K + 1), (K.choose j : ℝ) * (blockWindowConst j * 2 ^ j)
        * ((K - j).factorial * 44 ^ (K - j))) * (1 + |v|) ^ K / L ^ K := by
  have hL0 : 0 < L := by linarith
  have h1v : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  rw [notchJetConst, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hc := blockWindowConst_nonneg j
  have hpow : (1 + |v|) ^ (K - j) ≤ (1 + |v|) ^ K := pow_le_pow_right₀ h1v (Nat.sub_le K j)
  have hLsplit : L ^ K = L ^ j * L ^ (K - j) := by rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [hLsplit]
  set A : ℝ := (K.choose j : ℝ) * (blockWindowConst j * 2 ^ j) * ((K - j).factorial * 44 ^ (K - j))
    with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hLj : 0 < L ^ j := by positivity
  have hLkj : 0 < L ^ (K - j) := by positivity
  have e : (K.choose j : ℝ) * (blockWindowConst j / (L / 2) ^ j) *
      ((K - j).factorial * (44 * (1 + |v|) / L) ^ (K - j)) =
      A * (1 + |v|) ^ (K - j) / (L ^ j * L ^ (K - j)) := by
    rw [hA, div_pow, div_pow, mul_pow]
    field_simp
  rw [e]
  gcongr

/-- **Jets of the windowed carrier.** -/
theorem norm_iteratedDeriv_notchCarrier_le (K : ℕ) {L v t : ℝ} (hL : 16 ≤ L) (hv : |v| ≤ L / 4)
    (ht : L / 2 ≤ t) :
    ‖iteratedDeriv K (notchCarrier L v) t‖ ≤ notchJetConst K L v * ‖critDualCarrier v t‖ := by
  have hL0 : (0 : ℝ) < L := by linarith
  have ht4 : (4 : ℝ) ≤ t := by linarith
  have hvt : 2 * |v| ≤ t := by linarith
  have hleib := norm_iteratedFDeriv_mul_le
    ((contDiff_notchWindow L).of_le (WithTop.coe_le_coe.mpr le_top) :
      ContDiff ℝ ((K : ℕ∞) : WithTop ℕ∞) (notchWindow L))
    (contDiff_critDualCarrier v K) t (le_refl ((K : ℕ∞) : WithTop ℕ∞))
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hleib
  unfold notchCarrier
  refine hleib.trans ?_
  rw [notchJetConst, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := norm_iteratedDeriv_blockWindowC_le j L (2 * L) (η := L / 2) (by linarith) t
  have h2 := norm_iteratedDeriv_critDualCarrier_le ht4 hvt (K - j)
  have hbase : 22 * (1 + |v|) / t ≤ 44 * (1 + |v|) / L := by
    rw [div_le_div_iff₀ (by linarith) hL0]
    nlinarith [abs_nonneg v]
  have h2' : ‖iteratedDeriv (K - j) (critDualCarrier v) t‖
      ≤ (K - j).factorial * ‖critDualCarrier v t‖ * (44 * (1 + |v|) / L) ^ (K - j) :=
    h2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _)
      (by positivity))
  calc (K.choose j : ℝ) * ‖iteratedDeriv j (notchWindow L) t‖
        * ‖iteratedDeriv (K - j) (critDualCarrier v) t‖
      ≤ (K.choose j : ℝ) * (blockWindowConst j / (L / 2) ^ j)
          * ((K - j).factorial * ‖critDualCarrier v t‖ * (44 * (1 + |v|) / L) ^ (K - j)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2' (norm_nonneg _)
          (mul_nonneg (by positivity) (div_nonneg (blockWindowConst_nonneg j) (by positivity)))
    _ = (K.choose j : ℝ) * (blockWindowConst j / (L / 2) ^ j)
          * ((K - j).factorial * (44 * (1 + |v|) / L) ^ (K - j)) * ‖critDualCarrier v t‖ := by
        ring

/-- **`K`-fold oscillation of the windowed dual carrier.** -/
theorem norm_integral_notchCarrier_mul_cexp_le (K : ℕ) {L v ξ : ℝ} (hL : 16 ≤ L)
    (hv : |v| ≤ L / 4) (hξ : ξ ≠ 0) :
    ‖∫ t, notchCarrier L v t * Complex.exp (-(ξ * t) * I)‖
      ≤ 2 * L * (notchJetConst K L v * (9 * L ^ 2 * (1 + |v|) ^ 2)) / |ξ| ^ K := by
  have hL0 : (0 : ℝ) < L := by linarith
  refine (norm_integral_mul_cexp_le_of_iteratedDeriv K (contDiff_notchCarrier L v K)
    (fun n _ => integrable_iteratedDeriv_of_hasCompactSupport (contDiff_notchCarrier L v K)
      (hasCompactSupport_notchCarrier hL0) (by omega)) hξ).trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := integral_norm_le_of_forall_mem_Icc (g := iteratedDeriv K (notchCarrier L v))
    (a := L / 2) (b := 5 * L / 2) (M := notchJetConst K L v * (9 * L ^ 2 * (1 + |v|) ^ 2))
    (by linarith) (integrable_iteratedDeriv_of_hasCompactSupport (contDiff_notchCarrier L v K)
      (hasCompactSupport_notchCarrier hL0) le_rfl)
    (fun t ht => iteratedDeriv_notchCarrier_eq_zero K hL0 ht)
    (fun t ht => by
      refine (norm_iteratedDeriv_notchCarrier_le K hL hv ht.1).trans ?_
      apply mul_le_mul_of_nonneg_left _ (notchJetConst_nonneg K hL0 v)
      have := norm_critCarrier_dual_le_window (v := v) (by linarith) ht
      simpa [critDualCarrier, levinsonShift_eq_dual] using this)
  refine h.trans (le_of_eq ?_)
  ring

/-- **`K`-fold dual-line oscillation bound.** -/
theorem exists_norm_notchDualOscillation_le_pow (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L Y ξ : ℝ}, 16 ≤ L → 0 < Y → ξ ≠ 0 →
      ‖∫ t, notchWindow L t * critDualWeight t Y * Complex.exp (-(ξ * t) * I)‖ ≤
        C / Y * (L ^ 3 / (L * |ξ|) ^ K + L ^ 3 * Real.exp (-(L ^ 2) / 32)) := by
  set A_K : ℝ := ∑ j ∈ Finset.range (K + 1), (K.choose j : ℝ) * (blockWindowConst j * 2 ^ j)
        * ((K - j).factorial * 44 ^ (K - j)) with hA_K
  have hA_K0 : 0 ≤ A_K := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (blockWindowConst_nonneg j) (by positivity)))
      (by positivity)
  set I_K : ℝ := ∫ v : ℝ, (1 + |v|) ^ (K + 2) * Real.exp (-(v ^ (2 : ℕ))) with hI_K
  have hI_K0 : 0 ≤ I_K := integral_nonneg fun v => by positivity
  clear_value A_K I_K
  set C : ℝ := (1 / (2 * Real.pi)) * Real.exp 1 *
    (18 * A_K * I_K + 18 * (Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi))) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  clear_value C
  refine ⟨C, hC0, fun {L Y ξ} hL hY hξ => ?_⟩
  have hL0 : 0 < L := by linarith
  rw [integral_notch_critDualWeight_eq (by linarith) hY, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  set inner : ℝ → ℂ := fun v : ℝ => ∫ t, notchWindow L t *
      critCarrier t (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) * Complex.exp (-(ξ * t) * I) with hinner
  set S : Set ℝ := {v : ℝ | |v| ≤ L / 4} with hS
  have hSmeas : MeasurableSet Sᶜ :=
    (isClosed_le continuous_abs continuous_const).measurableSet.compl
  have hξL : 0 < L * |ξ| := by have := abs_pos.mpr hξ; positivity
  set g : ℝ → ℝ := fun v => (Y⁻¹ * Real.exp 1) *
    (18 * A_K * L ^ 3 / (L * |ξ|) ^ K * ((1 + |v|) ^ (K + 2) * Real.exp (-(v ^ (2 : ℕ)))) +
      18 * L ^ 3 * Sᶜ.indicator (fun v => (1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ)))) v) with hg
  have hgint : Integrable g := by
    have h1 := (integrable_one_add_abs_pow_mul_exp_neg_sq (K + 2)).const_mul
      (18 * A_K * L ^ 3 / (L * |ξ|) ^ K)
    have h2 := ((integrable_one_add_abs_pow_mul_exp_neg_sq 2).indicator hSmeas).const_mul
      (18 * L ^ 3)
    exact (h1.add h2).const_mul _
  have hpt : ∀ v, ‖inner v * smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ g v := by
    intro v
    rw [norm_mul]
    have hm := norm_smoothAFEMellinIntegrand_vertical_le hY (show (0 : ℝ) < 1 by norm_num) v
    have hm' : ‖smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        (Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ (2 : ℕ))) := by
      simpa [Real.rpow_neg_one] using hm
    have hinnerb : ‖inner v‖ ≤ 18 * A_K * L ^ 3 / (L * |ξ|) ^ K * (1 + |v|) ^ (K + 2) +
        18 * L ^ 3 * Sᶜ.indicator (fun v => (1 + |v|) ^ 2) v := by
      by_cases hv : |v| ≤ L / 4
      · have hb := norm_integral_notchCarrier_mul_cexp_le K hL hv hξ
        have hrw : inner v = ∫ t, notchCarrier L v t * Complex.exp (-(ξ * t) * I) := by
          simp only [hinner, notchCarrier, critDualCarrier, levinsonShift_eq_dual]
        have hnot : v ∉ Sᶜ := by simp [hS, hv]
        rw [indicator_of_notMem hnot, mul_zero, add_zero, hrw]
        refine hb.trans ?_
        have hJ := notchJetConst_le K (L := L) (by linarith) v
        have hJ0 := notchJetConst_nonneg K hL0 v
        have hLK : 0 < L ^ K := by positivity
        have hξK : 0 < |ξ| ^ K := by have := abs_pos.mpr hξ; positivity
        rw [← hA_K] at hJ
        have hA_K0' := hA_K0
        calc 2 * L * (notchJetConst K L v * (9 * L ^ 2 * (1 + |v|) ^ 2)) / |ξ| ^ K
            ≤ 2 * L * (A_K * (1 + |v|) ^ K / L ^ K * (9 * L ^ 2 * (1 + |v|) ^ 2)) / |ξ| ^ K := by
              gcongr
          _ = 18 * A_K * L ^ 3 / (L * |ξ|) ^ K * (1 + |v|) ^ (K + 2) := by
              rw [mul_pow]
              field_simp
              ring
      · have hb := norm_windowed_dual_le_trivial (v := v) (ξ := ξ) hL
        have hmem : v ∈ Sᶜ := by simp [hS, hv]
        rw [indicator_of_mem hmem]
        have hnn : 0 ≤ 18 * A_K * L ^ 3 / (L * |ξ|) ^ K * (1 + |v|) ^ (K + 2) := by positivity
        linarith
    have hind : Sᶜ.indicator (fun v => (1 + |v|) ^ 2) v * Real.exp (-(v ^ (2 : ℕ))) =
        Sᶜ.indicator (fun v => (1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ)))) v := by
      by_cases hv : v ∈ Sᶜ
      · rw [indicator_of_mem hv, indicator_of_mem hv]
      · rw [indicator_of_notMem hv, indicator_of_notMem hv, zero_mul]
    calc ‖inner v‖ * ‖smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ (18 * A_K * L ^ 3 / (L * |ξ|) ^ K * (1 + |v|) ^ (K + 2) +
            18 * L ^ 3 * Sᶜ.indicator (fun v => (1 + |v|) ^ 2) v) *
          ((Y⁻¹ * Real.exp 1) * Real.exp (-(v ^ (2 : ℕ)))) :=
          mul_le_mul hinnerb hm' (norm_nonneg _) (by
            have : 0 ≤ Sᶜ.indicator (fun v : ℝ => (1 + |v|) ^ 2) v :=
              indicator_nonneg (fun _ _ => by positivity) v
            positivity)
      _ = g v := by
          simp only [hg]
          rw [← hind]
          ring
  have hbound := norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)
  have hgval : ∫ v, g v ≤ (Y⁻¹ * Real.exp 1) * (18 * A_K * L ^ 3 / (L * |ξ|) ^ K * I_K +
      18 * L ^ 3 * (Real.exp (2 ^ 2) * Real.exp (-(L / 4) ^ 2 / 2) * Real.sqrt (4 * Real.pi))) := by
    have htail := integral_one_add_abs_pow_mul_exp_neg_sq_compl_le 2 (V := L / 4) (by linarith)
    have hsplit : ∫ v, g v = (Y⁻¹ * Real.exp 1) * (18 * A_K * L ^ 3 / (L * |ξ|) ^ K * I_K +
        18 * L ^ 3 * ∫ v in Sᶜ, (1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ)))) := by
      simp only [hg]
      rw [integral_const_mul, integral_add, integral_const_mul, integral_const_mul,
        integral_indicator hSmeas, ← hI_K]
      · exact (integrable_one_add_abs_pow_mul_exp_neg_sq (K + 2)).const_mul _
      · exact ((integrable_one_add_abs_pow_mul_exp_neg_sq 2).indicator hSmeas).const_mul _
    rw [hsplit]
    have htail' : ∫ v in Sᶜ, (1 + |v|) ^ 2 * Real.exp (-(v ^ (2 : ℕ))) ≤
        Real.exp (2 ^ 2) * Real.exp (-(L / 4) ^ 2 / 2) * Real.sqrt (4 * Real.pi) := by
      simpa using htail
    gcongr
  have hexp : Real.exp (-(L / 4) ^ 2 / 2) = Real.exp (-(L ^ 2) / 32) := by
    congr 1; ring
  rw [hexp] at hgval
  calc 1 / (2 * Real.pi) * ‖∫ v : ℝ, inner v *
        smoothAFEMellinIntegrand Y (((1 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ 1 / (2 * Real.pi) * ((Y⁻¹ * Real.exp 1) * (18 * A_K * L ^ 3 / (L * |ξ|) ^ K * I_K +
          18 * L ^ 3 * (Real.exp (2 ^ 2) * Real.exp (-(L ^ 2) / 32) *
            Real.sqrt (4 * Real.pi)))) :=
        mul_le_mul_of_nonneg_left (hbound.trans hgval) (by positivity)
    _ ≤ C / Y * (L ^ 3 / (L * |ξ|) ^ K + L ^ 3 * Real.exp (-(L ^ 2) / 32)) := by
        rw [hCdef]
        have hA : 0 ≤ L ^ 3 / (L * |ξ|) ^ K := by positivity
        have hB : 0 ≤ L ^ 3 * Real.exp (-(L ^ 2) / 32) := by positivity
        have hsq : 0 ≤ Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi) := by positivity
        have key : 18 * A_K * L ^ 3 / (L * |ξ|) ^ K * I_K + 18 * L ^ 3 * (Real.exp (2 ^ 2) *
            Real.exp (-(L ^ 2) / 32) * Real.sqrt (4 * Real.pi)) ≤
            (18 * A_K * I_K + 18 * (Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi))) *
              (L ^ 3 / (L * |ξ|) ^ K + L ^ 3 * Real.exp (-(L ^ 2) / 32)) := by
          have e1 : 18 * A_K * L ^ 3 / (L * |ξ|) ^ K * I_K =
              18 * A_K * I_K * (L ^ 3 / (L * |ξ|) ^ K) := by ring
          have e2 : 18 * L ^ 3 * (Real.exp (2 ^ 2) * Real.exp (-(L ^ 2) / 32) *
              Real.sqrt (4 * Real.pi)) = 18 * (Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi)) *
                (L ^ 3 * Real.exp (-(L ^ 2) / 32)) := by ring
          rw [e1, e2]
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hA_K0) hI_K0) hB,
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hsq) hA]
        calc 1 / (2 * Real.pi) * ((Y⁻¹ * Real.exp 1) * (18 * A_K * L ^ 3 / (L * |ξ|) ^ K * I_K +
              18 * L ^ 3 * (Real.exp (2 ^ 2) * Real.exp (-(L ^ 2) / 32) *
                Real.sqrt (4 * Real.pi))))
            ≤ 1 / (2 * Real.pi) * ((Y⁻¹ * Real.exp 1) *
                ((18 * A_K * I_K + 18 * (Real.exp (2 ^ 2) * Real.sqrt (4 * Real.pi))) *
                  (L ^ 3 / (L * |ξ|) ^ K + L ^ 3 * Real.exp (-(L ^ 2) / 32)))) := by
              gcongr
          _ = _ := by ring

end RHTower.ZetaNotch
