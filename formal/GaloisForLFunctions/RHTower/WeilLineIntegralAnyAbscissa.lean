import GaloisForLFunctions.RHTower.WeilAtomicExplicitFormula
import GaloisForLFunctions.RHTower.DigammaBinetFourthOrder
import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import GaloisForLFunctions.RHTower.WeilPositiveShortIntervalSupport

/-!
# The Weil functional as a line integral on any line of absolute convergence

For real weights `lam` whose Dirichlet series `Σ_{n≥2} lam(n) n^{−s}` converges absolutely at
`s = c` with `c ≥ 3/2`, and every autocorrelation `k = f ⋆ f̃` of a `C²` compactly supported `f`,

`W_lam(k) = (1/2π) ∫ (H_k(c + it) + H_k(1 − c − it)) Φ_lam(c + it) dt`
(`weilFullFunctional_weilTest_eq_line`),

with `H_k(s) = k̂((s − ½)/i)` and `Φ_lam` the Weil function.  No absolute convergence below `c` is
assumed.  The prime part is a Fourier inversion on the line `Re s = c`; the pole part is the two-line
residue identity at `z₀ = 0`; the archimedean part is moved from `Re s = 3/2` to `Re s = c` by a
vertical contour shift, using the decay `|H_k(σ + it)| ≪ (1 + t²)^{−2}` on every vertical strip
(`norm_Hfn_weilTest_le_wide`) and the linear growth of `Γ_ℝ'/Γ_ℝ` (`norm_logDeriv_Gammaℝ_le_lin`,
from the fourth-order Binet bound).
-/

open Complex MeasureTheory Filter Topology Set
open Zeta23 Zeta23.WeilEF RHTower.WeilLineIntegral

noncomputable section

namespace RHTower.WeilLineAnyAbscissa

/-- Decay of `H_k` on every vertical strip `|σ − ½| ≤ M`. -/
theorem norm_Hfn_le_wide {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, |σ - 1 / 2| ≤ M → ‖Hfn k ((σ : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨Λ₁, hΛ₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  set B : ℝ := max Λ₁ 0 with hB
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ B := fun u hu => (hΛ₁ u hu).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  set M' : ℝ := max M 0 with hM'
  set A : ℝ := Real.exp (M' * B) * ((∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖) with hA
  have hI1 : 0 ≤ ∫ u, ‖k u‖ := integral_nonneg fun _ => norm_nonneg _
  have hI2 : 0 ≤ ∫ u, ‖deriv (deriv k) u‖ := integral_nonneg fun _ => norm_nonneg _
  have hA0 : 0 ≤ A := by positivity
  refine ⟨2 * A, by positivity, fun σ t hσ => ?_⟩
  rw [Hfn_apply]
  set z : ℂ := (t : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I with hz
  have hzim : z.im = 1 / 2 - σ := by simp [hz]
  have hzre : z.re = t := by simp [hz]
  have him : |z.im| ≤ M' := by
    rw [hzim, abs_sub_comm]
    exact hσ.trans (le_max_left _ _)
  have hexp : Real.exp (|z.im| * B) ≤ Real.exp (M' * B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right him hB0)
  have hzn : |t| ≤ ‖z‖ := by rw [← hzre]; exact Complex.abs_re_le_norm z
  have ht2 : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : |t| ≤ 1
  · have h1 := Zeta23.norm_paperFT_le hki hsupp z
    calc ‖paperFT k z‖ ≤ Real.exp (|z.im| * B) * ∫ u, ‖k u‖ := h1
      _ ≤ Real.exp (M' * B) * ∫ u, ‖k u‖ := by gcongr
      _ ≤ A := by rw [hA]; nlinarith [Real.exp_pos (M' * B)]
      _ ≤ 2 * A / (1 + t ^ 2) := by
          rw [le_div_iff₀ ht2]
          have : t ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
          nlinarith
  · push Not at ht
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hzn; simp at hzn; rw [hzn] at ht; simp at ht; linarith
    have h2 := Zeta23.norm_paperFT_le_div hk hsupp hz0
    have hzsq : t ^ 2 ≤ ‖z‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hzn 2
    have ht1 : 1 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith
    calc ‖paperFT k z‖ ≤ Real.exp (|z.im| * B) * (∫ u, ‖deriv (deriv k) u‖) / ‖z‖ ^ 2 := h2
      _ ≤ Real.exp (M' * B) * (∫ u, ‖deriv (deriv k) u‖) / t ^ 2 := by gcongr
      _ ≤ A / t ^ 2 := by gcongr; rw [hA]; nlinarith [Real.exp_pos (M' * B)]
      _ ≤ 2 * A / (1 + t ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) ht2]; nlinarith

/-- `|H_{f⋆f̃}(σ + it)| ≪ (1 + t²)^{−2}` on every vertical strip `|σ − ½| ≤ M`. -/
theorem norm_Hfn_weilTest_le_wide {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (M : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, |σ - 1 / 2| ≤ M →
      ‖Hfn (EF.weilTest f f) (σ + t * I)‖ ≤ C / (1 + t ^ 2) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le_wide hf hfc M
  refine ⟨C * C, mul_nonneg hC0 hC0, fun σ t hσ => ?_⟩
  have hfac : Hfn (EF.weilTest f f) (σ + t * I) =
      Hfn f (σ + t * I) * (starRingEnd ℂ) (Hfn f (((1 - σ : ℝ) : ℂ) + t * I)) := by
    unfold Hfn
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc]
    congr 3
    rw [map_div₀, Complex.conj_I, map_sub, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, map_ofNat]
    push_cast
    field_simp
    ring
  have hσ' : |(1 - σ) - 1 / 2| ≤ M := by
    rw [show (1 - σ) - 1 / 2 = -(σ - 1 / 2) by ring, abs_neg]; exact hσ
  rw [hfac, norm_mul, Complex.norm_conj, pow_two, ← div_mul_div_comm]
  exact mul_le_mul (hC σ t hσ) (hC (1 - σ) t hσ') (norm_nonneg _) (div_nonneg hC0 (by positivity))

/-- Linear growth of `Γ_ℝ'/Γ_ℝ` on `3/2 ≤ Re s ≤ c`, from the fourth-order Binet bound. -/
theorem norm_logDeriv_Gammaℝ_le_lin (c : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 3 / 2 ≤ s.re → s.re ≤ c →
      ‖logDeriv Complex.Gammaℝ s‖ ≤ A * (1 + |s.im|) := by
  have hπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  refine ⟨Real.log Real.pi + |c| + Real.pi + 4, by positivity, fun s h1 h2 => ?_⟩
  have hre : 0 < s.re := by linarith
  rw [logDeriv_Gammaℝ hre]
  set w : ℂ := s / 2 with hw
  have hwre : w.re = s.re / 2 := by simp [hw]
  have hwre' : 3 / 4 ≤ w.re := by rw [hwre]; linarith
  have hwn : 3 / 4 ≤ ‖w‖ := hwre'.trans ((le_abs_self _).trans (Complex.abs_re_le_norm w))
  have hwpos : 0 < ‖w‖ := by linarith
  have hB := RHTower.DigammaBinet.norm_digamma_sub_stirling_le (w := w) (by linarith)
  -- `‖log w‖ ≤ ‖w‖ + 1 + π`
  have hlog : ‖Complex.log w‖ ≤ ‖w‖ + 1 + Real.pi := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im]
    have ha := Complex.abs_arg_le_pi w
    have hl1 : Real.log ‖w‖ ≤ ‖w‖ := (Real.log_le_sub_one_of_pos hwpos).trans (by linarith)
    have hl2 : -1 ≤ Real.log ‖w‖ := by
      rw [Real.le_log_iff_exp_le hwpos]
      linarith [Real.exp_neg_one_lt_half]
    have : |Real.log ‖w‖| ≤ ‖w‖ + 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hinv1 : ‖1 / (2 * w)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, div_le_one (by positivity)]
    linarith
  have hinv2 : ‖1 / (12 * w ^ 2)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, norm_pow, div_le_one (by positivity)]
    nlinarith
  have hrem : 1 / (120 * w.re ^ 4) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (3 / 4 : ℝ) ^ 4 ≤ w.re ^ 4 := pow_le_pow_left₀ (by norm_num) hwre' 4
    nlinarith
  have hψ : ‖Complex.digamma w‖ ≤ ‖w‖ + 1 + Real.pi + 3 := by
    have e : Complex.digamma w = (Complex.digamma w - Complex.log w + 1 / (2 * w) +
        1 / (12 * w ^ 2)) + Complex.log w - 1 / (2 * w) - 1 / (12 * w ^ 2) := by ring
    rw [e]
    have n1 := norm_sub_le (Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2) +
      Complex.log w - 1 / (2 * w)) (1 / (12 * w ^ 2))
    have n2 := norm_sub_le (Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2) +
      Complex.log w) (1 / (2 * w))
    have n3 := norm_add_le (Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2))
      (Complex.log w)
    linarith
  have hwle : ‖w‖ ≤ (|c| + |s.im|) / 2 := by
    rw [hw, norm_div, Complex.norm_ofNat]
    have h3 := Complex.norm_le_abs_re_add_abs_im s
    have h4 : |s.re| ≤ |c| := by
      rw [abs_of_pos hre]; exact h2.trans (le_abs_self c)
    linarith
  have hn1 : ‖-((Real.log Real.pi : ℝ) : ℂ) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ, Complex.norm_ofNat]
  have hn2 : ‖(1 / 2 : ℂ) * Complex.digamma w‖ = 1 / 2 * ‖Complex.digamma w‖ := by
    rw [norm_mul]; norm_num
  refine (norm_add_le _ _).trans ?_
  rw [hn1, hn2]
  have hpi := Real.pi_pos
  nlinarith [abs_nonneg s.im, abs_nonneg c]

/-- `F_k(t) = H_k(c + it) + H_k(1 − c − it)`. -/
def lineF (k : ℝ → ℂ) (c t : ℝ) : ℂ := Hfn k (c + t * I) + Hfn k (1 - c - t * I)

/-- **The archimedean part on any line `Re s = c ≥ 3/2`.** -/
theorem integral_lineF_mul_logDeriv_Gammaℝ {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {c : ℝ} (hc : 3 / 2 ≤ c) :
    ∫ t : ℝ, lineF (EF.weilTest f f) c t * logDeriv Complex.Gammaℝ (c + t * I) =
      ∫ r : ℝ, paperFT (EF.weilTest f f) r * (Zeta23.EF.gammaBracket r : ℂ) := by
  set k := EF.weilTest f f with hkdef
  have hk : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  -- the formula on `Re s = 3/2`
  have hG : (∫ t : ℝ, lineF k (3 / 2) t * logDeriv Complex.Gammaℝ ((3 / 2 : ℝ) + t * I)) =
      ∫ r : ℝ, paperFT k r * (Zeta23.EF.gammaBracket r : ℂ) := by
    unfold lineF
    rw [gamma_line_shift hk hkc (by norm_num) le_rfl]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [gammaR_bracket t, Zeta23.EF.gammaBracket]
    congr 4
    ring_nf
  rw [← hG]
  -- the vertical shift from `3/2` to `c`
  obtain ⟨D, hD0, hD⟩ := norm_Hfn_weilTest_le_wide hf hfc c
  obtain ⟨A, hA0, hA⟩ := norm_logDeriv_Gammaℝ_le_lin c
  set Ψ : ℂ → ℂ := fun s => (Hfn k s + Hfn k (1 - s)) * logDeriv Complex.Gammaℝ s with hΨ
  have hΨline : ∀ σ t : ℝ, Ψ ((σ : ℂ) + t * I) = lineF k σ t * logDeriv Complex.Gammaℝ (σ + t * I) :=
    fun σ t => by simp only [hΨ, lineF]; congr 2; ring_nf
  have hHd := differentiable_Hfn hk hkc
  have hd : ∀ s : ℂ, s.re ∈ uIcc (3 / 2) c → DifferentiableAt ℂ Ψ s := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    have hre : 0 < s.re := by linarith [hs.1]
    refine ((hHd s).add ((hHd _).comp s (differentiableAt_const _ |>.sub differentiableAt_id))).mul ?_
    have heq : (fun z : ℂ => -((Real.log Real.pi : ℝ) : ℂ) / 2 + 1 / 2 * Complex.digamma (z / 2)) =ᶠ[𝓝 s]
        logDeriv Complex.Gammaℝ := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre] with z hz
      exact (logDeriv_Gammaℝ hz).symm
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
    refine (differentiableAt_const _).add ((differentiableAt_const _).mul ?_)
    exact (differentiableAt_digamma_of_re_pos (by simp; linarith)).comp s
      (differentiableAt_id.div_const 2)
  have hb : ∀ s : ℂ, s.re ∈ uIcc (3 / 2) c → ‖Ψ s‖ ≤ 4 * D * A / (1 + s.im ^ 2) := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    have h1 : |s.re - 1 / 2| ≤ c := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h2 : |(1 - s.re) - 1 / 2| ≤ c := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hb1 : ‖Hfn k s‖ ≤ D / (1 + s.im ^ 2) ^ 2 := by
      have := hD s.re s.im h1
      rwa [Complex.re_add_im] at this
    have hb2 : ‖Hfn k (1 - s)‖ ≤ D / (1 + s.im ^ 2) ^ 2 := by
      have := hD (1 - s.re) (-s.im) h2
      have e1 : ((1 - s.re : ℝ) : ℂ) + ((-s.im : ℝ) : ℂ) * I = 1 - s := by
        conv_rhs => rw [← Complex.re_add_im s]
        push_cast; ring
      rwa [e1, neg_sq] at this
    have hlin := hA s hs.1 hs.2
    have hsq : (1 + |s.im|) ≤ 2 * (1 + s.im ^ 2) := by nlinarith [sq_abs s.im, abs_nonneg s.im]
    simp only [hΨ]
    rw [norm_mul]
    calc ‖Hfn k s + Hfn k (1 - s)‖ * ‖logDeriv Complex.Gammaℝ s‖
        ≤ (D / (1 + s.im ^ 2) ^ 2 + D / (1 + s.im ^ 2) ^ 2) * (A * (1 + |s.im|)) :=
          mul_le_mul ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hlin (norm_nonneg _)
            (by positivity)
      _ ≤ (D / (1 + s.im ^ 2) ^ 2 + D / (1 + s.im ^ 2) ^ 2) * (A * (2 * (1 + s.im ^ 2))) := by
          gcongr
      _ = 4 * D * A / (1 + s.im ^ 2) := by field_simp; ring
  have hshift := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay hd hb
  simp_rw [hΨline] at hshift
  exact hshift.symm

/-- `‖Σ lam(n) n^{−(c+it)}‖` is bounded by the absolute series at `c`. -/
theorem norm_LSeries_line_le {a : ℕ → ℂ} {c : ℝ} (hsum : LSeriesSummable a c) (t : ℝ) :
    ‖LSeries a ((c : ℂ) + t * I)‖ ≤ ∑' n, ‖LSeries.term a c n‖ := by
  have hs : LSeriesSummable a ((c : ℂ) + t * I) :=
    (LSeriesSummable_iff_of_re_eq_re (by simp)).mpr hsum
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hs.norm).trans (le_of_eq (tsum_congr fun n => ?_))
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp

/-- **The Weil functional of an autocorrelation as a line integral on any line `Re s = c ≥ 3/2`
of absolute convergence.** -/
theorem weilFullFunctional_weilTest_eq_line {lam : ℕ → ℝ} {c : ℝ} (hc : 3 / 2 ≤ c)
    (hsum : LSeriesSummable (WeilHerglotz.lamC lam) c) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    weilFullFunctional lam (EF.weilTest f f) = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, lineF (EF.weilTest f f) c t * WeilHerglotz.weilFunction lam (c + t * I) := by
  set k := EF.weilTest f f with hkdef
  have hk : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  set kn : ℝ → ℂ := fun u => k (-u) with hkn
  have hkn2 : ContDiff ℝ 2 kn := hk.comp contDiff_neg
  have hknc : HasCompactSupport kn := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le_wide hk hkc c
  obtain ⟨Cn, hCn0, hCn⟩ := norm_Hfn_le_wide hkn2 hknc c
  obtain ⟨D, hD0, hD⟩ := norm_Hfn_weilTest_le_wide hf hfc c
  obtain ⟨A, hA0, hA⟩ := norm_logDeriv_Gammaℝ_le_lin c
  have hc1 : 1 < c := by linarith
  have hcc : |c - 1 / 2| ≤ c := abs_le.mpr ⟨by linarith, by linarith⟩
  set F : ℝ → ℂ := lineF k c with hF
  have hFm : ∀ t : ℝ, Hfn k (1 - c - t * I) = Hfn kn (c + t * I) := fun t => Hfn_mirror k c t
  have hFc : Continuous F := by
    have e : F = fun t : ℝ => Hfn k (c + t * I) + Hfn kn (c + t * I) := by
      funext t
      simp only [hF, lineF, hFm]
    rw [e]
    exact (continuous_Hfn_line hk hkc c).add (continuous_Hfn_line hkn2 hknc c)
  have hFb : ∀ t : ℝ, ‖F t‖ ≤ (C + Cn) / (1 + t ^ 2) := by
    intro t
    simp only [hF, lineF, hFm]
    refine (norm_add_le _ _).trans ?_
    rw [add_div]
    exact add_le_add (hC c t hcc) (hCn c t hcc)
  have hFb2 : ∀ t : ℝ, ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := by
    intro t
    have e : (1 : ℂ) - c - t * I = ((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    simp only [hF, lineF]
    refine (norm_add_le _ _).trans ?_
    rw [e]
    have h1 := hD c t hcc
    have h2 := hD (1 - c) (-t) (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [neg_sq] at h2
    rw [two_mul, add_div]
    exact add_le_add h1 h2
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  -- integrability of the three pieces
  have hiG : Integrable (fun t : ℝ => F t * logDeriv Complex.Gammaℝ (c + t * I)) := by
    have hcont : Continuous fun t : ℝ => logDeriv Complex.Gammaℝ ((c : ℂ) + t * I) := by
      have heq : (fun t : ℝ => logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)) =
          fun t : ℝ => -((Real.log Real.pi : ℝ) : ℂ) / 2 +
            1 / 2 * Complex.digamma (((c : ℂ) + t * I) / 2) := by
        funext t
        exact logDeriv_Gammaℝ (by rw [hre]; linarith)
      rw [heq]
      refine continuous_const.add (continuous_const.mul ?_)
      refine continuous_iff_continuousAt.mpr fun t => ?_
      exact ((differentiableAt_digamma_of_re_pos (by simp; linarith)).continuousAt).comp
        (by fun_prop)
    refine (integrable_inv_one_add_sq.const_mul (4 * D * A)).mono'
      (hFc.mul hcont).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    have hl := hA ((c : ℂ) + t * I) (by rw [hre]; exact hc) (by rw [hre])
    have him : ((c : ℂ) + t * I).im = t := by simp
    rw [him] at hl
    have hsq : (1 + |t|) ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_abs t, abs_nonneg t]
    calc ‖F t‖ * ‖logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)‖
        ≤ (2 * D / (1 + t ^ 2) ^ 2) * (A * (2 * (1 + t ^ 2))) :=
          mul_le_mul (hFb2 t) (hl.trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = 4 * D * A * (1 + t ^ 2)⁻¹ := by field_simp; ring
  have hdomF : Integrable (fun t : ℝ => (C + Cn) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hig : Integrable (fun t : ℝ => F t * gPair 0 (c + t * I)) := by
    have hcont : Continuous (fun t : ℝ => gPair 0 ((c : ℂ) + t * I)) := by
      unfold gPair
      refine Continuous.add ?_ ?_
      · refine continuous_const.div (by fun_prop) fun t h => ?_
        have := congrArg Complex.re h; simp at this; linarith
      · refine continuous_const.div (by fun_prop) fun t h => ?_
        have := congrArg Complex.re h; simp at this; linarith
    refine (hdomF.mul_const (1 / c + 1 / (c - 1))).mono'
      (hFc.mul hcont).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    calc ‖F t‖ * ‖gPair 0 ((c : ℂ) + t * I)‖ ≤ ((C + Cn) / (1 + t ^ 2)) * (1 / c + 1 / (c - 1)) :=
          mul_le_mul (hFb t) (WeilAtomic.norm_gPair_zero_le hc1 t) (norm_nonneg _) (by positivity)
      _ = (C + Cn) * (1 + t ^ 2)⁻¹ * (1 / c + 1 / (c - 1)) := by rw [div_eq_mul_inv]
  have hLc : Continuous (fun t : ℝ => LSeries (WeilHerglotz.lamC lam) ((c : ℂ) + t * I)) := by
    have hcont : ∀ n : ℕ, Continuous (fun t : ℝ =>
        LSeries.term (WeilHerglotz.lamC lam) ((c : ℂ) + t * I) n) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simpa [LSeries.term_zero] using continuous_const
      · simp only [LSeries.term_of_ne_zero hn]
        refine continuous_const.div ?_ (fun t => ?_)
        · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn))
        · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
    exact continuous_tsum hcont hsum.norm fun n t => by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]; simp
  set S : ℝ := ∑' n, ‖LSeries.term (WeilHerglotz.lamC lam) c n‖ with hS
  have hiL1 : ∀ {j : ℝ → ℂ} (Cj : ℝ), (∀ t : ℝ, ‖Hfn j (c + t * I)‖ ≤ Cj / (1 + t ^ 2)) →
      Continuous (fun t : ℝ => Hfn j (c + t * I)) →
      Integrable (fun t : ℝ => Hfn j (c + t * I) * LSeries (WeilHerglotz.lamC lam) (c + t * I)) := by
    intro j Cj hb hcj
    refine ((integrable_inv_one_add_sq.const_mul Cj).mul_const S).mono'
      (hcj.mul hLc).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    calc ‖Hfn j (c + t * I)‖ * ‖LSeries (WeilHerglotz.lamC lam) (c + t * I)‖
        ≤ (Cj / (1 + t ^ 2)) * S := mul_le_mul (hb t) (norm_LSeries_line_le hsum t)
          (norm_nonneg _) ((norm_nonneg _).trans (hb t))
      _ = Cj * (1 + t ^ 2)⁻¹ * S := by rw [div_eq_mul_inv]
  have hiLk := hiL1 C (fun t => hC c t hcc) (continuous_Hfn_line hk hkc c)
  have hiLn := hiL1 Cn (fun t => hCn c t hcc) (continuous_Hfn_line hkn2 hknc c)
  have hiL : Integrable (fun t : ℝ => F t * LSeries (WeilHerglotz.lamC lam) (c + t * I)) :=
    (hiLk.add hiLn).congr (Eventually.of_forall fun t => by
      simp only [Pi.add_apply, hF, lineF, hFm]; ring)
  -- the integral splits
  have hsplit : (∫ t : ℝ, F t * WeilHerglotz.weilFunction lam (c + t * I)) =
      (∫ t : ℝ, F t * logDeriv Complex.Gammaℝ (c + t * I)) +
        (∫ t : ℝ, F t * gPair 0 (c + t * I)) -
          ∫ t : ℝ, F t * LSeries (WeilHerglotz.lamC lam) (c + t * I) := by
    have hGg : Integrable (fun t : ℝ => F t * logDeriv Complex.Gammaℝ (c + t * I) +
        F t * gPair 0 (c + t * I)) := hiG.add hig
    rw [← integral_add hiG hig, ← integral_sub hGg hiL]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [weilFunction_eq lam (by rw [hre]; linarith)]
    ring
  -- the pole part
  have hpole : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, F t * gPair 0 (c + t * I)) =
      paperFT k (I / 2) + paperFT k (-I / 2) := by
    have h := two_line_pair (differentiable_Hfn hk hkc) (c := c) (C := C)
      (fun σ t h1 h2 => hC σ t (abs_le.mpr ⟨by linarith, by linarith⟩)) (z₀ := 0)
      (by simp; linarith) (by simp; linarith)
    rw [sub_zero, Hfn_zero, Hfn_one] at h
    exact h
  -- the prime part
  have hP1 := hasSum_prime_side_line hk hkc hsum
  have hP2 := hasSum_prime_side_line hkn2 hknc hsum
  have hprime : HasSum (fun n : ℕ => ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n)))
      ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F t * LSeries (WeilHerglotz.lamC lam) (c + t * I)) := by
    have hint : (∫ t : ℝ, F t * LSeries (WeilHerglotz.lamC lam) (c + t * I)) =
        (∫ t : ℝ, Hfn k (c + t * I) * LSeries (WeilHerglotz.lamC lam) (c + t * I)) +
          ∫ t : ℝ, Hfn kn (c + t * I) * LSeries (WeilHerglotz.lamC lam) (c + t * I) := by
      rw [← integral_add hiLk hiLn]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hF, lineF, hFm]
      ring
    rw [hint, mul_add]
    refine (hP1.add hP2).congr_fun fun n => ?_
    simp only [hkn, WeilHerglotz.lamC]
    split_ifs with h
    · push_cast; ring
    · simp
  have hG := integral_lineF_mul_logDeriv_Gammaℝ hf hfc hc
  rw [weilFullFunctional, hprime.tsum_eq, hsplit]
  simp only [hF] at hG ⊢
  rw [hG]
  rw [mul_sub, mul_add, hpole]
  ring

end RHTower.WeilLineAnyAbscissa

end
