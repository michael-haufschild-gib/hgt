import GaloisForLFunctions.RHTower.StretchedBoseDefect
import GaloisForLFunctions.RHTower.SincSeparatorContour
import GaloisForLFunctions.HTGeometry.GammaHorizontalRatio
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Stretched Bose kernels: membership forces RH

Let `a > 1`, `f_a(t) = e^{-t^a}` and `D_a(t) = Γ(1/a+1)/t - Σ_{n ≥ 1} f_a(nt)`.

**Theorem** (`riemannHypothesis_of_kernelL2_mem_closure`).  If `f_a` lies in the closed linear span
of the integer dilates `D_a(k·)`, `k ≥ 1`, in `L²(0,∞)`, then RH holds.

**Proof.**  Let `ζ(ρ) = 0` with `1/2 < Re ρ < 1`.  Choose `λ > πa/(a-1)` and the sinc separator `Ψ`
of `SincSeparatorMellin`, normalised by `Ψ(1) = 0`.  The vector `g` with Mellin transform
`conj(Ψ/F_a)` on the critical line lies in `L²`.  Here `F_a(s) = Γ(s/a)/a` decays at rate `π/(2a)`
(`norm_Gamma_ge`), while `Ψ` decays at rate `π/2 - π²/(2λ) > π/(2a)`.  Parseval gives
`⟨g, D_a(k·)⟩ = -(1/2π) ∫ ζΨ k^{-s} = 0` and `⟨g, f_a⟩ = (1/2π) ∫ Ψ = 1`
(`integral_zeta_mul_sepMellin_half`, `integral_sepMellin_half`).  So `g` is orthogonal to the span
but not to `f_a`.

The rate condition `π/(2a) < π/2` is exactly `a > 1`.  For `a ≤ 1` no separator of this shape is
square integrable, and for `a = 1` the dilates are complete (`boseDilateL2_span_dense`).
-/

open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate InnerProductSpace

noncomputable section

namespace RHTower.StretchedBose

open GaloisForLFunctions.HTGeometry
open RHTower.SincSeparator

/-- `|Γ(x + ib)| ≥ Γ(x) e^{-(π/2)|b|} / (1 + |b|/x)` for `x > 0`. -/
theorem norm_Gamma_ge {x : ℝ} (hx0 : 0 < x) (b : ℝ) :
    Real.Gamma x * Real.exp (-(Real.pi / 2 * |b|)) / (1 + |b| / x) ≤
      ‖Complex.Gamma ((x : ℂ) + (b : ℂ) * I)‖ := by
  have h := HTGeometry.Gamma_le_norm_Gamma_mul_exp hx0 b
  have hq : 0 ≤ |b| / x := by positivity
  have hlog : Real.log (1 + b ^ 2 / x ^ 2) ≤ 2 * Real.log (1 + |b| / x) := by
    rw [← Real.log_rpow (by positivity)]
    refine Real.log_le_log (by positivity) ?_
    rw [show (1 + |b| / x) ^ (2 : ℝ) = (1 + |b| / x) ^ (2 : ℕ) by norm_cast,
      show b ^ 2 / x ^ 2 = (|b| / x) ^ 2 by rw [div_pow, sq_abs]]
    nlinarith
  have hlog0 : 0 ≤ Real.log (1 + b ^ 2 / x ^ 2) := Real.log_nonneg (by
    have : 0 ≤ b ^ 2 / x ^ 2 := by positivity
    linarith)
  have hR : HTGeometry.gammaRatioBound x b ≤ Real.log (1 + |b| / x) + Real.pi / 2 * |b| := by
    unfold HTGeometry.gammaRatioBound
    have h1 : (1 - x) / 2 * Real.log (1 + b ^ 2 / x ^ 2) ≤ Real.log (1 + |b| / x) := by
      have : (1 - x) / 2 ≤ 1 / 2 := by linarith
      have hl1 : 0 ≤ Real.log (1 + |b| / x) := Real.log_nonneg (by linarith)
      nlinarith
    have h2 : |b| * Real.arctan (|b| / x) ≤ Real.pi / 2 * |b| := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.arctan_lt_pi_div_two _).le (abs_nonneg b)
    linarith
  have hE : Real.exp (HTGeometry.gammaRatioBound x b) ≤
      (1 + |b| / x) * Real.exp (Real.pi / 2 * |b|) := by
    calc Real.exp (HTGeometry.gammaRatioBound x b)
        ≤ Real.exp (Real.log (1 + |b| / x) + Real.pi / 2 * |b|) := Real.exp_le_exp.mpr hR
      _ = (1 + |b| / x) * Real.exp (Real.pi / 2 * |b|) := by
          rw [Real.exp_add, Real.exp_log (by positivity)]
  have hpos : 0 < 1 + |b| / x := by positivity
  rw [div_le_iff₀ hpos]
  calc Real.Gamma x * Real.exp (-(Real.pi / 2 * |b|))
      ≤ ‖Complex.Gamma ((x : ℂ) + (b : ℂ) * I)‖ * Real.exp (HTGeometry.gammaRatioBound x b) *
          Real.exp (-(Real.pi / 2 * |b|)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ ≤ ‖Complex.Gamma ((x : ℂ) + (b : ℂ) * I)‖ * ((1 + |b| / x) * Real.exp (Real.pi / 2 * |b|)) *
          Real.exp (-(Real.pi / 2 * |b|)) := by gcongr
    _ = ‖Complex.Gamma ((x : ℂ) + (b : ℂ) * I)‖ * (1 + |b| / x) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add]; simp

theorem mellinLinePoint_div (a ξ : ℝ) (ha : a ≠ 0) :
    mellinLinePoint ξ / (a : ℂ) = ((1 / (2 * a) : ℝ) : ℂ) + ((-(2 * Real.pi * ξ) / a : ℝ) : ℂ) * I := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [mellinLinePoint, div_eq_iff ha']
  push_cast
  field_simp
  ring

/-- `|F_a(s(ξ))| ≥ c e^{-(π/(2a))|t|}/(1 + 2|t|)` with `t = -2πξ`. -/
theorem norm_mellinFactor_ge {a : ℝ} (ha0 : 0 < a) (ξ : ℝ) :
    Real.Gamma (1 / (2 * a)) / a * Real.exp (-(Real.pi / (2 * a) * |2 * Real.pi * ξ|)) /
        (1 + 2 * |2 * Real.pi * ξ|) ≤ ‖mellinFactor a (mellinLinePoint ξ)‖ := by
  set x : ℝ := 1 / (2 * a) with hx
  set b : ℝ := -(2 * Real.pi * ξ) / a with hb
  have hx0 : 0 < x := by positivity
  have hG := norm_Gamma_ge hx0 b
  have hbabs : |b| = |2 * Real.pi * ξ| / a := by rw [hb, abs_div, abs_neg, abs_of_pos ha0]
  have hbx : |b| / x = 2 * |2 * Real.pi * ξ| := by rw [hbabs, hx]; field_simp
  have hexp : Real.pi / 2 * |b| = Real.pi / (2 * a) * |2 * Real.pi * ξ| := by
    rw [hbabs]; field_simp
  rw [hbx, hexp] at hG
  unfold mellinFactor
  rw [mellinLinePoint_div a ξ ha0.ne', norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha0]
  calc Real.Gamma x / a * Real.exp (-(Real.pi / (2 * a) * |2 * Real.pi * ξ|)) /
        (1 + 2 * |2 * Real.pi * ξ|)
      = (Real.Gamma x * Real.exp (-(Real.pi / (2 * a) * |2 * Real.pi * ξ|)) /
          (1 + 2 * |2 * Real.pi * ξ|)) / a := by ring
    _ ≤ ‖Complex.Gamma ((x : ℂ) + (b : ℂ) * I)‖ / a := by gcongr

/-! ## The separator vector -/

/-- The separator in Mellin coordinates: `ξ ↦ conj(Ψ(s(ξ)) / F_a(s(ξ)))`. -/
def separatorMellin (a lam : ℝ) (ρ c : ℂ) (ξ : ℝ) : ℂ :=
  conj (sepMellin lam ρ c (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ))

theorem mellinLinePoint_im (ξ : ℝ) : (mellinLinePoint ξ).im = -(2 * Real.pi * ξ) := by
  simp [mellinLinePoint]

theorem mellinFactor_ne_zero {a : ℝ} (ha0 : 0 < a) (ξ : ℝ) :
    mellinFactor a (mellinLinePoint ξ) ≠ 0 := by
  unfold mellinFactor
  refine div_ne_zero (Complex.Gamma_ne_zero_of_re_pos ?_) (by exact_mod_cast ha0.ne')
  rw [Complex.div_ofReal_re, mellinLinePoint_re]; positivity

theorem continuous_separatorMellin {a lam : ℝ} (ha0 : 0 < a) (hlam : 0 < lam) {ρ : ℂ}
    (hρ1 : 1 / 2 < ρ.re) (hρ2 : ρ.re < 1) (c : ℂ) : Continuous (separatorMellin a lam ρ c) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  have hΨ : ContinuousAt (sepMellin lam ρ c) (mellinLinePoint ξ) :=
    continuousAt_sepMellin hlam (by rw [mellinLinePoint_re]; norm_num)
      (by rw [mellinLinePoint_re]; linarith) (by
        intro h; have := congrArg Complex.re h; rw [mellinLinePoint_re] at this; linarith)
  have hF : ContinuousAt (mellinFactor a) (mellinLinePoint ξ) :=
    (analyticAt_mellinFactor ha0 (by rw [mellinLinePoint_re]; norm_num)).continuousAt
  have hc := continuous_mellinLinePoint.continuousAt (x := ξ)
  unfold separatorMellin
  exact (Complex.continuous_conj.continuousAt).comp
    ((hΨ.comp hc).div (hF.comp hc) (mellinFactor_ne_zero ha0 ξ))

/-- The rate condition: for `λ = πa/(a-1) + π`, `π/2 - π²/(2λ) - π/(2a) > 0`. -/
theorem separator_rate_pos {a : ℝ} (ha : 1 < a) :
    0 < Real.pi / 2 - Real.pi ^ 2 / (2 * (Real.pi * a / (a - 1) + Real.pi)) - Real.pi / (2 * a) := by
  have ha1 : 0 < a - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hπ := Real.pi_pos
  have hL : 0 < Real.pi * a / (a - 1) + Real.pi := by positivity
  have h2 : 0 < 2 * a - 1 := by linarith
  have key : Real.pi ^ 2 / (2 * (Real.pi * a / (a - 1) + Real.pi)) =
      Real.pi * (a - 1) / (2 * (2 * a - 1)) := by
    rw [show Real.pi * a / (a - 1) + Real.pi = Real.pi * (2 * a - 1) / (a - 1) by
      field_simp; ring]
    field_simp
  rw [key]
  rw [show Real.pi / 2 - Real.pi * (a - 1) / (2 * (2 * a - 1)) - Real.pi / (2 * a) =
    Real.pi * (a - 1) ^ 2 / (2 * a * (2 * a - 1)) by field_simp; ring]
  positivity

/-- **Division by `F_a` stays square integrable** when the numerator decays faster than `F_a`.
If `ξ ↦ conj(Ψ(s(ξ))/F_a(s(ξ)))` is continuous and `|Ψ(1/2 + it)| ≤ K |t|^N e^{-δ|t|}` for
`|t| ≥ T₀ ≥ 1` with `δ > π/(2a)`, then it is bounded by `B (1 + ξ²)⁻¹`. -/
theorem exists_norm_conj_div_mellinFactor_le {a : ℝ} (ha0 : 0 < a) {Ψ : ℂ → ℂ} {δ : ℝ}
    (hrate : 0 < δ - Real.pi / (2 * a))
    (hcont : Continuous fun ξ : ℝ => conj (Ψ (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ)))
    {K T₀ : ℝ} {N : ℕ} (hT₀ : 1 ≤ T₀)
    (hK : ∀ s : ℂ, s.re = 1 / 2 → T₀ ≤ |s.im| → ‖Ψ s‖ ≤ K * |s.im| ^ N * Real.exp (-(δ * |s.im|))) :
    ∃ B : ℝ, ∀ ξ : ℝ, ‖conj (Ψ (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ))‖ ≤
      B * (1 + ξ ^ 2)⁻¹ := by
  set δ' : ℝ := δ - Real.pi / (2 * a) with hδ'
  obtain ⟨M, hM⟩ := exists_pow_mul_exp_neg_le hrate (N + 1)
  set Γx : ℝ := Real.Gamma (1 / (2 * a)) with hΓx
  have hΓx0 : 0 < Γx := Real.Gamma_pos_of_pos (by positivity)
  set R : ℝ := T₀ / (2 * Real.pi) with hR
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max (B₀ * (1 + R ^ 2)) (3 * |K| * a / Γx * M), fun ξ => ?_⟩
  set t : ℝ := 2 * Real.pi * ξ with ht
  have habs_im : |(mellinLinePoint ξ).im| = |t| := by rw [mellinLinePoint_im, abs_neg]
  have hpos : 0 < 1 + ξ ^ 2 := by positivity
  rcases le_or_gt T₀ |t| with hbig | hsmall
  · have ht1 : 1 ≤ |t| := hT₀.trans hbig
    have hΨ := hK (mellinLinePoint ξ) (mellinLinePoint_re ξ) (by rw [habs_im]; exact hbig)
    rw [habs_im] at hΨ
    have hF := norm_mellinFactor_ge ha0 ξ
    rw [← ht] at hF
    have hFpos : 0 < Γx / a * Real.exp (-(Real.pi / (2 * a) * |t|)) / (1 + 2 * |t|) := by
      positivity
    have hG : ‖conj (Ψ (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ))‖ ≤
        (|K| * |t| ^ N * Real.exp (-(δ * |t|))) /
          (Γx / a * Real.exp (-(Real.pi / (2 * a) * |t|)) / (1 + 2 * |t|)) := by
      rw [Complex.norm_conj, norm_div]
      refine div_le_div₀ (by positivity) (hΨ.trans ?_) hFpos hF
      gcongr; exact le_abs_self K
    have hsimp : (|K| * |t| ^ N * Real.exp (-(δ * |t|))) /
          (Γx / a * Real.exp (-(Real.pi / (2 * a) * |t|)) / (1 + 2 * |t|)) =
        |K| * a / Γx * ((1 + 2 * |t|) * |t| ^ N * Real.exp (-(δ' * |t|))) := by
      have he : Real.exp (-(δ * |t|)) =
          Real.exp (-(δ' * |t|)) * Real.exp (-(Real.pi / (2 * a) * |t|)) := by
        rw [← Real.exp_add, hδ']; ring_nf
      rw [he]
      field_simp
    rw [hsimp] at hG
    have h3 : (1 + 2 * |t|) * |t| ^ N ≤ 3 * |t| ^ (N + 1) := by
      rw [pow_succ]; nlinarith [pow_nonneg (abs_nonneg t) N]
    have hξ : (1 + t ^ 2)⁻¹ ≤ (1 + ξ ^ 2)⁻¹ := by
      have hπ2 : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      rw [inv_le_inv₀ (by positivity) hpos, ht, mul_pow, mul_pow]
      nlinarith [mul_nonneg (sq_nonneg ξ) (sub_nonneg.mpr hπ2)]
    have hM0 : 0 ≤ M := by
      have h0 : 0 < |(1 : ℝ)| ^ (N + 1) * Real.exp (-(δ' * |(1 : ℝ)|)) := by positivity
      have h1 : 0 < (1 + (1 : ℝ) ^ 2)⁻¹ := by positivity
      have h2 := lt_of_lt_of_le h0 (hM 1 (by norm_num))
      by_contra hneg
      push Not at hneg
      have := mul_nonpos_of_nonpos_of_nonneg hneg.le h1.le
      linarith
    calc ‖conj (Ψ (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ))‖
        ≤ |K| * a / Γx * ((1 + 2 * |t|) * |t| ^ N * Real.exp (-(δ' * |t|))) := hG
      _ ≤ |K| * a / Γx * (3 * (|t| ^ (N + 1) * Real.exp (-(δ' * |t|)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ ≤ |K| * a / Γx * (3 * (M * (1 + t ^ 2)⁻¹)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM t ht1) (by norm_num))
            (by positivity)
      _ ≤ |K| * a / Γx * (3 * (M * (1 + ξ ^ 2)⁻¹)) := by gcongr
      _ = 3 * |K| * a / Γx * M * (1 + ξ ^ 2)⁻¹ := by ring
      _ ≤ max (B₀ * (1 + R ^ 2)) (3 * |K| * a / Γx * M) * (1 + ξ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hξR : ξ ∈ Icc (-R) R := by
      have hπ : 0 < 2 * Real.pi := by positivity
      have : |ξ| ≤ R := by
        rw [hR, le_div_iff₀ hπ]
        have : |t| = 2 * Real.pi * |ξ| := by rw [ht, abs_mul, abs_of_pos hπ]
        linarith
      exact ⟨by linarith [neg_abs_le ξ], by linarith [le_abs_self ξ]⟩
    have hB := hB₀ ξ hξR
    have hB0 : 0 ≤ B₀ := (norm_nonneg _).trans hB
    have hξ2 : ξ ^ 2 ≤ R ^ 2 := by
      have := abs_le.mpr ⟨hξR.1, hξR.2⟩
      nlinarith [sq_abs ξ, abs_nonneg ξ]
    calc ‖conj (Ψ (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ))‖ ≤ B₀ := hB
      _ ≤ B₀ * (1 + R ^ 2) * (1 + ξ ^ 2)⁻¹ := by
          rw [mul_assoc, ← div_eq_mul_inv]
          refine le_mul_of_one_le_right hB0 ?_
          rw [one_le_div hpos]; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

theorem memLp_conj_div_mellinFactor {a : ℝ} (ha0 : 0 < a) {Ψ : ℂ → ℂ} {δ : ℝ}
    (hrate : 0 < δ - Real.pi / (2 * a))
    (hcont : Continuous fun ξ : ℝ => conj (Ψ (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ)))
    {K T₀ : ℝ} {N : ℕ} (hT₀ : 1 ≤ T₀)
    (hK : ∀ s : ℂ, s.re = 1 / 2 → T₀ ≤ |s.im| → ‖Ψ s‖ ≤ K * |s.im| ^ N * Real.exp (-(δ * |s.im|))) :
    MemLp (fun ξ : ℝ => conj (Ψ (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ))) 2 volume := by
  obtain ⟨B, hB⟩ := exists_norm_conj_div_mellinFactor_le ha0 hrate hcont hT₀ hK
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine (integrable_inv_one_add_sq.const_mul (B ^ 2)).mono'
    (hcont.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  have hpos : 0 < 1 + ξ ^ 2 := by positivity
  have hinv1 : (1 + ξ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ξ])
  have hn := hB ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖conj (Ψ (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ))‖ ^ 2 ≤
        (B * (1 + ξ ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = B ^ 2 * (1 + ξ ^ 2)⁻¹ * (1 + ξ ^ 2)⁻¹ := by ring
    _ ≤ B ^ 2 * (1 + ξ ^ 2)⁻¹ * 1 := mul_le_mul_of_nonneg_left hinv1 (by positivity)
    _ = B ^ 2 * (1 + ξ ^ 2)⁻¹ := by ring

theorem memLp_separatorMellin {a lam : ℝ} (ha0 : 0 < a) (hlam : Real.pi < lam)
    (hrate : 0 < Real.pi / 2 - Real.pi ^ 2 / (2 * lam) - Real.pi / (2 * a)) {ρ : ℂ}
    (hρ1 : 1 / 2 < ρ.re) (hρ2 : ρ.re < 1) (c : ℂ) : MemLp (separatorMellin a lam ρ c) 2 volume := by
  have hl : 0 < lam := Real.pi_pos.trans hlam
  obtain ⟨K, N, hK⟩ := exists_norm_sepMellin_le hl ρ c (1 / 2) (1 / 2)
  exact memLp_conj_div_mellinFactor ha0 hrate (continuous_separatorMellin ha0 hl hρ1 hρ2 c)
    (by linarith [abs_nonneg ρ.im] : (1 : ℝ) ≤ |ρ.im| + 2)
    (fun s hs ht => hK s hs.ge hs.le ht)

/-! ## Pairings -/

/-- `∫ h(s(ξ)) dξ = (2π)⁻¹ ∫ h(1/2 + it) dt`. -/
theorem integral_comp_mellinLinePoint (h : ℂ → ℂ) :
    ∫ ξ : ℝ, h (mellinLinePoint ξ) = ((2 * Real.pi)⁻¹ : ℝ) • ∫ t : ℝ, h (1 / 2 + t * I) := by
  have hc := Measure.integral_comp_mul_left (fun y : ℝ => h (1 / 2 + y * I)) (-(2 * Real.pi))
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hπ)] at hc
  rw [← hc]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [mellinLinePoint_eq]
  congr 1
  push_cast
  ring

/-- Pairing a vector with a known Mellin image against the separator. -/
theorem inner_separator_eq {u : HalfLineL2} {G : ℝ → ℂ} (hG : MemLp G 2 volume) {v : HalfLineL2}
    {φ : ℝ → ℂ} (hv : (halfLineMellinUnitary v : ℝ → ℂ) =ᵐ[volume] φ)
    (hu : u = halfLineMellinUnitary.symm (hG.toLp G)) :
    ⟪u, v⟫_ℂ = ∫ ξ, conj (G ξ) * φ ξ := by
  have hin : ∀ x y : ℂ, ⟪x, y⟫_ℂ = conj x * y := fun x y => by simp [mul_comm]
  rw [← halfLineMellinUnitary.inner_map_map, hu, LinearIsometryEquiv.apply_symm_apply,
    MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hv, MemLp.coeFn_toLp hG] with ξ h1 h2
  rw [hin, h1, h2]

theorem conj_separatorMellin_mul {a lam : ℝ} (ha0 : 0 < a) (ρ c : ℂ) (ξ : ℝ) (z : ℂ) :
    conj (separatorMellin a lam ρ c ξ) * (mellinFactor a (mellinLinePoint ξ) * z) =
      sepMellin lam ρ c (mellinLinePoint ξ) * z := by
  unfold separatorMellin
  rw [Complex.conj_conj]
  have hF := mellinFactor_ne_zero ha0 ξ
  field_simp

/-- **The separator vector.** -/
def separatorL2 {a lam : ℝ} (ha0 : 0 < a) (hlam : Real.pi < lam)
    (hrate : 0 < Real.pi / 2 - Real.pi ^ 2 / (2 * lam) - Real.pi / (2 * a)) {ρ : ℂ}
    (hρ1 : 1 / 2 < ρ.re) (hρ2 : ρ.re < 1) (c : ℂ) : HalfLineL2 :=
  halfLineMellinUnitary.symm ((memLp_separatorMellin ha0 hlam hrate hρ1 hρ2 c).toLp _)

theorem inner_separatorL2_kernelL2 {a lam : ℝ} (ha0 : 0 < a) (hlam : Real.pi < lam)
    (hrate : 0 < Real.pi / 2 - Real.pi ^ 2 / (2 * lam) - Real.pi / (2 * a)) {ρ : ℂ}
    (hρ1 : 1 / 2 < ρ.re) (hρ2 : ρ.re < 1) (c : ℂ) :
    ⟪separatorL2 ha0 hlam hrate hρ1 hρ2 c, kernelL2 ha0⟫_ℂ = 1 := by
  rw [inner_separator_eq (u := separatorL2 ha0 hlam hrate hρ1 hρ2 c)
    (memLp_separatorMellin ha0 hlam hrate hρ1 hρ2 c) (halfLineMellinUnitary_kernelL2 ha0) rfl]
  have hpt : ∀ ξ : ℝ, conj (separatorMellin a lam ρ c ξ) * mellinFactor a (mellinLinePoint ξ) =
      sepMellin lam ρ c (mellinLinePoint ξ) := fun ξ => by
    simpa using conj_separatorMellin_mul (lam := lam) ha0 ρ c ξ 1
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_comp_mellinLinePoint (sepMellin lam ρ c),
    integral_sepMellin_half hlam hρ1 hρ2 c, Complex.real_smul]
  push_cast
  field_simp

theorem inner_separatorL2_defectDilateL2 {a lam : ℝ} (ha0 : 0 < a) (hlam : Real.pi < lam)
    (hrate : 0 < Real.pi / 2 - Real.pi ^ 2 / (2 * lam) - Real.pi / (2 * a)) {ρ : ℂ}
    (hρ1 : 1 / 2 < ρ.re) (hρ2 : ρ.re < 1) (hζ : riemannZeta ρ = 0) {c : ℂ}
    (hc : sepMellin lam ρ c 1 = 0) (k : ℕ) :
    ⟪separatorL2 ha0 hlam hrate hρ1 hρ2 c, defectDilateL2 ha0 k⟫_ℂ = 0 := by
  rw [inner_separator_eq (u := separatorL2 ha0 hlam hrate hρ1 hρ2 c)
    (memLp_separatorMellin ha0 hlam hrate hρ1 hρ2 c) (halfLineMellinUnitary_defectDilateL2 ha0 k) rfl]
  have hpt : ∀ ξ : ℝ, conj (separatorMellin a lam ρ c ξ) *
      -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * mellinFactor a (mellinLinePoint ξ) *
        riemannZeta (mellinLinePoint ξ)) =
      -(riemannZeta (mellinLinePoint ξ) * sepMellin lam ρ c (mellinLinePoint ξ) *
        ((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ)) := fun ξ => by
    have h := conj_separatorMellin_mul (lam := lam) ha0 ρ c ξ
      (-(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)))
    rw [show mellinFactor a (mellinLinePoint ξ) *
        -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) =
        -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * mellinFactor a (mellinLinePoint ξ) *
          riemannZeta (mellinLinePoint ξ)) by ring] at h
    rw [h]; ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_neg,
    integral_comp_mellinLinePoint (fun s => riemannZeta s * sepMellin lam ρ c s *
      ((k + 1 : ℕ) : ℂ) ^ (-s)),
    integral_zeta_mul_sepMellin_half hlam hρ1 hρ2 hζ hc (Nat.le_add_left 1 k)]
  simp

/-! ## The main theorem -/

/-- **An off-line zero separates `f_a` from the integer dilates of `D_a`** (`a > 1`). -/
theorem kernelL2_not_mem_closure_of_offLine_zero {a : ℝ} (ha : 1 < a) {ρ : ℂ}
    (hρ1 : 1 / 2 < ρ.re) (hρ2 : ρ.re < 1) (hζ : riemannZeta ρ = 0) :
    kernelL2 (a := a) (by linarith) ∉
      (Submodule.span ℂ (Set.range (defectDilateL2 (a := a) (by linarith)))).topologicalClosure := by
  have ha0 : 0 < a := by linarith
  set lam : ℝ := Real.pi * a / (a - 1) + Real.pi with hlamdef
  have hlam : Real.pi < lam := by
    have : 0 < Real.pi * a / (a - 1) := by
      have : 0 < a - 1 := by linarith
      positivity
    linarith
  have hrate := separator_rate_pos ha
  rw [← hlamdef] at hrate
  have hl : 0 < lam := Real.pi_pos.trans hlam
  have hρ1' : (1 : ℂ) - ρ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  set c : ℂ := -(polarNum lam ρ 1 / (1 - ρ)) / sinMellin lam 1 with hcdef
  have hc : sepMellin lam ρ c 1 = 0 := by
    unfold sepMellin
    rw [hcdef]
    field_simp [sinMellin_one_ne_zero hl]
    ring
  set g := separatorL2 ha0 hlam hrate hρ1 hρ2 c with hg
  set K := Submodule.span ℂ (Set.range (defectDilateL2 (a := a) ha0)) with hK
  have hgK : g ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ⟪u, g⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨k, rfl⟩
      rw [inner_eq_zero_symm]
      exact inner_separatorL2_defectDilateL2 ha0 hlam hrate hρ1 hρ2 hζ hc k
    · exact inner_zero_left _
    · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
    · intro r x _ hx; rw [inner_smul_left, hx, mul_zero]
  intro hmem
  have hclos : K.topologicalClosure ≤ Kᗮᗮ :=
    K.topologicalClosure_minimal K.le_orthogonal_orthogonal Kᗮ.isClosed_orthogonal
  have h1 := (Submodule.mem_orthogonal _ _).mp (hclos hmem) g hgK
  rw [inner_separatorL2_kernelL2 ha0 hlam hrate hρ1 hρ2 c] at h1
  exact one_ne_zero h1

/-- **Membership forces RH.**  For `a > 1`, if `e^{-t^a}` lies in the closed span of the integer
dilates of the stretched Bose defect `D_a`, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_kernelL2_mem_closure {a : ℝ} (ha : 1 < a)
    (hmem : kernelL2 (a := a) (by linarith) ∈
      (Submodule.span ℂ (Set.range (defectDilateL2 (a := a) (by linarith)))).topologicalClosure) :
    RiemannHypothesis := by
  rw [RHTower.rh_iff_xi_ne_zero_right]
  intro s hs hxi
  have hs1 : 1 / 2 < s.re := hs
  have hsne : s ≠ 1 := by
    rintro rfl
    rw [RHTower.xi_one] at hxi
    norm_num at hxi
  have hz : riemannZeta s = 0 := (RHTower.xi_eq_zero_iff (by linarith) hsne).mp hxi
  by_cases hs2 : s.re < 1
  · exact kernelL2_not_mem_closure_of_offLine_zero ha hs1 hs2 hz hmem
  · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hs2) hz

end RHTower.StretchedBose
