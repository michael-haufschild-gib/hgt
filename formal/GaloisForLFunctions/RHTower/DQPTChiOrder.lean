import GaloisForLFunctions.RHTower.GammaVerticalRatioAsymptotic
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# DQPT: the order of the functional-equation factor `χ(s)` in the critical strip

**Supplementary Note 7** of arXiv:2511.11199 (published Supplementary Note 7):
for `s = β + it` with `0 < β < 1`,

`χ(s) = 2^s π^{s−1} sin(πs/2) Γ(1−s)`,   `|χ(s)| = Θ(|t|^{1/2−β})`.

The paper computes the two ingredients `|sin(πs/2)| = Θ(e^{π|t|/2})` and, via Stirling in a
sector, `|Γ(1−s)| = √(2π)|1−s|^{1/2−β} e^{−π|t|/2}(1 + O(|t|^{-1}))`.

Here the exponential factors are handled exactly instead of asymptotically:
`‖sin(π s/2)‖² = sin²(πβ/2) + sinh²(πt/2)` is an identity, `‖Γ(1/2 + it)‖² = π/cosh(πt)` is an
identity (`HTGeometry.norm_Gamma_half_add_I_sq`), and the remaining ratio
`‖Γ((1−β)+it)‖/‖Γ(1/2+it)‖` is pinned by the corpus's vertical Gamma-ratio law
(`RHTower.gamma_vertical_ratio_norm_rpow_tendsto`).  This gives the **sharp** constant:

`|χ(β+it)| · (t/2π)^{β−1/2} → 1`,

which implies the paper's `Θ(|t|^{1/2−β})`.

Main results:
* `dqpt_norm_sin_sq_eq` — `‖sin(x + iy)‖² = sin²x + sinh²y`;
* `dqpt_norm_dqptChi` — **Supplementary Note 7 (7.2)**;
* `dqpt_norm_sin_pi_half_sq` — **Supplementary Note 7 (7.4)**;
* `dqpt_gamma_ratio_tendsto` — the two-sided vertical Gamma-ratio law;
* `dqpt_norm_chi_tendsto` — **the sharp form of Supplementary Note 7 (7.14)**;
* `dqpt_norm_chi_isTheta` — the paper's `Θ(|t|^{1/2−β})`.
-/

namespace RHTower.DQPT

open Complex Filter Topology Set

noncomputable section

/-! ## The modulus of the complex sine -/

theorem dqpt_norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simp only [Complex.norm_def, Complex.normSq_apply]
  rw [Real.sq_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
  ring

/-- `‖sin(x + iy)‖² = sin²x + sinh²y`. -/
theorem dqpt_norm_sin_sq_eq (x y : ℝ) :
    ‖Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2
      = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  have hsin : Complex.sin ((x : ℂ) + (y : ℂ) * Complex.I)
      = ((Real.sin x * Real.cosh y : ℝ) : ℂ)
        + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast
    ring
  rw [hsin, dqpt_norm_sq_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hpyth := Real.sin_sq_add_cos_sq x
  have hcosh := Real.cosh_sq' y
  nlinarith [hpyth, hcosh]

/-- **Supplementary Note 7 (7.4).**  `‖sin(πs/2)‖² = sin²(πβ/2) + sinh²(πt/2)`. -/
theorem dqpt_norm_sin_pi_half_sq (β t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * (((β : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) / 2)‖ ^ 2
      = Real.sin (Real.pi * β / 2) ^ 2 + Real.sinh (Real.pi * t / 2) ^ 2 := by
  have harg : (Real.pi : ℂ) * (((β : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) / 2
      = ((Real.pi * β / 2 : ℝ) : ℂ) + ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, dqpt_norm_sin_sq_eq]

/-! ## The paper's functional-equation factor -/

/-- `χ(s) = 2^s π^{s−1} sin(πs/2) Γ(1−s)`. -/
def dqptChi (s : ℂ) : ℂ :=
  (2 : ℂ) ^ s * ((Real.pi : ℝ) : ℂ) ^ (s - 1) * Complex.sin ((Real.pi : ℂ) * s / 2)
    * Complex.Gamma (1 - s)

/-- **Supplementary Note 7 (7.2).** -/
theorem dqpt_norm_dqptChi (s : ℂ) :
    ‖dqptChi s‖ = (2 : ℝ) ^ s.re * Real.pi ^ (s.re - 1)
      * ‖Complex.sin ((Real.pi : ℂ) * s / 2)‖ * ‖Complex.Gamma (1 - s)‖ := by
  have hb : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have h2 : ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ s.re := by
    rw [← hb, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpi : ‖((Real.pi : ℝ) : ℂ) ^ (s - 1)‖ = Real.pi ^ (s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.sub_re, Complex.one_re]
  rw [dqptChi, norm_mul, norm_mul, norm_mul, h2, hpi]

/-! ## The two-sided vertical Gamma-ratio law -/

theorem dqpt_norm_Gamma_line_pos {a τ : ℝ} (hτ : 0 < τ) :
    0 < ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖ :=
  norm_pos_iff.mpr (gammaArg_Gamma_ne_zero hτ a)

theorem dqpt_gamma_ratio_tendsto_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun τ : ℝ =>
        ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
          / ‖Complex.Gamma ((b : ℂ) + (τ : ℂ) * Complex.I)‖ * τ ^ (b - a))
      atTop (𝓝 1) := by
  have hδ : (0 : ℝ) ≤ b - a := by linarith
  have hbase := gamma_vertical_ratio_norm_rpow_tendsto ha hδ
  refine hbase.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  have hcast : ((a + (b - a) : ℝ) : ℂ) = ((b : ℝ) : ℂ) := by
    congr 1
    ring
  have hxpos := dqpt_norm_Gamma_line_pos (a := a) hτ
  have hypos := dqpt_norm_Gamma_line_pos (a := b) hτ
  rw [hcast]
  congr 1
  rw [Real.exp_sub, Real.exp_log hxpos, Real.exp_log hypos]

/-- **The two-sided vertical Gamma-ratio law.**  For `a, b ≥ 0`,
`(‖Γ(a+iτ)‖/‖Γ(b+iτ)‖)·τ^{b−a} → 1`. -/
theorem dqpt_gamma_ratio_tendsto {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun τ : ℝ =>
        ‖Complex.Gamma ((a : ℂ) + (τ : ℂ) * Complex.I)‖
          / ‖Complex.Gamma ((b : ℂ) + (τ : ℂ) * Complex.I)‖ * τ ^ (b - a))
      atTop (𝓝 1) := by
  rcases le_total a b with hab | hba
  · exact dqpt_gamma_ratio_tendsto_of_le ha hab
  · have hswap := dqpt_gamma_ratio_tendsto_of_le hb hba
    have hinv := hswap.inv₀ (by norm_num)
    rw [inv_one] at hinv
    refine hinv.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
    have hxpos := dqpt_norm_Gamma_line_pos (a := a) hτ
    have hypos := dqpt_norm_Gamma_line_pos (a := b) hτ
    have hpow : (τ : ℝ) ^ (b - a) = ((τ : ℝ) ^ (a - b))⁻¹ := by
      rw [← Real.rpow_neg (le_of_lt hτ)]
      congr 1
      ring
    rw [hpow, mul_inv, inv_div]
  
/-! ## The exact modulus on the critical line -/

theorem dqpt_norm_Gamma_half_line (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
      = Real.sqrt (Real.pi / Real.cosh (Real.pi * τ)) := by
  have hcast : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  have hsq := GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_sq τ
  rw [hcast]
  have hnn : (0 : ℝ) ≤ ‖Complex.Gamma ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I)‖ := norm_nonneg _
  rw [← hsq, Real.sqrt_sq hnn]

/-! ## The sharp asymptotic -/

theorem dqpt_sinh_sq_half (τ : ℝ) :
    Real.sinh (Real.pi * τ / 2) ^ 2 = (Real.cosh (Real.pi * τ) - 1) / 2 := by
  have h := Real.cosh_two_mul (Real.pi * τ / 2)
  have hsq := Real.cosh_sq' (Real.pi * τ / 2)
  have harg : 2 * (Real.pi * τ / 2) = Real.pi * τ := by ring
  rw [harg] at h
  linarith

theorem dqpt_tendsto_cosh_atTop :
    Tendsto (fun τ : ℝ => Real.cosh (Real.pi * τ)) atTop atTop := by
  have hlin : Tendsto (fun τ : ℝ => Real.pi * τ) atTop atTop :=
    Filter.Tendsto.const_mul_atTop Real.pi_pos tendsto_id
  have hexp : Tendsto (fun τ : ℝ => Real.exp (Real.pi * τ) / 2) atTop atTop := by
    exact (Real.tendsto_exp_atTop.comp hlin).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono (fun τ => ?_) hexp
  rw [Real.cosh_eq]
  have hpos : (0 : ℝ) < Real.exp (-(Real.pi * τ)) := Real.exp_pos _
  linarith

/-- The exact "sine times critical-line Gamma" factor converges to `√(π/2)`. -/
theorem dqpt_tendsto_sin_mul_Gamma_half {β : ℝ} :
    Tendsto (fun τ : ℝ =>
        ‖Complex.sin ((Real.pi : ℂ) * (((β : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I) / 2)‖
          * ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖)
      atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  have hquot : Tendsto (fun τ : ℝ =>
      Real.pi * (Real.sin (Real.pi * β / 2) ^ 2 + Real.sinh (Real.pi * τ / 2) ^ 2)
        / Real.cosh (Real.pi * τ)) atTop (𝓝 (Real.pi / 2)) := by
    have hrewrite : (fun τ : ℝ =>
        Real.pi * (Real.sin (Real.pi * β / 2) ^ 2 + Real.sinh (Real.pi * τ / 2) ^ 2)
          / Real.cosh (Real.pi * τ))
          =ᶠ[atTop] (fun τ : ℝ => Real.pi / 2
            + Real.pi * (Real.sin (Real.pi * β / 2) ^ 2 - 1 / 2) / Real.cosh (Real.pi * τ)) := by
      filter_upwards with τ
      have hc : Real.cosh (Real.pi * τ) ≠ 0 := ne_of_gt (Real.cosh_pos _)
      rw [dqpt_sinh_sq_half τ]
      field_simp
      ring
    refine Tendsto.congr' hrewrite.symm ?_
    have hz : Tendsto (fun τ : ℝ =>
        Real.pi * (Real.sin (Real.pi * β / 2) ^ 2 - 1 / 2) / Real.cosh (Real.pi * τ))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop dqpt_tendsto_cosh_atTop
    simpa using (tendsto_const_nhds (x := Real.pi / 2)).add hz
  have hsqrt : Tendsto (fun τ : ℝ =>
      Real.sqrt (Real.pi * (Real.sin (Real.pi * β / 2) ^ 2 + Real.sinh (Real.pi * τ / 2) ^ 2)
        / Real.cosh (Real.pi * τ))) atTop (𝓝 (Real.sqrt (Real.pi / 2))) :=
    (Real.continuous_sqrt.tendsto _).comp hquot
  refine hsqrt.congr' ?_
  filter_upwards with τ
  have hs : ‖Complex.sin ((Real.pi : ℂ) * (((β : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I) / 2)‖
      = Real.sqrt (Real.sin (Real.pi * β / 2) ^ 2 + Real.sinh (Real.pi * τ / 2) ^ 2) := by
    have h := dqpt_norm_sin_pi_half_sq β τ
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  rw [hs, dqpt_norm_Gamma_half_line τ, ← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-- The algebraic constant identity `2^β π^{β−1} √(π/2) = (2π)^{β−1/2}`. -/
theorem dqpt_chi_constant (β : ℝ) :
    (2 : ℝ) ^ β * Real.pi ^ (β - 1) * Real.sqrt (Real.pi / 2) = (2 * Real.pi) ^ (β - 1 / 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (Real.pi / 2) = Real.pi ^ ((1 : ℝ) / 2) * (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow (le_of_lt hpi) (by norm_num)]
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg (by norm_num)]
    rw [div_eq_mul_inv]
  rw [hsqrt, Real.mul_rpow (by norm_num) (le_of_lt hpi)]
  rw [show (β - 1 / 2 : ℝ) = β + (-(1 : ℝ) / 2) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show (β + (-(1 : ℝ) / 2) : ℝ) = (β - 1) + (1 : ℝ) / 2 by ring,
    Real.rpow_add hpi]
  ring

/-- **The sharp form of Supplementary Note 7 (7.14).**
`|χ(β+it)| · (t/2π)^{β−1/2} → 1`, i.e. `|χ(β+it)| ~ (t/2π)^{1/2−β}`.
Only `β < 1` is needed; in particular this covers the paper's open strip `0 < β < 1`. -/
theorem dqpt_norm_chi_tendsto {β : ℝ} (hβ1 : β < 1) :
    Tendsto (fun t : ℝ => ‖dqptChi ((β : ℂ) + (t : ℂ) * Complex.I)‖ * t ^ (β - 1 / 2))
      atTop (𝓝 ((2 * Real.pi) ^ (β - 1 / 2))) := by
  have hre : ∀ t : ℝ, ((β : ℂ) + (t : ℂ) * Complex.I).re = β := by
    intro t; simp
  have hconj : ∀ t : ℝ,
      ‖Complex.Gamma (1 - ((β : ℂ) + (t : ℂ) * Complex.I))‖
        = ‖Complex.Gamma ((((1 - β : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ := by
    intro t
    have hz : (1 : ℂ) - ((β : ℂ) + (t : ℂ) * Complex.I)
        = starRingEnd ℂ ((((1 - β : ℝ)) : ℂ) + (t : ℂ) * Complex.I) := by
      simp [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hz, norm_Gamma_conj]
  have hratio := dqpt_gamma_ratio_tendsto (a := 1 - β) (b := 1 / 2)
    (by linarith) (by norm_num)
  have hsin := dqpt_tendsto_sin_mul_Gamma_half (β := β)
  have hprod := hratio.mul hsin
  have hconst : Tendsto (fun _ : ℝ => (2 : ℝ) ^ β * Real.pi ^ (β - 1)) atTop
      (𝓝 ((2 : ℝ) ^ β * Real.pi ^ (β - 1))) := tendsto_const_nhds
  have htotal := hconst.mul hprod
  rw [one_mul] at htotal
  have hlim : (2 : ℝ) ^ β * Real.pi ^ (β - 1) * Real.sqrt (Real.pi / 2)
      = (2 * Real.pi) ^ (β - 1 / 2) := dqpt_chi_constant β
  rw [hlim] at htotal
  refine htotal.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hGpos := dqpt_norm_Gamma_line_pos (a := (1 / 2 : ℝ)) ht
  have hexp : (1 : ℝ) / 2 - (1 - β) = β - 1 / 2 := by ring
  rw [dqpt_norm_dqptChi, hre t, hconj t, hexp]
  field_simp

/-- **Supplementary Note 7 (7.14).**  `|χ(β+it)| = Θ(t^{1/2−β})` as `t → ∞`. -/
theorem dqpt_norm_chi_isTheta {β : ℝ} (hβ1 : β < 1) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ᶠ t : ℝ in atTop,
        c₁ * t ^ (1 / 2 - β) ≤ ‖dqptChi ((β : ℂ) + (t : ℂ) * Complex.I)‖
          ∧ ‖dqptChi ((β : ℂ) + (t : ℂ) * Complex.I)‖ ≤ c₂ * t ^ (1 / 2 - β) := by
  set L : ℝ := (2 * Real.pi) ^ (β - 1 / 2) with hL
  have hLpos : 0 < L := by
    rw [hL]; exact Real.rpow_pos_of_pos (by positivity) _
  have hlim := dqpt_norm_chi_tendsto hβ1
  refine ⟨L / 2, 2 * L, by positivity, by positivity, ?_⟩
  have hnear : ∀ᶠ t : ℝ in atTop,
      L / 2 < ‖dqptChi ((β : ℂ) + (t : ℂ) * Complex.I)‖ * t ^ (β - 1 / 2)
        ∧ ‖dqptChi ((β : ℂ) + (t : ℂ) * Complex.I)‖ * t ^ (β - 1 / 2) < 2 * L := by
    have h1 := hlim.eventually (eventually_gt_nhds (show L / 2 < L by linarith))
    have h2 := hlim.eventually (eventually_lt_nhds (show L < 2 * L by linarith))
    filter_upwards [h1, h2] with t ha hb
    exact ⟨ha, hb⟩
  filter_upwards [hnear, eventually_gt_atTop (0 : ℝ)] with t ht htpos
  have hpow : (0 : ℝ) < t ^ (β - 1 / 2) := Real.rpow_pos_of_pos htpos _
  have hinv : t ^ (1 / 2 - β) = (t ^ (β - 1 / 2))⁻¹ := by
    rw [← Real.rpow_neg (le_of_lt htpos)]
    congr 1
    ring
  constructor
  · rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hpow]
    linarith [ht.1]
  · rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hpow]
    linarith [ht.2]

end

end RHTower.DQPT
