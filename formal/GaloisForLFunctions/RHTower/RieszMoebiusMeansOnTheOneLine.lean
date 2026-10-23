import GaloisForLFunctions.RHTower.InverseZetaRieszPerronShift
import GaloisForLFunctions.RHTower.MoebiusPartialSumBound
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegionBound
import GaloisForLFunctions.RHTower.BarnesMellinRemainder

/-!
# Riesz means of the Möbius series on the `1`-line

The continued reciprocal `I = 1/ζ` (`invZetaCont`, with `I(1) = 0`) is analytic on a neighbourhood
of `Re u ≥ 1` (`differentiableAt_invZetaCont_of_zeroFree`, from the zero-free region
`riemannZeta_ne_zero_of_lt_re`), with polynomially small size and derivative there:
`|I(σ + it)|, |I'(σ + it)| ≤ C (|t| + 3)^{1/32}` for `1 ≤ σ ≤ 9/8`
(`exists_norm_invZetaCont_le_rpow`, `exists_norm_deriv_invZetaCont_le_rpow`).  The derivative bound
is `I' = −(ζ'/ζ) I` with the corpus log-derivative bound at large heights, and compactness below.
Consequently `I` is Lipschitz near the `1`-line (`exists_norm_invZetaCont_sub_le`).
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section
set_option autoImplicit false

/-! ### Analyticity near the `1`-line -/

/-- Off the zeros the residue unit `(u − 1)ζ(u)` does not vanish. -/
theorem zetaResidueUnit_ne_zero_of_zeroFree {u : ℂ} (h0 : 0 < u.re)
    (h : 1 - 1 / 58 / Real.log (|u.im| + 4) < u.re) : zetaResidueUnit u ≠ 0 := by
  by_cases h1 : u = 1
  · rw [h1, zetaResidueUnit_one]; exact one_ne_zero
  rw [(zetaResidueUnit_eventuallyEq h1).eq_of_nhds]
  exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_lt_re h0 h)

theorem differentiableAt_invZetaCont_of_zeroFree {u : ℂ} (h0 : 0 < u.re)
    (h : 1 - 1 / 58 / Real.log (|u.im| + 4) < u.re) : DifferentiableAt ℂ invZetaCont u :=
  (differentiableAt_id.sub_const 1).div (analyticAt_zetaResidueUnit u).differentiableAt
    (zetaResidueUnit_ne_zero_of_zeroFree h0 h)

theorem zeroFree_of_one_le_re {u : ℂ} (h : 1 ≤ u.re) :
    0 < u.re ∧ 1 - 1 / 58 / Real.log (|u.im| + 4) < u.re := by
  have hlog : 0 < Real.log (|u.im| + 4) := Real.log_pos (by linarith [abs_nonneg u.im])
  have : 0 < 1 / 58 / Real.log (|u.im| + 4) := by positivity
  exact ⟨by linarith, by linarith⟩

theorem differentiableAt_invZetaCont_of_one_le_re {u : ℂ} (h : 1 ≤ u.re) :
    DifferentiableAt ℂ invZetaCont u :=
  differentiableAt_invZetaCont_of_zeroFree (zeroFree_of_one_le_re h).1 (zeroFree_of_one_le_re h).2

/-- An open zero-free neighbourhood of the piece `Re u ≥ 1, |Im u| ≤ T` of the closed half-plane. -/
def oneLineNbhd (T : ℝ) : Set ℂ := {u | 1 - 1 / 58 / Real.log (T + 5) < u.re ∧ |u.im| < T + 1}

theorem isOpen_oneLineNbhd (T : ℝ) : IsOpen (oneLineNbhd T) :=
  (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)

theorem differentiableOn_invZetaCont_oneLineNbhd {T : ℝ} (hT : 0 ≤ T) :
    DifferentiableOn ℂ invZetaCont (oneLineNbhd T) := by
  intro u hu
  obtain ⟨h1, h2⟩ := hu
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlT : Real.log 2 ≤ Real.log (T + 5) := Real.log_le_log (by norm_num) (by linarith)
  have hpos' : 0 < Real.log (|u.im| + 4) := Real.log_pos (by linarith [abs_nonneg u.im])
  have hle : Real.log (|u.im| + 4) ≤ Real.log (T + 5) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsmall : 1 / 58 / Real.log (T + 5) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hcmp : 1 / 58 / Real.log (T + 5) ≤ 1 / 58 / Real.log (|u.im| + 4) :=
    div_le_div_of_nonneg_left (by norm_num) hpos' hle
  exact (differentiableAt_invZetaCont_of_zeroFree (by linarith) (by linarith)).differentiableWithinAt

theorem rect_subset_oneLineNbhd {T : ℝ} :
    Icc (1 : ℝ) (9 / 8) ×ℂ Icc (-T) T ⊆ oneLineNbhd T := by
  intro u hu
  rw [Complex.mem_reProdIm] at hu
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hT : 0 ≤ T := by linarith [hu.2.1, hu.2.2]
  have hlT : Real.log 2 ≤ Real.log (T + 5) := Real.log_le_log (by norm_num) (by linarith)
  have : 0 < 1 / 58 / Real.log (T + 5) := by
    have : 0 < Real.log (T + 5) := by linarith
    positivity
  refine ⟨by linarith [hu.1.1], ?_⟩
  rw [abs_lt]
  constructor <;> linarith [hu.2.1, hu.2.2]

theorem convex_reProdIm_Icc (a b c d : ℝ) : Convex ℝ (Icc a b ×ℂ Icc c d) := by
  intro x hx y hy s t hs ht hst
  rw [Complex.mem_reProdIm] at hx hy ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  exact ⟨by simpa [smul_eq_mul] using (convex_Icc a b) hx.1 hy.1 hs ht hst,
    by simpa [smul_eq_mul] using (convex_Icc c d) hx.2 hy.2 hs ht hst⟩

/-! ### Size and derivative near the `1`-line -/

theorem one_le_log_add_exp_one (t : ℝ) : 1 ≤ Real.log (|t| + Real.exp 1) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith [abs_nonneg t]

/-- `|1/ζ(σ + it)| ≤ K log¹¹(|t| + e)` for `1 ≤ σ ≤ 5/4`, the line itself by continuity. -/
theorem exists_norm_invZetaCont_le :
    ∃ K : ℝ, 0 < K ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 5 / 4 →
      ‖invZetaCont ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K * Real.log (|t| + Real.exp 1) ^ 11 := by
  obtain ⟨K, hK, hb⟩ := RHTower.norm_LSeries_moebius_le_uniform
  refine ⟨K, hK, fun σ t h1 h2 => ?_⟩
  rcases h1.lt_or_eq with h | h
  · rw [invZetaCont_eq_LSeries (by simpa using h)]
    exact hb σ t h h2
  · subst h
    have hcont : ContinuousAt (fun σ' : ℝ => invZetaCont ((σ' : ℂ) + (t : ℂ) * I)) 1 :=
      (differentiableAt_invZetaCont_of_one_le_re (by simp)).continuousAt.comp
        (f := fun σ' : ℝ => (σ' : ℂ) + (t : ℂ) * I) (by fun_prop)
    have hlim : Tendsto (fun σ' : ℝ => ‖invZetaCont ((σ' : ℂ) + (t : ℂ) * I)‖) (𝓝[>] 1)
        (𝓝 ‖invZetaCont (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖) :=
      (continuous_norm.tendsto _).comp (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 5 / 4 by norm_num)] with σ' hσ'
    rw [invZetaCont_eq_LSeries (by simpa using hσ'.1)]
    exact hb σ' t hσ'.1 hσ'.2.le

/-- `|I'(σ + it)| ≤ C log¹³(|t| + e)` for `1 ≤ σ ≤ 9/8`: `I' = −(ζ'/ζ) I` at large heights. -/
theorem exists_norm_deriv_invZetaCont_le :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 9 / 8 →
      ‖deriv invZetaCont ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log (|t| + Real.exp 1) ^ 13 := by
  obtain ⟨c', C₀, T, hc', hC₀, hT4, hld⟩ := Sieve.exists_logDeriv_zeta_bound
  obtain ⟨K, hK, hI⟩ := exists_norm_invZetaCont_le
  have hT0 : 0 ≤ T := by linarith
  have hcd : ContinuousOn (deriv invZetaCont) (oneLineNbhd T) :=
    ((differentiableOn_invZetaCont_oneLineNbhd hT0).deriv (isOpen_oneLineNbhd T)).continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn
    (hcd.mono (rect_subset_oneLineNbhd (T := T)))
  refine ⟨max B 0 + C₀ * K + 1, by positivity, fun σ t h1 h2 => ?_⟩
  have hp : 1 ≤ Real.log (|t| + Real.exp 1) ^ 13 := one_le_pow₀ (one_le_log_add_exp_one t)
  have hCpos : 0 ≤ C₀ * K := by positivity
  rcases le_or_gt |t| T with ht | ht
  · have hmem : (σ : ℂ) + (t : ℂ) * I ∈ Icc (1 : ℝ) (9 / 8) ×ℂ Icc (-T) T := by
      rw [Complex.mem_reProdIm]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      exact ⟨⟨h1, h2⟩, abs_le.mp ht⟩
    calc ‖deriv invZetaCont ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B := hB _ hmem
      _ ≤ max B 0 + C₀ * K + 1 := by linarith [le_max_left B 0]
      _ ≤ (max B 0 + C₀ * K + 1) * Real.log (|t| + Real.exp 1) ^ 13 :=
          le_mul_of_one_le_right (by positivity) hp
  · set u : ℂ := (σ : ℂ) + (t : ℂ) * I with hu
    have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht; linarith
    have hu1 : u ≠ 1 := fun h => by
      have := congrArg Complex.im h; simp [hu] at this; exact ht0 this
    have hz : riemannZeta u ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp [hu]; linarith)
    have heq : invZetaCont =ᶠ[𝓝 u] fun v => (riemannZeta v)⁻¹ :=
      (eventually_ne_nhds hu1).mono fun v hv => invZetaCont_eq hv
    have hderiv : deriv invZetaCont u = -deriv riemannZeta u / riemannZeta u ^ 2 := by
      rw [heq.deriv_eq]
      exact ((differentiableAt_riemannZeta hu1).hasDerivAt.inv hz).deriv
    have hnorm : ‖deriv invZetaCont u‖ = ‖logDeriv riemannZeta u‖ * ‖invZetaCont u‖ := by
      rw [hderiv, logDeriv_apply, invZetaCont_eq hu1, norm_div, norm_neg, norm_pow, norm_div,
        norm_inv]
      have hz' : ‖riemannZeta u‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      field_simp
    have hlogt : 0 < Real.log |t| := Real.log_pos (by linarith)
    have hl := hld σ t ht.le (by have : 0 < c' / Real.log |t| := by positivity
                                 linarith) h2
    have hi := hI σ t h1 (by linarith)
    have hlog_le : Real.log |t| ≤ Real.log (|t| + Real.exp 1) :=
      Real.log_le_log (by linarith) (by linarith [Real.exp_pos 1])
    have hsq : Real.log |t| ^ 2 ≤ Real.log (|t| + Real.exp 1) ^ 2 :=
      pow_le_pow_left₀ hlogt.le hlog_le 2
    calc ‖deriv invZetaCont u‖ = ‖logDeriv riemannZeta u‖ * ‖invZetaCont u‖ := hnorm
      _ ≤ (C₀ * Real.log |t| ^ 2) * (K * Real.log (|t| + Real.exp 1) ^ 11) :=
          mul_le_mul hl hi (norm_nonneg _) (by positivity)
      _ ≤ (C₀ * Real.log (|t| + Real.exp 1) ^ 2) * (K * Real.log (|t| + Real.exp 1) ^ 11) := by
          gcongr
      _ = C₀ * K * Real.log (|t| + Real.exp 1) ^ 13 := by ring
      _ ≤ (max B 0 + C₀ * K + 1) * Real.log (|t| + Real.exp 1) ^ 13 := by
          gcongr
          linarith [le_max_right B 0]

/-- **`1/ζ` is Lipschitz next to the `1`-line**: for `0 ≤ Re w ≤ 1/8`, `|Im w| ≤ 1`,
`|I(1 + iτ + w) − I(1 + iτ)| ≤ L log¹³(|τ| + 1 + e) |w|`. -/
theorem exists_norm_invZetaCont_sub_le :
    ∃ L : ℝ, 0 < L ∧ ∀ (τ : ℝ) (w : ℂ), 0 ≤ w.re → w.re ≤ 1 / 8 → |w.im| ≤ 1 →
      ‖invZetaCont (1 + (τ : ℂ) * I + w) - invZetaCont (1 + (τ : ℂ) * I)‖ ≤
        L * Real.log (|τ| + 1 + Real.exp 1) ^ 13 * ‖w‖ := by
  obtain ⟨C, hC, hd⟩ := exists_norm_deriv_invZetaCont_le
  refine ⟨C, hC, fun τ w hw0 hw1 hwi => ?_⟩
  set S := Icc (1 : ℝ) (9 / 8) ×ℂ Icc (τ - 1) (τ + 1) with hS
  have hmem0 : 1 + (τ : ℂ) * I ∈ S := by
    rw [hS, Complex.mem_reProdIm]; simp
  have hmem1 : 1 + (τ : ℂ) * I + w ∈ S := by
    rw [hS, Complex.mem_reProdIm]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.one_im, Complex.mul_im, zero_add]
    exact ⟨⟨by linarith, by linarith⟩, by linarith [abs_le.mp hwi], by linarith [abs_le.mp hwi]⟩
  have hdiff : ∀ v ∈ S, DifferentiableAt ℂ invZetaCont v := fun v hv => by
    rw [hS, Complex.mem_reProdIm] at hv
    exact differentiableAt_invZetaCont_of_one_le_re hv.1.1
  have hbound : ∀ v ∈ S, ‖deriv invZetaCont v‖ ≤ C * Real.log (|τ| + 1 + Real.exp 1) ^ 13 := by
    intro v hv
    rw [hS, Complex.mem_reProdIm] at hv
    have h := hd v.re v.im hv.1.1 hv.1.2
    rw [Complex.re_add_im] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    have hvim : |v.im| ≤ |τ| + 1 := by
      rw [abs_le]; constructor <;> linarith [hv.2.1, hv.2.2, neg_abs_le τ, le_abs_self τ]
    have hl1 := one_le_log_add_exp_one v.im
    exact pow_le_pow_left₀ (by linarith) (Real.log_le_log (by positivity) (by linarith)) 13
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound (convex_reProdIm_Icc _ _ _ _)
    hmem0 hmem1
  simpa using h

end

end RHTower
