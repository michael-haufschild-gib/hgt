import GaloisForLFunctions.RHTower.InverseZetaRieszPerronShift
import GaloisForLFunctions.RHTower.MoebiusPartialSumBound
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegionBound
import GaloisForLFunctions.RHTower.BarnesMellinRemainder

/-!
# Riesz means of the Möbius series on the `1`-line

For `X = N + ½` the Riesz means `Q_N(z) = Σ_{n ≤ N} μ(n)(1 − n/X) n^{−z}` converge to `1/ζ` on the
`1`-line, `Q_N(1 + iτ) → 1/ζ(1 + iτ)` (`tendsto_moebiusRieszPoly_one_line`, Landau's theorem in Riesz
form), with a bound uniform in `N`: `|Q_N(1 + iτ)| ≤ C (|τ| + 4)^{1/32}`
(`exists_norm_moebiusRieszPoly_one_line_le`).

**Proof.**  The continued reciprocal `I = 1/ζ` (`invZetaCont`, `I(1) = 0`) is analytic on a
neighbourhood of `Re u ≥ 1` (`differentiableAt_invZetaCont_of_zeroFree`, from the zero-free region
`riemannZeta_ne_zero_of_lt_re`), with `|I|, |I'| ≪ log^{13}(|t| + e)` for `1 ≤ Re u ≤ 9/8`
(`exists_norm_invZetaCont_le`, `exists_norm_deriv_invZetaCont_le`: `I' = −(ζ'/ζ) I` at large
heights, compactness below), so `I` is Lipschitz next to the line (`exists_norm_invZetaCont_sub_le`).
The Perron formula on `Re w = c > 0` with the constant term split off
(`moebiusRieszPoly_one_line_eq_of_pos`) passes to `c = 0` by dominated convergence, because the
Lipschitz bound cancels the pole of `X^w/(w(w+1))` at `w = 0` (`exists_norm_rieszIntegrand_le`):
`Q_N = (1 − 1/X) I + (1/2π) ∫ X^{iy}(I(· + iy) − I)/(iy(iy+1)) dy` (`moebiusRieszPoly_one_line_eq`).
The integral is uniformly bounded, and it is a Fourier integral of a fixed integrable function at
frequency `log X/2π`, so it tends to `0` (Riemann–Lebesgue).
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower

noncomputable section
set_option autoImplicit false

/-! ### Analyticity near the `1`-line -/

/-- Off the zeros the residue unit `(u − 1)ζ(u)` does not vanish. -/
theorem zetaResidueUnit_ne_zero_near_one_line {u : ℂ} (h0 : 0 < u.re)
    (h : 1 - 1 / 58 / Real.log (|u.im| + 4) < u.re) : zetaResidueUnit u ≠ 0 := by
  by_cases h1 : u = 1
  · rw [h1, zetaResidueUnit_one]; exact one_ne_zero
  rw [(zetaResidueUnit_eventuallyEq h1).eq_of_nhds]
  exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_lt_re h0 h)

theorem differentiableAt_invZetaCont_of_zeroFree {u : ℂ} (h0 : 0 < u.re)
    (h : 1 - 1 / 58 / Real.log (|u.im| + 4) < u.re) : DifferentiableAt ℂ invZetaCont u :=
  (differentiableAt_id.sub_const 1).div (analyticAt_zetaResidueUnit u).differentiableAt
    (zetaResidueUnit_ne_zero_near_one_line h0 h)

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
      _ ≤ (C₀ * Real.log (|t| + Real.exp 1) ^ 2) * (K * Real.log (|t| + Real.exp 1) ^ 11) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC₀.le)
            (mul_nonneg hK.le (pow_nonneg (by linarith [one_le_log_add_exp_one t]) 11))
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
    rw [hS, Complex.mem_reProdIm]; norm_num
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

/-! ### Polynomial forms of the bounds -/

theorem log_pow_le_rpow_one_div_32 {x : ℝ} (hx : 1 ≤ x) {k : ℕ} (hk : 0 < k) :
    Real.log x ^ k ≤ (32 * k) ^ k * x ^ (1 / 32 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hε : (0 : ℝ) < 1 / (32 * k) := by positivity
  have h' : Real.log x ≤ 32 * k * x ^ (1 / (32 * k) : ℝ) := by
    calc Real.log x ≤ x ^ (1 / (32 * k) : ℝ) / (1 / (32 * k)) := Real.log_le_rpow_div hx0 hε
      _ = 32 * k * x ^ (1 / (32 * k) : ℝ) := by rw [div_div_eq_mul_div, div_one]; ring
  calc Real.log x ^ k ≤ (32 * k * x ^ (1 / (32 * k) : ℝ)) ^ k :=
        pow_le_pow_left₀ (Real.log_nonneg hx) h' k
    _ = (32 * k) ^ k * x ^ (1 / 32 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / (32 * k) : ℝ)), ← Real.rpow_mul hx0]
        congr 2
        field_simp

theorem exists_norm_invZetaCont_le_rpow :
    ∃ K : ℝ, 0 < K ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 5 / 4 →
      ‖invZetaCont ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K * (|t| + 4) ^ (1 / 32 : ℝ) := by
  obtain ⟨K, hK, hI⟩ := exists_norm_invZetaCont_le
  refine ⟨K * (32 * 11) ^ 11, by positivity, fun σ t h1 h2 => ?_⟩
  have he : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_d9; linarith
  have hx1 : 1 ≤ |t| + Real.exp 1 := by linarith [abs_nonneg t, Real.add_one_le_exp 1]
  have hl := log_pow_le_rpow_one_div_32 hx1 (k := 11) (by norm_num)
  have hm : (|t| + Real.exp 1) ^ (1 / 32 : ℝ) ≤ (|t| + 4) ^ (1 / 32 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  calc _ ≤ K * Real.log (|t| + Real.exp 1) ^ 11 := hI σ t h1 h2
    _ ≤ K * ((32 * 11) ^ 11 * (|t| + Real.exp 1) ^ (1 / 32 : ℝ)) := by
        push_cast at hl
        exact mul_le_mul_of_nonneg_left hl hK.le
    _ ≤ K * ((32 * 11) ^ 11 * (|t| + 4) ^ (1 / 32 : ℝ)) := by gcongr
    _ = K * (32 * 11) ^ 11 * (|t| + 4) ^ (1 / 32 : ℝ) := by ring

theorem exists_norm_invZetaCont_sub_le_rpow :
    ∃ L : ℝ, 0 < L ∧ ∀ (τ : ℝ) (w : ℂ), 0 ≤ w.re → w.re ≤ 1 / 8 → |w.im| ≤ 1 →
      ‖invZetaCont (1 + (τ : ℂ) * I + w) - invZetaCont (1 + (τ : ℂ) * I)‖ ≤
        L * (|τ| + 4) ^ (1 / 32 : ℝ) * ‖w‖ := by
  obtain ⟨L, hL, hLip⟩ := exists_norm_invZetaCont_sub_le
  refine ⟨L * (32 * 13) ^ 13, by positivity, fun τ w hw0 hw1 hwi => ?_⟩
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; linarith
  have hx1 : 1 ≤ |τ| + 1 + Real.exp 1 := by linarith [abs_nonneg τ, Real.exp_pos 1]
  have hl := log_pow_le_rpow_one_div_32 hx1 (k := 13) (by norm_num)
  have hm : (|τ| + 1 + Real.exp 1) ^ (1 / 32 : ℝ) ≤ (|τ| + 4) ^ (1 / 32 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  calc _ ≤ L * Real.log (|τ| + 1 + Real.exp 1) ^ 13 * ‖w‖ := hLip τ w hw0 hw1 hwi
    _ ≤ L * ((32 * 13) ^ 13 * (|τ| + 4) ^ (1 / 32 : ℝ)) * ‖w‖ := by
        push_cast at hl
        gcongr
        exact hl.trans (by gcongr)
    _ = L * (32 * 13) ^ 13 * (|τ| + 4) ^ (1 / 32 : ℝ) * ‖w‖ := by ring

/-! ### The Riesz integrand -/

/-- `1 ≤ 2 (1 + y²)^{−3/4}` for `|y| ≤ 1`. -/
theorem one_le_two_mul_one_add_sq_rpow {y : ℝ} (hy : |y| ≤ 1) : 1 ≤ 2 * (1 + y ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have hy2 : y ^ 2 ≤ 1 := by nlinarith [sq_abs y, abs_nonneg y]
  have hm := Real.rpow_le_rpow_of_nonpos (by positivity) (show 1 + y ^ 2 ≤ 2 by linarith)
    (by norm_num : -(3 / 4 : ℝ) ≤ 0)
  have h2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), one_div]
    apply inv_anti₀ (by positivity)
    calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  linarith

/-- `((a+1)^{1/32} + 1)/a² ≤ 6 (1 + a²)^{−3/4}` for `a ≥ 1`. -/
theorem riesz_tail_rpow_le {a : ℝ} (ha : 1 ≤ a) :
    ((a + 1) ^ (1 / 32 : ℝ) + 1) / a ^ 2 ≤ 6 * (1 + a ^ 2) ^ (-(3 / 4 : ℝ)) := by
  set B := 1 + a ^ 2 with hB
  have hB1 : 1 ≤ B := by nlinarith
  have hB0 : 0 < B := by linarith
  have ha2 : B ≤ 2 * a ^ 2 := by nlinarith
  have hq : (a + 1) ^ (1 / 32 : ℝ) ≤ 2 * B ^ (1 / 4 : ℝ) := by
    have h1 : (a + 1) ^ (1 / 32 : ℝ) ≤ (2 * B) ^ (1 / 32 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by nlinarith) (by norm_num)
    have h2 : (2 * B) ^ (1 / 32 : ℝ) ≤ (2 * B) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h3 : (2 * B) ^ (1 / 4 : ℝ) = 2 ^ (1 / 4 : ℝ) * B ^ (1 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hB0.le
    have h4 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hB4 : 0 ≤ B ^ (1 / 4 : ℝ) := by positivity
    nlinarith
  have hone : 1 ≤ B ^ (1 / 4 : ℝ) := Real.one_le_rpow hB1 (by norm_num)
  have hexp : B ^ (1 / 4 : ℝ) / B = B ^ (-(3 / 4 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hB0]; norm_num
  have ha2' : 0 < a ^ 2 := by positivity
  calc ((a + 1) ^ (1 / 32 : ℝ) + 1) / a ^ 2 ≤ (3 * B ^ (1 / 4 : ℝ)) / a ^ 2 := by
        gcongr; linarith
    _ ≤ (3 * B ^ (1 / 4 : ℝ)) / (B / 2) := by
        gcongr; linarith
    _ = 6 * (B ^ (1 / 4 : ℝ) / B) := by field_simp; ring
    _ = 6 * B ^ (-(3 / 4 : ℝ)) := by rw [hexp]

/-- **The Riesz integrand is dominated**: for `X ≥ 1`, `0 ≤ c ≤ 1/8`,
`|X^w/(w(w+1)) (I(1 + iτ + w) − I(1 + iτ))| ≤ X^c A (|τ|+4)^{1/32} (1 + y²)^{−3/4}`, `w = c + iy`. -/
theorem exists_norm_rieszIntegrand_le :
    ∃ A : ℝ, 0 < A ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (τ c y : ℝ), 0 ≤ c → c ≤ 1 / 8 →
      ‖Perron.f X ((c : ℂ) + (y : ℂ) * I) *
          (invZetaCont (1 + (τ : ℂ) * I + ((c : ℂ) + (y : ℂ) * I)) -
            invZetaCont (1 + (τ : ℂ) * I))‖ ≤
        X ^ c * (A * (|τ| + 4) ^ (1 / 32 : ℝ) * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) := by
  obtain ⟨K, hK, hI⟩ := exists_norm_invZetaCont_le_rpow
  obtain ⟨L, hL, hLip⟩ := exists_norm_invZetaCont_sub_le_rpow
  refine ⟨2 * L + 6 * K, by positivity, fun X hX τ c y hc0 hc1 => ?_⟩
  set w : ℂ := (c : ℂ) + (y : ℂ) * I with hw
  set q : ℝ := (|τ| + 4) ^ (1 / 32 : ℝ) with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  have hwre : w.re = c := by simp [hw]
  have hwim : w.im = y := by simp [hw]
  have hXc : 0 < X ^ c := Real.rpow_pos_of_pos (by linarith) c
  have hf : ‖Perron.f X w‖ = X ^ c * (‖w‖ * ‖w + 1‖)⁻¹ := by
    rw [norm_perron_f X (by linarith) w, hwre, norm_perron_f_one_eq]
  have hw1 : 1 ≤ ‖w + 1‖ := by
    have : (w + 1).re = c + 1 := by simp [hw]
    calc (1 : ℝ) ≤ (w + 1).re := by rw [this]; linarith
      _ ≤ |(w + 1).re| := le_abs_self _
      _ ≤ ‖w + 1‖ := Complex.abs_re_le_norm _
  have hP : 0 ≤ (1 + y ^ 2) ^ (-(3 / 4 : ℝ)) := by positivity
  rw [norm_mul, hf]
  rcases le_or_gt |y| 1 with hy | hy
  · -- near the real axis: Lipschitz
    have hlip := hLip τ w (by rw [hwre]; exact hc0) (by rw [hwre]; exact hc1) (by rw [hwim]; exact hy)
    have hkey : (‖w‖ * ‖w + 1‖)⁻¹ * ‖w‖ ≤ 1 := by
      rcases eq_or_lt_of_le (norm_nonneg w) with h0 | h0
      · rw [← h0]; simp
      · rw [mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ h0.ne', one_mul]
        exact inv_le_one_of_one_le₀ hw1
    have h2 := one_le_two_mul_one_add_sq_rpow hy
    calc X ^ c * (‖w‖ * ‖w + 1‖)⁻¹ * ‖invZetaCont (1 + (τ : ℂ) * I + w) -
          invZetaCont (1 + (τ : ℂ) * I)‖
        ≤ X ^ c * (‖w‖ * ‖w + 1‖)⁻¹ * (L * q * ‖w‖) :=
          mul_le_mul_of_nonneg_left hlip (by positivity)
      _ = X ^ c * (L * q) * ((‖w‖ * ‖w + 1‖)⁻¹ * ‖w‖) := by ring
      _ ≤ X ^ c * (L * q) * 1 := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ X ^ c * (L * q) * (2 * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ X ^ c * ((2 * L + 6 * K) * q * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) := by
          rw [show X ^ c * (L * q) * (2 * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) =
            X ^ c * ((2 * L) * q * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) by ring]
          gcongr
          linarith
  · -- far from the real axis: size
    set a := |y| with ha
    have ha1 : 1 ≤ a := hy.le
    have hwn : a ≤ ‖w‖ := by
      calc a = |w.im| := by rw [hwim]
        _ ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hwn1 : a ≤ ‖w + 1‖ := by
      calc a = |(w + 1).im| := by simp [hw, ha]
        _ ≤ ‖w + 1‖ := Complex.abs_im_le_norm _
    have hinv : (‖w‖ * ‖w + 1‖)⁻¹ ≤ 1 / a ^ 2 := by
      rw [one_div, sq]
      exact inv_anti₀ (by positivity) (mul_le_mul hwn hwn1 (by positivity) (norm_nonneg _))
    have hre : (1 + (τ : ℂ) * I + w).re = 1 + c := by simp [hw]
    have him : (1 + (τ : ℂ) * I + w).im = τ + y := by simp [hw]
    have hz1 := hI (1 + c) (τ + y) (by linarith) (by linarith)
    have hz0 := hI 1 τ le_rfl (by norm_num)
    have e1 : ((1 + c : ℝ) : ℂ) + ((τ + y : ℝ) : ℂ) * I = 1 + (τ : ℂ) * I + w := by
      rw [hw]; push_cast; ring
    have e0 : ((1 : ℝ) : ℂ) + (τ : ℂ) * I = 1 + (τ : ℂ) * I := by push_cast; ring
    rw [e1] at hz1
    rw [e0] at hz0
    have hgrow : (|τ + y| + 4) ^ (1 / 32 : ℝ) ≤ q * (a + 1) ^ (1 / 32 : ℝ) := by
      rw [hq, ← Real.mul_rpow (by positivity) (by positivity)]
      refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
      have := abs_add_le τ y
      nlinarith [abs_nonneg τ, abs_nonneg y]
    have hbr : ‖invZetaCont (1 + (τ : ℂ) * I + w) - invZetaCont (1 + (τ : ℂ) * I)‖ ≤
        K * q * ((a + 1) ^ (1 / 32 : ℝ) + 1) := by
      calc _ ≤ ‖invZetaCont (1 + (τ : ℂ) * I + w)‖ + ‖invZetaCont (1 + (τ : ℂ) * I)‖ :=
            norm_sub_le _ _
        _ ≤ K * (|τ + y| + 4) ^ (1 / 32 : ℝ) + K * q := add_le_add hz1 hz0
        _ ≤ K * (q * (a + 1) ^ (1 / 32 : ℝ)) + K * q := by gcongr
        _ = K * q * ((a + 1) ^ (1 / 32 : ℝ) + 1) := by ring
    have htail := riesz_tail_rpow_le ha1
    have hay : a ^ 2 = y ^ 2 := sq_abs y
    rw [hay] at htail
    calc X ^ c * (‖w‖ * ‖w + 1‖)⁻¹ * ‖invZetaCont (1 + (τ : ℂ) * I + w) -
          invZetaCont (1 + (τ : ℂ) * I)‖
        ≤ X ^ c * (1 / a ^ 2) * (K * q * ((a + 1) ^ (1 / 32 : ℝ) + 1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hinv hXc.le) hbr (norm_nonneg _) (by positivity)
      _ = X ^ c * (K * q) * (((a + 1) ^ (1 / 32 : ℝ) + 1) / y ^ 2) := by rw [← hay]; ring
      _ ≤ X ^ c * (K * q) * (6 * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ X ^ c * ((2 * L + 6 * K) * q * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) := by
          rw [show X ^ c * (K * q) * (6 * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) =
            X ^ c * ((6 * K) * q * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) by ring]
          gcongr
          linarith

theorem integrable_rpow_neg_three_quarters :
    Integrable fun y : ℝ => (1 + y ^ 2) ^ (-(3 / 4 : ℝ)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 3 / 2)
    (by simp; norm_num)
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  norm_num

/-! ### The Riesz means on the `1`-line -/

theorem one_le_perronLength {N : ℕ} (hN : 1 ≤ N) : 1 ≤ perronLength N := by
  unfold perronLength
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- The Riesz integrand `X^w/(w(w+1)) (I(1 + iτ + w) − I(1 + iτ))` on `Re w = c`. -/
def rieszIntegrand (X τ c y : ℝ) : ℂ :=
  Perron.f X ((c : ℂ) + (y : ℂ) * I) *
    (invZetaCont (1 + (τ : ℂ) * I + ((c : ℂ) + (y : ℂ) * I)) - invZetaCont (1 + (τ : ℂ) * I))

theorem continuousAt_perron_f {X : ℝ} (hX : 0 < X) {w : ℂ} (h0 : w ≠ 0) (h1 : w + 1 ≠ 0) :
    ContinuousAt (Perron.f X) w := by
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  show ContinuousAt (fun s : ℂ => (X : ℂ) ^ s / (s * (s + 1))) w
  exact (continuousAt_const_cpow hX').div (continuousAt_id.mul (continuousAt_id.add continuousAt_const))
    (mul_ne_zero h0 h1)

theorem continuousAt_rieszIntegrand_y {X : ℝ} (hX : 0 < X) (τ : ℝ) {c y : ℝ} (hc : 0 ≤ c)
    (hy : (c : ℂ) + (y : ℂ) * I ≠ 0) : ContinuousAt (rieszIntegrand X τ c) y := by
  have h1 : (c : ℂ) + (y : ℂ) * I + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hre : 1 ≤ (1 + (τ : ℂ) * I + ((c : ℂ) + (y : ℂ) * I)).re := by simp; linarith
  unfold rieszIntegrand
  refine ((continuousAt_perron_f hX hy h1).comp (f := fun y : ℝ => (c : ℂ) + (y : ℂ) * I)
    (by fun_prop)).mul (ContinuousAt.sub ?_ continuousAt_const)
  exact (differentiableAt_invZetaCont_of_one_le_re hre).continuousAt.comp
    (f := fun y : ℝ => 1 + (τ : ℂ) * I + ((c : ℂ) + (y : ℂ) * I)) (by fun_prop)

theorem aestronglyMeasurable_rieszIntegrand {X : ℝ} (hX : 0 < X) (τ : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    AEStronglyMeasurable (rieszIntegrand X τ c) volume := by
  have hcont : ContinuousOn (rieszIntegrand X τ c) {(0 : ℝ)}ᶜ := fun y hy =>
    (continuousAt_rieszIntegrand_y hX τ hc (fun h => by
      have := congrArg Complex.im h; simp at this; exact hy this)).continuousWithinAt
  have hm := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ)).compl
  rwa [restrict_compl_singleton] at hm

theorem exists_integrable_rieszIntegrand :
    ∃ A : ℝ, 0 < A ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (τ c : ℝ), 0 ≤ c → c ≤ 1 / 8 →
      Integrable (rieszIntegrand X τ c) ∧
        ∀ y, ‖rieszIntegrand X τ c y‖ ≤
          X ^ c * (A * (|τ| + 4) ^ (1 / 32 : ℝ) * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) := by
  obtain ⟨A, hA, hb⟩ := exists_norm_rieszIntegrand_le
  refine ⟨A, hA, fun X hX τ c hc0 hc1 => ⟨?_, fun y => hb X hX τ c y hc0 hc1⟩⟩
  exact Integrable.mono' (integrable_rpow_neg_three_quarters.const_mul
      (X ^ c * (A * (|τ| + 4) ^ (1 / 32 : ℝ))))
    (aestronglyMeasurable_rieszIntegrand (by linarith) τ hc0)
    (ae_of_all _ fun y => by
      have := hb X hX τ c y hc0 hc1
      rw [show X ^ c * (A * (|τ| + 4) ^ (1 / 32 : ℝ)) * (1 + y ^ 2) ^ (-(3 / 4 : ℝ)) =
        X ^ c * (A * (|τ| + 4) ^ (1 / 32 : ℝ) * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))) by ring]
      exact this)

/-- The Perron formula on a line `Re w = c > 0`, with the constant term split off. -/
theorem moebiusRieszPoly_one_line_eq_of_pos {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1 / 8) :
    moebiusRieszPoly N (1 + (τ : ℂ) * I) =
      ((1 - 1 / perronLength N : ℝ) : ℂ) * invZetaCont (1 + (τ : ℂ) * I) +
        ((2 * Real.pi)⁻¹ : ℝ) • ∫ y : ℝ, rieszIntegrand (perronLength N) τ c y := by
  obtain ⟨A, hA, hint⟩ := exists_integrable_rieszIntegrand
  set X := perronLength N with hXdef
  have hX1 : 1 ≤ X := one_le_perronLength hN
  have hX0 : 0 < X := by linarith
  have h1 := moebiusRieszPoly_eq_verticalIntegral' N (z := 1 + (τ : ℂ) * I) hc0
    (by simp; linarith)
  rw [verticalIntegral'_eq_smul] at h1
  have h2 := verticalIntegral'_perron_f_eq N (n := 1) le_rfl hc0
  rw [Nat.cast_one, div_one, if_pos hN, verticalIntegral'_eq_smul] at h2
  have hfi : Integrable fun y : ℝ => Perron.f X ((c : ℂ) + (y : ℂ) * I) :=
    Perron.isIntegrable hX0 hc0.ne' (by linarith)
  have hsplit : (∫ y : ℝ, Perron.f X ((c : ℂ) + (y : ℂ) * I) *
        invZetaCont (1 + (τ : ℂ) * I + ((c : ℂ) + (y : ℂ) * I))) =
      (∫ y : ℝ, rieszIntegrand X τ c y) +
        invZetaCont (1 + (τ : ℂ) * I) * ∫ y : ℝ, Perron.f X ((c : ℂ) + (y : ℂ) * I) := by
    rw [← integral_const_mul, ← integral_add (hint X hX1 τ c hc0.le hc1).1 (hfi.const_mul _)]
    congr 1
    funext y
    unfold rieszIntegrand
    ring
  rw [← hXdef] at h2
  rw [h1, hsplit, smul_add, add_comm]
  congr 1
  calc ((2 * Real.pi)⁻¹ : ℝ) • (invZetaCont (1 + (τ : ℂ) * I) *
        ∫ y : ℝ, Perron.f X ((c : ℂ) + (y : ℂ) * I))
      = invZetaCont (1 + (τ : ℂ) * I) *
          (((2 * Real.pi)⁻¹ : ℝ) • ∫ y : ℝ, Perron.f X ((c : ℂ) + (y : ℂ) * I)) := by
        rw [Complex.real_smul, Complex.real_smul]; ring
    _ = _ := by rw [h2, mul_comm]

/-- **The Riesz means on the `1`-line**:
`Q_N(1 + iτ) = (1 − 1/X) I(1 + iτ) + (1/2π) ∫ X^{iy}/(iy(iy + 1)) (I(1 + iτ + iy) − I(1 + iτ)) dy`. -/
theorem moebiusRieszPoly_one_line_eq {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) :
    moebiusRieszPoly N (1 + (τ : ℂ) * I) =
      ((1 - 1 / perronLength N : ℝ) : ℂ) * invZetaCont (1 + (τ : ℂ) * I) +
        ((2 * Real.pi)⁻¹ : ℝ) • ∫ y : ℝ, rieszIntegrand (perronLength N) τ 0 y := by
  obtain ⟨A, hA, hint⟩ := exists_integrable_rieszIntegrand
  set X := perronLength N with hXdef
  have hX1 : 1 ≤ X := one_le_perronLength hN
  have hX0 : 0 < X := by linarith
  -- dominated convergence as `c ↓ 0`
  have hlim : Tendsto (fun c => ∫ y : ℝ, rieszIntegrand X τ c y) (𝓝[>] 0)
      (𝓝 (∫ y : ℝ, rieszIntegrand X τ 0 y)) := by
    have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ), c ∈ Ioc (0 : ℝ) (1 / 8) :=
      Ioc_mem_nhdsGT (by norm_num)
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => X ^ (1 / 8 : ℝ) * (A * (|τ| + 4) ^ (1 / 32 : ℝ) * (1 + y ^ 2) ^ (-(3 / 4 : ℝ))))
      ?_ ?_ ((integrable_rpow_neg_three_quarters.const_mul
        (X ^ (1 / 8 : ℝ) * (A * (|τ| + 4) ^ (1 / 32 : ℝ)))).congr (ae_of_all _ fun y => by
        simp only; ring)) ?_
    · filter_upwards [hev] with c hc
      exact aestronglyMeasurable_rieszIntegrand hX0 τ hc.1.le
    · filter_upwards [hev] with c hc
      refine ae_of_all _ fun y => ((hint X hX1 τ c hc.1.le hc.2).2 y).trans ?_
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hX1 hc.2)
        (by positivity)
    · have hae : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
        rw [ae_iff]; simpa using (measure_singleton (0 : ℝ) : volume {(0 : ℝ)} = 0)
      filter_upwards [hae] with y hy
      have hc : ContinuousAt (fun c : ℝ => rieszIntegrand X τ c y) 0 := by
        have hy0 : ((0 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := fun h => by
          have := congrArg Complex.im h; simp at this; exact hy this
        have hy1 : ((0 : ℝ) : ℂ) + (y : ℂ) * I + 1 ≠ 0 := fun h => by
          have := congrArg Complex.re h; simp at this
        have hre : 1 ≤ (1 + (τ : ℂ) * I + (((0 : ℝ) : ℂ) + (y : ℂ) * I)).re := by simp
        unfold rieszIntegrand
        refine ((continuousAt_perron_f hX0 hy0 hy1).comp (f := fun c : ℝ => (c : ℂ) + (y : ℂ) * I)
          (by fun_prop)).mul (ContinuousAt.sub ?_ continuousAt_const)
        exact (differentiableAt_invZetaCont_of_one_le_re hre).continuousAt.comp
          (f := fun c : ℝ => 1 + (τ : ℂ) * I + ((c : ℂ) + (y : ℂ) * I)) (by fun_prop)
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
  -- the right side is constant for `0 < c ≤ 1/8`
  have hconst : Tendsto (fun c => ((1 - 1 / X : ℝ) : ℂ) * invZetaCont (1 + (τ : ℂ) * I) +
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ y : ℝ, rieszIntegrand X τ c y) (𝓝[>] 0)
      (𝓝 (moebiusRieszPoly N (1 + (τ : ℂ) * I))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with c hc
    exact moebiusRieszPoly_one_line_eq_of_pos hN τ hc.1 hc.2
  exact tendsto_nhds_unique hconst (tendsto_const_nhds.add (hlim.const_smul _))

/-- **Uniform bound for the Riesz means on the `1`-line**: `|Q_N(1 + iτ)| ≤ C (|τ| + 4)^{1/32}`. -/
theorem exists_norm_moebiusRieszPoly_one_line_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (τ : ℝ),
      ‖moebiusRieszPoly N (1 + (τ : ℂ) * I)‖ ≤ C * (|τ| + 4) ^ (1 / 32 : ℝ) := by
  obtain ⟨K, hK, hI⟩ := exists_norm_invZetaCont_le_rpow
  obtain ⟨A, hA, hint⟩ := exists_integrable_rieszIntegrand
  set J₀ := ∫ y : ℝ, (1 + y ^ 2) ^ (-(3 / 4 : ℝ)) with hJ₀
  have hJ0 : 0 ≤ J₀ := integral_nonneg fun y => by positivity
  refine ⟨K + (2 * Real.pi)⁻¹ * A * J₀ + 1, by positivity, fun N τ => ?_⟩
  have hq : 1 ≤ (|τ| + 4) ^ (1 / 32 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [moebiusRieszPoly]; positivity
  set X := perronLength N
  have hX1 : 1 ≤ X := one_le_perronLength hN
  rw [moebiusRieszPoly_one_line_eq hN τ]
  have hz := hI 1 τ le_rfl (by norm_num)
  rw [show ((1 : ℝ) : ℂ) + (τ : ℂ) * I = 1 + (τ : ℂ) * I by push_cast; ring] at hz
  have hc : |1 - 1 / X| ≤ 1 := by
    rw [abs_le]; constructor
    · have : 0 ≤ 1 / X := by positivity
      have : 1 / X ≤ 1 := by rw [div_le_one (by linarith)]; exact hX1
      linarith
    · have : 0 ≤ 1 / X := by positivity
      linarith
  have hJ : ‖∫ y : ℝ, rieszIntegrand X τ 0 y‖ ≤ A * (|τ| + 4) ^ (1 / 32 : ℝ) * J₀ := by
    calc _ ≤ ∫ y : ℝ, A * (|τ| + 4) ^ (1 / 32 : ℝ) * (1 + y ^ 2) ^ (-(3 / 4 : ℝ)) :=
          norm_integral_le_of_norm_le (integrable_rpow_neg_three_quarters.const_mul _)
            (ae_of_all _ fun y => by
              have := (hint X hX1 τ 0 le_rfl (by norm_num)).2 y
              rwa [Real.rpow_zero, one_mul] at this)
      _ = A * (|τ| + 4) ^ (1 / 32 : ℝ) * J₀ := integral_const_mul _ _
  calc ‖((1 - 1 / X : ℝ) : ℂ) * invZetaCont (1 + (τ : ℂ) * I) +
        ((2 * Real.pi)⁻¹ : ℝ) • ∫ y : ℝ, rieszIntegrand X τ 0 y‖
      ≤ |1 - 1 / X| * ‖invZetaCont (1 + (τ : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ y : ℝ, rieszIntegrand X τ 0 y‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    _ ≤ 1 * (K * (|τ| + 4) ^ (1 / 32 : ℝ)) +
          (2 * Real.pi)⁻¹ * (A * (|τ| + 4) ^ (1 / 32 : ℝ) * J₀) := by
        gcongr
    _ ≤ (K + (2 * Real.pi)⁻¹ * A * J₀ + 1) * (|τ| + 4) ^ (1 / 32 : ℝ) := by
        nlinarith

/-- **Landau's theorem for Riesz means on the `1`-line**: `Q_N(1 + iτ) → 1/ζ(1 + iτ)`. -/
theorem tendsto_moebiusRieszPoly_one_line (τ : ℝ) :
    Tendsto (fun N => moebiusRieszPoly N (1 + (τ : ℂ) * I)) atTop
      (𝓝 (invZetaCont (1 + (τ : ℂ) * I))) := by
  obtain ⟨A, hA, hint⟩ := exists_integrable_rieszIntegrand
  -- the integrand at `c = 0` is a Fourier integral of a fixed integrable function
  set h : ℝ → ℂ := fun y => (((y : ℂ) * I) * ((y : ℂ) * I + 1))⁻¹ *
    (invZetaCont (1 + (τ : ℂ) * I + (y : ℂ) * I) - invZetaCont (1 + (τ : ℂ) * I)) with hh
  have hfour : ∀ X : ℝ, 0 < X → ∀ y : ℝ, rieszIntegrand X τ 0 y =
      Real.fourierChar (-(y * (-(Real.log X / (2 * Real.pi))))) • h y := by
    intro X hX y
    have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    unfold rieszIntegrand
    simp only [Complex.ofReal_zero, zero_add, hh]
    show (X : ℂ) ^ ((y : ℂ) * I) / (((y : ℂ) * I) * ((y : ℂ) * I + 1)) * _ = _
    rw [Complex.cpow_def_of_ne_zero hX', ← Complex.ofReal_log hX.le]
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have e : ((2 * Real.pi * -(y * -(Real.log X / (2 * Real.pi))) : ℝ) : ℂ) * I =
        (Real.log X : ℂ) * ((y : ℂ) * I) := by
      push_cast
      field_simp
    rw [e, div_eq_mul_inv]
    ring
  have hRL := Real.tendsto_integral_exp_smul_cocompact h
  have hw : Tendsto (fun N : ℕ => -(Real.log (perronLength N) / (2 * Real.pi))) atTop atBot := by
    have hX : Tendsto (fun N : ℕ => perronLength N) atTop atTop := by
      unfold perronLength
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact tendsto_neg_atTop_atBot.comp
      ((Real.tendsto_log_atTop.comp hX).atTop_div_const (by positivity))
  have hint0 : Tendsto (fun N : ℕ => ∫ y : ℝ, rieszIntegrand (perronLength N) τ 0 y) atTop (𝓝 0) := by
    have := hRL.comp (hw.mono_right atBot_le_cocompact)
    refine this.congr fun N => ?_
    simp only [Function.comp]
    exact (integral_congr_ae (ae_of_all _ fun y => (hfour _ (by
      have := one_le_perronLength (N := N + 1) (by omega)
      unfold perronLength at this ⊢; positivity) y))).symm
  have hcoef : Tendsto (fun N : ℕ => ((1 - 1 / perronLength N : ℝ) : ℂ)) atTop (𝓝 1) := by
    have hX : Tendsto (fun N : ℕ => perronLength N) atTop atTop := by
      unfold perronLength
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h1 : Tendsto (fun N : ℕ => (1 - 1 / perronLength N : ℝ)) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hX.inv_tendsto_atTop
      rw [sub_zero] at h
      refine h.congr fun N => ?_
      simp [one_div]
    exact (Complex.continuous_ofReal.tendsto 1).comp h1 |>.congr fun N => rfl
  have hfull := (hcoef.mul_const (invZetaCont (1 + (τ : ℂ) * I))).add (hint0.const_smul
    ((2 * Real.pi)⁻¹ : ℝ))
  rw [one_mul, smul_zero, add_zero] at hfull
  refine hfull.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (moebiusRieszPoly_one_line_eq hN τ).symm

end

end RHTower
