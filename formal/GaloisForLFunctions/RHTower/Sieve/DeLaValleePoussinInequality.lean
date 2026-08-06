import GaloisForLFunctions.RHTower.Sieve.ZetaLandauInput
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleLogDeriv
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivThreeFourOne
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound
import GaloisForLFunctions.PNTPlus.ZetaBounds

/-!
# The de la Vallée Poussin inequality

Combining

* the pole bound `-Re ζ'/ζ(σ) ≤ 1/(σ-1) + A`,
* Landau's lemma at `σ + iγ`, keeping the assumed zero,
* Landau's lemma at `σ + 2iγ`, keeping nothing,

through the three-four-one inequality for the logarithmic derivative gives, for a zero `β + iγ`
close enough to the abscissa,

```text
4/(1 + δ - β)  ≤  3/δ + 3A + 320·( (5/4) log(7 + 8|γ|) + (3/4) log(1 + 1/δ) ).
```

The right side is `3/δ + O(log|γ|)` once `δ` is not too small, so choosing `δ` a small multiple of
`1/log|γ|` forces `1 - β` to exceed a multiple of `1/log|γ|`.  That is the zero-free region of
exponent `1`.
-/

namespace RHTower.Sieve

open Complex

/-- The two ways of writing the logarithmic derivative agree. -/
theorem neg_div_re_eq_neg_logDeriv_re (s : ℂ) :
    (-deriv riemannZeta s / riemannZeta s).re = -(logDeriv riemannZeta s).re := by
  rw [logDeriv_apply, neg_div, Complex.neg_re]

/-- The crude bound at a doubled height. -/
theorem norm_riemannZeta_double_height_le {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (ht : 1 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ ≤ 7 + 4 * |t| := by
  set w : ℂ := (σ : ℂ) + 2 * (t : ℂ) * Complex.I with hwdef
  have hre : w.re = σ := by rw [hwdef]; simp
  have him : w.im = 2 * t := by rw [hwdef]; simp
  have hnorm : ‖w‖ ≤ 2 + 2 * |t| := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im w) ?_
    rw [hre, him]
    have h1 : |σ| = σ := abs_of_pos (by linarith)
    have h2 : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
    rw [h1, h2]
    linarith
  have hcrude := norm_riemannZeta_le_crude (w := w) (by rw [hre]; linarith)
    (by rw [him, abs_mul]; simp; linarith)
  linarith

/-- **The reciprocal estimate in logarithmic form.** -/
theorem neg_log_norm_riemannZeta_le {σ t : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (ht : 1 ≤ |t|) :
    -Real.log ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 3 / 4 * Real.log (1 + 1 / (σ - 1)) + 1 / 4 * Real.log (7 + 4 * |t|) := by
  have hne1 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [hcon] at him
    simp only [Complex.one_im] at him
    rw [← him] at ht
    simp at ht
    linarith
  have hz1 : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hz1pos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_pos_iff.mpr hz1
  have hzσ : riemannZeta (σ : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hzσpos : (0 : ℝ) < ‖riemannZeta (σ : ℂ)‖ := norm_pos_iff.mpr hzσ
  have hz2 : riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hz2pos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr hz2
  have hinv := ZetaInvBound1 (σ := σ) (t := t) hσ1
  have hlog := Real.log_le_log (by positivity) hinv
  rw [Real.log_div one_ne_zero (ne_of_gt hz1pos), Real.log_one, zero_sub,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow hzσpos,
    Real.log_rpow hz2pos] at hlog
  refine le_trans hlog ?_
  have hA : Real.log ‖riemannZeta (σ : ℂ)‖ ≤ Real.log (1 + 1 / (σ - 1)) :=
    log_norm_riemannZeta_real_le hσ1
  have hB : Real.log ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖
      ≤ Real.log (7 + 4 * |t|) :=
    Real.log_le_log hz2pos (norm_riemannZeta_double_height_le hσ1 hσ2 ht)
  linarith

/-- **The de la Vallée Poussin inequality.** -/
theorem dlvp_inequality {β γ δ A : ℝ}
    (hA : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A)
    (hγ : 3 ≤ |γ|) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    (hβ : 1 - β ≤ 1 / 16) (hβ1 : β ≤ 1)
    (hzero : riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0) :
    4 / (1 + δ - β)
      ≤ 3 / δ + 3 * A
        + 320 * (5 / 4 * Real.log (7 + 8 * |γ|) + 3 / 4 * Real.log (1 + 1 / δ)) := by
  set σ : ℝ := 1 + δ with hσdef
  clear_value σ
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  have hγ0 : (0 : ℝ) ≤ |γ| := abs_nonneg γ
  have hγ2 : 3 ≤ |2 * γ| := by rw [abs_mul]; simp; linarith
  have hsb : 0 < σ - β := by rw [hσdef]; linarith
  -- the Landau data at height `γ`
  obtain ⟨Z₁, m₁, _, hz₁, hmem₁, hmult₁, hkey₁⟩ := zeta_landau_at hσ1 hσ2 hγ
  have hρmem : ((β : ℂ) + (γ : ℂ) * Complex.I) ∈ Z₁ := by
    refine hmem₁ _ ?_ hzero
    have hdiff : ((β : ℂ) + (γ : ℂ) * Complex.I) - ((σ : ℂ) + (γ : ℂ) * Complex.I)
        = (((β - σ : ℝ)) : ℂ) := by push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    rw [hσdef]
    linarith
  have hsum₁ : ∑ ρ ∈ ({(β : ℂ) + (γ : ℂ) * Complex.I} : Finset ℂ), (m₁ ρ : ℝ)
      * ((((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)⁻¹).re
      = (m₁ ((β : ℂ) + (γ : ℂ) * Complex.I) : ℝ) * (1 / (σ - β)) := by
    rw [Finset.sum_singleton]
    congr 1
    have hdiff : ((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)
        = (((σ - β : ℝ)) : ℂ) := by push_cast; ring
    rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have hone : (1 : ℝ) ≤ (m₁ ((β : ℂ) + (γ : ℂ) * Complex.I) : ℝ) := by
    exact_mod_cast hmult₁ _ hρmem
  have hkeyone := hkey₁ {(β : ℂ) + (γ : ℂ) * Complex.I}
    (Finset.singleton_subset_iff.mpr hρmem)
  rw [hsum₁] at hkeyone
  -- the Landau data at height `2γ`
  obtain ⟨Z₂, m₂, _, hz₂, hmem₂, hmult₂, hkey₂⟩ := zeta_landau_at hσ1 hσ2 hγ2
  have hkeytwo := hkey₂ ∅ (Finset.empty_subset _)
  rw [Finset.sum_empty, sub_zero] at hkeytwo
  -- the three-four-one inequality
  have h341 := zero_le_three_four_one_logDeriv (σ := σ) (t := γ) hσ1
  rw [neg_div_re_eq_neg_logDeriv_re, neg_div_re_eq_neg_logDeriv_re,
    neg_div_re_eq_neg_logDeriv_re] at h341
  have hcast2 : ((2 * γ : ℝ) : ℂ) = (2 * γ : ℂ) := by push_cast; ring
  rw [← hcast2] at h341
  -- the pole bound
  have hpole := hA σ hσ1 hσ2
  rw [neg_div_re_eq_neg_logDeriv_re] at hpole
  have hpole' : -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / δ + A := by
    have : σ - 1 = δ := by rw [hσdef]; ring
    rw [this] at hpole
    exact hpole
  -- the Landau constants
  have hz1pos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))
  have hz2pos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))
  set X : ℝ := 5 / 4 * Real.log (7 + 8 * |γ|) + 3 / 4 * Real.log (1 + 1 / δ) with hXdef
  clear_value X
  have hlogγ : Real.log (7 + 4 * |γ|) ≤ Real.log (7 + 8 * |γ|) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2γ : Real.log (7 + 2 * |2 * γ|) ≤ Real.log (7 + 8 * |γ|) := by
    rw [abs_mul]
    simp only [abs_two]
    exact Real.log_le_log (by linarith) (by linarith)
  have hδeq : Real.log (1 + 1 / (σ - 1)) = Real.log (1 + 1 / δ) := by
    have : σ - 1 = δ := by rw [hσdef]; ring
    rw [this]
  have hM₁ : Real.log ((7 + 2 * |γ|)
      / ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖) ≤ X := by
    rw [Real.log_div (by linarith) (ne_of_gt hz1pos)]
    have hnum : Real.log (7 + 2 * |γ|) ≤ Real.log (7 + 8 * |γ|) :=
      Real.log_le_log (by linarith) (by linarith)
    have hden := neg_log_norm_riemannZeta_le (σ := σ) (t := γ) hσ1 hσ2 (by linarith)
    rw [hδeq] at hden
    rw [hXdef]
    linarith [hlogγ]
  have hM₂ : Real.log ((7 + 2 * |2 * γ|)
      / ‖riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)‖) ≤ X := by
    rw [Real.log_div (by rw [abs_mul]; simp; linarith) (ne_of_gt hz2pos)]
    have hden := neg_log_norm_riemannZeta_le (σ := σ) (t := 2 * γ) hσ1 hσ2 (by linarith)
    rw [hδeq] at hden
    have hfour : Real.log (7 + 4 * |2 * γ|) ≤ Real.log (7 + 8 * |γ|) := by
      rw [abs_mul]
      simp only [abs_two]
      exact Real.log_le_log (by linarith) (by linarith)
    rw [hXdef]
    linarith [hlog2γ]
  -- assembling
  have hone' : (1 : ℝ) / (σ - β) ≤ (m₁ ((β : ℂ) + (γ : ℂ) * Complex.I) : ℝ) * (1 / (σ - β)) := by
    have hpos : (0 : ℝ) < 1 / (σ - β) := by positivity
    nlinarith [hone, hpos]
  have hkey1' : -(logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
      ≤ 64 * X - 1 / (σ - β) := by
    have := hkeyone
    nlinarith [hM₁, hone']
  have hkey2' : -(logDeriv riemannZeta ((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)).re
      ≤ 64 * X := by
    nlinarith [hkeytwo, hM₂]
  have hdiv : 4 / (σ - β) = 4 * (1 / (σ - β)) := by ring
  have hgoal : 4 / (σ - β) ≤ 3 / δ + 3 * A + 320 * X := by
    rw [hdiv]
    have e1 : 3 * -(logDeriv riemannZeta ((σ : ℂ))).re ≤ 3 * (1 / δ + A) :=
      mul_le_mul_of_nonneg_left hpole' (by norm_num)
    have e2 : 4 * -(logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
        ≤ 4 * (64 * X - 1 / (σ - β)) :=
      mul_le_mul_of_nonneg_left hkey1' (by norm_num)
    have hsum := add_le_add (add_le_add e1 e2) hkey2'
    have h3d : (3 : ℝ) / δ = 3 * (1 / δ) := by ring
    rw [h3d]
    linarith only [h341, hsum]
  exact hgoal

end RHTower.Sieve
