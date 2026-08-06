import GaloisForLFunctions.RHTower.Sieve.ZetaLandauInput
import GaloisForLFunctions.RHTower.Sieve.DeLaValleePoussinInequality

/-!
# Counting the zeros of `ζ` near a point of the abscissa

Landau's lemma at `9/8 + iγ`, *keeping every* retained zero rather than discarding it, bounds their
number.  Each retained zero `ρ` sits within `1/8` of the centre and has `Re ρ ≤ 1`, so

```text
Re (9/8 + iγ - ρ)⁻¹ = (9/8 - Re ρ)/|9/8 + iγ - ρ|² ≥ (1/8)·64 = 8,
```

while the left side of Landau's inequality is bounded below by the value of the von Mangoldt series
at the real point `9/8`, because each of its terms has real part at least the negative of its
modulus.  Hence

```text
∑_ρ m_ρ ≪ log|γ|,
```

which is the classical `N(t+1) - N(t) = O(log t)`.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

/-- The three-four-one weight, in the degenerate form needed for a lower bound. -/
theorem neg_le_cos_mul {a E θ : ℝ} (ha : 0 ≤ a) (hE : 0 ≤ E) :
    -(a * (E * 1)) ≤ a * (E * Real.cos θ) := by
  have hcos := Real.neg_one_le_cos θ
  nlinarith [mul_nonneg (mul_nonneg ha hE) (by linarith : (0 : ℝ) ≤ Real.cos θ + 1)]

/-- Each von Mangoldt term at a shifted point is at least minus its value on the real axis. -/
theorem neg_re_term_le (n : ℕ) {σ γ : ℝ} :
    -(LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ)) ((σ : ℂ)) n).re
      ≤ (LSeries.term (fun m => ((vonMangoldt m : ℝ) : ℂ))
          ((σ : ℂ) + (γ : ℂ) * Complex.I) n).re := by
  rcases eq_or_ne n 0 with h | h
  · subst h
    simp [LSeries.term]
  · have hre0 : ((σ : ℂ)).re = σ := by simp
    have him0 : ((σ : ℂ)).im = 0 := by simp
    have hre1 : ((σ : ℂ) + (γ : ℂ) * Complex.I).re = σ := by simp
    have him1 : ((σ : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    rw [re_lseries_term_vonMangoldt h, re_lseries_term_vonMangoldt h, hre0, him0, hre1, him1]
    have hzero : Real.log n * 0 = 0 := by ring
    rw [hzero, Real.cos_zero]
    exact neg_le_cos_mul vonMangoldt_nonneg (Real.exp_nonneg _)

/-- **A lower bound for the logarithmic derivative off the real axis.** -/
theorem neg_re_logDeriv_ge {σ γ : ℝ} (hσ : 1 < σ) :
    -(-(logDeriv riemannZeta ((σ : ℂ))).re)
      ≤ -(logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)).re := by
  have hre0 : ((σ : ℂ)).re = σ := by simp
  have hre1 : ((σ : ℂ) + (γ : ℂ) * Complex.I).re = σ := by simp
  have h0 : (1 : ℝ) < ((σ : ℂ)).re := by rw [hre0]; exact hσ
  have h1 : (1 : ℝ) < ((σ : ℂ) + (γ : ℂ) * Complex.I).re := by rw [hre1]; exact hσ
  have hlog0 : -(logDeriv riemannZeta ((σ : ℂ))).re
      = (LSeries (fun m => ((vonMangoldt m : ℝ) : ℂ)) ((σ : ℂ))).re := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div h0, logDeriv_apply, neg_div,
      Complex.neg_re]
  have hlog1 : -(logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)).re
      = (LSeries (fun m => ((vonMangoldt m : ℝ) : ℂ))
          ((σ : ℂ) + (γ : ℂ) * Complex.I)).re := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1, logDeriv_apply, neg_div,
      Complex.neg_re]
  rw [hlog0, hlog1, re_lseries_vonMangoldt h0, re_lseries_vonMangoldt h1]
  have hs0 := summable_re_lseries_term_vonMangoldt h0
  have hs1 := summable_re_lseries_term_vonMangoldt h1
  rw [← tsum_neg]
  exact hs0.neg.tsum_le_tsum (fun n => neg_re_term_le n) hs1

/-- The real part of the reciprocal at a retained zero is at least `8`. -/
theorem eight_le_re_inv {γ : ℝ} {ρ : ℂ}
    (hρ : ‖(((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ ≤ 1 / 8)
    (hne : (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) ≠ ρ) (hre : ρ.re ≤ 1) :
    (8 : ℝ) ≤ (((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)⁻¹).re := by
  set w : ℂ := (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ with hwdef
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  have hwre : w.re = 9 / 8 - ρ.re := by rw [hwdef]; simp
  have hnormsq : Complex.normSq w = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq w
  have hnorm : ‖w‖ ≤ 1 / 8 := by rw [hwdef]; exact hρ
  have hnormpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  have hsq : Complex.normSq w ≤ 1 / 64 := by
    rw [hnormsq]
    nlinarith [hnormpos, hnorm]
  have hsqpos : (0 : ℝ) < Complex.normSq w := by
    rw [hnormsq]
    positivity
  rw [Complex.inv_re, hwre]
  rw [le_div_iff₀ hsqpos]
  nlinarith [hsq, hre]

/-- **The zero-counting bound.**  The zeros of `ζ` within `1/8` of `9/8 + iγ`, counted with
multiplicity, number `O(log|γ|)`. -/
theorem exists_zero_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 3 ≤ |γ| →
      ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
        (∀ w : ℂ, ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 1 / 8 →
          riemannZeta w = 0 → w ∈ Z) ∧
        (∀ ρ ∈ Z, riemannZeta ρ = 0) ∧
        (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
        ∑ ρ ∈ Z, (m ρ : ℝ) ≤ C * Real.log (7 + 8 * |γ|) := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  refine ⟨8 * 64 * (5 / 4 + 3 / 4) + (8 + max A 0), by positivity, fun γ hγ => ?_⟩
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hσ1 : (1 : ℝ) < 9 / 8 := by norm_num
  have hσ2 : (9 : ℝ) / 8 ≤ 2 := by norm_num
  obtain ⟨Z, m, hdist, hzero, hmem, hmult, hkey⟩ := zeta_landau_at hσ1 hσ2 hγ
  refine ⟨Z, m, hmem, hzero, hmult, ?_⟩
  set c : ℂ := (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) with hcdef
  have hcz : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hcdef]; simp; norm_num)
  -- each retained zero contributes at least `8`
  have hterm : ∀ ρ ∈ Z, (8 : ℝ) * (m ρ : ℝ) ≤ (m ρ : ℝ) * ((c - ρ)⁻¹).re := by
    intro ρ hρ
    have hρz : riemannZeta ρ = 0 := hzero ρ hρ
    have hne : c ≠ ρ := by
      intro hcon
      exact hcz (by rw [hcon]; exact hρz)
    have hrere : ρ.re ≤ 1 := by
      by_contra hcon
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt (not_le.mp hcon)) hρz
    have hdistc : ‖c - ρ‖ ≤ 1 / 8 := by
      have hZ : ‖ρ - c‖ ≤ 1 / 8 := hdist ρ hρ
      rw [← norm_neg]
      simpa using hZ
    have h8 := eight_le_re_inv (γ := γ) (ρ := ρ) (by rw [← hcdef]; exact hdistc)
      (by rw [← hcdef]; exact hne) hrere
    rw [← hcdef] at h8
    have hm0 : (0 : ℝ) ≤ (m ρ : ℝ) := Nat.cast_nonneg _
    nlinarith [h8, hm0]
  have hsum8 : (8 : ℝ) * ∑ ρ ∈ Z, (m ρ : ℝ)
      ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * ((c - ρ)⁻¹).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  -- the lower bound on the left side of Landau's inequality
  have hlow := neg_re_logDeriv_ge (σ := 9 / 8) (γ := γ) hσ1
  rw [← hcdef] at hlow
  have hpole := hA (9 / 8) hσ1 hσ2
  rw [neg_div_re_eq_neg_logDeriv_re] at hpole
  have hpole' : -(logDeriv riemannZeta (((9 / 8 : ℝ) : ℂ))).re ≤ 8 + A := by
    have hd : (9 : ℝ) / 8 - 1 = 1 / 8 := by norm_num
    rw [hd] at hpole
    norm_num at hpole ⊢
    linarith
  have hkeyfull := hkey Z (le_refl Z)
  -- assembling
  have hlogM : Real.log ((7 + 2 * |γ|) / ‖riemannZeta c‖)
      ≤ 5 / 4 * Real.log (7 + 8 * |γ|) + 3 / 4 * Real.log (1 + 1 / (9 / 8 - 1)) := by
    have hzpos : (0 : ℝ) < ‖riemannZeta c‖ := norm_pos_iff.mpr hcz
    rw [Real.log_div (by linarith) (ne_of_gt hzpos)]
    have hnum : Real.log (7 + 2 * |γ|) ≤ Real.log (7 + 8 * |γ|) :=
      Real.log_le_log (by linarith) (by linarith)
    have hden := neg_log_norm_riemannZeta_le (σ := 9 / 8) (t := γ) hσ1 hσ2 (by linarith)
    have hfour : Real.log (7 + 4 * |γ|) ≤ Real.log (7 + 8 * |γ|) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [hcdef]
    linarith
  have hlogpos : (1 : ℝ) ≤ Real.log (7 + 8 * |γ|) := by
    have h31 : (31 : ℝ) ≤ 7 + 8 * |γ| := by linarith
    have he : Real.exp 1 ≤ 31 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hlogconst : Real.log (1 + 1 / (9 / 8 - 1)) ≤ Real.log (7 + 8 * |γ|) := by
    have hval : (1 : ℝ) + 1 / (9 / 8 - 1) = 9 := by norm_num
    rw [hval]
    exact Real.log_le_log (by norm_num) (by linarith)
  have hAle : A ≤ max A 0 := le_max_left _ _
  have hA0 : (0 : ℝ) ≤ max A 0 := le_max_right _ _
  have hS : ∑ ρ ∈ Z, (m ρ : ℝ) * ((c - ρ)⁻¹).re
      ≤ 64 * Real.log ((7 + 2 * |γ|) / ‖riemannZeta c‖) + (8 + A) := by
    linarith [hkeyfull, hlow, hpole']
  have hlogM2 : Real.log ((7 + 2 * |γ|) / ‖riemannZeta c‖)
      ≤ 2 * Real.log (7 + 8 * |γ|) := by
    linarith [hlogM, hlogconst]
  have hfinal : (8 : ℝ) * ∑ ρ ∈ Z, (m ρ : ℝ)
      ≤ 128 * Real.log (7 + 8 * |γ|) + (8 + A) := by
    linarith [hsum8, hS, hlogM2]
  have hCle : (8 : ℝ) + A ≤ (8 + max A 0) * Real.log (7 + 8 * |γ|) := by
    nlinarith [hAle, hlogpos, hA0]
  nlinarith [hfinal, hCle, hlogpos, hA0]

end RHTower.Sieve
