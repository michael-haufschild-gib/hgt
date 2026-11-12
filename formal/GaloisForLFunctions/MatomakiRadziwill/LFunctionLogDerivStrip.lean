import GaloisForLFunctions.MatomakiRadziwill.LFunctionConj
import GaloisForLFunctions.RHTower.Sieve.ZetaLandauWide

/-!
# `L'/L` in a thin strip left of `Re s = 1`

For a nonprincipal character `χ` mod `q` and the Vinogradov–Korobov width
`ε(t) = (log t)^{-2/3}(log log t)^{-5/3}/10⁸` (`vkWidth`), every large `Y` satisfies
(`exists_LFunction_logDeriv_strip`)

`L(σ + iγ, χ) ≠ 0`,  `‖L'/L(σ + iγ, χ)‖ ≤ C log Y / ε(Y + 1)`   for `|γ| ≤ Y`, `1 − ε(Y+1)/2 ≤ σ ≤ 9/8`.

The proof is the corpus argument for `ζ'/ζ` (`Sieve.exists_logDeriv_zeta_bound_of_width`) with the
inputs for `L`:

* crude growth `‖L(s, ψ)‖ ≤ 2q(1 + ‖s‖/Re s)` on `Re s > 0`, hence `≤ 2q(90 + 40|γ|)` on the disc of
  radius `11/10` about `9/8 + iγ`, against `‖L(9/8 + iγ)‖ ≥ 1/9`: Landau's lemma bounds `L'/L` minus
  the zeros of the half-disc by `O_q(log|γ|)`;
* the zero count from Landau's inequality at the centre, where `Re L'/L ≤ Re(−ζ'/ζ(9/8))`;
* each retained zero lies left of `1 − ε(|γ|+1)` (`LFunction_ne_zero_vinogradovKorobov_abs`), so at
  distance at least `ε/2` from the point.

Heights below a fixed `T₀` are covered by compactness: `L` has no zero on `[1, 9/8] × [−T₀, T₀]`,
hence none on a thickening, where `L'/L` is continuous and bounded.
-/

open Complex Metric LSeries ArithmeticFunction RHTower.Sieve Filter Topology
open scoped LSeries.notation

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {q : ℕ} [NeZero q]

theorem one_le_modulus : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

/-- Crude growth: `‖L(s, ψ)‖ ≤ 2q(1 + ‖s‖/Re s)` for `Re s > 0`. -/
theorem norm_LFunction_le_crude (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction ψ s‖ ≤ 2 * q * (1 + ‖s‖ / s.re) := by
  have h := RHTower.norm_LFunction_sub_character_partial_le hψ hs 0
  have h0 : RHTower.dirichletPartialSum (fun j => ψ (j + 1)) 0 s = 0 := by
    simp [RHTower.dirichletPartialSum]
  rw [h0, sub_zero] at h
  simpa using h

/-- **Growth on the wide disc.**  `‖L(w, ψ)‖ ≤ 2q(90 + 40|γ|)` for `‖w − (9/8 + iγ)‖ < 11/10`. -/
theorem norm_LFunction_wide_disc_le (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) {γ : ℝ} {w : ℂ}
    (hw : w ∈ ball (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I) (11 / 10)) :
    ‖DirichletCharacter.LFunction ψ w‖ ≤ 2 * q * (90 + 40 * |γ|) := by
  have hd : ‖w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ < 11 / 10 := by
    simpa [dist_eq_norm] using hw
  have hre : 1 / 40 < w.re := by
    have h1 := Complex.abs_re_le_norm (w - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I))
    rw [Complex.sub_re, wide_centre_re] at h1
    have h2 := neg_abs_le (w.re - 9 / 8)
    linarith
  have hc : ‖(((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ ≤ 9 / 8 + |γ| := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    rw [wide_centre_re, wide_centre_im, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 8)]
  have hnorm : ‖w‖ ≤ 9 / 8 + |γ| + 11 / 10 := by
    have h := norm_sub_norm_le w (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)
    linarith
  have hrat : ‖w‖ / w.re ≤ 40 * ‖w‖ := by
    rw [div_le_iff₀ (by linarith)]
    have h := mul_nonneg (norm_nonneg w) (by linarith : (0 : ℝ) ≤ 40 * w.re - 1)
    nlinarith [h]
  have hq : (0 : ℝ) ≤ 2 * q := by positivity
  calc ‖DirichletCharacter.LFunction ψ w‖ ≤ 2 * q * (1 + ‖w‖ / w.re) :=
        norm_LFunction_le_crude ψ hψ (by linarith)
    _ ≤ 2 * q * (90 + 40 * |γ|) := by
        refine mul_le_mul_of_nonneg_left ?_ hq
        linarith

/-- The Landau constant of the wide disc for modulus `q`. -/
def lWideD (q : ℕ) : ℝ := Real.log (2340 * q) + 1

theorem log_2340_mul_nonneg : 0 ≤ Real.log (2340 * (q : ℝ)) :=
  Real.log_nonneg (by have := one_le_modulus (q := q); linarith)

theorem lWideD_pos : 0 < lWideD q := by
  have := log_2340_mul_nonneg (q := q)
  unfold lWideD
  linarith

/-- `1/9 ≤ ‖L(9/8 + iγ, ψ)‖ ≤ 9`. -/
theorem L_wide_centre_bounds (ψ : DirichletCharacter ℂ q) (γ : ℝ) :
    1 / 9 ≤ ‖DirichletCharacter.LFunction ψ (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ ∧
      ‖DirichletCharacter.LFunction ψ (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ ≤ 9 := by
  have hlow := inv_le_norm_LFunction ψ (σ := 9 / 8) (by norm_num) γ
  have hup := norm_LFunction_le_of_one_lt ψ (s := ((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)
    (by rw [wide_centre_re]; norm_num)
  rw [wide_centre_re] at hup
  norm_num at hlow hup ⊢
  exact ⟨hlow, hup⟩

/-- **The Landau ratio on the wide disc.** -/
theorem log_L_wide_ratio_le (ψ : DirichletCharacter ℂ q) {γ : ℝ} (hγ : 4 ≤ |γ|) :
    Real.log (2 * q * (90 + 40 * |γ|)
        / ‖DirichletCharacter.LFunction ψ (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖)
      ≤ lWideD q * Real.log |γ| := by
  have hq1 := one_le_modulus (q := q)
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hN0 : (0 : ℝ) < 2 * q * (90 + 40 * |γ|) := by positivity
  obtain ⟨hLc, -⟩ := L_wide_centre_bounds ψ γ
  have hLc0 : (0 : ℝ) < ‖DirichletCharacter.LFunction ψ (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ := by
    linarith
  rw [Real.log_div hN0.ne' hLc0.ne']
  have h1 : Real.log (2 * q * (90 + 40 * |γ|)) ≤ Real.log (260 * q) + Real.log |γ| := by
    rw [← Real.log_mul (by positivity) hγ0.ne']
    apply Real.log_le_log hN0
    have hstep : (180 : ℝ) * q ≤ 180 * q * |γ| := by
      have h := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ |γ|)
        (by positivity : (0 : ℝ) ≤ 180 * q)
      linarith
    nlinarith [hstep]
  have h2 : -Real.log ‖DirichletCharacter.LFunction ψ (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖
      ≤ Real.log 9 := by
    have h := Real.log_le_log (by norm_num) hLc
    rw [one_div, Real.log_inv] at h
    linarith
  have h3 : Real.log (260 * q) + Real.log 9 = Real.log (2340 * q) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    ring
  have hL1 := one_le_log_abs hγ
  have h4 : Real.log (2340 * (q : ℝ)) ≤ Real.log (2340 * q) * Real.log |γ| :=
    le_mul_of_one_le_right log_2340_mul_nonneg hL1
  unfold lWideD
  rw [add_mul, one_mul]
  linarith

/-- **Landau's data on the wide disc** for `L(s, ψ)`. -/
theorem L_landau_wide (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) {γ : ℝ} (hγ : 4 ≤ |γ|) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z, ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ ≤ 21 / 40) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction ψ ρ = 0) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ∀ z : ℂ, ‖z - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ ≤ 21 / 160 →
        DirichletCharacter.LFunction ψ z ≠ 0 →
        ‖logDeriv (DirichletCharacter.LFunction ψ) z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖
          ≤ 320 / 21 * lWideD q * Real.log |γ| := by
  set c : ℂ := ((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I with hcdef
  have hq1 := one_le_modulus (q := q)
  have hfc : DirichletCharacter.LFunction ψ c ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ)
      (by rw [hcdef, wide_centre_re]; norm_num)
  obtain ⟨hLc, hLc9⟩ := L_wide_centre_bounds ψ γ
  have hpos : (0 : ℝ) < ‖DirichletCharacter.LFunction ψ c‖ := norm_pos_iff.mpr hfc
  have hM1 : (1 : ℝ) < 2 * q * (90 + 40 * |γ|) / ‖DirichletCharacter.LFunction ψ c‖ := by
    rw [lt_div_iff₀ hpos, one_mul]
    have h : (180 : ℝ) ≤ 2 * q * (90 + 40 * |γ|) := by
      have h1 : (90 : ℝ) ≤ 90 + 40 * |γ| := by linarith [abs_nonneg γ]
      have h2 := mul_le_mul h1 (by linarith : (2 : ℝ) ≤ 2 * q) (by norm_num) (by linarith)
      linarith
    linarith
  have hbound : ∀ w ∈ ball c (11 / 10 : ℝ), ‖DirichletCharacter.LFunction ψ w‖
      ≤ (2 * q * (90 + 40 * |γ|) / ‖DirichletCharacter.LFunction ψ c‖)
        * ‖DirichletCharacter.LFunction ψ c‖ := by
    intro w hw
    rw [div_mul_cancel₀ _ hpos.ne']
    exact norm_LFunction_wide_disc_le ψ hψ hw
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction ψ) (ball c (11 / 10)) :=
    (DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd isOpen_ball
  obtain ⟨Z, m, hZdist, hZzero, -, hZmult, hZkey⟩ :=
    landau_logDeriv (f := DirichletCharacter.LFunction ψ) (c := c) (R := 21 / 20) (R₀ := 11 / 10)
      (by norm_num) (by norm_num) hM1 han hfc hbound
  refine ⟨Z, m, fun ρ hρ => by linarith [hZdist ρ hρ], hZzero, hZmult, fun z hz hfz => ?_⟩
  have hkey := hZkey z (by linarith) hfz
  have hrw : 16 * Real.log (2 * q * (90 + 40 * |γ|) / ‖DirichletCharacter.LFunction ψ c‖)
      / (21 / 20) = 320 / 21 * Real.log (2 * q * (90 + 40 * |γ|)
        / ‖DirichletCharacter.LFunction ψ c‖) := by ring
  rw [hrw] at hkey
  have hlog := log_L_wide_ratio_le ψ hγ
  rw [← hcdef] at hlog
  have hD := lWideD_pos (q := q)
  nlinarith [hkey, hlog]

/-- `Re (c − ρ)⁻¹ ≥ 200/441` for `c = 9/8 + iγ`, `‖ρ − c‖ ≤ 21/40` and `Re ρ ≤ 1`. -/
theorem wide_re_inv_ge_of_re_le {γ : ℝ} {ρ : ℂ}
    (hd : ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ ≤ 21 / 40) (hrere : ρ.re ≤ 1) :
    (200 / 441 : ℝ) ≤ (((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I) - ρ)⁻¹).re := by
  set w : ℂ := (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I) - ρ with hwdef
  have hwre : w.re = 9 / 8 - ρ.re := by rw [hwdef, Complex.sub_re, wide_centre_re]
  have hw0 : w ≠ 0 := by
    intro h
    have : w.re = 0 := by rw [h]; simp
    linarith
  have hnorm : ‖w‖ ≤ 21 / 40 := by
    rw [hwdef, ← norm_neg]
    simpa using hd
  have hnormsq : Complex.normSq w = ‖w‖ ^ (2 : ℕ) := Complex.normSq_eq_norm_sq w
  have hnormpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  have hsq : Complex.normSq w ≤ 441 / 1600 := by
    rw [hnormsq]; nlinarith [hnormpos, hnorm]
  have hsqpos : (0 : ℝ) < Complex.normSq w := by
    rw [hnormsq]; positivity
  rw [Complex.inv_re, hwre, le_div_iff₀ hsqpos]
  nlinarith [hsq, hrere]

omit [NeZero q] in
/-- `−Re L(ψΛ, σ + iy) ≤ Re(−ζ'/ζ(σ))` for `σ > 1`. -/
theorem neg_re_LSeries_twist_vonMangoldt_le (ψ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ)
    (y : ℝ) :
    -(LSeries (↗ψ * ↗Λ) ((σ : ℂ) + (y : ℂ) * I)).re ≤
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have hs0 : 1 < ((σ : ℂ)).re := by simp [hσ]
  have hs1 : 1 < ((σ : ℂ) + (y : ℂ) * I).re := by simp [hσ]
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs0]
  have H1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt ψ hs1
  have HΛ := LSeriesSummable_vonMangoldt hs0
  rw [LSeries, LSeries, Complex.re_tsum H1, Complex.re_tsum HΛ, ← tsum_neg]
  refine ((Complex.hasSum_re H1.hasSum).summable.neg).tsum_le_tsum (fun n => ?_)
    (Complex.hasSum_re HΛ.hasSum).summable
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hσpow : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hn0.le]
  have hnσ : (0 : ℝ) < (n : ℝ) ^ σ := by positivity
  have hre1 : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
  have hnorm : ‖term (↗ψ * ↗Λ) ((σ : ℂ) + (y : ℂ) * I) n‖ ≤ Λ n / (n : ℝ) ^ σ := by
    rw [norm_term_eq, if_neg hn, hre1]
    refine div_le_div_of_nonneg_right ?_ hnσ.le
    simp only [Pi.mul_apply, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_left vonMangoldt_nonneg (DirichletCharacter.norm_le_one ψ _)
  have hreΛ : (term (fun n => ((Λ n : ℝ) : ℂ)) (σ : ℂ) n).re = Λ n / (n : ℝ) ^ σ := by
    rw [term_of_ne_zero hn, hσpow, ← Complex.ofReal_div, Complex.ofReal_re]
  have habs := Complex.abs_re_le_norm (term (↗ψ * ↗Λ) ((σ : ℂ) + (y : ℂ) * I) n)
  have hneg := neg_abs_le (term (↗ψ * ↗Λ) ((σ : ℂ) + (y : ℂ) * I) n).re
  show -(term (↗ψ * ↗Λ) ((σ : ℂ) + (y : ℂ) * I) n).re ≤
    (term (fun n => ((Λ n : ℝ) : ℂ)) (σ : ℂ) n).re
  rw [hreΛ]
  linarith

/-- `Re L'/L(9/8 + iγ, ψ) ≤ 8 + A`, `A` the constant of the pole bound for `ζ'/ζ`. -/
theorem re_logDeriv_L_wide_centre_le (ψ : DirichletCharacter ℂ q) {A : ℝ}
    (hA : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A) (γ : ℝ) :
    (logDeriv (DirichletCharacter.LFunction ψ) (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)).re
      ≤ 8 + A := by
  have hs : 1 < ((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)).re := by rw [wide_centre_re]; norm_num
  have h1 := re_LSeries_twist_vonMangoldt_eq ψ hs
  have h2 := neg_re_LSeries_twist_vonMangoldt_le ψ (σ := 9 / 8) (by norm_num) γ
  have h3 := hA (9 / 8) (by norm_num) (by norm_num)
  have h4 : (1 : ℝ) / (9 / 8 - 1) = 8 := by norm_num
  rw [h4] at h3
  linarith

/-- **The zero count on the wide disc.**  If the zeros `Z` (multiplicities `m`) satisfy Landau's
inequality with error `K` at the centre, then `(200/441) Σ m ≤ K + 8 + A`. -/
theorem L_wide_zero_count (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) {A : ℝ}
    (hA : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A)
    {γ K : ℝ} (Z : Finset ℂ) (m : ℂ → ℕ)
    (hdist : ∀ ρ ∈ Z, ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ ≤ 21 / 40)
    (hzero : ∀ ρ ∈ Z, DirichletCharacter.LFunction ψ ρ = 0)
    (hkey : ‖logDeriv (DirichletCharacter.LFunction ψ) (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)
        - ∑ ρ ∈ Z, (m ρ : ℂ) / ((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I) - ρ)‖ ≤ K) :
    (200 / 441 : ℝ) * ∑ ρ ∈ Z, (m ρ : ℝ) ≤ K + 8 + A := by
  set c : ℂ := ((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I with hcdef
  have hreSum : (∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ)).re = ∑ ρ ∈ Z, (m ρ : ℝ) * ((c - ρ)⁻¹).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun ρ _ => re_natCast_div _ _
  have hsplit : (∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ)).re
      ≤ (logDeriv (DirichletCharacter.LFunction ψ) c).re + K := by
    have h := Complex.abs_re_le_norm
      (logDeriv (DirichletCharacter.LFunction ψ) c - ∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ))
    rw [Complex.sub_re] at h
    have h2 := abs_le.mp (le_trans h hkey)
    linarith [h2.1]
  have hcentre := re_logDeriv_L_wide_centre_le ψ hA γ
  have hterm : ∀ ρ ∈ Z, (200 / 441 : ℝ) * (m ρ : ℝ) ≤ (m ρ : ℝ) * ((c - ρ)⁻¹).re := by
    intro ρ hρ
    have hrere : ρ.re ≤ 1 := by
      by_contra hcon
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ)
        (le_of_lt (not_le.mp hcon)) (hzero ρ hρ)
    have h := wide_re_inv_ge_of_re_le (hdist ρ hρ) hrere
    have hm0 : (0 : ℝ) ≤ (m ρ : ℝ) := Nat.cast_nonneg _
    nlinarith [h, hm0]
  have hsum : (200 / 441 : ℝ) * ∑ ρ ∈ Z, (m ρ : ℝ) ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * ((c - ρ)⁻¹).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  linarith [hsum, hreSum, hsplit, hcentre]

/-- **Every zero near the wide centre lies left of the region**, for a zero-free region of
antitone width `w` at both signs of the height. -/
theorem L_wide_zero_re_le_width (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) {w : ℝ → ℝ}
    {T₀ γ : ℝ} (hT₀ : 4 ≤ T₀)
    (hwanti : ∀ s t : ℝ, T₀ ≤ s → s ≤ t → w t ≤ w s)
    (hregion : ∀ β γ' : ℝ, T₀ ≤ |γ'| → β ≤ 1 → 1 - w |γ'| < β →
      DirichletCharacter.LFunction ψ ((β : ℂ) + (γ' : ℂ) * I) ≠ 0)
    (hγ : T₀ + 1 ≤ |γ|) {ρ : ℂ}
    (hd : ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ ≤ 21 / 40)
    (hz : DirichletCharacter.LFunction ψ ρ = 0) :
    ρ.re ≤ 1 - w (|γ| + 1) := by
  have hrere : ρ.re ≤ 1 := by
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ)
      (le_of_lt (not_le.mp hcon)) hz
  have him : |ρ.im - γ| ≤ 21 / 40 := by
    have h1 := Complex.abs_im_le_norm (ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I))
    rw [Complex.sub_im, wide_centre_im] at h1
    linarith
  have habs := abs_le.mp him
  have hlow : T₀ ≤ |ρ.im| := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases ρ.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [habs.1, habs.2, hγ]
  have hup : |ρ.im| ≤ |γ| + 1 := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases ρ.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [habs.1, habs.2, hγ]
  by_contra hcon
  have hwle : w (|γ| + 1) ≤ w |ρ.im| := hwanti _ _ hlow hup
  have hgt : 1 - w |ρ.im| < ρ.re := by linarith [not_le.mp hcon]
  refine hregion ρ.re ρ.im hlow hrere hgt ?_
  rw [Complex.re_add_im]
  exact hz

/-- The final arithmetic of the width bound. -/
theorem width_bound_arith {Lg w S D E Lz : ℝ} (hL0 : 0 < Lg) (hw0 : 0 < w) (hwS : w ≤ 1 / 80)
    (hD : 0 < D) (hS : S ≤ E * Lg) (hLz : Lz ≤ 320 / 21 * D * Lg + S * (2 / w)) :
    Lz ≤ (320 / 21 * D / 80 + 2 * E) * Lg / w := by
  have hlin : 320 / 21 * D * Lg ≤ 320 / 21 * D / 80 * Lg / w := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hw0]
    have h := mul_le_mul_of_nonneg_left hwS (by positivity : (0 : ℝ) ≤ 320 / 21 * D * Lg)
    nlinarith [h]
  have hprod : S * (2 / w) ≤ 2 * E * Lg / w := by
    have hstep := mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ 2 / w)
    calc S * (2 / w) ≤ (E * Lg) * (2 / w) := hstep
      _ = 2 * E * Lg / w := by field_simp
  have hsum : 320 / 21 * D / 80 * Lg / w + 2 * E * Lg / w = (320 / 21 * D / 80 + 2 * E) * Lg / w := by
    field_simp
  linarith

/-- **`L'/L` inside a zero-free region of arbitrary antitone width.** -/
theorem exists_logDeriv_LFunction_bound_of_width (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    {w : ℝ → ℝ} {T₀ : ℝ} (hT₀ : 4 ≤ T₀)
    (hwpos : ∀ t : ℝ, T₀ ≤ t → 0 < w t)
    (hwsmall : ∀ t : ℝ, T₀ ≤ t → w t ≤ 1 / 80)
    (hwanti : ∀ s t : ℝ, T₀ ≤ s → s ≤ t → w t ≤ w s)
    (hregion : ∀ β γ' : ℝ, T₀ ≤ |γ'| → β ≤ 1 → 1 - w |γ'| < β →
      DirichletCharacter.LFunction ψ ((β : ℂ) + (γ' : ℂ) * I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ γ : ℝ, T₀ + 1 ≤ |γ| → 1 - w (|γ| + 1) / 2 ≤ σ → σ ≤ 9 / 8 →
        DirichletCharacter.LFunction ψ ((σ : ℂ) + (γ : ℂ) * I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction ψ) ((σ : ℂ) + (γ : ℂ) * I)‖
          ≤ C * Real.log |γ| / w (|γ| + 1) := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  set D : ℝ := lWideD q with hDdef
  have hD : 0 < D := lWideD_pos
  set E : ℝ := 441 / 200 * (320 / 21 * D + 8 + max A 0) with hEdef
  have hE : 0 < E := by
    have : (0 : ℝ) ≤ max A 0 := le_max_right _ _
    rw [hEdef]; positivity
  refine ⟨320 / 21 * D / 80 + 2 * E, by positivity, ?_⟩
  intro σ γ hγT hσlow hσ98
  have hγ4 : (4 : ℝ) ≤ |γ| := by linarith
  have hγT₀ : T₀ ≤ |γ| := by linarith
  have hL1 := one_le_log_abs hγ4
  have hL0 : (0 : ℝ) < Real.log |γ| := by linarith
  have hTup : T₀ ≤ |γ| + 1 := by linarith
  have hw0 : 0 < w (|γ| + 1) := hwpos _ hTup
  have hwS : w (|γ| + 1) ≤ 1 / 80 := hwsmall _ hTup
  have hwγ : w (|γ| + 1) ≤ w |γ| := hwanti _ _ hγT₀ (by linarith)
  have hzne : DirichletCharacter.LFunction ψ ((σ : ℂ) + (γ : ℂ) * I) ≠ 0 := by
    rcases le_or_gt σ 1 with hle | hgt
    · exact hregion σ γ hγT₀ hle (by linarith)
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ)
        (by simp; linarith)
  refine ⟨hzne, ?_⟩
  obtain ⟨Z, m, hZdist, hZzero, -, hZkey⟩ := L_landau_wide ψ hψ hγ4
  have hzc : ‖((σ : ℂ) + (γ : ℂ) * I) - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)‖ ≤ 21 / 160 := by
    have hdiff : ((σ : ℂ) + (γ : ℂ) * I) - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I)
        = (((σ - 9 / 8 : ℝ)) : ℂ) := by push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hkeyz := hZkey ((σ : ℂ) + (γ : ℂ) * I) hzc hzne
  have hfc : DirichletCharacter.LFunction ψ (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ)
      (by rw [wide_centre_re]; norm_num)
  have hkeyc := hZkey (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * I) (by rw [sub_self, norm_zero]; norm_num) hfc
  have hcnt0 := L_wide_zero_count ψ hψ hA Z m hZdist hZzero hkeyc
  have hcnt : ∑ ρ ∈ Z, (m ρ : ℝ) ≤ E * Real.log |γ| := by
    have hAle : A ≤ max A 0 := le_max_left _ _
    have hA0 : (0 : ℝ) ≤ max A 0 := le_max_right _ _
    have h1 : ∑ ρ ∈ Z, (m ρ : ℝ) ≤ 441 / 200 * (320 / 21 * D * Real.log |γ| + 8 + max A 0) := by
      linarith
    have h2 : (8 + max A 0) ≤ (8 + max A 0) * Real.log |γ| :=
      le_mul_of_one_le_right (by linarith) hL1
    rw [hEdef]
    nlinarith [h1, h2]
  have hdistz : ∀ ρ ∈ Z, w (|γ| + 1) / 2 ≤ ‖((σ : ℂ) + (γ : ℂ) * I) - ρ‖ := by
    intro ρ hρ
    have hleft := L_wide_zero_re_le_width ψ hψ hT₀ hwanti hregion hγT (hZdist ρ hρ) (hZzero ρ hρ)
    have h1 := Complex.abs_re_le_norm (((σ : ℂ) + (γ : ℂ) * I) - ρ)
    have h2 : (((σ : ℂ) + (γ : ℂ) * I) - ρ).re = σ - ρ.re := by
      rw [Complex.sub_re]
      simp
    rw [h2] at h1
    linarith [le_abs_self (σ - ρ.re)]
  have hsumz : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * I) - ρ)‖
      ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) * (2 / w (|γ| + 1)) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    rw [norm_div, Complex.norm_natCast]
    have hd := hdistz ρ hρ
    have hdpos : (0 : ℝ) < ‖((σ : ℂ) + (γ : ℂ) * I) - ρ‖ := by linarith
    rw [div_le_iff₀ hdpos]
    have hm0 : (0 : ℝ) ≤ (m ρ : ℝ) := Nat.cast_nonneg _
    have hinv : (1 : ℝ) ≤ 2 / w (|γ| + 1) * ‖((σ : ℂ) + (γ : ℂ) * I) - ρ‖ := by
      have hmul := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 / w (|γ| + 1))
      have hone : 2 / w (|γ| + 1) * (w (|γ| + 1) / 2) = 1 := by field_simp
      rw [hone] at hmul
      exact hmul
    nlinarith [hm0, hinv]
  have hsplit := norm_le_norm_sub_add
    (logDeriv (DirichletCharacter.LFunction ψ) ((σ : ℂ) + (γ : ℂ) * I))
    (∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * I) - ρ))
  exact width_bound_arith hL0 hw0 hwS hD hcnt (by linarith [hsplit, hkeyz, hsumz])

/-- The Vinogradov–Korobov width `ε(t) = (log t)^{-2/3}(log log t)^{-5/3}/10⁸`. -/
def vkWidth (t : ℝ) : ℝ :=
  Real.log t ^ (-(2 : ℝ) / 3) * Real.log (Real.log t) ^ (-(5 : ℝ) / 3) / 10 ^ 8

/-- The height past which both logarithms in `vkWidth` are at least `1`. -/
def vkThreshold : ℝ := Real.exp (Real.exp 1)

theorem one_le_log_log_of_vkThreshold_le {t : ℝ} (ht : vkThreshold ≤ t) :
    1 ≤ Real.log t ∧ 1 ≤ Real.log (Real.log t) := by
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht
  have hlog : Real.exp 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]; exact ht
  refine ⟨le_trans he1 hlog, ?_⟩
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact hlog

theorem vkWidth_pos {t : ℝ} (ht : vkThreshold ≤ t) : 0 < vkWidth t := by
  obtain ⟨h1, h2⟩ := one_le_log_log_of_vkThreshold_le ht
  unfold vkWidth
  have a := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log t) (-(2 : ℝ) / 3)
  have b := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log (Real.log t)) (-(5 : ℝ) / 3)
  positivity

theorem vkWidth_le_log_pow {t : ℝ} (ht : vkThreshold ≤ t) :
    vkWidth t ≤ Real.log t ^ (-(2 : ℝ) / 3) / 10 ^ 8 := by
  obtain ⟨h1, h2⟩ := one_le_log_log_of_vkThreshold_le ht
  unfold vkWidth
  have a := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log t) (-(2 : ℝ) / 3)
  have b : Real.log (Real.log t) ^ (-(5 : ℝ) / 3) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h2 (by norm_num)
  have hmul : Real.log t ^ (-(2 : ℝ) / 3) * Real.log (Real.log t) ^ (-(5 : ℝ) / 3)
      ≤ Real.log t ^ (-(2 : ℝ) / 3) := mul_le_of_le_one_right a.le b
  exact div_le_div_of_nonneg_right hmul (by norm_num)

theorem vkWidth_le {t : ℝ} (ht : vkThreshold ≤ t) : vkWidth t ≤ 1 / 80 := by
  obtain ⟨h1, -⟩ := one_le_log_log_of_vkThreshold_le ht
  have a : Real.log t ^ (-(2 : ℝ) / 3) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
  have h := vkWidth_le_log_pow ht
  have h2 : Real.log t ^ (-(2 : ℝ) / 3) / 10 ^ 8 ≤ 1 / 10 ^ 8 :=
    div_le_div_of_nonneg_right a (by norm_num)
  linarith [show (1 : ℝ) / 10 ^ 8 ≤ 1 / 80 by norm_num]

theorem vkWidth_anti {s t : ℝ} (hs : vkThreshold ≤ s) (hst : s ≤ t) : vkWidth t ≤ vkWidth s := by
  obtain ⟨hs1, hs2⟩ := one_le_log_log_of_vkThreshold_le hs
  have hs0 : 0 < s := by linarith [Real.add_one_le_exp (Real.exp 1), Real.exp_pos (Real.exp 1),
    show vkThreshold = Real.exp (Real.exp 1) from rfl]
  have hlog : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
  have hloglog : Real.log (Real.log s) ≤ Real.log (Real.log t) :=
    Real.log_le_log (by linarith) hlog
  have a := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < Real.log s) hlog
    (by norm_num : -(2 : ℝ) / 3 ≤ 0)
  have b := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < Real.log (Real.log s)) hloglog
    (by norm_num : -(5 : ℝ) / 3 ≤ 0)
  have a0 := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log t) (-(2 : ℝ) / 3)
  have b0 := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log (Real.log t)) (-(5 : ℝ) / 3)
  have bs0 := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Real.log (Real.log s)) (-(5 : ℝ) / 3)
  unfold vkWidth
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  exact mul_le_mul a b b0.le (le_trans a0.le a)

/-- **`L'/L` in the Vinogradov–Korobov strip at large heights.** -/
theorem exists_logDeriv_LFunction_vk (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ T₀ C : ℝ, 4 ≤ T₀ ∧ vkThreshold ≤ T₀ ∧ 0 < C ∧
      ∀ σ γ : ℝ, T₀ + 1 ≤ |γ| → 1 - vkWidth (|γ| + 1) / 2 ≤ σ → σ ≤ 9 / 8 →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (γ : ℂ) * I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (γ : ℂ) * I)‖
          ≤ C * Real.log |γ| / vkWidth (|γ| + 1) := by
  obtain ⟨γ₀, hγ₀⟩ := LFunction_ne_zero_vinogradovKorobov_abs χ hχ
  set T₀ : ℝ := max (max γ₀ 4) vkThreshold with hT₀def
  have hT4 : 4 ≤ T₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hTv : vkThreshold ≤ T₀ := le_max_right _ _
  have hTγ : γ₀ ≤ T₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  obtain ⟨C, hC, hbound⟩ := exists_logDeriv_LFunction_bound_of_width χ hχ (w := vkWidth) hT4
    (fun t ht => vkWidth_pos (le_trans hTv ht)) (fun t ht => vkWidth_le (le_trans hTv ht))
    (fun s t hs hst => vkWidth_anti (le_trans hTv hs) hst)
    (fun β γ' hγ' _ hβ => hγ₀ β γ' (le_trans hTγ hγ') hβ)
  exact ⟨T₀, C, hT4, hTv, hC, hbound⟩

/-- **Low heights by compactness.**  For every `T` there is a strip `1 − c₀ ≤ σ ≤ 9/8`,
`|γ| ≤ T`, free of zeros of `L(s, χ)`, on which `‖L'/L‖ ≤ M₀`. -/
theorem exists_LFunction_logDeriv_low (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (T : ℝ) :
    ∃ c₀ M₀ : ℝ, 0 < c₀ ∧ 0 ≤ M₀ ∧ ∀ σ γ : ℝ, |γ| ≤ T → 1 - c₀ ≤ σ → σ ≤ 9 / 8 →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (γ : ℂ) * I) ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (γ : ℂ) * I)‖ ≤ M₀ := by
  set f : ℂ → ℂ := DirichletCharacter.LFunction χ with hfdef
  have hf : Differentiable ℂ f := DirichletCharacter.differentiable_LFunction hχ
  set K : Set ℂ := Set.Icc (1 : ℝ) (9 / 8) ×ℂ Set.Icc (-T) T with hKdef
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hU : IsOpen {s : ℂ | f s ≠ 0} := isOpen_ne_fun hf.continuous continuous_const
  have hKU : K ⊆ {s : ℂ | f s ≠ 0} := by
    intro s hs
    have hre : s.re ∈ Set.Icc (1 : ℝ) (9 / 8) := (Complex.mem_reProdIm.mp hs).1
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre.1
  obtain ⟨dl, hdl, hsub⟩ := hKc.exists_cthickening_subset_open hU hKU
  have hK'c : IsCompact (cthickening dl K) := hKc.cthickening
  have hderiv : Continuous (deriv f) := (hf.contDiff (n := 1)).continuous_deriv le_rfl
  have hcont : ContinuousOn (logDeriv f) (cthickening dl K) := by
    intro s hs
    have hfs : f s ≠ 0 := hsub hs
    have h : ContinuousAt (fun x => deriv f x / f x) s :=
      hderiv.continuousAt.div hf.continuous.continuousAt hfs
    exact h.continuousWithinAt
  obtain ⟨M, hM⟩ := hK'c.exists_bound_of_continuousOn hcont
  refine ⟨dl, max M 0, hdl, le_max_right _ _, fun σ γ hγ hσ1 hσ2 => ?_⟩
  have hK : (((max σ 1 : ℝ) : ℂ) + (γ : ℂ) * I) ∈ K := by
    rw [hKdef, Complex.mem_reProdIm]
    have hre : ((((max σ 1 : ℝ) : ℂ) + (γ : ℂ) * I)).re = max σ 1 := by simp
    have him : ((((max σ 1 : ℝ) : ℂ) + (γ : ℂ) * I)).im = γ := by simp
    rw [hre, him]
    have hg := abs_le.mp hγ
    exact ⟨⟨le_max_right _ _, max_le hσ2 (by norm_num)⟩, ⟨hg.1, hg.2⟩⟩
  have hmem : (σ : ℂ) + (γ : ℂ) * I ∈ cthickening dl K := by
    refine mem_cthickening_of_dist_le _ (((max σ 1 : ℝ) : ℂ) + (γ : ℂ) * I) dl K hK ?_
    rw [dist_eq_norm]
    have hdiff : (σ : ℂ) + (γ : ℂ) * I - (((max σ 1 : ℝ) : ℂ) + (γ : ℂ) * I)
        = (((σ - max σ 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · have : max σ 1 ≤ σ + dl := max_le (by linarith) (by linarith)
      linarith
    · linarith [le_max_left σ 1, hdl]
  exact ⟨hsub hmem, le_trans (hM _ hmem) (le_max_left _ _)⟩

/-- `vkWidth t → 0`. -/
theorem eventually_vkWidth_le {c : ℝ} (hc : 0 < c) : ∀ᶠ t : ℝ in atTop, vkWidth t ≤ c := by
  have hlim : Tendsto (fun t : ℝ => Real.log t ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp Real.tendsto_log_atTop
  have hev := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < c * 10 ^ 8))
  filter_upwards [hev, eventually_ge_atTop vkThreshold] with t ht hvt
  have h := vkWidth_le_log_pow hvt
  rw [neg_div] at h
  have h2 : Real.log t ^ (-(2 / 3 : ℝ)) / 10 ^ 8 ≤ c := by
    rw [div_le_iff₀ (by norm_num)]
    exact ht.le
  linarith

/-- **`L'/L` in the strip `1 − ε(Y+1)/2 ≤ σ ≤ 9/8`, `|γ| ≤ Y`.**  For a nonprincipal character `χ`
there are `C > 0` and `Y₀ ≥ e^e` such that for every `Y ≥ Y₀`, `L(·, χ)` has no zero there and
`‖L'/L(σ + iγ, χ)‖ ≤ C log Y / ε(Y + 1)`. -/
theorem exists_LFunction_logDeriv_strip (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C Y₀ : ℝ, 0 < C ∧ vkThreshold ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∀ σ γ : ℝ, |γ| ≤ Y →
      1 - vkWidth (Y + 1) / 2 ≤ σ → σ ≤ 9 / 8 →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (γ : ℂ) * I) ≠ 0 ∧
        ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (γ : ℂ) * I)‖
          ≤ C * Real.log Y / vkWidth (Y + 1) := by
  obtain ⟨T₀, C₁, hT4, hTv, hC₁, hhigh⟩ := exists_logDeriv_LFunction_vk χ hχ
  obtain ⟨c₀, M₀, hc₀, hM₀, hlow⟩ := exists_LFunction_logDeriv_low χ hχ (T₀ + 1)
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.mp (eventually_vkWidth_le (by positivity : 0 < 2 * c₀))
  refine ⟨C₁ + M₀ + 1, max (max (T₀ + 1) t₁) vkThreshold, by positivity, le_max_right _ _, ?_⟩
  intro Y hY σ γ hγ hσ1 hσ2
  have hYT : T₀ + 1 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hYt : t₁ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hYv : vkThreshold ≤ Y := le_trans (le_max_right _ _) hY
  have hY1v : vkThreshold ≤ Y + 1 := by linarith
  obtain ⟨hlY, -⟩ := one_le_log_log_of_vkThreshold_le hYv
  have hwY0 : 0 < vkWidth (Y + 1) := vkWidth_pos hY1v
  have hwY1 : vkWidth (Y + 1) ≤ 1 / 80 := vkWidth_le hY1v
  have hwYc : vkWidth (Y + 1) ≤ 2 * c₀ := ht₁ (Y + 1) (by linarith)
  have hratio : 1 ≤ Real.log Y / vkWidth (Y + 1) := by
    rw [le_div_iff₀ hwY0]; linarith
  have hCge : ∀ B : ℝ, 0 ≤ B → B ≤ C₁ + M₀ + 1 → B ≤ (C₁ + M₀ + 1) * Real.log Y / vkWidth (Y + 1) := by
    intro B hB0 hBC
    rw [mul_div_assoc]
    calc B = B * 1 := (mul_one B).symm
      _ ≤ (C₁ + M₀ + 1) * (Real.log Y / vkWidth (Y + 1)) :=
          mul_le_mul hBC hratio (by norm_num) (by positivity)
  rcases lt_or_ge |γ| (T₀ + 1) with hsmall | hbig
  · obtain ⟨hne, hb⟩ := hlow σ γ hsmall.le (by linarith) hσ2
    exact ⟨hne, le_trans hb (hCge M₀ hM₀ (by linarith))⟩
  · have hγv : vkThreshold ≤ |γ| + 1 := by linarith
    have hanti : vkWidth (Y + 1) ≤ vkWidth (|γ| + 1) := vkWidth_anti hγv (by linarith)
    obtain ⟨hne, hb⟩ := hhigh σ γ hbig (by linarith) hσ2
    refine ⟨hne, le_trans hb ?_⟩
    have hγ0 : 0 < |γ| := by linarith
    have hlogγ : Real.log |γ| ≤ Real.log Y := Real.log_le_log hγ0 hγ
    have hlogγ0 : 0 ≤ Real.log |γ| := Real.log_nonneg (by linarith)
    have hstep : C₁ * Real.log |γ| / vkWidth (|γ| + 1) ≤ C₁ * Real.log Y / vkWidth (Y + 1) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hlogγ hC₁.le) hwY0 hanti
    have hstep2 : C₁ * Real.log Y / vkWidth (Y + 1) ≤ (C₁ + M₀ + 1) * Real.log Y / vkWidth (Y + 1) := by
      refine div_le_div_of_nonneg_right ?_ hwY0.le
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith

end

end GaloisForLFunctions.MatomakiRadziwill
