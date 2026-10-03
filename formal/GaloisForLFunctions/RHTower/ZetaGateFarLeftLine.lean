import GaloisForLFunctions.RHTower.ZetaGateRectangleLeftLine
import GaloisForLFunctions.RHTower.SmoothDyadicZetaReflection

/-!
# Product-AFE left-line remainders on `Re w = −(2j+1)`

The rectangle argument of `ZetaGateRectangleLeftLine` moves the left lines of the smoothed and dual
diagonals to any depth `Re w = −(2j+1)`.  The `χ` poles of the dual integrand lie on the two
horizontal lines `Im w = ±τ`, outside the rectangle `|Im w| ≤ |τ|/2`, and the far line keeps the
`χ` arguments strictly between the odd integers `2j+1` and `2j+3`.

* `χ(z + 2) = χ(z) · 4π²/(−(1+z)z)` gives `‖χ(σ+it)‖ ≤ C(1+|t|)^{−(σ−½)}` on
  `2j + 29/20 ≤ σ ≤ 2j + 3/2` (`exists_norm_zetaChi_le_farLine`) and a polynomial bound on
  `−½ ≤ σ ≤ 2j + 3/2` above height two (`exists_norm_zetaChi_le_poly_far`).
* `‖smoothLeft‖ ≤ K (x/c)^{−(2j+1)}` (`exists_norm_smoothLeft_le_far`).
* `‖dualLeft‖ ≤ K (cx)^{2j+1} (1+|τ|)^{−2(2j+1−d)}` for `|τ| ≥ 4`, `cx ≥ 1`
  (`exists_norm_dualLeft_le_far`).
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower.ZetaGateProductAFE

noncomputable section

/-! ## `χ` on far vertical strips -/

/-- `Γ_ℝ(1 − s)` has no pole for `2j + 1 < Re s < 2j + 3`. -/
theorem gammaℝ_one_sub_ne_zero_of_re_far (j : ℕ) {s : ℂ} (h1 : 2 * (j : ℝ) + 1 < s.re)
    (h3 : s.re < 2 * (j : ℝ) + 3) : Gammaℝ (1 - s) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have hre := congrArg Complex.re hn
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero] at hre
  norm_num at hre
  have ha : (j : ℝ) < n := by linarith
  have hb : (n : ℝ) < j + 1 := by linarith
  have ha' : j < n := by exact_mod_cast ha
  have hb' : n < j + 1 := by exact_mod_cast hb
  omega

/-- **`χ` above height two on `½ ≤ Re s ≤ 3/2`.** -/
theorem exists_norm_zetaChi_le_of_two_le_abs_wide :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 → 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ (-(σ - 1 / 2)) := by
  obtain ⟨c, C', hc, hC', hratio⟩ :=
    GaloisForLFunctions.RHTower.exists_twoSided_gamma_vertical_ratio (a₁ := 3 / 4) (δ₁ := 1)
      (by norm_num) (by norm_num)
  refine ⟨3 * Real.pi / c, by positivity, fun σ t hσ1 hσ2 ht => ?_⟩
  have he0 : 0 ≤ σ - 1 / 2 := by linarith
  have he1 : σ - 1 / 2 ≤ 1 := by linarith
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  set τ : ℝ := |t| / 2 with hτ
  have hτ1 : 1 ≤ τ := by rw [hτ]; linarith
  have hτ0 : 0 < τ := by linarith
  have hhalf : (1 - s) / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [hs] at this
    rw [this, abs_zero] at ht
    linarith
  have hadd : (1 - s) / 2 + 1 = ((((3 - σ) / 2 : ℝ)) : ℂ) + (((-t / 2 : ℝ)) : ℂ) * I := by
    rw [hs]; push_cast; ring
  have hden : s / 2 = (((σ / 2 : ℝ)) : ℂ) + (((t / 2 : ℝ)) : ℂ) * I := by
    rw [hs]; push_cast; ring
  have hG1 := Complex.Gamma_add_one ((1 - s) / 2) hhalf
  rw [hadd] at hG1
  have hnum : ‖Complex.Gamma ((1 - s) / 2)‖
      = ‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
          / ‖(1 - s) / 2‖ := by
    have hn0 : ‖(1 - s) / 2‖ ≠ 0 := norm_ne_zero_iff.mpr hhalf
    rw [eq_div_iff hn0, mul_comm, ← norm_mul, ← hG1, norm_Gamma_re_add_abs_im]
    congr 3
    · push_cast; ring
    · rw [hτ, abs_div, abs_neg, abs_two]
  have hden' : ‖Complex.Gamma (s / 2)‖ = ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
    rw [hden, norm_Gamma_re_add_abs_im, hτ, abs_div, abs_two]
  have hr := (hratio (σ / 2) ((3 - 2 * σ) / 2) τ (by linarith) (by linarith) (by linarith)
    (by linarith) hτ1).1
  have hGa : 0 < ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hτ0 (σ / 2))
  have hGb : 0 < ‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hτ0 _)
  set Gb := ‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖ with hGbdef
  set Ga := ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ with hGadef
  have hquot : Gb / Ga ≤ τ ^ ((3 - 2 * σ) / 2) / c := by
    rw [div_le_div_iff₀ hGa hc]
    rw [le_div_iff₀ hGb] at hr
    have hτpow : τ ^ (-((3 - 2 * σ) / 2)) * τ ^ ((3 - 2 * σ) / 2) = 1 := by
      rw [← Real.rpow_add hτ0]; simp
    have key : c * τ ^ (-((3 - 2 * σ) / 2)) * Gb * τ ^ ((3 - 2 * σ) / 2) = Gb * c := by
      calc c * τ ^ (-((3 - 2 * σ) / 2)) * Gb * τ ^ ((3 - 2 * σ) / 2)
          = Gb * c * (τ ^ (-((3 - 2 * σ) / 2)) * τ ^ ((3 - 2 * σ) / 2)) := by ring
        _ = Gb * c := by rw [hτpow, mul_one]
    rw [← key]
    calc c * τ ^ (-((3 - 2 * σ) / 2)) * Gb * τ ^ ((3 - 2 * σ) / 2)
        ≤ Ga * τ ^ ((3 - 2 * σ) / 2) := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = τ ^ ((3 - 2 * σ) / 2) * Ga := by ring
  have hnorm_half : τ ≤ ‖(1 - s) / 2‖ := by
    have h2 : ‖(1 - s) / 2‖ = ‖1 - s‖ / 2 := by rw [norm_div]; norm_num
    have h := Complex.abs_im_le_norm (1 - s)
    have him : (1 - s).im = -t := by simp [hs]
    rw [him, abs_neg] at h
    rw [h2, hτ]
    linarith
  rw [norm_zetaChi_eq s, hnum, hden']
  have hsre : s.re = σ := by simp [hs]
  rw [hsre]
  have hπ : Real.pi ^ (σ - 1 / 2) ≤ Real.pi := by
    calc Real.pi ^ (σ - 1 / 2) ≤ Real.pi ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) he1
      _ = Real.pi := Real.rpow_one _
  have hτexp : τ ^ ((3 - 2 * σ) / 2) / τ = τ ^ (-(σ - 1 / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hτ0]
    congr 1; ring
  have hτ3 : τ ^ (-(σ - 1 / 2)) ≤ 3 * (1 + |t|) ^ (-(σ - 1 / 2)) := by
    have h1 : (1 + |t|) / 3 ≤ τ := by rw [hτ]; linarith
    have h2 : τ ^ (-(σ - 1 / 2)) ≤ ((1 + |t|) / 3) ^ (-(σ - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
    rw [Real.div_rpow hpos.le (by norm_num)] at h2
    have h3 : (3 : ℝ) ^ (-(σ - 1 / 2)) ≥ 1 / 3 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
        (show -(1 : ℝ) ≤ -(σ - 1 / 2) by linarith)
      rw [Real.rpow_neg_one] at this
      linarith [show (3 : ℝ)⁻¹ = 1 / 3 by norm_num]
    have h4 : 0 ≤ (1 + |t|) ^ (-(σ - 1 / 2)) := by positivity
    calc τ ^ (-(σ - 1 / 2)) ≤ (1 + |t|) ^ (-(σ - 1 / 2)) / (3 : ℝ) ^ (-(σ - 1 / 2)) := h2
      _ ≤ (1 + |t|) ^ (-(σ - 1 / 2)) / (1 / 3) :=
          div_le_div_of_nonneg_left h4 (by norm_num) h3
      _ = 3 * (1 + |t|) ^ (-(σ - 1 / 2)) := by ring
  calc Real.pi ^ (σ - 1 / 2)
        * (‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
            / ‖(1 - s) / 2‖)
        / ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖
      = Real.pi ^ (σ - 1 / 2)
          * (‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
            / ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖) / ‖(1 - s) / 2‖ := by ring
    _ ≤ Real.pi * (τ ^ ((3 - 2 * σ) / 2) / c) / τ := by
        have hq0 : 0 ≤ ‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
            / ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by positivity
        calc Real.pi ^ (σ - 1 / 2)
              * (‖Complex.Gamma (((((σ / 2) + (3 - 2 * σ) / 2 : ℝ)) : ℂ) + (τ : ℂ) * I)‖
                / ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖) / ‖(1 - s) / 2‖
            ≤ Real.pi * (τ ^ ((3 - 2 * σ) / 2) / c) / ‖(1 - s) / 2‖ := by
              gcongr
          _ ≤ Real.pi * (τ ^ ((3 - 2 * σ) / 2) / c) / τ := by
              apply div_le_div_of_nonneg_left (by positivity) hτ0 hnorm_half
    _ = (Real.pi / c) * (τ ^ ((3 - 2 * σ) / 2) / τ) := by ring
    _ = (Real.pi / c) * τ ^ (-(σ - 1 / 2)) := by rw [hτexp]
    _ ≤ (Real.pi / c) * (3 * (1 + |t|) ^ (-(σ - 1 / 2))) :=
        mul_le_mul_of_nonneg_left hτ3 (by positivity)
    _ = (3 * Real.pi / c) * (1 + |t|) ^ (-(σ - 1 / 2)) := by ring

/-- **The two-step recursion.**  `‖χ(z + 2)‖ ≤ ‖χ(z)‖ · 4π²/(Im z)²` for `Re z > −2` and
`|Im z| ≥ 1`. -/
theorem norm_zetaChi_add_two_le {z : ℂ} (hre : -2 < z.re) (him : 1 ≤ |z.im|) :
    ‖zetaChi (z + 2)‖ ≤ ‖zetaChi z‖ * (4 * Real.pi ^ 2 / z.im ^ 2) := by
  have hz1 : z + 2 ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    rw [this, abs_zero] at him
    linarith
  have hz2 : z + 2 ≠ 2 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    rw [this, abs_zero] at him
    linarith
  have hΓ : Gammaℝ (z + 2) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hrec := zetaChi_sub_two hz1 hz2 hΓ
  rw [show z + 2 - 2 = z by ring, show (1 : ℂ) - (z + 2) = -(1 + z) by ring] at hrec
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have habs : 0 < |z.im| := by linarith
  have him2 : 0 < z.im ^ 2 := by rw [← sq_abs]; positivity
  have hprod : z.im ^ 2 ≤ ‖1 + z‖ * ‖z‖ := by
    have h1 : |z.im| ≤ ‖1 + z‖ := by
      have := Complex.abs_im_le_norm (1 + z)
      simpa using this
    have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    calc z.im ^ 2 = |z.im| * |z.im| := by rw [sq, abs_mul_abs_self]
      _ ≤ ‖1 + z‖ * ‖z‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  have h4 : ‖(4 : ℂ) * (Real.pi : ℂ) ^ 2‖ = 4 * Real.pi ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    norm_num
  have hn : ‖zetaChi z‖ = ‖zetaChi (z + 2)‖ * (‖1 + z‖ * ‖z‖ / (4 * Real.pi ^ 2)) := by
    rw [hrec, norm_mul, norm_div, norm_mul, norm_neg, h4]
  have hratio : 1 ≤ (‖1 + z‖ * ‖z‖ / (4 * Real.pi ^ 2)) * (4 * Real.pi ^ 2 / z.im ^ 2) := by
    rw [div_mul_div_comm, one_le_div (by positivity)]
    have := mul_le_mul_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2)
    linarith
  rw [hn]
  calc ‖zetaChi (z + 2)‖ = ‖zetaChi (z + 2)‖ * 1 := (mul_one _).symm
    _ ≤ ‖zetaChi (z + 2)‖ * ((‖1 + z‖ * ‖z‖ / (4 * Real.pi ^ 2)) * (4 * Real.pi ^ 2 / z.im ^ 2)) :=
        mul_le_mul_of_nonneg_left hratio (norm_nonneg _)
    _ = _ := by ring

/-- **`χ` decays on the far strips `½ + 2j ≤ Re s ≤ 3/2 + 2j` above height two.** -/
theorem exists_norm_zetaChi_le_far_of_two_le_abs (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 → 2 ≤ |t| →
      ‖zetaChi (((σ + 2 * j : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ C * (1 + |t|) ^ (-(σ + 2 * j - 1 / 2)) := by
  induction j with
  | zero =>
    obtain ⟨C, hC, h⟩ := exists_norm_zetaChi_le_of_two_le_abs_wide
    exact ⟨C, hC, fun σ t h1 h2 ht => by simpa using h σ t h1 h2 ht⟩
  | succ j ih =>
    obtain ⟨C, hC, h⟩ := ih
    refine ⟨C * (9 * Real.pi ^ 2), by positivity, fun σ t h1 h2 ht => ?_⟩
    set z : ℂ := ((σ + 2 * j : ℝ) : ℂ) + (t : ℂ) * I with hz
    have hzre : z.re = σ + 2 * j := by simp [hz]
    have hzim : z.im = t := by simp [hz]
    have hshift : (((σ + 2 * ((j + 1 : ℕ) : ℝ) : ℝ)) : ℂ) + (t : ℂ) * I = z + 2 := by
      rw [hz]; push_cast; ring
    rw [hshift]
    have hrec := norm_zetaChi_add_two_le (z := z)
      (by rw [hzre]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith) (by rw [hzim]; linarith)
    rw [hzim] at hrec
    refine hrec.trans ?_
    have hpos : (0 : ℝ) < 1 + |t| := by positivity
    have ht2 : 0 < t ^ 2 := by
      have : 0 < |t| := by linarith
      rw [← sq_abs]; positivity
    have hinv : 4 * Real.pi ^ 2 / t ^ 2 ≤ 9 * Real.pi ^ 2 * (1 + |t|) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hpos.le, show (1 + |t|) ^ (2 : ℝ) = (1 + |t|) ^ 2 by norm_cast,
        ← div_eq_mul_inv, div_le_div_iff₀ ht2 (by positivity)]
      have hsq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      rw [hsq]
      have : (1 + |t|) ^ 2 ≤ (9 / 4) * |t| ^ 2 := by nlinarith
      have hp : 0 ≤ Real.pi ^ 2 := by positivity
      nlinarith
    have hexp : (1 + |t|) ^ (-(σ + 2 * j - 1 / 2)) * (1 + |t|) ^ (-(2 : ℝ))
        = (1 + |t|) ^ (-(σ + 2 * ((j + 1 : ℕ) : ℝ) - 1 / 2)) := by
      rw [← Real.rpow_add hpos]
      congr 1
      push_cast
      ring
    calc ‖zetaChi z‖ * (4 * Real.pi ^ 2 / t ^ 2)
        ≤ (C * (1 + |t|) ^ (-(σ + 2 * j - 1 / 2))) * (9 * Real.pi ^ 2 * (1 + |t|) ^ (-(2 : ℝ))) :=
          mul_le_mul (h σ t h1 h2 ht) hinv (by positivity) (by positivity)
      _ = C * (9 * Real.pi ^ 2) * ((1 + |t|) ^ (-(σ + 2 * j - 1 / 2))
            * (1 + |t|) ^ (-(2 : ℝ))) := by ring
      _ = C * (9 * Real.pi ^ 2) * (1 + |t|) ^ (-(σ + 2 * ((j + 1 : ℕ) : ℝ) - 1 / 2)) := by
          rw [hexp]

/-- **`χ` is polynomially bounded on `−½ ≤ Re s ≤ 2j + 3/2` above height two.** -/
theorem exists_norm_zetaChi_le_poly_far (j : ℕ) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, -(1 / 2) ≤ σ → σ ≤ 2 * j + 3 / 2 → 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ M := by
  induction j with
  | zero =>
    obtain ⟨C₁, M₁, hC₁, h₁⟩ := exists_norm_zetaChi_strip_le 1
    obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_zetaChi_le_of_two_le_abs_wide
    refine ⟨C₁ + C₂, M₁, by positivity, fun σ t hσ1 hσ2 ht => ?_⟩
    have h1t : 1 ≤ (1 + |t|) ^ M₁ := one_le_pow₀ (by linarith [abs_nonneg t])
    rcases le_or_gt σ (1 / 2) with hσ | hσ
    · have := h₁ σ t (by push_cast; linarith) hσ ht
      calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₁ * (1 + |t|) ^ M₁ := this
        _ ≤ (C₁ + C₂) * (1 + |t|) ^ M₁ :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · have := h₂ σ t hσ.le (by push_cast at hσ2; linarith) ht
      have hle : (1 + |t|) ^ (-(σ - 1 / 2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by linarith)
      calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C₂ * (1 + |t|) ^ (-(σ - 1 / 2)) := this
        _ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left hle hC₂
        _ ≤ (C₁ + C₂) * (1 + |t|) ^ M₁ := by nlinarith
  | succ j ih =>
    obtain ⟨C, M, hC, h⟩ := ih
    refine ⟨C * Real.pi ^ 2 + C, M, by positivity, fun σ t hσ1 hσ2 ht => ?_⟩
    have hP : 0 ≤ C * (1 + |t|) ^ M := by positivity
    rcases le_or_gt σ (2 * j + 3 / 2) with hσ | hσ
    · calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ M := h σ t hσ1 hσ ht
        _ ≤ (C * Real.pi ^ 2 + C) * (1 + |t|) ^ M := by
            have : 0 ≤ C * Real.pi ^ 2 * (1 + |t|) ^ M := by positivity
            nlinarith
    · set z : ℂ := (((σ - 2 : ℝ)) : ℂ) + (t : ℂ) * I with hz
      have hzre : z.re = σ - 2 := by simp [hz]
      have hzim : z.im = t := by simp [hz]
      have hshift : (σ : ℂ) + (t : ℂ) * I = z + 2 := by rw [hz]; push_cast; ring
      rw [hshift]
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hrec := norm_zetaChi_add_two_le (z := z) (by rw [hzre]; linarith)
        (by rw [hzim]; linarith)
      rw [hzim] at hrec
      have hz' := h (σ - 2) t (by linarith) (by push_cast at hσ2; linarith) ht
      have ht2 : 4 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
      have hfac : 4 * Real.pi ^ 2 / t ^ 2 ≤ Real.pi ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [sq_nonneg Real.pi]
      calc ‖zetaChi (z + 2)‖ ≤ ‖zetaChi z‖ * (4 * Real.pi ^ 2 / t ^ 2) := hrec
        _ ≤ (C * (1 + |t|) ^ M) * Real.pi ^ 2 :=
            mul_le_mul hz' hfac (by positivity) hP
        _ ≤ (C * Real.pi ^ 2 + C) * (1 + |t|) ^ M := by nlinarith

/-- **`χ` on the far line strip `2j + 29/20 ≤ Re s ≤ 2j + 3/2`, at every height.** -/
theorem exists_norm_zetaChi_le_farLine (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 2 * j + 29 / 20 ≤ σ → σ ≤ 2 * j + 3 / 2 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ (-(σ - 1 / 2)) := by
  obtain ⟨CA, hCA, hA⟩ := exists_norm_zetaChi_le_far_of_two_le_abs j
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_on_rect (f := zetaChi) (a := 2 * j + 29 / 20)
    (b := 2 * j + 3 / 2) (c := 2) (fun σ t hσ1 hσ2 _ => by
      have hG : Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I)) ≠ 0 :=
        gammaℝ_one_sub_ne_zero_of_re_far j (by simp; linarith) (by simp; linarith)
      exact (zetaChi_analyticAt hG).continuousAt)
  refine ⟨CA + 3 ^ (2 * j + 1) * B, by positivity, fun σ t hσ1 hσ2 => ?_⟩
  have hpos : (0 : ℝ) < 1 + |t| := by positivity
  have h0 : 0 ≤ (1 + |t|) ^ (-(σ - 1 / 2)) := by positivity
  rcases le_or_gt 2 |t| with ht | ht
  · have h := hA (σ - 2 * j) t (by linarith) (by linarith) ht
    rw [show σ - 2 * (j : ℝ) + 2 * j = σ by ring] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) h0
  · have h := hB σ t hσ1 hσ2 ht.le
    have hlow : (3 : ℝ) ^ (-((2 * j + 1 : ℕ) : ℝ)) ≤ (1 + |t|) ^ (-(σ - 1 / 2)) := by
      calc (3 : ℝ) ^ (-((2 * j + 1 : ℕ) : ℝ)) ≤ (3 : ℝ) ^ (-(σ - 1 / 2)) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
        _ ≤ (1 + |t|) ^ (-(σ - 1 / 2)) :=
            Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
    have h3 : (3 : ℝ) ^ (2 * j + 1) * (3 : ℝ) ^ (-((2 * j + 1 : ℕ) : ℝ)) = 1 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, mul_inv_cancel₀ (by positivity)]
    calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B := h
      _ = 3 ^ (2 * j + 1) * B * (3 : ℝ) ^ (-((2 * j + 1 : ℕ) : ℝ)) := by
          rw [mul_comm (3 ^ (2 * j + 1)) B, mul_assoc, h3, mul_one]
      _ ≤ 3 ^ (2 * j + 1) * B * (1 + |t|) ^ (-(σ - 1 / 2)) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ (CA + 3 ^ (2 * j + 1) * B) * (1 + |t|) ^ (-(σ - 1 / 2)) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCA) h0

/-! ## `ζ` on far left strips -/

/-- **`ζ` is polynomially bounded on `−(4j+3) ≤ Re s ≤ ¾`, at every height.** -/
theorem exists_norm_riemannZeta_le_farStrip (j : ℕ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, -(4 * (j : ℝ) + 3) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨Cz, N, hCz, hz⟩ := exists_bound_norm_riemannZeta_strip (4 * (j : ℝ) + 3)
  obtain ⟨B, hB0, hB⟩ := exists_norm_le_on_rect (f := riemannZeta) (a := -(4 * (j : ℝ) + 3))
    (b := 3 / 4) (c := 1) (fun σ t _ hσ2 _ => by
      have hne : (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      exact (differentiableAt_riemannZeta hne).continuousAt)
  refine ⟨Cz + B, N, by positivity, fun σ t hσ1 hσ2 => ?_⟩
  have h1 : 1 ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  have hP : 0 ≤ (1 + |t|) ^ N := by positivity
  rcases le_or_gt 1 |t| with ht | ht
  · have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h := hz σ t (by rw [abs_le]; constructor <;> linarith) ht
    have hpow : |t| ^ N ≤ (1 + |t|) ^ N := pow_le_pow_left₀ (abs_nonneg t) (by linarith) N
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cz * |t| ^ N := h
      _ ≤ Cz * (1 + |t|) ^ N := mul_le_mul_of_nonneg_left hpow hCz
      _ ≤ (Cz + B) * (1 + |t|) ^ N := mul_le_mul_of_nonneg_right (by linarith) hP
  · have h := hB σ t hσ1 hσ2 ht.le
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ B := h
      _ ≤ (Cz + B) * 1 := by linarith
      _ ≤ (Cz + B) * (1 + |t|) ^ N := mul_le_mul_of_nonneg_left h1 (by positivity)

/-! ## The Gaussian kernel far to the left -/

theorem norm_smoothAFEGaussianKernel_farLine_le {A : ℝ} (hA : 1 ≤ A) (t : ℝ) :
    ‖smoothAFEGaussianKernel ((((-A : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ Real.exp (A ^ 2) * Real.exp (-(t ^ 2)) := by
  rw [norm_smoothAFEGaussianKernel_eq_contour]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  have hnorm : 1 ≤ ‖(((-A : ℝ) : ℂ)) + (t : ℂ) * I‖ := by
    have := Complex.abs_re_le_norm ((((-A : ℝ) : ℂ)) + (t : ℂ) * I)
    rw [show ((((-A : ℝ) : ℂ)) + (t : ℂ) * I).re = -A by simp, abs_neg,
      abs_of_pos (by linarith : (0 : ℝ) < A)] at this
    linarith
  calc Real.exp ((-A) ^ 2 - t ^ 2) / ‖(((-A : ℝ) : ℂ)) + (t : ℂ) * I‖
      ≤ Real.exp ((-A) ^ 2 - t ^ 2) / 1 :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hnorm
    _ = Real.exp (A ^ 2) * Real.exp (-(t ^ 2)) := by
        rw [div_one, show (-A) ^ 2 - t ^ 2 = A ^ 2 + -(t ^ 2) by ring, Real.exp_add]

theorem norm_smoothAFEGaussianKernel_horizontal_far_le {A u T ε : ℝ} (hu1 : -A ≤ u) (hu2 : u ≤ 0)
    (hT : 1 ≤ T) (hε : ε = 1 ∨ ε = -1) :
    ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ Real.exp (A ^ 2) * Real.exp (-(T ^ 2)) := by
  have hεsq : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  rw [norm_smoothAFEGaussianKernel_eq_contour]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
  have hnorm : 1 ≤ ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)
    rw [show ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I).im = ε * T by simp, abs_mul, hεabs, one_mul,
      abs_of_pos (by linarith : (0 : ℝ) < T)] at this
    linarith
  have hu : u ^ 2 ≤ A ^ 2 := by nlinarith
  calc Real.exp (u ^ 2 - (ε * T) ^ 2) / ‖(u : ℂ) + ((ε * T : ℝ) : ℂ) * I‖
      ≤ Real.exp (u ^ 2 - (ε * T) ^ 2) / 1 :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hnorm
    _ ≤ Real.exp (A ^ 2) * Real.exp (-(T ^ 2)) := by
        rw [div_one, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [mul_pow, hεsq]
        linarith

/-! ## The smoothed diagonal on `Re w = −(2j+1)` -/

/-- The depth `2j + 1` of the far left line. -/
def farDepth (j : ℕ) : ℝ := 2 * j + 1

theorem one_le_farDepth (j : ℕ) : 1 ≤ farDepth j := by
  unfold farDepth
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem one_add_abs_two_mul_pow_le (N : ℕ) (t : ℝ) :
    (1 + |2 * t|) ^ N ≤ 2 ^ N * (1 + |t|) ^ N := by
  have h : 1 + |2 * t| ≤ 2 * (1 + |t|) := by rw [abs_mul, abs_two]; linarith
  calc (1 + |2 * t|) ^ N ≤ (2 * (1 + |t|)) ^ N := pow_le_pow_left₀ (by positivity) h N
    _ = 2 ^ N * (1 + |t|) ^ N := mul_pow _ _ _

/-- The smoothed diagonal integrand on `Re w = −(2j+1)`, `9/20 ≤ σ₀ ≤ ½`. -/
theorem norm_smoothDiagonalIntegrand_far_le (j : ℕ) {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 9 / 20 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hζ : ∀ σ t : ℝ, -(4 * (j : ℝ) + 3) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N)
    (t : ℝ) :
    ‖smoothDiagonalIntegrand σ₀ c x ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (C * 2 ^ N * Real.exp (farDepth j ^ 2) * (x / c) ^ (-farDepth j))
          * ((1 + |t|) ^ N * Real.exp (-(t ^ 2))) := by
  have hA : farDepth j = 2 * j + 1 := rfl
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold smoothDiagonalIntegrand
  rw [norm_mul, norm_mul]
  have harg : (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I))
      = ((2 * σ₀ - 2 * farDepth j : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hz : ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I))‖
      ≤ C * (2 ^ N * (1 + |t|) ^ N) := by
    rw [harg]
    refine (hζ _ (2 * t) (by rw [hA]; linarith) (by rw [hA]; linarith)).trans ?_
    exact mul_le_mul_of_nonneg_left (one_add_abs_two_mul_pow_le N t) hC
  have hp : ‖((x / c : ℝ) : ℂ) ^ ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I)‖
      = (x / c) ^ (-farDepth j) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hc)]
    simp
  have hk := norm_smoothAFEGaussianKernel_farLine_le (one_le_farDepth j) t
  calc ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I))‖
        * ‖((x / c : ℝ) : ℂ) ^ ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I)‖
        * ‖smoothAFEGaussianKernel ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (C * (2 ^ N * (1 + |t|) ^ N)) * (x / c) ^ (-farDepth j)
          * (Real.exp (farDepth j ^ 2) * Real.exp (-(t ^ 2))) := by
        rw [hp]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hz (by positivity)) hk (norm_nonneg _)
          (by positivity)
    _ = (C * 2 ^ N * Real.exp (farDepth j ^ 2) * (x / c) ^ (-farDepth j))
          * ((1 + |t|) ^ N * Real.exp (-(t ^ 2))) := by ring

theorem integrable_smoothDiagonalIntegrand_far (j : ℕ) {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hσ0 : 9 / 20 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) :
    Integrable (fun t : ℝ =>
      smoothDiagonalIntegrand σ₀ c x ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I)) := by
  obtain ⟨C, N, hC0, hζ⟩ := exists_norm_riemannZeta_le_farStrip j
  have h1 := one_le_farDepth j
  have hcont := continuous_smoothDiagonalIntegrand_line (σ₀ := σ₀) hc hx (u := -farDepth j)
    (by linarith) (by linarith)
  refine Integrable.mono' ((integrable_one_add_abs_pow_mul_exp_neg_sq N).const_mul
    (C * 2 ^ N * Real.exp (farDepth j ^ 2) * (x / c) ^ (-farDepth j)))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  exact norm_smoothDiagonalIntegrand_far_le j hc hx hσ0 hσ1 hC0 hζ t

/-- The smoothed diagonal integrand on a horizontal edge `u ± iT`, `−(2j+1) ≤ u ≤ −1/4`. -/
theorem norm_smoothDiagonalIntegrand_horizontal_far_le (j : ℕ) {σ₀ c x : ℝ} (hc : 0 < c)
    (hx : 0 < x) (hσ0 : 9 / 20 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hζ : ∀ σ t : ℝ, -(4 * (j : ℝ) + 3) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N)
    {u T : ℝ} (hu1 : -farDepth j ≤ u) (hu2 : u ≤ -(1 / 4)) (hT : 1 ≤ T) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ‖smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (C * max ((x / c) ^ (-farDepth j)) ((x / c) ^ (-(1 / 4 : ℝ)))
          * Real.exp (farDepth j ^ 2)) * ((1 + 2 * T) ^ N * Real.exp (-(T ^ 2))) := by
  have hA : farDepth j = 2 * j + 1 := rfl
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  unfold smoothDiagonalIntegrand
  rw [norm_mul, norm_mul]
  have harg : (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
      = ((2 * σ₀ + 2 * u : ℝ) : ℂ) + ((2 * (ε * T) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have habs : |2 * (ε * T)| = 2 * T := by
    rw [abs_mul, abs_mul, hεabs, abs_two, abs_of_pos (by linarith : (0 : ℝ) < T)]
    ring
  have hz : ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ C * (1 + 2 * T) ^ N := by
    rw [harg]
    have h := hζ (2 * σ₀ + 2 * u) (2 * (ε * T)) (by rw [hA] at hu1; linarith) (by linarith)
    rwa [habs] at h
  have hp : ‖((x / c : ℝ) : ℂ) ^ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ max ((x / c) ^ (-farDepth j)) ((x / c) ^ (-(1 / 4 : ℝ))) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hc)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    exact rpow_le_max_of_mem_Icc (div_pos hx hc) hu1 hu2
  have hk := norm_smoothAFEGaussianKernel_horizontal_far_le (A := farDepth j) hu1 (by linarith) hT
    hε
  calc ‖riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
        * ‖((x / c : ℝ) : ℂ) ^ ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        * ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ (C * (1 + 2 * T) ^ N) * max ((x / c) ^ (-farDepth j)) ((x / c) ^ (-(1 / 4 : ℝ)))
          * (Real.exp (farDepth j ^ 2) * Real.exp (-(T ^ 2))) :=
        mul_le_mul (mul_le_mul hz hp (norm_nonneg _) (by positivity)) hk (norm_nonneg _)
          (by positivity)
    _ = (C * max ((x / c) ^ (-farDepth j)) ((x / c) ^ (-(1 / 4 : ℝ)))
          * Real.exp (farDepth j ^ 2)) * ((1 + 2 * T) ^ N * Real.exp (-(T ^ 2))) := by ring

theorem tendsto_smoothDiagonalIntegrand_horizontal_far (j : ℕ) {σ₀ c x : ℝ} (hc : 0 < c)
    (hx : 0 < x) (hσ0 : 9 / 20 ≤ σ₀) (hσ1 : σ₀ ≤ 1 / 2) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    Tendsto (fun T : ℝ => ∫ u : ℝ in (-farDepth j : ℝ)..(-(1 / 4) : ℝ),
      smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, N, hC, hζ⟩ := exists_norm_riemannZeta_le_farStrip j
  have h1 := one_le_farDepth j
  set B : ℝ := C * max ((x / c) ^ (-farDepth j)) ((x / c) ^ (-(1 / 4 : ℝ)))
    * Real.exp (farDepth j ^ 2) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hlen : |(-(1 / 4) : ℝ) - (-farDepth j)| = farDepth j - 1 / 4 := by
    rw [abs_of_nonneg (by linarith)]; ring
  have hmajor : Tendsto (fun T : ℝ => ((farDepth j - 1 / 4) * B * 2 ^ N)
      * ((1 / 2 + T) ^ N * Real.exp (-(T ^ 2)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_shifted_pow_mul_exp_neg_sq (1 / 2) N).const_mul ((farDepth j - 1 / 4) * B * 2 ^ N)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hbound : ∀ u ∈ Set.uIoc (-farDepth j : ℝ) (-(1 / 4) : ℝ),
      ‖smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        ≤ B * ((1 + 2 * T) ^ N * Real.exp (-(T ^ 2))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith)] at hu
    exact norm_smoothDiagonalIntegrand_horizontal_far_le j hc hx hσ0 hσ1 hC hζ hu.1.le hu.2 hT hε
  calc ‖∫ u : ℝ in (-farDepth j : ℝ)..(-(1 / 4) : ℝ),
        smoothDiagonalIntegrand σ₀ c x ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ B * ((1 + 2 * T) ^ N * Real.exp (-(T ^ 2))) * |(-(1 / 4) : ℝ) - (-farDepth j)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ((farDepth j - 1 / 4) * B * 2 ^ N) * ((1 / 2 + T) ^ N * Real.exp (-(T ^ 2))) := by
        rw [hlen, show 1 + 2 * T = 2 * (1 / 2 + T) by ring, mul_pow]
        ring

theorem differentiableOn_smoothDiagonalIntegrand_farStrip (j : ℕ) {σ₀ c x : ℝ} (hc : 0 < c)
    (hx : 0 < x) (hσ1 : σ₀ ≤ 1 / 2) :
    DifferentiableOn ℂ (smoothDiagonalIntegrand σ₀ c x)
      (HTGeometry.verticalStrip (-farDepth j) (-(1 / 4))) := by
  intro w hw
  rw [HTGeometry.mem_verticalStrip] at hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith [hw.2]
  have hne : (((2 * σ₀ : ℝ) : ℂ) + 2 * w) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith [hw.2]
  apply DifferentiableAt.differentiableWithinAt
  unfold smoothDiagonalIntegrand smoothAFEGaussianKernel
  have hz : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * w)) w :=
    (differentiableAt_riemannZeta hne).comp w (by fun_prop)
  have hp : DifferentiableAt ℂ (fun w : ℂ => ((x / c : ℝ) : ℂ) ^ w) w :=
    (differentiableAt_id).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (div_pos hx hc).ne'))
  have hk : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w ^ 2) / w) w :=
    ((Complex.differentiable_exp.comp (differentiable_id.pow 2)) w).div differentiableAt_id hw0
  exact (hz.mul hp).mul hk

/-- **The smoothed-diagonal remainder on `Re w = −(2j+1)`.** -/
theorem smoothLeft_eq_far (j : ℕ) {σ₀ c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hσ0 : 9 / 20 ≤ σ₀)
    (hσ1 : σ₀ ≤ 1 / 2) :
    smoothLeft σ₀ c x = (1 / (2 * Real.pi)) •
      ∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I) := by
  unfold smoothLeft
  congr 1
  have h1 := one_le_farDepth j
  have hbot := tendsto_smoothDiagonalIntegrand_horizontal_far j hc hx hσ0 hσ1 (ε := -1)
    (Or.inr rfl)
  have htop := tendsto_smoothDiagonalIntegrand_horizontal_far j hc hx hσ0 hσ1 (ε := 1)
    (Or.inl rfl)
  simp only [neg_one_mul, one_mul] at hbot htop
  exact integral_vertical_line_eq_of_horizontal_tendsto (by linarith)
    (differentiableOn_smoothDiagonalIntegrand_farStrip j hc hx hσ1)
    (integrable_smoothDiagonalIntegrand_far j hc hx hσ0 hσ1)
    (integrable_smoothDiagonalIntegrand_left hc hx (by linarith) hσ1) hbot htop

/-- **`‖smoothLeft‖ ≤ K (x/c)^{−(2j+1)}`**, uniformly in `σ₀ ∈ [9/20, ½]`, `c`, `x`. -/
theorem exists_norm_smoothLeft_le_far (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ₀ c x : ℝ, 9 / 20 ≤ σ₀ → σ₀ ≤ 1 / 2 → 0 < c → 0 < x →
      ‖smoothLeft σ₀ c x‖ ≤ K * (x / c) ^ (-farDepth j) := by
  obtain ⟨C, N, hC0, hζ⟩ := exists_norm_riemannZeta_le_farStrip j
  have hG0 : 0 ≤ ∫ t : ℝ, (1 + |t|) ^ N * Real.exp (-(t ^ 2)) :=
    integral_nonneg fun t => by positivity
  refine ⟨(1 / (2 * Real.pi)) * (C * 2 ^ N * Real.exp (farDepth j ^ 2)
    * ∫ t : ℝ, (1 + |t|) ^ N * Real.exp (-(t ^ 2))), by positivity,
    fun σ₀ c x hσ0 hσ1 hc hx => ?_⟩
  rw [smoothLeft_eq_far j hc hx hσ0 hσ1, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have hbound := fun t : ℝ => norm_smoothDiagonalIntegrand_far_le j hc hx hσ0 hσ1 hC0 hζ t
  have hnorm : ‖∫ t : ℝ,
        smoothDiagonalIntegrand σ₀ c x ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (C * 2 ^ N * Real.exp (farDepth j ^ 2) * (x / c) ^ (-farDepth j))
          * ∫ t : ℝ, (1 + |t|) ^ N * Real.exp (-(t ^ 2)) := by
    calc ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, ‖smoothDiagonalIntegrand σ₀ c x ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (C * 2 ^ N * Real.exp (farDepth j ^ 2) * (x / c) ^ (-farDepth j))
            * ((1 + |t|) ^ N * Real.exp (-(t ^ 2))) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            ((integrable_one_add_abs_pow_mul_exp_neg_sq N).const_mul _)
            (Filter.Eventually.of_forall fun t => hbound t)
      _ = _ := by rw [integral_const_mul]
  calc (1 / (2 * Real.pi))
        * ‖∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x ((((-farDepth j : ℝ) : ℂ)) + (t : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * ((C * 2 ^ N * Real.exp (farDepth j ^ 2) * (x / c) ^ (-farDepth j))
          * ∫ t : ℝ, (1 + |t|) ^ N * Real.exp (-(t ^ 2))) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-! ## The dual diagonal on `Re w = −(2j+1)` -/

theorem natCast_four_mul_add_two_eq (j : ℕ) : ((4 * j + 2 : ℕ) : ℝ) = 2 * farDepth j := by
  unfold farDepth
  push_cast
  ring

/-- `χ(½ − d ± iτ − w)` is analytic at `w` when `2j + 1 < ½ − d − Re w < 2j + 3`. -/
theorem analyticAt_zetaChi_displaced_sub_of_re_far (j : ℕ) {d τ : ℝ} {w : ℂ}
    (h1 : 2 * (j : ℝ) + 1 < 1 / 2 - d - w.re) (h3 : 1 / 2 - d - w.re < 2 * (j : ℝ) + 3) :
    AnalyticAt ℂ (fun w : ℂ => zetaChi (displacedLinePt d τ - w)) w := by
  have hre : (displacedLinePt d τ - w).re = 1 / 2 - d - w.re := by
    simp only [displacedLinePt, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one,
      add_zero]
  have hG : Gammaℝ (1 - (displacedLinePt d τ - w)) ≠ 0 :=
    gammaℝ_one_sub_ne_zero_of_re_far j (by rw [hre]; exact h1) (by rw [hre]; exact h3)
  exact (zetaChi_analyticAt hG).comp ((analyticAt_const).sub analyticAt_id)

theorem continuous_dualDiagonalIntegrand_farLine (j : ℕ) {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) :
    Continuous (fun v : ℝ =>
      dualDiagonalIntegrand d c x τ ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I)) := by
  have hA : farDepth j = 2 * j + 1 := rfl
  rw [continuous_iff_continuousAt]
  intro v
  have hline : ContinuousAt (fun v : ℝ => (((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I) v := by
    fun_prop
  set w : ℂ := (((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I with hw
  have hwre : w.re = -farDepth j := by simp [hw]
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hwre] at this
    simp at this
    linarith [one_le_farDepth j]
  have hc1 := analyticAt_zetaChi_displaced_sub_of_re_far j (d := d) (τ := τ) (w := w)
    (by rw [hwre, hA]; linarith) (by rw [hwre, hA]; linarith)
  have hc2 := analyticAt_zetaChi_displaced_sub_of_re_far j (d := d) (τ := -τ) (w := w)
    (by rw [hwre, hA]; linarith) (by rw [hwre, hA]; linarith)
  have hm := analyticAt_smoothAFEMellinIntegrand (mul_pos hc hx) hw0
  have hne : (((1 + 2 * d : ℝ) : ℂ) + 2 * w) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero, Complex.one_re] at this
    rw [hwre] at this
    linarith [one_le_farDepth j]
  have hz : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * w)) w :=
    (differentiableAt_riemannZeta hne).comp w (by fun_prop)
  have hG : ContinuousAt (dualDiagonalIntegrand d c x τ) w := by
    unfold dualDiagonalIntegrand carrierIntegrand
    exact ((hc1.continuousAt.mul hc2.continuousAt).mul hm.continuousAt).mul hz.continuousAt
  exact ContinuousAt.comp (g := dualDiagonalIntegrand d c x τ)
    (f := fun v : ℝ => (((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I) hG hline

/-- The dual diagonal integrand on `Re w = −(2j+1)`, `0 < d ≤ 1/20`.  Both `χ` factors sit on
`Re s = 2j + 3/2 − d`. -/
theorem norm_dualDiagonalIntegrand_far_le (j : ℕ) {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) {Cχ Cζ : ℝ} {N : ℕ} (hCχ : 0 ≤ Cχ)
    (hCζ : 0 ≤ Cζ)
    (hχ : ∀ σ t : ℝ, 2 * j + 29 / 20 ≤ σ → σ ≤ 2 * j + 3 / 2 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, -(4 * (j : ℝ) + 3) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ N)
    (v : ℝ) :
    ‖dualDiagonalIntegrand d c x τ ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ (Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * (1 + |τ|) ^ (-(2 * farDepth j - 2 * d))
          * ((1 + |v|) ^ (4 * j + 2 + N) * Real.exp (-(v ^ 2))) := by
  have hA : farDepth j = 2 * j + 1 := rfl
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have ha0 : (0 : ℝ) ≤ farDepth j - d := by rw [hA]; linarith
  unfold dualDiagonalIntegrand carrierIntegrand smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hχ' : ∀ σ : ℝ, |σ| = |τ| →
      ‖zetaChi (displacedLinePt d σ - ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I))‖
        ≤ Cχ * ((1 + |v|) ^ (farDepth j - d) * (1 + |τ|) ^ (-(farDepth j - d))) := by
    intro σ hσ
    have harg : displacedLinePt d σ - ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I)
        = ((1 / 2 - d + farDepth j : ℝ) : ℂ) + ((σ - v : ℝ) : ℂ) * I := by
      unfold displacedLinePt; push_cast; ring
    rw [harg]
    have h := hχ (1 / 2 - d + farDepth j) (σ - v) (by rw [hA]; linarith) (by rw [hA]; linarith)
    rw [show (1 / 2 - d + farDepth j - 1 / 2 : ℝ) = farDepth j - d by ring] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCχ)
    have htr := one_add_abs_sub_rpow_neg_le ha0 σ v
    refine htr.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hσ]
  have h1 := hχ' τ rfl
  have h2 := hχ' (-τ) (abs_neg τ)
  have hp : ‖((c * x : ℝ) : ℂ) ^ (-((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I))‖
      = (c * x) ^ farDepth j := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hc hx)]
    simp
  have hk := norm_smoothAFEGaussianKernel_farLine_le (one_le_farDepth j) v
  have hz : ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I))‖
      ≤ Cζ * (2 ^ N * (1 + |v|) ^ N) := by
    have harg : (((1 + 2 * d : ℝ) : ℂ) + 2 * ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I))
        = ((1 + 2 * d - 2 * farDepth j : ℝ) : ℂ) + ((2 * v : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg]
    refine (hζ _ (2 * v) (by rw [hA]; linarith) (by rw [hA]; linarith)).trans ?_
    exact mul_le_mul_of_nonneg_left (one_add_abs_two_mul_pow_le N v) hCζ
  have hva : (1 + |v|) ^ (farDepth j - d) * (1 + |v|) ^ (farDepth j - d)
      ≤ (1 + |v|) ^ (4 * j + 2) := by
    rw [← Real.rpow_add (by positivity)]
    calc (1 + |v|) ^ (farDepth j - d + (farDepth j - d))
        ≤ (1 + |v|) ^ (((4 * j + 2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v])
            (by rw [natCast_four_mul_add_two_eq]; linarith)
      _ = (1 + |v|) ^ (4 * j + 2) := Real.rpow_natCast _ _
  have hτa : (1 + |τ|) ^ (-(farDepth j - d)) * (1 + |τ|) ^ (-(farDepth j - d))
      = (1 + |τ|) ^ (-(2 * farDepth j - 2 * d)) := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  calc ‖zetaChi (displacedLinePt d τ - ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I))‖
        * ‖zetaChi (displacedLinePt d (-τ) - ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I))‖
        * (‖((c * x : ℝ) : ℂ) ^ (-((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I))‖
          * ‖smoothAFEGaussianKernel ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I)‖)
        * ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ)
            + 2 * ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I))‖
      ≤ (Cχ * ((1 + |v|) ^ (farDepth j - d) * (1 + |τ|) ^ (-(farDepth j - d))))
          * (Cχ * ((1 + |v|) ^ (farDepth j - d) * (1 + |τ|) ^ (-(farDepth j - d))))
          * ((c * x) ^ farDepth j * (Real.exp (farDepth j ^ 2) * Real.exp (-(v ^ 2))))
          * (Cζ * (2 ^ N * (1 + |v|) ^ N)) := by
        rw [hp]
        gcongr
    _ = (Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * ((1 + |τ|) ^ (-(farDepth j - d)) * (1 + |τ|) ^ (-(farDepth j - d)))
          * (((1 + |v|) ^ (farDepth j - d) * (1 + |v|) ^ (farDepth j - d)) * (1 + |v|) ^ N
              * Real.exp (-(v ^ 2))) := by ring
    _ ≤ (Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * ((1 + |τ|) ^ (-(farDepth j - d)) * (1 + |τ|) ^ (-(farDepth j - d)))
          * ((1 + |v|) ^ (4 * j + 2) * (1 + |v|) ^ N * Real.exp (-(v ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right hva (by positivity)
    _ = (Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * (1 + |τ|) ^ (-(2 * farDepth j - 2 * d))
          * ((1 + |v|) ^ (4 * j + 2 + N) * Real.exp (-(v ^ 2))) := by
        rw [hτa, pow_add]; ring

theorem integrable_dualDiagonalIntegrand_far (j : ℕ) {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) :
    Integrable (fun v : ℝ =>
      dualDiagonalIntegrand d c x τ ((((-farDepth j : ℝ) : ℂ)) + (v : ℂ) * I)) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_farLine j
  obtain ⟨Cζ, N, hCζ, hζ⟩ := exists_norm_riemannZeta_le_farStrip j
  refine Integrable.mono' ((integrable_one_add_abs_pow_mul_exp_neg_sq (4 * j + 2 + N)).const_mul
    ((Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
      * (1 + |τ|) ^ (-(2 * farDepth j - 2 * d))))
    (continuous_dualDiagonalIntegrand_farLine j hd hd20 hc hx).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  exact norm_dualDiagonalIntegrand_far_le j hd hd20 hc hx hCχ hCζ hχ hζ v

/-! ## The dual diagonal: the far rectangle -/

/-- The dual integrand on a horizontal edge `u ± i|τ|/2`, `−(2j+1) ≤ u ≤ −1/4`, `|τ| ≥ 4`. -/
theorem norm_dualDiagonalIntegrand_horizontal_far_le (j : ℕ) {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hcx : 1 ≤ c * x) {CA Cζ : ℝ} {M N : ℕ}
    (hCA : 0 ≤ CA)
    (hA : ∀ σ t : ℝ, -(1 / 2) ≤ σ → σ ≤ 2 * j + 3 / 2 → 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ CA * (1 + |t|) ^ M)
    (hζ : ∀ σ t : ℝ, -(4 * (j : ℝ) + 3) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ N)
    (hτ : 4 ≤ |τ|) {u : ℝ} (hu1 : -farDepth j ≤ u) (hu2 : u ≤ -(1 / 4)) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖
      ≤ (CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * ((1 + |τ|) ^ (2 * M + N) * Real.exp (-((|τ| / 2) ^ 2))) := by
  have hAdef : farDepth j = 2 * j + 1 := rfl
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  unfold dualDiagonalIntegrand carrierIntegrand smoothAFEMellinIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have hχ' : ∀ σ : ℝ, |σ| = |τ| →
      ‖zetaChi (displacedLinePt d σ - ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
        ≤ CA * (2 ^ M * (1 + |τ|) ^ M) := by
    intro σ hσ
    have harg : displacedLinePt d σ - ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)
        = ((1 / 2 - d - u : ℝ) : ℂ) + ((σ - ε * (|τ| / 2) : ℝ) : ℂ) * I := by
      unfold displacedLinePt; push_cast; ring
    rw [harg]
    have hεT : |ε * (|τ| / 2)| = |τ| / 2 := by
      rw [abs_mul, hεabs, one_mul, abs_of_pos (by linarith : (0 : ℝ) < |τ| / 2)]
    have him : 2 ≤ |σ - ε * (|τ| / 2)| := by
      have h1 : |σ| ≤ |σ - ε * (|τ| / 2)| + |ε * (|τ| / 2)| := by
        have := abs_add_le (σ - ε * (|τ| / 2)) (ε * (|τ| / 2))
        simpa using this
      rw [hεT, hσ] at h1
      linarith
    have himle : |σ - ε * (|τ| / 2)| ≤ 2 * |τ| := by
      have := abs_sub (σ) (ε * (|τ| / 2))
      rw [hεT, hσ] at this
      linarith
    have h := hA (1 / 2 - d - u) (σ - ε * (|τ| / 2)) (by linarith) (by rw [hAdef] at hu1; linarith)
      him
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCA)
    calc (1 + |σ - ε * (|τ| / 2)|) ^ M ≤ (2 * (1 + |τ|)) ^ M :=
          pow_le_pow_left₀ (by positivity) (by linarith) M
      _ = 2 ^ M * (1 + |τ|) ^ M := mul_pow _ _ _
  have h1 := hχ' τ rfl
  have h2 := hχ' (-τ) (abs_neg τ)
  have hp : ‖((c * x : ℝ) : ℂ) ^ (-((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
      ≤ (c * x) ^ farDepth j := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hc hx)]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
    exact Real.rpow_le_rpow_of_exponent_le hcx (by linarith)
  have hk := norm_smoothAFEGaussianKernel_horizontal_far_le (A := farDepth j) (u := u)
    (T := |τ| / 2) hu1 (by linarith) (by linarith) hε
  have hz : ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ)
      + 2 * ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖ ≤ Cζ * (1 + |τ|) ^ N := by
    have harg : (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))
        = ((1 + 2 * d + 2 * u : ℝ) : ℂ) + ((2 * (ε * (|τ| / 2)) : ℝ) : ℂ) * I := by
      push_cast; ring
    have habs : |2 * (ε * (|τ| / 2))| = |τ| := by
      rw [abs_mul, abs_mul, hεabs, abs_two, abs_of_pos (by linarith : (0 : ℝ) < |τ| / 2)]
      ring
    rw [harg]
    have h := hζ (1 + 2 * d + 2 * u) (2 * (ε * (|τ| / 2))) (by rw [hAdef] at hu1; linarith)
      (by linarith)
    rwa [habs] at h
  calc ‖zetaChi (displacedLinePt d τ - ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
        * ‖zetaChi (displacedLinePt d (-τ) - ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
        * (‖((c * x : ℝ) : ℂ) ^ (-((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
          * ‖smoothAFEGaussianKernel ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖)
        * ‖riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I))‖
      ≤ (CA * (2 ^ M * (1 + |τ|) ^ M)) * (CA * (2 ^ M * (1 + |τ|) ^ M))
          * ((c * x) ^ farDepth j * (Real.exp (farDepth j ^ 2) * Real.exp (-((|τ| / 2) ^ 2))))
          * (Cζ * (1 + |τ|) ^ N) := by
        gcongr
    _ = (CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * ((1 + |τ|) ^ (2 * M + N) * Real.exp (-((|τ| / 2) ^ 2))) := by
        rw [show (4 : ℝ) ^ M = 2 ^ M * 2 ^ M by rw [← mul_pow]; norm_num, pow_add,
          show 2 * M = M + M by ring, pow_add]
        ring

/-- `(1+y)^L e^{−y²/4} ≤ (L+k)! e² (1+y)^{−k}` for `y ≥ 0`. -/
theorem one_add_pow_mul_exp_neg_half_sq_le (L k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ L * Real.exp (-((y / 2) ^ 2))
      ≤ ((L + k).factorial * Real.exp 2) * (1 + y) ^ (-(k : ℝ)) := by
  have hy1 : (0 : ℝ) < 1 + y := by linarith
  have hfact := Real.pow_div_factorial_le_exp (1 + y) hy1.le (L + k)
  have hf0 : (0 : ℝ) < (L + k).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [div_le_iff₀ hf0] at hfact
  have hexp : Real.exp (1 + y) * Real.exp (-((y / 2) ^ 2)) ≤ Real.exp 2 := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (y - 2)]
  rw [Real.rpow_neg hy1.le, Real.rpow_natCast]
  have hk : 0 < (1 + y) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hk]
  calc (1 + y) ^ L * Real.exp (-((y / 2) ^ 2)) * (1 + y) ^ k
      = (1 + y) ^ (L + k) * Real.exp (-((y / 2) ^ 2)) := by rw [pow_add]; ring
    _ ≤ (Real.exp (1 + y) * (L + k).factorial) * Real.exp (-((y / 2) ^ 2)) :=
        mul_le_mul_of_nonneg_right hfact (Real.exp_pos _).le
    _ = (L + k).factorial * (Real.exp (1 + y) * Real.exp (-((y / 2) ^ 2))) := by ring
    _ ≤ (L + k).factorial * Real.exp 2 := mul_le_mul_of_nonneg_left hexp hf0.le

/-- **The far rectangle step.**  On `[−(2j+1), −1/4] × [−|τ|/2, |τ|/2]` neither `χ` factor has a
pole, so the central part of `Re w = −1/4` equals that of `Re w = −(2j+1)` up to the two edges. -/
theorem norm_intervalIntegral_dualDiagonalIntegrand_left_le_far (j : ℕ) {d c x τ : ℝ}
    (hd : 0 < d) (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hτ : 4 ≤ |τ|) :
    ‖∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
        dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (y : ℂ) * I)‖
      ≤ ‖∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
          dualDiagonalIntegrand d c x τ ((((-farDepth j : ℝ) : ℂ)) + (y : ℂ) * I)‖
        + ‖∫ u : ℝ in (-farDepth j : ℝ)..(-(1 / 4) : ℝ),
          dualDiagonalIntegrand d c x τ ((u : ℂ) + ((|τ| / 2 : ℝ) : ℂ) * I)‖
        + ‖∫ u : ℝ in (-farDepth j : ℝ)..(-(1 / 4) : ℝ),
          dualDiagonalIntegrand d c x τ ((u : ℂ) + ((-(|τ| / 2) : ℝ) : ℂ) * I)‖ := by
  have h1A := one_le_farDepth j
  have hsub : DifferentiableOn ℂ (dualDiagonalIntegrand d c x τ)
      (Set.uIcc ((((-farDepth j : ℝ) : ℂ)) + ((-(|τ| / 2) : ℝ) : ℂ) * I).re
          ((((-(1 / 4) : ℝ) : ℂ)) + ((|τ| / 2 : ℝ) : ℂ) * I).re
        ×ℂ Set.uIcc ((((-farDepth j : ℝ) : ℂ)) + ((-(|τ| / 2) : ℝ) : ℂ) * I).im
          ((((-(1 / 4) : ℝ) : ℂ)) + ((|τ| / 2 : ℝ) : ℂ) * I).im) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add,
      add_zero]
    intro p hp
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hp
    obtain ⟨⟨_, hre2⟩, ⟨him1, him2⟩⟩ := hp
    have hp0 : p ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hre2
      linarith
    have himabs : |p.im| ≤ |τ| / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have him1' : p.im ≠ τ := by
      intro h
      rw [h] at himabs
      linarith
    have him2' : p.im ≠ -τ := by
      intro h
      rw [h, abs_neg] at himabs
      linarith
    have hc1 := analyticAt_zetaChi_displaced_sub_of_im (d := d) him1'
    have hc2 := analyticAt_zetaChi_displaced_sub_of_im (d := d) him2'
    have hm := analyticAt_smoothAFEMellinIntegrand (mul_pos hc hx) hp0
    have hne : (((1 + 2 * d : ℝ) : ℂ) + 2 * p) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
        Complex.im_ofNat, zero_mul, sub_zero, Complex.one_re] at this
      linarith
    have hz : DifferentiableAt ℂ (fun w : ℂ => riemannZeta (((1 + 2 * d : ℝ) : ℂ) + 2 * w)) p :=
      (differentiableAt_riemannZeta hne).comp p (by fun_prop)
    apply DifferentiableAt.differentiableWithinAt
    unfold dualDiagonalIntegrand carrierIntegrand
    exact ((hc1.differentiableAt.mul hc2.differentiableAt).mul hm.differentiableAt).mul hz
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dualDiagonalIntegrand d c x τ) _ _ hsub
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add,
    add_zero, smul_eq_mul] at hrect
  set A := ∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
    dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (y : ℂ) * I)
  set B := ∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
    dualDiagonalIntegrand d c x τ ((((-farDepth j : ℝ) : ℂ)) + (y : ℂ) * I)
  set top := ∫ u : ℝ in (-farDepth j : ℝ)..(-(1 / 4) : ℝ),
    dualDiagonalIntegrand d c x τ ((u : ℂ) + ((|τ| / 2 : ℝ) : ℂ) * I)
  set bot := ∫ u : ℝ in (-farDepth j : ℝ)..(-(1 / 4) : ℝ),
    dualDiagonalIntegrand d c x τ ((u : ℂ) + ((-(|τ| / 2) : ℝ) : ℂ) * I)
  have hAeq : I * A = I * B + top - bot := by linear_combination hrect
  have h1 : ‖A‖ = ‖I * A‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  rw [h1, hAeq]
  calc ‖I * B + top - bot‖ ≤ ‖I * B + top‖ + ‖bot‖ := norm_sub_le _ _
    _ ≤ ‖I * B‖ + ‖top‖ + ‖bot‖ := by gcongr; exact norm_add_le _ _
    _ = ‖B‖ + ‖top‖ + ‖bot‖ := by rw [norm_mul, Complex.norm_I, one_mul]

/-- The shifted centre on `Re w = −(2j+1)`. -/
theorem norm_intervalIntegral_dualDiagonalIntegrand_far_le (j : ℕ) {d c x τ : ℝ} (hd : 0 < d)
    (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hτ : 0 ≤ |τ|) {Cχ Cζ : ℝ} {N : ℕ}
    (hCχ : 0 ≤ Cχ) (hCζ : 0 ≤ Cζ)
    (hχ : ∀ σ t : ℝ, 2 * j + 29 / 20 ≤ σ → σ ≤ 2 * j + 3 / 2 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, -(4 * (j : ℝ) + 3) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ N) :
    ‖∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
        dualDiagonalIntegrand d c x τ ((((-farDepth j : ℝ) : ℂ)) + (y : ℂ) * I)‖
      ≤ (Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * (1 + |τ|) ^ (-(2 * farDepth j - 2 * d))
          * ∫ v : ℝ, (1 + |v|) ^ (4 * j + 2 + N) * Real.exp (-(v ^ 2)) := by
  have hint := integrable_dualDiagonalIntegrand_far j (τ := τ) hd hd20 hc hx
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc ‖∫ y in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
        dualDiagonalIntegrand d c x τ ((((-farDepth j : ℝ) : ℂ)) + (y : ℂ) * I)‖
      ≤ ∫ y in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
        ‖dualDiagonalIntegrand d c x τ ((((-farDepth j : ℝ) : ℂ)) + (y : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, ‖dualDiagonalIntegrand d c x τ ((((-farDepth j : ℝ) : ℂ)) + (y : ℂ) * I)‖ :=
        setIntegral_le_integral hint.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ∫ y : ℝ, ((Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * (1 + |τ|) ^ (-(2 * farDepth j - 2 * d)))
          * ((1 + |y|) ^ (4 * j + 2 + N) * Real.exp (-(y ^ 2))) :=
        integral_mono hint.norm
          ((integrable_one_add_abs_pow_mul_exp_neg_sq (4 * j + 2 + N)).const_mul _)
          (fun y => norm_dualDiagonalIntegrand_far_le j hd hd20 hc hx hCχ hCζ hχ hζ y)
    _ = _ := by rw [integral_const_mul]

/-- A horizontal edge of the far rectangle. -/
theorem norm_intervalIntegral_dualDiagonalIntegrand_horizontal_far_le (j : ℕ) {d c x τ : ℝ}
    (hd : 0 < d) (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hcx : 1 ≤ c * x) {CA Cζ : ℝ}
    {M N : ℕ} (hCA : 0 ≤ CA) (hCζ : 0 ≤ Cζ)
    (hA : ∀ σ t : ℝ, -(1 / 2) ≤ σ → σ ≤ 2 * j + 3 / 2 → 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ CA * (1 + |t|) ^ M)
    (hζ : ∀ σ t : ℝ, -(4 * (j : ℝ) + 3) ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ N)
    (hτ : 4 ≤ |τ|) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ‖∫ u : ℝ in (-farDepth j : ℝ)..(-(1 / 4) : ℝ),
        dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖
      ≤ (CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * (((2 * M + N + (4 * j + 2)).factorial * Real.exp 2)
            * (1 + |τ|) ^ (-((4 * j + 2 : ℕ) : ℝ))) * farDepth j := by
  have h1A := one_le_farDepth j
  have hbound : ∀ u ∈ Set.uIoc (-farDepth j : ℝ) (-(1 / 4)),
      ‖dualDiagonalIntegrand d c x τ ((u : ℂ) + ((ε * (|τ| / 2) : ℝ) : ℂ) * I)‖
        ≤ (CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j
          * (((2 * M + N + (4 * j + 2)).factorial * Real.exp 2)
            * (1 + |τ|) ^ (-((4 * j + 2 : ℕ) : ℝ))) := by
    intro u hu
    rw [Set.uIoc_of_le (by linarith)] at hu
    refine (norm_dualDiagonalIntegrand_horizontal_far_le j hd hd20 hc hx hcx hCA hA hζ hτ
      hu.1.le hu.2 hε).trans ?_
    have hpg := one_add_pow_mul_exp_neg_half_sq_le (2 * M + N) (4 * j + 2) (abs_nonneg τ)
    have h0 : 0 ≤ (CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * (c * x) ^ farDepth j := by
      positivity
    exact mul_le_mul_of_nonneg_left hpg h0
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans ?_
  have hlen : |(-(1 / 4) : ℝ) - (-farDepth j)| ≤ farDepth j := by
    rw [abs_of_nonneg (by linarith)]; linarith
  exact mul_le_mul_of_nonneg_left hlen (by positivity)

/-- The unshifted tails `|Im w| > |τ|/2` of the line `Re w = −1/4`, with the decay
`(1+|τ|)^{−(4j+2)}`. -/
theorem norm_setIntegral_compl_dualDiagonalIntegrand_left_le_far (j : ℕ) {d c x τ : ℝ}
    (hd : 0 < d) (hd20 : d ≤ 1 / 20) (hc : 0 < c) (hx : 0 < x) (hτ : 4 ≤ |τ|) {Cχ Cζ : ℝ}
    (hCχ : 0 ≤ Cχ) (hCζ : 0 ≤ Cζ)
    (hχ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cχ * (1 + |t|) ^ (-(σ - 1 / 2)))
    (hζ : ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 3 / 4 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cζ * (1 + |t|) ^ 2) :
    ‖∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
        dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ)
          * (2 ^ (4 * j + 2) * (1 + |τ|) ^ (-((4 * j + 2 : ℕ) : ℝ)))
          * ∫ v : ℝ, (1 + |v|) ^ (3 + (4 * j + 2)) * Real.exp (-(v ^ 2)) := by
  set k : ℕ := 4 * j + 2 with hk
  have hgint := integrable_dualDiagonalIntegrand_left (τ := τ) hd (by linarith) hc hx
  have hτ0 : (0 : ℝ) < 1 + |τ| := by positivity
  set E : ℝ := 2 ^ k * (1 + |τ|) ^ (-(k : ℝ)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hM : Integrable (fun v : ℝ => ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16))
      * (c * x) ^ (1 / 4 : ℝ) * E) * ((1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2)))) :=
    (integrable_one_add_abs_pow_mul_exp_neg_sq (3 + k)).const_mul _
  have hpt : ∀ v ∈ (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
      ‖dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
        ≤ ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * E)
          * ((1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2))) := by
    intro v hv
    have hv' : |τ| / 2 ≤ |v| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
      rcases hv with hv | hv
      · rw [abs_of_neg (show v < 0 by linarith)]; linarith
      · rw [abs_of_pos (show 0 < v by linarith)]; linarith
    have hb := norm_dualDiagonalIntegrand_left_le (τ := τ) hd (by linarith) hc hx hCχ hCζ hχ hζ v
    refine hb.trans ?_
    have hτd : (1 + |τ|) ^ (-(1 / 2 - 2 * d)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ]) (by linarith)
    have hpoly : (1 + |v|) ^ 3 ≤ E * (1 + |v|) ^ (3 + k) := by
      have hτv : 1 + |τ| ≤ 2 * (1 + |v|) := by linarith
      have hpk : (1 + |τ|) ^ k ≤ 2 ^ k * (1 + |v|) ^ k := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hτ0.le hτv k
      have hEk : E * (1 + |τ|) ^ k = 2 ^ k := by
        rw [hE, Real.rpow_neg hτ0.le, Real.rpow_natCast, mul_assoc,
          inv_mul_cancel₀ (by positivity), mul_one]
      have h1 : 1 ≤ E * (1 + |v|) ^ k := by
        have h2k : (0 : ℝ) < 2 ^ k := by positivity
        have : 2 ^ k * 1 ≤ 2 ^ k * (E * (1 + |v|) ^ k) := by
          calc 2 ^ k * 1 = E * (1 + |τ|) ^ k := by rw [hEk, mul_one]
            _ ≤ E * (2 ^ k * (1 + |v|) ^ k) := mul_le_mul_of_nonneg_left hpk hE0
            _ = 2 ^ k * (E * (1 + |v|) ^ k) := by ring
        exact le_of_mul_le_mul_left this h2k
      calc (1 + |v|) ^ 3 = (1 + |v|) ^ 3 * 1 := (mul_one _).symm
        _ ≤ (1 + |v|) ^ 3 * (E * (1 + |v|) ^ k) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = E * (1 + |v|) ^ (3 + k) := by rw [pow_add]; ring
    have hK : 0 ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) := by
      positivity
    have he : 0 ≤ Real.exp (-(v ^ 2)) := (Real.exp_pos _).le
    have h3 : 0 ≤ (1 + |v|) ^ 3 * Real.exp (-(v ^ 2)) := by positivity
    calc (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ)
          * (1 + |τ|) ^ (-(1 / 2 - 2 * d)) * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2)))
        ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * 1
            * ((1 + |v|) ^ 3 * Real.exp (-(v ^ 2))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτd hK) h3
      _ ≤ (16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * 1
            * (E * (1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hpoly he
      _ = ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * E)
            * ((1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2))) := by ring
  calc ‖∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
        dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ ∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
        ‖dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
        ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * E)
          * ((1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2))) :=
        setIntegral_mono_on hgint.norm.integrableOn hM.integrableOn measurableSet_Ioc.compl hpt
    _ ≤ ∫ v : ℝ, ((16 * Cχ * Cχ * Cζ * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ) * E)
          * ((1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2))) :=
        setIntegral_le_integral hM (Filter.Eventually.of_forall fun v => by positivity)
    _ = _ := by rw [integral_const_mul]

/-- **`‖dualLeft‖ ≤ K (cx)^{2j+1} (1+|τ|)^{−2(2j+1−d)}`** for `0 < d ≤ 1/20`, `cx ≥ 1`, `|τ| ≥ 4`:
the far rectangle step, the shifted centre, the two edges and the unshifted tails. -/
theorem exists_norm_dualLeft_le_far (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 20 → 0 < c → 0 < x → 1 ≤ c * x →
      4 ≤ |τ| →
        ‖dualLeft d c x τ‖
          ≤ K * (c * x) ^ farDepth j * (1 + |τ|) ^ (-(2 * farDepth j - 2 * d)) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_le_farLine j
  obtain ⟨CA, M, hCA, hA⟩ := exists_norm_zetaChi_le_poly_far j
  obtain ⟨Cζ, N, hCζ, hζ⟩ := exists_norm_riemannZeta_le_farStrip j
  obtain ⟨Cχl, hCχl, hχl⟩ := exists_norm_zetaChi_le_rightStrip
  obtain ⟨Cζl, hCζl, hζl⟩ := exists_norm_riemannZeta_le_leftStrip
  set k : ℕ := 4 * j + 2 with hk
  have hJ1 : 0 ≤ ∫ v : ℝ, (1 + |v|) ^ (4 * j + 2 + N) * Real.exp (-(v ^ 2)) :=
    integral_nonneg fun v => by positivity
  have hJ3 : 0 ≤ ∫ v : ℝ, (1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2)) :=
    integral_nonneg fun v => by positivity
  have h1A := one_le_farDepth j
  refine ⟨(1 / (2 * Real.pi)) * ((Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2))
      * (∫ v : ℝ, (1 + |v|) ^ (4 * j + 2 + N) * Real.exp (-(v ^ 2)))
    + 2 * ((CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2))
      * ((2 * M + N + k).factorial * Real.exp 2) * farDepth j)
    + (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * 2 ^ k
      * (∫ v : ℝ, (1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2)))), by positivity,
    fun d c x τ hd hd20 hc hx hcx hτ => ?_⟩
  have hτ0 : (0 : ℝ) < 1 + |τ| := by positivity
  have hEk : (1 + |τ|) ^ (-(k : ℝ)) ≤ (1 + |τ|) ^ (-(2 * farDepth j - 2 * d)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ])
      (by rw [hk, natCast_four_mul_add_two_eq]; linarith)
  have hP14 : (c * x) ^ (1 / 4 : ℝ) ≤ (c * x) ^ farDepth j :=
    Real.rpow_le_rpow_of_exponent_le hcx (by linarith)
  -- the four pieces
  have hrect := norm_intervalIntegral_dualDiagonalIntegrand_left_le_far j (τ := τ) hd hd20 hc hx
    hτ
  have hcen := norm_intervalIntegral_dualDiagonalIntegrand_far_le j (τ := τ) hd hd20 hc hx
    (abs_nonneg τ) hCχ hCζ hχ hζ
  have htop := norm_intervalIntegral_dualDiagonalIntegrand_horizontal_far_le j (τ := τ) hd hd20 hc
    hx hcx hCA hCζ hA hζ hτ (ε := 1) (Or.inl rfl)
  have hbot := norm_intervalIntegral_dualDiagonalIntegrand_horizontal_far_le j (τ := τ) hd hd20 hc
    hx hcx hCA hCζ hA hζ hτ (ε := -1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at htop hbot
  have htail := norm_setIntegral_compl_dualDiagonalIntegrand_left_le_far j (τ := τ) hd hd20 hc hx
    hτ hCχl hCζl hχl hζl
  have hgint := integrable_dualDiagonalIntegrand_left (τ := τ) hd (by linarith) hc hx
  have hsplit := integral_add_compl (measurableSet_Ioc (a := -(|τ| / 2)) (b := |τ| / 2)) hgint
  have hcentre : ∫ y : ℝ in (-(|τ| / 2) : ℝ)..(|τ| / 2),
      dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (y : ℂ) * I)
      = ∫ v in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
          dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I) :=
    intervalIntegral.integral_of_le (by linarith)
  rw [hcentre] at hrect
  have hdual : dualLeft d c x τ = (1 / (2 * Real.pi)) • ∫ v : ℝ,
      dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I) := rfl
  rw [hdual, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), ← hsplit]
  set E := (1 + |τ|) ^ (-(2 * farDepth j - 2 * d))
  set P := (c * x) ^ farDepth j
  have hE0 : 0 ≤ E := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hA2 : 0 ≤ (CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * P
      * ((2 * M + N + k).factorial * Real.exp 2) := by positivity
  have hedge : (CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * P
      * (((2 * M + N + (4 * j + 2)).factorial * Real.exp 2) * (1 + |τ|) ^ (-((4 * j + 2 : ℕ) : ℝ)))
      * farDepth j
      ≤ (CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * P
        * ((2 * M + N + k).factorial * Real.exp 2) * E * farDepth j := by
    have := mul_le_mul_of_nonneg_left hEk hA2
    have h0 : (0 : ℝ) ≤ farDepth j := by linarith
    calc (CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * P
          * (((2 * M + N + (4 * j + 2)).factorial * Real.exp 2)
            * (1 + |τ|) ^ (-((4 * j + 2 : ℕ) : ℝ))) * farDepth j
        = ((CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * P
          * ((2 * M + N + k).factorial * Real.exp 2)) * (1 + |τ|) ^ (-(k : ℝ)) * farDepth j := by
          rw [hk]; ring
      _ ≤ ((CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2)) * P
          * ((2 * M + N + k).factorial * Real.exp 2)) * E * farDepth j :=
          mul_le_mul_of_nonneg_right this h0
      _ = _ := by ring
  have htail' : (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * (c * x) ^ (1 / 4 : ℝ)
      * (2 ^ (4 * j + 2) * (1 + |τ|) ^ (-((4 * j + 2 : ℕ) : ℝ)))
      * (∫ v : ℝ, (1 + |v|) ^ (3 + (4 * j + 2)) * Real.exp (-(v ^ 2)))
      ≤ (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * P * (2 ^ k * E)
        * (∫ v : ℝ, (1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2))) := by
    rw [← hk]
    gcongr
  have hpieces :
      ‖(∫ v in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
          dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))
        + ∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
          dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ ((Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2))
            * (∫ v : ℝ, (1 + |v|) ^ (4 * j + 2 + N) * Real.exp (-(v ^ 2)))
          + 2 * ((CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2))
            * ((2 * M + N + k).factorial * Real.exp 2) * farDepth j)
          + (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * 2 ^ k
            * (∫ v : ℝ, (1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2)))) * P * E := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (hrect.trans (add_le_add (add_le_add hcen htop) hbot)) htail).trans ?_
    refine (add_le_add (add_le_add (add_le_add le_rfl hedge) hedge) htail').trans (le_of_eq ?_)
    ring
  calc (1 / (2 * Real.pi))
        * ‖(∫ v in Set.Ioc (-(|τ| / 2)) (|τ| / 2),
            dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I))
          + ∫ v in (Set.Ioc (-(|τ| / 2)) (|τ| / 2))ᶜ,
            dualDiagonalIntegrand d c x τ ((((-(1 / 4) : ℝ) : ℂ)) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (((Cχ * Cχ * Cζ * 2 ^ N * Real.exp (farDepth j ^ 2))
            * (∫ v : ℝ, (1 + |v|) ^ (4 * j + 2 + N) * Real.exp (-(v ^ 2)))
          + 2 * ((CA * CA * Cζ * 4 ^ M * Real.exp (farDepth j ^ 2))
            * ((2 * M + N + k).factorial * Real.exp 2) * farDepth j)
          + (16 * Cχl * Cχl * Cζl * Real.exp (1 / 16)) * 2 ^ k
            * (∫ v : ℝ, (1 + |v|) ^ (3 + k) * Real.exp (-(v ^ 2)))) * P * E) :=
        mul_le_mul_of_nonneg_left hpieces (by positivity)
    _ = _ := by ring

end

end RHTower.ZetaGateProductAFE
