import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound
import GaloisForLFunctions.HTGeometry.GammaSymmetricSplitDecay
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# The convexity bound for the Riemann zeta function

For `0 < η ≤ 1/2` there is a constant `C` with

`‖ζ(σ + it)‖ ≤ C t^{(1+η−σ)/2}` for `−η ≤ σ ≤ 1+η` and `t ≥ 8`.

The proof is the Phragmén–Lindelöf principle in the strip `−η ≤ Re s ≤ 1+η`, applied to the bounded
function `F(s) = (s−1)ζ(s) · exp((s − it₀)²) · t₀^{−(3+η−s)/2}`.  The Gaussian factor localises at
height `t₀`; the power of the fixed real number `t₀` has modulus `t₀^{−(3+η−Re s)/2}`, which depends
on `Re s` only.  On the right edge `‖ζ‖ ≤ 1 + 1/η`.  On the left edge the functional equation gives
`ζ(−η+it) = χ(−η+it) ζ(1+η−it)`, and `‖χ(−η+it)‖ ≤ 2e^{3/2}|t|^{1/2+η}` follows from the sharp
vertical Gamma ratio `‖Γ(a+iy)‖ ≤ y^{a−b} e^{6(b−a)/y} ‖Γ(b+iy)‖` (`0 < a ≤ b`, `y ≥ 4`).
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- `(1+|x|)² e^{−x²} ≤ 2`. -/
theorem one_add_abs_sq_mul_exp_neg_sq_le (x : ℝ) : (1 + |x|) ^ 2 * Real.exp (-x ^ 2) ≤ 2 := by
  have h1 : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
    nlinarith [sq_abs x, sq_nonneg (1 - |x|)]
  have h2 : 1 + x ^ 2 ≤ Real.exp (x ^ 2) := by linarith [Real.add_one_le_exp (x ^ 2)]
  calc (1 + |x|) ^ 2 * Real.exp (-x ^ 2) ≤ 2 * Real.exp (x ^ 2) * Real.exp (-x ^ 2) := by
        gcongr; linarith
    _ = 2 := by rw [mul_assoc, ← Real.exp_add]; simp

/-- For `t₀ ≥ 1` and `0 ≤ p ≤ 2`: `(|t|/t₀)^p ≤ (1 + |t − t₀|)²`. -/
theorem abs_div_rpow_le_one_add_sq {t t₀ p : ℝ} (ht₀ : 1 ≤ t₀) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    (|t| / t₀) ^ p ≤ (1 + |t - t₀|) ^ 2 := by
  have ht₀0 : 0 < t₀ := by linarith
  have habs : |t| ≤ t₀ + |t - t₀| := by
    have := abs_add_le (t - t₀) t₀
    rw [sub_add_cancel, abs_of_pos ht₀0] at this; linarith
  have hB : |t| / t₀ ≤ 1 + |t - t₀| := by
    rw [div_le_iff₀ ht₀0]
    nlinarith [abs_nonneg (t - t₀)]
  have hB1 : 1 ≤ 1 + |t - t₀| := by linarith [abs_nonneg (t - t₀)]
  calc (|t| / t₀) ^ p ≤ (1 + |t - t₀|) ^ p :=
        Real.rpow_le_rpow (by positivity) hB hp0
    _ ≤ (1 + |t - t₀|) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB1 hp2
    _ = (1 + |t - t₀|) ^ 2 := by norm_cast

/-- **Sharp vertical Gamma ratio.**  For `0 < a ≤ b` and `y ≥ 4`,
`‖Γ(a+iy)‖ ≤ y^{a−b} e^{6(b−a)/y} ‖Γ(b+iy)‖`. -/
theorem norm_Gamma_vertical_le_rpow_mul {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b) (hy : 4 ≤ y) :
    ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖
      ≤ y ^ (a - b) * Real.exp (6 * (b - a) / y) * ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ := by
  have hs := HTGeometry.log_norm_Gamma_split_le (X₀ := b) (X₁ := a) (Y := y) (d := 0) ha hab hy
    (by simp; linarith)
  simp only [add_zero, sub_zero, abs_zero] at hs
  have hne : ∀ x : ℝ, Complex.Gamma ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro x
    apply Complex.Gamma_ne_zero
    intro m hm
    have h := congrArg Complex.im hm
    simp at h
    linarith
  have ha' := norm_pos_iff.mpr (hne a)
  have hb' := norm_pos_iff.mpr (hne b)
  have hy0 : 0 < y := by linarith
  have hlog : Real.log ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖
      ≤ Real.log (y ^ (a - b) * Real.exp (6 * (b - a) / y)
          * ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖) := by
    rw [Real.log_mul (by positivity) hb'.ne', Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_rpow hy0, Real.log_exp]
    have e : 12 * (b - a) / y = 2 * (6 * (b - a) / y) := by ring
    linarith
  exact (Real.log_le_log_iff ha' (by positivity)).mp hlog

/-- **The functional-equation factor on a line left of the strip.**  For `0 < η ≤ 1/2` and `t ≥ 8`,
`‖χ(−η+it)‖ ≤ 2e^{3/2} t^{1/2+η}`. -/
theorem norm_zetaChi_left_line_le {η t : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (ht : 8 ≤ t) :
    ‖zetaChi (((-η : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 2 * Real.exp (3 / 2) * t ^ (1 / 2 + η) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = t / 2 := ⟨_, rfl⟩
  have hy4 : 4 ≤ y := by rw [hy]; linarith
  have hy0 : 0 < y := by linarith
  have ht0 : 0 < t := by linarith
  rw [norm_zetaChi_eq]
  have hzre : (((-η : ℝ) : ℂ) + (t : ℂ) * I).re = -η := by simp
  have hnum : (1 - (((-η : ℝ) : ℂ) + (t : ℂ) * I)) / 2
      = (starRingEnd ℂ) ((((1 + η) / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    rw [hy]; simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
  have hden : (((-η : ℝ) : ℂ) + (t : ℂ) * I) / 2 + 1 = (((1 - η / 2 : ℝ)) : ℂ) + (y : ℂ) * I := by
    rw [hy]; push_cast; ring
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (((-η : ℝ) : ℂ) + (t : ℂ) * I) / 2 := ⟨_, rfl⟩
  rw [← hw] at hden
  rw [← hw, hzre, hnum, Complex.Gamma_conj, RCLike.norm_conj]
  have hwim : w.im = y := by rw [hw, hy]; simp
  have hw0 : w ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hwim] at this; simp at this; linarith
  have hΓne : Complex.Gamma w ≠ 0 := by
    apply Complex.Gamma_ne_zero; intro m hm
    have := congrArg Complex.im hm; rw [hwim] at this; simp at this; linarith
  have hΓw := Complex.Gamma_add_one w hw0
  rw [hden] at hΓw
  have hwnorm : ‖w‖ ≤ 2 * y := by
    rw [hw, norm_div]
    have h1 : ‖((-η : ℝ) : ℂ) + (t : ℂ) * I‖ ≤ η + t := by
      refine (norm_add_le _ _).trans ?_
      simp [abs_of_pos hη, abs_of_pos ht0]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, hy]; linarith
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hGw : ‖Complex.Gamma w‖ = ‖Complex.Gamma ((((1 - η / 2 : ℝ)) : ℂ) + (y : ℂ) * I)‖ / ‖w‖ := by
    rw [hΓw, norm_mul]; field_simp
  have hratio := norm_Gamma_vertical_le_rpow_mul (a := (1 + η) / 2) (b := 1 - η / 2) (y := y)
    (by positivity) (by linarith) hy4
  have hGB : 0 < ‖Complex.Gamma ((((1 - η / 2 : ℝ)) : ℂ) + (y : ℂ) * I)‖ := by
    rw [hΓw]; exact norm_pos_iff.mpr (mul_ne_zero hw0 hΓne)
  have hab : (1 + η) / 2 - (1 - η / 2) = η - 1 / 2 := by ring
  have hba : 6 * (1 - η / 2 - (1 + η) / 2) / y ≤ 3 / 2 := by
    rw [div_le_iff₀ hy0]; nlinarith
  rw [hab] at hratio
  have hpi : Real.pi ^ (-η - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hpi0 : 0 < Real.pi ^ (-η - 1 / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hexp : Real.exp (6 * (1 - η / 2 - (1 + η) / 2) / y) ≤ Real.exp (3 / 2) :=
    Real.exp_le_exp.mpr hba
  have hyt : y ^ (1 / 2 + η) ≤ t ^ (1 / 2 + η) :=
    Real.rpow_le_rpow hy0.le (by rw [hy]; linarith) (by positivity)
  have hyy : y ^ (η - 1 / 2) * y = y ^ (1 / 2 + η) := by
    rw [← Real.rpow_add_one hy0.ne']; ring_nf
  rw [hGw, div_div_eq_mul_div]
  calc Real.pi ^ (-η - 1 / 2) *
        ‖Complex.Gamma ((((1 + η) / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ * ‖w‖
        / ‖Complex.Gamma ((((1 - η / 2 : ℝ)) : ℂ) + (y : ℂ) * I)‖
      ≤ 1 * (y ^ (η - 1 / 2) * Real.exp (6 * (1 - η / 2 - (1 + η) / 2) / y)
          * ‖Complex.Gamma ((((1 - η / 2 : ℝ)) : ℂ) + (y : ℂ) * I)‖) * (2 * y)
        / ‖Complex.Gamma ((((1 - η / 2 : ℝ)) : ℂ) + (y : ℂ) * I)‖ := by
        gcongr
    _ = 2 * (y ^ (η - 1 / 2) * y) * Real.exp (6 * (1 - η / 2 - (1 + η) / 2) / y) := by
        rw [div_eq_iff hGB.ne']; ring
    _ ≤ 2 * t ^ (1 / 2 + η) * Real.exp (3 / 2) := by
        rw [hyy]; gcongr
    _ = 2 * Real.exp (3 / 2) * t ^ (1 / 2 + η) := by ring

/-- `‖χ(−η+it)‖ ≤ 2e^{3/2}|t|^{1/2+η}` for `|t| ≥ 8`. -/
theorem norm_zetaChi_left_line_le_abs {η t : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (ht : 8 ≤ |t|) :
    ‖zetaChi (((-η : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 2 * Real.exp (3 / 2) * |t| ^ (1 / 2 + η) := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢; exact norm_zetaChi_left_line_le hη hη2 ht
  · have hc : (((-η : ℝ) : ℂ) + (t : ℂ) * I)
        = (starRingEnd ℂ) (((-η : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
    rw [hc, zetaChi_conj, RCLike.norm_conj, abs_of_neg h]
    rw [abs_of_neg h] at ht
    exact norm_zetaChi_left_line_le hη hη2 ht

/-- The Phragmén–Lindelöf weight `exp((s − it₀)²) · exp(−((3+η−s)/2) log t₀)`. -/
def convexityWeight (η t₀ : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((s - (t₀ : ℂ) * I) ^ 2)
    * Complex.exp (-(((3 + η : ℝ) : ℂ) - s) / 2 * (Real.log t₀ : ℂ))

theorem differentiable_convexityWeight (η t₀ : ℝ) : Differentiable ℂ (convexityWeight η t₀) := by
  unfold convexityWeight; fun_prop

theorem norm_convexityWeight (η t₀ : ℝ) (z : ℂ) :
    ‖convexityWeight η t₀ z‖
      = Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2)
        * Real.exp (-((3 + η - z.re) / 2) * Real.log t₀) := by
  unfold convexityWeight
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  congr 2
  · simp [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  · simp [Complex.mul_re]; ring

/-- On the right edge, `‖(s−1)ζ(s)‖ ≤ (1 + 1/η)(1 + |t|)`. -/
theorem norm_zetaEntire_right_edge_le {η t : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ‖zetaEntire (((1 + η : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (1 + 1 / η) * (1 + |t|) := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ((1 + η : ℝ) : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  rw [← hz]
  have hzre : z.re = 1 + η := by rw [hz]; simp
  have hz1 : z ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hzre] at this; simp at this; linarith
  rw [zetaEntire_eq hz1, norm_mul]
  have h1 : ‖z - 1‖ ≤ 1 + |t| := by
    have e : z - 1 = (η : ℂ) + (t : ℂ) * I := by rw [hz]; push_cast; ring
    rw [e]; refine (norm_add_le _ _).trans ?_
    simp [abs_of_pos hη]; linarith
  have h2 : ‖riemannZeta z‖ ≤ 1 + 1 / η := by
    have := Sieve.norm_riemannZeta_le (s := z) (by rw [hzre]; linarith)
    rw [hzre, add_sub_cancel_left] at this; exact this
  calc ‖z - 1‖ * ‖riemannZeta z‖ ≤ (1 + |t|) * (1 + 1 / η) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (1 + 1 / η) * (1 + |t|) := by ring

/-- On the left edge, `‖(s−1)ζ(s)‖ ≤ 4e^{3/2}(1 + 1/η)|t|^{3/2+η}` for `|t| ≥ 8`. -/
theorem norm_zetaEntire_left_edge_le {η t : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (ht : 8 ≤ |t|) :
    ‖zetaEntire (((-η : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ 4 * Real.exp (3 / 2) * (1 + 1 / η) * |t| ^ (3 / 2 + η) := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ((-η : ℝ) : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  have hχ := norm_zetaChi_left_line_le_abs hη hη2 ht
  rw [← hz] at hχ ⊢
  have hzre : z.re = -η := by rw [hz]; simp
  have hzim : z.im = t := by rw [hz]; simp
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  have hz1 : z ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hzre] at this; simp at this; linarith
  have hz0 : z ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hzim] at this; simp at this; exact ht0 this
  have hre1 : (1 - z).re = 1 + η := by simp [hzre]
  have hG : Complex.Gammaℝ (1 - z) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hre1]; linarith)
  rw [zetaEntire_eq hz1, norm_mul, zeta_eq_zetaChi_mul hz0 hz1 hG, norm_mul]
  have hζ : ‖riemannZeta (1 - z)‖ ≤ 1 + 1 / η := by
    have := Sieve.norm_riemannZeta_le (s := 1 - z) (by rw [hre1]; linarith)
    rw [hre1, add_sub_cancel_left] at this; exact this
  have hz1n : ‖z - 1‖ ≤ 2 * |t| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero, hzre, hzim]
    rw [abs_of_neg (by linarith)]; linarith
  have hpow : |t| ^ (3 / 2 + η) = |t| * |t| ^ (1 / 2 + η) := by
    rw [show (3 / 2 : ℝ) + η = 1 + (1 / 2 + η) by ring,
      Real.rpow_add (by positivity), Real.rpow_one]
  calc ‖z - 1‖ * (‖zetaChi z‖ * ‖riemannZeta (1 - z)‖)
      ≤ (2 * |t|) * ((2 * Real.exp (3 / 2) * |t| ^ (1 / 2 + η)) * (1 + 1 / η)) := by gcongr
    _ = 4 * Real.exp (3 / 2) * (1 + 1 / η) * (|t| * |t| ^ (1 / 2 + η)) := by ring
    _ = 4 * Real.exp (3 / 2) * (1 + 1 / η) * |t| ^ (3 / 2 + η) := by rw [hpow]

/-- Polynomial growth of `(s−1)ζ(s)` in the strip `−1/2 ≤ Re s ≤ 3/2`, `|Im s| ≥ 2`. -/
theorem norm_zetaEntire_strip_le {z : ℂ} (h1 : -1 / 2 ≤ z.re) (h2 : z.re ≤ 3 / 2)
    (him : 2 ≤ |z.im|) : ‖zetaEntire z‖ ≤ 5 * Real.exp 2 * (4 + |z.im|) ^ 3 := by
  have hz1 : z ≠ 1 := by
    intro h; rw [h] at him; simp at him; linarith
  rw [zetaEntire_eq hz1, norm_mul]
  have hζ := norm_riemannZeta_le_smoothAFE_strip (σ := z.re) (t := z.im) h1 h2 him
  rw [Complex.re_add_im] at hζ
  have hn : ‖z - 1‖ ≤ 4 + |z.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    have : |z.re - 1| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hi : 0 ≤ |z.im| := abs_nonneg _
  calc ‖z - 1‖ * ‖riemannZeta z‖
      ≤ (4 + |z.im|) * (5 * Real.exp 2 * (1 + |z.im|) * (4 + |z.im|)) :=
        mul_le_mul hn hζ (norm_nonneg _) (by positivity)
    _ ≤ (4 + |z.im|) * (5 * Real.exp 2 * (4 + |z.im|) * (4 + |z.im|)) := by
        gcongr; linarith
    _ = 5 * Real.exp 2 * (4 + |z.im|) ^ 3 := by ring

/-- `(4+x)³ ≤ 64 exp(3 exp x)` for `x ≥ 0`. -/
theorem four_add_cube_le_exp_exp {x : ℝ} (hx : 0 ≤ x) :
    (4 + x) ^ 3 ≤ 64 * Real.exp (3 * Real.exp x) := by
  have h1 : 4 + x ≤ 4 * Real.exp x := by
    have := Real.add_one_le_exp (x / 4)
    have h2 : Real.exp (x / 4) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    linarith
  have h3 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  calc (4 + x) ^ 3 ≤ (4 * Real.exp x) ^ 3 := by gcongr
    _ = 64 * Real.exp (3 * x) := by
        rw [mul_pow, ← Real.exp_nat_mul]; norm_num
    _ ≤ 64 * Real.exp (3 * Real.exp x) := by gcongr

/-- The weight on the strip is at most `e^{9/4}`. -/
theorem norm_convexityWeight_le_strip {η t₀ : ℝ} (hη2 : η ≤ 1 / 2) (ht₀ : 1 ≤ t₀) {z : ℂ}
    (h1 : -η ≤ z.re) (h2 : z.re ≤ 1 + η) :
    ‖convexityWeight η t₀ z‖ ≤ Real.exp (9 / 4) := by
  rw [norm_convexityWeight]
  have hl : 0 ≤ Real.log t₀ := Real.log_nonneg ht₀
  have ha : Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) ≤ Real.exp (9 / 4) := by
    apply Real.exp_le_exp.mpr
    have : z.re ^ 2 ≤ 9 / 4 := by nlinarith
    nlinarith [sq_nonneg (z.im - t₀)]
  have hb : Real.exp (-((3 + η - z.re) / 2) * Real.log t₀) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ (3 + η - z.re) / 2 := by linarith
    nlinarith
  calc Real.exp (z.re ^ 2 - (z.im - t₀) ^ 2) * Real.exp (-((3 + η - z.re) / 2) * Real.log t₀)
      ≤ Real.exp (9 / 4) * 1 := mul_le_mul ha hb (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (9 / 4) := mul_one _

/-- The weight on the left edge. -/
theorem norm_convexityWeight_left_edge {η t₀ t : ℝ} (ht₀ : 0 < t₀) :
    ‖convexityWeight η t₀ (((-η : ℝ) : ℂ) + (t : ℂ) * I)‖
      = Real.exp (η ^ 2) * Real.exp (-(t - t₀) ^ 2) * t₀ ^ (-(3 / 2 + η)) := by
  rw [norm_convexityWeight]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  rw [Real.rpow_def_of_pos ht₀, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The weight on the right edge. -/
theorem norm_convexityWeight_right_edge {η t₀ t : ℝ} (ht₀ : 0 < t₀) :
    ‖convexityWeight η t₀ (((1 + η : ℝ) : ℂ) + (t : ℂ) * I)‖
      = Real.exp ((1 + η) ^ 2) * Real.exp (-(t - t₀) ^ 2) / t₀ := by
  rw [norm_convexityWeight]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im]
  have e : Real.exp (-((3 + η - (1 + η + (t * 0 - 0 * 1))) / 2) * Real.log t₀) = t₀⁻¹ := by
    rw [show -((3 + η - (1 + η + (t * 0 - 0 * 1))) / 2) * Real.log t₀ = -Real.log t₀ by ring,
      Real.exp_neg, Real.exp_log ht₀]
  rw [e, div_eq_mul_inv, ← Real.exp_add]
  congr 2
  ring

/-- **The convexity bound for `ζ`.**  For `0 < η ≤ 1/2` there is `C > 0` with
`‖ζ(σ+it)‖ ≤ C t^{(1+η−σ)/2}` whenever `−η ≤ σ ≤ 1+η` and `t ≥ 8`. -/
theorem exists_norm_riemannZeta_le_convexity {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, -η ≤ σ → σ ≤ 1 + η → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ ((1 + η - σ) / 2) := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (0 : ℂ) 10).exists_bound_of_continuousOn
    (differentiable_zetaEntire.continuous.continuousOn (s := Metric.closedBall (0 : ℂ) 10))
  obtain ⟨K, hK⟩ : ∃ K, K = max K₀ 0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hK ▸ le_max_right _ _
  obtain ⟨CL, hCL⟩ : ∃ CL, CL = 8 * Real.exp (3 / 2) * (1 + 1 / η) * Real.exp (1 / 4) := ⟨_, rfl⟩
  obtain ⟨CR, hCR⟩ : ∃ CR, CR = 4 * (1 + 1 / η) * Real.exp (9 / 4) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁, C₁ = max (K * Real.exp (1 / 4)) (max CL CR) := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; exact le_max_of_le_left (by positivity)
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro σ t₀ hσ1 hσ2 ht₀
  have ht₀0 : 0 < t₀ := by linarith
  set F : ℂ → ℂ := fun z => zetaEntire z * convexityWeight η t₀ z with hFdef
  have hFd : Differentiable ℂ F :=
    differentiable_zetaEntire.mul (differentiable_convexityWeight η t₀)
  have hFn : ∀ z, ‖F z‖ = ‖zetaEntire z‖ * ‖convexityWeight η t₀ z‖ := fun z => norm_mul _ _
  -- growth in the strip
  have hgrowth : ∃ c < Real.pi / (1 + η - -η), ∃ B,
      F =O[Filter.comap (abs ∘ Complex.im) Filter.atTop
        ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (-η) (1 + η))]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, 3, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]; linarith [Real.pi_gt_three]
    · apply Asymptotics.IsBigO.of_bound (5 * Real.exp 2 * 64 * Real.exp (9 / 4))
      have hmem : {z : ℂ | 2 ≤ |z.im|} ∩ (Complex.re ⁻¹' Set.Ioo (-η) (1 + η)) ∈
          Filter.comap (abs ∘ Complex.im) Filter.atTop
            ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (-η) (1 + η)) :=
        Filter.inter_mem_inf (Filter.preimage_mem_comap (Filter.Ici_mem_atTop 2))
          (Filter.mem_principal_self _)
      filter_upwards [hmem] with z hz
      obtain ⟨hzi, hzs⟩ := hz
      simp only [Set.mem_setOf_eq] at hzi
      simp only [Set.mem_preimage, Set.mem_Ioo] at hzs
      rw [hFn, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
      have h1 := norm_zetaEntire_strip_le (z := z) (by linarith) (by linarith) hzi
      have h2 := norm_convexityWeight_le_strip (η := η) (t₀ := t₀) hη2 (by linarith)
        hzs.1.le hzs.2.le
      have h3 := four_add_cube_le_exp_exp (abs_nonneg z.im)
      calc ‖zetaEntire z‖ * ‖convexityWeight η t₀ z‖
          ≤ (5 * Real.exp 2 * (4 + |z.im|) ^ 3) * Real.exp (9 / 4) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ ≤ (5 * Real.exp 2 * (64 * Real.exp (3 * Real.exp |z.im|))) * Real.exp (9 / 4) := by
            gcongr
        _ = 5 * Real.exp 2 * 64 * Real.exp (9 / 4) * Real.exp (3 * Real.exp |z.im|) := by
            ring
  -- left edge
  have hleft : ∀ z : ℂ, z.re = -η → ‖F z‖ ≤ C₁ := by
    intro z hz
    have hz' : z = ((-η : ℝ) : ℂ) + (z.im : ℂ) * I := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [hz]
    rw [hFn, hz', norm_convexityWeight_left_edge ht₀0]
    rcases le_or_gt |z.im| 8 with hsmall | hbig
    · have hball : ((-η : ℝ) : ℂ) + (z.im : ℂ) * I ∈ Metric.closedBall (0 : ℂ) 10 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
        simp only [mul_zero, sub_zero, mul_one, add_zero, zero_add]
        rw [abs_neg, abs_of_pos hη]; linarith
      have hG : ‖zetaEntire (((-η : ℝ) : ℂ) + (z.im : ℂ) * I)‖ ≤ K :=
        (hK₀ _ hball).trans (hK ▸ le_max_left _ _)
      have hw1 : Real.exp (η ^ 2) ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr (by nlinarith)
      have hw2 : Real.exp (-(z.im - t₀) ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hw3 : t₀ ^ (-(3 / 2 + η)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      calc ‖zetaEntire (((-η : ℝ) : ℂ) + (z.im : ℂ) * I)‖
            * (Real.exp (η ^ 2) * Real.exp (-(z.im - t₀) ^ 2) * t₀ ^ (-(3 / 2 + η)))
          ≤ K * (Real.exp (1 / 4) * 1 * 1) := by
            gcongr
        _ ≤ C₁ := by rw [hC₁, mul_one, mul_one]; exact le_max_left _ _
    · have hG := norm_zetaEntire_left_edge_le hη hη2 hbig.le
      have hw1 : Real.exp (η ^ 2) ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr (by nlinarith)
      have hratio : |z.im| ^ (3 / 2 + η) * t₀ ^ (-(3 / 2 + η)) = (|z.im| / t₀) ^ (3 / 2 + η) := by
        rw [Real.rpow_neg ht₀0.le, Real.div_rpow (abs_nonneg _) ht₀0.le]
        exact (div_eq_mul_inv _ _).symm
      have hq := abs_div_rpow_le_one_add_sq (t := z.im) (t₀ := t₀) (p := 3 / 2 + η)
        (by linarith) (by positivity) (by linarith)
      have hg := one_add_abs_sq_mul_exp_neg_sq_le (z.im - t₀)
      have hneg : -(z.im - t₀) ^ 2 = -((z.im - t₀) ^ 2) := by ring
      rw [hneg]
      calc ‖zetaEntire (((-η : ℝ) : ℂ) + (z.im : ℂ) * I)‖
            * (Real.exp (η ^ 2) * Real.exp (-((z.im - t₀) ^ 2)) * t₀ ^ (-(3 / 2 + η)))
          ≤ (4 * Real.exp (3 / 2) * (1 + 1 / η) * |z.im| ^ (3 / 2 + η))
            * (Real.exp (1 / 4) * Real.exp (-((z.im - t₀) ^ 2)) * t₀ ^ (-(3 / 2 + η))) := by
            gcongr
        _ = 4 * Real.exp (3 / 2) * (1 + 1 / η) * Real.exp (1 / 4)
            * ((|z.im| ^ (3 / 2 + η) * t₀ ^ (-(3 / 2 + η))) * Real.exp (-((z.im - t₀) ^ 2))) := by
            ring
        _ ≤ 4 * Real.exp (3 / 2) * (1 + 1 / η) * Real.exp (1 / 4)
            * ((1 + |z.im - t₀|) ^ 2 * Real.exp (-((z.im - t₀) ^ 2))) := by
            rw [hratio]; gcongr
        _ ≤ 4 * Real.exp (3 / 2) * (1 + 1 / η) * Real.exp (1 / 4) * 2 := by gcongr
        _ = CL := by rw [hCL]; ring
        _ ≤ C₁ := by rw [hC₁]; exact le_max_of_le_right (le_max_left _ _)
  -- right edge
  have hright : ∀ z : ℂ, z.re = 1 + η → ‖F z‖ ≤ C₁ := by
    intro z hz
    have hz' : z = ((1 + η : ℝ) : ℂ) + (z.im : ℂ) * I := by
      conv_lhs => rw [← Complex.re_add_im z]
      rw [hz]
    rw [hFn, hz', norm_convexityWeight_right_edge ht₀0]
    have hG := norm_zetaEntire_right_edge_le (t := z.im) hη (by linarith)
    have hw1 : Real.exp ((1 + η) ^ 2) ≤ Real.exp (9 / 4) := Real.exp_le_exp.mpr (by nlinarith)
    have hlin : (1 + |z.im|) / t₀ ≤ 2 * (1 + |z.im - t₀|) := by
      rw [div_le_iff₀ ht₀0]
      have habs : |z.im| ≤ t₀ + |z.im - t₀| := by
        have := abs_add_le (z.im - t₀) t₀
        rw [sub_add_cancel, abs_of_pos ht₀0] at this; linarith
      nlinarith [abs_nonneg (z.im - t₀)]
    have hg := one_add_abs_sq_mul_exp_neg_sq_le (z.im - t₀)
    have hg' : (1 + |z.im - t₀|) * Real.exp (-((z.im - t₀) ^ 2)) ≤ 2 := by
      refine le_trans ?_ hg
      gcongr
      nlinarith [abs_nonneg (z.im - t₀)]
    have hneg : -(z.im - t₀) ^ 2 = -((z.im - t₀) ^ 2) := by ring
    rw [hneg]
    calc ‖zetaEntire (((1 + η : ℝ) : ℂ) + (z.im : ℂ) * I)‖
          * (Real.exp ((1 + η) ^ 2) * Real.exp (-((z.im - t₀) ^ 2)) / t₀)
        ≤ ((1 + 1 / η) * (1 + |z.im|)) * (Real.exp (9 / 4) * Real.exp (-((z.im - t₀) ^ 2)) / t₀) := by
          gcongr
      _ = (1 + 1 / η) * Real.exp (9 / 4) * ((1 + |z.im|) / t₀) * Real.exp (-((z.im - t₀) ^ 2)) := by
          ring
      _ ≤ (1 + 1 / η) * Real.exp (9 / 4) * (2 * (1 + |z.im - t₀|)) * Real.exp (-((z.im - t₀) ^ 2)) := by
          gcongr
      _ = 2 * (1 + 1 / η) * Real.exp (9 / 4) * ((1 + |z.im - t₀|) * Real.exp (-((z.im - t₀) ^ 2))) := by
          ring
      _ ≤ 2 * (1 + 1 / η) * Real.exp (9 / 4) * 2 := by gcongr
      _ = CR := by rw [hCR]; ring
      _ ≤ C₁ := by rw [hC₁]; exact le_max_of_le_right (le_max_right _ _)
  -- Phragmén–Lindelöf
  have hre : ((σ : ℂ) + (t₀ : ℂ) * I).re = σ := by simp
  have hPL := PhragmenLindelof.vertical_strip (a := -η) (b := 1 + η) (C := C₁) (f := F)
    (z := (σ : ℂ) + (t₀ : ℂ) * I) hFd.diffContOnCl hgrowth hleft hright
    (by rw [hre]; exact hσ1) (by rw [hre]; exact hσ2)
  rw [hFn, norm_convexityWeight] at hPL
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, mul_zero, mul_one, zero_add,
    add_zero, sub_self] at hPL
  have hz1 : (σ : ℂ) + (t₀ : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hrp : Real.exp (-((3 + η - σ) / 2) * Real.log t₀) = t₀ ^ (-((3 + η - σ) / 2)) := by
    rw [Real.rpow_def_of_pos ht₀0]; ring_nf
  rw [hrp] at hPL
  have hexp1 : 1 ≤ Real.exp (σ ^ 2 - 0 ^ 2) := Real.one_le_exp (by nlinarith)
  have hpos : 0 < t₀ ^ (-((3 + η - σ) / 2)) := Real.rpow_pos_of_pos ht₀0 _
  have hGle : ‖zetaEntire ((σ : ℂ) + (t₀ : ℂ) * I)‖ ≤ C₁ * t₀ ^ ((3 + η - σ) / 2) := by
    have h1 : ‖zetaEntire ((σ : ℂ) + (t₀ : ℂ) * I)‖ * t₀ ^ (-((3 + η - σ) / 2)) ≤ C₁ := by
      calc ‖zetaEntire ((σ : ℂ) + (t₀ : ℂ) * I)‖ * t₀ ^ (-((3 + η - σ) / 2))
          ≤ ‖zetaEntire ((σ : ℂ) + (t₀ : ℂ) * I)‖
            * (Real.exp (σ ^ 2 - 0 ^ 2) * t₀ ^ (-((3 + η - σ) / 2))) := by
            gcongr; exact le_mul_of_one_le_left hpos.le hexp1
        _ ≤ C₁ := by simpa using hPL
    rw [Real.rpow_neg ht₀0.le] at h1
    have hp : 0 < t₀ ^ ((3 + η - σ) / 2) := Real.rpow_pos_of_pos ht₀0 _
    rwa [mul_inv_le_iff₀ hp] at h1
  rw [zetaEntire_eq hz1, norm_mul] at hGle
  have hn : t₀ ≤ ‖(σ : ℂ) + (t₀ : ℂ) * I - 1‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp [abs_of_pos ht₀0]
  have hζ : ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖ ≤ C₁ * t₀ ^ ((3 + η - σ) / 2) / t₀ := by
    rw [le_div_iff₀ ht₀0]
    calc ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖ * t₀
        ≤ ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖ * ‖(σ : ℂ) + (t₀ : ℂ) * I - 1‖ := by gcongr
      _ = ‖(σ : ℂ) + (t₀ : ℂ) * I - 1‖ * ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖ := by ring
      _ ≤ C₁ * t₀ ^ ((3 + η - σ) / 2) := hGle
  have hsub : C₁ * t₀ ^ ((3 + η - σ) / 2) / t₀ = C₁ * t₀ ^ ((1 + η - σ) / 2) := by
    rw [mul_div_assoc, ← Real.rpow_sub_one ht₀0.ne']; congr 2; ring
  rw [hsub] at hζ
  calc ‖riemannZeta ((σ : ℂ) + (t₀ : ℂ) * I)‖ ≤ C₁ * t₀ ^ ((1 + η - σ) / 2) := hζ
    _ ≤ (C₁ + 1) * t₀ ^ ((1 + η - σ) / 2) := by
        gcongr; linarith

end

end RHTower
