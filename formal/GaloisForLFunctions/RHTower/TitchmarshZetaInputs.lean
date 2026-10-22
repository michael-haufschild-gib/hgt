import GaloisForLFunctions.RHTower.SmoothAFEZetaLeftLineBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound
import GaloisForLFunctions.RHTower.ZetaLowerBound
import GaloisForLFunctions.RHTower.Deninger.DeningerZetaLowerBound
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# Quantitative zeta inputs for Titchmarsh's shrinking zero-gap theorem

Titchmarsh's first proof of Theorem 9.12 propagates a branch of `log ζ` from `Re s = 2`
to the left by overlapping circles.  The circles only need a polynomial upper bound for `ζ`
on a fixed strip and a polynomial lower bound at their terminal point.

The existing smooth approximate-functional-equation bound stops at `Re s = -1/2`.  The terminal
circle crosses that line by a small fixed amount.  `norm_zetaChi_le_negative_one_strip` closes this
thin gap by one additional Gamma recurrence.  The resulting bound is deliberately coarse but fully
uniform on `-1 ≤ Re s ≤ 5/2`.
-/

open Complex

namespace RHTower

/-- A two-step bounded-width Gamma-ratio estimate. -/
private theorem norm_Gamma_ratio_le_exp_four
    {a b y : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hwidth : b - a ≤ 1)
    (hy : 1 ≤ y) :
    ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp 4 := by
  let m : ℝ := (a + b) / 2
  have ham : a ≤ m := by dsimp only [m]; linarith
  have hmb : m ≤ b := by dsimp only [m]; linarith
  have hma : m - a ≤ 1 / 2 := by dsimp only [m]; linarith
  have hbm : b - m ≤ 1 / 2 := by dsimp only [m]; linarith
  have hleft := norm_Gamma_vertical_ratio_le_exp_two ha0 ham hma hy
  have hm0 : 0 ≤ m := ha0.trans ham
  have hright := norm_Gamma_vertical_ratio_le_exp_two hm0 hmb hbm hy
  have hGa : Complex.Gamma ((a : ℂ) + (y : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    simp at him
    linarith
  have hGm : Complex.Gamma ((m : ℂ) + (y : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    simp at him
    linarith
  have hGb : Complex.Gamma ((b : ℂ) + (y : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    simp at him
    linarith
  have hsplit :
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ =
        (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
            ‖Complex.Gamma ((m : ℂ) + (y : ℂ) * I)‖) *
          (‖Complex.Gamma ((m : ℂ) + (y : ℂ) * I)‖ /
            ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖) := by
    field_simp [norm_ne_zero_iff.mpr hGa, norm_ne_zero_iff.mpr hGm,
      norm_ne_zero_iff.mpr hGb]
  rw [hsplit]
  calc
    (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((m : ℂ) + (y : ℂ) * I)‖) *
        (‖Complex.Gamma ((m : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖)
        ≤ Real.exp 2 * Real.exp 2 :=
      mul_le_mul hleft hright (by positivity) (by positivity)
    _ = Real.exp 4 := by rw [← Real.exp_add]; ring_nf

/-- Uniform polynomial bound for the functional-equation factor on the extra strip
`-1 ≤ σ ≤ -1/2`.  One Gamma recurrence contributes one factor of `1+|t|`; a bounded-width
Gamma ratio contributes only an absolute constant. -/
theorem norm_zetaChi_le_negative_one_strip
    {σ t : ℝ} (hσlow : -1 ≤ σ) (hσhigh : σ ≤ -1 / 2)
    (ht : 2 ≤ |t|) :
    ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp 4 * (1 + |t|) ^ 2 := by
  rw [norm_zetaChi_real_add_im_eq_abs σ t]
  let T : ℝ := |t|
  let z : ℂ := (σ : ℂ) + (T : ℂ) * I
  let a : ℝ := (1 - σ) / 2
  let b : ℝ := 1 + σ / 2
  let y : ℝ := T / 2
  have hT : 2 ≤ T := ht
  have hy : 1 ≤ y := by dsimp only [y, T]; linarith
  have ha0 : 0 ≤ a := by dsimp only [a]; linarith
  have hab : a ≤ b + 1 := by dsimp only [a, b]; linarith
  have hwidth : (b + 1) - a ≤ 1 := by dsimp only [a, b]; linarith
  have hratio :
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma (((b + 1 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp 4 :=
    norm_Gamma_ratio_le_exp_four ha0 hab hwidth hy
  have hnumArg : (1 - z) / 2 = (a : ℂ) - (y : ℂ) * I := by
    dsimp only [z, a, y]
    push_cast
    ring
  have hnumNorm :
      ‖Complex.Gamma ((1 - z) / 2)‖ =
        ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ := by
    rw [hnumArg,
      show (a : ℂ) - (y : ℂ) * I =
        (starRingEnd ℂ) ((a : ℂ) + (y : ℂ) * I) by
          apply Complex.ext <;> simp,
      Complex.Gamma_conj, Complex.norm_conj]
  have hdenArg : z / 2 + 1 = (b : ℂ) + (y : ℂ) * I := by
    dsimp only [z, b, y]
    push_cast
    ring
  have hshiftArg :
      ((b + 1 : ℝ) : ℂ) + (y : ℂ) * I =
        ((b : ℂ) + (y : ℂ) * I) + 1 := by
    push_cast
    ring
  have hz0 : z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    dsimp only [z, T] at him
    simp at him
    rw [him] at ht
    norm_num at ht
  have hzhalf0 : z / 2 ≠ 0 := div_ne_zero hz0 (by norm_num)
  have hrec0 := Complex.Gamma_add_one (z / 2) hzhalf0
  have hbiy0 : (b : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hrec1 := Complex.Gamma_add_one ((b : ℂ) + (y : ℂ) * I) hbiy0
  have hdenNe : Complex.Gamma (z / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    dsimp only [z, T] at him
    simp at him
    rw [him] at ht
    norm_num at ht
  have hbGammaNe : Complex.Gamma ((b : ℂ) + (y : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    simp at him
    linarith
  have hb1GammaNe :
      Complex.Gamma (((b + 1 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    simp at him
    linarith
  have hdenNorm :
      ‖Complex.Gamma (z / 2)‖ =
        ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ / ‖z / 2‖ := by
    have hnorm := congrArg norm hrec0
    rw [norm_mul] at hnorm
    rw [hdenArg] at hnorm
    rw [eq_div_iff (norm_ne_zero_iff.mpr hzhalf0)]
    simpa [mul_comm] using hnorm.symm
  have hbRatio :
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ =
        ‖((b : ℂ) + (y : ℂ) * I)‖ *
          (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
            ‖Complex.Gamma (((b + 1 : ℝ) : ℂ) + (y : ℂ) * I)‖) := by
    have hnorm := congrArg norm hrec1
    rw [norm_mul, ← hshiftArg] at hnorm
    rw [hnorm]
    field_simp [norm_ne_zero_iff.mpr hbGammaNe, norm_ne_zero_iff.mpr hb1GammaNe,
      norm_ne_zero_iff.mpr hbiy0]
  have hrawRatio :
      ‖Complex.Gamma ((1 - z) / 2)‖ / ‖Complex.Gamma (z / 2)‖ =
        ‖z / 2‖ * ‖((b : ℂ) + (y : ℂ) * I)‖ *
          (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
            ‖Complex.Gamma (((b + 1 : ℝ) : ℂ) + (y : ℂ) * I)‖) := by
    rw [hnumNorm, hdenNorm]
    calc
      ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
          (‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖ / ‖z / 2‖) =
          ‖z / 2‖ *
            (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
              ‖Complex.Gamma ((b : ℂ) + (y : ℂ) * I)‖) := by
            field_simp [norm_ne_zero_iff.mpr hdenNe,
              norm_ne_zero_iff.mpr hbGammaNe, norm_ne_zero_iff.mpr hzhalf0]
      _ = ‖z / 2‖ * ‖((b : ℂ) + (y : ℂ) * I)‖ *
          (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
            ‖Complex.Gamma (((b + 1 : ℝ) : ℂ) + (y : ℂ) * I)‖) := by
            rw [hbRatio]
            ring
  have hσabs : |σ| ≤ 1 := (abs_le).2 ⟨by linarith, by linarith⟩
  have hT0 : 0 ≤ T := abs_nonneg t
  have hzNorm : ‖z / 2‖ ≤ 1 + T := by
    have hz : ‖z‖ ≤ 1 + T := by
      dsimp only [z]
      calc
        ‖(σ : ℂ) + (T : ℂ) * I‖ ≤ ‖(σ : ℂ)‖ + ‖(T : ℂ) * I‖ := norm_add_le _ _
        _ = |σ| + T := by simp [hT0]
        _ ≤ 1 + T := by linarith
    rw [norm_div, Complex.norm_ofNat]
    nlinarith [norm_nonneg z]
  have hbNorm : ‖((b : ℂ) + (y : ℂ) * I)‖ ≤ 1 + T := by
    have hbabs : |b| ≤ 1 := by
      rw [abs_le]
      constructor <;> dsimp only [b] <;> linarith
    calc
      ‖((b : ℂ) + (y : ℂ) * I)‖ ≤ ‖(b : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = |b| + |y| := by simp
      _ ≤ 1 + T := by
        have hy0 : 0 ≤ y := by dsimp only [y]; positivity
        rw [abs_of_nonneg hy0]
        dsimp only [y]
        linarith
  have hpiFactor : Real.pi ^ (σ - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  rw [norm_zetaChi_eq z, mul_div_assoc, hrawRatio]
  have hratioNonneg :
      0 ≤ ‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
        ‖Complex.Gamma (((b + 1 : ℝ) : ℂ) + (y : ℂ) * I)‖ := by positivity
  calc
    Real.pi ^ (z.re - 1 / 2) *
        (‖z / 2‖ * ‖(b : ℂ) + (y : ℂ) * I‖ *
          (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
            ‖Complex.Gamma (((b + 1 : ℝ) : ℂ) + (y : ℂ) * I)‖))
        = Real.pi ^ (σ - 1 / 2) *
          (‖z / 2‖ * ‖(b : ℂ) + (y : ℂ) * I‖ *
            (‖Complex.Gamma ((a : ℂ) + (y : ℂ) * I)‖ /
              ‖Complex.Gamma (((b + 1 : ℝ) : ℂ) + (y : ℂ) * I)‖)) := by
            congr 3
            simp [z]
    _ ≤ 1 * ((1 + T) * (1 + T) * Real.exp 4) := by gcongr
    _ = Real.exp 4 * (1 + |t|) ^ 2 := by dsimp only [T]; ring

/-- A single polynomial upper envelope for `ζ` on every circle used in the Titchmarsh chain. -/
theorem norm_riemannZeta_le_titchmarsh_strip
    {σ t : ℝ} (hσlow : -1 ≤ σ) (_hσhigh : σ ≤ 5 / 2)
    (ht : 2 ≤ |t|) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      20 * Real.exp 4 * (1 + |t|) ^ 2 := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hbasePos : 0 ≤ 1 + |t| := by positivity
  rcases le_total (-1 / 2 : ℝ) σ with hright | hleft
  · rcases le_total σ (3 / 2 : ℝ) with hmid | hfar
    · have h := norm_riemannZeta_le_smoothAFE_strip hright hmid ht
      calc
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
            ≤ 5 * Real.exp 2 * (1 + |t|) * (4 + |t|) := h
        _ ≤ 20 * Real.exp 4 * (1 + |t|) ^ 2 := by
          have he : Real.exp 2 ≤ Real.exp 4 := Real.exp_le_exp.mpr (by linarith)
          have hfour : 4 + |t| ≤ 4 * (1 + |t|) := by linarith [abs_nonneg t]
          calc
            5 * Real.exp 2 * (1 + |t|) * (4 + |t|)
                ≤ 5 * Real.exp 4 * (1 + |t|) * (4 + |t|) := by gcongr
            _ ≤ 5 * Real.exp 4 * (1 + |t|) * (4 * (1 + |t|)) := by gcongr
            _ = 20 * Real.exp 4 * (1 + |t|) ^ 2 := by ring
    · have hzeta := Sieve.norm_riemannZeta_le (s := z) (by dsimp only [z]; simp; linarith)
      have hthree : 1 + 1 / (z.re - 1) ≤ 3 := by
        have hden : 1 / 2 ≤ z.re - 1 := by dsimp only [z]; simp; linarith
        have hden0 : 0 < z.re - 1 := by linarith
        have hinv : 1 / (z.re - 1) ≤ 2 := by
          rw [div_le_iff₀ hden0]
          nlinarith
        linarith
      exact hzeta.trans (hthree.trans <| by
        have he : 1 ≤ Real.exp 4 := Real.one_le_exp (by linarith)
        nlinarith [sq_nonneg (1 + |t|)])
  · have hχ := norm_zetaChi_le_negative_one_strip hσlow hleft ht
    have hz0 : z ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      dsimp only [z] at him
      simp at him
      rw [him] at ht
      norm_num at ht
    have hz1 : z ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      dsimp only [z] at him
      simp at him
      rw [him] at ht
      norm_num at ht
    have hGamma : Complex.Gammaℝ (1 - z) ≠ 0 := by
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      dsimp only [z]
      simp
      linarith
    have hreflect := zeta_eq_zetaChi_mul hz0 hz1 hGamma
    have hrightZeta := Sieve.norm_riemannZeta_le (s := 1 - z) (by
      dsimp only [z]
      simp
      linarith)
    have hthree : 1 + 1 / ((1 - z).re - 1) ≤ 3 := by
      have hden : 1 / 2 ≤ (1 - z).re - 1 := by dsimp only [z]; simp; linarith
      have hden0 : 0 < (1 - z).re - 1 := by linarith
      have hinv : 1 / ((1 - z).re - 1) ≤ 2 := by
        rw [div_le_iff₀ hden0]
        nlinarith
      linarith
    rw [hreflect, norm_mul]
    calc
      ‖zetaChi z‖ * ‖riemannZeta (1 - z)‖
          ≤ (Real.exp 4 * (1 + |t|) ^ 2) * 3 :=
        mul_le_mul hχ (hrightZeta.trans hthree) (norm_nonneg _) (by positivity)
      _ ≤ 20 * Real.exp 4 * (1 + |t|) ^ 2 := by
        have hnonneg : 0 ≤ Real.exp 4 * (1 + |t|) ^ 2 := by positivity
        nlinarith

/-- Exact terminal lower bound used by the zero-gap chain.  It combines the exact critical-left-line
modulus of `zetaChi` with the quartic lower bound for `ζ(3/2-it)`. -/
theorem titchmarsh_terminal_zeta_lower {t : ℝ} (ht : 9 ≤ |t|) :
    (‖smoothAFEZetaLeftLinePt t‖ / (2 * Real.pi)) ^ 4 *
        ((1 / 2 : ℝ) ^ 3 / (756 * Real.log |t|)) ≤
      ‖riemannZeta (smoothAFEZetaLeftLinePt t)‖ ^ 4 := by
  let s := smoothAFEZetaLeftLinePt t
  have hs0 : s ≠ 0 := smoothAFEZetaLeftLinePt_ne_zero t
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [s] at hre
    rw [smoothAFEZetaLeftLinePt_re] at hre
    norm_num at hre
  have hGamma : Complex.Gammaℝ (1 - s) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    dsimp only [s]
    rw [Complex.sub_re, Complex.one_re, smoothAFEZetaLeftLinePt_re]
    norm_num
  have hreflect := zeta_eq_zetaChi_mul hs0 hs1 hGamma
  have hone : 1 - s = (((3 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    dsimp only [s, smoothAFEZetaLeftLinePt]
    push_cast
    ring
  have hzeta := pow_four_norm_riemannZeta_ge (x := 1 / 2) (t := -t)
    (by simpa [abs_neg] using ht) (by norm_num) (by norm_num)
  have hzeta' :
      (1 / 2 : ℝ) ^ 3 / (756 * Real.log |t|) ≤
        ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ ^ 4 := by
    simpa only [abs_neg, show (1 + (1 / 2 : ℝ)) = 3 / 2 by ring] using hzeta
  rw [hone] at hreflect
  rw [hreflect, norm_mul, mul_pow,
    norm_zetaChi_smoothAFEZetaLeftLinePt]
  exact mul_le_mul_of_nonneg_left hzeta' (by positivity)

/-- The normalized logarithm at the right-hand anchor is absolutely bounded, uniformly in height.
The generous constant `10` keeps the circle recursion free of irrelevant Archimedean constants. -/
theorem norm_log_riemannZeta_two_add_I_mul_le_ten (t : ℝ) :
    ‖Complex.log (riemannZeta (2 + (t : ℂ) * I))‖ ≤ 10 := by
  let s : ℂ := 2 + (t : ℂ) * I
  have hsre : s.re = 2 := by simp [s]
  have hlower : (1 : ℝ) / 4 ≤ ‖riemannZeta s‖ :=
    norm_riemannZeta_ge_of_two_le_re (by rw [hsre])
  have hupper : ‖riemannZeta s‖ ≤ 2 := by
    have h := Sieve.norm_riemannZeta_le (s := s) (by rw [hsre]; norm_num)
    rw [hsre] at h
    norm_num at h ⊢
    exact h
  have hnormpos : 0 < ‖riemannZeta s‖ := lt_of_lt_of_le (by norm_num) hlower
  have hlogUpper : Real.log ‖riemannZeta s‖ ≤ 1 := by
    calc
      Real.log ‖riemannZeta s‖ ≤ Real.log 2 := Real.log_le_log hnormpos hupper
      _ ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hlogFour : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h ⊢
    exact h
  have hlogLower : -3 ≤ Real.log ‖riemannZeta s‖ := by
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hlower
    have hquarter : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hquarter] at hmono
    linarith
  have habs : |Real.log ‖riemannZeta s‖| ≤ 3 :=
    (abs_le).2 ⟨hlogLower, hlogUpper.trans (by norm_num)⟩
  have harg : |Complex.arg (riemannZeta s)| ≤ Real.pi := Complex.abs_arg_le_pi _
  calc
    ‖Complex.log (riemannZeta (2 + (t : ℂ) * I))‖ =
        ‖Complex.log (riemannZeta s)‖ := by rfl
    _ ≤ |(Complex.log (riemannZeta s)).re| +
        |(Complex.log (riemannZeta s)).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖riemannZeta s‖| + |Complex.arg (riemannZeta s)| := by
      rw [Complex.log_re, Complex.log_im]
    _ ≤ 3 + Real.pi := add_le_add habs harg
    _ ≤ 10 := by linarith [Real.pi_lt_four]

end RHTower
