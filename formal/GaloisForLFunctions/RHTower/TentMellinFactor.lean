import Mathlib
import GaloisForLFunctions.RHTower.RectangularWindowAmplitudeAnalytic
import GaloisForLFunctions.HTGeometry.RiemannSumCell

/-!
# The rectangular-window and tent Mellin factors

The elementary Mellin/Laplace factors of the prime-polar moving-tent tomography
(`prime-polar-moving-tent-divisor-tomography`, §2).  After the substitution `w = s − 1`, `u = eˣ`, the
box (rectangular-window) factor is the geometric integral

`A_L(w) = ∫₀ᴸ e^{-wx} dx = (1 − e^{-wL}) / w`,

with removable value `L` at `w = 0`, and the tent factor is its square `I_L(w) = A_L(w)²` (the tent
being the additive self-convolution of the box).  These are entire in `s` and supply the exact
`(1 − e^{-Lw})²/w²` shape of the completed window transform.
-/

open scoped Real
open intervalIntegral HTGeometry

namespace RHTower

/-- The primitive integral `∫ₐᵇ x e^{cx} dx = [(cx−1)e^{cx}/c²]ₐᵇ` (`c ≠ 0`), absent from mathlib. -/
theorem integral_id_mul_cexp (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    (∫ x in a..b, (x : ℂ) * Complex.exp (c * (x : ℂ)))
      = ((c * b - 1) * Complex.exp (c * b)) / c ^ 2
        - ((c * a - 1) * Complex.exp (c * a)) / c ^ 2 := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun t : ℝ => ((c * (t : ℂ) - 1) * Complex.exp (c * (t : ℂ))) / c ^ 2)
      ((x : ℂ) * Complex.exp (c * (x : ℂ))) x := by
    intro x
    have hx : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
        (Complex.exp (c * (x : ℂ)) * c) x := hx.cexp
    have hprod := (hx.sub_const (1 : ℂ)).mul hexp
    have hfin := hprod.div_const (c ^ 2)
    convert hfin using 1
    field_simp
    ring
  have hcont : Continuous (fun x : ℝ => (x : ℂ) * Complex.exp (c * (x : ℂ))) :=
    Complex.continuous_ofReal.mul ((Complex.continuous_ofReal.const_mul c).cexp)
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) (hcont.intervalIntegrable a b)]

/-- The tent (triangular) window of half-width `L`: `x` on `[0,L]`, `2L−x` on `[L,2L]`. -/
noncomputable def tentFn (L x : ℝ) : ℝ := if x ≤ L then x else 2 * L - x

/-- The tent is the pointwise minimum of the two edges `x` and `2L − x`. -/
theorem tentFn_eq_min (L x : ℝ) : tentFn L x = min x (2 * L - x) := by
  rw [tentFn]
  by_cases h : x ≤ L
  · rw [if_pos h, min_eq_left (by linarith)]
  · rw [if_neg h, min_eq_right (by linarith)]

/-- **The tent window is `1`-Lipschitz** — its two edges have slope `±1` and meet at the peak.  This
is the modulus of continuity feeding the uniform Riemann-sum estimate for the moving-tent sum. -/
theorem lipschitzWith_tentFn (L : ℝ) : LipschitzWith 1 (tentFn L) := by
  have hg : LipschitzWith 1 (fun x : ℝ => 2 * L - x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rw [show (2 * L - x) - (2 * L - y) = -(x - y) by ring, abs_neg]
  have hmin : LipschitzWith 1 (fun x : ℝ => min x (2 * L - x)) := by
    simpa using LipschitzWith.min LipschitzWith.id hg
  have heq : tentFn L = fun x => min x (2 * L - x) := funext (tentFn_eq_min L)
  rw [heq]; exact hmin

/-- The box (rectangular-window) Laplace factor `A_L(w) = ∫₀ᴸ e^{-wx} dx`. -/
noncomputable def boxLaplace (L : ℝ) (w : ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..L, Complex.exp (-w * (x : ℂ))

/-- **Box Laplace factor, closed form.**  For `w ≠ 0`, `A_L(w) = (1 − e^{-wL}) / w`. -/
theorem boxLaplace_eq (L : ℝ) (w : ℂ) (hw : w ≠ 0) :
    boxLaplace L w = (1 - Complex.exp (-w * (L : ℂ))) / w := by
  rw [boxLaplace, integral_exp_mul_complex (neg_ne_zero.mpr hw)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- **Removable value at `w = 0`.**  `A_L(0) = L`: the box factor extends continuously with value the
window length. -/
theorem boxLaplace_zero (L : ℝ) : boxLaplace L 0 = (L : ℂ) := by
  simp only [boxLaplace, neg_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
    sub_zero]
  rw [Complex.real_smul, mul_one]

/-- **Tent Mellin factor `= box factor squared` (§2, eq. 10).**  The Laplace transform of the tent
window over `[0, 2L]` equals the square of the box factor: `∫₀²ᴸ τ_L(x) e^{-wx} dx = A_L(w)²`.  The
tent is `x` on `[0,L]` and `2L−x` on `[L,2L]`; splitting there and using `∫ e^{-wx}` and
`∫ x e^{-wx}` gives, after cancellation, `((1−e^{-wL})/w)²`. -/
theorem tentLaplace_eq_boxLaplace_sq (L : ℝ) (hL : 0 ≤ L) (w : ℂ) (hw : w ≠ 0) :
    (∫ x in (0 : ℝ)..(2 * L), (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ)))
      = (boxLaplace L w) ^ 2 := by
  have hnw : -w ≠ 0 := neg_ne_zero.mpr hw
  have htcont : Continuous (fun x : ℝ => (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ))) := by
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_)
      ((Complex.continuous_ofReal.const_mul _).cexp)
    exact Continuous.if_le continuous_id (continuous_const.sub continuous_id) continuous_id
      continuous_const (fun x hx => by rw [hx]; ring)
  have h0L : (∫ x in (0 : ℝ)..L, (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ)))
      = ∫ x in (0 : ℝ)..L, (x : ℂ) * Complex.exp (-w * (x : ℂ)) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hL] at hx; simp [tentFn, hx.2]
  have hL2 : (∫ x in (L : ℝ)..(2 * L), (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ)))
      = ∫ x in (L : ℝ)..(2 * L),
          (((2 * L : ℝ) : ℂ) - (x : ℂ)) * Complex.exp (-w * (x : ℂ)) := by
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by linarith)] at hx
    by_cases h : x ≤ L
    · have hxeq : x = L := le_antisymm h hx.1
      subst hxeq; simp only [tentFn, le_refl, if_true]; push_cast; ring
    · simp only [tentFn, if_neg h]; push_cast; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := L)
      (htcont.intervalIntegrable 0 L) (htcont.intervalIntegrable L (2 * L)), h0L, hL2]
  have hsub : (∫ x in (L : ℝ)..(2 * L), (((2 * L : ℝ) : ℂ) - (x : ℂ)) * Complex.exp (-w * (x : ℂ)))
      = ((2 * L : ℝ) : ℂ) * (∫ x in (L : ℝ)..(2 * L), Complex.exp (-w * (x : ℂ)))
        - ∫ x in (L : ℝ)..(2 * L), (x : ℂ) * Complex.exp (-w * (x : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr (fun x _ => ?_); ring
    · exact (Complex.continuous_ofReal.const_mul _).cexp.const_mul _ |>.intervalIntegrable _ _
    · exact (Complex.continuous_ofReal.mul
        (Complex.continuous_ofReal.const_mul _).cexp).intervalIntegrable _ _
  rw [hsub, integral_id_mul_cexp (-w) hnw 0 L, integral_id_mul_cexp (-w) hnw L (2 * L),
    integral_exp_mul_complex hnw, boxLaplace_eq L w hw]
  have hE2 : Complex.exp (-w * ((2 * L : ℝ) : ℂ)) = Complex.exp (-w * (L : ℂ)) ^ 2 := by
    rw [pow_two, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hE2]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  push_cast
  field_simp
  ring

/-- The integral box factor coincides with the entire `rectangularWindowAmplitude` (the closed-form
`A_L` with its removable value at the origin). -/
theorem boxLaplace_eq_rectangularWindowAmplitude (L : ℝ) (w : ℂ) :
    boxLaplace L w = rectangularWindowAmplitude L w := by
  by_cases hw : w = 0
  · rw [hw, boxLaplace_zero, rectangularWindowAmplitude_zero]
  · rw [boxLaplace_eq L w hw, rectangularWindowAmplitude_eq_div hw,
      show (-w * (L : ℂ)) = (-(L : ℂ) * w) from by ring]

/-- **Tent Mellin factor `= A_L²` (eq. 11).**  Restating `(10)` with the entire closed-form amplitude:
`∫₀²ᴸ τ_L(x) e^{-wx} dx = A_L(w)²` where `A_L = rectangularWindowAmplitude`. -/
theorem tentLaplace_eq_rectangularWindowAmplitude_sq (L : ℝ) (hL : 0 ≤ L) (w : ℂ) (hw : w ≠ 0) :
    (∫ x in (0 : ℝ)..(2 * L), (tentFn L x : ℂ) * Complex.exp (-w * (x : ℂ)))
      = (rectangularWindowAmplitude L w) ^ 2 := by
  rw [tentLaplace_eq_boxLaplace_sq L hL w hw, boxLaplace_eq_rectangularWindowAmplitude]

/-- **The tent Mellin factor is entire** (§2, `I_L(s) = A_L(s−1)²` is entire in `s`).  As the square
of the shifted entire amplitude `A_L`, `s ↦ A_L(s−1)²` is holomorphic on all of `ℂ`. -/
theorem tentMellinFactor_differentiable (L : ℝ) :
    Differentiable ℂ (fun s : ℂ => (rectangularWindowAmplitude L (s - 1)) ^ 2) :=
  ((rectangularWindowAmplitude_differentiable L).comp (differentiable_id.sub_const 1)).pow 2

/-- The moving-tent-of-log integrand `g_s(u) = τ_L(log u)·e^{-s·log u}` (§3, eq. 13), written with the
exponential in place of the complex power.  On `u > 0` this is exactly `τ_L(log u)·u^{-s}`
(`gTent_eq_cpow`). -/
noncomputable def gTent (L : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  (tentFn L (Real.log u) : ℂ) * Complex.exp (-s * (Real.log u : ℂ))

/-- The exponential form of `g_s` coincides with the complex power `τ_L(log u)·u^{-s}` for `u > 0`. -/
theorem gTent_eq_cpow (L : ℝ) (s : ℂ) {u : ℝ} (hu : 0 < u) :
    gTent L s u = (tentFn L (Real.log u) : ℂ) * (↑u : ℂ) ^ (-s) := by
  have hune : (↑u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have key : (↑u : ℂ) ^ (-s) = Complex.exp (-s * (Real.log u : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hune, Complex.ofReal_log hu.le,
      mul_comm (Complex.log (↑u)) (-s)]
  rw [gTent, key]

/-- **The moving-tent-of-log integrand is Lipschitz on its support** (§3, eq. 14).  `g_s` is Lipschitz
on `[1, e^{2L}]` — the multiplicative window covering the tent's support — with a finite constant.  The
constant is `L·(‖s‖·e^{|Re s|·2L}) + e^{|Re s|·2L}`, built from: `τ_L(log u)` (`1`-Lipschitz `τ_L`
composed with `1`-Lipschitz `log` on `[1,∞)`, bounded by `L`) times `u^{-s} = e^{-s·log u}` (the
Laplace exponential composed with `log`, bounded by `e^{|Re s|·2L}`), via the bounded-product Lipschitz
rule.  This is the modulus of continuity underlying the uniform Riemann-sum estimate `(15)`. -/
theorem gTent_lipschitzOnWith (L : ℝ) (hL : 0 ≤ L) (s : ℂ) :
    ∃ C : NNReal, LipschitzOnWith C (gTent L s) (Set.Icc 1 (Real.exp (2 * L))) := by
  have hsub : Set.Icc (1 : ℝ) (Real.exp (2 * L)) ⊆ Set.Ici 1 := fun u hu => hu.1
  have hlog : LipschitzOnWith 1 Real.log (Set.Icc 1 (Real.exp (2 * L))) :=
    lipschitzOnWith_log_Ici_one.mono hsub
  have htentC : LipschitzWith (1 * 1) (fun x : ℝ => (↑(tentFn L x) : ℂ)) :=
    (Complex.isometry_ofReal.lipschitz).comp (lipschitzWith_tentFn L)
  have hA : LipschitzOnWith ((1 * 1) * 1) (fun u => (↑(tentFn L (Real.log u)) : ℂ))
      (Set.Icc 1 (Real.exp (2 * L))) :=
    htentC.lipschitzOnWith.comp hlog (Set.mapsTo_univ _ _)
  have hmaps : Set.MapsTo Real.log (Set.Icc 1 (Real.exp (2 * L))) (Set.Icc 0 (2 * L)) := by
    intro u hu
    refine ⟨Real.log_nonneg hu.1, ?_⟩
    calc Real.log u ≤ Real.log (Real.exp (2 * L)) := Real.log_le_log (by linarith [hu.1]) hu.2
      _ = 2 * L := Real.log_exp _
  have hB : LipschitzOnWith (_ * 1) (fun u => Complex.exp (-s * (Real.log u : ℂ)))
      (Set.Icc 1 (Real.exp (2 * L))) :=
    (lipschitzOnWith_cexp_neg_mul s (2 * L) (by positivity)).comp hlog hmaps
  have hboundA : ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp (2 * L)), ‖(↑(tentFn L (Real.log u)) : ℂ)‖ ≤ L := by
    intro u hu
    have hlu0 : 0 ≤ Real.log u := Real.log_nonneg hu.1
    have hlu2 : Real.log u ≤ 2 * L := (hmaps hu).2
    rw [Complex.norm_real, Real.norm_eq_abs, tentFn_eq_min,
      abs_of_nonneg (le_min hlu0 (by linarith))]
    have h1 := min_le_left (Real.log u) (2 * L - Real.log u)
    have h2 := min_le_right (Real.log u) (2 * L - Real.log u)
    linarith
  have hboundB : ∀ u ∈ Set.Icc (1 : ℝ) (Real.exp (2 * L)),
      ‖Complex.exp (-s * (Real.log u : ℂ))‖ ≤ Real.exp (|s.re| * (2 * L)) := by
    intro u hu
    have hlu0 : 0 ≤ Real.log u := Real.log_nonneg hu.1
    have hlu2 : Real.log u ≤ 2 * L := (hmaps hu).2
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-s * (Real.log u : ℂ)).re = -(s.re) * Real.log u := by simp [Complex.mul_re]
    rw [hre]
    nlinarith [le_abs_self s.re, neg_abs_le s.re, abs_nonneg s.re, hlu0, hlu2]
  exact ⟨_, lipschitzOnWith_mul_of_bound hA hB hboundA hboundB⟩

/-- **The integral of the moving-tent integrand equals the tent Mellin factor** (§3, connecting
`(13)` to `(8)`).  Under the substitution `u = eˣ`, `∫₁^{e^{2L}} g_s(u) du = ∫₀^{2L} τ_L(x) e^{-(s-1)x} dx`.
The improper `∫₀^∞` of `(8)` reduces to this compact integral because `g_s` is supported on
`[1, e^{2L}]`. -/
theorem gTent_integral_eq_tentLaplace (L : ℝ) (s : ℂ) :
    (∫ u in (1 : ℝ)..(Real.exp (2 * L)), gTent L s u)
      = ∫ x in (0 : ℝ)..(2 * L), (tentFn L x : ℂ) * Complex.exp (-(s - 1) * (x : ℂ)) := by
  have hgcont : ContinuousOn (gTent L s) (Set.Ioi 0) := by
    have hlog : ContinuousOn Real.log (Set.Ioi 0) :=
      Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
    have h1 : ContinuousOn (fun u => (tentFn L (Real.log u) : ℂ)) (Set.Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((lipschitzWith_tentFn L).continuous.comp_continuousOn hlog)
    have h2 : ContinuousOn (fun u => Complex.exp (-s * (Real.log u : ℂ))) (Set.Ioi 0) :=
      Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hlog))
    exact h1.mul h2
  have himg : Real.exp '' Set.uIcc (0 : ℝ) (2 * L) ⊆ Set.Ioi 0 := by
    intro y hy; obtain ⟨x, _, rfl⟩ := hy; exact Real.exp_pos x
  have hcov := intervalIntegral.integral_deriv_smul_comp'' (a := 0) (b := 2 * L)
    (f := Real.exp) (f' := Real.exp) (g := gTent L s)
    Real.continuous_exp.continuousOn
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.continuous_exp.continuousOn
    (hgcont.mono himg)
  rw [Real.exp_zero] at hcov
  rw [← hcov]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [Function.comp_apply, gTent, Real.log_exp]
  rw [Complex.real_smul, Complex.ofReal_exp,
    show Complex.exp (↑x) * (↑(tentFn L x) * Complex.exp (-s * ↑x))
      = ↑(tentFn L x) * (Complex.exp (↑x) * Complex.exp (-s * ↑x)) from by ring,
    ← Complex.exp_add]
  congr 2
  ring

/-- **The moving-tent integral equals the squared window amplitude** (`I_L(s) = A_L(s-1)²`, `s ≠ 1`).
Combines the change of variables with `tentLaplace_eq_rectangularWindowAmplitude_sq`. -/
theorem gTent_integral_eq_amplitude_sq (L : ℝ) (hL : 0 ≤ L) (s : ℂ) (hs : s ≠ 1) :
    (∫ u in (1 : ℝ)..(Real.exp (2 * L)), gTent L s u) = (rectangularWindowAmplitude L (s - 1)) ^ 2 := by
  rw [gTent_integral_eq_tentLaplace,
    tentLaplace_eq_rectangularWindowAmplitude_sq L hL (s - 1) (sub_ne_zero.mpr hs)]

/-- The **truncated tent** `τ_L(x) = (L − |x − L|)₊ = max 0 (min x (2L−x))` (§1, eq. 1), the card's
actual window: it coincides with `tentFn` on the support `[0, 2L]` but is `0` outside, which is what
makes the moving-prime sum `(2)` finite via the support condition `(3)`. -/
noncomputable def tentPos (L x : ℝ) : ℝ := max 0 (tentFn L x)

/-- On the support `[0, 2L]` the truncated tent equals the plain (min) tent. -/
theorem tentPos_eq_tentFn_of_mem (L : ℝ) {x : ℝ} (hx : x ∈ Set.Icc 0 (2 * L)) :
    tentPos L x = tentFn L x := by
  rw [tentPos, max_eq_right]
  rw [tentFn_eq_min]
  exact le_min hx.1 (by linarith [hx.2])

/-- Outside `[0, 2L]` the truncated tent vanishes — the finiteness of the moving-prime sum. -/
theorem tentPos_eq_zero_of_notMem (L : ℝ) {x : ℝ} (hx : x ∉ Set.Icc 0 (2 * L)) :
    tentPos L x = 0 := by
  rw [tentPos, max_eq_left]
  rw [tentFn_eq_min]
  rcases not_and_or.mp (fun h => hx ⟨h.1, h.2⟩) with h | h
  · exact le_trans (min_le_left _ _) (le_of_not_ge h)
  · exact le_trans (min_le_right _ _) (by linarith [le_of_not_ge h])

/-- The truncated tent is `1`-Lipschitz (`max 0` preserves the Lipschitz constant of `tentFn`). -/
theorem lipschitzWith_tentPos (L : ℝ) : LipschitzWith 1 (tentPos L) :=
  (lipschitzWith_tentFn L).const_max 0

/-- **Truncation does not change the Mellin factor.**  Since `tentPos` and `tentFn` agree on the
integration interval `[0, 2L]`, `∫₀²ᴸ τ_L(x) e^{-wx} dx = A_L(w)²` for the truncated tent as well. -/
theorem tentPosLaplace_eq_amplitude_sq (L : ℝ) (hL : 0 ≤ L) (w : ℂ) (hw : w ≠ 0) :
    (∫ x in (0 : ℝ)..(2 * L), (tentPos L x : ℂ) * Complex.exp (-w * (x : ℂ)))
      = (rectangularWindowAmplitude L w) ^ 2 := by
  rw [← tentLaplace_eq_rectangularWindowAmplitude_sq L hL w hw]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [Set.uIcc_of_le (by linarith)] at hx
  rw [tentPos_eq_tentFn_of_mem L hx]

end RHTower
