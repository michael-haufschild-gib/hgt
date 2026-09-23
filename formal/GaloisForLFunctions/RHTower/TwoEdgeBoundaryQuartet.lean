import Mathlib

/-!
# Two-edge boundary profiles exponentially amplify every fixed off-line quartet

For a real profile `f` supported in `(0, L)` and an aperture `a > L`, the even boundary profile
`φ_a(x) = f(a − |x|)` has the exact two-edge transform

```text
G_a(w) = e^{a w} A_f(w) + e^{−a w} A_f(−w),
A_f(w) = ∫_0^L f(s) e^{−w s} ds .
```

The transform is even in `w`, so the Weil contribution of a functional-equation/Schwarz quartet at
`w = δ + iT` is `4 Re (G_a(w)²)`.  Expanding gives one exponentially growing oscillatory term, one
bounded term and one decaying term; choosing the aperture so that the leading phase is `π` makes
the growing term exactly `−4 e^{2aδ} |A_f(w)|²`, so the quartet contribution tends to `−∞` along a
cofinal aperture sequence.

On the imaginary axis the aperture factor has modulus one, so the all-line background is bounded
uniformly in the aperture by the divisor sum of `(‖A_f(it)‖ + ‖A_f(−it)‖)²`.

Everything here is exact interval-integral algebra; no estimate on `f` beyond its support is used.
-/

namespace RHTower

open Complex intervalIntegral

noncomputable section

/-! ## The two-edge transform -/

/-- The one-sided Laplace transform of the boundary profile. -/
def edgeLaplace (f : ℝ → ℝ) (L : ℝ) (w : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..L, (f s : ℂ) * Complex.exp (-w * (s : ℂ))

/-- The two-edge boundary profile transform, written as the two boundary-layer integrals. -/
def twoEdgeTransform (f : ℝ → ℝ) (L a : ℝ) (w : ℂ) : ℂ :=
  (∫ x in (a - L)..a, (f (a - x) : ℂ) * Complex.exp (w * (x : ℂ)))
    + ∫ x in (-a)..(-(a - L)), (f (a + x) : ℂ) * Complex.exp (w * (x : ℂ))

/-- **Equation `(4)`.**  The exact two-edge identity. -/
theorem twoEdgeTransform_eq (f : ℝ → ℝ) (L a : ℝ) (w : ℂ) :
    twoEdgeTransform f L a w
      = Complex.exp ((a : ℂ) * w) * edgeLaplace f L w
        + Complex.exp (-((a : ℂ) * w)) * edgeLaplace f L (-w) := by
  have hright : (∫ x in (a - L)..a, (f (a - x) : ℂ) * Complex.exp (w * (x : ℂ)))
      = Complex.exp ((a : ℂ) * w) * edgeLaplace f L w := by
    have hfun : ∀ x : ℝ, (f (a - x) : ℂ) * Complex.exp (w * (x : ℂ))
        = (fun s : ℝ => (f s : ℂ) * Complex.exp (w * (((a : ℝ) - s : ℝ) : ℂ))) (a - x) := by
      intro x
      have hx : ((a - (a - x) : ℝ) : ℂ) = (x : ℂ) := by push_cast; ring
      simp only [hx]
    rw [intervalIntegral.integral_congr (g := fun x : ℝ =>
      (fun s : ℝ => (f s : ℂ) * Complex.exp (w * (((a : ℝ) - s : ℝ) : ℂ))) (a - x))
      (fun x _ => hfun x)]
    rw [intervalIntegral.integral_comp_sub_left
      (fun s : ℝ => (f s : ℂ) * Complex.exp (w * (((a : ℝ) - s : ℝ) : ℂ))) a]
    have hsimp : a - a = 0 := by ring
    have hsimp2 : a - (a - L) = L := by ring
    rw [hsimp, hsimp2, edgeLaplace, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show (((a : ℝ) - s : ℝ) : ℂ) = (a : ℂ) - (s : ℂ) from by push_cast; ring]
    rw [mul_sub, Complex.exp_sub]
    field_simp
    rw [mul_assoc, ← Complex.exp_add]
    simp
  have hleft : (∫ x in (-a)..(-(a - L)), (f (a + x) : ℂ) * Complex.exp (w * (x : ℂ)))
      = Complex.exp (-((a : ℂ) * w)) * edgeLaplace f L (-w) := by
    have hfun : ∀ x : ℝ, (f (a + x) : ℂ) * Complex.exp (w * (x : ℂ))
        = (fun s : ℝ => (f s : ℂ) * Complex.exp (w * ((s - (a : ℝ) : ℝ) : ℂ))) (a + x) := by
      intro x
      have hx : ((a + x - (a : ℝ) : ℝ) : ℂ) = (x : ℂ) := by push_cast; ring
      simp only [hx]
    rw [intervalIntegral.integral_congr (g := fun x : ℝ =>
      (fun s : ℝ => (f s : ℂ) * Complex.exp (w * ((s - (a : ℝ) : ℝ) : ℂ))) (a + x))
      (fun x _ => hfun x)]
    rw [intervalIntegral.integral_comp_add_left
      (fun s : ℝ => (f s : ℂ) * Complex.exp (w * ((s - (a : ℝ) : ℝ) : ℂ))) a]
    have hsimp : a + -a = 0 := by ring
    have hsimp2 : a + -(a - L) = L := by ring
    rw [hsimp, hsimp2, edgeLaplace, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [show ((s - (a : ℝ) : ℝ) : ℂ) = (s : ℂ) - (a : ℂ) from by push_cast; ring]
    rw [mul_sub, Complex.exp_sub]
    field_simp
    rw [mul_assoc, ← Complex.exp_add]
    simp
  rw [twoEdgeTransform, hright, hleft]

/-- **Equation `(5)`.**  The two-edge transform is even. -/
theorem twoEdgeTransform_neg (f : ℝ → ℝ) (L a : ℝ) (w : ℂ) :
    twoEdgeTransform f L a (-w) = twoEdgeTransform f L a w := by
  rw [twoEdgeTransform_eq, twoEdgeTransform_eq, neg_neg]
  rw [show ((a : ℂ) * -w) = -((a : ℂ) * w) from by ring, neg_neg]
  ring

/-! ## The quartet contribution -/

/-- The centred quartet point `δ + iT`. -/
def quartetEdge (δ T : ℝ) : ℂ := (δ : ℂ) + (T : ℂ) * Complex.I

@[simp] theorem quartetEdge_re (δ T : ℝ) : (quartetEdge δ T).re = δ := by
  simp [quartetEdge]

@[simp] theorem quartetEdge_im (δ T : ℝ) : (quartetEdge δ T).im = T := by
  simp [quartetEdge]

/-- **Equation `(7)`.**  The Weil contribution of a functional-equation/Schwarz quartet. -/
def quartetContribution (f : ℝ → ℝ) (L a : ℝ) (w : ℂ) : ℝ :=
  4 * ((twoEdgeTransform f L a w) ^ (2 : ℕ)).re

theorem quartetContribution_eq_mul (f : ℝ → ℝ) (L a : ℝ) (w : ℂ) :
    quartetContribution f L a w
      = 4 * (twoEdgeTransform f L a w * twoEdgeTransform f L a (-w)).re := by
  rw [quartetContribution, twoEdgeTransform_neg, sq]

/-- **Equation `(8)`.**  The three-term aperture expansion of the quartet contribution. -/
theorem quartetContribution_expand (f : ℝ → ℝ) (L a δ T : ℝ) :
    quartetContribution f L a (quartetEdge δ T)
      = 4 * Real.exp (2 * a * δ)
          * (Complex.exp (((2 * a * T : ℝ) : ℂ) * Complex.I)
              * (edgeLaplace f L (quartetEdge δ T)) ^ (2 : ℕ)).re
        + 8 * (edgeLaplace f L (quartetEdge δ T)
              * edgeLaplace f L (-(quartetEdge δ T))).re
        + 4 * Real.exp (-(2 * a * δ))
          * (Complex.exp (-(((2 * a * T : ℝ) : ℂ) * Complex.I))
              * (edgeLaplace f L (-(quartetEdge δ T))) ^ (2 : ℕ)).re := by
  set w : ℂ := quartetEdge δ T with hw
  set A : ℂ := edgeLaplace f L w with hA
  set B : ℂ := edgeLaplace f L (-w) with hB
  have hsq : (twoEdgeTransform f L a w) ^ (2 : ℕ)
      = Complex.exp (2 * (a : ℂ) * w) * A ^ (2 : ℕ) + 2 * (A * B)
        + Complex.exp (-(2 * (a : ℂ) * w)) * B ^ (2 : ℕ) := by
    rw [twoEdgeTransform_eq]
    have h1 : Complex.exp ((a : ℂ) * w) * Complex.exp ((a : ℂ) * w)
        = Complex.exp (2 * (a : ℂ) * w) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : Complex.exp (-((a : ℂ) * w)) * Complex.exp (-((a : ℂ) * w))
        = Complex.exp (-(2 * (a : ℂ) * w)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h3 : Complex.exp ((a : ℂ) * w) * Complex.exp (-((a : ℂ) * w)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [← hA, ← hB]
    linear_combination (A ^ (2 : ℕ)) * h1 + (B ^ (2 : ℕ)) * h2 + (2 * A * B) * h3
  have hsplitPos : Complex.exp (2 * (a : ℂ) * w)
      = ((Real.exp (2 * a * δ) : ℝ) : ℂ) * Complex.exp (((2 * a * T : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hw, quartetEdge]
    push_cast
    ring
  have hsplitNeg : Complex.exp (-(2 * (a : ℂ) * w))
      = ((Real.exp (-(2 * a * δ)) : ℝ) : ℂ)
        * Complex.exp (-(((2 * a * T : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [hw, quartetEdge]
    push_cast
    ring
  rw [quartetContribution, hsq, hsplitPos, hsplitNeg]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring


/-! ## The cofinal negative aperture sequence -/

/-- The aperture sequence putting the leading quartet phase at `π`. -/
def apertureSeq (A : ℂ) (T : ℝ) (k : ℕ) : ℝ :=
  (Real.pi - 2 * A.arg + 2 * Real.pi * k) / (2 * T)

/-- **Equation `(9)`.**  At these apertures the leading oscillatory factor is exactly `-‖A‖²`. -/
theorem exp_apertureSeq_mul_sq (A : ℂ) {T : ℝ} (hT : 0 < T) (k : ℕ) :
    Complex.exp (((2 * apertureSeq A T k * T : ℝ) : ℂ) * Complex.I) * A ^ (2 : ℕ)
      = -((‖A‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hphase : (2 * apertureSeq A T k * T : ℝ) = Real.pi - 2 * A.arg + 2 * Real.pi * k := by
    rw [apertureSeq]
    field_simp
  set r : ℝ := ‖A‖ with hr
  set θ : ℝ := A.arg with hθ
  have hA : A = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [hr, hθ]; exact (Complex.norm_mul_exp_arg_mul_I A).symm
  have hsq : (Complex.exp ((θ : ℂ) * Complex.I)) ^ (2 : ℕ)
      = Complex.exp (2 * (θ : ℂ) * Complex.I) := by
    rw [sq, ← Complex.exp_add]; congr 1; ring
  have hexp : Complex.exp (((Real.pi - 2 * θ + 2 * Real.pi * (k : ℕ) : ℝ) : ℂ) * Complex.I)
      * Complex.exp (2 * (θ : ℂ) * Complex.I) = -1 := by
    rw [← Complex.exp_add]
    have hval : ((Real.pi - 2 * θ + 2 * Real.pi * (k : ℕ) : ℝ) : ℂ) * Complex.I
        + 2 * (θ : ℂ) * Complex.I
        = (Real.pi : ℂ) * Complex.I + (k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hval, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hphase, hA, mul_pow, hsq]
  rw [show (Complex.exp (((Real.pi - 2 * θ + 2 * Real.pi * (k : ℕ) : ℝ) : ℂ) * Complex.I)
      * ((r : ℂ) ^ (2 : ℕ) * Complex.exp (2 * (θ : ℂ) * Complex.I)))
      = ((r : ℂ) ^ (2 : ℕ)) * (Complex.exp (((Real.pi - 2 * θ + 2 * Real.pi * (k : ℕ) : ℝ) : ℂ)
        * Complex.I) * Complex.exp (2 * (θ : ℂ) * Complex.I)) from by ring]
  rw [hexp]
  push_cast
  ring

theorem apertureSeq_atTop (A : ℂ) {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (apertureSeq A T) Filter.atTop Filter.atTop := by
  have hfun : apertureSeq A T
      = fun k : ℕ => (Real.pi / T) * (k : ℝ) + (Real.pi - 2 * A.arg) / (2 * T) := by
    funext k
    rw [apertureSeq]
    field_simp
    ring
  rw [hfun]
  refine Filter.tendsto_atTop_add_const_right _ _ ?_
  exact Filter.Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop

/-! ## The cofinal divergence -/

open Filter in
/-- **Equation `(10)`, bound form.**  At the chosen apertures the quartet contribution is the
exponentially growing negative leading term plus a bounded remainder. -/
theorem quartetContribution_apertureSeq_le (f : ℝ → ℝ) (L δ T : ℝ) {hT : 0 < T} {k : ℕ}
    (hak : 0 ≤ apertureSeq (edgeLaplace f L (quartetEdge δ T)) T k) (hδ : 0 ≤ δ) :
    quartetContribution f L (apertureSeq (edgeLaplace f L (quartetEdge δ T)) T k)
        (quartetEdge δ T)
      ≤ -(4 * ‖edgeLaplace f L (quartetEdge δ T)‖ ^ (2 : ℕ))
          * Real.exp (2 * apertureSeq (edgeLaplace f L (quartetEdge δ T)) T k * δ)
        + (8 * (‖edgeLaplace f L (quartetEdge δ T)‖
              * ‖edgeLaplace f L (-(quartetEdge δ T))‖)
            + 4 * ‖edgeLaplace f L (-(quartetEdge δ T))‖ ^ (2 : ℕ)) := by
  set A : ℂ := edgeLaplace f L (quartetEdge δ T) with hA
  set B : ℂ := edgeLaplace f L (-(quartetEdge δ T)) with hB
  set a : ℝ := apertureSeq A T k with ha
  rw [quartetContribution_expand]
  have hlead : (Complex.exp (((2 * a * T : ℝ) : ℂ) * Complex.I) * A ^ (2 : ℕ)).re = -‖A‖ ^ (2 : ℕ) := by
    rw [ha, exp_apertureSeq_mul_sq A hT k]
    rw [Complex.neg_re, Complex.ofReal_re]
  have hmid : (A * B).re ≤ ‖A‖ * ‖B‖ := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul]
  have htail : (Complex.exp (-(((2 * a * T : ℝ) : ℂ) * Complex.I)) * B ^ (2 : ℕ)).re ≤ ‖B‖ ^ (2 : ℕ) := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, norm_pow]
    have hnorm : ‖Complex.exp (-(((2 * a * T : ℝ) : ℂ) * Complex.I))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (-(((2 * a * T : ℝ) : ℂ) * Complex.I)).re = 0 := by
        simp [Complex.mul_re]
      rw [hre, Real.exp_zero]
    rw [hnorm, one_mul]
  have hexpneg : Real.exp (-(2 * a * δ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 2 * a * δ := by positivity
    linarith
  have hBsq : (0 : ℝ) ≤ ‖B‖ ^ (2 : ℕ) := by positivity
  have hexppos : (0 : ℝ) < Real.exp (2 * a * δ) := Real.exp_pos _
  rw [hlead]
  have hterm3 : 4 * Real.exp (-(2 * a * δ))
      * (Complex.exp (-(((2 * a * T : ℝ) : ℂ) * Complex.I)) * B ^ (2 : ℕ)).re
      ≤ 4 * ‖B‖ ^ (2 : ℕ) := by
    have h1 : Real.exp (-(2 * a * δ))
        * (Complex.exp (-(((2 * a * T : ℝ) : ℂ) * Complex.I)) * B ^ (2 : ℕ)).re
        ≤ Real.exp (-(2 * a * δ)) * ‖B‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
    have h2 : Real.exp (-(2 * a * δ)) * ‖B‖ ^ (2 : ℕ) ≤ 1 * ‖B‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hexpneg hBsq
    linarith
  nlinarith [hmid, hterm3, hexppos]

open Filter in
/-- **Equation `(10)`.**  For a fixed off-line quartet with nonzero profile transform, the quartet
contribution tends to `-∞` along the aperture sequence. -/
theorem tendsto_quartetContribution_atBot (f : ℝ → ℝ) (L δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (hAne : edgeLaplace f L (quartetEdge δ T) ≠ 0) :
    Tendsto (fun k : ℕ => quartetContribution f L
        (apertureSeq (edgeLaplace f L (quartetEdge δ T)) T k) (quartetEdge δ T))
      atTop atBot := by
  set A : ℂ := edgeLaplace f L (quartetEdge δ T) with hA
  set B : ℂ := edgeLaplace f L (-(quartetEdge δ T)) with hB
  have hseq : Tendsto (apertureSeq A T) atTop atTop := apertureSeq_atTop A hT
  have hlin : Tendsto (fun k : ℕ => 2 * apertureSeq A T k * δ) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hδ (Filter.Tendsto.const_mul_atTop (by norm_num) hseq)
  have hexp : Tendsto (fun k : ℕ => Real.exp (2 * apertureSeq A T k * δ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hApos : (0 : ℝ) < 4 * ‖A‖ ^ (2 : ℕ) := by
    have : (0 : ℝ) < ‖A‖ := norm_pos_iff.mpr hAne
    positivity
  have hgrow : Tendsto (fun k : ℕ => (4 * ‖A‖ ^ (2 : ℕ))
      * Real.exp (2 * apertureSeq A T k * δ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hApos hexp
  have hneg : Tendsto (fun k : ℕ => -((4 * ‖A‖ ^ (2 : ℕ))
      * Real.exp (2 * apertureSeq A T k * δ))) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hgrow
  have hbound : Tendsto (fun k : ℕ => -((4 * ‖A‖ ^ (2 : ℕ))
      * Real.exp (2 * apertureSeq A T k * δ))
      + (8 * (‖A‖ * ‖B‖) + 4 * ‖B‖ ^ (2 : ℕ))) atTop atBot :=
    Filter.tendsto_atBot_add_const_right _ _ hneg
  refine tendsto_atBot_mono' _ ?_ hbound
  have hev : ∀ᶠ k : ℕ in atTop, 0 ≤ apertureSeq A T k := hseq.eventually_ge_atTop 0
  filter_upwards [hev] with k hk
  have h := quartetContribution_apertureSeq_le f L δ T (hT := hT) (k := k) hk hδ.le
  simpa [hA, hB] using h


open Filter in
/-- **Equation `(13)`.**  Against any uniformly bounded background, the quartet-augmented form is
negative along the aperture sequence. -/
theorem eventually_augmented_neg (f : ℝ → ℝ) (L δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (hAne : edgeLaplace f L (quartetEdge δ T) ≠ 0) (bg : ℝ → ℝ) {Kbg : ℝ}
    (hbg : ∀ a : ℝ, |bg a| ≤ Kbg) :
    ∀ᶠ k : ℕ in atTop,
      quartetContribution f L (apertureSeq (edgeLaplace f L (quartetEdge δ T)) T k)
          (quartetEdge δ T)
        + bg (apertureSeq (edgeLaplace f L (quartetEdge δ T)) T k) < 0 := by
  have htend := tendsto_quartetContribution_atBot f L δ T hδ hT hAne
  have hev := htend.eventually (Filter.eventually_lt_atBot (-Kbg))
  filter_upwards [hev] with k hk
  have hb := (abs_le.mp (hbg (apertureSeq (edgeLaplace f L (quartetEdge δ T)) T k))).2
  linarith


/-! ## The imaginary-axis bound -/

/-- **Equation `(11)`.**  On the imaginary axis the aperture factor has modulus one. -/
theorem norm_twoEdgeTransform_imaginary_le (f : ℝ → ℝ) (L a t : ℝ) :
    ‖twoEdgeTransform f L a ((t : ℂ) * Complex.I)‖
      ≤ ‖edgeLaplace f L ((t : ℂ) * Complex.I)‖
        + ‖edgeLaplace f L (-((t : ℂ) * Complex.I))‖ := by
  rw [twoEdgeTransform_eq]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖Complex.exp ((a : ℂ) * ((t : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : ((a : ℂ) * ((t : ℂ) * Complex.I)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  have h2 : ‖Complex.exp (-((a : ℂ) * ((t : ℂ) * Complex.I)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-((a : ℂ) * ((t : ℂ) * Complex.I))).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  rw [norm_mul, norm_mul, h1, h2, one_mul, one_mul]


/-- **Equation `(12)`, pointwise form.**  On the imaginary axis the quartet contribution is bounded
by the profile transform data alone, uniformly in the aperture. -/
theorem abs_quartetContribution_imaginary_le (f : ℝ → ℝ) (L a t : ℝ) :
    |quartetContribution f L a ((t : ℂ) * Complex.I)|
      ≤ 4 * (‖edgeLaplace f L ((t : ℂ) * Complex.I)‖
          + ‖edgeLaplace f L (-((t : ℂ) * Complex.I))‖) ^ (2 : ℕ) := by
  set G : ℂ := twoEdgeTransform f L a ((t : ℂ) * Complex.I) with hG
  set S : ℝ := ‖edgeLaplace f L ((t : ℂ) * Complex.I)‖
      + ‖edgeLaplace f L (-((t : ℂ) * Complex.I))‖ with hS
  have hGS : ‖G‖ ≤ S := norm_twoEdgeTransform_imaginary_le f L a t
  have hSnn : 0 ≤ S := le_trans (norm_nonneg _) hGS
  have hre : |(G ^ (2 : ℕ)).re| ≤ ‖G‖ ^ (2 : ℕ) := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_pow]
  have hsq : ‖G‖ ^ (2 : ℕ) ≤ S ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ (norm_nonneg _) hGS 2
  rw [quartetContribution, abs_mul]
  have h4 : |(4 : ℝ)| = 4 := by norm_num
  rw [h4]
  have : |(G ^ (2 : ℕ)).re| ≤ S ^ (2 : ℕ) := le_trans hre hsq
  linarith

/-- Summability of the all-line background, uniformly in the aperture. -/
theorem summable_quartetContribution_imaginary (f : ℝ → ℝ) (L a : ℝ) (t : ℕ → ℝ)
    (hsum : Summable fun n => (‖edgeLaplace f L ((t n : ℂ) * Complex.I)‖
      + ‖edgeLaplace f L (-((t n : ℂ) * Complex.I))‖) ^ (2 : ℕ)) :
    Summable fun n => quartetContribution f L a ((t n : ℂ) * Complex.I) := by
  refine Summable.of_abs ?_
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    (fun n => abs_quartetContribution_imaginary_le f L a (t n)) ?_
  exact hsum.mul_left 4

/-- **Equation `(12)`.**  The all-line background is bounded by a constant independent of the
aperture. -/
theorem abs_tsum_quartetContribution_imaginary_le (f : ℝ → ℝ) (L a : ℝ) (t : ℕ → ℝ)
    (hsum : Summable fun n => (‖edgeLaplace f L ((t n : ℂ) * Complex.I)‖
      + ‖edgeLaplace f L (-((t n : ℂ) * Complex.I))‖) ^ (2 : ℕ)) :
    |∑' n, quartetContribution f L a ((t n : ℂ) * Complex.I)|
      ≤ 4 * ∑' n, (‖edgeLaplace f L ((t n : ℂ) * Complex.I)‖
          + ‖edgeLaplace f L (-((t n : ℂ) * Complex.I))‖) ^ (2 : ℕ) := by
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded (hsum.hasSum.mul_left 4) fun n => ?_
  rw [Real.norm_eq_abs]
  exact abs_quartetContribution_imaginary_le f L a (t n)


/-! ## The finite rightmost layer -/

open MeasureTheory in
/-- A single oscillatory term has a bounded primitive. -/
theorem norm_integral_oscillatory_le (c : ℂ) {T : ℝ} (hT : 0 < T) (Y : ℝ) :
    ‖∫ a in (0 : ℝ)..Y, c * Complex.exp (((2 * a * T : ℝ) : ℂ) * Complex.I)‖ ≤ ‖c‖ / T := by
  set c₀ : ℂ := 2 * (T : ℂ) * Complex.I with hc₀
  have hc₀ne : c₀ ≠ 0 := by
    rw [hc₀]
    have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hT)
    simp [hTne, Complex.I_ne_zero]
  have hfun : ∀ a : ℝ, c * Complex.exp (((2 * a * T : ℝ) : ℂ) * Complex.I)
      = c * Complex.exp (c₀ * (a : ℂ)) := by
    intro a
    congr 2
    rw [hc₀]
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun a _ => hfun a), intervalIntegral.integral_const_mul,
    integral_exp_mul_complex hc₀ne]
  rw [norm_mul, norm_div]
  have hnum : ‖Complex.exp (c₀ * (Y : ℂ)) - Complex.exp (c₀ * ((0 : ℝ) : ℂ))‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖Complex.exp (c₀ * (Y : ℂ))‖ = 1 := by
      rw [Complex.norm_exp, hc₀]
      have : (2 * (T : ℂ) * Complex.I * (Y : ℂ)).re = 0 := by simp [Complex.mul_re]
      rw [this, Real.exp_zero]
    have h2 : ‖Complex.exp (c₀ * ((0 : ℝ) : ℂ))‖ = 1 := by
      simp
    rw [h1, h2]
    norm_num
  have hden : ‖c₀‖ = 2 * T := by
    rw [hc₀, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hT]
    norm_num
  rw [hden]
  have hTpos : (0 : ℝ) < 2 * T := by linarith
  calc ‖c‖ * (‖Complex.exp (c₀ * (Y : ℂ)) - Complex.exp (c₀ * ((0 : ℝ) : ℂ))‖ / (2 * T))
      ≤ ‖c‖ * (2 / (2 * T)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact div_le_div_of_nonneg_right hnum hTpos.le
    _ = ‖c‖ / T := by field_simp


open MeasureTheory in
/-- The finite trigonometric polynomial and its bounded primitive. -/
theorem abs_integral_trigPolynomial_le {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ)
    (hT : ∀ j, 0 < T j) (Y : ℝ) :
    ‖∫ a in (0 : ℝ)..Y, ∑ j, c j * Complex.exp (((2 * a * T j : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ j, ‖c j‖ / T j := by
  have hint : ∀ j : Fin r, IntervalIntegrable
      (fun a : ℝ => c j * Complex.exp (((2 * a * T j : ℝ) : ℂ) * Complex.I)) volume 0 Y := by
    intro j
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun j _ => hint j)]
  refine le_trans (norm_sum_le _ _) ?_
  exact Finset.sum_le_sum fun j _ => norm_integral_oscillatory_le (c j) (hT j) Y


/-! ## Parseval for finite trigonometric polynomials -/

open MeasureTheory in
/-- The primitive bound at any nonzero frequency. -/
theorem norm_integral_oscillatory_le' (c : ℂ) {T : ℝ} (hT : T ≠ 0) (Y : ℝ) :
    ‖∫ a in (0 : ℝ)..Y, c * Complex.exp (((2 * a * T : ℝ) : ℂ) * Complex.I)‖ ≤ ‖c‖ / |T| := by
  set c₀ : ℂ := 2 * (T : ℂ) * Complex.I with hc₀
  have hc₀ne : c₀ ≠ 0 := by
    rw [hc₀]
    have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
    simp [hTne, Complex.I_ne_zero]
  have hfun : ∀ a : ℝ, c * Complex.exp (((2 * a * T : ℝ) : ℂ) * Complex.I)
      = c * Complex.exp (c₀ * (a : ℂ)) := by
    intro a
    congr 2
    rw [hc₀]
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun a _ => hfun a), intervalIntegral.integral_const_mul,
    integral_exp_mul_complex hc₀ne, norm_mul, norm_div]
  have hnum : ‖Complex.exp (c₀ * (Y : ℂ)) - Complex.exp (c₀ * ((0 : ℝ) : ℂ))‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖Complex.exp (c₀ * (Y : ℂ))‖ = 1 := by
      rw [Complex.norm_exp, hc₀]
      have hz : (2 * (T : ℂ) * Complex.I * (Y : ℂ)).re = 0 := by simp [Complex.mul_re]
      rw [hz, Real.exp_zero]
    have h2 : ‖Complex.exp (c₀ * ((0 : ℝ) : ℂ))‖ = 1 := by simp
    rw [h1, h2]
    norm_num
  have hden : ‖c₀‖ = 2 * |T| := by
    rw [hc₀, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  rw [hden]
  have hTpos : (0 : ℝ) < 2 * |T| := by
    have : (0 : ℝ) < |T| := abs_pos.mpr hT
    linarith
  calc ‖c‖ * (‖Complex.exp (c₀ * (Y : ℂ)) - Complex.exp (c₀ * ((0 : ℝ) : ℂ))‖ / (2 * |T|))
      ≤ ‖c‖ * (2 / (2 * |T|)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact div_le_div_of_nonneg_right hnum hTpos.le
    _ = ‖c‖ / |T| := by
        rw [show (2 : ℝ) / (2 * |T|) = 1 / |T| from by field_simp]
        ring

theorem re_sq_eq (z : ℂ) : z.re ^ (2 : ℕ) = ((z ^ (2 : ℕ)).re + ‖z‖ ^ (2 : ℕ)) / 2 := by
  have hsq : (z ^ (2 : ℕ)).re = z.re * z.re - z.im * z.im := by
    rw [sq, Complex.mul_re]
  rw [hsq, Complex.sq_norm, Complex.normSq_apply]
  ring


/-- The complex trigonometric polynomial with frequencies `2T j`. -/
def trigPoly {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ) (a : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (((2 * a * T j : ℝ) : ℂ) * Complex.I)

theorem trigPoly_sq {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ) (a : ℝ) :
    (trigPoly c T a) ^ (2 : ℕ)
      = ∑ j, ∑ k, (c j * c k)
          * Complex.exp (((2 * a * (T j + T k) : ℝ) : ℂ) * Complex.I) := by
  rw [trigPoly, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [show (c j * Complex.exp (((2 * a * T j : ℝ) : ℂ) * Complex.I))
        * (c k * Complex.exp (((2 * a * T k : ℝ) : ℂ) * Complex.I))
      = (c j * c k) * (Complex.exp (((2 * a * T j : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((2 * a * T k : ℝ) : ℂ) * Complex.I)) from by ring]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem conj_trigPoly {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ) (a : ℝ) :
    (starRingEnd ℂ) (trigPoly c T a)
      = ∑ k, (starRingEnd ℂ) (c k)
          * Complex.exp ((-(2 * a * T k : ℝ) : ℝ) * Complex.I) := by
  rw [trigPoly, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem trigPoly_normSq {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ) (a : ℝ) :
    ((‖trigPoly c T a‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ j, ∑ k, (c j * (starRingEnd ℂ) (c k))
          * Complex.exp (((2 * a * (T j - T k) : ℝ) : ℂ) * Complex.I) := by
  have hmul : trigPoly c T a * (starRingEnd ℂ) (trigPoly c T a)
      = ((‖trigPoly c T a‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  rw [← hmul, conj_trigPoly, trigPoly, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [show (c j * Complex.exp (((2 * a * T j : ℝ) : ℂ) * Complex.I))
        * ((starRingEnd ℂ) (c k) * Complex.exp ((-(2 * a * T k : ℝ) : ℝ) * Complex.I))
      = (c j * (starRingEnd ℂ) (c k)) * (Complex.exp (((2 * a * T j : ℝ) : ℂ) * Complex.I)
        * Complex.exp ((-(2 * a * T k : ℝ) : ℝ) * Complex.I)) from by ring]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem trigPolyRe_sq {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ) (a : ℝ) :
    ((trigPoly c T a).re) ^ (2 : ℕ)
      = ((∑ j, ∑ k, (c j * c k)
            * Complex.exp (((2 * a * (T j + T k) : ℝ) : ℂ) * Complex.I)).re
        + (∑ j, ∑ k, (c j * (starRingEnd ℂ) (c k))
            * Complex.exp (((2 * a * (T j - T k) : ℝ) : ℂ) * Complex.I)).re) / 2 := by
  rw [re_sq_eq, trigPoly_sq]
  congr 2
  rw [← trigPoly_normSq, Complex.ofReal_re]


open MeasureTheory in
/-- The primitive bound for a finite indexed family of nonzero frequencies. -/
theorem norm_integral_indexedSum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℂ)
    (lam : ι → ℝ) (hlam : ∀ i ∈ s, lam i ≠ 0) (Y : ℝ) :
    ‖∫ a in (0 : ℝ)..Y, ∑ i ∈ s, d i
        * Complex.exp (((2 * a * lam i : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ i ∈ s, ‖d i‖ / |lam i| := by
  have hint : ∀ i ∈ s, IntervalIntegrable
      (fun a : ℝ => d i * Complex.exp (((2 * a * lam i : ℝ) : ℂ) * Complex.I)) volume 0 Y := by
    intro i _
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_finsetSum hint]
  refine le_trans (norm_sum_le _ _) ?_
  exact Finset.sum_le_sum fun i hi => norm_integral_oscillatory_le' (d i) (hlam i hi) Y

open MeasureTheory in
theorem continuous_trigPolyTerm {ι : Type*} (d : ι → ℂ) (lam : ι → ℝ) (i : ι) :
    Continuous fun a : ℝ => d i * Complex.exp (((2 * a * lam i : ℝ) : ℂ) * Complex.I) := by
  fun_prop

open MeasureTheory in
/-- **Parseval for a finite trigonometric polynomial.**  The mean square grows linearly in the
coefficient energy, with a remainder bounded independently of the length of the interval. -/
theorem abs_integral_trigPolyRe_sq_sub_le {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ)
    (hT : ∀ j, 0 < T j) (hinj : Function.Injective T) (Y : ℝ) :
    |(∫ a in (0 : ℝ)..Y, ((trigPoly c T a).re) ^ (2 : ℕ)) - (Y / 2) * (∑ j, ‖c j‖ ^ (2 : ℕ))|
      ≤ ((∑ j, ∑ k, ‖c j * c k‖ / |T j + T k|)
          + ∑ j, ∑ k ∈ Finset.univ.erase j,
              ‖c j * (starRingEnd ℂ) (c k)‖ / |T j - T k|) / 2 := by
  classical
  set Ssum : ℝ → ℂ := fun a => ∑ j, ∑ k, (c j * c k)
      * Complex.exp (((2 * a * (T j + T k) : ℝ) : ℂ) * Complex.I) with hSsum
  set Dsum : ℝ → ℂ := fun a => ∑ j, ∑ k, (c j * (starRingEnd ℂ) (c k))
      * Complex.exp (((2 * a * (T j - T k) : ℝ) : ℂ) * Complex.I) with hDsum
  have hcontS : Continuous Ssum := by
    rw [hSsum]
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => by fun_prop
  have hcontD : Continuous Dsum := by
    rw [hDsum]
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => by fun_prop
  have hpt : ∀ a : ℝ, ((trigPoly c T a).re) ^ (2 : ℕ) = ((Ssum a).re + (Dsum a).re) / 2 := by
    intro a
    exact trigPolyRe_sq c T a
  have hintS : IntervalIntegrable (fun a : ℝ => (Ssum a).re) volume 0 Y :=
    (Complex.continuous_re.comp hcontS).intervalIntegrable 0 Y
  have hintD : IntervalIntegrable (fun a : ℝ => (Dsum a).re) volume 0 Y :=
    (Complex.continuous_re.comp hcontD).intervalIntegrable 0 Y
  have hsplit : (∫ a in (0 : ℝ)..Y, ((trigPoly c T a).re) ^ (2 : ℕ))
      = ((∫ a in (0 : ℝ)..Y, (Ssum a).re) + ∫ a in (0 : ℝ)..Y, (Dsum a).re) / 2 := by
    rw [intervalIntegral.integral_congr (g := fun a : ℝ => ((Ssum a).re + (Dsum a).re) / 2)
      (fun a _ => hpt a)]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hintS hintD]
  rw [hsplit]
  -- the `A²` half is bounded
  have hSint : ∀ j : Fin r, IntervalIntegrable
      (fun a : ℝ => ∑ k, (c j * c k)
        * Complex.exp (((2 * a * (T j + T k) : ℝ) : ℂ) * Complex.I)) volume 0 Y := by
    intro j
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun k _ => by fun_prop
  have hSbound : ‖∫ a in (0 : ℝ)..Y, Ssum a‖ ≤ ∑ j, ∑ k, ‖c j * c k‖ / |T j + T k| := by
    rw [hSsum, intervalIntegral.integral_finsetSum (fun j _ => hSint j)]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    exact norm_integral_indexedSum_le Finset.univ (fun k => c j * c k)
      (fun k => T j + T k) (fun k _ => ne_of_gt (by linarith [hT j, hT k])) Y
  have hSre : (∫ a in (0 : ℝ)..Y, (Ssum a).re) = (∫ a in (0 : ℝ)..Y, Ssum a).re :=
    intervalIntegral_re (hcontS.intervalIntegrable 0 Y)
  have hSabs : |∫ a in (0 : ℝ)..Y, (Ssum a).re|
      ≤ ∑ j, ∑ k, ‖c j * c k‖ / |T j + T k| := by
    rw [hSre]
    exact le_trans (Complex.abs_re_le_norm _) hSbound
  -- the `|A|²` half splits into the diagonal and a bounded remainder
  set Doff : ℝ → ℂ := fun a => ∑ j, ∑ k ∈ Finset.univ.erase j,
    (c j * (starRingEnd ℂ) (c k))
      * Complex.exp (((2 * a * (T j - T k) : ℝ) : ℂ) * Complex.I) with hDoff
  have hcontDoff : Continuous Doff := by
    rw [hDoff]
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => by fun_prop
  have hDsplit : ∀ a : ℝ, Dsum a = ((∑ j, ‖c j‖ ^ (2 : ℕ) : ℝ) : ℂ) + Doff a := by
    intro a
    rw [hDsum, hDoff, Complex.ofReal_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    have hzero : T j - T j = 0 := by ring
    rw [hzero]
    have hexp : Complex.exp (((2 * a * (0 : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
      norm_num
    rw [hexp, mul_one, Complex.mul_conj, Complex.sq_norm]
  have hDoffbound : ‖∫ a in (0 : ℝ)..Y, Doff a‖
      ≤ ∑ j, ∑ k ∈ Finset.univ.erase j, ‖c j * (starRingEnd ℂ) (c k)‖ / |T j - T k| := by
    have hDint : ∀ j : Fin r, IntervalIntegrable
        (fun a : ℝ => ∑ k ∈ Finset.univ.erase j, (c j * (starRingEnd ℂ) (c k))
          * Complex.exp (((2 * a * (T j - T k) : ℝ) : ℂ) * Complex.I)) volume 0 Y := by
      intro j
      apply Continuous.intervalIntegrable
      exact continuous_finsetSum _ fun k _ => by fun_prop
    rw [hDoff, intervalIntegral.integral_finsetSum (fun j _ => hDint j)]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    refine norm_integral_indexedSum_le (Finset.univ.erase j) (fun k => c j * (starRingEnd ℂ) (c k))
      (fun k => T j - T k) (fun k hk => ?_) Y
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    intro hzero
    exact hkj (hinj (by linarith [sub_eq_zero.mp hzero]))
  have hDre : (∫ a in (0 : ℝ)..Y, (Dsum a).re)
      = Y * (∑ j, ‖c j‖ ^ (2 : ℕ)) + (∫ a in (0 : ℝ)..Y, Doff a).re := by
    have hfun : (fun a : ℝ => (Dsum a).re)
        = fun a : ℝ => (∑ j, ‖c j‖ ^ (2 : ℕ)) + (Doff a).re := by
      funext a
      rw [hDsplit a, Complex.add_re, Complex.ofReal_re]
    have hoff : (∫ a in (0 : ℝ)..Y, (Doff a).re) = (∫ a in (0 : ℝ)..Y, Doff a).re :=
      intervalIntegral_re (hcontDoff.intervalIntegrable 0 Y)
    rw [hfun, intervalIntegral.integral_add
      (f := fun _ : ℝ => (∑ j, ‖c j‖ ^ (2 : ℕ))) (g := fun a : ℝ => (Doff a).re)
      intervalIntegrable_const
      ((Complex.continuous_re.comp hcontDoff).intervalIntegrable 0 Y),
      intervalIntegral.integral_const, hoff]
    simp [smul_eq_mul]
  have hDabs : |(∫ a in (0 : ℝ)..Y, (Dsum a).re) - Y * (∑ j, ‖c j‖ ^ (2 : ℕ))|
      ≤ ∑ j, ∑ k ∈ Finset.univ.erase j,
          ‖c j * (starRingEnd ℂ) (c k)‖ / |T j - T k| := by
    rw [hDre]
    have hval : Y * (∑ j, ‖c j‖ ^ (2 : ℕ)) + (∫ a in (0 : ℝ)..Y, Doff a).re
        - Y * (∑ j, ‖c j‖ ^ (2 : ℕ)) = (∫ a in (0 : ℝ)..Y, Doff a).re := by ring
    rw [hval]
    exact le_trans (Complex.abs_re_le_norm _) hDoffbound
  have h1 := abs_le.mp hSabs
  have h2 := abs_le.mp hDabs
  refine abs_le.mpr ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩


open MeasureTheory in
theorem continuous_trigPoly {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ) :
    Continuous (trigPoly c T) := by
  unfold trigPoly
  exact continuous_finsetSum _ fun j _ => by fun_prop

theorem norm_trigPoly_le {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ) (a : ℝ) :
    ‖trigPoly c T a‖ ≤ ∑ j, ‖c j‖ := by
  unfold trigPoly
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_exp]
  have hre : (((2 * a * T j : ℝ) : ℂ) * Complex.I).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero, mul_one]

open MeasureTheory in
theorem abs_integral_trigPolyRe_le {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ)
    (hT : ∀ j, 0 < T j) (Y : ℝ) :
    |∫ a in (0 : ℝ)..Y, (trigPoly c T a).re| ≤ ∑ j, ‖c j‖ / T j := by
  have hre : (∫ a in (0 : ℝ)..Y, (trigPoly c T a).re)
      = (∫ a in (0 : ℝ)..Y, trigPoly c T a).re :=
    intervalIntegral_re ((continuous_trigPoly c T).intervalIntegrable 0 Y)
  rw [hre]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  exact abs_integral_trigPolynomial_le c T hT Y

set_option maxHeartbeats 2000000 in
open MeasureTheory in
/-- **Equation `(15)`.**  A nonzero finite real trigonometric polynomial with distinct strictly
positive frequencies drops below a fixed negative level at arbitrarily large apertures. -/
theorem exists_neg_trigPolyRe {r : ℕ} (c : Fin r → ℂ) (T : Fin r → ℝ)
    (hT : ∀ j, 0 < T j) (hinj : Function.Injective T) (hne : ∃ j, c j ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ A₀ : ℝ, ∃ a : ℝ, A₀ ≤ a ∧ (trigPoly c T a).re ≤ -η := by
  classical
  set P : ℝ → ℝ := fun a => (trigPoly c T a).re with hP
  set S : ℝ := ∑ j, ‖c j‖ ^ (2 : ℕ) with hSdef
  set B : ℝ := ∑ j, ‖c j‖ with hBdef
  set M₀ : ℝ := ∑ j, ‖c j‖ / T j with hM₀
  set C : ℝ := ((∑ j, ∑ k, ‖c j * c k‖ / |T j + T k|)
    + ∑ j, ∑ k ∈ Finset.univ.erase j,
        ‖c j * (starRingEnd ℂ) (c k)‖ / |T j - T k|) / 2 with hC
  have hSpos : 0 < S := by
    obtain ⟨j₀, hj₀⟩ := hne
    rw [hSdef]
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨j₀, Finset.mem_univ j₀, ?_⟩
    have : 0 < ‖c j₀‖ := norm_pos_iff.mpr hj₀
    positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hM₀nn : 0 ≤ M₀ := by
    rw [hM₀]
    refine Finset.sum_nonneg fun j _ => ?_
    exact div_nonneg (norm_nonneg _) (hT j).le
  have hCnn : 0 ≤ C := by
    rw [hC]
    refine div_nonneg (add_nonneg ?_ ?_) (by norm_num)
    · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
    · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  set η : ℝ := min 1 (S / (4 * (B + 1))) with hη
  have hBpos : 0 < B + 1 := by linarith
  have hηpos : 0 < η := by
    rw [hη]
    refine lt_min one_pos ?_
    positivity
  have hηle1 : η ≤ 1 := min_le_left _ _
  have hηkey : (B + η) * η ≤ S / 4 := by
    have h1 : (B + η) * η ≤ (B + 1) * η := by nlinarith
    have h2 : η ≤ S / (4 * (B + 1)) := min_le_right _ _
    have h3 : (B + 1) * η ≤ (B + 1) * (S / (4 * (B + 1))) :=
      mul_le_mul_of_nonneg_left h2 hBpos.le
    have h4 : (B + 1) * (S / (4 * (B + 1))) = S / 4 := by field_simp
    linarith
  refine ⟨η, hηpos, fun A₀ => ?_⟩
  by_contra hcontra
  have hcon : ∀ a : ℝ, A₀ ≤ a → -η < P a := by
    intro a ha
    by_contra hle
    exact hcontra ⟨a, ha, not_lt.mp hle⟩
  have hPcont : Continuous P := Complex.continuous_re.comp (continuous_trigPoly c T)
  have hPbound : ∀ a : ℝ, |P a| ≤ B := fun a =>
    le_trans (Complex.abs_re_le_norm _) (norm_trigPoly_le c T a)
  -- choose a large aperture window
  set K : ℝ := 2 * C + 2 * (B + η) * M₀ + 4 * η * M₀ with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    have : 0 ≤ (B + η) := by linarith
    positivity
  set Z : ℝ := 4 * K / S + 1 with hZ
  have hZpos : 0 < Z := by
    rw [hZ]
    have : 0 ≤ 4 * K / S := by positivity
    linarith
  set Y : ℝ := A₀ + Z with hY
  have hAY : A₀ ≤ Y := by rw [hY]; linarith
  -- pointwise facts on `[A₀, Y]`
  have hQnn : ∀ a ∈ Set.uIcc A₀ Y, 0 ≤ P a + η := by
    intro a ha
    rw [Set.uIcc_of_le hAY] at ha
    have := hcon a ha.1
    linarith
  have hQle : ∀ a ∈ Set.uIcc A₀ Y, (P a + η) ^ (2 : ℕ) ≤ (B + η) * (P a + η) := by
    intro a ha
    have h0 := hQnn a ha
    have hb := (abs_le.mp (hPbound a)).2
    nlinarith
  -- integral comparisons
  have hint1 : IntervalIntegrable (fun a => (P a + η) ^ (2 : ℕ)) volume A₀ Y :=
    (((hPcont.add continuous_const)).pow 2).intervalIntegrable A₀ Y
  have hint2 : IntervalIntegrable (fun a => (B + η) * (P a + η)) volume A₀ Y :=
    ((continuous_const.mul (hPcont.add continuous_const))).intervalIntegrable A₀ Y
  have hmono : (∫ a in A₀..Y, (P a + η) ^ (2 : ℕ)) ≤ ∫ a in A₀..Y, (B + η) * (P a + η) :=
    intervalIntegral.integral_mono_on hAY hint1 hint2 (fun a ha => hQle a (by
      rw [Set.uIcc_of_le hAY]; exact ha))
  -- integrability of the pieces
  have hPint : IntervalIntegrable P volume A₀ Y := hPcont.intervalIntegrable A₀ Y
  have hP2int : IntervalIntegrable (fun a => P a ^ (2 : ℕ)) volume A₀ Y :=
    (hPcont.pow 2).intervalIntegrable A₀ Y
  -- the linear integral
  set I : ℝ := ∫ a in A₀..Y, P a with hI
  have hIsplit : I = (∫ a in (0 : ℝ)..Y, P a) - ∫ a in (0 : ℝ)..A₀, P a := by
    rw [hI]
    exact (intervalIntegral.integral_interval_sub_left (hPcont.intervalIntegrable 0 Y)
      (hPcont.intervalIntegrable 0 A₀)).symm
  have hIbound : |I| ≤ 2 * M₀ := by
    rw [hIsplit, hP]
    have h1 := abs_le.mp (abs_integral_trigPolyRe_le c T hT Y)
    have h2 := abs_le.mp (abs_integral_trigPolyRe_le c T hT A₀)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- the quadratic integral
  set J : ℝ := ∫ a in A₀..Y, P a ^ (2 : ℕ) with hJ
  have hJsplit : J = (∫ a in (0 : ℝ)..Y, P a ^ (2 : ℕ)) - ∫ a in (0 : ℝ)..A₀, P a ^ (2 : ℕ) := by
    rw [hJ]
    exact (intervalIntegral.integral_interval_sub_left
      ((hPcont.pow 2).intervalIntegrable 0 Y)
      ((hPcont.pow 2).intervalIntegrable 0 A₀)).symm
  have hJbound : ((Y - A₀) / 2) * S - 2 * C ≤ J := by
    rw [hJsplit, hP]
    have h1 := abs_le.mp (abs_integral_trigPolyRe_sq_sub_le c T hT hinj Y)
    have h2 := abs_le.mp (abs_integral_trigPolyRe_sq_sub_le c T hT hinj A₀)
    linarith [h1.1, h2.2]
  have hLHS : (∫ a in A₀..Y, (P a + η) ^ (2 : ℕ)) = J + 2 * η * I + η ^ (2 : ℕ) * (Y - A₀) := by
    have hfun : (fun a : ℝ => (P a + η) ^ (2 : ℕ))
        = fun a : ℝ => P a ^ (2 : ℕ) + (2 * η * P a + η ^ (2 : ℕ)) := by
      funext a; ring
    rw [hfun,
      intervalIntegral.integral_add (f := fun a : ℝ => P a ^ (2 : ℕ))
        (g := fun a : ℝ => 2 * η * P a + η ^ (2 : ℕ)) hP2int
        (((continuous_const.mul hPcont).add continuous_const).intervalIntegrable A₀ Y),
      intervalIntegral.integral_add (f := fun a : ℝ => 2 * η * P a) (g := fun _ : ℝ => η ^ (2 : ℕ))
        ((continuous_const.mul hPcont).intervalIntegrable A₀ Y) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, ← hJ, ← hI]
    simp only [smul_eq_mul]
    ring
  have hRHSint : (∫ a in A₀..Y, (B + η) * (P a + η)) = (B + η) * (I + η * (Y - A₀)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (f := P) (g := fun _ : ℝ => η) hPint
        intervalIntegrable_const,
      intervalIntegral.integral_const, ← hI]
    simp only [smul_eq_mul]
    ring
  rw [hLHS, hRHSint] at hmono
  have hZval : Y - A₀ = Z := by rw [hY]; ring
  rw [hZval] at hmono hJbound
  have hab := abs_le.mp hIbound
  have hIle : (B + η) * I - 2 * η * I ≤ 2 * (B + η) * M₀ + 4 * η * M₀ := by
    nlinarith [hab.1, hab.2, hBnn, hηpos.le, hM₀nn]
  have hcoef : S / 4 ≤ S / 2 + η ^ (2 : ℕ) - (B + η) * η := by
    nlinarith [hηkey, sq_nonneg η]
  have hkey : Z * (S / 2 + η ^ (2 : ℕ) - (B + η) * η) ≤ 2 * C + ((B + η) * I - 2 * η * I) := by
    nlinarith [hmono, hJbound]
  have hfinal : Z * (S / 4) ≤ K := by
    have h1 : Z * (S / 4) ≤ Z * (S / 2 + η ^ (2 : ℕ) - (B + η) * η) :=
      mul_le_mul_of_nonneg_left hcoef hZpos.le
    rw [hK]
    linarith [h1, hkey, hIle]
  have hzz : Z * (S / 4) = K + S / 4 := by
    rw [hZ]
    field_simp
  linarith [hfinal, hzz, hSpos]


end

end RHTower
