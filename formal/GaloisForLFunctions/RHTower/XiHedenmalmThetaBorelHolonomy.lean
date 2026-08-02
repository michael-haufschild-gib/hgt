import GaloisForLFunctions.RHTower.XiHedenmalmBoundaryValueProblem
import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity

/-!
# The Borel holonomy of the flat theta tail

The Hedenmalm boundary eigenfunction is the two-ended theta primitive

`u α x = exp (-i α x) ∫_{-∞}^{x} exp (i α y) k y dy`,

where `k` is the completed all-integer theta source.  At a zero of the centered completed Xi
function the same value is the negative of the right tail, and the right tail is superexponentially
flat at every order.

The substitution `y = x + log (1 + t) / 2` is an exact diffeomorphism from the open ray `(0,∞)` onto
`(x,∞)`.  In that chart the flat tail becomes a strictly positive source density multiplied by the
single complex dilation character

`M α t = exp (i α * log (1 + t) / 2) = (1 + t) ^ (i α / 2)`.

This module proves the exact factorization, the positivity and mass law of the source density, the
three pointwise multiplier laws (reflection, adjunction, radial drift), and the identification of
`M α` with the normalized dilation character `r ↦ r ^ (ρ - 1/2)` of the centered zero `ρ` at the
geometric samples `1 + t = r ^ (2 j)`.

Everything here is unconditional: no zero is placed on the critical line.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## The Borel chart -/

/-- The essential-tail chart of the theta right tail: the inverse of `t = exp (2 (y - x)) - 1`. -/
def hedenmalmBorelChart (t : ℝ) : ℝ := Real.log (1 + t) / 2

@[simp] theorem hedenmalmBorelChart_zero : hedenmalmBorelChart 0 = 0 := by
  simp [hedenmalmBorelChart]

theorem hedenmalmBorelChart_pos {t : ℝ} (ht : 0 < t) : 0 < hedenmalmBorelChart t := by
  have h : (1 : ℝ) < 1 + t := by linarith
  have := Real.log_pos h
  simpa [hedenmalmBorelChart] using by linarith

theorem hedenmalmBorelChart_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hedenmalmBorelChart t := by
  rcases ht.lt_or_eq with h | h
  · exact (hedenmalmBorelChart_pos h).le
  · simp [← h]

theorem hedenmalmBorelChart_exp (y : ℝ) :
    hedenmalmBorelChart (Real.exp (2 * y) - 1) = y := by
  rw [hedenmalmBorelChart]
  have : (1 : ℝ) + (Real.exp (2 * y) - 1) = Real.exp (2 * y) := by ring
  rw [this, Real.log_exp]
  ring

/-- The chart is a bijection from the open Borel ray onto the theta right tail. -/
theorem image_hedenmalmBorelChart (x : ℝ) :
    (fun t : ℝ => x + hedenmalmBorelChart t) '' Ioi 0 = Ioi x := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact mem_Ioi.mpr (by
      have := hedenmalmBorelChart_pos (mem_Ioi.mp ht)
      linarith)
  · intro hy
    refine ⟨Real.exp (2 * (y - x)) - 1, ?_, ?_⟩
    · have hpos : (0 : ℝ) < 2 * (y - x) := by
        have := mem_Ioi.mp hy
        linarith
      have : (1 : ℝ) < Real.exp (2 * (y - x)) := by
        simpa using Real.exp_lt_exp.mpr hpos
      exact mem_Ioi.mpr (by linarith)
    · simp [hedenmalmBorelChart_exp]

theorem injOn_hedenmalmBorelChart (x : ℝ) :
    Set.InjOn (fun t : ℝ => x + hedenmalmBorelChart t) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < 1 + a := by have := mem_Ioi.mp ha; linarith
  have hb' : (0 : ℝ) < 1 + b := by have := mem_Ioi.mp hb; linarith
  simp only [hedenmalmBorelChart, add_right_inj] at hab
  have hlog : Real.log (1 + a) = Real.log (1 + b) := by linarith
  have := Real.log_injOn_pos (mem_Ioi.mpr ha') (mem_Ioi.mpr hb') hlog
  linarith

theorem hasDerivAt_hedenmalmBorelChart (x : ℝ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (fun s : ℝ => x + hedenmalmBorelChart s)
      (1 / (1 + t) / 2) t := by
  have hne : (1 : ℝ) + t ≠ 0 := by linarith
  have hlin : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
    simpa using (hasDerivAt_id t).const_add (1 : ℝ)
  have hlog : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
    simpa using hlin.log hne
  simpa [hedenmalmBorelChart] using (hlog.div_const 2).const_add x

/-- The chart Jacobian in the normalized form used by the source density. -/
theorem abs_hedenmalmBorelChartJacobian (t : ℝ) (ht : 0 < t) :
    |1 / (1 + t) / 2| = 1 / (2 * (1 + t)) := by
  have ht' : (0 : ℝ) < 1 / (1 + t) / 2 := by positivity
  rw [abs_of_pos ht', div_div, mul_comm]

/-- **Exact logarithmic change of variables on the theta right tail.**  Every Bochner integral over
the tail `(x,∞)` becomes an integral over the fixed Borel ray `(0,∞)` with Jacobian
`1 / (2 (1 + t))`. -/
theorem integral_Ioi_eq_integral_hedenmalmBorelChart
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (x : ℝ) (g : ℝ → F) :
    ∫ y in Ioi x, g y =
      ∫ t in Ioi (0 : ℝ), (1 / (2 * (1 + t))) • g (x + hedenmalmBorelChart t) := by
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ => x + hedenmalmBorelChart s)
        (1 / (1 + t) / 2) (Ioi 0) t := by
    intro t ht
    exact (hasDerivAt_hedenmalmBorelChart x
      (by have := mem_Ioi.mp ht; linarith)).hasDerivWithinAt
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv (injOn_hedenmalmBorelChart x) g
  rw [image_hedenmalmBorelChart] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  simp only [abs_hedenmalmBorelChartJacobian t (mem_Ioi.mp ht)]

/-! ## The Borel character and the positive source density -/

/-- The universal complex dilation character carried by the theta tail in the Borel chart. -/
def hedenmalmBorelCharacter (alpha : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * alpha * (hedenmalmBorelChart t : ℂ))

/-- The positive source density of the theta right tail in the Borel chart. -/
def hedenmalmBorelDensity (x t : ℝ) : ℝ :=
  thetaCuspFullSource (x + hedenmalmBorelChart t) / (2 * (1 + t))

@[simp] theorem hedenmalmBorelCharacter_zero_arg (alpha : ℂ) :
    hedenmalmBorelCharacter alpha 0 = 1 := by
  simp [hedenmalmBorelCharacter]

@[simp] theorem hedenmalmBorelCharacter_zero (t : ℝ) :
    hedenmalmBorelCharacter 0 t = 1 := by
  simp [hedenmalmBorelCharacter]

theorem hedenmalmBorelCharacter_ne_zero (alpha : ℂ) (t : ℝ) :
    hedenmalmBorelCharacter alpha t ≠ 0 :=
  Complex.exp_ne_zero _

theorem continuousOn_hedenmalmBorelChart :
    ContinuousOn hedenmalmBorelChart (Ioi (-1 : ℝ)) := by
  unfold hedenmalmBorelChart
  refine ContinuousOn.div_const (ContinuousOn.log (by fun_prop) ?_) 2
  intro t ht
  have := mem_Ioi.mp ht
  linarith

theorem continuousOn_hedenmalmBorelCharacter (alpha : ℂ) :
    ContinuousOn (fun t : ℝ => hedenmalmBorelCharacter alpha t) (Ioi (-1 : ℝ)) := by
  unfold hedenmalmBorelCharacter
  exact Complex.continuous_exp.comp_continuousOn
    ((continuous_const.continuousOn).mul
      (Complex.continuous_ofReal.comp_continuousOn continuousOn_hedenmalmBorelChart))

/-- **Strict positivity of the Borel source density.**  The all-orders-flat theta tail is not zero
in the essential chart. -/
theorem hedenmalmBorelDensity_pos (x : ℝ) {t : ℝ} (ht : -1 < t) :
    0 < hedenmalmBorelDensity x t := by
  refine div_pos (thetaCuspFullSource_pos_all _) ?_
  linarith

theorem hedenmalmBorelDensity_nonneg (x : ℝ) {t : ℝ} (ht : -1 < t) :
    0 ≤ hedenmalmBorelDensity x t :=
  (hedenmalmBorelDensity_pos x ht).le

theorem continuousOn_hedenmalmBorelDensity (x : ℝ) :
    ContinuousOn (hedenmalmBorelDensity x) (Ioi (-1 : ℝ)) := by
  have hk : ContinuousOn (fun t : ℝ => thetaCuspFullSource (x + hedenmalmBorelChart t))
      (Ioi (-1 : ℝ)) :=
    contDiff_thetaCuspFullSource.continuous.comp_continuousOn
      (continuousOn_const.add continuousOn_hedenmalmBorelChart)
  refine ContinuousOn.div hk (by fun_prop) ?_
  intro t ht
  have ht' := mem_Ioi.mp ht
  have : (0 : ℝ) < 2 * (1 + t) := by linarith
  exact ne_of_gt this

/-- **Mass law of the Borel density.**  Its total mass is exactly the theta tail mass. -/
theorem integral_Ioi_hedenmalmBorelDensity (x : ℝ) :
    ∫ t in Ioi (0 : ℝ), hedenmalmBorelDensity x t =
      ∫ y in Ioi x, thetaCuspFullSource y := by
  rw [integral_Ioi_eq_integral_hedenmalmBorelChart x thetaCuspFullSource]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t _
  simp only [hedenmalmBorelDensity, smul_eq_mul]
  ring

/-! ## The exact Borel-tail factorization -/

/-- The completed theta Fourier--Laplace integral of the eigenfunction parameter. -/
theorem integral_thetaCuspFourierLaplaceIntegrand_neg
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
    (∫ y : ℝ, thetaCuspFourierLaplaceIntegrand (-alpha) y) = XiC alpha := by
  have hstripNeg : |(-alpha).im| < 1 := by simpa using hstrip
  have hmem : -alpha ∈ thetaCuspFourierLaplaceStrip := by
    rw [thetaCuspFourierLaplaceStrip]
    exact abs_lt.mp hstripNeg
  rw [← thetaCuspFourierLaplace, thetaCuspFourierLaplace_eq_XiC_on_strip hmem, XiC_even]

/-- The Hedenmalm right tail in the Borel chart, before zero specialization. -/
theorem integral_Ioi_thetaCuspFourierLaplaceIntegrand_eq_borel
    (alpha : ℂ) (x : ℝ) :
    (∫ y in Ioi x, thetaCuspFourierLaplaceIntegrand (-alpha) y) =
      Complex.exp (Complex.I * alpha * (x : ℂ)) *
        ∫ t in Ioi (0 : ℝ),
          hedenmalmBorelCharacter alpha t * (hedenmalmBorelDensity x t : ℂ) := by
  rw [integral_Ioi_eq_integral_hedenmalmBorelChart x
    (thetaCuspFourierLaplaceIntegrand (-alpha)), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t _
  have hexp :
      Complex.exp (-Complex.I * (-alpha) * ((x + hedenmalmBorelChart t : ℝ) : ℂ)) =
        Complex.exp (Complex.I * alpha * (x : ℂ)) *
          hedenmalmBorelCharacter alpha t := by
    rw [hedenmalmBorelCharacter, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hint : thetaCuspFourierLaplaceIntegrand (-alpha) (x + hedenmalmBorelChart t) =
      Complex.exp (Complex.I * alpha * (x : ℂ)) * hedenmalmBorelCharacter alpha t *
        ((thetaCuspFullSource (x + hedenmalmBorelChart t) : ℝ) : ℂ) := by
    unfold thetaCuspFourierLaplaceIntegrand
    rw [hexp]
  dsimp only
  rw [hint, hedenmalmBorelDensity,
    div_eq_mul_one_div (thetaCuspFullSource (x + hedenmalmBorelChart t)) (2 * (1 + t)),
    Complex.ofReal_mul, Complex.real_smul]
  ring

/-- **Theorem 1 (exact Borel-tail factorization).**  At every zero of the centered completed Xi
function, the Hedenmalm two-ended eigenfunction is the negative of one universal complex dilation
character integrated against a strictly positive source density on the fixed Borel ray. -/
theorem xiHedenmalmBoundaryEigenfunction_eq_borelTail
    {alpha : ℂ} (hstrip : |alpha.im| < 1) (hzero : XiC alpha = 0) (x : ℝ) :
    xiHedenmalmBoundaryEigenfunction alpha x =
      -∫ t in Ioi (0 : ℝ),
          hedenmalmBorelCharacter alpha t * (hedenmalmBorelDensity x t : ℂ) := by
  have hstripNeg : |(-alpha).im| < 1 := by simpa using hstrip
  have hint : Integrable (thetaCuspFourierLaplaceIntegrand (-alpha)) :=
    integrable_thetaCuspFourierLaplaceIntegrand hstripNeg
  have hsplit := integral_add_compl (f := thetaCuspFourierLaplaceIntegrand (-alpha))
    (s := Iic x) measurableSet_Iic hint
  rw [compl_Iic, integral_thetaCuspFourierLaplaceIntegrand_neg hstrip, hzero] at hsplit
  have hIic :
      (∫ y in Iic x, thetaCuspFourierLaplaceIntegrand (-alpha) y) =
        -∫ y in Ioi x, thetaCuspFourierLaplaceIntegrand (-alpha) y := by
    linear_combination hsplit
  rw [xiHedenmalmBoundaryEigenfunction, thetaCuspBoundaryPrimitive, hIic,
    integral_Ioi_thetaCuspFourierLaplaceIntegrand_eq_borel alpha x]
  have hcancel :
      Complex.exp (Complex.I * (-alpha) * (x : ℂ)) *
          Complex.exp (Complex.I * alpha * (x : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  calc
    Complex.exp (Complex.I * (-alpha) * (x : ℂ)) *
        -(Complex.exp (Complex.I * alpha * (x : ℂ)) *
          ∫ t in Ioi (0 : ℝ),
            hedenmalmBorelCharacter alpha t * (hedenmalmBorelDensity x t : ℂ))
        = -((Complex.exp (Complex.I * (-alpha) * (x : ℂ)) *
              Complex.exp (Complex.I * alpha * (x : ℂ))) *
            ∫ t in Ioi (0 : ℝ),
              hedenmalmBorelCharacter alpha t * (hedenmalmBorelDensity x t : ℂ)) := by
        ring
    _ = -∫ t in Ioi (0 : ℝ),
            hedenmalmBorelCharacter alpha t * (hedenmalmBorelDensity x t : ℂ) := by
        rw [hcancel, one_mul]

/-! ## Reflection, adjunction, and radial drift -/

/-- Spectral reflection inverts the Borel character. -/
theorem hedenmalmBorelCharacter_neg (alpha : ℂ) (t : ℝ) :
    hedenmalmBorelCharacter (-alpha) t = (hedenmalmBorelCharacter alpha t)⁻¹ := by
  rw [hedenmalmBorelCharacter, hedenmalmBorelCharacter, ← Complex.exp_neg]
  congr 1
  ring

theorem hedenmalmBorelCharacter_mul (alpha beta : ℂ) (t : ℝ) :
    hedenmalmBorelCharacter (alpha + beta) t =
      hedenmalmBorelCharacter alpha t * hedenmalmBorelCharacter beta t := by
  rw [hedenmalmBorelCharacter, hedenmalmBorelCharacter, hedenmalmBorelCharacter,
    ← Complex.exp_add]
  congr 1
  ring

/-- Hilbert adjunction conjugates the Borel character to the reflected conjugate parameter. -/
theorem conj_hedenmalmBorelCharacter (alpha : ℂ) (t : ℝ) :
    (starRingEnd ℂ) (hedenmalmBorelCharacter alpha t) =
      hedenmalmBorelCharacter (-(starRingEnd ℂ) alpha) t := by
  rw [hedenmalmBorelCharacter, hedenmalmBorelCharacter, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **Radial drift.**  The modulus of the Borel character is the exact real radial power fixed by
the horizontal displacement of the spectral parameter. -/
theorem norm_hedenmalmBorelCharacter (alpha : ℂ) (t : ℝ) :
    ‖hedenmalmBorelCharacter alpha t‖ =
      Real.exp (-alpha.im * hedenmalmBorelChart t) := by
  rw [hedenmalmBorelCharacter, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem norm_hedenmalmBorelCharacter_rpow (alpha : ℂ) {t : ℝ} (ht : -1 < t) :
    ‖hedenmalmBorelCharacter alpha t‖ = (1 + t) ^ (-alpha.im / 2) := by
  have hpos : (0 : ℝ) < 1 + t := by linarith
  rw [norm_hedenmalmBorelCharacter, Real.rpow_def_of_pos hpos, hedenmalmBorelChart]
  congr 1
  ring

/-- The Borel character in its literal complex-power form. -/
theorem hedenmalmBorelCharacter_eq_cpow (alpha : ℂ) {t : ℝ} (ht : -1 < t) :
    hedenmalmBorelCharacter alpha t =
      ((1 + t : ℝ) : ℂ) ^ (Complex.I * alpha / 2) := by
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have hne : ((1 + t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  rw [Complex.cpow_def_of_ne_zero hne, hedenmalmBorelCharacter, hedenmalmBorelChart]
  congr 1
  rw [← Complex.ofReal_log hpos.le]
  push_cast
  ring

/-- **Theorem 3 (contraction law).**  On the full-support Borel ray the character is a pointwise
contraction exactly when the spectral parameter lies in the closed upper half plane. -/
theorem hedenmalmBorelCharacter_norm_le_one_iff (alpha : ℂ) :
    (∀ t ∈ Ioi (0 : ℝ), ‖hedenmalmBorelCharacter alpha t‖ ≤ 1) ↔ 0 ≤ alpha.im := by
  have hq : 0 < hedenmalmBorelChart 1 := hedenmalmBorelChart_pos one_pos
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    rw [norm_hedenmalmBorelCharacter] at h1
    have hle : -alpha.im * hedenmalmBorelChart 1 ≤ 0 := Real.exp_le_one_iff.mp h1
    nlinarith
  · intro h t ht
    rw [norm_hedenmalmBorelCharacter]
    have hqt : 0 < hedenmalmBorelChart t := hedenmalmBorelChart_pos (mem_Ioi.mp ht)
    have hnonpos : -alpha.im * hedenmalmBorelChart t ≤ 0 := by nlinarith
    exact Real.exp_le_one_iff.mpr hnonpos

/-- **Theorem 3 (unitarity law).**  The character has modulus one on the whole Borel ray exactly
when the spectral parameter is real. -/
theorem hedenmalmBorelCharacter_norm_eq_one_iff (alpha : ℂ) :
    (∀ t ∈ Ioi (0 : ℝ), ‖hedenmalmBorelCharacter alpha t‖ = 1) ↔ alpha.im = 0 := by
  constructor
  · intro h
    have h1 := h 1 (by norm_num)
    rw [norm_hedenmalmBorelCharacter] at h1
    have hq : 0 < hedenmalmBorelChart 1 := hedenmalmBorelChart_pos one_pos
    have hzero : -alpha.im * hedenmalmBorelChart 1 = 0 :=
      (Real.exp_eq_one_iff _).mp h1
    rcases mul_eq_zero.mp hzero with h' | h'
    · linarith
    · exact absurd h' (ne_of_gt hq)
  · intro h t _
    rw [norm_hedenmalmBorelCharacter, h]
    simp

/-- **Theorem 3 (trichotomy, boundedness of both reflected multipliers).**  Both the character and
its spectral reflection are pointwise bounded on the Borel ray exactly when the parameter is
real. -/
theorem hedenmalmBorelCharacter_bounded_reflected_iff (alpha : ℂ) :
    (∃ C : ℝ, ∀ t ∈ Ioi (0 : ℝ),
        ‖hedenmalmBorelCharacter alpha t‖ ≤ C ∧
          ‖hedenmalmBorelCharacter (-alpha) t‖ ≤ C) ↔ alpha.im = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    set c : ℝ := |alpha.im| with hc
    have hcpos : 0 < c := abs_pos.mpr hne
    have hgrow : ∀ t ∈ Ioi (0 : ℝ), Real.exp (c * hedenmalmBorelChart t) ≤ C := by
      intro t ht
      rcases le_or_gt 0 alpha.im with h | h
      · have hcc : c = alpha.im := by rw [hc, abs_of_nonneg h]
        have hbound := (hC t ht).2
        rw [norm_hedenmalmBorelCharacter, Complex.neg_im, neg_neg] at hbound
        rw [hcc]
        exact hbound
      · have hcc : c = -alpha.im := by rw [hc, abs_of_neg h]
        have hbound := (hC t ht).1
        rw [norm_hedenmalmBorelCharacter] at hbound
        rw [hcc]
        exact hbound
    obtain ⟨n, hn⟩ := exists_nat_gt (max C 1)
    have hn1 : (1 : ℝ) < n := lt_of_le_of_lt (le_max_right C 1) hn
    have hnC : C < (n : ℝ) := lt_of_le_of_lt (le_max_left C 1) hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hlogpos : 0 < Real.log n := Real.log_pos hn1
    set y : ℝ := Real.log n / c with hy
    have hypos : 0 < y := div_pos hlogpos hcpos
    have hylt : 0 < Real.exp (2 * y) - 1 := by
      have : (1 : ℝ) < Real.exp (2 * y) := Real.one_lt_exp_iff.mpr (by linarith)
      linarith
    have hmem : Real.exp (2 * y) - 1 ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hylt
    have hchart : hedenmalmBorelChart (Real.exp (2 * y) - 1) = y :=
      hedenmalmBorelChart_exp y
    have hle := hgrow _ hmem
    rw [hchart] at hle
    have hcy : c * y = Real.log n := by
      rw [hy]
      field_simp
    rw [hcy, Real.exp_log hnpos] at hle
    linarith
  · intro h
    refine ⟨1, fun t ht => ⟨?_, ?_⟩⟩
    · rw [norm_hedenmalmBorelCharacter, h]
      simp
    · rw [norm_hedenmalmBorelCharacter]
      simp [h]

/-- **Theorem 3 (13).**  Functional reflection agrees with Hilbert adjunction on the Borel boundary
exactly when the associated centered zero lies on the critical line. -/
theorem re_centeredSpectralPoint (alpha : ℂ) :
    (1 / 2 + alpha * Complex.I).re = 1 / 2 - alpha.im := by
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.div_re, Complex.one_re, Complex.one_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_ofNat]
  ring

theorem hedenmalmBorelCharacter_bounded_reflected_iff_re_eq_half (alpha : ℂ) :
    (∃ C : ℝ, ∀ t ∈ Ioi (0 : ℝ),
        ‖hedenmalmBorelCharacter alpha t‖ ≤ C ∧
          ‖hedenmalmBorelCharacter (-alpha) t‖ ≤ C) ↔
      (1 / 2 + alpha * Complex.I).re = 1 / 2 := by
  rw [hedenmalmBorelCharacter_bounded_reflected_iff, re_centeredSpectralPoint]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    linarith

/-! ## The Borel holonomy is the normalized dilation character -/

/-- The normalized dilation character of a centered spectral point. -/
def soninDilationCharacter (r : ℝ) (rho : ℂ) : ℂ := (r : ℂ) ^ (rho - 1 / 2)

/-- **Theorem 4 (16b).**  The Borel multiplier is not a second spectral character: it is the
normalized dilation character evaluated at the radial sample `sqrt (1 + t)`. -/
theorem soninDilationCharacter_sqrt_eq_hedenmalmBorelCharacter
    (alpha : ℂ) {t : ℝ} (ht : -1 < t) :
    soninDilationCharacter (Real.sqrt (1 + t)) (1 / 2 + alpha * Complex.I) =
      hedenmalmBorelCharacter alpha t := by
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have hsqrt : (0 : ℝ) < Real.sqrt (1 + t) := Real.sqrt_pos.mpr hpos
  have hne : ((Real.sqrt (1 + t) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hsqrt)
  rw [soninDilationCharacter, Complex.cpow_def_of_ne_zero hne, hedenmalmBorelCharacter]
  congr 1
  have hlogsqrt : Real.log (Real.sqrt (1 + t)) = Real.log (1 + t) / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hpos]
    ring
  rw [← Complex.ofReal_log hsqrt.le, hlogsqrt, hedenmalmBorelChart]
  push_cast
  ring

/-- **Theorem 4 (16c).**  At the geometric samples `1 + t = r ^ (2 j)` the Borel multiplier is the
`j`-th power of the fixed dilation character. -/
theorem hedenmalmBorelCharacter_geometric_sample
    (alpha : ℂ) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    hedenmalmBorelCharacter alpha (r ^ (2 * j) - 1) =
      soninDilationCharacter r (1 / 2 + alpha * Complex.I) ^ j := by
  have hrpow : (0 : ℝ) < r ^ (2 * j) := pow_pos hr _
  have hne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hchart : hedenmalmBorelChart (r ^ (2 * j) - 1) = j * Real.log r := by
    rw [hedenmalmBorelChart]
    have h1 : (1 : ℝ) + (r ^ (2 * j) - 1) = r ^ (2 * j) := by ring
    rw [h1, Real.log_pow]
    push_cast
    ring
  rw [hedenmalmBorelCharacter, hchart, soninDilationCharacter,
    Complex.cpow_def_of_ne_zero hne, ← Complex.exp_nat_mul]
  congr 1
  rw [← Complex.ofReal_log hr.le]
  push_cast
  ring

/-- **Theorem 4 (16g).**  The squared modulus at the geometric samples is the `j`-th power of the
relative determinant torsion of the dilation character. -/
theorem norm_sq_hedenmalmBorelCharacter_geometric_sample
    (alpha : ℂ) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ‖hedenmalmBorelCharacter alpha (r ^ (2 * j) - 1)‖ ^ 2 =
      (‖soninDilationCharacter r (1 / 2 + alpha * Complex.I)‖ ^ 2) ^ j := by
  rw [hedenmalmBorelCharacter_geometric_sample alpha hr j, norm_pow]
  ring

/-- The radial exponent at the geometric samples is exactly the horizontal displacement of the
centered zero. -/
theorem norm_hedenmalmBorelCharacter_geometric_sample_rpow
    (alpha : ℂ) {r : ℝ} (hr : 0 < r) (j : ℕ) :
    ‖hedenmalmBorelCharacter alpha (r ^ (2 * j) - 1)‖ =
      r ^ (-(j : ℝ) * alpha.im) := by
  have hrpow : (0 : ℝ) < r ^ (2 * j) := pow_pos hr _
  have hchart : hedenmalmBorelChart (r ^ (2 * j) - 1) = j * Real.log r := by
    rw [hedenmalmBorelChart]
    have h1 : (1 : ℝ) + (r ^ (2 * j) - 1) = r ^ (2 * j) := by ring
    rw [h1, Real.log_pow]
    push_cast
    ring
  rw [norm_hedenmalmBorelCharacter, hchart, Real.rpow_def_of_pos hr]
  congr 1
  ring


/-- Integrability transfers along the Borel chart. -/
theorem integrableOn_Ioi_iff_hedenmalmBorelChart
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (x : ℝ) (g : ℝ → F) :
    IntegrableOn g (Ioi x) ↔
      IntegrableOn
        (fun t : ℝ => (1 / (2 * (1 + t))) • g (x + hedenmalmBorelChart t)) (Ioi 0) := by
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ => x + hedenmalmBorelChart s)
        (1 / (1 + t) / 2) (Ioi 0) t := by
    intro t ht
    exact (hasDerivAt_hedenmalmBorelChart x
      (by have := mem_Ioi.mp ht; linarith)).hasDerivWithinAt
  have h := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hderiv (injOn_hedenmalmBorelChart x) g
  rw [image_hedenmalmBorelChart] at h
  rw [h]
  constructor
  · intro hI
    refine hI.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [abs_hedenmalmBorelChartJacobian t (mem_Ioi.mp ht)]
  · intro hI
    refine hI.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [abs_hedenmalmBorelChartJacobian t (mem_Ioi.mp ht)]

/-- The exponentially tilted theta source is integrable throughout the completed strip. -/
theorem integrable_exp_mul_thetaCuspFullSource {c : ℝ} (hc : |c| < 1) :
    Integrable (fun y : ℝ => Real.exp (c * y) * thetaCuspFullSource y) := by
  have hw : |((c : ℂ) * Complex.I).im| < 1 := by simpa using hc
  have hint := integrable_thetaCuspFourierLaplaceIntegrand hw
  refine hint.norm.congr ?_
  filter_upwards with y
  have hrw : -Complex.I * ((c : ℂ) * Complex.I) * (y : ℂ) = ((c * y : ℝ) : ℂ) := by
    push_cast
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-(c : ℂ) * (y : ℂ)) * hI
  unfold thetaCuspFourierLaplaceIntegrand
  rw [norm_mul, hrw, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaCuspFullSource_pos_all y), Complex.ofReal_re]

/-- **The Borel holonomy is square integrable against the source density.**  For every centered
parameter in the open half strip the radially tilted theta tail has finite mass. -/
theorem integrableOn_norm_sq_hedenmalmBorelCharacter_mul_density
    {alpha : ℂ} (halpha : |alpha.im| < 1 / 2) (x : ℝ) :
    IntegrableOn
      (fun t : ℝ =>
        ‖hedenmalmBorelCharacter alpha t‖ ^ 2 * hedenmalmBorelDensity x t) (Ioi 0) := by
  set c : ℝ := -2 * alpha.im with hc
  have hcabs : |c| < 1 := by
    rw [hc, abs_mul]
    have : |(-2 : ℝ)| = 2 := by norm_num
    rw [this]
    linarith [halpha]
  have hbase : Integrable (fun y : ℝ => Real.exp (c * y) * thetaCuspFullSource y) :=
    integrable_exp_mul_thetaCuspFullSource hcabs
  have hshift : Integrable (fun y : ℝ => Real.exp (c * (y - x)) * thetaCuspFullSource y) := by
    refine (hbase.const_mul (Real.exp (-(c * x)))).congr ?_
    filter_upwards with y
    rw [← mul_assoc, ← Real.exp_add]
    have hsum : -(c * x) + c * y = c * (y - x) := by ring
    rw [hsum]
  have hiff := (integrableOn_Ioi_iff_hedenmalmBorelChart x
    (fun y : ℝ => Real.exp (c * (y - x)) * thetaCuspFullSource y)).mp hshift.integrableOn
  refine hiff.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht' : (0 : ℝ) < 1 + t := by have := mem_Ioi.mp ht; linarith
  have hnorm : ‖hedenmalmBorelCharacter alpha t‖ ^ 2 =
      Real.exp (c * hedenmalmBorelChart t) := by
    rw [norm_hedenmalmBorelCharacter, ← Real.exp_nat_mul]
    congr 1
    rw [hc]
    push_cast
    ring
  have harg : x + hedenmalmBorelChart t - x = hedenmalmBorelChart t := by ring
  dsimp only
  rw [smul_eq_mul, hnorm, hedenmalmBorelDensity, harg]
  ring

end RHTower
