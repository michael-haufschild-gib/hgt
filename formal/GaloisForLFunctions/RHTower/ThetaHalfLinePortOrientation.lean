import GaloisForLFunctions.RHTower.CausalThetaHalfLaplace
import GaloisForLFunctions.RHTower.ThetaZeroDivisionSource
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment

/-!
# The literal theta half-line port on the closed right half-plane

For `K(w) = ∫₀^∞ e^{wu} k(u) du` and `ν = -k' > 0` on `(0, ∞)`, integration by parts gives
`w K(-w) = ∫₀^∞ (1 - e^{-wu}) ν(u) du`, whose real part is positive on the closed right half-plane
minus the origin (on the imaginary axis it is `∫ ν(u)(1 - cos γu) du`), while `K(0) = ∫₀^∞ k > 0`.
Hence `K(-w)` has no zero with `Re w ≥ 0`, and at every zero of `K(w) + K(-w)` both halves are
nonzero.  On the imaginary axis `K(iγ) = ∫ k cos(γu) + i b(γ)` with `Ξ(γ) = 2∫ k cos(γu)` and the
half-ray sine response `b(γ) = ∫₀^∞ k(u) sin(γu) du = γ⁻¹ ∫ ν(u)(1 - cos γu) du > 0`.

Reality `K(w̄) = conj K(w)` gives `Ξ'(γ) = -2 Im K'(iγ)`, and at a critical zero the one-port
imbalance `D(α, γ) = |K(α+iγ)|² - |K(-α-iγ)|²` has normal derivative
`∂_α D(0, γ) = 4 b(γ) Im K'(iγ) = -2 b(γ) Ξ'(γ)`.  Differentiation under the integral gives the
first source moment law `Ξ'(γ) = -2 ∫₀^∞ u k(u) sin(γu) du`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## Reality and the central value of the half-line transform -/

/-- `K(w̄) = conj K(w)`. -/
theorem thetaHalfLaplace_conj (w : ℂ) :
    thetaHalfLaplace ((starRingEnd ℂ) w) = (starRingEnd ℂ) (thetaHalfLaplace w) := by
  rw [thetaHalfLaplace, thetaHalfLaplaceTail, thetaHalfLaplace, thetaHalfLaplaceTail,
    ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

theorem integrableOn_Ioi_thetaCuspFullSource : IntegrableOn thetaCuspFullSource (Ioi 0) :=
  (thetaCuspSchwartzReal.integrable (μ := (volume : Measure ℝ))).integrableOn

/-- `K(0) = ∫₀^∞ k > 0`. -/
theorem thetaHalfLaplace_zero :
    thetaHalfLaplace 0 = ((∫ u in Ioi (0 : ℝ), thetaCuspFullSource u : ℝ) : ℂ) := by
  rw [thetaHalfLaplace, thetaHalfLaplaceTail, ← integral_complex_ofReal]
  simp

/-! ## Strict positivity on the closed right half-plane -/

/-- On the imaginary axis `Re(iγ K(-iγ)) = ∫₀^∞ ν(u)(1 - cos γu) du > 0` for `γ ≠ 0`. -/
theorem re_mul_thetaHalfLaplace_neg_pos_of_re_eq_zero {w : ℂ} (hw : w.re = 0) (hw0 : w ≠ 0) :
    0 < (w * thetaHalfLaplace (-w)).re := by
  rw [mul_thetaHalfLaplace_neg_of_nonneg hw.ge hw0]
  set γ := w.im with hγ
  have hγ0 : γ ≠ 0 := by
    intro h; apply hw0; exact Complex.ext hw (by rw [← hγ, h]; rfl)
  have hwγ : w = γ * I := Complex.ext (by simp [hw]) (by simp [hγ])
  set ν : ℝ → ℝ := fun u => -deriv thetaCuspFullSource u with hν
  have hνint : IntegrableOn ν (Ioi 0) := integrableOn_Ioi_deriv_thetaCuspFullSource.neg
  have hcd := continuous_deriv_thetaCuspFullSource
  have hint : IntegrableOn (fun u : ℝ => (((-deriv thetaCuspFullSource u : ℝ)) : ℂ) *
      (1 - Complex.exp (-(w * u)))) (Ioi 0) := by
    refine Integrable.mono' (hνint.norm.mul_const 2) (by fun_prop : Continuous fun u : ℝ =>
      (((-deriv thetaCuspFullSource u : ℝ)) : ℂ) * (1 - Complex.exp (-(w * u)))).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
    rw [norm_mul, Complex.norm_real]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
    rw [norm_one, Complex.norm_exp]
    simp [hw]
    norm_num
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  have hpt : ∀ u : ℝ, ((((-deriv thetaCuspFullSource u : ℝ)) : ℂ) *
      (1 - Complex.exp (-(w * u)))).re = ν u * (1 - Real.cos (γ * u)) := by
    intro u
    rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, hwγ,
      show -((γ : ℂ) * I * u) = ((-(γ * u) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  simp_rw [hpt]
  have hν0 : ∀ u, 0 < u → 0 < ν u := fun u hu => by
    simp only [hν]; linarith [deriv_thetaCuspFullSource_neg_of_pos hu]
  have hgcont : Continuous fun u => ν u * (1 - Real.cos (γ * u)) := by
    simp only [hν]; fun_prop
  have hgint : IntegrableOn (fun u => ν u * (1 - Real.cos (γ * u))) (Ioi 0) := by
    refine Integrable.mono' (hνint.norm.mul_const 2) hgcont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x _ => ?_))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]; constructor <;> linarith [Real.neg_one_le_cos (γ * x), Real.cos_le_one (γ * x)]
  have hg0 : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ ν u * (1 - Real.cos (γ * u)) := fun u hu =>
    mul_nonneg (hν0 u hu).le (by linarith [Real.cos_le_one (γ * u)])
  -- positivity on a period interval
  set P := Real.pi / |γ|
  have hP : 0 < P := div_pos Real.pi_pos (abs_pos.mpr hγ0)
  have hpos : 0 < ∫ u in (P / 2)..(3 * P / 2), ν u * (1 - Real.cos (γ * u)) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hgcont.intervalIntegrable _ _)
      (fun u hu => mul_pos (hν0 u (by linarith [hu.1])) ?_) (by linarith)
    have hu1 : P / 2 < u := hu.1
    have hu2 : u < 3 * P / 2 := hu.2
    have hcos : Real.cos (γ * u) = Real.cos (|γ| * u) := by
      rcases abs_cases γ with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, neg_mul, Real.cos_neg]
    rw [hcos, sub_pos]
    have hx1 : Real.pi / 2 < |γ| * u := by
      have := mul_lt_mul_of_pos_left hu1 (abs_pos.mpr hγ0)
      rwa [show |γ| * (P / 2) = Real.pi / 2 by simp only [P]; field_simp] at this
    have hx2 : |γ| * u < 3 * Real.pi / 2 := by
      have := mul_lt_mul_of_pos_left hu2 (abs_pos.mpr hγ0)
      rwa [show |γ| * (3 * P / 2) = 3 * Real.pi / 2 by simp only [P]; field_simp] at this
    rcases le_or_gt (|γ| * u) Real.pi with h | h
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) h hx1
      rw [Real.cos_pi_div_two] at this
      linarith
    · have h' := Real.cos_pi_sub (|γ| * u - Real.pi)
      have h3 : Real.cos (|γ| * u) = -Real.cos (|γ| * u - Real.pi) := by
        rw [Real.cos_sub_pi]; ring
      rw [h3]
      have := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩ (x := |γ| * u - Real.pi)
      linarith
  refine lt_of_lt_of_le hpos ?_
  rw [intervalIntegral.integral_of_le (by linarith)]
  exact setIntegral_mono_set hgint ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ hg0)) (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by positivity))).eventuallyLE

/-- **Closed half-plane positivity (1).** `Re(w K(-w)) > 0` for `Re w ≥ 0`, `w ≠ 0`. -/
theorem re_mul_thetaHalfLaplace_neg_pos_of_nonneg {w : ℂ} (hw : 0 ≤ w.re) (hw0 : w ≠ 0) :
    0 < (w * thetaHalfLaplace (-w)).re := by
  rcases hw.eq_or_lt with h | h
  · exact re_mul_thetaHalfLaplace_neg_pos_of_re_eq_zero h.symm hw0
  · exact re_mul_thetaHalfLaplace_neg_pos h

/-- `K(-w)` is zero-free on the closed right half-plane. -/
theorem thetaHalfLaplace_neg_ne_zero_of_nonneg {w : ℂ} (hw : 0 ≤ w.re) :
    thetaHalfLaplace (-w) ≠ 0 := by
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [neg_zero, thetaHalfLaplace_zero]
    exact_mod_cast integral_Ioi_thetaCuspFullSource_pos.ne'
  · intro h
    have := re_mul_thetaHalfLaplace_neg_pos_of_nonneg hw hw0
    rw [h, mul_zero, Complex.zero_re] at this
    exact lt_irrefl _ this

/-- **Half-transform nonvanishing at Xi zeros.** If `K(w) + K(-w) = 0` then `K(w) ≠ 0` and
`K(-w) ≠ 0`. -/
theorem thetaHalfLaplace_ne_zero_of_add_neg_eq_zero {w : ℂ}
    (h : thetaHalfLaplace w + thetaHalfLaplace (-w) = 0) :
    thetaHalfLaplace w ≠ 0 ∧ thetaHalfLaplace (-w) ≠ 0 := by
  rcases le_total 0 w.re with hw | hw
  · have h1 := thetaHalfLaplace_neg_ne_zero_of_nonneg hw
    refine ⟨fun h0 => h1 ?_, h1⟩
    rw [h0, zero_add] at h; exact h
  · have h1 := thetaHalfLaplace_neg_ne_zero_of_nonneg (w := -w) (by simp; linarith)
    rw [neg_neg] at h1
    refine ⟨h1, fun h0 => h1 ?_⟩
    rw [h0, add_zero] at h; exact h

/-! ## The half-ray sine response -/

/-- The half-ray sine response `b(γ) = ∫₀^∞ k(u) sin(γu) du`. -/
def thetaHalfSineResponse (γ : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), thetaCuspFullSource u * Real.sin (γ * u)

/-- The half-ray cosine response `∫₀^∞ k(u) cos(γu) du`. -/
def thetaHalfCosineResponse (γ : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), thetaCuspFullSource u * Real.cos (γ * u)

theorem thetaHalfLaplace_I_mul (γ : ℝ) :
    thetaHalfLaplace (γ * I) =
      (thetaHalfCosineResponse γ : ℂ) + (thetaHalfSineResponse γ : ℂ) * I := by
  have hk := integrableOn_Ioi_thetaCuspFullSource
  have hc : IntegrableOn (fun u => thetaCuspFullSource u * Real.cos (γ * u)) (Ioi 0) :=
    hk.mono' (continuous_thetaCuspFullSource.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (thetaCuspFullSource_pos_all u)]
        exact mul_le_of_le_one_right (thetaCuspFullSource_pos_all u).le (Real.abs_cos_le_one _))
  have hs : IntegrableOn (fun u => thetaCuspFullSource u * Real.sin (γ * u)) (Ioi 0) :=
    hk.mono' (continuous_thetaCuspFullSource.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (thetaCuspFullSource_pos_all u)]
        exact mul_le_of_le_one_right (thetaCuspFullSource_pos_all u).le (Real.abs_sin_le_one _))
  have hA : Integrable (fun u : ℝ => ((thetaCuspFullSource u * Real.cos (γ * u) : ℝ) : ℂ))
      (volume.restrict (Ioi 0)) := hc.ofReal
  have hB : Integrable (fun u : ℝ => ((thetaCuspFullSource u * Real.sin (γ * u) : ℝ) : ℂ) * I)
      (volume.restrict (Ioi 0)) := (hs.ofReal (𝕜 := ℂ)).mul_const I
  rw [thetaHalfCosineResponse, thetaHalfSineResponse, ← integral_complex_ofReal,
    ← integral_complex_ofReal, ← integral_mul_const, ← integral_add hA hB,
    thetaHalfLaplace, thetaHalfLaplaceTail]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [show (γ : ℂ) * I * u = ((γ * u : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- `Ξ(γ) = 2 ∫₀^∞ k(u) cos(γu) du`. -/
theorem Xi_eq_two_mul_thetaHalfCosineResponse (γ : ℝ) :
    Xi γ = 2 * thetaHalfCosineResponse γ := by
  have h := thetaHalfLaplace_add_neg (γ * I)
  rw [show I * (γ * I) = -(γ : ℂ) by rw [mul_comm, mul_assoc, Complex.I_mul_I]; ring, XiC_even,
    XiC_ofReal, show -((γ : ℂ) * I) = (starRingEnd ℂ) ((γ : ℂ) * I) by simp,
    thetaHalfLaplace_conj, thetaHalfLaplace_I_mul] at h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- `γ b(γ) = ∫₀^∞ ν(u)(1 - cos γu) du > 0`, so `b(γ) > 0` for `γ > 0`. -/
theorem thetaHalfSineResponse_pos {γ : ℝ} (hγ : 0 < γ) : 0 < thetaHalfSineResponse γ := by
  have h := re_mul_thetaHalfLaplace_neg_pos_of_re_eq_zero (w := (γ : ℂ) * I) (by simp)
    (mul_ne_zero (by exact_mod_cast hγ.ne') Complex.I_ne_zero)
  rw [show -((γ : ℂ) * I) = (starRingEnd ℂ) ((γ : ℂ) * I) by simp, thetaHalfLaplace_conj,
    thetaHalfLaplace_I_mul] at h
  simp at h
  nlinarith

/-- At a critical Xi zero, `K(iγ) = i b(γ)`. -/
theorem thetaHalfLaplace_I_mul_of_Xi_eq_zero {γ : ℝ} (h : Xi γ = 0) :
    thetaHalfLaplace (γ * I) = (thetaHalfSineResponse γ : ℂ) * I := by
  rw [thetaHalfLaplace_I_mul]
  have := Xi_eq_two_mul_thetaHalfCosineResponse γ
  rw [h] at this
  have h0 : thetaHalfCosineResponse γ = 0 := by linarith
  rw [h0]; simp

/-! ## The normal derivative of the port imbalance -/

theorem hasDerivAt_thetaHalfLaplace (w : ℂ) :
    HasDerivAt thetaHalfLaplace (deriv thetaHalfLaplace w) w :=
  (differentiable_thetaHalfLaplace w).hasDerivAt

/-- `K'(w̄) = conj K'(w)`. -/
theorem deriv_thetaHalfLaplace_conj (w : ℂ) :
    deriv thetaHalfLaplace ((starRingEnd ℂ) w) = (starRingEnd ℂ) (deriv thetaHalfLaplace w) := by
  have h := (hasDerivAt_thetaHalfLaplace w).conj_conj
  have e : (⇑(starRingEnd ℂ) ∘ thetaHalfLaplace ∘ ⇑(starRingEnd ℂ)) = thetaHalfLaplace := by
    funext z
    simp only [Function.comp, ← thetaHalfLaplace_conj, Complex.conj_conj]
  rw [e] at h
  exact h.deriv

/-- `Ξ(t) = K(it) + K(-it)` on the real axis. -/
theorem ofReal_Xi_eq_thetaHalfLaplace (t : ℝ) :
    (Xi t : ℂ) = thetaHalfLaplace (t * I) + thetaHalfLaplace (-(t * I)) := by
  rw [thetaHalfLaplace_add_neg, show I * (t * I) = -(t : ℂ) by
    rw [mul_comm, mul_assoc, Complex.I_mul_I]; ring, XiC_even, XiC_ofReal]

theorem hasDerivAt_thetaHalfLaplace_mul_I (γ : ℝ) :
    HasDerivAt (fun t : ℝ => thetaHalfLaplace (t * I)) (deriv thetaHalfLaplace (γ * I) * I) γ := by
  have h := ((hasDerivAt_thetaHalfLaplace ((γ : ℂ) * I)).comp (γ : ℂ)
    ((hasDerivAt_id (γ : ℂ)).mul_const I)).comp_ofReal
  simpa using h

theorem hasDerivAt_thetaHalfLaplace_neg_mul_I (γ : ℝ) :
    HasDerivAt (fun t : ℝ => thetaHalfLaplace (-(t * I)))
      (-(deriv thetaHalfLaplace (-(γ * I)) * I)) γ := by
  have h := ((hasDerivAt_thetaHalfLaplace (-((γ : ℂ) * I))).comp (γ : ℂ)
    ((hasDerivAt_id (γ : ℂ)).mul_const I).neg).comp_ofReal
  simpa using h

/-- `Ξ'(γ) = -2 Im K'(iγ)`. -/
theorem hasDerivAt_Xi_thetaHalfLaplace (γ : ℝ) :
    HasDerivAt Xi (-2 * (deriv thetaHalfLaplace (γ * I)).im) γ := by
  have h := (hasDerivAt_thetaHalfLaplace_mul_I γ).add (hasDerivAt_thetaHalfLaplace_neg_mul_I γ)
  have e : (fun t : ℝ => thetaHalfLaplace (t * I)) + (fun t : ℝ => thetaHalfLaplace (-(t * I))) =
      fun t : ℝ => ((Xi t : ℝ) : ℂ) := by
    funext t; simp only [Pi.add_apply]; rw [ofReal_Xi_eq_thetaHalfLaplace]
  rw [e, show -((γ : ℂ) * I) = (starRingEnd ℂ) ((γ : ℂ) * I) by simp,
    deriv_thetaHalfLaplace_conj] at h
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt γ h
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] at hre
  refine hre.congr_deriv ?_
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem deriv_Xi_eq (γ : ℝ) : deriv Xi γ = -2 * (deriv thetaHalfLaplace (γ * I)).im :=
  (hasDerivAt_Xi_thetaHalfLaplace γ).deriv

/-- The one-port imbalance `D(α, γ) = |K(α + iγ)|² - |K(-α - iγ)|²`. -/
def thetaHalfPortImbalance (γ α : ℝ) : ℝ :=
  ‖thetaHalfLaplace (α + γ * I)‖ ^ 2 - ‖thetaHalfLaplace (-(α + γ * I))‖ ^ 2

theorem thetaHalfPortImbalance_zero (γ : ℝ) : thetaHalfPortImbalance γ 0 = 0 := by
  rw [thetaHalfPortImbalance, Complex.ofReal_zero, zero_add,
    show -((γ : ℂ) * I) = (starRingEnd ℂ) ((γ : ℂ) * I) by simp, thetaHalfLaplace_conj,
    Complex.norm_conj, sub_self]

/-- **Normal derivative law (4).** At a critical zero, `∂_α D(0, γ) = -2 b(γ) Ξ'(γ)`. -/
theorem hasDerivAt_thetaHalfPortImbalance {γ : ℝ} (hγ : Xi γ = 0) :
    HasDerivAt (thetaHalfPortImbalance γ) (-2 * thetaHalfSineResponse γ * deriv Xi γ) 0 := by
  have hf1 : HasDerivAt (fun α : ℝ => thetaHalfLaplace (α + γ * I))
      (deriv thetaHalfLaplace (γ * I)) 0 := by
    have h := ((hasDerivAt_thetaHalfLaplace ((((0 : ℝ) : ℂ)) + γ * I)).comp (((0 : ℝ) : ℂ))
      ((hasDerivAt_id (((0 : ℝ) : ℂ))).add_const ((γ : ℂ) * I))).comp_ofReal
    simpa using h
  have hf2 : HasDerivAt (fun α : ℝ => thetaHalfLaplace (-(α + γ * I)))
      (-deriv thetaHalfLaplace (-(γ * I))) 0 := by
    have h := ((hasDerivAt_thetaHalfLaplace (-((((0 : ℝ) : ℂ)) + γ * I))).comp (((0 : ℝ) : ℂ))
      ((hasDerivAt_id (((0 : ℝ) : ℂ))).add_const ((γ : ℂ) * I)).neg).comp_ofReal
    simpa using h
  have h := hf1.norm_sq.sub hf2.norm_sq
  refine h.congr_deriv ?_
  have hK := thetaHalfLaplace_I_mul_of_Xi_eq_zero hγ
  simp only [Complex.ofReal_zero, zero_add]
  rw [show -((γ : ℂ) * I) = (starRingEnd ℂ) ((γ : ℂ) * I) by simp, thetaHalfLaplace_conj,
    deriv_thetaHalfLaplace_conj, hK, deriv_Xi_eq, Complex.inner, Complex.inner]
  simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The first logarithmic source moment `∫₀^∞ u k(u) sin(γu) du`. -/
def thetaHalfSineMoment (γ : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), u * thetaCuspFullSource u * Real.sin (γ * u)

/-- **(7a).** `Ξ'(γ) = -2 ∫₀^∞ u k(u) sin(γu) du`. -/
theorem hasDerivAt_Xi_eq_moment (γ : ℝ) :
    HasDerivAt Xi (-2 * thetaHalfSineMoment γ) γ := by
  have hm : Integrable (fun u : ℝ => ‖u‖ ^ 1 * ‖thetaCuspFullSource u‖) :=
    thetaCuspSchwartzReal.integrable_pow_mul (volume : Measure ℝ) 1
  have hkc := continuous_thetaCuspFullSource
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (g : ℝ) (u : ℝ) => thetaCuspFullSource u * Real.cos (g * u))
    (F' := fun (g : ℝ) (u : ℝ) => -(u * thetaCuspFullSource u * Real.sin (g * u)))
    (x₀ := γ) (bound := fun u => ‖u‖ ^ 1 * ‖thetaCuspFullSource u‖) (s := univ) univ_mem
    (Eventually.of_forall fun g => (hkc.mul (by fun_prop)).aestronglyMeasurable)
    (integrableOn_Ioi_thetaCuspFullSource.mono' (hkc.mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (thetaCuspFullSource_pos_all u)]
        exact mul_le_of_le_one_right (thetaCuspFullSource_pos_all u).le (Real.abs_cos_le_one _)))
    ((by fun_prop : Continuous fun u : ℝ =>
      -(u * thetaCuspFullSource u * Real.sin (γ * u))).aestronglyMeasurable)
    (Eventually.of_forall fun u g _ => by
      rw [norm_neg, norm_mul, norm_mul, pow_one]
      exact mul_le_of_le_one_right (by positivity) (by
        rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _))
    hm.integrableOn
    (Eventually.of_forall fun u g _ => by
      have := ((hasDerivAt_id g).mul_const u).cos.const_mul (thetaCuspFullSource u)
      refine this.congr_deriv ?_
      simp only [id, one_mul]; ring)
  have hX : Xi = fun g => 2 * thetaHalfCosineResponse g := funext Xi_eq_two_mul_thetaHalfCosineResponse
  rw [hX]
  refine (key.2.const_mul 2).congr_deriv ?_
  rw [thetaHalfSineMoment, integral_neg]
  ring

theorem deriv_Xi_eq_moment (γ : ℝ) : deriv Xi γ = -2 * thetaHalfSineMoment γ :=
  (hasDerivAt_Xi_eq_moment γ).deriv

end RHTower
