import GaloisForLFunctions.RHTower.CHMDLightConePrimeKernelDecomposition

/-!
# CHMD: the massless zero-side wave and its explicit formula

Every nontrivial zero `ρ` carries the spectral parameter `γ_ρ` (`|Im γ_ρ| < 1/2`), the Klein–Gordon
frequency `ρ_ρ = √(γ_ρ² + 2)` and the weight `w_ρ = sech²(γ_ρ/2)`.  In complex time `z` set

* `Φ(z) = Σ_ρ m_ρ cos(z ρ_ρ) w_ρ`   (`kgZeroWave`, the causal wave: `Φ(y) = φ_Λ(y)` for real `y`),
* `Φ₀(z) = Σ_ρ m_ρ cos(z γ_ρ) w_ρ`   (`masslessZeroWave`, its massless counterpart).

Since `‖w_ρ‖ ≤ C e^{−|Re γ_ρ|}` (`norm_kgWeight_le`) and the zeros have finite exponential moments
(`summable_mult_mul_exp_neg_abs_re`), both series converge locally uniformly on the time strip
`|Im z| < 1` and define holomorphic functions there (`differentiableOn_masslessZeroWave`,
`differentiableOn_kgZeroWave`).

**Massless explicit formula** (`masslessZeroWave_ofReal`).  For real `v`,

`Φ₀(v) = (2/cos²(1/4)) cosh(v/2) + (1/2π) ∫ cos(vr) sech²(r/2) γ(r) dr − Σ_n (Λ(n)/√n)(D(log n + v) + D(log n − v))`

with `D(v) = 2v/sinh(πv)`.  The test `cos(vz) sech²(z/2)` is not a spectral square, but
`cos(vz) = 2cos²(vz/2) − 1` writes it as `2 Ψ_v Ψ_v^# − sech Sech^#` with `Ψ_v = cos(v·/2) sech(·/2)`,
and the even Weil functional is linear (`evenWeilDensity_sum`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open WeilOneSided WeilSpectral RHTower.EvenSector
open RHTower.CHMDStage3 RHTower.CHMDStage11 RHTower.CHMDStage15 RHTower.CHMDStage22
open RHTower.CHMDGrowthCollapse

/-! ## Exponential summability over the zeros -/

/-- `Σ_ρ m_ρ e^{−ε|Re γ_ρ|} < ∞` for every `ε > 0`. -/
theorem summable_mult_mul_exp_neg_abs_re {ε : ℝ} (hε : 0 < ε) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * Real.exp (-(ε * |(Zeta23.gammaOf (ρ : ℂ)).re|)) := by
  have hsum : Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ))) := by
    have := WeilEF.zero_sum_inv_sq zetaSeam
    simpa [zetaZeroConfig] using this
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    (hsum.mul_left ((5 / 4 : ℝ) * (1 + 2 / ε ^ 2)))
  have hre : (Zeta23.gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := WeilEF.gammaOf_re _
  rw [hre]
  have hexp := CHMDStage15.exp_neg_mul_abs_le_inv_one_add_sq hε (ρ : ℂ).im
  have hnormSq := one_add_normSq_gammaOf_le ρ
  have hpos1 : 0 < 1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)) := by
    have := Complex.normSq_nonneg (Zeta23.gammaOf (ρ : ℂ)); linarith
  have hpos2 : 0 < 1 + (ρ : ℂ).im ^ 2 := by positivity
  have hdiv : (1 + 2 / ε ^ 2) / (1 + (ρ : ℂ).im ^ 2) ≤
      (5 / 4 : ℝ) * (1 + 2 / ε ^ 2) / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ))) := by
    rw [div_le_div_iff₀ hpos2 hpos1]
    have : 0 ≤ 1 + 2 / ε ^ 2 := by positivity
    nlinarith
  calc (zetaZeroConfig.mult ρ : ℝ) * Real.exp (-(ε * |(ρ : ℂ).im|))
      ≤ (zetaZeroConfig.mult ρ : ℝ) *
          ((5 / 4 : ℝ) * (1 + 2 / ε ^ 2) / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)))) :=
        mul_le_mul_of_nonneg_left (hexp.trans hdiv) (Nat.cast_nonneg _)
    _ = (5 / 4 : ℝ) * (1 + 2 / ε ^ 2) *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf (ρ : ℂ)))) := by
        ring

/-! ## Bounds on the spectral data -/

/-- The sech constant `C₀ = (2/cos(5/8))²`. -/
def sechConst : ℝ := (2 / Real.cos (5 / 8)) ^ 2

theorem sechConst_pos : 0 < sechConst := by
  unfold sechConst
  have : 0 < Real.cos (5 / 8) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three],
    by linarith [Real.pi_gt_three]⟩
  positivity

/-- `‖w_ρ‖ ≤ C₀ e^{−|Re γ_ρ|}`. -/
theorem norm_kgWeight_le (ρ : zetaZeroConfig.carrier) :
    ‖kgWeight ρ‖ ≤ sechConst * Real.exp (-|(Zeta23.gammaOf (ρ : ℂ)).re|) := by
  have hIm := abs_im_gammaOf_lt ρ
  set γ := Zeta23.gammaOf (ρ : ℂ)
  have h1 := norm_sechHalf_le (z := γ) (by linarith)
  have h2 := norm_sechHalf_le (z := conj γ) (by rw [Complex.conj_im, abs_neg]; linarith)
  rw [Complex.conj_re] at h2
  unfold CHMDGrowthCollapse.kgWeight specSq
  rw [norm_mul, Complex.norm_conj]
  calc ‖sechHalf γ‖ * ‖sechHalf (conj γ)‖
      ≤ (2 / Real.cos (5 / 8) * Real.exp (-(1 / 2 * |γ.re|))) *
          (2 / Real.cos (5 / 8) * Real.exp (-(1 / 2 * |γ.re|))) :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = (2 / Real.cos (5 / 8)) ^ 2 * (Real.exp (-(1 / 2 * |γ.re|)) *
          Real.exp (-(1 / 2 * |γ.re|))) := by ring
    _ = sechConst * Real.exp (-|γ.re|) := by
        rw [← Real.exp_add]
        unfold sechConst
        congr 2
        ring

theorem norm_cos_mul_le (z ζ : ℂ) :
    ‖Complex.cos (z * ζ)‖ ≤ Real.exp (|z.re| * |ζ.im| + |z.im| * |ζ.re|) := by
  refine (norm_ccos_le_exp_abs_im _).trans (Real.exp_le_exp.mpr ?_)
  rw [Complex.mul_im]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]

theorem abs_re_kgFreq_le (ρ : zetaZeroConfig.carrier) :
    |(kgFreq ρ).re| ≤ |(Zeta23.gammaOf (ρ : ℂ)).re| + 5 / 2 := by
  have hIm := abs_im_gammaOf_lt ρ
  set γ := Zeta23.gammaOf (ρ : ℂ)
  have hsq : ‖kgFreq ρ‖ ^ 2 ≤ (‖γ‖ + 2) ^ 2 := by
    rw [← norm_pow, kgFreq_sq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
    nlinarith [norm_nonneg γ]
  have hn : ‖kgFreq ρ‖ ≤ ‖γ‖ + 2 := by
    nlinarith [norm_nonneg (kgFreq ρ), norm_nonneg γ]
  have hγ : ‖γ‖ ≤ |γ.re| + |γ.im| := Complex.norm_le_abs_re_add_abs_im γ
  linarith [Complex.abs_re_le_norm (kgFreq ρ)]

/-! ## The two zero-side waves in complex time -/

/-- The time strip `|Im z| < 1`. -/
def causalTimeStrip : Set ℂ := {z | |z.im| < 1}

theorem isOpen_causalTimeStrip : IsOpen causalTimeStrip :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

/-- The massless zero-side wave `Φ₀(z) = Σ_ρ m_ρ cos(z γ_ρ) w_ρ`. -/
def masslessZeroWave (z : ℂ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ)

/-- The Klein–Gordon zero-side wave `Φ(z) = Σ_ρ m_ρ cos(z ρ_ρ) w_ρ`. -/
def kgZeroWave (z : ℂ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * kgFreq ρ) * kgWeight ρ)

theorem kgZeroWave_ofReal (y : ℝ) : kgZeroWave y = (chmdWave y : ℂ) :=
  (ofReal_chmdWave y).symm

theorem norm_masslessTerm_le {z : ℂ} {η R : ℝ} (hη : |z.im| ≤ η) (hR : |z.re| ≤ R)
    (ρ : zetaZeroConfig.carrier) :
    ‖(zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ)‖ ≤
      sechConst * Real.exp (R / 2) * ((zetaZeroConfig.mult ρ : ℝ) *
        Real.exp (-((1 - η) * |(Zeta23.gammaOf (ρ : ℂ)).re|))) := by
  have hIm := abs_im_gammaOf_lt ρ
  set γ := Zeta23.gammaOf (ρ : ℂ)
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hc : ‖Complex.cos (z * γ)‖ ≤ Real.exp (R / 2 + η * |γ.re|) := by
    refine (norm_cos_mul_le z γ).trans (Real.exp_le_exp.mpr ?_)
    have h1 : |z.re| * |γ.im| ≤ R / 2 := by
      have := mul_le_mul hR hIm.le (abs_nonneg _) ((abs_nonneg _).trans hR); linarith
    have h2 : |z.im| * |γ.re| ≤ η * |γ.re| := mul_le_mul_of_nonneg_right hη (abs_nonneg _)
    linarith
  have hw := norm_kgWeight_le ρ
  calc (zetaZeroConfig.mult ρ : ℝ) * (‖Complex.cos (z * γ)‖ * ‖kgWeight ρ‖)
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (Real.exp (R / 2 + η * |γ.re|) *
          (sechConst * Real.exp (-|γ.re|))) := by
        gcongr
    _ = sechConst * Real.exp (R / 2) * ((zetaZeroConfig.mult ρ : ℝ) *
          Real.exp (-((1 - η) * |γ.re|))) := by
        rw [show Real.exp (R / 2 + η * |γ.re|) * (sechConst * Real.exp (-|γ.re|)) =
          sechConst * (Real.exp (R / 2 + η * |γ.re|) * Real.exp (-|γ.re|)) by ring,
          ← Real.exp_add, show R / 2 + η * |γ.re| + -|γ.re| = R / 2 + -((1 - η) * |γ.re|) by ring,
          Real.exp_add]
        ring

theorem norm_kgTerm_le' {z : ℂ} {η R : ℝ} (hη : |z.im| ≤ η) (hη0 : 0 ≤ η) (hR : |z.re| ≤ R)
    (ρ : zetaZeroConfig.carrier) :
    ‖(zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * kgFreq ρ) * kgWeight ρ)‖ ≤
      sechConst * Real.exp (R / 2 + 5 / 2 * η) * ((zetaZeroConfig.mult ρ : ℝ) *
        Real.exp (-((1 - η) * |(Zeta23.gammaOf (ρ : ℂ)).re|))) := by
  have hIm := abs_im_kgFreq_lt ρ
  have hRe := abs_re_kgFreq_le ρ
  set γ := Zeta23.gammaOf (ρ : ℂ)
  rw [norm_mul, norm_mul, Complex.norm_natCast]
  have hc : ‖Complex.cos (z * kgFreq ρ)‖ ≤ Real.exp (R / 2 + 5 / 2 * η + η * |γ.re|) := by
    refine (norm_cos_mul_le z (kgFreq ρ)).trans (Real.exp_le_exp.mpr ?_)
    have h1 : |z.re| * |(kgFreq ρ).im| ≤ R / 2 := by
      have := mul_le_mul hR hIm.le (abs_nonneg _) ((abs_nonneg _).trans hR); linarith
    have h2 : |z.im| * |(kgFreq ρ).re| ≤ η * (|γ.re| + 5 / 2) :=
      mul_le_mul hη hRe (abs_nonneg _) hη0
    linarith
  have hw := norm_kgWeight_le ρ
  calc (zetaZeroConfig.mult ρ : ℝ) * (‖Complex.cos (z * kgFreq ρ)‖ * ‖kgWeight ρ‖)
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (Real.exp (R / 2 + 5 / 2 * η + η * |γ.re|) *
          (sechConst * Real.exp (-|γ.re|))) := by
        gcongr
    _ = sechConst * Real.exp (R / 2 + 5 / 2 * η) * ((zetaZeroConfig.mult ρ : ℝ) *
          Real.exp (-((1 - η) * |γ.re|))) := by
        rw [show Real.exp (R / 2 + 5 / 2 * η + η * |γ.re|) * (sechConst * Real.exp (-|γ.re|)) =
          sechConst * (Real.exp (R / 2 + 5 / 2 * η + η * |γ.re|) * Real.exp (-|γ.re|)) by ring,
          ← Real.exp_add, show R / 2 + 5 / 2 * η + η * |γ.re| + -|γ.re| =
            R / 2 + 5 / 2 * η + -((1 - η) * |γ.re|) by ring, Real.exp_add]
        ring

/-- A point of the time strip has a box neighbourhood `|Im| < η`, `|Re| < R` with `η < 1`. -/
theorem exists_box_nhds {z₀ : ℂ} (hz₀ : z₀ ∈ causalTimeStrip) :
    ∃ η R : ℝ, 0 ≤ η ∧ η < 1 ∧ {z : ℂ | |z.im| < η ∧ |z.re| < R} ∈ 𝓝 z₀ := by
  have h : |z₀.im| < 1 := hz₀
  refine ⟨(|z₀.im| + 1) / 2, |z₀.re| + 1, by positivity, by linarith, ?_⟩
  refine IsOpen.mem_nhds ?_ ⟨by linarith, by linarith⟩
  exact (isOpen_lt (continuous_abs.comp continuous_im) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_re) continuous_const)

theorem differentiableOn_masslessZeroWave : DifferentiableOn ℂ masslessZeroWave causalTimeStrip := by
  intro z₀ hz₀
  obtain ⟨η, R, hη0, hη1, hU⟩ := exists_box_nhds hz₀
  set U := {z : ℂ | |z.im| < η ∧ |z.re| < R}
  have hUo : IsOpen U := (isOpen_lt (continuous_abs.comp continuous_im) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_re) continuous_const)
  have hd : DifferentiableOn ℂ masslessZeroWave U :=
    differentiableOn_tsum_of_summable_norm
      ((summable_mult_mul_exp_neg_abs_re (by linarith : (0 : ℝ) < 1 - η)).mul_left
        (sechConst * Real.exp (R / 2)))
      (fun ρ => (by fun_prop : Differentiable ℂ fun z : ℂ =>
        (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * Zeta23.gammaOf (ρ : ℂ)) *
          kgWeight ρ)).differentiableOn) hUo
      fun ρ z hz => norm_masslessTerm_le hz.1.le hz.2.le ρ
  exact (hd.differentiableAt hU).differentiableWithinAt

theorem differentiableOn_kgZeroWave : DifferentiableOn ℂ kgZeroWave causalTimeStrip := by
  intro z₀ hz₀
  obtain ⟨η, R, hη0, hη1, hU⟩ := exists_box_nhds hz₀
  set U := {z : ℂ | |z.im| < η ∧ |z.re| < R}
  have hUo : IsOpen U := (isOpen_lt (continuous_abs.comp continuous_im) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_re) continuous_const)
  have hd : DifferentiableOn ℂ kgZeroWave U :=
    differentiableOn_tsum_of_summable_norm
      ((summable_mult_mul_exp_neg_abs_re (by linarith : (0 : ℝ) < 1 - η)).mul_left
        (sechConst * Real.exp (R / 2 + 5 / 2 * η)))
      (fun ρ => (by fun_prop : Differentiable ℂ fun z : ℂ =>
        (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * kgFreq ρ) *
          kgWeight ρ)).differentiableOn) hUo
      fun ρ z hz => norm_kgTerm_le' hz.1.le hη0 hz.2.le ρ
  exact (hd.differentiableAt hU).differentiableWithinAt

theorem summable_masslessTerm (z : ℂ) (hz : z ∈ causalTimeStrip) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ) := by
  have h : |z.im| < 1 := hz
  exact Summable.of_norm_bounded
    ((summable_mult_mul_exp_neg_abs_re (by linarith : (0 : ℝ) < 1 - |z.im|)).mul_left
      (sechConst * Real.exp (|z.re| / 2))) fun ρ => norm_masslessTerm_le le_rfl le_rfl ρ

/-! ## Reality on the real axis -/

theorem masslessTerm_reflectZero (v : ℝ) (ρ : zetaZeroConfig.carrier) :
    Complex.cos (v * Zeta23.gammaOf ((reflectZero ρ : zetaZeroConfig.carrier) : ℂ)) *
        kgWeight (reflectZero ρ) =
      conj (Complex.cos (v * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ) := by
  rw [kgWeight_reflectZero, map_mul, ← Complex.cos_conj, map_mul, Complex.conj_ofReal]
  unfold reflectZero
  simp only
  rw [gammaOf_reflect]

theorem tsum_im_masslessTerm (v : ℝ) :
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
      (Complex.cos (v * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ).im = 0 := by
  set f : zetaZeroConfig.carrier → ℝ := fun ρ => (zetaZeroConfig.mult ρ : ℝ) *
    (Complex.cos (v * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ).im with hf
  have hrefl : ∀ ρ, f (reflectEquiv ρ) = -f ρ := by
    intro ρ
    simp only [hf, reflectEquiv, Equiv.coe_fn_mk, mult_reflectZero, masslessTerm_reflectZero,
      Complex.conj_im]
    ring
  have h1 : ∑' ρ, f ρ = ∑' ρ, f (reflectEquiv ρ) := (reflectEquiv.tsum_eq f).symm
  have h2 : ∑' ρ, f (reflectEquiv ρ) = -∑' ρ, f ρ := by
    simp_rw [hrefl]; exact tsum_neg
  have : ∑' ρ, f ρ = -∑' ρ, f ρ := h1.trans h2
  linarith

theorem masslessZeroWave_ofReal_eq_tsum_re (v : ℝ) :
    masslessZeroWave v = ((∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
      (Complex.cos (v * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ).re : ℝ) : ℂ) := by
  have hs := summable_masslessTerm (v : ℂ) (by simp [causalTimeStrip])
  apply Complex.ext
  · rw [Complex.ofReal_re, masslessZeroWave, Complex.re_tsum hs]
    exact tsum_congr fun ρ => by simp [Complex.mul_re]
  · rw [Complex.ofReal_im, masslessZeroWave, Complex.im_tsum hs, ← tsum_im_masslessTerm v]
    exact tsum_congr fun ρ => by simp [Complex.mul_im]

/-! ## The massless explicit formula -/

/-- `Ψ_v(z) = cos(vz/2) sech(z/2)`. -/
def cosHalfSech (v : ℝ) (z : ℂ) : ℂ := Complex.cos (v * z / 2) * sechHalf z

theorem evenStrip_cosHalfSech (v : ℝ) : EvenStrip (cosHalfSech v) := by
  refine ⟨⟨1 / 2, Real.exp (|v| * (5 / 4) / 2) * (2 / Real.cos (5 / 8)), by norm_num,
    fun z hz => ?_, fun z hz => ?_⟩, fun z => ?_, fun r => ?_⟩
  · exact (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.cos (v * z / 2)).differentiableAt.mul
      (evenStrip_sechHalf.strip.choose_spec.choose_spec.2.diff z hz)
  · unfold cosHalfSech
    rw [norm_mul, mul_assoc]
    refine mul_le_mul ?_ (norm_sechHalf_le hz) (norm_nonneg _) (Real.exp_pos _).le
    refine (norm_ccos_le_exp_abs_im _).trans (Real.exp_le_exp.mpr ?_)
    have him : (v * z / 2 : ℂ).im = v * z.im / 2 := by simp [Complex.mul_im]
    rw [him, abs_div, abs_mul, abs_two]
    gcongr
  · unfold cosHalfSech
    rw [show (v : ℂ) * -z / 2 = -(v * z / 2) by ring, Complex.cos_neg, evenStrip_sechHalf.even]
  · unfold cosHalfSech
    rw [sechHalf_ofReal, show (v : ℂ) * r / 2 = ((v * r / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos, ← Complex.ofReal_mul, Complex.ofReal_im]

theorem specSq_cosHalfSech (v : ℝ) (z : ℂ) :
    specSq (cosHalfSech v) z = Complex.cos (v * z / 2) ^ 2 * specSq sechHalf z := by
  unfold specSq cosHalfSech
  rw [map_mul, ← Complex.cos_conj, show conj ((v : ℂ) * conj z / 2) = v * z / 2 by
    rw [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj, map_ofNat]]
  ring

/-- `cos(vz) sech²(z/2) = 2 Ψ_v Ψ_v^# − sech sech^#`. -/
theorem cos_mul_specSq_sechHalf_eq (v : ℝ) (z : ℂ) :
    Complex.cos (v * z) * specSq sechHalf z =
      2 * specSq (cosHalfSech v) z - specSq sechHalf z := by
  have h : Complex.cos (v * z) = 2 * Complex.cos (v * z / 2) ^ 2 - 1 := by
    rw [← Complex.cos_two_mul]; congr 1; ring
  rw [specSq_cosHalfSech, h]
  ring

/-- The massless Weil side `(2/cos²(1/4)) cosh(v/2) + (1/2π) A₀(v) − P₀(v)`. -/
def masslessWeilSide (v : ℝ) : ℝ :=
  2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2) + 1 / (2 * π) * masslessArchWave v -
    masslessPrimeWave v

theorem evenWeilDensity_cos_mul_specSq_sechHalf (v : ℝ) :
    evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (fun z => Complex.cos (v * z) * specSq sechHalf z) = masslessWeilSide v := by
  rw [evenWeilDensity_eq_parts]
  have hpole : evenPolePart (fun z => Complex.cos (v * z) * specSq sechHalf z) =
      2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2) := by
    rw [← evenPolePart_specSq_sechHalf]
    unfold evenPolePart
    have h1 : Complex.cos (v * (I / 2)) = (Real.cosh (v / 2) : ℂ) := by
      rw [show (v : ℂ) * (I / 2) = ((v / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.cos_mul_I,
        Complex.ofReal_cosh]
    have h2 : Complex.cos (v * (-I / 2)) = (Real.cosh (v / 2) : ℂ) := by
      rw [show (v : ℂ) * (-I / 2) = -(v * (I / 2)) by ring, Complex.cos_neg, h1]
    simp only
    rw [h1, h2, ← mul_add, Complex.re_ofReal_mul, mul_comm]
  have harch : evenArchPart (fun z => Complex.cos (v * z) * specSq sechHalf z) =
      masslessArchWave v := by
    unfold evenArchPart masslessArchWave
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [show (v : ℂ) * r = ((v * r : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      Complex.re_ofReal_mul, specSq_sechHalf_ofReal_re]
  have hprime : evenPrimePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (fun z => Complex.cos (v * z) * specSq sechHalf z) = masslessPrimeWave v := by
    unfold evenPrimePart masslessPrimeWave
    refine tsum_congr fun n => ?_
    congr 1
    rw [← integral_cos_mul_sechSqHalf_mul_cos v (Real.log n)]
    congr 2
    funext r
    beta_reduce
    rw [show (v : ℂ) * r = ((v * r : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      Complex.re_ofReal_mul, specSq_sechHalf_ofReal_re]
  rw [hpole, harch, hprime]
  rfl

/-- **The massless explicit formula**:
`Σ_ρ m_ρ Re(cos(vγ_ρ) w_ρ) = (2/cos²(1/4)) cosh(v/2) + (1/2π) A₀(v) − P₀(v)`. -/
theorem tsum_re_masslessTerm_eq (v : ℝ) :
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
      (Complex.cos (v * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ).re = masslessWeilSide v := by
  have hΨ := goodDensity_specSq (evenStrip_cosHalfSech v)
  have hS := goodDensity_specSq evenStrip_sechHalf
  have hlin := evenWeilDensity_sum abs_vonMangoldt_le_sqrt_mul_one_add_log
    (Finset.univ : Finset (Fin 2)) ![2, -1] (K := ![specSq (cosHalfSech v), specSq sechHalf])
    (fun i _ => by fin_cases i <;> simpa)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hlin
  have hfun : (fun z => Complex.cos (v * z) * specSq sechHalf z) =
      fun z => ((2 : ℝ) : ℂ) * specSq (cosHalfSech v) z + ((-1 : ℝ) : ℂ) * specSq sechHalf z := by
    funext z
    rw [cos_mul_specSq_sechHalf_eq]
    push_cast
    ring
  rw [← evenWeilDensity_cos_mul_specSq_sechHalf v, hfun, hlin,
    evenWeilDensity_specSq_vonMangoldt_eq_tsum_re (evenStrip_cosHalfSech v),
    evenWeilDensity_specSq_vonMangoldt_eq_tsum_re evenStrip_sechHalf,
    ← tsum_mul_left, ← tsum_mul_left,
    ← (summable_re_zeroSide_of_goodDensity hΨ).mul_left 2 |>.tsum_add
      ((summable_re_zeroSide_of_goodDensity hS).mul_left (-1))]
  refine tsum_congr fun ρ => ?_
  unfold CHMDGrowthCollapse.kgWeight
  rw [cos_mul_specSq_sechHalf_eq]
  simp [Complex.mul_re]
  ring

/-- **The massless explicit formula in complex form**: `Φ₀(v) = W₀(v)` for real `v`. -/
theorem masslessZeroWave_ofReal (v : ℝ) : masslessZeroWave v = (masslessWeilSide v : ℂ) := by
  rw [masslessZeroWave_ofReal_eq_tsum_re, tsum_re_masslessTerm_eq]

end RHTower.CHMDLightCone
