import GaloisForLFunctions.CompactHyperbolicSurfaces.AutomorphicKernels
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCayleyDensity
import GaloisForLFunctions.HTGeometry.AnalyticCircleMean
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral

/-!
# The Bergman kernel of the upper half-plane

`h(z, w) = 2i √(Im z Im w)/(z − w̄)` (`bergK`) is the weight-one Bergman factor:

* `|h(z, w)|² = 1/(1 + u(z, w))`, `h(z, z) = 1`, `h(w, z) = \overline{h(z, w)}`;
* `h(gz, gw) = ε_g(z) \overline{ε_g(w)} h(z, w)` for `g ∈ SL(2, ℝ)` (`bergK_smul`), with the
  unimodular cocycle `ε_g(z) = (cz + d)/|cz + d|` (`autF`, `autF_mul`);
* **reproducing identity** (`integral_bergK_pow`): for `n ≥ 0`,
  `∫_ℍ h(z, y)^{n+2} h(y, w)^{n+2} dμ(y) = (4π/(n + 1)) h(z, w)^{n+2}`.

For the identity, `z = i` by equivariance.  The Cayley map `y = i(1 + ζ)/(1 − ζ)`,
`w = i(1 + ω)/(1 − ω)` gives `h(i, y) h(y, w) = (1 − |ζ|²) h(i, w)/(1 − ζω̄)` and
`dμ = 4 dA/(1 − |ζ|²)²`, and `∫_D (1 − |ζ|²)^n f dA = π f(0)/(n + 1)` for bounded holomorphic `f`
(polar coordinates and the circle mean value, `integral_ball_weight_mul`).  The same chart gives
`1 + u(i, y) = 1/(1 − |ζ|²)`, so `∫_ℍ (1 + u(z, y))^{−(n+2)} dμ(y) < ∞`
(`lintegral_one_add_pairU_pow_lt_top`).
-/

open MeasureTheory Set Filter UpperHalfPlane Metric
open scoped ENNReal MatrixGroups ComplexConjugate Real

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The kernel -/

/-- The Bergman factor `h(z, w) = 2i √(Im z Im w)/(z − w̄)`. -/
def bergK (z w : ℂ) : ℂ := 2 * Complex.I * (√(z.im * w.im) : ℝ) / (z - conj w)

theorem sub_conj_ne_zero {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : z - conj w ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
  linarith

/-- `|z − w̄|² = |z − w|² + 4 Im z Im w`. -/
theorem normSq_sub_conj (z w : ℂ) :
    Complex.normSq (z - conj w) = Complex.normSq (z - w) + 4 * z.im * w.im := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

/-- `1 + u(z, w) = |z − w̄|²/(4 Im z Im w)`. -/
theorem one_add_pairU_eq (z w : ℍ) :
    1 + pairU z w = Complex.normSq ((z : ℂ) - conj (w : ℂ)) / (4 * z.im * w.im) := by
  have hz := z.im_pos
  have hw := w.im_pos
  rw [pairU, normSq_sub_conj, Complex.dist_eq, ← Complex.normSq_eq_norm_sq]
  simp only [coe_im]
  field_simp
  ring

/-- `|h(z, w)|² = 1/(1 + u(z, w))`. -/
theorem norm_bergK_sq (z w : ℍ) : ‖bergK z w‖ ^ 2 = (1 + pairU z w)⁻¹ := by
  have hz := z.im_pos
  have hw := w.im_pos
  have hne := sub_conj_ne_zero (z := (z : ℂ)) (w := (w : ℂ)) hz hw
  have hN : 0 < Complex.normSq ((z : ℂ) - conj (w : ℂ)) := Complex.normSq_pos.mpr hne
  rw [one_add_pairU_eq, inv_div, ← Complex.normSq_eq_norm_sq, bergK, Complex.normSq_div,
    Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (by simp only [coe_im]; positivity)]
  simp only [Complex.normSq_I, coe_im]
  norm_num
  field_simp

/-- `|h(z, w)^{2k}| = (1 + u(z, w))^{−k}`. -/
theorem norm_bergK_pow_two_mul (z w : ℍ) (k : ℕ) :
    ‖bergK z w ^ (2 * k)‖ = ((1 + pairU z w) ^ k)⁻¹ := by
  rw [norm_pow, pow_mul, norm_bergK_sq, inv_pow]

theorem norm_bergK_le_one (z w : ℍ) : ‖bergK z w‖ ≤ 1 := by
  have h := norm_bergK_sq z w
  have hu := pairU_nonneg z w
  have h1 : ‖bergK z w‖ ^ 2 ≤ 1 ^ 2 := by
    rw [h, one_pow]; exact inv_le_one_of_one_le₀ (by linarith)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h1

/-- `h(z, z) = 1`. -/
theorem bergK_self (z : ℍ) : bergK z z = 1 := by
  have hz := z.im_pos
  rw [bergK, Complex.sub_conj]
  simp only [coe_im]
  rw [Real.sqrt_mul_self hz.le]
  have h2 : ((2 * z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * z.im) ≠ 0)
  rw [div_eq_one_iff_eq (mul_ne_zero h2 Complex.I_ne_zero)]
  push_cast
  ring

/-- `h(w, z) = \overline{h(z, w)}`. -/
theorem bergK_swap (z w : ℂ) : bergK w z = conj (bergK z w) := by
  rw [bergK, bergK, map_div₀, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I, map_sub,
    Complex.conj_conj, map_ofNat, mul_comm w.im z.im]
  rw [show conj z - w = -(w - conj z) by ring, div_neg]
  ring

/-! ### The automorphy factor -/

theorem det_SL' (g : SL(2, ℝ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe g
  rwa [Matrix.det_fin_two] at h

/-- `j_g(z) = cz + d`. -/
def jF (g : SL(2, ℝ)) (z : ℂ) : ℂ := (g 1 0 : ℂ) * z + g 1 1

/-- The unimodular automorphy factor `ε_g(z) = (cz + d)/|cz + d|`. -/
def autF (g : SL(2, ℝ)) (z : ℂ) : ℂ := jF g z / (‖jF g z‖ : ℂ)

theorem jF_ne_zero (g : SL(2, ℝ)) (z : ℍ) : jF g z ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [jF, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    coe_re, coe_im, zero_mul, sub_zero, Complex.zero_re, Complex.add_im, Complex.mul_im,
    add_zero, Complex.zero_im] at h1 h2
  have hc : g 1 0 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h z.im_pos.ne'
  rw [hc, zero_mul, zero_add] at h1
  have := det_SL' g
  rw [hc, h1] at this
  simp at this

theorem conj_jF (g : SL(2, ℝ)) (z : ℂ) : conj (jF g z) = jF g (conj z) := by
  simp only [jF, map_add, map_mul, Complex.conj_ofReal]

theorem norm_autF (g : SL(2, ℝ)) (z : ℍ) : ‖autF g z‖ = 1 := by
  rw [autF, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (jF_ne_zero g z))]

/-- `\overline{ε} ε = 1`. -/
theorem conj_autF_mul_self (g : SL(2, ℝ)) (z : ℍ) : conj (autF g z) * autF g z = 1 := by
  rw [Complex.conj_mul', norm_autF]
  simp

theorem coe_smul_eq (g : SL(2, ℝ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = ((g 0 0 : ℂ) * z + g 0 1) / jF g z := by
  rw [coe_specialLinearGroup_apply]; rfl

/-- `gz − \overline{gw} = (z − w̄)/(j_g(z) \overline{j_g(w)})`. -/
theorem smul_sub_conj (g : SL(2, ℝ)) (z w : ℍ) :
    ((g • z : ℍ) : ℂ) - conj ((g • w : ℍ) : ℂ) = ((z : ℂ) - conj (w : ℂ)) /
      (jF g z * conj (jF g w)) := by
  have hz := jF_ne_zero g z
  have hw : conj (jF g w) ≠ 0 := (map_ne_zero _).mpr (jF_ne_zero g w)
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by exact_mod_cast det_SL' g
  rw [coe_smul_eq, coe_smul_eq, map_div₀, conj_jF]
  rw [conj_jF] at hw
  simp only [map_add, map_mul, Complex.conj_ofReal]
  rw [div_sub_div _ _ hz hw, div_eq_div_iff (mul_ne_zero hz hw) (mul_ne_zero hz hw)]
  simp only [jF]
  linear_combination (((g 1 0 : ℂ) * z + g 1 1) * ((g 1 0 : ℂ) * conj (w : ℂ) + g 1 1) *
    ((z : ℂ) - conj (w : ℂ))) * hdet

/-- `Im(gz) = Im z/|j_g(z)|²`. -/
theorem im_smul_eq (g : SL(2, ℝ)) (z : ℍ) : (g • z).im = z.im / ‖jF g z‖ ^ 2 := by
  have h := congrArg Complex.im (smul_sub_conj g z z)
  rw [Complex.sub_conj, Complex.sub_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.div_ofReal_im] at h
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
    mul_zero, add_zero, mul_one, coe_im] at h
  rw [mul_div_assoc] at h
  linarith

/-- **Equivariance.**  `h(gz, gw) = h(z, w) ε_g(z) \overline{ε_g(w)}`. -/
theorem bergK_smul (g : SL(2, ℝ)) (z w : ℍ) :
    bergK (g • z : ℍ) (g • w : ℍ) = bergK z w * autF g z * conj (autF g w) := by
  have hz := z.im_pos
  have hw := w.im_pos
  have hjz := jF_ne_zero g z
  have hjw := jF_ne_zero g w
  have hnz : ‖jF g z‖ ≠ 0 := norm_ne_zero_iff.mpr hjz
  have hnw : ‖jF g w‖ ≠ 0 := norm_ne_zero_iff.mpr hjw
  have hsq : √((g • z).im * (g • w).im) = √(z.im * w.im) / (‖jF g z‖ * ‖jF g w‖) := by
    rw [im_smul_eq, im_smul_eq, div_mul_div_comm, ← mul_pow, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by positivity)]
  have hne := sub_conj_ne_zero (z := (z : ℂ)) (w := (w : ℂ)) hz hw
  rw [bergK, bergK, show ((g • z : ℍ) : ℂ).im = (g • z).im from rfl,
    show ((g • w : ℍ) : ℂ).im = (g • w).im from rfl, hsq, smul_sub_conj, autF, autF, map_div₀,
    Complex.conj_ofReal]
  simp only [coe_im]
  have hcw : conj (jF g w) ≠ 0 := (map_ne_zero _).mpr hjw
  push_cast
  field_simp

/-- `j_{gh}(z) = j_g(hz) j_h(z)`. -/
theorem jF_mul (g h : SL(2, ℝ)) (z : ℍ) : jF (g * h) z = jF g (h • z : ℍ) * jF h z := by
  have hj : (h 1 0 : ℂ) * z + h 1 1 ≠ 0 := jF_ne_zero h z
  rw [coe_smul_eq]
  simp only [jF, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  field_simp
  ring

/-- **Cocycle.**  `ε_{gh}(z) = ε_g(hz) ε_h(z)`. -/
theorem autF_mul (g h : SL(2, ℝ)) (z : ℍ) : autF (g * h) z = autF g (h • z : ℍ) * autF h z := by
  rw [autF, autF, autF, jF_mul, norm_mul]
  have h1 := jF_ne_zero g (h • z)
  have h2 := jF_ne_zero h z
  have h1' : (‖jF g (h • z : ℍ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h1
  have h2' : (‖jF h z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h2
  push_cast
  field_simp

theorem autF_one (z : ℂ) : autF 1 z = 1 := by
  simp [autF, jF]

/-! ### Integrals over `ℍ` in the plane and in the disk -/

theorem range_coe_upperHalfPlane : Set.range UpperHalfPlane.coe = {z : ℂ | 0 < z.im} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩; exact y.im_pos
  · intro hz; exact ⟨⟨z, hz⟩, rfl⟩

theorem measurePreserving_coe_upperHalfPlane :
    MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict {z : ℂ | 0 < z.im}) :=
  ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap, range_coe_upperHalfPlane]⟩

/-- `∫_ℍ G dμ = ∫_{Im z > 0} G(z) (Im z)^{−2} dA`. -/
theorem integral_upperHalfPlane_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℂ → E) : ∫ y : ℍ, G y = ∫ z in {z : ℂ | 0 < z.im}, (z.im)⁻¹ ^ 2 • G z := by
  rw [volume_eq_comap_withDensity, integral_withDensity_eq_integral_toReal_smul
    measurable_hyperbolicDensity (ae_of_all _ hyperbolicDensity_lt_top)]
  simp_rw [hyperbolicDensity_toReal, ← inv_pow]
  exact measurePreserving_coe_upperHalfPlane.integral_comp measurableEmbedding_coe
    (fun z : ℂ => (z.im)⁻¹ ^ 2 • G z)

/-- The lower-integral form of `integral_upperHalfPlane_eq`. -/
theorem lintegral_upperHalfPlane_eq {G : ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y : ℍ, G y = ∫⁻ z in {z : ℂ | 0 < z.im}, ENNReal.ofReal ((z.im)⁻¹ ^ 2) * G z := by
  rw [volume_eq_comap_withDensity]
  change ∫⁻ y : ℍ, (G ∘ UpperHalfPlane.coe) y ∂_ = _
  rw [lintegral_withDensity_eq_lintegral_mul _ measurable_hyperbolicDensity
    (hG.comp measurable_coe)]
  simp only [Pi.mul_apply, Function.comp_apply, hyperbolicDensity, ← inv_pow]
  exact measurePreserving_coe_upperHalfPlane.lintegral_comp_emb measurableEmbedding_coe
    (fun z : ℂ => ENNReal.ofReal ((z.im)⁻¹ ^ 2) * G z)

/-- The Cayley chart for lower integrals: `dx dy/y² = 4 dA/(1 − |ζ|²)²`. -/
theorem lintegral_diskToUpper (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in {z : ℂ | 0 < z.im}, ENNReal.ofReal ((z.im)⁻¹ ^ 2) * g z =
      ∫⁻ ζ in ball 0 1, ENNReal.ofReal (4 / (1 - Complex.normSq ζ) ^ 2) * g (diskToUpper ζ) := by
  rw [← diskToUpper_image_ball, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    measurableSet_ball (fun w hw => ?_) diskToUpper_injOn_ball]
  · refine setLIntegral_congr_fun measurableSet_ball fun ζ hζ => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), diskToUpper_hyperbolic_density ζ hζ]
  · have hw1 : ‖w‖ < 1 := by simpa using hw
    have hw_ne : w ≠ 1 := by rintro rfl; norm_num at hw1
    exact (hasDerivAt_diskToUpper hw_ne).complexToReal_fderiv.hasFDerivWithinAt

/-! ### The Cayley chart -/

theorem ne_one_of_norm_lt_one {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ζ ≠ 1 := by
  rintro rfl; norm_num at hζ

theorem one_sub_conj_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 - conj ζ ≠ 0 := by
  rw [← map_one (starRingEnd ℂ), ← map_sub]
  exact (map_ne_zero _).mpr (sub_ne_zero.mpr (ne_one_of_norm_lt_one hζ).symm)

theorem one_sub_mul_conj_ne_zero {ζ ω : ℂ} (hζ : ‖ζ‖ < 1) (hω : ‖ω‖ < 1) :
    1 - ζ * conj ω ≠ 0 := by
  intro h
  have h1 : ‖ζ * conj ω‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
  rw [norm_mul, Complex.norm_conj] at h1
  nlinarith [norm_nonneg ζ, norm_nonneg ω]

theorem conj_diskToUpper (ζ : ℂ) :
    conj (diskToUpper ζ) = -Complex.I * (1 + conj ζ) / (1 - conj ζ) := by
  rw [diskToUpper, map_div₀, map_mul, Complex.conj_I, map_add, map_sub, map_one]

theorem I_sub_conj_diskToUpper {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    Complex.I - conj (diskToUpper ζ) = 2 * Complex.I / (1 - conj ζ) := by
  have h := one_sub_conj_ne_zero hζ
  rw [conj_diskToUpper]
  field_simp
  ring

theorem diskToUpper_sub_conj {ζ ω : ℂ} (hζ : ‖ζ‖ < 1) (hω : ‖ω‖ < 1) :
    diskToUpper ζ - conj (diskToUpper ω) =
      2 * Complex.I * (1 - ζ * conj ω) / ((1 - ζ) * (1 - conj ω)) := by
  have h1 : 1 - ζ ≠ 0 := sub_ne_zero.mpr (ne_one_of_norm_lt_one hζ).symm
  have h2 := one_sub_conj_ne_zero hω
  rw [conj_diskToUpper, diskToUpper]
  field_simp
  ring

/-- `h(i, y) h(y, w) = −4 Im y √(Im w)/((i − ȳ)(y − w̄))`. -/
theorem bergK_I_mul_bergK {y w : ℂ} (hy : 0 < y.im) :
    bergK Complex.I y * bergK y w =
      -4 * (y.im : ℂ) * (√w.im : ℝ) / ((Complex.I - conj y) * (y - conj w)) := by
  simp only [bergK, Complex.I_im, one_mul]
  rw [Real.sqrt_mul hy.le, div_mul_div_comm]
  congr 1
  have hs : ((√y.im : ℝ) : ℂ) * (√y.im : ℝ) = y.im := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hy.le]
  push_cast
  linear_combination (4 * ((√y.im : ℝ) : ℂ) ^ 2 * ((√w.im : ℝ) : ℂ)) * Complex.I_sq +
    (-4 * ((√w.im : ℝ) : ℂ)) * hs

/-- **The kernel in the Cayley chart.**  For `y = i(1+ζ)/(1−ζ)`, `w = i(1+ω)/(1−ω)`:
`h(i, y) h(y, w) = (1 − |ζ|²) h(i, w)/(1 − ζω̄)`. -/
theorem bergK_cayley {ζ ω : ℂ} (hζ : ‖ζ‖ < 1) (hω : ‖ω‖ < 1) :
    bergK Complex.I (diskToUpper ζ) * bergK (diskToUpper ζ) (diskToUpper ω) =
      ((1 - Complex.normSq ζ : ℝ) : ℂ) * bergK Complex.I (diskToUpper ω) / (1 - ζ * conj ω) := by
  have hy : 0 < (diskToUpper ζ).im := diskToUpper_im_pos ζ (by simpa using hζ)
  have h1 : 1 - ζ ≠ 0 := sub_ne_zero.mpr (ne_one_of_norm_lt_one hζ).symm
  have h2 := one_sub_conj_ne_zero hζ
  have h3 := one_sub_conj_ne_zero hω
  have h4 := one_sub_mul_conj_ne_zero hζ hω
  have hN : ((Complex.normSq (1 - ζ) : ℝ) : ℂ) = (1 - ζ) * (1 - conj ζ) := by
    rw [← Complex.mul_conj, map_sub, map_one]
  rw [bergK_I_mul_bergK hy, diskToUpper_im (ne_one_of_norm_lt_one hζ), I_sub_conj_diskToUpper hζ,
    diskToUpper_sub_conj hζ hω]
  conv_rhs => rw [bergK, Complex.I_im, one_mul, I_sub_conj_diskToUpper hω]
  push_cast
  rw [hN]
  field_simp
  linear_combination (-4 * (1 - (Complex.normSq ζ : ℂ)) * ((√(diskToUpper ω).im : ℝ) : ℂ)) *
    Complex.I_sq

/-! ### The weighted mean value on the disk -/

/-- Polar coordinates on the disk `ball 0 r`. -/
theorem setIntegral_ball_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℂ → E)
    (r : ℝ) : ∫ z in ball (0 : ℂ) r, g z =
      ∫ p in Ioo 0 r ×ˢ Ioo (-π) π, p.1 • g (Complex.polarCoord.symm p) := by
  have hS : MeasurableSet (Ioo 0 r ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  have hSsub : Ioo 0 r ×ˢ Ioo (-π) π ⊆ Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]; intro p hp; exact ⟨Ioo_subset_Ioi_self hp.1, hp.2⟩
  rw [← integral_indicator measurableSet_ball, ← Complex.integral_comp_polarCoord_symm
    ((ball (0 : ℂ) r).indicator g), ← Set.inter_eq_right.mpr hSsub, ← setIntegral_indicator hS]
  refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
  rw [polarCoord_target] at hp
  have hiff : Complex.polarCoord.symm p ∈ ball (0 : ℂ) r ↔ p ∈ Ioo 0 r ×ˢ Ioo (-π) π := by
    rw [mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    exact ⟨fun h => ⟨⟨hp.1, h⟩, hp.2⟩, fun h => h.1.2⟩
  by_cases h : p ∈ Ioo 0 r ×ˢ Ioo (-π) π
  · rw [indicator_of_mem (hiff.mpr h), indicator_of_mem h]
  · rw [indicator_of_notMem (fun h' => h (hiff.mp h')), indicator_of_notMem h, smul_zero]

theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, zero_add]

/-- The circle mean value over `(−π, π)`. -/
theorem integral_Ioo_circleMap {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ θ in Ioo (-π) π, f (circleMap 0 r θ) = (2 * π : ℂ) * f 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hp := ((periodic_circleMap 0 r).comp f).intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hp
  rw [show (fun θ => f (circleMap 0 r θ)) = f ∘ circleMap 0 r from rfl, hp]
  exact integral_circleMap_eq_center_of_analyticOnNhd_unitBall (hf.analyticOnNhd isOpen_ball)
    hr0 hr1

/-- `∫_0^1 r (1 − r²)^n dr = 1/(2(n + 1))`. -/
theorem integral_Ioo_mul_one_sub_sq_pow (n : ℕ) :
    ∫ r in Ioo (0 : ℝ) 1, r * (1 - r ^ 2) ^ n = 1 / (2 * ((n : ℝ) + 1)) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun r : ℝ => -(1 - r ^ 2) ^ (n + 1) / (2 * ((n : ℝ) + 1))) (x * (1 - x ^ 2) ^ n) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_sub (1 : ℝ)
    refine ((h1.pow (n + 1)).neg.div_const (2 * ((n : ℝ) + 1))).congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  field_simp
  ring

/-- **Weighted mean value on the disk.**  For `f` holomorphic and bounded on the unit disk,
`∫_D (1 − |ζ|²)^n f(ζ) dA = π f(0)/(n + 1)`. -/
theorem integral_ball_weight_mul {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) {B : ℝ}
    (hB : ∀ ζ ∈ ball (0 : ℂ) 1, ‖f ζ‖ ≤ B) (n : ℕ) :
    ∫ ζ in ball (0 : ℂ) 1, ((1 - Complex.normSq ζ : ℝ) : ℂ) ^ n * f ζ =
      ((π / (n + 1) : ℝ) : ℂ) * f 0 := by
  set S : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo (-π) π
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  set F : ℝ × ℝ → ℂ := fun p => ((p.1 * (1 - p.1 ^ 2) ^ n : ℝ) : ℂ) * f (circleMap 0 p.1 p.2)
  have hbox : ∀ p ∈ S, p.1 • (((1 - Complex.normSq (Complex.polarCoord.symm p) : ℝ) : ℂ) ^ n *
      f (Complex.polarCoord.symm p)) = F p := by
    intro p hp
    rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm, sq_abs,
      polarCoord_symm_eq_circleMap, Complex.real_smul]
    simp only [F]
    push_cast
    ring
  -- integrability on the box
  have hmaps : MapsTo (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) S (ball 0 1) := by
    intro p hp
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hp.1.1]
    exact hp.1.2
  have hcont : ContinuousOn F S := by
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) ?_
    exact hf.continuousOn.comp (Continuous.continuousOn (by unfold circleMap; fun_prop)) hmaps
  have hfin : (volume : Measure (ℝ × ℝ)) S ≠ ∞ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  have hint : IntegrableOn F S (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    refine ⟨hcont.aestronglyMeasurable hS, HasFiniteIntegral.restrict_of_bounded (C := B)
      hfin.lt_top ((ae_restrict_iff' hS).mpr (Eventually.of_forall fun p hp => ?_))⟩
    have h0 : 0 ≤ p.1 := hp.1.1.le
    have h1 : p.1 ≤ 1 := hp.1.2.le
    have hq0 : 0 ≤ 1 - p.1 ^ 2 := by nlinarith
    have hq1 : 1 - p.1 ^ 2 ≤ 1 := by nlinarith
    have hw : p.1 * (1 - p.1 ^ 2) ^ n ≤ 1 :=
      mul_le_one₀ h1 (pow_nonneg hq0 n) (pow_le_one₀ hq0 hq1)
    simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg h0, abs_of_nonneg (pow_nonneg hq0 n)]
    exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans (hB _ (hmaps hp))
  rw [setIntegral_ball_polar, setIntegral_congr_fun hS hbox, Measure.volume_eq_prod,
    setIntegral_prod F hint]
  have hinner : ∀ r ∈ Ioo (0 : ℝ) 1, ∫ θ in Ioo (-π) π, F (r, θ) =
      ((r * (1 - r ^ 2) ^ n : ℝ) : ℂ) * ((2 * π : ℂ) * f 0) := by
    intro r hr
    simp only [F]
    rw [integral_const_mul, integral_Ioo_circleMap hf hr.1.le hr.2]
  rw [setIntegral_congr_fun measurableSet_Ioo hinner, integral_mul_const, integral_complex_ofReal,
    integral_Ioo_mul_one_sub_sq_pow]
  push_cast
  field_simp

/-! ### The reproducing identity -/

/-- The reproducing identity at `z = i`. -/
theorem integral_bergK_I_pow (n : ℕ) (w : ℍ) :
    ∫ y : ℍ, bergK Complex.I y ^ (n + 2) * bergK y w ^ (n + 2) =
      ((4 * π / (n + 1) : ℝ) : ℂ) * bergK Complex.I w ^ (n + 2) := by
  set ω := upperToDisk w
  have hω : ‖ω‖ < 1 := by
    have h := normSq_upperToDisk_lt_one w.im_pos
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg ω]
  have hwω : diskToUpper ω = w := diskToUpper_upperToDisk w.im_pos
  rw [integral_upperHalfPlane_eq (fun y => bergK Complex.I y ^ (n + 2) * bergK y w ^ (n + 2)),
    integral_diskToUpper_hyperbolic]
  set f : ℂ → ℂ := fun ζ => ((1 - ζ * conj ω) ^ (n + 2))⁻¹
  have hpt : ∀ ζ ∈ ball (0 : ℂ) 1, (4 / (1 - Complex.normSq ζ) ^ (2 : ℕ)) •
      (bergK Complex.I (diskToUpper ζ) ^ (n + 2) * bergK (diskToUpper ζ) w ^ (n + 2)) =
      (4 * bergK Complex.I w ^ (n + 2)) * (((1 - Complex.normSq ζ : ℝ) : ℂ) ^ n * f ζ) := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ < 1 := by simpa using hζ
    have hq : (1 : ℝ) - Complex.normSq ζ ≠ 0 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
    have hq' : ((1 - Complex.normSq ζ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq
    have h4 := one_sub_mul_conj_ne_zero hζ1 hω
    rw [← mul_pow, ← hwω, bergK_cayley hζ1 hω, Complex.real_smul, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
    simp only [f]
    generalize ((1 - Complex.normSq ζ : ℝ) : ℂ) = a at hq' ⊢
    generalize 1 - ζ * conj ω = D at h4 ⊢
    rw [div_pow, mul_pow, pow_add a n 2]
    field_simp
  rw [setIntegral_congr_fun measurableSet_ball hpt, integral_const_mul]
  have hf : DifferentiableOn ℂ f (ball 0 1) := by
    intro ζ hζ
    have := one_sub_mul_conj_ne_zero (by simpa using hζ) hω
    exact (DifferentiableAt.inv (by fun_prop) (pow_ne_zero _ this)).differentiableWithinAt
  have hB : ∀ ζ ∈ ball (0 : ℂ) 1, ‖f ζ‖ ≤ ((1 - ‖ω‖) ^ (n + 2))⁻¹ := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ < 1 := by simpa using hζ
    have hlow : 1 - ‖ω‖ ≤ ‖1 - ζ * conj ω‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (ζ * conj ω)
      rw [norm_one, norm_mul, Complex.norm_conj] at h
      nlinarith [norm_nonneg ζ, norm_nonneg ω]
    simp only [f, norm_inv, norm_pow]
    exact inv_anti₀ (pow_pos (by linarith) _) (pow_le_pow_left₀ (by linarith) hlow _)
  rw [integral_ball_weight_mul hf hB n]
  simp only [f, zero_mul, sub_zero, one_pow, inv_one, mul_one]
  push_cast
  ring

/-- **The reproducing identity.**
`∫_ℍ h(z, y)^{n+2} h(y, w)^{n+2} dμ(y) = (4π/(n + 1)) h(z, w)^{n+2}`. -/
theorem integral_bergK_pow (n : ℕ) (z w : ℍ) :
    ∫ y : ℍ, bergK z y ^ (n + 2) * bergK y w ^ (n + 2) =
      ((4 * π / (n + 1) : ℝ) : ℂ) * bergK z w ^ (n + 2) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq SL(2, ℝ) I z
  set w' := g⁻¹ • w
  have hw : w = g • w' := (smul_inv_smul g w).symm
  rw [hw, ← integral_smul_eq_self (fun y : ℍ => bergK (g • I : ℍ) y ^ (n + 2) *
    bergK y (g • w' : ℍ) ^ (n + 2)) (g := g)]
  have hpt : ∀ y : ℍ, bergK (g • I : ℍ) (g • y : ℍ) ^ (n + 2) *
      bergK (g • y : ℍ) (g • w' : ℍ) ^ (n + 2) =
      (autF g I * conj (autF g w')) ^ (n + 2) *
        (bergK Complex.I y ^ (n + 2) * bergK y w' ^ (n + 2)) := by
    intro y
    rw [bergK_smul, bergK_smul, ← mul_pow, ← mul_pow, ← mul_pow]
    congr 1
    have h := conj_autF_mul_self g y
    rw [coe_I] at *
    linear_combination (bergK Complex.I y * bergK y w' * autF g I * conj (autF g w')) * h
  simp_rw [hpt]
  rw [integral_const_mul, integral_bergK_I_pow, bergK_smul, coe_I]
  ring

/-! ### Finiteness of the kernel masses -/

theorem one_add_pairUIc_diskToUpper {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    1 + pairUIc (diskToUpper ζ) = (1 - Complex.normSq ζ)⁻¹ := by
  have hne := ne_one_of_norm_lt_one hζ
  have h1 : 1 - ζ ≠ 0 := sub_ne_zero.mpr hne.symm
  have hN : Complex.normSq (1 - ζ) ≠ 0 := (Complex.normSq_pos.mpr h1).ne'
  have hq : 1 - Complex.normSq ζ ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
  have hsub : diskToUpper ζ - Complex.I = 2 * Complex.I * ζ / (1 - ζ) := by
    rw [diskToUpper]; field_simp; ring
  have hre : (diskToUpper ζ).re ^ 2 + ((diskToUpper ζ).im - 1) ^ 2 =
      4 * Complex.normSq ζ / Complex.normSq (1 - ζ) := by
    have h := congrArg Complex.normSq hsub
    rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I,
      Complex.normSq_apply] at h
    simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, sub_zero] at h
    rw [← h]
    norm_num
    ring
  rw [pairUIc, hre, diskToUpper_im hne]
  field_simp
  ring

/-- `∫_ℍ (1 + u(z, y))^{−(n+2)} dμ(y) < ∞`. -/
theorem lintegral_one_add_pairU_pow_lt_top (n : ℕ) (z : ℍ) :
    ∫⁻ y : ℍ, ENNReal.ofReal (((1 + pairU z y) ^ (n + 2))⁻¹) < ∞ := by
  rw [lintegral_pairU_eq_I (fun u => ENNReal.ofReal (((1 + u) ^ (n + 2))⁻¹)) z]
  have hG : Measurable fun w : ℂ => ENNReal.ofReal (((1 + pairUIc w) ^ (n + 2))⁻¹) :=
    ((measurable_const.add measurable_pairUIc).pow_const _).inv.ennreal_ofReal
  simp_rw [← pairUIc_coe]
  rw [lintegral_upperHalfPlane_eq hG, lintegral_diskToUpper]
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_ball (g := fun _ => ENNReal.ofReal 4)
    fun ζ hζ => ?_) ?_
  · have hζ1 : ‖ζ‖ < 1 := by simpa using hζ
    have hq0 : 0 < 1 - Complex.normSq ζ := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ]
    have hq1 : 1 - Complex.normSq ζ ≤ 1 := by linarith [Complex.normSq_nonneg ζ]
    rw [one_add_pairUIc_diskToUpper hζ1, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_pow, inv_inv, show n + 2 = 2 + n by ring, pow_add, div_mul_eq_mul_div,
      mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero 2 hq0.ne')]
    nlinarith [pow_le_one₀ hq0.le hq1 (n := n), pow_nonneg hq0.le n]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
