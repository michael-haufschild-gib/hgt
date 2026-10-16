import GaloisForLFunctions.RHTower.CHMDSmallScalePacketPositivityFirstOrder
import GaloisForLFunctions.RHTower.CHMDKleinGordonInverseLightCone

/-!
# CHMD: The Universal Strip-Sector Law, Higher Moment Positivity, Second-Order Degenerate Toeplitz Packets, and Positive Volterra Reconstruction of the Prime Wave

Stage 19 (`CHMDSmallScalePacketPositivityFirstOrder`) proved that the whole Toeplitz hierarchy of the
causal wave `φ_Λ(y) = cosineShiftFn Λ sechHalf y` is unconditionally nonnegative at small scale on
every packet `(t, c)` with `Σ cᵢ ≠ 0` or `Σ cᵢ tᵢ ≠ 0`, isolating the second-order degenerate
packets (`Σ cᵢ = Σ cᵢ tᵢ = 0`) and the next zero-measure moment `M₂ = Σ_ρ m_ρ Re(ρ_ρ⁴ w_ρ)` as the
frontier obstacle. Meanwhile Stage 20 (`CHMDLightConePrimeKernelDecomposition`) decomposed
`chmdPrimeWave` as the forward light-cone transmutation `L[P₀]` of the strictly positive d'Alembert
prime wave `P₀(v) = Σ_n (Λ(n)/√n)(D(log n + v) + D(log n − v)) > 0`, where the oscillatory Bessel
tail obstructed direct sign control of the prime wave.

This module overcomes both obstacles unconditionally:

1. **The Universal Strip-Sector Inequality and Higher Klein–Gordon Moment Positivity (`M₂, M₃, M₄ > 0`)**:
   On the critical strip `|Im z| < 1/2`, the Klein–Gordon multiplier `z² + 2 = U + i V`
   (`U = a² − b² + 2`, `V = 2 a b`) satisfies the universal sector inequality
   $$7 V^2 < U^2 \qquad (\text{`seven_mul_im_sq_lt_re_sq`}),$$
   because `U > a² + 7/4`, `V² ≤ a²`, and `(a² + 7/4)² − 7 a² = (a² − 7/4)² ≥ 0`.
   Consequently `(z² + 2)^m` has strictly positive real part and imaginary part positively aligned
   with `Im(cosh²(z/2)) = sinh(Re z) sin(Im z) / 2` across the entire critical strip for
   `m = 2, 3, 4` (`re_quarticDensity_pos`, `re_sexticDensity_pos`, `re_octicDensity_pos`). Every
   nontrivial zero `ρ` therefore contributes strictly positive fourth, sixth, and eighth moments
   `Re(ρ_ρ^{2m} w_ρ) > 0` (`m = 2, 3, 4`).
2. **All-Order Good Density, the Quartic Moment `M₂`, and the Quartic Explicit-Formula Inequality**:
   For every `m : ℕ`, `(z² + 2)^m sech²(z/2)` is a `GoodDensity`
   (`goodDensity_sq_add_two_pow_mul_specSq_sechHalf`), so all even frequency moments
   `Σ_ρ m_ρ ‖w_ρ‖ ‖ρ_ρ‖^{2m}` converge (`summable_kgFreq_even_pow`). The quartic moment
   `M₂ = kgQuarticMoment = Σ_ρ m_ρ Re(ρ_ρ⁴ w_ρ)` is unconditionally nonnegative, strictly positive
   whenever a zero exists, and equals `evenWeilDensity Λ (specSq quarticTest)`, yielding the
   unconditional quartic prime inequality `prime_quartic_le_pole_add_arch`.
3. **Fourth-Order Cosine Expansion and Small-Scale Positivity of Second-Order Degenerate & 3-Point Packets**:
   Using `cos x = 1 − 2 sin²(x/2)` and `Complex.sin_bound`, we establish the uniform fourth-order
   mode bound (`re_mul_cos_sub_one_quartic_expansion`) for all `|Im x| ≤ 1/4`:
   $$\Bigl|\operatorname{Re}\bigl(w(\cos x - 1)\bigr) -
     \Bigl(-\frac{1}{2}\operatorname{Re}(w x^2) + \frac{1}{24}\operatorname{Re}(w x^4)\Bigr)\Bigr|
     \le 4\,\|w\|\,\|x\|^6.$$
   Combined with the exact fourth-difference identity
   $$\sum_{i,j} c_i c_j (t_j - t_i)^4 =
     2\Bigl(\sum_i c_i\Bigr)\Bigl(\sum_i c_i t_i^4\Bigr)
     - 8\Bigl(\sum_i c_i t_i\Bigr)\Bigl(\sum_i c_i t_i^3\Bigr)
     + 6\Bigl(\sum_i c_i t_i^2\Bigr)^2,$$
   every second-order degenerate packet (`Σ cᵢ = Σ cᵢ tᵢ = 0`) satisfies
   $$T(\lambda) \ge \frac{1}{4}\lambda^4 \Bigl(\sum_i c_i t_i^2\Bigr)^2 M_2
     - 4\lambda^6 D_6 Q_6 \qquad (\text{`scaledForm_ge_of_second_order_degenerate`}).$$
   Hence every packet with `Σ cᵢ ≠ 0 ∨ Σ cᵢ tᵢ ≠ 0 ∨ Σ cᵢ tᵢ² ≠ 0` is unconditionally nonnegative at
   small scale (`exists_scaledForm_nonneg_of_up_to_second_moment`), and by the `3 × 3` Vandermonde
   identity every 3-point Toeplitz packet on `Fin 3` with injective sample points is unconditionally
   nonnegative at small scale (`exists_scaledForm_nonneg_fin_three`).
4. **Positive Volterra Inverse Light-Cone Reconstruction of the Prime Wave**:
   On the real axis, the inverse light-cone transmutation
   $$L^{-1}[A](y) = A(y) + \frac{y^2}{2} \int_{-1}^1 B\bigl(-2 y^2 (1 - t^2)\bigr) A(y t)\,dt$$
   has strictly positive kernel `B(−2 y² (1 − t²)) ≥ 1 > 0` (`one_le_lightConeBesselReal_of_nonpos`).
   Integrating the real inverse light-cone identity against `sech²(r/2) g(r)` reconstructs the
   strictly positive massless d'Alembert prime wave directly from `chmdPrimeWave`:
   $$L^{-1}[\operatorname{chmdPrimeWave}](y) = \operatorname{masslessPrimeWave}(y) > 0
     \qquad (\text{`inverseLightConeTransmute_chmdPrimeWave`}),$$
   yields the unconditional global Volterra upper bound on the causal wave for all `y : ℝ`:
   $$L^{-1}[\varphi_\Lambda](y) < \frac{2}{\cos^2(1/4)} \cosh(y/2)
     + \frac{1}{2\pi} \operatorname{masslessArchWave}(y)
     \qquad (\text{`inverseLightConeTransmute_chmdWave_lt`}),$$
   and forces quantitative positivity of `chmdPrimeWave` on every interval `[−|y|, |y|]`
   (`masslessPrimeWave_le_of_chmdPrimeWave_le_on_Icc`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators Real ComplexConjugate

noncomputable section

namespace RHTower.CHMDQuarticMoment

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage11 RHTower.CHMDStage13 RHTower.CHMDStage15 RHTower.CHMDStage22
open RHTower.CHMDGrowthCollapse RHTower.CHMDEnergyPositivity RHTower.CHMDSmallScale
open RHTower.CHMDLightCone

/-! ## Section 1: The Universal Strip-Sector Law and Higher Klein–Gordon Densities -/

theorem re_sq_add_two_gt {z : ℂ} (hz : |z.im| < 1 / 2) :
    z.re ^ 2 + 7 / 4 < (z ^ 2 + 2).re := by
  rw [re_sq_add_two]
  have hb := abs_lt.mp hz
  have hb2 : z.im ^ 2 < 1 / 4 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
  linarith

theorem im_sq_add_two_eq (z : ℂ) : (z ^ 2 + 2).im = 2 * z.re * z.im := by
  simp [sq]; ring

/-- **The Universal Strip-Sector Inequality**: on `|Im z| < 1/2`, the Klein–Gordon multiplier
`z² + 2` satisfies `7 (Im(z² + 2))² < (Re(z² + 2))²`. -/
theorem seven_mul_im_sq_lt_re_sq {z : ℂ} (hz : |z.im| < 1 / 2) :
    7 * (z ^ 2 + 2).im ^ 2 < (z ^ 2 + 2).re ^ 2 := by
  have hU : z.re ^ 2 + 7 / 4 < (z ^ 2 + 2).re := re_sq_add_two_gt hz
  have hb := abs_lt.mp hz
  have hb2 : z.im ^ 2 < 1 / 4 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
  have hV : (z ^ 2 + 2).im ^ 2 ≤ z.re ^ 2 := by
    rw [im_sq_add_two_eq]
    nlinarith [sq_nonneg z.re]
  have hU0 : 0 < z.re ^ 2 + 7 / 4 := by positivity
  have hU2 : (z.re ^ 2 + 7 / 4) ^ 2 < (z ^ 2 + 2).re ^ 2 := by
    nlinarith [sq_nonneg z.re]
  have hsec : 7 * z.re ^ 2 ≤ (z.re ^ 2 + 7 / 4) ^ 2 := by
    nlinarith [sq_nonneg (z.re ^ 2 - 7 / 4)]
  linarith

/-- General strip-positivity criterion against `specSq sechHalf`: any complex multiplier `w` with
`Re w > 0` and `Im w = c · Re z · Im z` (`c ≥ 0`) has `Re(w · sech²(z/2)) > 0` on `|Im z| < 1/2`. -/
theorem re_mul_specSq_sechHalf_pos_of_re_pos_of_im {z w : ℂ} (hz : |z.im| < 1 / 2)
    (hwre : 0 < w.re) {c : ℝ} (hc : 0 ≤ c) (hwim : w.im = c * (z.re * z.im)) :
    0 < (w * specSq sechHalf z).re := by
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.inv_def, ← mul_assoc, Complex.re_mul_ofReal]
  have hne : Complex.cosh (z / 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (cosh_half_ne_zero (by linarith))
  have hpos : 0 < (Complex.normSq (Complex.cosh (z / 2) ^ 2))⁻¹ :=
    inv_pos.mpr (Complex.normSq_pos.mpr hne)
  refine mul_pos ?_ hpos
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, re_cosh_half_sq, im_cosh_half_sq, hwim]
  have hb := abs_lt.mp hz
  have hcos : 0 < Real.cos z.im := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_gt_three]
  have hcos2 : 0 < Real.cos (z.im / 2) ^ 2 := by
    have : 0 < Real.cos (z.im / 2) := by
      apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_gt_three]
    positivity
  have hB : 0 < Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * Real.cos z.im := by
    have := mul_nonneg (sq_nonneg (Real.sinh (z.re / 2))) hcos.le
    linarith
  have hC : 0 ≤ (z.re * Real.sinh z.re) * (z.im * Real.sin z.im) :=
    mul_nonneg (self_mul_sinh_nonneg _) (self_mul_sin_nonneg hz)
  have hC' : 0 ≤ c * (z.re * z.im) * (Real.sinh z.re * Real.sin z.im / 2) := by
    rw [show c * (z.re * z.im) * (Real.sinh z.re * Real.sin z.im / 2) =
      (c / 2) * ((z.re * Real.sinh z.re) * (z.im * Real.sin z.im)) by ring]
    exact mul_nonneg (by positivity) hC
  nlinarith [mul_pos hwre hB]

/-- **Quartic Klein–Gordon density positivity on the strip (`m = 2`)**:
`Re((z² + 2)² sech²(z/2)) > 0` for `|Im z| < 1/2`. -/
theorem re_quarticDensity_pos {z : ℂ} (hz : |z.im| < 1 / 2) :
    0 < ((z ^ 2 + 2) ^ 2 * specSq sechHalf z).re := by
  set u := z ^ 2 + 2 with hu
  have hU : 0 < u.re := by linarith [re_sq_add_two_gt hz, sq_nonneg z.re]
  have hsec := seven_mul_im_sq_lt_re_sq hz
  have hre : (u ^ 2).re = u.re ^ 2 - u.im ^ 2 := by simp [sq]
  have him : (u ^ 2).im = (4 * u.re) * (z.re * z.im) := by
    have : (u ^ 2).im = 2 * u.re * u.im := by simp [sq]; ring
    rw [this, hu, im_sq_add_two_eq]; ring
  refine re_mul_specSq_sechHalf_pos_of_re_pos_of_im hz ?_ (by positivity) him
  rw [hre]
  nlinarith [sq_nonneg u.im]

/-- **Sextic Klein–Gordon density positivity on the strip (`m = 3`)**:
`Re((z² + 2)³ sech²(z/2)) > 0` for `|Im z| < 1/2`. -/
theorem re_sexticDensity_pos {z : ℂ} (hz : |z.im| < 1 / 2) :
    0 < ((z ^ 2 + 2) ^ 3 * specSq sechHalf z).re := by
  set u := z ^ 2 + 2 with hu
  have hU : 0 < u.re := by linarith [re_sq_add_two_gt hz, sq_nonneg z.re]
  have hsec := seven_mul_im_sq_lt_re_sq hz
  have hre : (u ^ 3).re = u.re * (u.re ^ 2 - 3 * u.im ^ 2) := by
    simp [pow_three]; ring
  have him : (u ^ 3).im = (2 * (3 * u.re ^ 2 - u.im ^ 2)) * (z.re * z.im) := by
    have : (u ^ 3).im = u.im * (3 * u.re ^ 2 - u.im ^ 2) := by simp [pow_three]; ring
    rw [this, hu, im_sq_add_two_eq]; ring
  have hpos1 : 0 < u.re ^ 2 - 3 * u.im ^ 2 := by nlinarith [sq_nonneg u.im]
  have hpos2 : 0 ≤ 2 * (3 * u.re ^ 2 - u.im ^ 2) := by nlinarith [sq_nonneg u.im]
  refine re_mul_specSq_sechHalf_pos_of_re_pos_of_im hz ?_ hpos2 him
  rw [hre]
  exact mul_pos hU hpos1

/-- **Octic Klein–Gordon density positivity on the strip (`m = 4`)**:
`Re((z² + 2)⁴ sech²(z/2)) > 0` for `|Im z| < 1/2`. -/
theorem re_octicDensity_pos {z : ℂ} (hz : |z.im| < 1 / 2) :
    0 < ((z ^ 2 + 2) ^ 4 * specSq sechHalf z).re := by
  set u := z ^ 2 + 2 with hu
  have hU : 0 < u.re := by linarith [re_sq_add_two_gt hz, sq_nonneg z.re]
  have hsec := seven_mul_im_sq_lt_re_sq hz
  have hre : (u ^ 4).re = u.re ^ 2 * (u.re ^ 2 - 6 * u.im ^ 2) + u.im ^ 4 := by
    have : u ^ 4 = (u ^ 2) * (u ^ 2) := by ring
    rw [this]; simp [sq]; ring
  have him : (u ^ 4).im = (8 * u.re * (u.re ^ 2 - u.im ^ 2)) * (z.re * z.im) := by
    have h1 : u ^ 4 = (u ^ 2) * (u ^ 2) := by ring
    have h2 : (u ^ 4).im = 4 * u.re * u.im * (u.re ^ 2 - u.im ^ 2) := by
      rw [h1]; simp [sq]; ring
    rw [h2, hu, im_sq_add_two_eq]; ring
  have hpos1 : 0 < u.re ^ 2 - 6 * u.im ^ 2 := by nlinarith [sq_nonneg u.im]
  have hpos2 : 0 ≤ 8 * u.re * (u.re ^ 2 - u.im ^ 2) := by
    have : 0 < u.re ^ 2 - u.im ^ 2 := by nlinarith [sq_nonneg u.im]
    positivity
  refine re_mul_specSq_sechHalf_pos_of_re_pos_of_im hz ?_ hpos2 him
  rw [hre]
  have : 0 < u.re ^ 2 * (u.re ^ 2 - 6 * u.im ^ 2) := mul_pos (by positivity) hpos1
  have : 0 ≤ u.im ^ 4 := by positivity
  linarith

theorem kgFreq_pow_even (ρ : zetaZeroConfig.carrier) (m : ℕ) :
    kgFreq ρ ^ (2 * m) = (Zeta23.gammaOf (ρ : ℂ) ^ 2 + 2) ^ m := by
  rw [pow_mul, kgFreq_sq]

/-- Every nontrivial zero has strictly positive quartic Klein–Gordon term `Re(ρ_ρ⁴ w_ρ) > 0`. -/
theorem re_kgFreq_pow_four_mul_kgWeight_pos (ρ : zetaZeroConfig.carrier) :
    0 < (kgFreq ρ ^ 4 * kgWeight ρ).re := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, kgFreq_pow_even]
  exact re_quarticDensity_pos (abs_im_gammaOf_lt ρ)

/-- Every nontrivial zero has strictly positive sextic Klein–Gordon term `Re(ρ_ρ⁶ w_ρ) > 0`. -/
theorem re_kgFreq_pow_six_mul_kgWeight_pos (ρ : zetaZeroConfig.carrier) :
    0 < (kgFreq ρ ^ 6 * kgWeight ρ).re := by
  rw [show (6 : ℕ) = 2 * 3 by rfl, kgFreq_pow_even]
  exact re_sexticDensity_pos (abs_im_gammaOf_lt ρ)

/-- Every nontrivial zero has strictly positive octic Klein–Gordon term `Re(ρ_ρ⁸ w_ρ) > 0`. -/
theorem re_kgFreq_pow_eight_mul_kgWeight_pos (ρ : zetaZeroConfig.carrier) :
    0 < (kgFreq ρ ^ 8 * kgWeight ρ).re := by
  rw [show (8 : ℕ) = 2 * 4 by rfl, kgFreq_pow_even]
  exact re_octicDensity_pos (abs_im_gammaOf_lt ρ)

/-! ## Section 2: All-Order Good Density, the Quartic Moment `M₂`, and the Quartic Prime Inequality -/

theorem norm_sq_add_two_pow_le (m : ℕ) {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    ‖(z ^ 2 + 2) ^ m‖ ≤ (|z.re| + 3) ^ (2 * m) := by
  rw [norm_pow, pow_mul]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ m
  have h1 : ‖z ^ 2 + 2‖ ≤ ‖z‖ ^ 2 + 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, show ‖(2 : ℂ)‖ = 2 by simp]
  have h2 : ‖z‖ ≤ |z.re| + 5 / 4 :=
    (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have h3 : ‖z‖ ^ 2 ≤ (|z.re| + 5 / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith [abs_nonneg z.re]

theorem pow_add_three_le_exp (m : ℕ) {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 ≤ t) :
    (t + 3) ^ (2 * m) ≤
      (((2 * m).factorial : ℝ) * Real.exp (3 * δ) / δ ^ (2 * m)) * Real.exp (δ * t) := by
  have h := Real.pow_div_factorial_le_exp (δ * (t + 3)) (by positivity) (2 * m)
  have hfac : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * m)
  have hδm : 0 < δ ^ (2 * m) := by positivity
  rw [div_le_iff₀ hfac, mul_pow] at h
  have hexp : Real.exp (δ * (t + 3)) = Real.exp (3 * δ) * Real.exp (δ * t) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at h
  calc (t + 3) ^ (2 * m) = δ ^ (2 * m) * (t + 3) ^ (2 * m) / δ ^ (2 * m) := by field_simp
    _ ≤ Real.exp (3 * δ) * Real.exp (δ * t) * ((2 * m).factorial : ℝ) / δ ^ (2 * m) := by gcongr
    _ = (((2 * m).factorial : ℝ) * Real.exp (3 * δ) / δ ^ (2 * m)) * Real.exp (δ * t) := by ring

/-- **All-order GoodDensity**: for every `m : ℕ`, `(z² + 2)^m sech²(z/2)` is a good spectral density. -/
theorem goodDensity_sq_add_two_pow_mul_specSq_sechHalf (m : ℕ) :
    GoodDensity (fun z : ℂ => (z ^ 2 + 2) ^ m * specSq sechHalf z) := by
  obtain ⟨ε, C, hε, hs⟩ := evenStrip_sechHalf.strip
  have hC := hs.const_nonneg (by norm_num)
  set δ : ℝ := ε / 2
  have hδ : 0 < δ := by positivity
  set K : ℝ := ((2 * m).factorial : ℝ) * Real.exp (3 * δ) / δ ^ (2 * m)
  have hK : 0 ≤ K := by positivity
  refine ⟨⟨3 * ε / 2, K * C ^ 2, by positivity, fun z hz => ?_, fun z hz => ?_⟩,
    fun z => ?_, fun r => ?_⟩
  · exact (((differentiableAt_id.pow 2).add (differentiableAt_const _)).pow m).mul
      (differentiableAt_specSq hs hz)
  · show ‖(z ^ 2 + 2) ^ m * specSq sechHalf z‖ ≤ K * C ^ 2 * Real.exp (-(3 * ε / 2 * |z.re|))
    rw [norm_mul]
    have h1 := norm_sq_add_two_pow_le m hz
    have h2 := norm_specSq_le hs hz
    have h3 := pow_add_three_le_exp m hδ (abs_nonneg z.re)
    have hexp : Real.exp (δ * |z.re|) * Real.exp (-(2 * ε * |z.re|)) =
        Real.exp (-(3 * ε / 2 * |z.re|)) := by
      rw [← Real.exp_add]; congr 1; unfold δ; ring
    calc ‖(z ^ 2 + 2) ^ m‖ * ‖specSq sechHalf z‖
        ≤ (|z.re| + 3) ^ (2 * m) * (C ^ 2 * Real.exp (-(2 * ε * |z.re|))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ (K * Real.exp (δ * |z.re|)) * (C ^ 2 * Real.exp (-(2 * ε * |z.re|))) := by gcongr
      _ = K * C ^ 2 * Real.exp (-(3 * ε / 2 * |z.re|)) := by rw [← hexp]; ring
  · show ((-z) ^ 2 + 2) ^ m * specSq sechHalf (-z) = (z ^ 2 + 2) ^ m * specSq sechHalf z
    rw [neg_sq, specSq_neg_of_even evenStrip_sechHalf.even]
  · show (((r : ℂ) ^ 2 + 2) ^ m * specSq sechHalf r).im = 0
    rw [show ((r : ℂ) ^ 2 + 2) ^ m = (((r ^ 2 + 2) ^ m : ℝ) : ℂ) by push_cast; ring,
      Complex.im_ofReal_mul, specSq_im_ofReal, mul_zero]

/-- All even frequency moments `Σ_ρ m_ρ ‖w_ρ‖ ‖ρ_ρ‖^{2m}` of the zero measure are finite. -/
theorem summable_kgFreq_even_pow (m : ℕ) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ (2 * m)) := by
  have h := summable_zeroSide_of_goodDensity (goodDensity_sq_add_two_pow_mul_specSq_sechHalf m)
  have h2 := summable_norm_iff.mpr h
  refine h2.congr fun ρ => ?_
  show ‖(zetaZeroConfig.mult ρ : ℂ) *
      ((Zeta23.gammaOf (ρ : ℂ) ^ 2 + 2) ^ m * specSq sechHalf (Zeta23.gammaOf (ρ : ℂ)))‖ = _
  rw [norm_mul, Complex.norm_natCast, norm_mul, ← kgFreq_pow_even, norm_pow]
  unfold CHMDGrowthCollapse.kgWeight
  ring

/-- The sextic mass `Σ_ρ m_ρ ‖w_ρ‖ ‖ρ_ρ‖⁶` is finite. -/
theorem summable_sextic :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 6) :=
  summable_kgFreq_even_pow 3

/-- The sextic mass `Q₆ = Σ_ρ m_ρ ‖w_ρ‖ ‖ρ_ρ‖⁶` of the zero measure. -/
def kgSexticMass : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 6)

theorem kgSexticMass_nonneg : 0 ≤ kgSexticMass :=
  tsum_nonneg fun _ => by positivity

/-- The quartic Klein–Gordon term `m_ρ Re(ρ_ρ⁴ w_ρ)` of a nontrivial zero. -/
def kgQuarticTerm (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) * (kgFreq ρ ^ 4 * kgWeight ρ).re

theorem kgQuarticTerm_pos (ρ : zetaZeroConfig.carrier) : 0 < kgQuarticTerm ρ := by
  unfold kgQuarticTerm
  have h1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ ρ.2
  exact mul_pos (by linarith) (re_kgFreq_pow_four_mul_kgWeight_pos ρ)

theorem kgQuarticTerm_le (ρ : zetaZeroConfig.carrier) :
    kgQuarticTerm ρ ≤ (zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4) := by
  unfold kgQuarticTerm
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ hm
  calc (kgFreq ρ ^ 4 * kgWeight ρ).re ≤ ‖kgFreq ρ ^ 4 * kgWeight ρ‖ := Complex.re_le_norm _
    _ = ‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4 := by rw [norm_mul, norm_pow, mul_comm]

theorem summable_kgQuarticTerm : Summable kgQuarticTerm :=
  Summable.of_nonneg_of_le (fun ρ => (kgQuarticTerm_pos ρ).le) kgQuarticTerm_le summable_quartic

/-- **The quartic Klein–Gordon moment** `M₂ = Σ_ρ m_ρ Re(ρ_ρ⁴ w_ρ)` of the zero measure. -/
def kgQuarticMoment : ℝ := ∑' ρ : zetaZeroConfig.carrier, kgQuarticTerm ρ

theorem kgQuarticMoment_nonneg : 0 ≤ kgQuarticMoment :=
  tsum_nonneg fun ρ => (kgQuarticTerm_pos ρ).le

theorem kgQuarticMoment_pos [Nonempty zetaZeroConfig.carrier] : 0 < kgQuarticMoment := by
  let ρ₀ : zetaZeroConfig.carrier := Classical.arbitrary _
  have h := summable_kgQuarticTerm.le_tsum ρ₀ (fun ρ _ => (kgQuarticTerm_pos ρ).le)
  exact (kgQuarticTerm_pos ρ₀).trans_le h

/-- The quartic test function `(z² + 2) sech(z/2)`. -/
def quarticTest (z : ℂ) : ℂ := (z ^ 2 + 2) * sechHalf z

theorem evenStrip_quarticTest : EvenStrip quarticTest := by
  obtain ⟨ε, C, hε, hs⟩ := evenStrip_sechHalf.strip
  have hC := hs.const_nonneg (by norm_num)
  set δ : ℝ := ε / 2
  have hδ : 0 < δ := by positivity
  set K : ℝ := ((2 * 1).factorial : ℝ) * Real.exp (3 * δ) / δ ^ (2 * 1)
  refine ⟨⟨ε / 2, K * C, by positivity, fun z hz => ?_, fun z hz => ?_⟩,
    fun z => ?_, fun r => ?_⟩
  · exact ((differentiableAt_id.pow 2).add (differentiableAt_const _)).mul (hs.diff z hz)
  · unfold quarticTest
    rw [norm_mul]
    have h1 : ‖z ^ 2 + 2‖ ≤ (|z.re| + 3) ^ (2 * 1) := by
      simpa using norm_sq_add_two_pow_le 1 hz
    have h2 := hs.bound z hz
    have h3 := pow_add_three_le_exp 1 hδ (abs_nonneg z.re)
    have hexp : Real.exp (δ * |z.re|) * Real.exp (-(ε * |z.re|)) =
        Real.exp (-(ε / 2 * |z.re|)) := by
      rw [← Real.exp_add]; congr 1; unfold δ; ring
    calc ‖z ^ 2 + 2‖ * ‖sechHalf z‖
        ≤ (|z.re| + 3) ^ (2 * 1) * (C * Real.exp (-(ε * |z.re|))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ (K * Real.exp (δ * |z.re|)) * (C * Real.exp (-(ε * |z.re|))) := by gcongr
      _ = K * C * Real.exp (-(ε / 2 * |z.re|)) := by rw [← hexp]; ring
  · unfold quarticTest; rw [neg_sq, evenStrip_sechHalf.even]
  · unfold quarticTest
    rw [show ((r : ℂ) ^ 2 + 2) = ((r ^ 2 + 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.im_ofReal_mul, evenStrip_sechHalf.real, mul_zero]

theorem specSq_quarticTest (z : ℂ) :
    specSq quarticTest z = (z ^ 2 + 2) ^ 2 * specSq sechHalf z := by
  unfold specSq quarticTest
  rw [map_mul, map_add, map_pow, Complex.conj_conj, map_ofNat]
  ring

/-- **The quartic moment `M₂` is the even Weil functional of `(z² + 2)² sech²(z/2)`.** -/
theorem kgQuarticMoment_eq_evenWeilDensity :
    kgQuarticMoment =
      evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq quarticTest) := by
  rw [evenWeilDensity_specSq_vonMangoldt_eq_tsum_re evenStrip_quarticTest]
  unfold kgQuarticMoment kgQuarticTerm
  refine tsum_congr fun ρ => ?_
  rw [specSq_quarticTest, ← kgFreq_pow_even ρ 2]
  rfl

/-- **The quartic explicit-formula prime inequality**, unconditional:
`Σ_{n ≥ 2} (Λ(n)/√n) (1/π) ∫ (r² + 2)² sech²(r/2) cos(r log n) dr ≤ 49/(8 cos²(1/4)) + (1/2π) ∫ (r² + 2)² sech²(r/2) γ(r) dr`. -/
theorem prime_quartic_le_pole_add_arch :
    (∑' n : ℕ,
      (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
        (1 / Real.pi * ∫ r : ℝ, ((r ^ 2 + 2) ^ 2 * sechSqHalf r) * Real.cos (r * Real.log n))) ≤
      49 / (8 * Real.cos (1 / 4 : ℝ) ^ 2) +
        1 / (2 * Real.pi) * (∫ r : ℝ, ((r ^ 2 + 2) ^ 2 * sechSqHalf r) * EF.gammaBracket r) := by
  have h0 : 0 ≤ evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (specSq quarticTest) := by
    rw [← kgQuarticMoment_eq_evenWeilDensity]; exact kgQuarticMoment_nonneg
  have hreal : ∀ r : ℝ, (specSq quarticTest r).re = (r ^ 2 + 2) ^ 2 * sechSqHalf r := by
    intro r
    rw [specSq_quarticTest,
      show (((r : ℂ) ^ 2 + 2) ^ 2) = (((r ^ 2 + 2) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, specSq_sechHalf_ofReal_re]
  have hpole : (specSq quarticTest (I / 2) + specSq quarticTest (-I / 2)).re =
      49 / (8 * Real.cos (1 / 4 : ℝ) ^ 2) := by
    rw [specSq_quarticTest, specSq_quarticTest,
      show ((I / 2 : ℂ) ^ 2 + 2) ^ 2 = ((49 / 16 : ℝ) : ℂ) by
        rw [div_pow, Complex.I_sq]; push_cast; ring,
      show ((-I / 2 : ℂ) ^ 2 + 2) ^ 2 = ((49 / 16 : ℝ) : ℂ) by
        rw [div_pow, neg_sq, Complex.I_sq]; push_cast; ring,
      ← mul_add, Complex.re_ofReal_mul]
    have := evenPolePart_specSq_sechHalf
    unfold evenPolePart at this
    rw [this]
    field_simp
    ring
  unfold evenWeilDensity at h0
  rw [hpole] at h0
  simp_rw [hreal] at h0
  linarith

/-! ## Section 3: Fourth-Order Cosine Expansion and Second-Order Degenerate Toeplitz Packets -/

/-- Fourth-order complex cosine bound: `‖cos x − (1 − x²/2 + x⁴/24)‖ ≤ ‖x‖⁶` for `‖x‖ ≤ 1`. -/
theorem cos_fourth_order_bound {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖Complex.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)‖ ≤ ‖x‖ ^ 6 := by
  set u : ℂ := x / 2 with hu
  set R : ℂ := Complex.sin u - (u - u ^ 3 / 6) with hR
  have hu_norm : ‖u‖ = ‖x‖ / 2 := by
    rw [hu, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hu1 : ‖u‖ ≤ 1 := by linarith [norm_nonneg x]
  have hR_bound : ‖R‖ ≤ ‖u‖ ^ 5 := by
    refine (Complex.sin_bound hu1).trans ?_
    have : 0 ≤ ‖u‖ ^ 5 := by positivity
    linarith
  have hid : Complex.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24) =
      -(u ^ 6 / 18 + 4 * u * R - 2 / 3 * u ^ 3 * R + 2 * R ^ 2) := by
    have hx2u : x = 2 * u := by rw [hu]; ring
    have hsin : Complex.sin u = u - u ^ 3 / 6 + R := by rw [hR]; ring
    rw [hx2u, Complex.cos_two_mul_eq_one_sub, hsin]
    ring
  rw [hid, norm_neg]
  have h1 : ‖u ^ 6 / 18 + 4 * u * R - 2 / 3 * u ^ 3 * R + 2 * R ^ 2‖ ≤
      ‖u ^ 6 / 18‖ + ‖4 * u * R‖ + ‖2 / 3 * u ^ 3 * R‖ + ‖2 * R ^ 2‖ := by
    calc ‖u ^ 6 / 18 + 4 * u * R - 2 / 3 * u ^ 3 * R + 2 * R ^ 2‖
        ≤ ‖u ^ 6 / 18 + 4 * u * R - 2 / 3 * u ^ 3 * R‖ + ‖2 * R ^ 2‖ := norm_add_le _ _
      _ ≤ ‖u ^ 6 / 18 + 4 * u * R‖ + ‖2 / 3 * u ^ 3 * R‖ + ‖2 * R ^ 2‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ‖u ^ 6 / 18‖ + ‖4 * u * R‖ + ‖2 / 3 * u ^ 3 * R‖ + ‖2 * R ^ 2‖ := by
          gcongr; exact norm_add_le _ _
  have hA : ‖u ^ 6 / 18‖ = ‖u‖ ^ 6 / 18 := by
    rw [norm_div, norm_pow, show ‖(18 : ℂ)‖ = 18 by norm_num]
  have hB : ‖4 * u * R‖ ≤ 4 * ‖u‖ ^ 6 := by
    rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    calc 4 * ‖u‖ * ‖R‖ ≤ 4 * ‖u‖ * ‖u‖ ^ 5 :=
          mul_le_mul_of_nonneg_left hR_bound (by positivity)
      _ = 4 * ‖u‖ ^ 6 := by ring
  have hu3 : ‖u‖ ^ 3 ≤ ‖u‖ := by
    nlinarith [norm_nonneg u, sq_nonneg ‖u‖, mul_nonneg (norm_nonneg u) (sub_nonneg.mpr hu1)]
  have hC : ‖2 / 3 * u ^ 3 * R‖ ≤ 2 / 3 * ‖u‖ ^ 6 := by
    rw [norm_mul, norm_mul, norm_div, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num,
      show ‖(3 : ℂ)‖ = 3 by norm_num]
    calc 2 / 3 * ‖u‖ ^ 3 * ‖R‖ ≤ 2 / 3 * ‖u‖ * ‖u‖ ^ 5 := by
          refine mul_le_mul ?_ hR_bound (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hu3 (by norm_num)
      _ = 2 / 3 * ‖u‖ ^ 6 := by ring
  have hR1 : ‖R‖ ≤ ‖u‖ := by
    refine hR_bound.trans ?_
    have h2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
    have h4 : ‖u‖ ^ 4 ≤ 1 := by nlinarith [sq_nonneg (‖u‖ ^ 2)]
    calc ‖u‖ ^ 5 = ‖u‖ * ‖u‖ ^ 4 := by ring
      _ ≤ ‖u‖ * 1 := mul_le_mul_of_nonneg_left h4 (norm_nonneg u)
      _ = ‖u‖ := mul_one _
  have hD : ‖2 * R ^ 2‖ ≤ 2 * ‖u‖ ^ 6 := by
    rw [norm_mul, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num, sq ‖R‖]
    calc 2 * (‖R‖ * ‖R‖) ≤ 2 * (‖u‖ * ‖u‖ ^ 5) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hR1 hR_bound (norm_nonneg _) (norm_nonneg _))
            (by norm_num)
      _ = 2 * ‖u‖ ^ 6 := by ring
  have hu6 : ‖u‖ ^ 6 = ‖x‖ ^ 6 / 64 := by rw [hu_norm, div_pow]; norm_num
  have hx6 : 0 ≤ ‖x‖ ^ 6 := by positivity
  linarith

/-- **Uniform fourth-order expansion of one cosine mode**: for every weight `w` and every `x` with
`|Im x| ≤ 1/4`,
`|Re(w(cos x − 1)) − (−Re(w x²)/2 + Re(w x⁴)/24)| ≤ 4 ‖w‖ ‖x‖⁶`. -/
theorem re_mul_cos_sub_one_quartic_expansion (w x : ℂ) (hx : |x.im| ≤ 1 / 4) :
    |(w * (Complex.cos x - 1)).re - (-(w * x ^ 2).re / 2 + (w * x ^ 4).re / 24)| ≤
      4 * ‖w‖ * ‖x‖ ^ 6 := by
  have hw : 0 ≤ ‖w‖ := norm_nonneg _
  have hx6 : 0 ≤ ‖x‖ ^ 6 := by positivity
  rcases le_or_gt ‖x‖ 1 with h1 | h1
  · have hcb := cos_fourth_order_bound h1
    have e : (w * (Complex.cos x - 1)).re - (-(w * x ^ 2).re / 2 + (w * x ^ 4).re / 24) =
        (w * (Complex.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24))).re := by
      have h : w * (Complex.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)) =
          w * (Complex.cos x - 1) + ((1 / 2 : ℝ) : ℂ) * (w * x ^ 2) -
            ((1 / 24 : ℝ) : ℂ) * (w * x ^ 4) := by push_cast; ring
      rw [h, Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
      ring
    rw [e]
    calc |(w * (Complex.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24))).re|
        ≤ ‖w * (Complex.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24))‖ := Complex.abs_re_le_norm _
      _ = ‖w‖ * ‖Complex.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)‖ := norm_mul _ _
      _ ≤ ‖w‖ * ‖x‖ ^ 6 := mul_le_mul_of_nonneg_left hcb hw
      _ ≤ 4 * ‖w‖ * ‖x‖ ^ 6 := by linarith [mul_nonneg hw hx6]
  · have hcos : ‖Complex.cos x‖ ≤ 2 := by
      refine (norm_ccos_le_exp_abs_im _).trans ?_
      calc Real.exp |x.im| ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr hx
        _ ≤ 2 := by
          have := Real.exp_one_lt_d9
          have h2 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          nlinarith [Real.exp_pos (1 / 4), sq_nonneg (Real.exp (1 / 4)),
            sq_nonneg (Real.exp (1 / 4) ^ 2 - 2)]
    have hA : |(w * (Complex.cos x - 1)).re| ≤ 3 * ‖w‖ := by
      calc |(w * (Complex.cos x - 1)).re| ≤ ‖w * (Complex.cos x - 1)‖ := Complex.abs_re_le_norm _
        _ = ‖w‖ * ‖Complex.cos x - 1‖ := norm_mul _ _
        _ ≤ ‖w‖ * 3 := by
            apply mul_le_mul_of_nonneg_left _ hw
            calc ‖Complex.cos x - 1‖ ≤ ‖Complex.cos x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ ≤ 2 + 1 := by rw [norm_one]; linarith
              _ = 3 := by norm_num
        _ = 3 * ‖w‖ := by ring
    have hB : |(w * x ^ 2).re / 2| ≤ ‖w‖ * ‖x‖ ^ 2 / 2 := by
      rw [abs_div, abs_two]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc |(w * x ^ 2).re| ≤ ‖w * x ^ 2‖ := Complex.abs_re_le_norm _
        _ = ‖w‖ * ‖x‖ ^ 2 := by rw [norm_mul, norm_pow]
    have hC : |(w * x ^ 4).re / 24| ≤ ‖w‖ * ‖x‖ ^ 4 / 24 := by
      rw [abs_div, show |(24 : ℝ)| = 24 by norm_num]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc |(w * x ^ 4).re| ≤ ‖w * x ^ 4‖ := Complex.abs_re_le_norm _
        _ = ‖w‖ * ‖x‖ ^ 4 := by rw [norm_mul, norm_pow]
    have hx2_gt : 1 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    have hx4_le : ‖x‖ ^ 4 ≤ ‖x‖ ^ 6 := by
      calc ‖x‖ ^ 4 = ‖x‖ ^ 4 * 1 := by ring
        _ ≤ ‖x‖ ^ 4 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left hx2_gt (by positivity)
        _ = ‖x‖ ^ 6 := by ring
    have hx2_le : ‖x‖ ^ 2 ≤ ‖x‖ ^ 6 := by
      calc ‖x‖ ^ 2 = ‖x‖ ^ 2 * 1 * 1 := by ring
        _ ≤ ‖x‖ ^ 2 * ‖x‖ ^ 2 * ‖x‖ ^ 2 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hx2_gt (by positivity)) hx2_gt (by positivity)
              (by positivity)
        _ = ‖x‖ ^ 6 := by ring
    have hx1_le : 1 ≤ ‖x‖ ^ 6 := hx2_gt.trans hx2_le
    have htri : |(w * (Complex.cos x - 1)).re - (-(w * x ^ 2).re / 2 + (w * x ^ 4).re / 24)| ≤
        |(w * (Complex.cos x - 1)).re| + |(w * x ^ 2).re / 2| + |(w * x ^ 4).re / 24| := by
      calc |(w * (Complex.cos x - 1)).re - (-(w * x ^ 2).re / 2 + (w * x ^ 4).re / 24)|
          = |(w * (Complex.cos x - 1)).re + (w * x ^ 2).re / 2 - (w * x ^ 4).re / 24| := by ring_nf
        _ ≤ |(w * (Complex.cos x - 1)).re + (w * x ^ 2).re / 2| + |(w * x ^ 4).re / 24| :=
            abs_sub _ _
        _ ≤ |(w * (Complex.cos x - 1)).re| + |(w * x ^ 2).re / 2| + |(w * x ^ 4).re / 24| := by
            gcongr; exact abs_add_le _ _
    nlinarith [mul_le_mul_of_nonneg_left hx1_le hw, mul_le_mul_of_nonneg_left hx2_le hw,
      mul_le_mul_of_nonneg_left hx4_le hw]

/-- The sextic packet mass `Σ_{i,j} |cᵢ||cⱼ| (tⱼ − tᵢ)⁶`. -/
def packetSextic {N : ℕ} (t c : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, |c i| * |c j| * (t j - t i) ^ 6

theorem packetSextic_nonneg {N : ℕ} (t c : Fin N → ℝ) : 0 ≤ packetSextic t c :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- **The fourth-difference identity**:
`Σ cᵢcⱼ(tⱼ − tᵢ)⁴ = 2(Σ cᵢ)(Σ cᵢtᵢ⁴) − 8(Σ cᵢtᵢ)(Σ cᵢtᵢ³) + 6(Σ cᵢtᵢ²)²`. -/
theorem sum_sum_mul_pow_four_sub {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j * (t j - t i) ^ 4) =
      2 * (∑ i, c i) * (∑ i, c i * t i ^ 4) -
        8 * (∑ i, c i * t i) * (∑ i, c i * t i ^ 3) +
        6 * (∑ i, c i * t i ^ 2) ^ 2 := by
  have e : ∀ i j, c i * c j * (t j - t i) ^ 4 =
      c i * (c j * t j ^ 4) - (4 * (c i * t i)) * (c j * t j ^ 3) +
        (6 * (c i * t i ^ 2)) * (c j * t j ^ 2) -
        (4 * (c i * t i ^ 3)) * (c j * t j) + (c i * t i ^ 4) * c j := by
    intro i j; ring
  simp_rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    ← Finset.mul_sum]
  ring

theorem sum_sum_mul_pow_four_sub_of_degenerate {N : ℕ} (t c : Fin N → ℝ)
    (h0 : ∑ i, c i = 0) (h1 : ∑ i, c i * t i = 0) :
    (∑ i, ∑ j, c i * c j * (t j - t i) ^ 4) = 6 * (∑ i, c i * t i ^ 2) ^ 2 := by
  rw [sum_sum_mul_pow_four_sub, h0, h1]; ring

/-- **One-zero lower bound for a second-order degenerate packet** (`Σ cᵢ = Σ cᵢ tᵢ = 0`) at scale
`λ` with `λ · 2T ≤ 1/2`. -/
theorem packetMode_ge_of_second_order_degenerate {N : ℕ} (t c : Fin N → ℝ)
    (h0 : ∑ i, c i = 0) (h1 : ∑ i, c i * t i = 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (hT : lam * (2 * ∑ k, |t k|) ≤ 1 / 2) (ρ : zetaZeroConfig.carrier) :
    1 / 4 * lam ^ 4 * (∑ i, c i * t i ^ 2) ^ 2 * (kgFreq ρ ^ 4 * kgWeight ρ).re -
        4 * lam ^ 6 * packetSextic t c * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 6) ≤
      packetMode t c lam ρ := by
  set w := kgWeight ρ with hw
  set k := kgFreq ρ with hk
  have hmode : packetMode t c lam ρ =
      ∑ i, ∑ j, c i * c j * w.re +
        ∑ i, ∑ j, c i * c j * (w * (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * k) - 1)).re := by
    unfold packetMode
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_sub w, mul_one, Complex.sub_re, mul_comm (Complex.cos _) w]
    ring
  rw [hmode, sum_sum_mul_const_of_sum_eq_zero c h0, zero_add]
  have hsum : ∑ i, ∑ j, (c i * c j *
        (-(lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re) / 2 +
          lam ^ 4 * (t j - t i) ^ 4 * (k ^ 4 * w).re / 24) -
        |c i| * |c j| * (4 * ‖w‖ * (lam ^ 6 * (t j - t i) ^ 6 * ‖k‖ ^ 6))) ≤
      ∑ i, ∑ j, c i * c j * (w * (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * k) - 1)).re := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    set x : ℂ := ((lam * (t j - t i) : ℝ) : ℂ) * k with hx
    have hxim : |x.im| ≤ 1 / 4 := by
      rw [hx, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
        abs_mul, abs_of_nonneg hlam]
      have hsub := abs_sub_le_two_mul_sum_abs t i j
      have hkim : |k.im| ≤ 1 / 2 := by rw [hk]; exact (abs_im_kgFreq_lt ρ).le
      have h3 : lam * |t j - t i| ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left hsub hlam).trans hT
      calc lam * |t j - t i| * |k.im| ≤ 1 / 2 * (1 / 2) :=
            mul_le_mul h3 hkim (abs_nonneg _) (by norm_num)
        _ = 1 / 4 := by norm_num
    have hb := re_mul_cos_sub_one_quartic_expansion w x hxim
    have hx2 : (w * x ^ 2).re = lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re := by
      rw [hx, show (((lam * (t j - t i) : ℝ) : ℂ) * k) ^ 2 =
        (((lam ^ 2 * (t j - t i) ^ 2 : ℝ) : ℂ)) * k ^ 2 by push_cast; ring,
        mul_comm w, mul_assoc, Complex.re_ofReal_mul]
    have hx4 : (w * x ^ 4).re = lam ^ 4 * (t j - t i) ^ 4 * (k ^ 4 * w).re := by
      rw [hx, show (((lam * (t j - t i) : ℝ) : ℂ) * k) ^ 4 =
        (((lam ^ 4 * (t j - t i) ^ 4 : ℝ) : ℂ)) * k ^ 4 by push_cast; ring,
        mul_comm w, mul_assoc, Complex.re_ofReal_mul]
    have hxn : ‖x‖ ^ 6 = lam ^ 6 * (t j - t i) ^ 6 * ‖k‖ ^ 6 := by
      rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (lam * (t j - t i)) ^ 6)]
      ring
    rw [hx2, hx4, hxn] at hb
    have hcc : |c i * c j| = |c i| * |c j| := abs_mul _ _
    have h5 : |c i * c j * ((w * (Complex.cos x - 1)).re -
          (-(lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re) / 2 +
            lam ^ 4 * (t j - t i) ^ 4 * (k ^ 4 * w).re / 24))| ≤
        |c i| * |c j| * (4 * ‖w‖ * (lam ^ 6 * (t j - t i) ^ 6 * ‖k‖ ^ 6)) := by
      rw [abs_mul, hcc]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    have h6 := (abs_le.mp h5).1
    linarith
  have hlhs : ∑ i, ∑ j, (c i * c j *
        (-(lam ^ 2 * (t j - t i) ^ 2 * (k ^ 2 * w).re) / 2 +
          lam ^ 4 * (t j - t i) ^ 4 * (k ^ 4 * w).re / 24) -
        |c i| * |c j| * (4 * ‖w‖ * (lam ^ 6 * (t j - t i) ^ 6 * ‖k‖ ^ 6))) =
      -(lam ^ 2 * (k ^ 2 * w).re / 2) * (∑ i, ∑ j, c i * c j * (t j - t i) ^ 2) +
        lam ^ 4 * (k ^ 4 * w).re / 24 * (∑ i, ∑ j, c i * c j * (t j - t i) ^ 4) -
        4 * lam ^ 6 * packetSextic t c * (‖w‖ * ‖k‖ ^ 6) := by
    unfold packetSextic
    simp_rw [Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
  rw [hlhs, sum_sum_mul_sq_sub_of_sum_eq_zero t c h0, h1,
    sum_sum_mul_pow_four_sub_of_degenerate t c h0 h1] at hsum
  linarith

/-- **Second-order expansion of a second-order degenerate Toeplitz packet**: if `Σ cᵢ = 0` and
`Σ cᵢ tᵢ = 0` and `λ · 2T ≤ 1/2`, then
`T(λ) ≥ (1/4) λ⁴ (Σ cᵢ tᵢ²)² M₂ − 4 λ⁶ D₆ Q₆`. -/
theorem scaledForm_ge_of_second_order_degenerate {N : ℕ} (t c : Fin N → ℝ)
    (h0 : ∑ i, c i = 0) (h1 : ∑ i, c i * t i = 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (hT : lam * (2 * ∑ k, |t k|) ≤ 1 / 2) :
    1 / 4 * lam ^ 4 * (∑ i, c i * t i ^ 2) ^ 2 * kgQuarticMoment -
        4 * lam ^ 6 * packetSextic t c * kgSexticMass ≤ scaledForm t c lam := by
  rw [scaledForm_eq_tsum]
  have hA : Summable fun ρ : zetaZeroConfig.carrier =>
      1 / 4 * lam ^ 4 * (∑ i, c i * t i ^ 2) ^ 2 * kgQuarticTerm ρ :=
    summable_kgQuarticTerm.mul_left _
  have hB : Summable fun ρ : zetaZeroConfig.carrier =>
      4 * lam ^ 6 * packetSextic t c *
        ((zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 6)) :=
    summable_sextic.mul_left _
  have hsum : 1 / 4 * lam ^ 4 * (∑ i, c i * t i ^ 2) ^ 2 * kgQuarticMoment -
      4 * lam ^ 6 * packetSextic t c * kgSexticMass =
      ∑' ρ : zetaZeroConfig.carrier,
        (1 / 4 * lam ^ 4 * (∑ i, c i * t i ^ 2) ^ 2 * kgQuarticTerm ρ -
          4 * lam ^ 6 * packetSextic t c *
            ((zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 6))) := by
    unfold kgQuarticMoment kgSexticMass
    rw [← tsum_mul_left, ← tsum_mul_left, hA.tsum_sub hB]
  rw [hsum]
  have hmode_summable : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * packetMode t c lam ρ := by
    have : ∀ i j : Fin N, Summable fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℝ) * (c i * c j *
          (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re) :=
      fun i j => ((summable_re_cosTerm (lam * (t j - t i))).mul_left (c i * c j)).congr
        fun ρ => by ring
    have h2 : Summable fun ρ : zetaZeroConfig.carrier => ∑ i, ∑ j,
        (zetaZeroConfig.mult ρ : ℝ) * (c i * c j *
          (Complex.cos (((lam * (t j - t i) : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re) :=
      summable_sum fun i _ => summable_sum fun j _ => this i j
    refine h2.congr fun ρ => ?_
    unfold packetMode
    simp_rw [Finset.mul_sum]
  refine Summable.tsum_le_tsum (fun ρ => ?_) (hA.sub hB) hmode_summable
  have h := packetMode_ge_of_second_order_degenerate t c h0 h1 hlam hT ρ
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h hm
  unfold kgQuarticTerm
  linarith

/-- **Small-scale positivity of all packets up to second order**: if `Σ cᵢ ≠ 0` or `Σ cᵢ tᵢ ≠ 0`
or `Σ cᵢ tᵢ² ≠ 0`, the scaled Toeplitz form of the causal wave is unconditionally nonnegative for
all sufficiently small scales. -/
theorem exists_scaledForm_nonneg_of_up_to_second_moment {N : ℕ} (t c : Fin N → ℝ)
    (h : (∑ i, c i) ≠ 0 ∨ (∑ i, c i * t i) ≠ 0 ∨ (∑ i, c i * t i ^ 2) ≠ 0) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 ≤ lam → lam ≤ lam₀ → 0 ≤ scaledForm t c lam := by
  rcases isEmpty_or_nonempty zetaZeroConfig.carrier with hempty | hne
  · refine ⟨1, one_pos, fun lam _ _ => ?_⟩
    unfold scaledForm
    simp [chmdWave_eq_zero_of_isEmpty]
  · haveI := hne
    by_cases h01 : (∑ i, c i) ≠ 0 ∨ (∑ i, c i * t i) ≠ 0
    · exact exists_scaledForm_nonneg t c h01
    · push Not at h01
      rcases h01 with ⟨h0, h1⟩
      have h2 : (∑ i, c i * t i ^ 2) ≠ 0 := by
        rcases h with h | h | h
        · exact absurd h0 h
        · exact absurd h1 h
        · exact h
      have hMpos : 0 < kgQuarticMoment := kgQuarticMoment_pos
      have hD0 : 0 ≤ packetSextic t c := packetSextic_nonneg t c
      have hQ0 : 0 ≤ kgSexticMass := kgSexticMass_nonneg
      have hSpos : 0 < (∑ i, c i * t i ^ 2) ^ 2 := by positivity
      have hT0 : 0 ≤ ∑ k, |t k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      set M : ℝ := kgQuarticMoment
      set D : ℝ := packetSextic t c
      set Q : ℝ := kgSexticMass
      set S : ℝ := (∑ i, c i * t i ^ 2) ^ 2
      set T : ℝ := ∑ k, |t k|
      refine ⟨min (1 / (4 * T + 4)) (Real.sqrt (S * M / (16 * (D + 1) * (Q + 1)))),
        lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity)), fun lam hl0 hl => ?_⟩
      have hl1 : lam ≤ 1 / (4 * T + 4) := hl.trans (min_le_left _ _)
      have hl2 : lam ≤ Real.sqrt (S * M / (16 * (D + 1) * (Q + 1))) := hl.trans (min_le_right _ _)
      have hT : lam * (2 * T) ≤ 1 / 2 := by
        calc lam * (2 * T) ≤ 1 / (4 * T + 4) * (2 * T) := by gcongr
          _ ≤ 1 / 2 := by
              rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
      have hmain := scaledForm_ge_of_second_order_degenerate t c h0 h1 hl0 hT
      have hl2' : lam ^ 2 ≤ S * M / (16 * (D + 1) * (Q + 1)) := by
        have := pow_le_pow_left₀ hl0 hl2 2
        rwa [Real.sq_sqrt (by positivity)] at this
      have hkey : 0 ≤ 1 / 4 * lam ^ 4 * S * M - 4 * lam ^ 6 * D * Q := by
        have hstep1 : 4 * lam ^ 2 * (D * Q) ≤ (1 / 4 * S * M) * (D * Q / ((D + 1) * (Q + 1))) := by
          calc 4 * lam ^ 2 * (D * Q) ≤ 4 * (S * M / (16 * (D + 1) * (Q + 1))) * (D * Q) := by
                gcongr
            _ = (1 / 4 * S * M) * (D * Q / ((D + 1) * (Q + 1))) := by field_simp; ring
        have hstep2 : D * Q / ((D + 1) * (Q + 1)) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith
        have hstep3 : (1 / 4 * S * M) * (D * Q / ((D + 1) * (Q + 1))) ≤ 1 / 4 * S * M :=
          mul_le_of_le_one_right (by positivity) hstep2
        have hstep4 : 4 * lam ^ 6 * D * Q = lam ^ 4 * (4 * lam ^ 2 * (D * Q)) := by ring
        rw [hstep4]
        have hlam4 : 0 ≤ lam ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (hstep1.trans hstep3) hlam4]
      linarith

/-- `3 × 3` Vandermonde vanishing: if `t : Fin 3 → ℝ` is injective and the zeroth, first, and
second moments of `c : Fin 3 → ℝ` vanish, then `c = 0`. -/
theorem eq_zero_of_fin_three_moments_eq_zero {t c : Fin 3 → ℝ} (ht : Function.Injective t)
    (h0 : ∑ i, c i = 0) (h1 : ∑ i, c i * t i = 0) (h2 : ∑ i, c i * t i ^ 2 = 0) :
    ∀ i, c i = 0 := by
  simp only [Fin.sum_univ_three] at h0 h1 h2
  have h01 : t 1 - t 0 ≠ 0 := sub_ne_zero.mpr (ht.ne (by decide))
  have h02 : t 2 - t 0 ≠ 0 := sub_ne_zero.mpr (ht.ne (by decide))
  have h12 : t 2 - t 1 ≠ 0 := sub_ne_zero.mpr (ht.ne (by decide))
  have hc0 : c 0 = 0 := by
    have hid : c 0 * ((t 1 - t 0) * (t 2 - t 0)) =
        (c 0 + c 1 + c 2) * (t 1 * t 2) -
          (c 0 * t 0 + c 1 * t 1 + c 2 * t 2) * (t 1 + t 2) +
          (c 0 * t 0 ^ 2 + c 1 * t 1 ^ 2 + c 2 * t 2 ^ 2) := by ring
    rw [h0, h1, h2] at hid
    have : c 0 * ((t 1 - t 0) * (t 2 - t 0)) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero h01 h02)
  have hc1 : c 1 = 0 := by
    have hid : c 1 * ((t 1 - t 0) * (t 2 - t 1)) =
        -(c 0 + c 1 + c 2) * (t 0 * t 2) +
          (c 0 * t 0 + c 1 * t 1 + c 2 * t 2) * (t 0 + t 2) -
          (c 0 * t 0 ^ 2 + c 1 * t 1 ^ 2 + c 2 * t 2 ^ 2) := by ring
    rw [h0, h1, h2] at hid
    have : c 1 * ((t 1 - t 0) * (t 2 - t 1)) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero h01 h12)
  have hc2 : c 2 = 0 := by linarith
  intro i
  match i with
  | ⟨0, _⟩ => exact hc0
  | ⟨1, _⟩ => exact hc1
  | ⟨2, _⟩ => exact hc2

/-- **Unconditional small-scale positivity of all 3-point Toeplitz packets**: for every 3-point
configuration `t : Fin 3 → ℝ` with distinct sample points and every coefficient vector
`c : Fin 3 → ℝ`, the scaled Toeplitz form `scaledForm t c λ` is nonnegative for all sufficiently
small `λ ≥ 0`. -/
theorem exists_scaledForm_nonneg_fin_three (t c : Fin 3 → ℝ) (ht : Function.Injective t) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 ≤ lam → lam ≤ lam₀ → 0 ≤ scaledForm t c lam := by
  by_cases h : (∑ i, c i) ≠ 0 ∨ (∑ i, c i * t i) ≠ 0 ∨ (∑ i, c i * t i ^ 2) ≠ 0
  · exact exists_scaledForm_nonneg_of_up_to_second_moment t c h
  · push Not at h
    rcases h with ⟨h0, h1, h2⟩
    have hc := eq_zero_of_fin_three_moments_eq_zero ht h0 h1 h2
    refine ⟨1, one_pos, fun lam _ _ => ?_⟩
    unfold scaledForm
    simp [hc]

/-! ## Section 4: Positive Volterra Inverse Light-Cone Reconstruction of the Prime Wave -/

/-- On the real axis, `lightConeBesselReal` is given by its power series
`Σ_k (−x/4)^k / (k! (k+1)!)`. -/
theorem lightConeBesselReal_eq_tsum (x : ℝ) :
    lightConeBesselReal x =
      ∑' k : ℕ, (-x / 4) ^ k / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ)) := by
  unfold lightConeBesselReal lightConeBessel
  rw [Complex.re_tsum (summable_norm_lightConeBesselTerm _).of_norm]
  refine tsum_congr fun k => ?_
  unfold lightConeBesselTerm
  rw [show (-(x : ℂ) / 4) ^ k / ((k.factorial : ℂ) * ((k + 1).factorial : ℂ)) =
      (((-x / 4) ^ k / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

theorem summable_lightConeBesselReal_term (x : ℝ) :
    Summable fun k : ℕ => (-x / 4) ^ k / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ)) := by
  have h := (summable_norm_lightConeBesselTerm (x : ℂ)).of_norm
  have hre := Complex.reCLM.summable h
  refine hre.congr fun k => ?_
  unfold lightConeBesselTerm
  rw [Complex.reCLM_apply,
    show (-(x : ℂ) / 4) ^ k / ((k.factorial : ℂ) * ((k + 1).factorial : ℂ)) =
      (((-x / 4) ^ k / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ)) : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

/-- **Strict positivity of the inverse light-cone Bessel kernel**: for every `x ≤ 0`,
`1 ≤ lightConeBesselReal x`. -/
theorem one_le_lightConeBesselReal_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    1 ≤ lightConeBesselReal x := by
  rw [lightConeBesselReal_eq_tsum]
  have hterm : ∀ k : ℕ, 0 ≤ (-x / 4) ^ k / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ)) := by
    intro k
    have hx4 : 0 ≤ -x / 4 := by linarith
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hk1 : (0 : ℝ) < (k + 1).factorial := by exact_mod_cast Nat.factorial_pos (k + 1)
    positivity
  have h0 := (summable_lightConeBesselReal_term x).le_tsum 0 (fun k _ => hterm k)
  simpa using h0

theorem lightConeBesselReal_pos_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    0 < lightConeBesselReal x :=
  lt_of_lt_of_le one_pos (one_le_lightConeBesselReal_of_nonpos hx)

/-- The real inverse light-cone transmutation
`L⁻¹[A](y) = A(y) + (y²/2) ∫_{−1}^{1} B(−2y²(1−t²)) A(yt) dt`. -/
def inverseLightConeTransmute (A : ℝ → ℝ) (y : ℝ) : ℝ :=
  A y + y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) * A (y * t)

theorem abs_lightConeBesselReal_inverse_light_cone_le (y : ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    |lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2))| ≤ Real.exp (y ^ 2 / 2) := by
  refine (abs_lightConeBesselReal_le _).trans (Real.exp_le_exp.mpr ?_)
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  have hnonpos : -2 * y ^ 2 * (1 - t ^ 2) ≤ 0 := by nlinarith [sq_nonneg y, sq_nonneg t]
  rw [abs_of_nonpos hnonpos]
  nlinarith [sq_nonneg y, sq_nonneg t]

theorem one_le_lightConeBesselReal_inverse_light_cone (y : ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    1 ≤ lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) := by
  refine one_le_lightConeBesselReal_of_nonpos ?_
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
  nlinarith [sq_nonneg y, sq_nonneg t]

/-- **The real inverse light-cone identity**:
`cos(y r) = cos(y √(r² + 2)) + (y²/2) ∫_{−1}^{1} B(−2 y² (1 − t²)) cos(y √(r² + 2) t) dt`. -/
theorem cos_mul_eq_inverseLightConeReal (y r : ℝ) :
    Real.cos (y * r) = Real.cos (y * Real.sqrt (r ^ 2 + 2)) +
      y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) *
          Real.cos (y * Real.sqrt (r ^ 2 + 2) * t) := by
  have h := cos_mul_eq_lightCone (y : ℂ) ((Real.sqrt (r ^ 2 + 2) : ℝ) : ℂ) (-2 : ℂ) (r : ℂ)
    (by rw [← Complex.ofReal_pow (Real.sqrt (r ^ 2 + 2)), Real.sq_sqrt (by positivity)]; push_cast; ring)
  have hint : (∫ t in (-1 : ℝ)..1,
      lightConeBessel ((-2 : ℂ) * (y : ℂ) ^ 2 * (1 - (t : ℂ) ^ 2)) *
        Complex.cos ((y : ℂ) * ((Real.sqrt (r ^ 2 + 2) : ℝ) : ℂ) * t)) =
      ((∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) *
          Real.cos (y * Real.sqrt (r ^ 2 + 2) * t) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Complex.ofReal_mul, ofReal_lightConeBesselReal, Complex.ofReal_cos]
    push_cast
    ring_nf
  rw [hint] at h
  apply Complex.ofReal_injective
  push_cast
  linear_combination h

/-- **Real inverse light-cone splitting of sech²-weighted integrals**: for continuous `g` with
`sech²(r/2) g(r)` integrable,
`∫ cos(yr) sech² g = ∫ cos(y√(r²+2)) sech² g + (y²/2) ∫_{−1}^{1} B(−2y²(1−t²)) ∫ cos(yt√(r²+2)) sech² g dr dt`. -/
theorem integral_cos_mul_sechSqHalf_mul_eq_inverseLightCone (y : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgi : Integrable fun r => sechSqHalf r * g r) :
    ∫ r, Real.cos (y * r) * sechSqHalf r * g r =
      (∫ r, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * g r) +
        y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) *
          ∫ r, Real.cos (y * t * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * g r := by
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) with hBt
  set I : ℝ → ℝ := fun r => ∫ t in (-1 : ℝ)..1,
    Bt t * Real.cos (y * Real.sqrt (r ^ 2 + 2) * t) with hI
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  have hlc : ∀ r, Real.cos (y * r) =
      Real.cos (y * Real.sqrt (r ^ 2 + 2)) + y ^ 2 / 2 * I r := by
    intro r
    rw [cos_mul_eq_inverseLightConeReal y r]
  have hIc : Continuous I :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r t => Bt t * Real.cos (y * Real.sqrt (r ^ 2 + 2) * t)) (by fun_prop) _ _
  have hIb : ∀ r, ‖I r‖ ≤ Real.exp (y ^ 2 / 2) * 2 := by
    intro r
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
      (C := Real.exp (y ^ 2 / 2))
      (f := fun t => Bt t * Real.cos (y * Real.sqrt (r ^ 2 + 2) * t)) fun t ht => by
        rw [Real.norm_eq_abs, abs_mul, ← mul_one (Real.exp (y ^ 2 / 2))]
        exact mul_le_mul (abs_lightConeBesselReal_inverse_light_cone_le y
          (mem_uIoc_neg_one_one_abs_le ht)) (Real.abs_cos_le_one _) (abs_nonneg _)
          (Real.exp_pos _).le
    simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 - -1), show (1 : ℝ) - -1 = 2 by norm_num] using h
  have hint1 : Integrable fun r => Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * g r := by
    refine hgi.norm.mono' (((by fun_prop : Continuous fun r : ℝ =>
      Real.cos (y * Real.sqrt (r ^ 2 + 2))).mul continuous_sechSqHalf).mul hg).aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    rw [mul_assoc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hint2 : Integrable fun r => I r * (sechSqHalf r * g r) := by
    refine (hgi.norm.const_mul (Real.exp (y ^ 2 / 2) * 2)).mono'
      (hIc.aestronglyMeasurable.mul (continuous_sechSqHalf.mul hg).aestronglyMeasurable)
      (Eventually.of_forall fun r => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hIb r) (norm_nonneg _)
  have hprod : Integrable (Function.uncurry fun t r =>
      Bt t * (Real.cos (y * Real.sqrt (r ^ 2 + 2) * t) * (sechSqHalf r * g r)))
      ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod volume) := by
    refine (Integrable.mul_prod (f := fun t => ‖Bt t‖) (g := fun r => ‖sechSqHalf r * g r‖)
      hBc.norm.integrableOn_uIoc hgi.norm).mono'
      (by
        refine Continuous.aestronglyMeasurable ?_
        exact (hBc.comp continuous_fst).mul ((by fun_prop : Continuous fun p : ℝ × ℝ =>
          Real.cos (y * Real.sqrt (p.2 ^ 2 + 2) * p.1)).mul
            ((continuous_sechSqHalf.comp continuous_snd).mul (hg.comp continuous_snd))))
      (Eventually.of_forall fun p => ?_)
    rcases p with ⟨t, r⟩
    simp only [Function.uncurry_apply_pair, norm_mul]
    have hcos : ‖Real.cos (y * Real.sqrt (r ^ 2 + 2) * t)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (by positivity) hcos) (norm_nonneg _)
  have hswap := MeasureTheory.intervalIntegral_integral_swap hprod
  have hleft : ∫ r, I r * (sechSqHalf r * g r) =
      ∫ r, ∫ t in (-1 : ℝ)..1,
        Bt t * (Real.cos (y * Real.sqrt (r ^ 2 + 2) * t) * (sechSqHalf r * g r)) := by
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [hI]
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hright : ∀ t, ∫ r, Bt t * (Real.cos (y * Real.sqrt (r ^ 2 + 2) * t) * (sechSqHalf r * g r)) =
      Bt t * ∫ r, Real.cos (y * t * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * g r := by
    intro t
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [show y * Real.sqrt (r ^ 2 + 2) * t = y * t * Real.sqrt (r ^ 2 + 2) by ring]
    ring
  calc ∫ r, Real.cos (y * r) * sechSqHalf r * g r
      = ∫ r, (Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * g r +
          y ^ 2 / 2 * (I r * (sechSqHalf r * g r))) := by
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only
        rw [hlc r]
        ring
    _ = (∫ r, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * g r) +
          y ^ 2 / 2 * ∫ r, I r * (sechSqHalf r * g r) := by
        rw [integral_add hint1 (hint2.const_mul _), integral_const_mul]
    _ = _ := by
        rw [hleft, ← hswap]
        simp_rw [hright]
        rfl

/-- **Inverse light-cone reconstruction of the prime kernel**:
`L⁻¹[K_·(u)](y) = D(u + y) + D(u − y) > 0`. -/
theorem inverseLightConeTransmute_chmdPrimeKernel (y u : ℝ) :
    inverseLightConeTransmute (fun v => chmdPrimeKernel v u) y =
      dAlembertReal (u + y) + dAlembertReal (u - y) := by
  have hgi : Integrable fun r => sechSqHalf r * Real.cos (r * u) :=
    integrable_sechSqHalf_mul (by fun_prop) fun r => Real.abs_cos_le_one _
  have h := integral_cos_mul_sechSqHalf_mul_eq_inverseLightCone y (by fun_prop) hgi
  have h1 := integral_cos_mul_sechSqHalf_mul_cos y u
  have hint : 1 / π * (y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
      lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) *
        ∫ r, Real.cos (y * t * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * u)) =
      y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) * chmdPrimeKernel (y * t) u := by
    unfold chmdPrimeKernel
    have hpull := intervalIntegral.integral_const_mul (a := (-1 : ℝ)) (b := 1) (1 / π)
      (fun t => lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) *
        ∫ r, Real.cos (y * t * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * u))
    rw [← mul_assoc, mul_comm (1 / π) (y ^ 2 / 2), mul_assoc, ← hpull]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [← h1, h, mul_add, hint]
  rfl

theorem continuous_chmdPrimeKernel (u : ℝ) : Continuous fun v : ℝ => chmdPrimeKernel v u := by
  unfold chmdPrimeKernel
  refine continuous_const.mul ?_
  refine continuous_of_dominated
    (bound := fun r => sechSqHalf r)
    (fun v => (((by fun_prop : Continuous fun r : ℝ => Real.cos (v * Real.sqrt (r ^ 2 + 2))).mul
      continuous_sechSqHalf).mul (by fun_prop)).aestronglyMeasurable)
    (fun v => Eventually.of_forall fun r => ?_)
    integrable_sechSqHalf
    (Eventually.of_forall fun r => by fun_prop)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (sechSqHalf_pos r)]
  calc |Real.cos (v * Real.sqrt (r ^ 2 + 2))| * sechSqHalf r * |Real.cos (r * u)|
      ≤ 1 * sechSqHalf r * 1 := by
        refine mul_le_mul
          (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (sechSqHalf_pos r).le)
          (Real.abs_cos_le_one _) (abs_nonneg _) (by linarith [sechSqHalf_pos r])
    _ = sechSqHalf r := by ring

theorem abs_chmdPrimeKernel_log_le {n : ℕ} (hn : 1 ≤ n) {v Y : ℝ} (hv : |v| ≤ Y) :
    |chmdPrimeKernel v (Real.log n)| ≤
      (1 + Y ^ 2 * Real.exp (Y ^ 2 / 2)) *
        (2 * (8 * (1 + Real.log n + Y) * Real.exp (π * Y) * (n : ℝ) ^ (-π))) := by
  have hY : 0 ≤ Y := (abs_nonneg v).trans hv
  have h := chmdPrimeKernel_eq_lightCone v (Real.log n)
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (2 * v ^ 2 * (1 - t ^ 2))
  set g : ℝ → ℝ := fun t =>
    dAlembertReal (Real.log n + v * t) + dAlembertReal (Real.log n - v * t)
  have hpos : 0 < dAlembertReal (Real.log n + v) + dAlembertReal (Real.log n - v) :=
    add_pos (dAlembertReal_pos _) (dAlembertReal_pos _)
  have hpair_v := dAlembert_pair_le hn hv
  have hg_bound : ∀ t ∈ Set.uIoc (-1 : ℝ) 1,
      ‖Bt t * g t‖ ≤ Real.exp (v ^ 2 / 2) *
        (2 * (8 * (1 + Real.log n + Y) * Real.exp (π * Y) * (n : ℝ) ^ (-π))) := by
    intro t ht
    have hta := mem_uIoc_neg_one_one_abs_le ht
    have hB := abs_lightConeBesselReal_light_cone_le v hta
    have hvt : |v * t| ≤ Y := by
      rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg v) hta).trans hv
    have hpair := dAlembert_pair_le hn hvt
    have hg_pos : 0 < g t := add_pos (dAlembertReal_pos _) (dAlembertReal_pos _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hg_pos]
    exact mul_le_mul hB hpair hg_pos.le (Real.exp_pos _).le
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
    (f := fun t => Bt t * g t) hg_bound
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 - -1),
    show (1 : ℝ) - -1 = 2 by norm_num] at hint
  rw [h]
  have htri : |dAlembertReal (Real.log n + v) + dAlembertReal (Real.log n - v) -
      v ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, Bt t * g t| ≤
      (dAlembertReal (Real.log n + v) + dAlembertReal (Real.log n - v)) +
        v ^ 2 / 2 * |∫ t in (-1 : ℝ)..1, Bt t * g t| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos hpos, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ v ^ 2 / 2)]
  have hv2 : v ^ 2 ≤ Y ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg v) hv 2
    rwa [sq_abs] at this
  have hexp : Real.exp (v ^ 2 / 2) ≤ Real.exp (Y ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hve : v ^ 2 * Real.exp (v ^ 2 / 2) ≤ Y ^ 2 * Real.exp (Y ^ 2 / 2) :=
    mul_le_mul hv2 hexp (Real.exp_pos _).le (sq_nonneg Y)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hM : 0 ≤ 2 * (8 * (1 + Real.log n + Y) * Real.exp (π * Y) * (n : ℝ) ^ (-π)) := by
    have := Real.rpow_pos_of_pos hn0 (-π)
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hint (by positivity : (0 : ℝ) ≤ v ^ 2 / 2),
    mul_le_mul_of_nonneg_right hve hM]

theorem summable_chmdPrimeWave_term (v : ℝ) :
    Summable fun n : ℕ => chmdPrimeWeight n * chmdPrimeKernel v (Real.log n) := by
  refine Summable.of_norm_bounded
    ((summable_chmdPrimeWeight_mul_rpow |v| (abs_nonneg v)).mul_left
      ((1 + |v| ^ 2 * Real.exp (|v| ^ 2 / 2)) * 2))
    fun n => ?_
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [chmdPrimeWeight_eq_zero_of_lt_two hn, zero_mul, norm_zero]
    have : 0 ≤ chmdPrimeWeight n := chmdPrimeWeight_nonneg n
    positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (chmdPrimeWeight_nonneg n),
    show (1 + |v| ^ 2 * Real.exp (|v| ^ 2 / 2)) * 2 *
      (chmdPrimeWeight n * (8 * (1 + Real.log n + |v|) * Real.exp (π * |v|) * (n : ℝ) ^ (-π))) =
      chmdPrimeWeight n * ((1 + |v| ^ 2 * Real.exp (|v| ^ 2 / 2)) *
        (2 * (8 * (1 + Real.log n + |v|) * Real.exp (π * |v|) * (n : ℝ) ^ (-π)))) by ring]
  exact mul_le_mul_of_nonneg_left (abs_chmdPrimeKernel_log_le (by omega) le_rfl)
    (chmdPrimeWeight_nonneg n)

/-- **Positive Volterra reconstruction of the prime wave**: the inverse light-cone transmutation
of `chmdPrimeWave` equals the strictly positive d'Alembert prime wave `masslessPrimeWave`
everywhere on `ℝ`. -/
theorem inverseLightConeTransmute_chmdPrimeWave (y : ℝ) :
    inverseLightConeTransmute chmdPrimeWave y = masslessPrimeWave y := by
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) with hBt
  set F : ℕ → ℝ → ℝ := fun n t =>
    chmdPrimeWeight n * (Bt t * chmdPrimeKernel (y * t) (Real.log n)) with hF
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  have hFint : HasSum (fun n => ∫ t in (-1 : ℝ)..1, F n t)
      (∫ t in (-1 : ℝ)..1, Bt t * chmdPrimeWave (y * t)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => (Real.exp (y ^ 2 / 2) * ((1 + |y| ^ 2 * Real.exp (|y| ^ 2 / 2)) * 2)) *
        (chmdPrimeWeight n * (8 * (1 + Real.log n + |y|) * Real.exp (π * |y|) * (n : ℝ) ^ (-π))))
      (fun n => (by
        simp only [hF]
        exact (continuous_const.mul (hBc.mul
          ((continuous_chmdPrimeKernel (Real.log n)).comp (by fun_prop)))).aestronglyMeasurable))
      (fun n => Eventually.of_forall fun t ht => ?_)
      (Eventually.of_forall fun _ _ =>
        (summable_chmdPrimeWeight_mul_rpow |y| (abs_nonneg y)).mul_left
          (Real.exp (y ^ 2 / 2) * ((1 + |y| ^ 2 * Real.exp (|y| ^ 2 / 2)) * 2)))
      intervalIntegrable_const
      (Eventually.of_forall fun t _ => ?_)
    · have hta := mem_uIoc_neg_one_one_abs_le ht
      rcases Nat.lt_or_ge n 2 with hn | hn
      · simp only [hF, chmdPrimeWeight_eq_zero_of_lt_two hn, zero_mul, norm_zero, mul_zero]
        exact le_rfl
      have hyt : |y * t| ≤ |y| := by
        rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg y) hta
      have hK := abs_chmdPrimeKernel_log_le (n := n) (by omega) hyt
      have hB := abs_lightConeBesselReal_inverse_light_cone_le y hta
      simp only [hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg (chmdPrimeWeight_nonneg n)]
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul hB hK (abs_nonneg _) (Real.exp_pos _).le)
        (chmdPrimeWeight_nonneg n)
      linarith
    · rw [chmdPrimeWave_eq_tsum_kernel]
      have h := ((summable_chmdPrimeWave_term (y * t)).hasSum).mul_left (Bt t)
      refine h.congr_fun fun n => ?_
      simp only [hF]
      ring
  have hterm : ∀ n : ℕ,
      chmdPrimeWeight n * (dAlembertReal (Real.log n + y) + dAlembertReal (Real.log n - y)) =
        chmdPrimeWeight n * chmdPrimeKernel y (Real.log n) +
          y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, F n t := by
    intro n
    rw [← inverseLightConeTransmute_chmdPrimeKernel]
    unfold inverseLightConeTransmute
    simp only [hF]
    rw [intervalIntegral.integral_const_mul]
    ring
  unfold masslessPrimeWave
  simp_rw [hterm]
  rw [(summable_chmdPrimeWave_term y).tsum_add (hFint.summable.mul_left _), tsum_mul_left,
    hFint.tsum_eq, ← chmdPrimeWave_eq_tsum_kernel]
  rfl

/-- **Strict positivity of the inverse light-cone transform of the prime wave** for all `y : ℝ`. -/
theorem inverseLightConeTransmute_chmdPrimeWave_pos (y : ℝ) :
    0 < inverseLightConeTransmute chmdPrimeWave y := by
  rw [inverseLightConeTransmute_chmdPrimeWave]
  exact masslessPrimeWave_pos y

/-- Inverse light-cone identity at the pole frequency `√(7/4)`:
`cosh(y/2) = cos(y√(7/4)) + (y²/2) ∫_{−1}^{1} B(−2y²(1−t²)) cos(yt√(7/4)) dt`. -/
theorem cosh_half_eq_inverseLightCone (y : ℝ) :
    Real.cosh (y / 2) = Real.cos (y * Real.sqrt (7 / 4)) +
      y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) *
          Real.cos (y * t * Real.sqrt (7 / 4)) := by
  have h := cos_mul_eq_lightCone (y : ℂ) ((Real.sqrt (7 / 4) : ℝ) : ℂ) (-2) (I / 2)
    (by rw [← ofReal_pow, Real.sq_sqrt (by norm_num), div_pow, I_sq]; push_cast; ring)
  have hc : Complex.cos ((y : ℂ) * (I / 2)) = (Real.cosh (y / 2) : ℂ) := by
    rw [show (y : ℂ) * (I / 2) = ((y / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.cos_mul_I,
      ofReal_cosh]
  have hint : (∫ t in (-1 : ℝ)..1, lightConeBessel ((-2 : ℂ) * (y : ℂ) ^ 2 * (1 - (t : ℂ) ^ 2)) *
      Complex.cos ((y : ℂ) * ((Real.sqrt (7 / 4) : ℝ) : ℂ) * t)) =
      ((∫ t in (-1 : ℝ)..1, lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) *
        Real.cos (y * t * Real.sqrt (7 / 4)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Complex.ofReal_mul, ofReal_lightConeBesselReal, Complex.ofReal_cos]
    push_cast
    ring_nf
  rw [hint, hc] at h
  apply ofReal_injective
  push_cast at h ⊢
  linear_combination h

/-- **Inverse light-cone reconstruction of the pole wave**:
`L⁻¹[chmdPoleWave](y) = (2 / cos²(1/4)) cosh(y/2)`. -/
theorem inverseLightConeTransmute_chmdPoleWave (y : ℝ) :
    inverseLightConeTransmute chmdPoleWave y =
      2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (y / 2) := by
  rw [cosh_half_eq_inverseLightCone, mul_add]
  unfold inverseLightConeTransmute
  simp_rw [chmdPoleWave_eq]
  have hpull := intervalIntegral.integral_const_mul (a := (-1 : ℝ)) (b := 1)
    (2 / Real.cos (1 / 4 : ℝ) ^ 2)
    (fun t => lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) * Real.cos (y * t * Real.sqrt (7 / 4)))
  have hcongr : (∫ t in (-1 : ℝ)..1,
      lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) *
        (2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cos (y * t * Real.sqrt (7 / 4)))) =
      ∫ t in (-1 : ℝ)..1, (2 / Real.cos (1 / 4 : ℝ) ^ 2) *
        (lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2)) * Real.cos (y * t * Real.sqrt (7 / 4))) :=
    intervalIntegral.integral_congr fun t _ => by ring
  rw [hcongr, hpull]
  ring

/-- **Inverse light-cone reconstruction of the archimedean wave**:
`L⁻¹[chmdArchWave](y) = masslessArchWave y`. -/
theorem inverseLightConeTransmute_chmdArchWave (y : ℝ) :
    inverseLightConeTransmute chmdArchWave y = masslessArchWave y := by
  unfold masslessArchWave inverseLightConeTransmute
  rw [integral_cos_mul_sechSqHalf_mul_eq_inverseLightCone y WeilHerglotz.continuous_gammaBracket
    integrable_sechSqHalf_mul_gammaBracket]
  simp_rw [chmdArchWave_eq]

theorem continuous_chmdPoleWave : Continuous chmdPoleWave := by
  have : chmdPoleWave = fun y => 2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cos (y * Real.sqrt (7 / 4)) := by
    funext y; exact chmdPoleWave_eq y
  rw [this]; fun_prop

theorem continuous_chmdArchWave : Continuous chmdArchWave := by
  have : chmdArchWave = fun y => ∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r *
      EF.gammaBracket r := by
    funext y; exact chmdArchWave_eq y
  rw [this]
  refine continuous_of_dominated
    (bound := fun r => sechSqHalf r * |EF.gammaBracket r|)
    (fun y => (((by fun_prop : Continuous fun r : ℝ => Real.cos (y * Real.sqrt (r ^ 2 + 2))).mul
      continuous_sechSqHalf).mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable)
    (fun y => Eventually.of_forall fun r => ?_)
    integrable_sechSqHalf_mul_abs_gammaBracket
    (Eventually.of_forall fun r => by fun_prop)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (sechSqHalf_pos r)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (sechSqHalf_pos r).le (Real.abs_cos_le_one _)) (abs_nonneg _)

theorem continuous_chmdPrimeWave : Continuous chmdPrimeWave := by
  have : chmdPrimeWave = fun y => chmdPoleWave y + 1 / (2 * π) * chmdArchWave y - chmdWave y := by
    funext y
    have h := chmdWave_eq_pole_add_arch_sub_prime y
    linarith
  rw [this]
  exact (continuous_chmdPoleWave.add (continuous_const.mul continuous_chmdArchWave)).sub
    continuous_chmdWave

/-- **Inverse light-cone three-part decomposition of the causal wave**:
`L⁻¹[φ_Λ](y) = (2/cos²(1/4)) cosh(y/2) + (1/2π) masslessArchWave y − masslessPrimeWave y`. -/
theorem inverseLightConeTransmute_chmdWave (y : ℝ) :
    inverseLightConeTransmute chmdWave y =
      2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (y / 2) +
        1 / (2 * π) * masslessArchWave y - masslessPrimeWave y := by
  rw [← inverseLightConeTransmute_chmdPoleWave, ← inverseLightConeTransmute_chmdArchWave,
    ← inverseLightConeTransmute_chmdPrimeWave]
  unfold inverseLightConeTransmute
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2))
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  have hi_pole : IntervalIntegrable (fun t => Bt t * chmdPoleWave (y * t)) volume (-1) 1 :=
    (hBc.mul (continuous_chmdPoleWave.comp (by fun_prop))).intervalIntegrable _ _
  have hi_arch : IntervalIntegrable (fun t => Bt t * chmdArchWave (y * t)) volume (-1) 1 :=
    (hBc.mul (continuous_chmdArchWave.comp (by fun_prop))).intervalIntegrable _ _
  have hi_prime : IntervalIntegrable (fun t => Bt t * chmdPrimeWave (y * t)) volume (-1) 1 :=
    (hBc.mul (continuous_chmdPrimeWave.comp (by fun_prop))).intervalIntegrable _ _
  have hsplit : (∫ t in (-1 : ℝ)..1, Bt t * chmdWave (y * t)) =
      (∫ t in (-1 : ℝ)..1, Bt t * chmdPoleWave (y * t)) +
        1 / (2 * π) * (∫ t in (-1 : ℝ)..1, Bt t * chmdArchWave (y * t)) -
        (∫ t in (-1 : ℝ)..1, Bt t * chmdPrimeWave (y * t)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi_pole
      (hi_arch.const_mul _), ← intervalIntegral.integral_sub (hi_pole.add (hi_arch.const_mul _))
      hi_prime]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [chmdWave_eq_pole_add_arch_sub_prime (y * t)]
    ring
  rw [hsplit, chmdWave_eq_pole_add_arch_sub_prime y]
  ring

/-- **Global Volterra Upper Bound on the Causal Wave**, unconditional: for every `y : ℝ`,
the positive Volterra transform `L⁻¹[φ_Λ](y)` is strictly bounded above by its pole-plus-archimedean
counterpart `(2/cos²(1/4)) cosh(y/2) + (1/2π) masslessArchWave y`. -/
theorem inverseLightConeTransmute_chmdWave_lt (y : ℝ) :
    inverseLightConeTransmute chmdWave y <
      2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (y / 2) + 1 / (2 * π) * masslessArchWave y := by
  rw [inverseLightConeTransmute_chmdWave]
  linarith [masslessPrimeWave_pos y]

/-- **Quantitative positivity of the prime wave on `[−|y|, |y|]`**: because the inverse light-cone
kernel `B(−2y²(1−t²))` is strictly positive (`≥ 1`) and bounded by `e^{y²/2}`, any upper bound
`chmdPrimeWave s ≤ M` on `[−|y|, |y|]` forces
`masslessPrimeWave y ≤ M (1 + y² e^{y²/2})`, and in particular `0 < M`. -/
theorem masslessPrimeWave_le_of_chmdPrimeWave_le_on_Icc (y M : ℝ)
    (hM : ∀ s ∈ Icc (-|y|) |y|, chmdPrimeWave s ≤ M) :
    masslessPrimeWave y ≤ M * (1 + y ^ 2 * Real.exp (y ^ 2 / 2)) ∧ 0 < M := by
  set Bt : ℝ → ℝ := fun t => lightConeBesselReal (-2 * y ^ 2 * (1 - t ^ 2))
  have hBc : Continuous Bt := continuous_lightConeBesselReal.comp (by fun_prop)
  have hy_mem : y ∈ Icc (-|y|) |y| := ⟨neg_abs_le y, le_abs_self y⟩
  have hMy : chmdPrimeWave y ≤ M := hM y hy_mem
  have hint_le : (∫ t in (-1 : ℝ)..1, Bt t * chmdPrimeWave (y * t)) ≤
      ∫ t in (-1 : ℝ)..1, Bt t * M := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((hBc.mul (continuous_chmdPrimeWave.comp (by fun_prop))).intervalIntegrable _ _)
      ((hBc.mul continuous_const).intervalIntegrable _ _)
      fun t ht => ?_
    have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hB0 : 0 ≤ Bt t := (lightConeBesselReal_pos_of_nonpos (by
      have : t ^ 2 ≤ 1 := by nlinarith [abs_nonneg t, sq_abs t]
      nlinarith [sq_nonneg y])).le
    have hyt : y * t ∈ Icc (-|y|) |y| := by
      rw [mem_Icc, ← abs_le, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg y) hta
    exact mul_le_mul_of_nonneg_left (hM (y * t) hyt) hB0
  have hrec : masslessPrimeWave y ≤ chmdPrimeWave y +
      y ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, Bt t * M := by
    rw [← inverseLightConeTransmute_chmdPrimeWave]
    unfold inverseLightConeTransmute
    linarith [mul_le_mul_of_nonneg_left hint_le (by positivity : (0 : ℝ) ≤ y ^ 2 / 2)]
  have hB_pos : 0 < ∫ t in (-1 : ℝ)..1, Bt t := by
    have h1 : (∫ t in (-1 : ℝ)..1, (1 : ℝ)) ≤ ∫ t in (-1 : ℝ)..1, Bt t := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        intervalIntegrable_const (hBc.intervalIntegrable _ _) fun t ht => ?_
      exact one_le_lightConeBesselReal_inverse_light_cone y (abs_le.mpr ⟨ht.1, ht.2⟩)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1
    linarith
  have hM_pos : 0 < M := by
    by_contra hle
    push Not at hle
    have hint_nonpos : (∫ t in (-1 : ℝ)..1, Bt t * M) ≤ 0 := by
      rw [intervalIntegral.integral_mul_const]
      exact mul_nonpos_of_nonneg_of_nonpos hB_pos.le hle
    have : masslessPrimeWave y ≤ 0 := by
      nlinarith [sq_nonneg y]
    linarith [masslessPrimeWave_pos y]
  have hB_upper : (∫ t in (-1 : ℝ)..1, Bt t) ≤ 2 * Real.exp (y ^ 2 / 2) := by
    have h1 : (∫ t in (-1 : ℝ)..1, Bt t) ≤ ∫ t in (-1 : ℝ)..1, Real.exp (y ^ 2 / 2) := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        (hBc.intervalIntegrable _ _) intervalIntegrable_const fun t ht => ?_
      exact (le_abs_self _).trans
        (abs_lightConeBesselReal_inverse_light_cone_le y (abs_le.mpr ⟨ht.1, ht.2⟩))
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h1
    linarith
  refine ⟨?_, hM_pos⟩
  rw [intervalIntegral.integral_mul_const] at hrec
  nlinarith [mul_le_mul_of_nonneg_right hB_upper hM_pos.le, sq_nonneg y]

end RHTower.CHMDQuarticMoment

end
