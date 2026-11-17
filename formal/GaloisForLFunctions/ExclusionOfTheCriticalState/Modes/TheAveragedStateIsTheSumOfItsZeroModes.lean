import GaloisForLFunctions.ExclusionOfTheCriticalState.TheAveragedStateDecaysAtTheRateOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateIsTheCauchyTransformOfItsZeroValues
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateEquationIsHolomorphicInTheProbeExponent
import GaloisForLFunctions.HTGeometry.LaplaceRayInjective
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.RiemannXiRealAxisNonvanishing

/-!
# The averaged state is the sum of its zero modes

Let `F` be the critical state, `a = a(W₀)`, `c_z = L F(z)` its values at the centred zeros (with
multiplicity) and `Ā` its causal average (`averagedState`), whose Laplace transform is `A(w) L F(w)`,
`A(w) = ((w + 9)(w + 10)(w + 11)(w + 12))⁻¹`. For every `t > 0`

  `Ā(t) = −a⁻¹ Σ_z c_z A(z − 8) e^{(z − 8)t} + Σ_{j=9}^{12} r_j L F(−j) e^{−jt}`,

`(r_9, r_10, r_11, r_12) = (1/6, −1/2, 1/2, −1/6)` the residues of `A` and `L F(−j)` the continuation of the
transform, the zero series absolutely convergent (`criticalState_averagedState_eq_modes`,
`criticalState_hasSum_averagedState`). Every zero contributes the mode `e^{−(8 − z)t}` with coefficient
`−a⁻¹ A(z − 8) L F(z)`; there is no hypothesis on the zeros.

Consequently the averaged state is its right-zero modes up to `O(e^{−8t})`
(`criticalState_averagedState_sub_rightModes_le`): the modes of the zeros on or left of the line and
the archimedean modes are `O(e^{−8t})`. Under a finite layer the right-zero modes are a finite sum
(`criticalState_averagedState_finiteLayer`).

Mechanism. On `Re w > 0` the transform of the state is its Mittag-Leffler series
`−a⁻¹ Σ_z c_z/(w + 8 − z)`, absolutely convergent since `c` is square-summable. The partial fractions
`A(w)/(w − p) = A(p)/(w − p) − Σ_j r_j/((p + j)(w + j))` at `p = z − 8` turn `A(w) L F(w)` into the
Laplace transform of the mode series (the second part sums to the Mittag-Leffler series at `w = −j`).
Both sides are continuous and `O(e^{−7t})` on `(0, ∞)`, and the Laplace transform is injective on
`L²(0, ∞)`.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-! ### Exponential modes on the half-line -/

theorem integrableOn_cexp_mul_expRay {p w : ℂ} (h : p.re < w.re) :
    IntegrableOn (fun t : ℝ => cexp (p * t) * expRay w t) (Ioi 0) := by
  have hre : (p - w).re < 0 := by rw [Complex.sub_re]; linarith
  refine (integrableOn_exp_mul_complex_Ioi hre 0).congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [expRay, ← Complex.exp_add]
  ring_nf

/-- The Laplace transform of a mode: `∫_0^∞ e^{pt} e^{−wt} dt = (w − p)⁻¹` for `Re p < Re w`. -/
theorem integral_cexp_mul_expRay {p w : ℂ} (h : p.re < w.re) :
    ∫ t in Ioi (0 : ℝ), cexp (p * t) * expRay w t = (w - p)⁻¹ := by
  have hre : (p - w).re < 0 := by rw [Complex.sub_re]; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => cexp ((p - w) * t))
      (fun t _ => by simp only; rw [expRay, ← Complex.exp_add]; congr 1; ring),
    integral_exp_mul_complex_Ioi hre 0, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    show w - p = -(p - w) by ring, inv_neg, neg_div, one_div]

theorem integral_norm_cexp_mul_expRay {p w : ℂ} (h : p.re < w.re) :
    ∫ t in Ioi (0 : ℝ), ‖cexp (p * t) * expRay w t‖ = (w.re - p.re)⁻¹ := by
  have e : ∀ t : ℝ, ‖cexp (p * t) * expRay w t‖ = Real.exp ((p.re - w.re) * t) := fun t => by
    rw [norm_mul, norm_cexp_mul_ofReal, norm_expRay, ← Real.exp_add]
    ring_nf
  simp_rw [e]
  rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero,
    show w.re - p.re = -(p.re - w.re) by ring, inv_neg, neg_div, one_div]

/-! ### The coefficients of the zero modes -/

/-- The coefficient `−a⁻¹ L F(z) A(z − 8)` of the mode of the zero `z`. -/
def zeroModeCoeff (W₀ : ℝ) (F : ℝ → ℝ) (q : XiZeroCopy) : ℂ :=
  -(criticalAliasCoefficient W₀ : ℂ)⁻¹ * negativeHalfLineLaplace (cx F) (centredZero q) *
    averageSymbol (centredZero q - 8)

/-- The sum of the zero modes `Σ_z −a⁻¹ c_z A(z − 8) e^{(z−8)t}`. -/
def zeroModeSeries (W₀ : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t)

/-- The four archimedean modes `Σ_{j=9}^{12} r_j L F(−j) e^{−jt}`. -/
def archimedeanModes (W₀ : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℂ :=
  1 / 6 * stateMeromorphic W₀ F (-9) * cexp (-9 * t) -
    1 / 2 * stateMeromorphic W₀ F (-10) * cexp (-10 * t) +
    1 / 2 * stateMeromorphic W₀ F (-11) * cexp (-11 * t) -
    1 / 6 * stateMeromorphic W₀ F (-12) * cexp (-12 * t)

/-- The Laplace transform `Σ_j r_j L F(−j)/(w + j)` of the archimedean modes. -/
def archimedeanTransform (W₀ : ℝ) (F : ℝ → ℝ) (w : ℂ) : ℂ :=
  1 / 6 * stateMeromorphic W₀ F (-9) * (w + 9)⁻¹ -
    1 / 2 * stateMeromorphic W₀ F (-10) * (w + 10)⁻¹ +
    1 / 2 * stateMeromorphic W₀ F (-11) * (w + 11)⁻¹ -
    1 / 6 * stateMeromorphic W₀ F (-12) * (w + 12)⁻¹

/-- At a centred zero, `|A(z − 8)| ≤ |z + 1|⁻¹`: the other three factors have modulus at least one. -/
theorem norm_averageSymbol_centredZero_sub_le (q : XiZeroCopy) :
    ‖averageSymbol (centredZero q - 8)‖ ≤ ‖((-1 : ℂ) - centredZero q)⁻¹‖ := by
  have hre := (abs_lt.mp (abs_re_centredZero_lt q)).1
  have hle : ∀ n : ℂ, n.im = 0 → 3 / 2 ≤ n.re → 1 ≤ ‖centredZero q + n‖ := fun n _ hn => by
    have h := Complex.re_le_norm (centredZero q + n)
    rw [Complex.add_re] at h
    linarith
  have h2 := hle 2 (by simp) (by norm_num)
  have h3 := hle 3 (by simp) (by norm_num)
  have h4 := hle 4 (by simp) (by norm_num)
  have h1 : 0 < ‖centredZero q + 1‖ := by
    have h := Complex.re_le_norm (centredZero q + 1)
    rw [Complex.add_re, Complex.one_re] at h
    linarith
  have e : averageSymbol (centredZero q - 8) =
      ((centredZero q + 1) * (centredZero q + 2) * (centredZero q + 3) * (centredZero q + 4))⁻¹ := by
    unfold averageSymbol
    congr 1
    ring
  have e1 : ‖(-1 : ℂ) - centredZero q‖ = ‖centredZero q + 1‖ := by
    rw [← norm_neg]
    congr 1
    ring
  rw [e, norm_inv, norm_inv, e1, norm_mul, norm_mul, norm_mul]
  apply inv_anti₀ h1
  have h234 : 1 ≤ ‖centredZero q + 2‖ * ‖centredZero q + 3‖ * ‖centredZero q + 4‖ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h2 h3) h4
  nlinarith [mul_le_mul_of_nonneg_left h234 h1.le]

/-- The mode coefficients are absolutely summable. -/
theorem criticalState_summable_norm_zeroModeCoeff {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Summable fun q => ‖zeroModeCoeff W₀ F q‖ := by
  have hp : ∀ q : XiZeroCopy, (1 / 2 : ℝ) ≤ ‖(-1 : ℂ) - centredZero q‖ := fun q => by
    have hre := (abs_lt.mp (abs_re_centredZero_lt q)).1
    have h := Complex.abs_re_le_norm ((-1 : ℂ) - centredZero q)
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re, abs_of_neg (by linarith)] at h
    linarith
  have hs := summable_norm_mul_inv_sub_centredZero
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF) (by norm_num : (0 : ℝ) < 1 / 2) hp
  refine (hs.mul_left ‖(criticalAliasCoefficient W₀ : ℂ)⁻¹‖).of_nonneg_of_le
    (fun q => norm_nonneg _) (fun q => ?_)
  unfold zeroModeCoeff
  rw [norm_mul, norm_mul, norm_neg, norm_mul, mul_assoc]
  gcongr
  exact norm_averageSymbol_centredZero_sub_le q

theorem norm_cexp_zeroMode (q : XiZeroCopy) (t : ℝ) :
    ‖cexp ((centredZero q - 8) * t)‖ = Real.exp (((centredZero q).re - 8) * t) := by
  rw [norm_cexp_mul_ofReal]
  congr 2

theorem norm_cexp_zeroMode_le (q : XiZeroCopy) {t : ℝ} (ht : 0 ≤ t) :
    ‖cexp ((centredZero q - 8) * t)‖ ≤ Real.exp (-(15 / 2 * t)) := by
  have hre := (abs_lt.mp (abs_re_centredZero_lt q)).2
  rw [norm_cexp_zeroMode]
  refine Real.exp_le_exp.mpr ?_
  nlinarith

theorem criticalState_summable_zeroModes {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun q => zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) := by
  refine Summable.of_norm_bounded
    ((criticalState_summable_norm_zeroModeCoeff hW hthreshold hF).mul_right
      (Real.exp (-(15 / 2 * t)))) fun q => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_zeroMode_le q ht) (norm_nonneg _)

/-- `|Σ_z modes(t)| ≤ (Σ_z |coeff_z|) e^{−15t/2}` for `t ≥ 0`. -/
theorem criticalState_norm_zeroModeSeries_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {t : ℝ} (ht : 0 ≤ t) :
    ‖zeroModeSeries W₀ F t‖ ≤
      (∑' q, ‖zeroModeCoeff W₀ F q‖) * Real.exp (-(15 / 2 * t)) := by
  have hS := criticalState_summable_norm_zeroModeCoeff hW hthreshold hF
  have hb : ∀ q, ‖zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t)‖ ≤
      ‖zeroModeCoeff W₀ F q‖ * Real.exp (-(15 / 2 * t)) := fun q => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cexp_zeroMode_le q ht) (norm_nonneg _)
  rw [← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm ((hS.mul_right _).of_nonneg_of_le (fun q => norm_nonneg _) hb)).trans
    (Summable.tsum_le_tsum hb ((hS.mul_right _).of_nonneg_of_le (fun q => norm_nonneg _) hb)
      (hS.mul_right _))

theorem criticalState_continuousOn_zeroModeSeries {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ContinuousOn (zeroModeSeries W₀ F) (Ici 0) := by
  refine continuousOn_tsum (fun q => (by fun_prop : Continuous fun t : ℝ =>
      zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t)).continuousOn)
    (criticalState_summable_norm_zeroModeCoeff hW hthreshold hF) fun q t ht => ?_
  rw [norm_mul]
  calc ‖zeroModeCoeff W₀ F q‖ * ‖cexp ((centredZero q - 8) * t)‖
      ≤ ‖zeroModeCoeff W₀ F q‖ * 1 :=
        mul_le_mul_of_nonneg_left ((norm_cexp_zeroMode_le q ht).trans
          (Real.exp_le_one_iff.mpr (by nlinarith [mem_Ici.mp ht]))) (norm_nonneg _)
    _ = ‖zeroModeCoeff W₀ F q‖ := mul_one _

/-- `|Σ_j r_j L F(−j) e^{−jt}| ≤ (Σ_j |L F(−j)|) e^{−9t}` for `t ≥ 0`. -/
theorem norm_archimedeanModes_le (W₀ : ℝ) (F : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖archimedeanModes W₀ F t‖ ≤
      (‖stateMeromorphic W₀ F (-9)‖ + ‖stateMeromorphic W₀ F (-10)‖ +
        ‖stateMeromorphic W₀ F (-11)‖ + ‖stateMeromorphic W₀ F (-12)‖) * Real.exp (-(9 * t)) := by
  have b : ∀ c M p : ℂ, ‖c‖ ≤ 1 → p.re ≤ -9 →
      ‖c * M * cexp (p * t)‖ ≤ ‖M‖ * Real.exp (-(9 * t)) := fun c M p hc hp => by
    rw [norm_mul, norm_mul, norm_cexp_mul_ofReal]
    have he : Real.exp (p.re * t) ≤ Real.exp (-(9 * t)) := Real.exp_le_exp.mpr (by nlinarith)
    calc ‖c‖ * ‖M‖ * Real.exp (p.re * t) ≤ 1 * ‖M‖ * Real.exp (-(9 * t)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hc (norm_nonneg _)) he (Real.exp_pos _).le
            (mul_nonneg zero_le_one (norm_nonneg _))
      _ = ‖M‖ * Real.exp (-(9 * t)) := by ring
  have b9 := b (1 / 6) (stateMeromorphic W₀ F (-9)) (-9) (by norm_num) (by norm_num)
  have b10 := b (1 / 2) (stateMeromorphic W₀ F (-10)) (-10) (by norm_num) (by norm_num)
  have b11 := b (1 / 2) (stateMeromorphic W₀ F (-11)) (-11) (by norm_num) (by norm_num)
  have b12 := b (1 / 6) (stateMeromorphic W₀ F (-12)) (-12) (by norm_num) (by norm_num)
  unfold archimedeanModes
  calc _ ≤ ‖1 / 6 * stateMeromorphic W₀ F (-9) * cexp (-9 * t)‖ +
        ‖1 / 2 * stateMeromorphic W₀ F (-10) * cexp (-10 * t)‖ +
        ‖1 / 2 * stateMeromorphic W₀ F (-11) * cexp (-11 * t)‖ +
        ‖1 / 6 * stateMeromorphic W₀ F (-12) * cexp (-12 * t)‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

/-! ### The transform of the averaged state in modes -/

theorem xi_half_add_ne_zero_of_re {w : ℂ} (hw : 0 < w.re) : xi (1 / 2 + (w + 8)) ≠ 0 := by
  apply _root_.RHTower.xi_ne_zero_of_one_lt_re
  have e : ((1 : ℂ) / 2 + (w + 8)).re = 1 / 2 + (w.re + 8) := by simp
  rw [e]
  linarith

theorem xi_half_add_ofReal_ne_zero (x : ℝ) : xi (1 / 2 + ((x : ℂ) + 8)) ≠ 0 := by
  have h := _root_.RHTower.xi_ne_zero_of_ofReal (1 / 2 + (x + 8))
  push_cast at h
  exact h

/-- **Partial fractions of the averaging symbol against a zero resolvent.** With `p = z − 8`,
`A(w)/(w − p) = A(p)/(w − p) − Σ_j r_j/((p + j)(w + j))`, multiplied by `−a⁻¹ c`. -/
theorem averageSymbol_mul_zeroResolvent {a c w z : ℂ} (ha : a ≠ 0) (hw : 0 < w.re)
    (hz : |z.re| < 1 / 2) :
    averageSymbol w * (-a⁻¹ * (c * (w + 8 - z)⁻¹)) =
      -a⁻¹ * c * averageSymbol (z - 8) * (w + 8 - z)⁻¹ +
        (1 / 6 * (w + 9)⁻¹ * (-a⁻¹ * (c * (-9 + 8 - z)⁻¹)) -
          1 / 2 * (w + 10)⁻¹ * (-a⁻¹ * (c * (-10 + 8 - z)⁻¹)) +
          1 / 2 * (w + 11)⁻¹ * (-a⁻¹ * (c * (-11 + 8 - z)⁻¹)) -
          1 / 6 * (w + 12)⁻¹ * (-a⁻¹ * (c * (-12 + 8 - z)⁻¹))) := by
  have hz1 := (abs_lt.mp hz).1
  have hz2 := (abs_lt.mp hz).2
  have pos : ∀ u : ℂ, 0 < u.re → u ≠ 0 := fun u hu h0 => by
    rw [h0, Complex.zero_re] at hu; exact lt_irrefl 0 hu
  have neg : ∀ u : ℂ, u.re < 0 → u ≠ 0 := fun u hu h0 => by
    rw [h0, Complex.zero_re] at hu; exact lt_irrefl 0 hu
  have w9 : w + 9 ≠ 0 := pos _ (by simp; linarith)
  have w10 : w + 10 ≠ 0 := pos _ (by simp; linarith)
  have w11 : w + 11 ≠ 0 := pos _ (by simp; linarith)
  have w12 : w + 12 ≠ 0 := pos _ (by simp; linarith)
  have w8 : w + 8 - z ≠ 0 := pos _ (by simp; linarith)
  have z9 : -9 + 8 - z ≠ 0 := neg _ (by simp; linarith)
  have z10 : -10 + 8 - z ≠ 0 := neg _ (by simp; linarith)
  have z11 : -11 + 8 - z ≠ 0 := neg _ (by simp; linarith)
  have z12 : -12 + 8 - z ≠ 0 := neg _ (by simp; linarith)
  have y9 : z - 8 + 9 ≠ 0 := pos _ (by simp; linarith)
  have y10 : z - 8 + 10 ≠ 0 := pos _ (by simp; linarith)
  have y11 : z - 8 + 11 ≠ 0 := pos _ (by simp; linarith)
  have y12 : z - 8 + 12 ≠ 0 := pos _ (by simp; linarith)
  unfold averageSymbol
  field_simp
  ring

/-- **The transform of the averaged state in modes.** On `Re w > 0`,
`A(w) L F(w) − Σ_j r_j L F(−j)/(w + j) = Σ_z −a⁻¹ c_z A(z − 8)/(w + 8 − z)`. -/
theorem criticalState_hasSum_zeroModeTransform {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : 0 < w.re) :
    HasSum (fun q => zeroModeCoeff W₀ F q * (w + 8 - centredZero q)⁻¹)
      (averageSymbol w * negativeHalfLineLaplace (cx F) w - archimedeanTransform W₀ F w) := by
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  have hA := (criticalState_hasSum_stateMeromorphic hW hthreshold hF
    (xi_half_add_ne_zero_of_re hw)).mul_left (averageSymbol w)
  have h9 := (criticalState_hasSum_stateMeromorphic hW hthreshold hF (w := -9)
    (by convert xi_half_add_ofReal_ne_zero (-9) using 3 <;> norm_num)).mul_left
      (1 / 6 * (w + 9)⁻¹)
  have h10 := (criticalState_hasSum_stateMeromorphic hW hthreshold hF (w := -10)
    (by convert xi_half_add_ofReal_ne_zero (-10) using 3 <;> norm_num)).mul_left
      (1 / 2 * (w + 10)⁻¹)
  have h11 := (criticalState_hasSum_stateMeromorphic hW hthreshold hF (w := -11)
    (by convert xi_half_add_ofReal_ne_zero (-11) using 3 <;> norm_num)).mul_left
      (1 / 2 * (w + 11)⁻¹)
  have h12 := (criticalState_hasSum_stateMeromorphic hW hthreshold hF (w := -12)
    (by convert xi_half_add_ofReal_ne_zero (-12) using 3 <;> norm_num)).mul_left
      (1 / 6 * (w + 12)⁻¹)
  have hC := hA.sub (((h9.sub h10).add h11).sub h12)
  have hLF : stateMeromorphic W₀ F w = negativeHalfLineLaplace (cx F) w :=
    (stateMeromorphic_eq_levyContinuation (by linarith)).trans
      (levyContinuation_eq_laplace hW hthreshold hF (by linarith))
  have hv : averageSymbol w * negativeHalfLineLaplace (cx F) w - archimedeanTransform W₀ F w =
      averageSymbol w * stateMeromorphic W₀ F w -
        (1 / 6 * (w + 9)⁻¹ * stateMeromorphic W₀ F (-9) -
          1 / 2 * (w + 10)⁻¹ * stateMeromorphic W₀ F (-10) +
          1 / 2 * (w + 11)⁻¹ * stateMeromorphic W₀ F (-11) -
          1 / 6 * (w + 12)⁻¹ * stateMeromorphic W₀ F (-12)) := by
    rw [hLF]
    unfold archimedeanTransform
    ring
  rw [hv]
  refine hC.congr_fun fun q => ?_
  rw [averageSymbol_mul_zeroResolvent ha hw (abs_re_centredZero_lt q)]
  unfold zeroModeCoeff
  ring

/-- The Laplace transform of the zero modes, term by term. -/
theorem criticalState_hasSum_integral_zeroModes {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : 0 < w.re) :
    HasSum (fun q => zeroModeCoeff W₀ F q * (w + 8 - centredZero q)⁻¹)
      (∫ t in Ioi (0 : ℝ), zeroModeSeries W₀ F t * expRay w t) := by
  have hre : ∀ q : XiZeroCopy, (centredZero q - 8).re = (centredZero q).re - 8 := fun q => by simp
  have hlt : ∀ q : XiZeroCopy, (centredZero q - 8).re < w.re := fun q => by
    have := (abs_lt.mp (abs_re_centredZero_lt q)).2
    rw [hre]
    linarith
  have hI : ∀ q : XiZeroCopy, Integrable (fun t : ℝ => zeroModeCoeff W₀ F q *
      (cexp ((centredZero q - 8) * t) * expRay w t)) (volume.restrict (Ioi 0)) := fun q =>
    (integrableOn_cexp_mul_expRay (hlt q)).const_mul _
  have hN : ∀ q : XiZeroCopy, ∫ t in Ioi (0 : ℝ), ‖zeroModeCoeff W₀ F q *
      (cexp ((centredZero q - 8) * t) * expRay w t)‖ =
        ‖zeroModeCoeff W₀ F q‖ * (w.re - (centredZero q - 8).re)⁻¹ := fun q => by
    simp_rw [norm_mul (zeroModeCoeff W₀ F q)]
    rw [integral_const_mul, integral_norm_cexp_mul_expRay (hlt q)]
  have hS : Summable fun q : XiZeroCopy => ∫ t in Ioi (0 : ℝ), ‖zeroModeCoeff W₀ F q *
      (cexp ((centredZero q - 8) * t) * expRay w t)‖ := by
    simp_rw [hN]
    refine ((criticalState_summable_norm_zeroModeCoeff hW hthreshold hF).mul_right
      (2 / 15)).of_nonneg_of_le
      (fun q => mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (by linarith [hlt q])))
      (fun q => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have := (abs_lt.mp (abs_re_centredZero_lt q)).2
    rw [hre]
    calc (w.re - ((centredZero q).re - 8))⁻¹ ≤ (15 / 2 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) (by linarith)
      _ = 2 / 15 := by norm_num
  have h := hasSum_integral_of_summable_integral_norm hI hS
  have hval : ∫ t in Ioi (0 : ℝ), zeroModeSeries W₀ F t * expRay w t =
      ∫ t in Ioi (0 : ℝ), ∑' q, zeroModeCoeff W₀ F q *
        (cexp ((centredZero q - 8) * t) * expRay w t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [zeroModeSeries]
    rw [← tsum_mul_right]
    exact tsum_congr fun q => by ring
  rw [hval]
  refine h.congr_fun fun q => ?_
  rw [integral_const_mul, integral_cexp_mul_expRay (hlt q)]
  congr 2
  ring

/-- The Laplace transform of the archimedean modes. -/
theorem integral_archimedeanModes_mul_expRay (W₀ : ℝ) (F : ℝ → ℝ) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t => archimedeanModes W₀ F t * expRay w t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), archimedeanModes W₀ F t * expRay w t = archimedeanTransform W₀ F w := by
  have h9 := integrableOn_cexp_mul_expRay (p := -9) (w := w) (by simp; linarith)
  have h10 := integrableOn_cexp_mul_expRay (p := -10) (w := w) (by simp; linarith)
  have h11 := integrableOn_cexp_mul_expRay (p := -11) (w := w) (by simp; linarith)
  have h12 := integrableOn_cexp_mul_expRay (p := -12) (w := w) (by simp; linarith)
  have i9 : IntegrableOn (fun t : ℝ => 1 / 6 * stateMeromorphic W₀ F (-9) *
      (cexp (-9 * t) * expRay w t)) (Ioi 0) := h9.const_mul _
  have i10 : IntegrableOn (fun t : ℝ => 1 / 2 * stateMeromorphic W₀ F (-10) *
      (cexp (-10 * t) * expRay w t)) (Ioi 0) := h10.const_mul _
  have i11 : IntegrableOn (fun t : ℝ => 1 / 2 * stateMeromorphic W₀ F (-11) *
      (cexp (-11 * t) * expRay w t)) (Ioi 0) := h11.const_mul _
  have i12 : IntegrableOn (fun t : ℝ => 1 / 6 * stateMeromorphic W₀ F (-12) *
      (cexp (-12 * t) * expRay w t)) (Ioi 0) := h12.const_mul _
  have i910 : IntegrableOn (fun t : ℝ => 1 / 6 * stateMeromorphic W₀ F (-9) *
      (cexp (-9 * t) * expRay w t) - 1 / 2 * stateMeromorphic W₀ F (-10) *
      (cexp (-10 * t) * expRay w t)) (Ioi 0) := i9.sub i10
  have i911 : IntegrableOn (fun t : ℝ => 1 / 6 * stateMeromorphic W₀ F (-9) *
      (cexp (-9 * t) * expRay w t) - 1 / 2 * stateMeromorphic W₀ F (-10) *
      (cexp (-10 * t) * expRay w t) + 1 / 2 * stateMeromorphic W₀ F (-11) *
      (cexp (-11 * t) * expRay w t)) (Ioi 0) := i910.add i11
  have e : (fun t : ℝ => archimedeanModes W₀ F t * expRay w t) = fun t : ℝ =>
      1 / 6 * stateMeromorphic W₀ F (-9) * (cexp (-9 * t) * expRay w t) -
        1 / 2 * stateMeromorphic W₀ F (-10) * (cexp (-10 * t) * expRay w t) +
        1 / 2 * stateMeromorphic W₀ F (-11) * (cexp (-11 * t) * expRay w t) -
        1 / 6 * stateMeromorphic W₀ F (-12) * (cexp (-12 * t) * expRay w t) := by
    funext t
    unfold archimedeanModes
    ring
  rw [e]
  refine ⟨i911.sub i12, ?_⟩
  rw [integral_sub i911 i12, integral_add i910 i11, integral_sub i9 i10,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cexp_mul_expRay (p := -9) (w := w) (by simp; linarith),
    integral_cexp_mul_expRay (p := -10) (w := w) (by simp; linarith),
    integral_cexp_mul_expRay (p := -11) (w := w) (by simp; linarith),
    integral_cexp_mul_expRay (p := -12) (w := w) (by simp; linarith)]
  unfold archimedeanTransform
  simp only [sub_neg_eq_add]

/-! ### The mode expansion -/

/-- **The averaged state is the sum of its zero modes.** For every `t > 0`,
`Ā(t) = Σ_z −a⁻¹ L F(z) A(z − 8) e^{(z−8)t} + Σ_{j=9}^{12} r_j L F(−j) e^{−jt}`. -/
theorem criticalState_averagedState_eq_modes {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {t : ℝ} (ht : 0 < t) :
    (averagedState F t : ℂ) = zeroModeSeries W₀ F t + archimedeanModes W₀ F t := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC⟩ := criticalState_averaged_decay_beyond_barrier hW hthreshold hF
    (β := 7) (by norm_num)
  set S : ℝ := ∑' q, ‖zeroModeCoeff W₀ F q‖
  set K : ℝ := ‖stateMeromorphic W₀ F (-9)‖ + ‖stateMeromorphic W₀ F (-10)‖ +
    ‖stateMeromorphic W₀ F (-11)‖ + ‖stateMeromorphic W₀ F (-12)‖
  have hS0 : 0 ≤ S := tsum_nonneg fun q => norm_nonneg _
  have hK0 : 0 ≤ K := by positivity
  have hcA : Continuous fun t : ℝ => ((averagedState F t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_averagedState hd.integrable)
  have hcZ : ContinuousOn (zeroModeSeries W₀ F) (Ioi 0) :=
    (criticalState_continuousOn_zeroModeSeries hW hthreshold hF).mono Ioi_subset_Ici_self
  have hcR : Continuous (archimedeanModes W₀ F) := by unfold archimedeanModes; fun_prop
  have hφc : ContinuousOn (fun t : ℝ => ((averagedState F t : ℝ) : ℂ) - zeroModeSeries W₀ F t -
      archimedeanModes W₀ F t) (Ioi 0) :=
    (hcA.continuousOn.sub hcZ).sub hcR.continuousOn
  -- the three pieces are `O(e^{−7t})` on `t > 0`
  have bA : ∀ t : ℝ, 0 < t → ‖((averagedState F t : ℝ) : ℂ)‖ ≤ |C| * Real.exp (-(7 * t)) :=
    fun t ht => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (hC t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have bZ : ∀ t : ℝ, 0 < t → ‖zeroModeSeries W₀ F t‖ ≤ S * Real.exp (-(7 * t)) := fun t ht =>
    (criticalState_norm_zeroModeSeries_le hW hthreshold hF ht.le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hS0)
  have bR : ∀ t : ℝ, 0 < t → ‖archimedeanModes W₀ F t‖ ≤ K * Real.exp (-(7 * t)) := fun t ht =>
    (norm_archimedeanModes_le W₀ F ht.le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hK0)
  have hmem : MemLp (fun t : ℝ => ((averagedState F t : ℝ) : ℂ) - zeroModeSeries W₀ F t -
      archimedeanModes W₀ F t) 2 (volume.restrict (Ioi (0 : ℝ))) := by
    refine ((memLp_two_expRay_restrict (w := 7) (by norm_num) 0).const_mul
      (((|C| + S + K : ℝ)) : ℂ)).of_le (hφc.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_expRay]
    have h7 : -((7 : ℂ).re * t) = -(7 * t) := by simp
    rw [h7]
    calc ‖((averagedState F t : ℝ) : ℂ) - zeroModeSeries W₀ F t - archimedeanModes W₀ F t‖
        ≤ ‖((averagedState F t : ℝ) : ℂ)‖ + ‖zeroModeSeries W₀ F t‖ +
            ‖archimedeanModes W₀ F t‖ :=
          (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (|C| + S + K) * Real.exp (-(7 * t)) := by
          nlinarith [bA t ht, bZ t ht, bR t ht]
  -- the Laplace transform of the difference vanishes on `Re w > 0`
  have hlap : ∀ w : ℂ, 0 < w.re → laplaceRay (fun t : ℝ => ((averagedState F t : ℝ) : ℂ) -
      zeroModeSeries W₀ F t - archimedeanModes W₀ F t) w = 0 := by
    intro w hw
    have hexp : ∀ t : ℝ, 0 < t → ‖expRay w t‖ ≤ 1 := fun t ht => by
      rw [norm_expRay]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    have hint : ∀ f : ℝ → ℂ, ContinuousOn f (Ioi 0) → ∀ B : ℝ,
        (∀ t : ℝ, 0 < t → ‖f t‖ ≤ B * Real.exp (-(7 * t))) →
          IntegrableOn (fun t => f t * expRay w t) (Ioi 0) := by
      intro f hf B hB
      refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 7)).const_mul B).mono'
        ((hf.mul (continuous_expRay w).continuousOn).aestronglyMeasurable measurableSet_Ioi)
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
      rw [norm_mul, show -7 * t = -(7 * t) by ring]
      calc ‖f t‖ * ‖expRay w t‖ ≤ B * Real.exp (-(7 * t)) * 1 :=
            mul_le_mul (hB t ht) (hexp t ht) (norm_nonneg _)
              ((norm_nonneg _).trans (hB t ht))
        _ = B * Real.exp (-(7 * t)) := mul_one _
    have iA := hint _ hcA.continuousOn _ bA
    have iZ := hint _ hcZ _ bZ
    have iR := (integral_archimedeanModes_mul_expRay W₀ F hw).1
    have vA : ∫ t in Ioi (0 : ℝ), ((averagedState F t : ℝ) : ℂ) * expRay w t =
        averageSymbol w * negativeHalfLineLaplace (cx F) w := by
      rw [← integral_averagedState_laplace hd hw]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [expRay]
      ring
    have vZ := (criticalState_hasSum_integral_zeroModes hW hthreshold hF hw).unique
      (criticalState_hasSum_zeroModeTransform hW hthreshold hF hw)
    have iAZ : IntegrableOn (fun x : ℝ => ((averagedState F x : ℝ) : ℂ) * expRay w x -
        zeroModeSeries W₀ F x * expRay w x) (Ioi 0) := iA.sub iZ
    have hpt : ∀ x : ℝ, (((averagedState F x : ℝ) : ℂ) - zeroModeSeries W₀ F x -
        archimedeanModes W₀ F x) * expRay w x = ((averagedState F x : ℝ) : ℂ) * expRay w x -
          zeroModeSeries W₀ F x * expRay w x - archimedeanModes W₀ F x * expRay w x :=
      fun x => by ring
    unfold laplaceRay
    simp_rw [hpt]
    rw [integral_sub iAZ iR, integral_sub iA iZ, vA, vZ,
      (integral_archimedeanModes_mul_expRay W₀ F hw).2]
    ring
  have hae := ae_eq_zero_of_laplaceRay_eq_zero hmem hlap
  have heq := Measure.eqOn_open_of_ae_eq (f := fun t : ℝ => ((averagedState F t : ℝ) : ℂ) -
      zeroModeSeries W₀ F t - archimedeanModes W₀ F t) (g := fun _ => (0 : ℂ))
    hae isOpen_Ioi hφc continuousOn_const
  have h0 := heq ht
  simp only at h0
  linear_combination h0

/-- The zero modes sum to the averaged state minus its archimedean modes. -/
theorem criticalState_hasSum_averagedState {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {t : ℝ} (ht : 0 < t) :
    HasSum (fun q => zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t))
      ((averagedState F t : ℂ) - archimedeanModes W₀ F t) := by
  rw [criticalState_averagedState_eq_modes hW hthreshold hF ht, add_sub_cancel_right]
  exact (criticalState_summable_zeroModes hW hthreshold hF ht.le).hasSum

/-- **The averaged state is its right-zero modes up to `O(e^{−8t})`.** The modes of the zeros with
`Re z ≤ 0` and the archimedean modes are `O(e^{−8t})`. -/
theorem criticalState_averagedState_sub_rightModes_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ K : ℝ, ∀ t : ℝ, 0 < t →
      ‖(averagedState F t : ℂ) - ∑' q : XiZeroCopy, (if 0 < (centredZero q).re then
          zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) else 0)‖ ≤
        K * Real.exp (-(8 * t)) := by
  have hS := criticalState_summable_norm_zeroModeCoeff hW hthreshold hF
  refine ⟨(∑' q, ‖zeroModeCoeff W₀ F q‖) + (‖stateMeromorphic W₀ F (-9)‖ +
    ‖stateMeromorphic W₀ F (-10)‖ + ‖stateMeromorphic W₀ F (-11)‖ +
    ‖stateMeromorphic W₀ F (-12)‖), fun t ht => ?_⟩
  have hs := criticalState_summable_zeroModes hW hthreshold hF ht.le
  have hle : ∀ q, ‖(if 0 < (centredZero q).re then
      zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) else 0)‖ ≤
        ‖zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t)‖ := fun q => by
    split_ifs <;> simp
  have hsR := Summable.of_norm_bounded hs.norm hle
  -- the left and on-line modes
  have hb : ∀ q, ‖zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) -
      (if 0 < (centredZero q).re then
        zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) else 0)‖ ≤
        ‖zeroModeCoeff W₀ F q‖ * Real.exp (-(8 * t)) := fun q => by
    split_ifs with h
    · rw [sub_self, norm_zero]; positivity
    · rw [sub_zero, norm_mul, norm_cexp_zeroMode]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      nlinarith [not_lt.mp h]
  have hD := hs.sub hsR
  have e := criticalState_averagedState_eq_modes hW hthreshold hF ht
  have e2 : (averagedState F t : ℂ) - ∑' q : XiZeroCopy, (if 0 < (centredZero q).re then
      zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) else 0) =
      (∑' q, (zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) -
        (if 0 < (centredZero q).re then
          zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) else 0))) +
        archimedeanModes W₀ F t := by
    rw [e, hs.tsum_sub hsR]
    unfold zeroModeSeries
    ring
  rw [e2]
  have h1 : ‖∑' q, (zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) -
      (if 0 < (centredZero q).re then
        zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) else 0))‖ ≤
      (∑' q, ‖zeroModeCoeff W₀ F q‖) * Real.exp (-(8 * t)) := by
    rw [← tsum_mul_right]
    have hn := (hS.mul_right (Real.exp (-(8 * t)))).of_nonneg_of_le (fun q => norm_nonneg _) hb
    exact (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum hb hn (hS.mul_right _))
  have h2 := (norm_archimedeanModes_le W₀ F ht.le).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity) :
      _ ≤ (‖stateMeromorphic W₀ F (-9)‖ + ‖stateMeromorphic W₀ F (-10)‖ +
        ‖stateMeromorphic W₀ F (-11)‖ + ‖stateMeromorphic W₀ F (-12)‖) * Real.exp (-(8 * t)))
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

/-- **Under a finite layer the averaged state is a finite sum of modes up to `O(e^{−8t})`.** -/
theorem criticalState_averagedState_finiteLayer {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (hfin : {q : XiZeroCopy | 0 < (centredZero q).re}.Finite) :
    ∃ K : ℝ, ∀ t : ℝ, 0 < t →
      ‖(averagedState F t : ℂ) - ∑ q ∈ hfin.toFinset,
          zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t)‖ ≤ K * Real.exp (-(8 * t)) := by
  obtain ⟨K, hK⟩ := criticalState_averagedState_sub_rightModes_le hW hthreshold hF
  refine ⟨K, fun t ht => ?_⟩
  have e : ∑' q : XiZeroCopy, (if 0 < (centredZero q).re then
      zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) else 0) =
      ∑ q ∈ hfin.toFinset, zeroModeCoeff W₀ F q * cexp ((centredZero q - 8) * t) := by
    rw [tsum_eq_sum (s := hfin.toFinset) fun q hq => if_neg (by simpa using hq)]
    exact Finset.sum_congr rfl fun q hq => if_pos (by simpa using hq)
  rw [← e]
  exact hK t ht

end GaloisForLFunctions.ExclusionOfTheCriticalState
