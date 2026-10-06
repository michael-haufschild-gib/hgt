import GaloisForLFunctions.RHTower.LiouvilleHyperbolaCutoffOscillation
import GaloisForLFunctions.RHTower.XiHorizontalSingletonFiberHalfDensity

/-!
# The cutoff transport law up to the two-thirds cut

`LiouvilleHyperbolaCutoffOscillation` proves that the Möbius head `A_θ` of the Liouville hyperbola
decomposition, cut at `x^θ` with `θ ≤ ½`, oscillates beyond `x^{1-θ/2-ε}` in every combination
`dP + cA_θ`, `c ≠ 0`. Two inputs limited it to `θ ≤ ½`: the root-head pole at the transported
point must not be cancelled, and the remainder `E_θ = O(x^θ)` must be holomorphic beyond `½`.

Here both are removed for `θ < 2/3`.

* The remainder transform is holomorphic on `Re z > θ`
  (`analyticOnNhd_cutoffRemainderTransform_wide`), and `θ < 1 - θ/2` exactly when `θ < 2/3`.
* At `w = 1 + θ(ρ - 1)` the root-head argument is `ρ + (1/(2θ) - ½)`, a point on the horizontal
  line of `ρ`. For `θ > ½` it lies inside the strip and could be a zero. Choosing `ρ` alone on its
  horizontal line excludes this (`zetaResidueUnit_rootArg_ne_zero_of_singleton`).
* Such a `ρ` with a nonvanishing contraction exists (`exists_singleton_zero_contracted_nonzero`):
  otherwise `ρ ↦ 1 + θ(ρ - 1)` would inject the horizontal-singleton zeros into the off-line
  copies, so `H₁(T) + N₀,s(T) ≤ N(T)`; the corpus densities `liminf H₁/N ≥ ½` and
  `liminf N₀,s/N ≥ ⅔` make the left side exceed `N(T)`.

**Theorem** (`frequently_gt_and_frequently_lt_wide`). For every `0 < θ < 2/3`, real `d`, `c ≠ 0`,
`β < 1 - θ/2` and `C ≥ 0`, `dP + cA_θ` exceeds `C x^β` and falls below `-C x^β` for arbitrarily
large `x`.
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.RHTower
open RHTower.LiouvilleTriangularHeadOscillation
open RHTower.LiouvilleHyperbolaCutoffOscillation

namespace RHTower.LiouvilleHyperbolaCutoffWide

noncomputable section

/-! ## Remainder holomorphy at a general exponent -/

/-- The transform of a measurable function bounded by `e^{au}`, `a ≥ 0`, is holomorphic on
`Re z > a`. -/
theorem differentiableAt_integral_mul_cexp_exp {g : ℝ → ℝ} (hg : Measurable g) {a : ℝ}
    (ha : 0 ≤ a) (hb : ∀ u, 0 < u → |g u| ≤ Real.exp (a * u)) {z : ℂ} (hz : a < z.re) :
    DifferentiableAt ℂ (fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * Complex.exp (-w * u)) z := by
  have hb' : ∀ u, 0 < u → |g u| ≤ 1 * Real.exp (a * u) := fun u hu => by
    rw [one_mul]; exact hb u hu
  have hg1 : ∀ u, 0 < u → (-1) * g u ≤ 1 * Real.exp (a * u) + 0 := fun u hu => by
    have := neg_abs_le (g u); have := hb u hu; linarith
  have h0 : Measurable (fun _ : ℝ => (0 : ℝ)) := measurable_const
  have hb0 : ∀ u, 0 < u → |(fun _ : ℝ => (0 : ℝ)) u| ≤ 1 * Real.exp (a * u) := fun u _ => by
    simp only [abs_zero]; positivity
  have hg0 : ∀ u, 0 < u → 1 * (fun _ : ℝ => (0 : ℝ)) u ≤ 1 * Real.exp (a * u) + 0 :=
    fun u _ => by simp only [mul_zero, add_zero, one_mul]; positivity
  obtain ⟨hc1, hlo1, hhi1⟩ := isAbscissa_oneSidedMeasure hg (η := -1) (ε := 2) (ε' := 1)
    (K := 0) (B := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl zero_le_one le_rfl
    ha hb' hg1
  obtain ⟨hc2, hlo2, hhi2⟩ := isAbscissa_oneSidedMeasure h0 (η := 1) (ε := 2) (ε' := 1)
    (K := 0) (B := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl zero_le_one le_rfl
    ha hb0 hg0
  have e1 := le_antisymm hhi1 hlo1
  have e2 := le_antisymm hhi2 hlo2
  rw [e1] at hc1
  rw [e2] at hc2
  have hV : IsOpen {w : ℂ | a < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun w : ℂ => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * Complex.exp (-w * u)) =ᶠ[𝓝 z]
      fun w => complexLaplace (expOneSidedMeasure g (-1) 2 a 0) w
        - complexLaplace (expOneSidedMeasure (fun _ => 0) 1 2 a 0) w := by
    filter_upwards [hV.mem_nhds hz] with w hw
    have hw' : a < w.re := hw
    rw [complexLaplace_oneSidedMeasure_eq hg ha le_rfl (by norm_num : (1 : ℝ) ≤ 2) hb' hg1 hw',
      complexLaplace_oneSidedMeasure_eq h0 ha le_rfl (by norm_num : (1 : ℝ) ≤ 2) hb0 hg0 hw']
    simp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  exact (hasDerivAt_complexLaplace hc1 hz).differentiableAt.sub
    (hasDerivAt_complexLaplace hc2 hz).differentiableAt

theorem abs_cutoffRemainder_exp_le_rpow {θ u : ℝ} (hθ1 : θ ≤ 1) (hu : 0 ≤ u) :
    |cutoffRemainder θ (Real.exp u)| ≤ Real.exp (θ * u) := by
  refine (abs_cutoffRemainder_le hθ1 (Real.one_le_exp hu)).trans ?_
  rw [exp_rpow_eq_exp_mul]
  exact Nat.floor_le (Real.exp_pos _).le

theorem analyticOnNhd_cutoffRemainderTransform_wide {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    AnalyticOnNhd ℂ (cutoffRemainderTransform θ) {z : ℂ | θ < z.re} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (differentiableAt_integral_mul_cexp_exp
      ((measurable_cutoffRemainder θ).comp Real.measurable_exp) hθ0
      (fun _ hu => abs_cutoffRemainder_exp_le_rpow hθ1 hu.le) hz).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

/-! ## Head bounds for `θ ≤ 1` -/

theorem abs_cutHarmonicHead_exp_le_wide {θ u : ℝ} (hθ1 : θ ≤ 1) (hu : 0 ≤ u) :
    |LiouvilleTriangularShortHead.squareMass * Real.exp u * mobiusHarmonic (Real.exp u ^ θ)|
      ≤ LiouvilleTriangularShortHead.squareMass * Real.exp (2 * u) := by
  have hZ := squareMass_pos
  have hE := Real.exp_pos u
  rw [exp_rpow_eq_exp_mul]
  have h1 : |mobiusHarmonic (Real.exp (θ * u))| ≤ Real.exp u :=
    (abs_mobiusHarmonic_le _).trans ((Nat.floor_le (Real.exp_pos _).le).trans
      (Real.exp_le_exp.mpr (by nlinarith)))
  have h2 : Real.exp (2 * u) = Real.exp u * Real.exp u := by rw [← Real.exp_add]; ring_nf
  rw [abs_mul, abs_mul, abs_of_pos hZ, abs_of_pos hE, h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

theorem abs_cutRootHead_exp_le_wide {θ u : ℝ} (hθ1 : θ ≤ 1) (hu : 0 ≤ u) :
    |-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ)| ≤ 2 * Real.exp (2 * u) := by
  rw [exp_rpow_eq_exp_mul, sqrt_exp_eq_exp_half_mul]
  have hE := Real.exp_pos (1 / 2 * u)
  have h1 : |mobiusRoot (Real.exp (θ * u))| ≤ Real.exp u :=
    (abs_mobiusRoot_le _).trans ((Nat.floor_le (Real.exp_pos _).le).trans
      (Real.exp_le_exp.mpr (by nlinarith)))
  have h2 : Real.exp (1 / 2 * u) * Real.exp u ≤ Real.exp (2 * u) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  rw [abs_mul, abs_mul, abs_of_pos hE]
  norm_num
  nlinarith [abs_nonneg (mobiusRoot (Real.exp (θ * u)))]

theorem abs_cutoffHead_exp_le_wide {θ u : ℝ} (hθ1 : θ ≤ 1) (hu : 0 ≤ u) :
    |cutoffHead θ (Real.exp u)|
      ≤ (LiouvilleTriangularShortHead.squareMass + 3) * Real.exp (2 * u) := by
  rw [cutoffHead_eq]
  have h1 := abs_cutHarmonicHead_exp_le_wide hθ1 hu
  have h2 := abs_cutRootHead_exp_le_wide hθ1 hu
  have h3 := abs_cutoffRemainder_exp_le_rpow hθ1 hu
  have hZ := squareMass_pos
  have e3 : Real.exp (θ * u) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by nlinarith)
  have hab := abs_add_le (LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.exp u ^ θ) + -2 * Real.sqrt (Real.exp u) *
        mobiusRoot (Real.exp u ^ θ)) (cutoffRemainder θ (Real.exp u))
  have hab2 := abs_add_le (LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.exp u ^ θ))
      (-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ))
  nlinarith

theorem abs_cutCombination_exp_le_wide {θ : ℝ} (hθ1 : θ ≤ 1) (d c : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    |d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)|
      ≤ (2 * |d| + |c| * (LiouvilleTriangularShortHead.squareMass + 3)) * Real.exp (2 * u) := by
  have h1 := abs_liouvilleTriangle_exp_le hu
  have h2 := abs_cutoffHead_exp_le_wide hθ1 hu
  calc |d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)|
      ≤ |d| * |liouvilleTriangle (Real.exp u)| + |c| * |cutoffHead θ (Real.exp u)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |d| * (2 * Real.exp (2 * u))
        + |c| * ((LiouvilleTriangularShortHead.squareMass + 3) * Real.exp (2 * u)) := by
        gcongr
    _ = _ := by ring

/-! ## Transforms for `θ < 1` -/

theorem integral_cutoffHead_exp_mul_cexp_wide {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {s : ℂ}
    (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), (cutoffHead θ (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = LiouvilleTriangularShortHead.squareMass / ((s - 1) * riemannZeta ((s - 1) / θ + 1))
        - 2 / ((s - 1 / 2) * riemannZeta ((s - 1 / 2) / θ + 1 / 2))
        + cutoffRemainderTransform θ s := by
  have hp : Measurable fun u : ℝ => Real.exp u ^ θ := Real.measurable_exp.pow_const θ
  have i1 : IntegrableOn (fun u : ℝ => ((LiouvilleTriangularShortHead.squareMass * Real.exp u *
      mobiusHarmonic (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le
      (g := fun u => LiouvilleTriangularShortHead.squareMass * Real.exp u *
        mobiusHarmonic (Real.exp u ^ θ))
      ((measurable_const.mul Real.measurable_exp).mul (measurable_mobiusHarmonic.comp hp))
      (fun u hu => abs_cutHarmonicHead_exp_le_wide hθ1.le hu.le) (by linarith)
  have i2 : IntegrableOn (fun u : ℝ => ((-2 * Real.sqrt (Real.exp u) *
      mobiusRoot (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le
      (g := fun u => -2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ))
      ((measurable_const.mul (Real.continuous_sqrt.measurable.comp Real.measurable_exp)).mul
        (measurable_mobiusRoot.comp hp))
      (fun u hu => abs_cutRootHead_exp_le_wide hθ1.le hu.le) (C := 2) (a := 2) hs
  have i3 : IntegrableOn (fun u : ℝ => (cutoffRemainder θ (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := 1) (a := θ)
      ((measurable_cutoffRemainder θ).comp Real.measurable_exp)
      (fun u hu => by simpa using abs_cutoffRemainder_exp_le_rpow hθ1.le hu.le) (by linarith)
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (cutoffHead θ (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = (((LiouvilleTriangularShortHead.squareMass * Real.exp u *
          mobiusHarmonic (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)
        + ((-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ) : ℝ) : ℂ)
          * Complex.exp (-s * u))
        + (cutoffRemainder θ (Real.exp u) : ℂ) * Complex.exp (-s * u) := by
    intro u _
    rw [cutoffHead_eq]
    push_cast
    ring
  have i12 : IntegrableOn (fun u : ℝ => ((LiouvilleTriangularShortHead.squareMass *
      Real.exp u * mobiusHarmonic (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)
      + ((-2 * Real.sqrt (Real.exp u) * mobiusRoot (Real.exp u ^ θ) : ℝ) : ℂ)
        * Complex.exp (-s * u)) (Ioi 0) := i1.add i2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i12 i3,
    integral_add i1 i2, integral_cutHarmonicHead hθ0 (by linarith) hs,
    integral_cutRootHead hθ0 (by linarith) hs]
  unfold cutoffRemainderTransform
  ring

theorem integral_cutCombination_exp_mul_cexp_wide {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (d c : ℝ) {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)
        : ℝ) : ℂ) * Complex.exp (-s * u)
      = cutPoleModel θ d c s + c * cutoffRemainderTransform θ s := by
  have i1 : IntegrableOn (fun u : ℝ => (liouvilleTriangle (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := 2) (a := 2)
      (measurable_liouvilleTriangle.comp Real.measurable_exp)
      (fun u hu => abs_liouvilleTriangle_exp_le hu.le) hs
  have i2 : IntegrableOn (fun u : ℝ => (cutoffHead θ (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := LiouvilleTriangularShortHead.squareMass + 3) (a := 2)
      ((measurable_cutoffHead θ).comp Real.measurable_exp)
      (fun u hu => abs_cutoffHead_exp_le_wide hθ1.le hu.le) hs
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ((d * liouvilleTriangle (Real.exp u)
        + c * cutoffHead θ (Real.exp u) : ℝ) : ℂ) * Complex.exp (-s * u)
      = (d : ℂ) * ((liouvilleTriangle (Real.exp u) : ℂ) * Complex.exp (-s * u))
        + (c : ℂ) * ((cutoffHead θ (Real.exp u) : ℂ) * Complex.exp (-s * u)) := by
    intro u _
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add (i1.const_mul _)
    (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_liouvilleTriangle_exp_mul_cexp hs, integral_cutoffHead_exp_mul_cexp_wide hθ0 hθ1 hs]
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  have hs1 : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have hs1' : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs; linarith
  have hsh : s - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hθre : ∀ w : ℂ, (w / θ).re = w.re / θ := fun w => by
    rw [show w / (θ : ℂ) = w * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
  have hhre : 1 < (headArg θ s).re := by
    unfold headArg
    rw [Complex.add_re, hθre, Complex.one_re, Complex.sub_re, Complex.one_re]
    have : 0 < (s.re - 1) / θ := div_pos (by linarith) hθ0
    linarith
  have hvre : 1 < (rootArg θ s).re := by
    unfold rootArg
    rw [Complex.add_re, hθre, Complex.sub_re]
    have : 1 ≤ (s.re - (1 / 2 : ℂ).re) / θ := by
      rw [le_div_iff₀ hθ0]; norm_num; linarith
    norm_num at this ⊢
    linarith
  have hh1 : headArg θ s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hhre; linarith
  have hv1 : rootArg θ s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hvre; linarith
  have hz1 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hzh : riemannZeta (headArg θ s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hhre
  have hzv : riemannZeta (rootArg θ s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hvre
  have hd1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
  have hdh : headArg θ s - 1 ≠ 0 := sub_ne_zero.mpr hh1
  have hdv : rootArg θ s - 1 ≠ 0 := sub_ne_zero.mpr hv1
  unfold cutPoleModel
  rw [zetaResidueUnit_eq hs1', zetaResidueUnit_eq hh1, zetaResidueUnit_eq hv1]
  have eh : headArg θ s - 1 = (s - 1) / θ := by unfold headArg; ring
  have ehz : (s - 1) / (θ : ℂ) + 1 = headArg θ s := rfl
  have evz : (s - 1 / 2) / (θ : ℂ) + 1 / 2 = rootArg θ s := rfl
  rw [ehz, evz, eh]
  have e3 : -2 * (c : ℂ) * (rootArg θ s - 1) /
      ((s - 1 / 2) * ((rootArg θ s - 1) * riemannZeta (rootArg θ s)))
      = -2 * c / ((s - 1 / 2) * riemannZeta (rootArg θ s)) := by
    rw [show -2 * (c : ℂ) * (rootArg θ s - 1) = (rootArg θ s - 1) * (-2 * c) by ring,
      show (s - 1 / 2) * ((rootArg θ s - 1) * riemannZeta (rootArg θ s))
        = (rootArg θ s - 1) * ((s - 1 / 2) * riemannZeta (rootArg θ s)) by ring,
      mul_div_mul_left _ _ hdv]
  rw [e3]
  generalize riemannZeta (rootArg θ s) = Zv at *
  generalize riemannZeta (headArg θ s) = Zh at *
  field_simp
  ring

/-! ### The contradiction -/


/-! ## The contradiction for `θ < 1` -/

theorem false_of_oneSided_wide {θ d c η C β K : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C) (hβθ : 1 - θ < β) (hβθ' : θ < β)
    (hK : 0 ≤ K) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hρlo : 1 / 2 ≤ ρ.re) (hρhi : ρ.re < 1) (hρim : ρ.im ≠ 0)
    (hwz : riemannZeta (1 + θ * (ρ - 1)) ≠ 0)
    (hUv : RHTower.zetaResidueUnit (rootArg θ (1 + θ * (ρ - 1))) ≠ 0)
    (hβw : β < 1 - θ * (1 - ρ.re))
    (hg : ∀ u, 0 < u → η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
      ≤ C * Real.exp (β * u) + K) :
    False := by
  set Z := LiouvilleTriangularShortHead.squareMass with hZdef
  have hZ := squareMass_pos
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  set f : ℝ → ℝ := fun u => d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)
    with hfdef
  have hf : Measurable f := (measurable_const.mul
    (measurable_liouvilleTriangle.comp Real.measurable_exp)).add
    (measurable_const.mul ((measurable_cutoffHead θ).comp Real.measurable_exp))
  set B : ℝ := 2 * |d| + |c| * (Z + 3) with hBdef
  have hB : 0 ≤ B := by positivity
  have hb : ∀ u, 0 < u → |f u| ≤ B * Real.exp (2 * u) := fun u hu =>
    abs_cutCombination_exp_le_wide hθ1.le d c hu.le
  have hβ0 : 0 ≤ β := by linarith
  have hβ2 : β ≤ 2 := by nlinarith
  have hCC : C < C + 1 := lt_add_one C
  obtain ⟨hc0, hlo, hhi⟩ := isAbscissa_oneSidedMeasure hf hη hC hCC hK hB hβ2
    (by norm_num) hb hg
  set ν := expOneSidedMeasure f η (C + 1) β K with hνdef
  set Ψ : ℂ → ℂ := fun z => ((C + 1 : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - η * (cutPoleModel θ d c z + c * cutoffRemainderTransform θ z) with hΨdef
  have hagree : ∀ z : ℂ, 2 < z.re → complexLaplace ν z = Ψ z := by
    intro z hz
    rw [complexLaplace_oneSidedMeasure_eq hf hβ0 hβ2 hCC.le hb hg hz]
    simp only [hΨdef, hfdef]
    rw [integral_cutCombination_exp_mul_cexp_wide hθ0 hθ1 d c hz]
  have hΨa : ∀ t : ℝ, β < t → AnalyticAt ℂ Ψ t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < t).ne'
    have htβ : (t : ℂ) - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hP := analyticAt_cutPoleModel_ofReal hθ0 d c (by linarith : (1 : ℝ) / 2 < t)
      (by linarith : 1 - θ < t)
    have hR : AnalyticAt ℂ (cutoffRemainderTransform θ) t :=
      analyticOnNhd_cutoffRemainderTransform_wide hθ0.le hθ1.le t (by simp; linarith)
    simp only [hΨdef]
    exact ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) htβ).add
      (analyticAt_const.div analyticAt_id ht0)).sub
      (analyticAt_const.mul (hP.add (analyticAt_const.mul hR)))
  have hcβ : IsAbscissa ν β := isAbscissa_eq_of_analyticAt_real hc0 hlo hhi hΨa hagree
  set V : Set ℂ := {z : ℂ | β < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  set Lf : ℂ → ℂ := fun z => (((C + 1 : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - complexLaplace ν z) * cutPoleDenominator θ z with hLf
  set Rf : ℂ → ℂ := fun z => (η : ℂ) * (cutPoleNumerator θ d c z
      + c * cutoffRemainderTransform θ z * cutPoleDenominator θ z) with hRf
  have hLa : AnalyticOnNhd ℂ Lf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hzβ : z - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have d1 : DifferentiableAt ℂ (fun z : ℂ => ((C + 1 : ℝ) : ℂ) / (z - β)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) hzβ
    have d2 : DifferentiableAt ℂ (fun z : ℂ => (K : ℂ) / z) z :=
      (differentiableAt_const _).div differentiableAt_id hz0
    exact (((d1.add d2).sub (hasDerivAt_complexLaplace hcβ hz').differentiableAt).mul
      (differentiableAt_cutPoleDenominator θ z)).differentiableWithinAt
  have hRa : AnalyticOnNhd ℂ Rf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have h2z : 2 * z ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hR : DifferentiableAt ℂ (cutoffRemainderTransform θ) z :=
      (analyticOnNhd_cutoffRemainderTransform_wide hθ0.le hθ1.le z
        (by simp; linarith)).differentiableAt
    exact ((differentiableAt_const _).mul ((differentiableAt_cutPoleNumerator θ d c h2z).add
      (((differentiableAt_const _).mul hR).mul
        (differentiableAt_cutPoleDenominator θ z)))).differentiableWithinAt
  have hθre : ∀ w : ℂ, (w / θ).re = w.re / θ := fun w => by
    rw [show w / (θ : ℂ) = w * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
  have hev : Lf =ᶠ[𝓝 (3 : ℂ)] Rf := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    have hz' : 2 < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hz1 : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz'; linarith
    have hzh : z - 1 / 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hhre : 1 < (headArg θ z).re := by
      unfold headArg
      rw [Complex.add_re, hθre, Complex.one_re, Complex.sub_re, Complex.one_re]
      have : 0 < (z.re - 1) / θ := div_pos (by linarith) hθ0
      linarith
    have hvre : 1 < (rootArg θ z).re := by
      unfold rootArg
      rw [Complex.add_re, hθre, Complex.sub_re]
      have : 1 ≤ (z.re - (1 / 2 : ℂ).re) / θ := by
        rw [le_div_iff₀ hθ0]; norm_num; linarith
      norm_num at this ⊢
      linarith
    have hh1 : headArg θ z ≠ 1 := by intro h; rw [h, Complex.one_re] at hhre; linarith
    have hv1 : rootArg θ z ≠ 1 := by intro h; rw [h, Complex.one_re] at hvre; linarith
    have hU : RHTower.zetaResidueUnit z ≠ 0 := by
      rw [zetaResidueUnit_eq hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_lt_re (by linarith))
    have hUh : RHTower.zetaResidueUnit (headArg θ z) ≠ 0 := by
      rw [zetaResidueUnit_eq hh1]
      exact mul_ne_zero (sub_ne_zero.mpr hh1) (riemannZeta_ne_zero_of_one_lt_re hhre)
    have hUv : RHTower.zetaResidueUnit (rootArg θ z) ≠ 0 := by
      rw [zetaResidueUnit_eq hv1]
      exact mul_ne_zero (sub_ne_zero.mpr hv1) (riemannZeta_ne_zero_of_one_lt_re hvre)
    simp only [hLf, hRf]
    rw [hagree z hz', ← cutPoleModel_mul_denominator θ d c hθC hz0 hU hzh hUv hUh]
    simp only [hΨdef]
    ring
  have h3V : (3 : ℂ) ∈ V := by show β < (3 : ℂ).re; norm_num; linarith
  have heq := hLa.eqOn_of_preconnected_of_eventuallyEq hRa
    (convex_halfSpace_re_gt β).isPreconnected h3V hev
  set w : ℂ := 1 + θ * (ρ - 1) with hwdef
  have hwre : w.re = 1 - θ * (1 - ρ.re) := by simp [hwdef]; ring
  have hwim : w.im = θ * ρ.im := by simp [hwdef]
  have hwlo : 1 - θ / 2 ≤ w.re := by rw [hwre]; nlinarith
  have hwV : w ∈ V := by show β < w.re; rw [hwre]; exact hβw
  have hhw : headArg θ w = ρ := by
    unfold headArg; rw [hwdef]; field_simp; ring
  have hUh : RHTower.zetaResidueUnit (headArg θ w) = 0 := by
    rw [hhw]; exact zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hρ
  have hDw : cutPoleDenominator θ w = 0 := by
    unfold cutPoleDenominator; rw [hUh, mul_zero]
  have h := heq hwV
  simp only [hLf, hRf, hDw, mul_zero, add_zero] at h
  have hNw : cutPoleNumerator θ d c w = c * Z / θ * (w * RHTower.zetaResidueUnit w * (w - 1 / 2)
      * RHTower.zetaResidueUnit (rootArg θ w)) := by
    unfold cutPoleNumerator; rw [hUh]; ring
  rw [hNw] at h
  have hη0 : (η : ℂ) ≠ 0 := by
    have : η ≠ 0 := by intro h0; rw [h0, abs_zero] at hη; norm_num at hη
    exact_mod_cast this
  have ha : (c : ℂ) * Z / θ ≠ 0 :=
    div_ne_zero (mul_ne_zero (by exact_mod_cast hc) (by exact_mod_cast hZ.ne')) hθC
  have hw0 : w ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; rw [Complex.zero_re] at this; linarith
  have hw1 : w ≠ 1 := by
    intro h0; have := congrArg Complex.im h0; rw [hwim, Complex.one_im] at this
    exact mul_ne_zero hθ0.ne' hρim this
  have hwh : w - 1 / 2 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hUw : RHTower.zetaResidueUnit w ≠ 0 := by
    rw [zetaResidueUnit_eq hw1]; exact mul_ne_zero (sub_ne_zero.mpr hw1) hwz
  exact (mul_ne_zero hη0 (mul_ne_zero ha (mul_ne_zero (mul_ne_zero (mul_ne_zero hw0 hUw) hwh)
    hUv))) h.symm



/-! ## A singleton critical zero whose contraction is not a zero -/

/-- Two distinct zeros on one horizontal line give fibre multiplicity at least two. -/
theorem two_le_xiHorizontalMultiplicity_of_ne {t : ℝ} {z w : ℂ} (hz : z ∈ stripHeightFinset t)
    (hw : w ∈ stripHeightFinset t) (hne : z ≠ w) : 2 ≤ xiHorizontalMultiplicity t := by
  classical
  have hpair : ({z, w} : Finset ℂ) ⊆ stripHeightFinset t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hz
    · exact hw
  have hle : (analyticOrderAt xi z).toNat + (analyticOrderAt xi w).toNat
      ≤ xiHorizontalMultiplicity t := by
    rw [xiHorizontalMultiplicity]
    simpa only [Finset.sum_pair hne] using
      (Finset.sum_le_sum_of_subset hpair (f := fun x => (analyticOrderAt xi x).toNat))
  have hz1 : 1 ≤ (analyticOrderAt xi z).toNat :=
    Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero (mem_stripHeightFinset.mp hz).2.2.2)
  have hw1 : 1 ≤ (analyticOrderAt xi w).toNat :=
    Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero (mem_stripHeightFinset.mp hw).2.2.2)
  omega

theorem xi_eq_zero_of_riemannZeta_eq_zero {z : ℂ} (hz : riemannZeta z = 0) (h0 : 0 < z.re) :
    xi z = 0 := by
  rcases RHTower.riemannZeta_eq_zero_iff_xi_or_trivial.mp hz with h | ⟨n, hn⟩
  · exact h
  · exfalso
    have := congrArg Complex.re hn
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- If every horizontal-singleton zero had a zero at its contraction `1 + θ(ρ - 1)`, the
singleton fibres would inject into the off-line copies. -/
theorem xiSingletonFiberCount_le_xiOffLineZeroCount_of_forall {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (h : ∀ ρ : ℂ, XiHorizontalSingletonZero ρ → 0 < ρ.im → riemannZeta (1 + θ * (ρ - 1)) = 0)
    (T : ℝ) : xiSingletonFiberCount T ≤ xiOffLineZeroCount T := by
  classical
  set S := (stripFinsetPos T).filter (fun z => xiHorizontalMultiplicity z.im = 1) with hS
  set O := (stripFinsetPos T).filter (fun z => ¬ z.re = 1 / 2) with hO
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  have hmaps : ∀ z ∈ S, (1 + θ * (z - 1)) ∈ O := by
    intro z hz
    rw [hS, Finset.mem_filter, mem_stripFinsetPos] at hz
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, hmul⟩ := hz
    have hsing : XiHorizontalSingletonZero z :=
      ⟨mem_stripHeightFinset.mpr ⟨h1, h2, rfl, h5⟩, hmul⟩
    have hre : z.re = 1 / 2 := xiHorizontalSingletonZero_re_eq_half hsing
    have hζ := h z hsing h3
    have hwre : (1 + θ * (z - 1)).re = 1 - θ / 2 := by simp [hre]; ring
    have hwim : (1 + θ * (z - 1)).im = θ * z.im := by simp
    rw [hO, Finset.mem_filter, mem_stripFinsetPos]
    refine ⟨⟨by rw [hwre]; linarith, by rw [hwre]; linarith, by rw [hwim]; positivity,
      by rw [hwim]; nlinarith, xi_eq_zero_of_riemannZeta_eq_zero hζ (by rw [hwre]; linarith)⟩,
      by rw [hwre]; intro h'; linarith⟩
  have hinj : Set.InjOn (fun z : ℂ => 1 + θ * (z - 1)) S := by
    intro z _ w _ hzw
    have : (θ : ℂ) * (z - 1) = θ * (w - 1) := by simpa using hzw
    have := mul_left_cancel₀ hθC this
    linear_combination this
  have hcard : S.card ≤ O.card := Finset.card_le_card_of_injOn _ hmaps hinj
  have hO_le : O.card ≤ xiOffLineZeroCount T := by
    rw [xiOffLineZeroCount, Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun z hz => ?_
    rw [hO, Finset.mem_filter, mem_stripFinsetPos] at hz
    exact Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hz.1.2.2.2.2)
  exact hcard.trans hO_le

/-- **A singleton critical zero with a nonvanishing contraction.** For every `0 < θ < 1` some
zero `ρ`, alone on its horizontal line (hence simple and critical), has `ζ(1 + θ(ρ - 1)) ≠ 0`.
Otherwise singleton fibres would inject into off-line copies, against the corpus densities
(singletons `≥ ½`, simple critical zeros `≥ ⅔`). -/
theorem exists_singleton_zero_contracted_nonzero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ ρ : ℂ, XiHorizontalSingletonZero ρ ∧ 0 < ρ.im ∧ riemannZeta (1 + θ * (ρ - 1)) ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ ρ : ℂ, XiHorizontalSingletonZero ρ → 0 < ρ.im →
      riemannZeta (1 + θ * (ρ - 1)) = 0 := fun ρ h1 h2 => by
    by_contra h3
    exact hcon ⟨ρ, h1, h2, h3⟩
  have hkey := xiSingletonFiberCount_le_xiOffLineZeroCount_of_forall hθ0 hθ1 hcon'
  have hb1 : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop xiSingletonFiberRatio :=
    isBoundedUnder_of ⟨0, fun T => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  have hb2 : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop xiSimpleCriticalRatio :=
    isBoundedUnder_of ⟨0, fun T => xiSimpleCriticalRatio_nonneg T⟩
  have e1 : ∀ᶠ T in atTop, (9 / 20 : ℝ) < xiSingletonFiberRatio T :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (by norm_num)
      zeta23_horizontalSingleton_density_half) hb1
  have e2 : ∀ᶠ T in atTop, (3 / 5 : ℝ) < xiSimpleCriticalRatio T :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (by norm_num)
      two_thirds_le_liminf_xiSimpleCriticalRatio) hb2
  obtain ⟨T, h1, h2, hN⟩ := (e1.and (e2.and eventually_pos_xiPosZeroCount_of_zeta23)).exists
  have hNpos : (0 : ℝ) < xiPosZeroCount T := by exact_mod_cast hN
  rw [xiSingletonFiberRatio, lt_div_iff₀ hNpos] at h1
  rw [xiSimpleCriticalRatio, lt_div_iff₀ hNpos] at h2
  have hsplit := xiPosCriticalZeroCount_add_xiOffLineZeroCount T
  have hsc := xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount T
  have hk : (xiSingletonFiberCount T : ℝ) ≤ xiOffLineZeroCount T := by exact_mod_cast hkey T
  have hs' : (xiPosCriticalZeroCount T : ℝ) + xiOffLineZeroCount T = xiPosZeroCount T := by
    exact_mod_cast hsplit
  have hsc' : (xiSimpleCriticalZeroCount T : ℝ) ≤ xiPosCriticalZeroCount T := by
    exact_mod_cast hsc
  linarith

/-! ## The cutoff law for `0 < θ < 2/3` -/

/-- An eventual bound becomes a bound on all `u > 0`, for every `θ ≤ 1`. -/
theorem exists_oneSided_of_eventually_le_wide {θ d c η C β β₁ : ℝ} (hθ1 : θ ≤ 1)
    (hη : |η| = 1) (hC : 0 ≤ C) (hββ₁ : β ≤ β₁)
    (h : ∀ᶠ x in atTop, η * (d * liouvilleTriangle x + c * cutoffHead θ x) ≤ C * x ^ β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u, 0 < u →
      η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
        ≤ C * Real.exp (β₁ * u) + K := by
  have hu : ∀ᶠ u in atTop, η * (d * liouvilleTriangle (Real.exp u) +
      c * cutoffHead θ (Real.exp u)) ≤ C * Real.exp (β₁ * u) := by
    filter_upwards [Real.tendsto_exp_atTop.eventually h, eventually_ge_atTop (0 : ℝ)]
      with u hu hu0
    rw [← Real.exp_mul] at hu
    calc _ ≤ C * Real.exp (u * β) := hu
      _ ≤ C * Real.exp (β₁ * u) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp hu
  set u₁ := max u₀ 0 with hu₁def
  set B : ℝ := 2 * |d| + |c| * (LiouvilleTriangularShortHead.squareMass + 3) with hBdef
  have hB : 0 ≤ B := by have := squareMass_pos; positivity
  refine ⟨B * Real.exp (2 * u₁), by positivity, fun u hu0 => ?_⟩
  have h4 : 0 ≤ C * Real.exp (β₁ * u) := by positivity
  by_cases hle : u₀ ≤ u
  · have := hu₀ u hle
    have : 0 ≤ B * Real.exp (2 * u₁) := by positivity
    linarith
  · have h1 := abs_cutCombination_exp_le_wide hθ1 d c hu0.le
    have h2 : Real.exp (2 * u) ≤ Real.exp (2 * u₁) :=
      Real.exp_le_exp.mpr (by have := le_max_left u₀ 0; linarith)
    have h3 : η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
        ≤ |d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)| :=
      calc _ ≤ |η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))| :=
            le_abs_self _
        _ = _ := by rw [abs_mul, hη, one_mul]
    have h5 : B * Real.exp (2 * u) ≤ B * Real.exp (2 * u₁) := mul_le_mul_of_nonneg_left h2 hB
    linarith

/-- For a singleton zero `ρ` the root-head argument `rootArg θ (1 + θ(ρ - 1)) = ρ + (1/(2θ) - ½)`
is not a zero, so its residue unit does not vanish. -/
theorem zetaResidueUnit_rootArg_ne_zero_of_singleton {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ρ : ℂ} (hρ : XiHorizontalSingletonZero ρ) (him : 0 < ρ.im) :
    RHTower.zetaResidueUnit (rootArg θ (1 + θ * (ρ - 1))) ≠ 0 := by
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  have hre : ρ.re = 1 / 2 := xiHorizontalSingletonZero_re_eq_half hρ
  set v := rootArg θ (1 + θ * (ρ - 1)) with hvdef
  have ev : v = ρ + (((1 / (2 * θ) - 1 / 2 : ℝ)) : ℂ) := by
    rw [hvdef]; unfold rootArg; push_cast; field_simp; ring
  have hc : 0 < 1 / (2 * θ) - 1 / 2 := by
    have : 1 / 2 < 1 / (2 * θ) := by rw [lt_div_iff₀ (by linarith)]; linarith
    linarith
  have hvre : v.re = 1 / 2 + (1 / (2 * θ) - 1 / 2) := by
    rw [ev, Complex.add_re, Complex.ofReal_re, hre]
  have hvim : v.im = ρ.im := by rw [ev, Complex.add_im, Complex.ofReal_im, add_zero]
  have hv1 : v ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hvim, Complex.one_im] at this; linarith
  have hζ : riemannZeta v ≠ 0 := by
    intro hz
    rcases le_or_gt 1 v.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz
    · have hxi := xi_eq_zero_of_riemannZeta_eq_zero hz (by rw [hvre]; linarith)
      have hvmem : v ∈ stripHeightFinset ρ.im :=
        mem_stripHeightFinset.mpr ⟨by rw [hvre]; linarith, h1, hvim, hxi⟩
      have hne : ρ ≠ v := by
        intro h; have := congrArg Complex.re h; rw [hre, hvre] at this; linarith
      have := two_le_xiHorizontalMultiplicity_of_ne hρ.1 hvmem hne
      rw [hρ.2] at this
      omega
  rw [zetaResidueUnit_eq hv1]
  exact mul_ne_zero (sub_ne_zero.mpr hv1) hζ

/-- A one-sided bound `η(dP + cA_θ)(x) ≤ C x^β` for large `x`, `β < 1 - θ/2`, `0 < θ < 2/3`,
`c ≠ 0`, is impossible. -/
theorem false_of_eventually_le_wide {θ d c η C β : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3)
    (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C) (hβ : β < 1 - θ / 2)
    (h : ∀ᶠ x in atTop, η * (d * liouvilleTriangle x + c * cutoffHead θ x) ≤ C * x ^ β) :
    False := by
  have hθ1 : θ < 1 := by linarith
  set m : ℝ := (max (max θ (1 - θ)) (1 / 2) + (1 - θ / 2)) / 2 with hmdef
  have hm1 : max (max θ (1 - θ)) (1 / 2) < 1 - θ / 2 := by
    refine max_lt (max_lt (by linarith) (by linarith)) (by linarith)
  set β₁ := max β m with hβ₁def
  have hmβ₁ : m ≤ β₁ := le_max_right _ _
  have hθm : θ < m := by
    have := le_max_left θ (1 - θ)
    have := le_max_left (max θ (1 - θ)) (1 / 2)
    rw [hmdef]; linarith
  have h1θm : 1 - θ < m := by
    have := le_max_right θ (1 - θ)
    have := le_max_left (max θ (1 - θ)) (1 / 2)
    rw [hmdef]; linarith
  have hβ₁ : β₁ < 1 - θ / 2 := max_lt hβ (by rw [hmdef]; linarith)
  obtain ⟨K, hK, hg⟩ := exists_oneSided_of_eventually_le_wide hθ1.le hη hC (le_max_left _ _) h
  obtain ⟨ρ, hsing, him, hwz⟩ := exists_singleton_zero_contracted_nonzero hθ0 hθ1
  have hre : ρ.re = 1 / 2 := xiHorizontalSingletonZero_re_eq_half hsing
  have hρ : riemannZeta ρ = 0 := by
    have hxi : xi ρ = 0 := (mem_stripHeightFinset.mp hsing.1).2.2.2
    exact RHTower.riemannZeta_eq_zero_iff_xi_or_trivial.mpr (Or.inl hxi)
  refine false_of_oneSided_wide (d := d) hθ0 hθ1 hc hη hC (by linarith) (by linarith) hK hρ
    (by rw [hre]) (by rw [hre]; norm_num) him.ne'
    hwz (zetaResidueUnit_rootArg_ne_zero_of_singleton hθ0 hθ1 hsing him)
    (by rw [hre]; linarith) hg

/-- **Cutoff transport law up to `θ < 2/3`.** For every `0 < θ < 2/3`, every real `d`, every
`c ≠ 0`, every `β < 1 - θ/2` and every `C ≥ 0`, the combination `dP + cA_θ` exceeds `C x^β`
and falls below `-C x^β` for arbitrarily large `x`. -/
theorem frequently_gt_and_frequently_lt_wide {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 2 / 3) (d c : ℝ)
    (hc : c ≠ 0) {β C : ℝ} (hβ : β < 1 - θ / 2) (hC : 0 ≤ C) :
    (∃ᶠ x in atTop, C * x ^ β < d * liouvilleTriangle x + c * cutoffHead θ x) ∧
      (∃ᶠ x in atTop, d * liouvilleTriangle x + c * cutoffHead θ x < -(C * x ^ β)) := by
  constructor
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le_wide hθ0 hθ hc (η := 1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx)
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le_wide hθ0 hθ hc (η := -1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [neg_one_mul, neg_le]; exact not_lt.mp hx)

end

end RHTower.LiouvilleHyperbolaCutoffWide
