import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanCrossKernel
import GaloisForLFunctions.RHTower.WeilMarkovPoleCapacity

/-!
# The self-energy of an atom is exactly logarithmic

`TheSelfEnergyOfAnAtomHasConstantOne` gives `levyEnergy g ≥ log(1/w)‖g‖²` for a bump of width `w`.
This file proves the matching upper bound: apart from `log(1/w)` the self-energy has no other
divergence, so the archimedean counterterm of an atom is `log(1/w) + O(1)` with constant exactly one.

Split the Lévy integral at `w` and `1`:

* on `(0, w]` the increments of a `K`-Lipschitz bump are small:
  `‖g − g(· + y)‖² ≤ 2Ky ‖g‖₁` (`integral_sub_shift_sq_le_lipschitz`), and `ω(y) ≤ e^{1/2}/(2y)`, so this
  range contributes at most `e^{1/2} K w ‖g‖₁`;
* on `(w, 1]` the shifts are disjoint and `ω(y) ≤ 1/(2y) + e^{1/2}/4`
  (`archLevyDensity_le_inv_two_mul_add`): at most `(log(1/w) + e^{1/2}/2)‖g‖²`;
* on `(1, ∞)`, `ω(y) ≤ e^{−y/2}/(1 − e^{−2})` (`archLevyDensity_le_exp_tail`): at most
  `4e^{−1/2}/(1 − e^{−2}) ‖g‖²`.

**The self-energy is exactly logarithmic** (`levyEnergy_atom_le`, `archForm_atom_le`):
`levyEnergy g ≤ (log(1/w) + C₀)‖g‖² + e^{1/2} K w ‖g‖₁`, `C₀ = e^{1/2}/2 + 4e^{−1/2}/(1 − e^{−2})`
(`selfEnergyConstant`). For a dilated profile `g = φ(·/w)` the last term is
`e^{1/2} Lip(φ)‖φ‖₁/‖φ‖₂² · ‖g‖²`, independent of `w`: `levyEnergy g = (log(1/w) + O_φ(1))‖g‖²`.
-/

noncomputable section

open MeasureTheory Set RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### Density bounds -/

/-- `ω(y) ≤ 1/(2y) + e^{1/2}/4` on `(0, 1]`. -/
theorem archLevyDensity_le_inv_two_mul_add {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    archLevyDensity y ≤ 1 / (2 * y) + Real.exp (1 / 2) / 4 := by
  refine (archLevyDensity_le_exp_div hy0).trans ?_
  -- `e^{y/2} − 1 ≤ (y/2) e^{y/2} ≤ (y/2) e^{1/2}`
  have h1 : Real.exp (y / 2) - 1 ≤ y / 2 * Real.exp (y / 2) := by
    have := Real.add_one_le_exp (-(y / 2))
    have e : Real.exp (-(y / 2)) * Real.exp (y / 2) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (y / 2)]
  have h2 : Real.exp (y / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  rw [div_le_iff₀ (by positivity)]
  have : (1 / (2 * y) + Real.exp (1 / 2) / 4) * (2 * y) = 1 + y / 2 * Real.exp (1 / 2) := by
    field_simp
    ring
  rw [this]
  nlinarith

/-- `ω(y) ≤ e^{−y/2}/(1 − e^{−2})` for `y ≥ 1`. -/
theorem archLevyDensity_le_exp_tail {y : ℝ} (hy1 : 1 ≤ y) :
    archLevyDensity y ≤ Real.exp (-y / 2) / (1 - Real.exp (-2)) := by
  unfold archLevyDensity
  have h2 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hle : Real.exp (-2 * y) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith) (by linarith)

/-! ### Lipschitz increments -/

/-- `‖g − g(· + y)‖² ≤ 2K|y| ‖g‖₁` for a `K`-Lipschitz `g`. -/
theorem integral_sub_shift_sq_le_lipschitz (hg : Continuous g) (hgc : HasCompactSupport g)
    {K : ℝ} (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) (y : ℝ) :
    ∫ u, (g u - g (u + y)) ^ 2 ≤ 2 * K * |y| * ∫ u, |g u| := by
  have hint1 : Integrable fun u => |g u| :=
    (hg.integrable_of_hasCompactSupport hgc).abs
  have hint2 : Integrable fun u => |g (u + y)| := hint1.comp_add_right y
  have hsq : Integrable fun u => (g u - g (u + y)) ^ 2 :=
    RHTower.WeilMarkovPole.integrable_sub_shift_sq hg hgc y
  have hpt : ∀ u, (g u - g (u + y)) ^ 2 ≤ K * |y| * (|g u| + |g (u + y)|) := by
    intro u
    have hL : |g u - g (u + y)| ≤ K * |y| := by
      have := hK u (u + y)
      rwa [show u - (u + y) = -y by ring, abs_neg] at this
    have habs : |g u - g (u + y)| ≤ |g u| + |g (u + y)| := abs_sub _ _
    calc (g u - g (u + y)) ^ 2 = |g u - g (u + y)| * |g u - g (u + y)| := by
          rw [← sq, sq_abs]
      _ ≤ (K * |y|) * (|g u| + |g (u + y)|) :=
          mul_le_mul hL habs (abs_nonneg _) (le_trans (abs_nonneg _) hL)
  calc ∫ u, (g u - g (u + y)) ^ 2 ≤ ∫ u, K * |y| * (|g u| + |g (u + y)|) :=
        integral_mono hsq ((hint1.add hint2).const_mul _) hpt
    _ = 2 * K * |y| * ∫ u, |g u| := by
        rw [integral_const_mul, integral_add hint1 hint2,
          integral_add_right_eq_self (fun u => |g u|) y]
        ring

/-! ### The upper bound -/

/-- The constant `C₀ = e^{1/2}/2 + 4e^{−1/2}/(1 − e^{−2})` of the self-energy. -/
def selfEnergyConstant : ℝ :=
  Real.exp (1 / 2) / 2 + 4 * Real.exp (-(1 / 2)) / (1 - Real.exp (-2))

/-- **The self-energy of an atom is exactly logarithmic**: for a `K`-Lipschitz `C²` bump supported
in `[0, w]`, `w ≤ 1`, `levyEnergy g ≤ (log(1/w) + C₀)‖g‖² + e^{1/2} K w ‖g‖₁`. -/
theorem levyEnergy_atom_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) :
    levyEnergy g ≤ (Real.log (1 / w) + selfEnergyConstant) * (∫ u, g u ^ 2) +
      Real.exp (1 / 2) * K * w * ∫ u, |g u| := by
  set M := ∫ u, g u ^ 2
  set A := ∫ u, |g u|
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hA : 0 ≤ A := integral_nonneg fun u => abs_nonneg _
  set L : ℝ → ℝ := fun y => archLevyDensity y * ∫ u, (g u - g (u + y)) ^ 2
  have hLint : IntegrableOn L (Ioi 0) := integrableOn_levyIntegrand hg hgc
  -- disjoint shifts beyond `w`
  have hfar : ∀ y, w < y → L y = 2 * M * archLevyDensity y := fun y hy => by
    simp only [L]
    rw [ArithmeticElectrostatics.integral_sq_sub_shift_of_disjoint hg.continuous hgc
      (bump_mul_shift_eq_zero hgsupp hy)]
    ring
  -- split `(0, ∞) = (0, w] ∪ (w, 1] ∪ (1, ∞)`
  have hsplit1 : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hsplit2 : Ioc (0 : ℝ) 1 = Ioc 0 w ∪ Ioc w 1 := (Ioc_union_Ioc_eq_Ioc hw0.le hw1).symm
  have hI1 : IntegrableOn L (Ioc 0 1) := hLint.mono_set fun y hy => hy.1
  have hI2 : IntegrableOn L (Ioi 1) :=
    hLint.mono_set fun y hy => mem_Ioi.mpr (lt_trans one_pos (mem_Ioi.mp hy))
  have hI3 : IntegrableOn L (Ioc 0 w) := hI1.mono_set fun y hy => ⟨hy.1, hy.2.trans hw1⟩
  have hI4 : IntegrableOn L (Ioc w 1) := hI1.mono_set fun y hy => ⟨lt_trans hw0 hy.1, hy.2⟩
  have hunion : ∫ y in Ioi 0, L y =
      (∫ y in Ioc 0 w, L y) + (∫ y in Ioc w 1, L y) + ∫ y in Ioi 1, L y := by
    rw [hsplit1, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2, hsplit2,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hI3 hI4]
  -- the near range `(0, w]`
  have hnear : ∫ y in Ioc 0 w, L y ≤ Real.exp (1 / 2) * K * w * A := by
    have hb : ∀ y ∈ Ioc 0 w, L y ≤ Real.exp (1 / 2) * K * A := by
      intro y hy
      have hy0 : 0 < y := hy.1
      have hd := archLevyDensity_le_sqrt_e_div hy0 (hy.2.trans hw1)
      have hinc := integral_sub_shift_sq_le_lipschitz hg.continuous hgc hK y
      rw [abs_of_pos hy0] at hinc
      have hω0 : 0 ≤ archLevyDensity y := (archLevyDensity_pos hy0).le
      calc L y ≤ archLevyDensity y * (2 * K * y * A) := mul_le_mul_of_nonneg_left hinc hω0
        _ ≤ Real.exp (1 / 2) / (2 * y) * (2 * K * y * A) :=
            mul_le_mul_of_nonneg_right hd (by positivity)
        _ = Real.exp (1 / 2) * K * A := by field_simp
    have := setIntegral_mono_on hI3 (integrableOn_const (by simp)) measurableSet_Ioc hb
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hw0.le, sub_zero] at this
    linarith
  -- the middle range `(w, 1]`
  have hmid : ∫ y in Ioc w 1, L y ≤ (Real.log (1 / w) + Real.exp (1 / 2) / 2) * M := by
    have hinv : IntegrableOn (fun y : ℝ => y⁻¹) (Ioc w 1) := by
      have hc : ContinuousOn (fun y : ℝ => y⁻¹) (Icc w 1) :=
        continuousOn_inv₀.mono fun y hy => ne_of_gt (lt_of_lt_of_le hw0 hy.1)
      exact (hc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hU : IntegrableOn (fun y : ℝ => M * y⁻¹ + M * (Real.exp (1 / 2) / 2)) (Ioc w 1) :=
      (hinv.const_mul M).add (integrableOn_const (by simp))
    have hb : ∀ y ∈ Ioc w 1, L y ≤ M * y⁻¹ + M * (Real.exp (1 / 2) / 2) := by
      intro y hy
      rw [hfar y hy.1]
      have hd := archLevyDensity_le_inv_two_mul_add (lt_trans hw0 hy.1) hy.2
      have : 2 * M * (1 / (2 * y) + Real.exp (1 / 2) / 4) =
          M * y⁻¹ + M * (Real.exp (1 / 2) / 2) := by
        field_simp
        ring
      nlinarith [mul_le_mul_of_nonneg_left hd (by linarith : (0 : ℝ) ≤ 2 * M)]
    have hval : ∫ y in Ioc w 1, (M * y⁻¹ + M * (Real.exp (1 / 2) / 2)) =
        M * Real.log (1 / w) + M * (Real.exp (1 / 2) / 2) * (1 - w) := by
      rw [integral_add (hinv.const_mul M) (integrableOn_const (by simp)), integral_const_mul,
        setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hw1,
        ← intervalIntegral.integral_of_le hw1, integral_inv_of_pos hw0 one_pos, one_div]
      ring
    have := setIntegral_mono_on hI4 hU measurableSet_Ioc hb
    rw [hval] at this
    have : M * (Real.exp (1 / 2) / 2) * (1 - w) ≤ M * (Real.exp (1 / 2) / 2) := by
      have : 0 ≤ M * (Real.exp (1 / 2) / 2) := by positivity
      nlinarith
    nlinarith
  -- the tail `(1, ∞)`
  have htail : ∫ y in Ioi 1, L y ≤ 4 * Real.exp (-(1 / 2)) / (1 - Real.exp (-2)) * M := by
    have h2 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hden : 0 < 1 - Real.exp (-2) := by linarith
    have hexp : IntegrableOn (fun y : ℝ => Real.exp (-(1 / 2) * y)) (Ioi 1) :=
      integrableOn_exp_mul_Ioi (by norm_num) 1
    have hU : IntegrableOn (fun y : ℝ => 2 * M / (1 - Real.exp (-2)) * Real.exp (-(1 / 2) * y))
        (Ioi 1) := hexp.const_mul _
    have hb : ∀ y ∈ Ioi 1, L y ≤ 2 * M / (1 - Real.exp (-2)) * Real.exp (-(1 / 2) * y) := by
      intro y hy
      have hy1 : (1 : ℝ) ≤ y := le_of_lt hy
      rw [hfar y (lt_of_le_of_lt hw1 hy)]
      have hd := archLevyDensity_le_exp_tail hy1
      rw [show -y / 2 = -(1 / 2) * y by ring] at hd
      calc 2 * M * archLevyDensity y ≤ 2 * M * (Real.exp (-(1 / 2) * y) / (1 - Real.exp (-2))) :=
            mul_le_mul_of_nonneg_left hd (by linarith)
        _ = _ := by ring
    have := setIntegral_mono_on hI2 hU measurableSet_Ioi hb
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num) 1] at this
    have e : 2 * M / (1 - Real.exp (-2)) * (-Real.exp (-(1 / 2) * 1) / -(1 / 2)) =
        4 * Real.exp (-(1 / 2)) / (1 - Real.exp (-2)) * M := by
      field_simp
      ring_nf
    linarith
  unfold levyEnergy
  rw [hunion]
  unfold selfEnergyConstant
  nlinarith

/-- **The archimedean self-energy of an atom, two-sided**:
`(2θ′(0) + log(1/w))‖g‖² ≤ archForm g ≤ (2θ′(0) + log(1/w) + C₀)‖g‖² + e^{1/2} K w ‖g‖₁`. -/
theorem archForm_atom_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hw0 : 0 < w) (hw1 : w ≤ 1) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u v, |g u - g v| ≤ K * |u - v|) :
    archForm g ≤ (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) + selfEnergyConstant) *
        (∫ u, g u ^ 2) + Real.exp (1 / 2) * K * w * ∫ u, |g u| := by
  rw [archForm_eq_levyEnergy hg hgc]
  have := levyEnergy_atom_le hg hgc hgsupp hw0 hw1 hK0 hK
  linarith

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
