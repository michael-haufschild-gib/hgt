import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewL2Form
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewCesaroLandauRecurrence
import GaloisForLFunctions.HTGeometry.BumpMollifierFamily
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Suzuki's smooth compact-test criterion

This file formalizes the smooth-test equivalence in Suzuki (2022), Theorem 1.3.  Tests are the
literal complex-valued `C_c^∞(-a,a)` functions of integral zero, and their Hermitian form is the
iterated integral in equation (1.10).  The difficult converse is obtained without assuming a
stronger abstract Weil criterion: normalized smooth two-bump differences localize the form at
`G_g(t,t) = 2 Ψ(t)`.  Positivity of every smooth test therefore forces pointwise nonnegativity of
Suzuki's displayed `Ψ`, hence RH by the exact pointwise criterion.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## Exact source test space and form -/

/-- Real form of Suzuki's kernel. -/
def suzukiScrewKernelReal (t u : ℝ) : ℝ :=
  -suzukiPsi (t - u) + suzukiPsi t + suzukiPsi u

theorem ofReal_suzukiScrewKernelReal (t u : ℝ) :
    (suzukiScrewKernelReal t u : ℂ) = suzukiScrewKernel t u := by
  simp [suzukiScrewKernelReal, suzukiScrewKernel, suzukiScrewG]

/-- Suzuki's explicit prime--Lerch function is continuous unconditionally. -/
theorem continuous_suzukiPsi : Continuous suzukiPsi := by
  have hfun : suzukiPsi = fun t : ℝ => -xiSuzukiScrewProfile t := by
    funext t
    rw [xiSuzukiScrewProfile]
    have h := congrArg Complex.re (ofReal_suzukiPsi_eq_xiScrewDivisor_all t)
    simpa using h
  rw [hfun]
  exact continuous_xiSuzukiScrewProfile.neg

theorem continuous_suzukiScrewKernelReal :
    Continuous fun p : ℝ × ℝ => suzukiScrewKernelReal p.1 p.2 := by
  unfold suzukiScrewKernelReal
  exact ((continuous_suzukiPsi.comp (continuous_fst.sub continuous_snd)).neg.add
    (continuous_suzukiPsi.comp continuous_fst)).add
    (continuous_suzukiPsi.comp continuous_snd)

/-- Literal source class `C₀(a)`: smooth compactly supported tests with support in `[-a,a]` and
zero mean. -/
structure SuzukiSmoothZeroMeanTest (a : ℝ) where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  support_subset : Function.support toFun ⊆ Icc (-a) a
  integral_zero : ∫ t : ℝ, toFun t = 0

instance (a : ℝ) : CoeFun (SuzukiSmoothZeroMeanTest a) fun _ => ℝ → ℂ :=
  ⟨SuzukiSmoothZeroMeanTest.toFun⟩

theorem SuzukiSmoothZeroMeanTest.continuous {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) : Continuous φ :=
  φ.smooth.continuous

theorem SuzukiSmoothZeroMeanTest.hasCompactSupport {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) : HasCompactSupport φ := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Icc (-a) a) isCompact_Icc ?_
  exact φ.support_subset

theorem SuzukiSmoothZeroMeanTest.integrable {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) : Integrable φ :=
  φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

/-- A literal smooth source test as an `L²(ℝ)` vector. -/
def SuzukiSmoothZeroMeanTest.toSoninL2 {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) : SoninL2 :=
  (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).toLp φ

theorem SuzukiSmoothZeroMeanTest.coeFn_toSoninL2 {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    ((φ.toSoninL2 : SoninL2) : ℝ → ℂ) =ᵐ[volume] φ :=
  MemLp.coeFn_toLp (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

theorem SuzukiSmoothZeroMeanTest.cutoff_toSoninL2_ae {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    ((suzukiCutoff a φ.toSoninL2 : SoninL2) : ℝ → ℂ) =ᵐ[volume] φ := by
  filter_upwards [indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc φ.toSoninL2,
    φ.coeFn_toSoninL2] with x hcut hcoe
  rw [hcut]
  by_cases hx : x ∈ Icc (-a) a
  · rw [indicator_of_mem hx, hcoe]
  · have hzero : φ x = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      exact hx (φ.support_subset hmem)
    rw [indicator_of_notMem hx, hzero]

/-- Suzuki (2022), equation (1.10), on the literal smooth source class. -/
def suzukiScrewSmoothForm {a : ℝ}
    (φ₁ φ₂ : SuzukiSmoothZeroMeanTest a) : ℂ :=
  ∫ t : ℝ, ∫ u : ℝ,
    suzukiScrewKernel t u * φ₁ u * (starRingEnd ℂ) (φ₂ t)

/-- The function-level source integral agrees exactly with the zero-extended `L²` form. -/
theorem suzukiScrewSmoothForm_eq_l2 {a : ℝ}
    (φ₁ φ₂ : SuzukiSmoothZeroMeanTest a) :
    suzukiScrewSmoothForm φ₁ φ₂ =
      suzukiScrewL2Form a φ₁.toSoninL2 φ₂.toSoninL2 := by
  rw [suzukiScrewSmoothForm, suzukiScrewL2Form]
  apply integral_congr_ae
  filter_upwards [φ₂.cutoff_toSoninL2_ae] with t ht
  apply integral_congr_ae
  filter_upwards [φ₁.cutoff_toSoninL2_ae] with u hu
  rw [hu, ht]

/-- Exact nonnegativity assertion in Suzuki (2022), Theorem 1.3. -/
def SuzukiSmoothTestFormNonnegative : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ φ : SuzukiSmoothZeroMeanTest a,
    0 ≤ (suzukiScrewSmoothForm φ φ).re

theorem suzukiSmoothTestFormNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) : SuzukiSmoothTestFormNonnegative := by
  intro a ha φ
  rw [suzukiScrewSmoothForm_eq_l2]
  exact suzukiScrewL2Form_nonneg_of_rh ha.le hRH φ.toSoninL2

/-! ## Normalized two-bump localization -/

/-- Unit-mass smooth bump of width `ε`, translated to the center `c`. -/
def suzukiCenteredBump {ε : ℝ} (hε : 0 < ε) (c x : ℝ) : ℝ :=
  bumpMollifier hε (x - c)

theorem continuous_suzukiCenteredBump {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Continuous (suzukiCenteredBump hε c) := by
  unfold suzukiCenteredBump
  exact (continuous_bumpMollifier hε).comp (continuous_id.sub continuous_const)

theorem contDiff_suzukiCenteredBump {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiCenteredBump hε c) := by
  unfold suzukiCenteredBump bumpMollifier
  exact (widthBump hε).contDiff_normed.comp
    (contDiff_id.sub contDiff_const)

theorem integrable_suzukiCenteredBump {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Integrable (suzukiCenteredBump hε c) := by
  change Integrable (fun x : ℝ => bumpMollifier hε (x + -c))
  exact (integrable_bumpMollifier hε).comp_add_right (-c)

theorem integral_suzukiCenteredBump {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    (∫ x : ℝ, suzukiCenteredBump hε c x) = 1 := by
  change (∫ x : ℝ, bumpMollifier hε (x - c)) = 1
  rw [integral_sub_right_eq_self, integral_bumpMollifier hε]

theorem suzukiCenteredBump_nonneg {ε : ℝ} (hε : 0 < ε) (c x : ℝ) :
    0 ≤ suzukiCenteredBump hε c x :=
  nonneg_bumpMollifier hε _

theorem abs_sub_center_le_of_suzukiCenteredBump_ne_zero
    {ε : ℝ} (hε : 0 < ε) {c x : ℝ}
    (hx : suzukiCenteredBump hε c x ≠ 0) : |x - c| ≤ ε := by
  by_contra hnot
  rw [not_le] at hnot
  exact hx (bumpMollifier_eq_zero hε hnot)

/-- Product-measure average of the real Suzuki kernel around `(c,d)`. -/
def suzukiLocalizedKernelAverage {ε : ℝ} (hε : 0 < ε) (c d : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ,
    suzukiScrewKernelReal p.1 p.2 *
      suzukiCenteredBump hε c p.1 * suzukiCenteredBump hε d p.2 ∂(volume.prod volume)

theorem integrable_suzukiLocalizedKernel {ε : ℝ} (hε : 0 < ε) (c d : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      suzukiScrewKernelReal p.1 p.2 *
        suzukiCenteredBump hε c p.1 * suzukiCenteredBump hε d p.2)
      (volume.prod volume) := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      suzukiScrewKernelReal p.1 p.2 *
        suzukiCenteredBump hε c p.1 * suzukiCenteredBump hε d p.2) := by
    exact (continuous_suzukiScrewKernelReal.mul
      ((continuous_suzukiCenteredBump hε c).comp continuous_fst)).mul
      ((continuous_suzukiCenteredBump hε d).comp continuous_snd)
  apply hcont.integrable_of_hasCompactSupport
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Icc (c - ε) (c + ε) ×ˢ Icc (d - ε) (d + ε))
    (isCompact_Icc.prod isCompact_Icc) ?_
  intro p hp
  have hmul : suzukiCenteredBump hε c p.1 * suzukiCenteredBump hε d p.2 ≠ 0 := by
    intro hz
    apply hp
    change suzukiScrewKernelReal p.1 p.2 *
      suzukiCenteredBump hε c p.1 * suzukiCenteredBump hε d p.2 = 0
    calc
      _ = suzukiScrewKernelReal p.1 p.2 *
          (suzukiCenteredBump hε c p.1 * suzukiCenteredBump hε d p.2) := by ring
      _ = 0 := by rw [hz, mul_zero]
  have hc0 : suzukiCenteredBump hε c p.1 ≠ 0 := (mul_ne_zero_iff.mp hmul).1
  have hd0 : suzukiCenteredBump hε d p.2 ≠ 0 := (mul_ne_zero_iff.mp hmul).2
  have hc := abs_sub_center_le_of_suzukiCenteredBump_ne_zero hε hc0
  have hd := abs_sub_center_le_of_suzukiCenteredBump_ne_zero hε hd0
  rw [abs_le] at hc hd
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem integral_suzukiCenteredBump_product {ε : ℝ} (hε : 0 < ε) (c d : ℝ) :
    (∫ p : ℝ × ℝ,
      suzukiCenteredBump hε c p.1 * suzukiCenteredBump hε d p.2
        ∂(volume.prod volume)) = 1 := by
  rw [integral_prod_mul, integral_suzukiCenteredBump hε c,
    integral_suzukiCenteredBump hε d, one_mul]

/-- A localized kernel average differs from its center value by no more than the local
oscillation of the kernel on the supporting square. -/
theorem abs_suzukiLocalizedKernelAverage_sub_le
    {ε η : ℝ} (hε : 0 < ε) (_hη : 0 ≤ η) (c d : ℝ)
    (hlocal : ∀ x y : ℝ, |x - c| ≤ ε → |y - d| ≤ ε →
      |suzukiScrewKernelReal x y - suzukiScrewKernelReal c d| ≤ η) :
    |suzukiLocalizedKernelAverage hε c d - suzukiScrewKernelReal c d| ≤ η := by
  let w : ℝ × ℝ → ℝ := fun p =>
    suzukiCenteredBump hε c p.1 * suzukiCenteredBump hε d p.2
  let F : ℝ × ℝ → ℝ := fun p => suzukiScrewKernelReal p.1 p.2 * w p
  let C : ℝ × ℝ → ℝ := fun p => suzukiScrewKernelReal c d * w p
  let D : ℝ × ℝ → ℝ := fun p =>
    (suzukiScrewKernelReal p.1 p.2 - suzukiScrewKernelReal c d) * w p
  have hcInt : Integrable (suzukiCenteredBump hε c) :=
    integrable_suzukiCenteredBump hε c
  have hdInt : Integrable (suzukiCenteredBump hε d) :=
    integrable_suzukiCenteredBump hε d
  have hwInt : Integrable w (volume.prod volume) := hcInt.mul_prod hdInt
  have hFInt : Integrable F (volume.prod volume) := by
    simpa only [F, w, mul_assoc] using integrable_suzukiLocalizedKernel hε c d
  have hCInt : Integrable C (volume.prod volume) := hwInt.const_mul _
  have hDInt : Integrable D (volume.prod volume) := by
    refine (hFInt.sub hCInt).congr (ae_of_all _ fun p => ?_)
    change F p - C p = D p
    dsimp only [F, C, D]
    ring
  have hwMass : (∫ p : ℝ × ℝ, w p ∂(volume.prod volume)) = 1 := by
    simpa only [w] using integral_suzukiCenteredBump_product hε c d
  have hdifference :
      suzukiLocalizedKernelAverage hε c d - suzukiScrewKernelReal c d =
        ∫ p : ℝ × ℝ, D p ∂(volume.prod volume) := by
    have hcenter : (∫ p : ℝ × ℝ, C p ∂(volume.prod volume)) =
        suzukiScrewKernelReal c d := by
      rw [show C = fun p => suzukiScrewKernelReal c d * w p by rfl,
        integral_const_mul, hwMass, mul_one]
    have havg : suzukiLocalizedKernelAverage hε c d =
        ∫ p : ℝ × ℝ, F p ∂(volume.prod volume) := by
      rw [suzukiLocalizedKernelAverage]
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [F, w]
      ring
    rw [havg]
    rw [← hcenter, ← integral_sub hFInt hCInt]
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [F, C, D]
    ring
  rw [hdifference, ← Real.norm_eq_abs]
  calc
    ‖∫ p : ℝ × ℝ, D p ∂(volume.prod volume)‖ ≤
        ∫ p : ℝ × ℝ, ‖D p‖ ∂(volume.prod volume) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, η * w p ∂(volume.prod volume) := by
      refine integral_mono hDInt.norm (hwInt.const_mul η) ?_
      intro p
      have hcNonneg := suzukiCenteredBump_nonneg hε c p.1
      have hdNonneg := suzukiCenteredBump_nonneg hε d p.2
      by_cases hc0 : suzukiCenteredBump hε c p.1 = 0
      · simp [D, w, hc0]
      by_cases hd0 : suzukiCenteredBump hε d p.2 = 0
      · simp [D, w, hd0]
      have hc := abs_sub_center_le_of_suzukiCenteredBump_ne_zero hε hc0
      have hd := abs_sub_center_le_of_suzukiCenteredBump_ne_zero hε hd0
      have hK := hlocal p.1 p.2 hc hd
      dsimp only [D, w]
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hcNonneg, abs_of_nonneg hdNonneg]
      exact mul_le_mul_of_nonneg_right hK (mul_nonneg hcNonneg hdNonneg)
    _ = η := by
      rw [integral_const_mul, hwMass, mul_one]

/-- Continuity supplies a width threshold on which every narrower smooth kernel average is close
to its point value. -/
theorem exists_width_suzukiLocalizedKernelAverage_close
    {η : ℝ} (hη : 0 < η) (c d : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε < δ →
      |suzukiLocalizedKernelAverage hε c d - suzukiScrewKernelReal c d| ≤ η := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp
    continuous_suzukiScrewKernelReal.continuousAt η hη
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  apply abs_suzukiLocalizedKernelAverage_sub_le hε hη.le c d
  intro x y hx hy
  have hdist : dist (x, y) (c, d) < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact lt_of_le_of_lt (max_le hx hy) hεδ
  have hout := hclose hdist
  simpa only [Real.dist_eq] using hout.le

/-- Smooth zero-mean difference of two normalized bumps, centered at `t` and `0`. -/
def suzukiTwoBumpTest {a ε t : ℝ} (hε : 0 < ε)
    (hmargin : |t| + ε < a) : SuzukiSmoothZeroMeanTest a where
  toFun := fun x => ((suzukiCenteredBump hε t x - suzukiCenteredBump hε 0 x : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp
    ((contDiff_suzukiCenteredBump hε t).sub (contDiff_suzukiCenteredBump hε 0))
  support_subset := by
    intro x hx
    have hdiff : suzukiCenteredBump hε t x - suzukiCenteredBump hε 0 x ≠ 0 := by
      intro hzero
      apply hx
      simp [hzero]
    have hor : suzukiCenteredBump hε t x ≠ 0 ∨ suzukiCenteredBump hε 0 x ≠ 0 := by
      by_cases htzero : suzukiCenteredBump hε t x = 0
      · right
        intro h0zero
        exact hdiff (by rw [htzero, h0zero, sub_zero])
      · exact Or.inl htzero
    have hxa : |x| < a := by
      rcases hor with ht0 | h00
      · have hxt := abs_sub_center_le_of_suzukiCenteredBump_ne_zero hε ht0
        calc
          |x| = |(x - t) + t| := by ring_nf
          _ ≤ |x - t| + |t| := abs_add_le _ _
          _ ≤ ε + |t| := by linarith
          _ < a := by linarith
      · have hx0 := abs_sub_center_le_of_suzukiCenteredBump_ne_zero hε h00
        simp only [sub_zero] at hx0
        exact hx0.trans_lt (by linarith [abs_nonneg t])
    exact Ioo_subset_Icc_self (abs_lt.mp hxa)
  integral_zero := by
    have htInt := integrable_suzukiCenteredBump hε t
    have h0Int := integrable_suzukiCenteredBump hε 0
    have hfun : (fun x : ℝ =>
        ((suzukiCenteredBump hε t x - suzukiCenteredBump hε 0 x : ℝ) : ℂ)) =
        fun x : ℝ => (suzukiCenteredBump hε t x : ℂ) -
          (suzukiCenteredBump hε 0 x : ℂ) := by
      funext x
      push_cast
      rfl
    have htMass : (∫ x : ℝ, (suzukiCenteredBump hε t x : ℂ)) = 1 := by
      exact_mod_cast integral_suzukiCenteredBump hε t
    have h0Mass : (∫ x : ℝ, (suzukiCenteredBump hε 0 x : ℂ)) = 1 := by
      exact_mod_cast integral_suzukiCenteredBump hε 0
    rw [hfun, integral_sub htInt.ofReal h0Int.ofReal, htMass, h0Mass, sub_self]

/-- The equation-(1.10) value of a two-bump difference is the alternating sum of the four
localized kernel averages. -/
theorem suzukiScrewSmoothForm_twoBump
    {a ε t : ℝ} (hε : 0 < ε) (hmargin : |t| + ε < a) :
    suzukiScrewSmoothForm (suzukiTwoBumpTest hε hmargin)
        (suzukiTwoBumpTest hε hmargin) =
      ((suzukiLocalizedKernelAverage hε t t -
        suzukiLocalizedKernelAverage hε t 0 -
        suzukiLocalizedKernelAverage hε 0 t +
        suzukiLocalizedKernelAverage hε 0 0 : ℝ) : ℂ) := by
  let L : ℝ → ℝ → ℝ × ℝ → ℝ := fun c d p =>
    suzukiScrewKernelReal p.1 p.2 *
      suzukiCenteredBump hε c p.1 * suzukiCenteredBump hε d p.2
  let H : ℝ × ℝ → ℝ := fun p =>
    suzukiScrewKernelReal p.1 p.2 *
      (suzukiCenteredBump hε t p.1 - suzukiCenteredBump hε 0 p.1) *
      (suzukiCenteredBump hε t p.2 - suzukiCenteredBump hε 0 p.2)
  have hL (c d : ℝ) : Integrable (L c d) (volume.prod volume) := by
    simpa only [L] using integrable_suzukiLocalizedKernel hε c d
  have hHrepr : H = fun p => L t t p - L t 0 p - L 0 t p + L 0 0 p := by
    funext p
    dsimp only [H, L]
    ring
  have hHInt : Integrable H (volume.prod volume) := by
    rw [hHrepr]
    exact (((hL t t).sub (hL t 0)).sub (hL 0 t)).add (hL 0 0)
  let HC : ℝ × ℝ → ℂ := fun p => (H p : ℂ)
  have hHCInt : Integrable HC (volume.prod volume) := hHInt.ofReal
  have hsourceProd :
      suzukiScrewSmoothForm (suzukiTwoBumpTest hε hmargin)
          (suzukiTwoBumpTest hε hmargin) =
        ∫ p : ℝ × ℝ, HC p ∂(volume.prod volume) := by
    rw [suzukiScrewSmoothForm]
    rw [integral_prod HC hHCInt]
    apply integral_congr_ae
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    dsimp only [HC, H, suzukiTwoBumpTest]
    rw [← ofReal_suzukiScrewKernelReal]
    simp only [conj_ofReal]
    push_cast
    ring
  rw [hsourceProd]
  have hcast : (∫ p : ℝ × ℝ, HC p ∂(volume.prod volume)) =
      ((∫ p : ℝ × ℝ, H p ∂(volume.prod volume) : ℝ) : ℂ) := by
    exact integral_ofReal
  rw [hcast]
  congr 1
  rw [hHrepr]
  have haverage (c d : ℝ) :
      (∫ p : ℝ × ℝ, L c d p ∂(volume.prod volume)) =
        suzukiLocalizedKernelAverage hε c d := by
    rfl
  have hsub₁ :
      (∫ p : ℝ × ℝ, (L t t - L t 0) p ∂(volume.prod volume)) =
        (∫ p : ℝ × ℝ, L t t p ∂(volume.prod volume)) -
          ∫ p : ℝ × ℝ, L t 0 p ∂(volume.prod volume) :=
    integral_sub (hL t t) (hL t 0)
  have hsub₂ :
      (∫ p : ℝ × ℝ, ((L t t - L t 0) - L 0 t) p ∂(volume.prod volume)) =
        (∫ p : ℝ × ℝ, (L t t - L t 0) p ∂(volume.prod volume)) -
          ∫ p : ℝ × ℝ, L 0 t p ∂(volume.prod volume) :=
    integral_sub ((hL t t).sub (hL t 0)) (hL 0 t)
  have hadd :
      (∫ p : ℝ × ℝ, (((L t t - L t 0) - L 0 t) + L 0 0) p
        ∂(volume.prod volume)) =
        (∫ p : ℝ × ℝ, ((L t t - L t 0) - L 0 t) p ∂(volume.prod volume)) +
          ∫ p : ℝ × ℝ, L 0 0 p ∂(volume.prod volume) :=
    integral_add (((hL t t).sub (hL t 0)).sub (hL 0 t)) (hL 0 0)
  calc
    (∫ p : ℝ × ℝ, (fun p => L t t p - L t 0 p - L 0 t p + L 0 0 p) p
        ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, ((((L t t - L t 0) - L 0 t) + L 0 0) p)
          ∂(volume.prod volume) := by rfl
    _ = (∫ p : ℝ × ℝ, L t t p ∂(volume.prod volume)) -
          (∫ p : ℝ × ℝ, L t 0 p ∂(volume.prod volume)) -
          (∫ p : ℝ × ℝ, L 0 t p ∂(volume.prod volume)) +
          (∫ p : ℝ × ℝ, L 0 0 p ∂(volume.prod volume)) := by
      rw [hadd, hsub₂, hsub₁]
    _ = _ := by
      rw [haverage t t, haverage t 0, haverage 0 t, haverage 0 0]

/-! ## The exact converse and Theorem 1.3 -/

/-- Positivity on every literal smooth zero-mean compact test forces pointwise nonnegativity of
Suzuki's `Ψ`.  This is the rigorous two-bump localization step. -/
theorem suzukiPsiPointwiseNonnegative_of_smoothTestFormNonnegative
    (hsource : SuzukiSmoothTestFormNonnegative) :
    SuzukiPsiPointwiseNonnegative := by
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · simp
  by_contra hneg
  rw [not_le] at hneg
  let η : ℝ := -suzukiPsi t / 8
  have hη : 0 < η := by
    dsimp only [η]
    linarith
  obtain ⟨δtt, hδtt, hcloseTT⟩ :=
    exists_width_suzukiLocalizedKernelAverage_close hη t t
  obtain ⟨δt0, hδt0, hcloseT0⟩ :=
    exists_width_suzukiLocalizedKernelAverage_close hη t 0
  obtain ⟨δ0t, hδ0t, hclose0T⟩ :=
    exists_width_suzukiLocalizedKernelAverage_close hη 0 t
  obtain ⟨δ00, hδ00, hclose00⟩ :=
    exists_width_suzukiLocalizedKernelAverage_close hη 0 0
  let δ : ℝ := min (min δtt δt0) (min δ0t δ00)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (lt_min hδtt hδt0) (lt_min hδ0t hδ00)
  let ε : ℝ := min δ 1 / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  have hεδ : ε < δ := by
    dsimp only [ε]
    have hm : 0 < min δ 1 := lt_min hδ one_pos
    have hle := min_le_left δ 1
    linarith
  have hεone : ε < 1 := by
    dsimp only [ε]
    have hm : 0 < min δ 1 := lt_min hδ one_pos
    have hle := min_le_right δ 1
    linarith
  have hεδtt : ε < δtt := hεδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεδt0 : ε < δt0 := hεδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hεδ0t : ε < δ0t := hεδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεδ00 : ε < δ00 := hεδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hTT := hcloseTT ε hε hεδtt
  have hT0 := hcloseT0 ε hε hεδt0
  have h0T := hclose0T ε hε hεδ0t
  have h00 := hclose00 ε hε hεδ00
  have hKTT : suzukiScrewKernelReal t t = 2 * suzukiPsi t := by
    simp [suzukiScrewKernelReal]
    ring
  have hKT0 : suzukiScrewKernelReal t 0 = 0 := by
    simp [suzukiScrewKernelReal]
  have hK0T : suzukiScrewKernelReal 0 t = 0 := by
    simp [suzukiScrewKernelReal]
  have hK00 : suzukiScrewKernelReal 0 0 = 0 := by
    simp [suzukiScrewKernelReal]
  rw [hKTT] at hTT
  rw [hKT0] at hT0
  rw [hK0T] at h0T
  rw [hK00] at h00
  have hQneg :
      suzukiLocalizedKernelAverage hε t t -
        suzukiLocalizedKernelAverage hε t 0 -
        suzukiLocalizedKernelAverage hε 0 t +
        suzukiLocalizedKernelAverage hε 0 0 < 0 := by
    have htt := abs_le.mp hTT
    have ht0 := abs_le.mp hT0
    have h0t := abs_le.mp h0T
    have hzero := abs_le.mp h00
    dsimp only [η] at htt ht0 h0t hzero
    linarith
  let a : ℝ := |t| + 1
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hmargin : |t| + ε < a := by
    dsimp only [a]
    linarith
  have hform := hsource a ha (suzukiTwoBumpTest hε hmargin)
  rw [suzukiScrewSmoothForm_twoBump hε hmargin] at hform
  norm_num at hform
  linarith

/-- The literal smooth-test condition implies RH. -/
theorem riemannHypothesis_of_suzukiSmoothTestFormNonnegative
    (hsource : SuzukiSmoothTestFormNonnegative) : RiemannHypothesis :=
  riemannHypothesis_of_suzukiPsiPointwiseNonnegative
    (suzukiPsiPointwiseNonnegative_of_smoothTestFormNonnegative hsource)

/-- **Suzuki (2022), Theorem 1.3, exact smooth-test equivalence.** -/
theorem riemannHypothesis_iff_suzukiSmoothTestFormNonnegative :
    RiemannHypothesis ↔ SuzukiSmoothTestFormNonnegative :=
  ⟨suzukiSmoothTestFormNonnegative_of_riemannHypothesis,
    riemannHypothesis_of_suzukiSmoothTestFormNonnegative⟩

/-- Exact conjunction of the equivalence and strict `L²(-a,a)` clause in Suzuki (2022),
Theorem 1.3. -/
def SuzukiTheoremOneThreeConclusion : Prop :=
  SuzukiSmoothTestFormNonnegative ∧
    ∀ (a : ℝ), 0 < a → ∀ f : SuzukiApertureL2 a,
      (f : SoninL2) ≠ 0 → 0 < (suzukiScrewL2Form a f f).re

/-- **Suzuki (2022), Theorem 1.3, full formal capstone.**  RH is equivalent to the literal
smooth-test positivity statement, and under the same condition the form is strictly positive on
every nonzero vector in every exact `L²(-a,a)` aperture. -/
theorem riemannHypothesis_iff_suzukiTheoremOneThreeConclusion :
    RiemannHypothesis ↔ SuzukiTheoremOneThreeConclusion := by
  constructor
  · intro hRH
    refine ⟨suzukiSmoothTestFormNonnegative_of_riemannHypothesis hRH, ?_⟩
    intro a ha f hf
    exact suzuki_theorem_one_three_strict_l2 hRH ha f hf
  · exact fun h => riemannHypothesis_of_suzukiSmoothTestFormNonnegative h.1

end RHTower
