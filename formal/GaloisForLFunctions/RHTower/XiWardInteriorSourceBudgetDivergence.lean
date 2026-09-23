import GaloisForLFunctions.RHTower.XiWardInteriorReflectionAbsorption
import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary
import GaloisForLFunctions.HTGeometry.FisherOneCornerCoareaTransform

/-!
# Vertical divergence of the reflected CCM source majorant

Functional-equation absorption bounds the real part of the interior Ward
symbol by `xiWardInteriorSourceArithmeticBound`, an expression involving
only pole, Gamma, and von Mangoldt source data.  This file determines its
large-height behavior on every fixed source line.

The pole terms have nonnegative real part.  The von Mangoldt Dirichlet
series is uniformly bounded on a fixed line strictly right of `1`, whereas
the real Gamma logarithmic derivative diverges.  Consequently the complete
source majorant diverges to `+∞`.

Thus this particular reflected source majorant cannot itself supply a
height-uniform four-unit boundary budget.  Any successful CCM boundary
lift must retain a cancellation or an operator-valued channel discarded by
the real-part absorption inequality.
-/

open Complex Filter Topology MeasureTheory
open scoped Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The real part of the completed real-Gamma logarithmic derivative tends
to `+∞` on every fixed upper vertical line whose real part is positive. -/
theorem re_logDeriv_Gammaℝ_vertical_tendsto_atTop
    {h : ℝ} (hh : 1 / 2 < h) :
    Tendsto
      (fun t : ℝ =>
        (logDeriv Complex.Gammaℝ
          ((((1 / 2 + h : ℝ) : ℂ) + I * (t : ℂ)))).re)
      atTop atTop := by
  have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hpsi0 :=
    GaloisForLFunctions.re_digamma_vertical_tendsto_atTop
      (show 0 ≤ (1 / 2 + h) / 2 by linarith)
  have hpsi :
      Tendsto
        (fun t : ℝ =>
          (Complex.digamma
            (((((1 / 2 + h) / 2 : ℝ) : ℂ)) +
              ((t / 2 : ℝ) : ℂ) * I)).re)
        atTop atTop :=
    hpsi0.comp hhalf
  have hpsiDiv :
      Tendsto
        (fun t : ℝ =>
          (Complex.digamma
            (((((1 / 2 + h) / 2 : ℝ) : ℂ)) +
              ((t / 2 : ℝ) : ℂ) * I)).re / 2)
        atTop atTop :=
    hpsi.atTop_div_const (by norm_num)
  have hshift :=
    tendsto_atTop_add_const_left atTop (-(Real.log Real.pi / 2)) hpsiDiv
  apply hshift.congr'
  filter_upwards with t
  rw [logDeriv_Gammaℝ_eq]
  · simp only [Complex.add_re, Complex.neg_re, Complex.div_re,
      Complex.ofReal_re, Complex.ofReal_im]
    have harg :
        ((((1 / 2 + h : ℝ) : ℂ) + I * (t : ℂ)) / 2) =
          ((((1 / 2 + h) / 2 : ℝ) : ℂ) +
            ((t / 2 : ℝ) : ℂ) * I) := by
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im]
    rw [harg]
    simp
    ring
  · simp [Complex.add_re, Complex.mul_re]
    linarith

/-- On every fixed interior source line, the source-only majorant obtained
by reflecting and absorbing the complementary Xi divisor diverges to
`+∞` with height. -/
theorem xiWardInteriorSourceArithmeticBound_vertical_tendsto_atTop
    {h : ℝ} (hh : 1 / 2 < h) :
    Tendsto
      (fun t : ℝ =>
        xiWardInteriorSourceArithmeticBound
          ((h : ℂ) + I * (t : ℂ)))
      atTop atTop := by
  let C : ℝ :=
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) /
      (n : ℝ) ^ (1 / 2 + h)
  have hgamma := re_logDeriv_Gammaℝ_vertical_tendsto_atTop hh
  have hlower :
      Tendsto
        (fun t : ℝ =>
          ((logDeriv Complex.Gammaℝ
            ((((1 / 2 + h : ℝ) : ℂ) + I * (t : ℂ)))).re - C) * 2)
        atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-C) hgamma).atTop_mul_const
      (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards with t
  let s : ℂ := (((1 / 2 + h : ℝ) : ℂ) + I * (t : ℂ))
  have hsre : s.re = 1 / 2 + h := by
    simp [s, Complex.add_re, Complex.mul_re]
  have hsone : 1 < s.re := by rw [hsre]; linarith
  have hspos : 0 < s.re := by linarith
  have hsm1pos : 0 < (s - 1).re := by
    rw [Complex.sub_re, hsre]
    norm_num
    linarith
  have hinv0 : 0 ≤ s⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg hspos.le (Complex.normSq_nonneg s)
  have hinv1 : 0 ≤ (s - 1)⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg hsm1pos.le (Complex.normSq_nonneg (s - 1))
  have hLnorm := norm_LSeries_vonMangoldt_le hsone
  rw [hsre] at hLnorm
  have hLre :
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤ C :=
    (Complex.re_le_norm _).trans hLnorm
  unfold xiWardInteriorSourceArithmeticBound
  have hnode :
      ((1 / 2 : ℂ) + ((h : ℂ) + I * (t : ℂ))) = s := by
    dsimp [s]
    push_cast
    ring
  rw [hnode]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, Complex.add_re, Complex.sub_re]
  nlinarith

/-- The divergence is not merely an artifact of the reflected majorant.
On every fixed Euler line strictly right of `1`, the real part of the
actual completed Xi logarithmic current tends to `+∞`.  The Gamma current
forces the divergence while the absolutely convergent von Mangoldt current
is uniformly bounded. -/
theorem re_logDeriv_xi_vertical_tendsto_atTop
    {h : ℝ} (hh : 1 / 2 < h) :
    Tendsto
      (fun t : ℝ =>
        (logDeriv xi
          ((((1 / 2 + h : ℝ) : ℂ) + I * (t : ℂ)))).re)
      atTop atTop := by
  let C : ℝ :=
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) /
      (n : ℝ) ^ (1 / 2 + h)
  have hgamma := re_logDeriv_Gammaℝ_vertical_tendsto_atTop hh
  have hlower :
      Tendsto
        (fun t : ℝ =>
          (logDeriv Complex.Gammaℝ
            ((((1 / 2 + h : ℝ) : ℂ) + I * (t : ℂ)))).re - C)
        atTop atTop :=
    tendsto_atTop_add_const_right atTop (-C) hgamma
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards with t
  let s : ℂ := (((1 / 2 + h : ℝ) : ℂ) + I * (t : ℂ))
  have hsre : s.re = 1 / 2 + h := by
    simp [s, Complex.add_re, Complex.mul_re]
  have hsone : 1 < s.re := by rw [hsre]; linarith
  have hspos : 0 < s.re := by linarith
  have hsm1pos : 0 < (s - 1).re := by
    rw [Complex.sub_re, hsre]
    norm_num
    linarith
  have hinv0 : 0 ≤ s⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg hspos.le (Complex.normSq_nonneg s)
  have hinv1 : 0 ≤ (s - 1)⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg hsm1pos.le (Complex.normSq_nonneg (s - 1))
  have hLnorm := norm_LSeries_vonMangoldt_le hsone
  rw [hsre] at hLnorm
  have hLreLower :
      -C ≤
        -(LSeries
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re := by
    have hre :
        (LSeries
          (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s).re ≤ C :=
      (Complex.re_le_norm _).trans hLnorm
    linarith
  rw [logDeriv_xi_eq_arithmetic hsone]
  simp only [Complex.add_re, Complex.sub_re]
  linarith

/-- Consequently the actual completed Xi logarithmic current has unbounded
norm on every fixed Euler line.  This rules out any unsmoothed finite-energy
Hardy/Laplace realization of the *full* source current; a viable four-unit
construction must project away the Gamma/polar local channel before taking
the Hilbert norm. -/
theorem norm_logDeriv_xi_vertical_tendsto_atTop
    {h : ℝ} (hh : 1 / 2 < h) :
    Tendsto
      (fun t : ℝ =>
        ‖logDeriv xi
          ((((1 / 2 + h : ℝ) : ℂ) + I * (t : ℂ)))‖)
      atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (re_logDeriv_xi_vertical_tendsto_atTop hh)
  exact Filter.Eventually.of_forall fun t =>
    Complex.re_le_norm _

/-- Every half-line Cauchy feature on one fixed vertical line has the same
Hilbert norm.  This is the exact Paley--Wiener evaluation constant, obtained
from the already-proved Cauchy Gram rather than from a pointwise estimate. -/
theorem norm_sq_halfLineLaplaceFeature_vertical
    {h t : ℝ} (hh : 0 < h) :
    ‖halfLineLaplaceFeature
        ((h : ℂ) + I * (t : ℂ)) (by simp; exact hh)‖ ^ (2 : ℕ) =
      1 / (2 * h) := by
  have hi := inner_halfLineLaplaceFeature
    (w := ((h : ℂ) + I * (t : ℂ)))
    (z := ((h : ℂ) + I * (t : ℂ)))
    (by simp; exact hh) (by simp; exact hh)
  rw [inner_self_eq_norm_sq_to_K] at hi
  have hden :
      ((h : ℂ) + I * (t : ℂ)) +
          star ((h : ℂ) + I * (t : ℂ)) =
        ((2 * h : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [hden] at hi
  norm_cast at hi
  exact Complex.ofReal_injective hi

theorem norm_halfLineLaplaceFeature_vertical_eq
    {h t : ℝ} (hh : 0 < h) :
    ‖halfLineLaplaceFeature
        ((h : ℂ) + I * (t : ℂ)) (by simp; exact hh)‖ =
      ‖halfLineLaplaceFeature (h : ℂ) (by simpa using hh)‖ := by
  have hleft := norm_sq_halfLineLaplaceFeature_vertical
    (h := h) (t := t) hh
  have hright := norm_sq_halfLineLaplaceFeature_vertical
    (h := h) (t := 0) hh
  simp only [ofReal_zero, mul_zero, add_zero] at hright
  nlinarith [norm_nonneg
    (halfLineLaplaceFeature
      ((h : ℂ) + I * (t : ℂ)) (by simp; exact hh)),
    norm_nonneg (halfLineLaplaceFeature (h : ℂ) (by simpa using hh))]

/-- **No unsmoothed Hardy realization of the full completed source
current.**  On no fixed Euler line can one finite-energy half-line source
have Laplace transform equal to the full Xi logarithmic current.  Cauchy
evaluation makes every such represented column uniformly bounded in the
vertical direction, while the actual source current diverges there.

This is a definition-level obstruction to projecting the already-scalarized
full Möbius--Gamma current.  The anti-causal projection must act before the
Gamma/polar local channel is scalarized. -/
theorem not_exists_halfLineLaplaceSource_logDeriv_xi_vertical
    {h : ℝ} (hh : 1 < h) :
    ¬ ∃ source : Lp ℂ 2 halfLineLaplaceMeasure,
      ∀ t : ℝ,
        halfLineLaplaceTransform source
            ((h : ℂ) + I * (t : ℂ)) (by simp; linarith) =
          logDeriv xi ((h : ℂ) + I * (t : ℂ)) := by
  rintro ⟨source, hsource⟩
  let B : ℝ :=
    ‖halfLineLaplaceFeature (h : ℂ) (by simpa using (by linarith : 0 < h))‖ *
      ‖source‖
  have hbound : ∀ t : ℝ,
      ‖logDeriv xi ((h : ℂ) + I * (t : ℂ))‖ ≤ B := by
    intro t
    rw [← hsource t]
    change ‖inner ℂ
      (halfLineLaplaceFeature
        ((h : ℂ) + I * (t : ℂ)) (by simp; linarith)) source‖ ≤ B
    calc
      _ ≤ ‖halfLineLaplaceFeature
          ((h : ℂ) + I * (t : ℂ)) (by simp; linarith)‖ * ‖source‖ :=
        norm_inner_le_norm _ _
      _ = B := by
        rw [norm_halfLineLaplaceFeature_vertical_eq
          (by linarith : 0 < h)]
  have hdiv :
      Tendsto
        (fun t : ℝ => ‖logDeriv xi ((h : ℂ) + I * (t : ℂ))‖)
        atTop atTop := by
    have hd :=
      norm_logDeriv_xi_vertical_tendsto_atTop
        (h := h - 1 / 2)
        (show 1 / 2 < h - 1 / 2 by linarith)
    convert hd using 1
    funext t
    congr 4
    ring
  have heventually : ∀ᶠ t : ℝ in atTop,
      B + 1 ≤ ‖logDeriv xi ((h : ℂ) + I * (t : ℂ))‖ :=
    (tendsto_atTop.1 hdiv) (B + 1)
  obtain ⟨T, hT⟩ := eventually_atTop.1 heventually
  linarith [hT T le_rfl, hbound T]

/-- No finite constant uniformly bounds the reflected source majorant on a
fixed vertical source line. -/
theorem not_exists_uniform_xiWardInteriorSourceArithmeticBound
    {h : ℝ} (hh : 1 / 2 < h) :
    ¬ ∃ C : ℝ, ∀ t : ℝ,
      xiWardInteriorSourceArithmeticBound
        ((h : ℂ) + I * (t : ℂ)) ≤ C := by
  rintro ⟨C, hC⟩
  have heventually :
      ∀ᶠ t : ℝ in atTop,
        C + 1 ≤ xiWardInteriorSourceArithmeticBound
          ((h : ℂ) + I * (t : ℂ)) :=
    (tendsto_atTop.1
      (xiWardInteriorSourceArithmeticBound_vertical_tendsto_atTop hh))
      (C + 1)
  obtain ⟨T, hT⟩ := eventually_atTop.1 heventually
  have hlower := hT T le_rfl
  have hupper := hC T
  linarith

end

end RHTower
