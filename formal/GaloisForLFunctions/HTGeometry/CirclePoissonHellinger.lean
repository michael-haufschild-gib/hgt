import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import GaloisForLFunctions.HTGeometry.WeightedHolder

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

/-- Positive square-root density of a circle Poisson law. -/
def circlePoissonHalfDensity (a : CirclePoissonParameter) (z : Circle) : ℝ :=
  Real.sqrt (poissonKernel 0 (a : ℂ) (z : ℂ))

theorem continuous_circlePoissonHalfDensity (a : CirclePoissonParameter) :
    Continuous (circlePoissonHalfDensity a) := by
  exact Real.continuous_sqrt.comp (continuous_circlePoissonDensity_real a)

theorem circlePoissonHalfDensity_nonneg (a : CirclePoissonParameter) (z : Circle) :
    0 ≤ circlePoissonHalfDensity a z := Real.sqrt_nonneg _

theorem circlePoissonHalfDensity_sq (a : CirclePoissonParameter) (z : Circle) :
    circlePoissonHalfDensity a z ^ 2 = poissonKernel 0 (a : ℂ) (z : ℂ) := by
  exact Real.sq_sqrt (circlePoissonDensity_nonneg a z)

theorem integral_sq_circlePoissonHalfDensity (a : CirclePoissonParameter) :
    ∫ z, circlePoissonHalfDensity a z ^ 2 ∂circleLebesgue = 1 := by
  simp_rw [circlePoissonHalfDensity_sq]
  rw [integral_circleLebesgue_eq_circleAverage
    (fun z : ℂ => poissonKernel 0 (a : ℂ) z)
    (continuous_circlePoissonDensity_real a).aestronglyMeasurable]
  exact Bottcher.poissonKernel_circleAverage_eq_one a.2

/-- Local Hellinger affinity of two circle Poisson laws. -/
def circlePoissonHellingerAffinity (a b : CirclePoissonParameter) : ℝ :=
  ∫ z, circlePoissonHalfDensity a z * circlePoissonHalfDensity b z ∂circleLebesgue

theorem circlePoissonHellingerAffinity_nonneg (a b : CirclePoissonParameter) :
    0 ≤ circlePoissonHellingerAffinity a b := by
  apply integral_nonneg
  intro z
  exact mul_nonneg (circlePoissonHalfDensity_nonneg a z)
    (circlePoissonHalfDensity_nonneg b z)

theorem one_sub_circlePoissonHellingerAffinity_eq (a b : CirclePoissonParameter) :
    1 - circlePoissonHellingerAffinity a b =
      (1 / 2 : ℝ) * ∫ z, (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z) ^ 2
        ∂circleLebesgue := by
  have ha : Integrable (fun z => circlePoissonHalfDensity a z ^ 2) circleLebesgue :=
    ((continuous_circlePoissonHalfDensity a).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : Integrable (fun z => circlePoissonHalfDensity b z ^ 2) circleLebesgue :=
    ((continuous_circlePoissonHalfDensity b).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hab : Integrable (fun z => circlePoissonHalfDensity a z * circlePoissonHalfDensity b z)
      circleLebesgue := by
    have hc := (continuous_circlePoissonHalfDensity a).mul
      (continuous_circlePoissonHalfDensity b)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint : (fun z : Circle =>
      (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z) ^ 2) =
      fun z => circlePoissonHalfDensity a z ^ 2 + circlePoissonHalfDensity b z ^ 2 -
        2 * (circlePoissonHalfDensity a z * circlePoissonHalfDensity b z) := by
    funext z
    ring
  rw [hpoint]
  have hcalc :
      (∫ z, circlePoissonHalfDensity a z ^ 2 + circlePoissonHalfDensity b z ^ 2 -
        2 * (circlePoissonHalfDensity a z * circlePoissonHalfDensity b z) ∂circleLebesgue) =
      (∫ z, circlePoissonHalfDensity a z ^ 2 ∂circleLebesgue) +
        (∫ z, circlePoissonHalfDensity b z ^ 2 ∂circleLebesgue) -
          2 * ∫ z, circlePoissonHalfDensity a z * circlePoissonHalfDensity b z
            ∂circleLebesgue := by
    calc
      (∫ z, circlePoissonHalfDensity a z ^ 2 + circlePoissonHalfDensity b z ^ 2 -
          2 * (circlePoissonHalfDensity a z * circlePoissonHalfDensity b z)
          ∂circleLebesgue) =
          (∫ z, circlePoissonHalfDensity a z ^ 2 + circlePoissonHalfDensity b z ^ 2
            ∂circleLebesgue) -
            ∫ z, 2 * (circlePoissonHalfDensity a z * circlePoissonHalfDensity b z)
              ∂circleLebesgue := integral_sub (ha.add hb) (hab.const_mul 2)
      _ = _ := by rw [integral_add ha hb, integral_const_mul]
  rw [hcalc, integral_sq_circlePoissonHalfDensity,
    integral_sq_circlePoissonHalfDensity]
  unfold circlePoissonHellingerAffinity
  ring

theorem circlePoissonHellingerAffinity_le_one (a b : CirclePoissonParameter) :
    circlePoissonHellingerAffinity a b ≤ 1 := by
  rw [← sub_nonneg, one_sub_circlePoissonHellingerAffinity_eq]
  positivity

theorem integral_coe_mul_poissonKernel_circleLebesgue (a : CirclePoissonParameter) :
    ∫ z : Circle, (z : ℂ) * (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ) ∂circleLebesgue =
      (a : ℂ) := by
  rw [integral_circleLebesgue_eq_circleAverage_complex
    (fun z : ℂ => z * (poissonKernel 0 (a : ℂ) z : ℂ))]
  · have hd : DiffContOnCl ℂ (fun z : ℂ => z) (Metric.ball 0 1) := by
      exact ⟨differentiableOn_id, continuousOn_id⟩
    have h := DiffContOnCl.circleAverage_poissonKernel_smul hd a.2
    have heq : (poissonKernel 0 (a : ℂ) • fun z : ℂ => z) =
        fun z : ℂ => z * (poissonKernel 0 (a : ℂ) z : ℂ) := by
      funext z
      simp [Complex.real_smul, mul_comm]
    rw [← heq]
    exact h
  · have hp : Continuous (fun z : Circle =>
        (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_circlePoissonDensity_real a)
    have hz : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
    exact (hz.mul hp).aestronglyMeasurable

/-- The first Fourier moment forces a universal quadratic lower bound on the Hellinger defect. -/
theorem norm_sq_div_eight_le_one_sub_circlePoissonHellingerAffinity
    (a b : CirclePoissonParameter) :
    ‖(a : ℂ) - (b : ℂ)‖ ^ 2 / 8 ≤ 1 - circlePoissonHellingerAffinity a b := by
  let D : Circle → ℝ := fun z =>
    circlePoissonHalfDensity a z - circlePoissonHalfDensity b z
  let S : Circle → ℝ := fun z =>
    circlePoissonHalfDensity a z + circlePoissonHalfDensity b z
  let A : ℝ := ∫ z, D z ^ 2 ∂circleLebesgue
  let B : ℝ := ∫ z, S z ^ 2 ∂circleLebesgue
  have hDc : Continuous D := by
    exact (continuous_circlePoissonHalfDensity a).sub
      (continuous_circlePoissonHalfDensity b)
  have hSc : Continuous S := by
    exact (continuous_circlePoissonHalfDensity a).add
      (continuous_circlePoissonHalfDensity b)
  have hAint : Integrable (fun z => D z ^ 2) circleLebesgue :=
    (hDc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hBint : Integrable (fun z => S z ^ 2) circleLebesgue :=
    (hSc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hA0 : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
  have hB4 : B ≤ 4 := by
    have hmajor : Integrable (fun z =>
        2 * circlePoissonHalfDensity a z ^ 2 +
          2 * circlePoissonHalfDensity b z ^ 2) circleLebesgue := by
      have hc := (((continuous_circlePoissonHalfDensity a).pow 2).const_mul 2).add
        (((continuous_circlePoissonHalfDensity b).pow 2).const_mul 2)
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      B ≤ ∫ z, 2 * circlePoissonHalfDensity a z ^ 2 +
          2 * circlePoissonHalfDensity b z ^ 2 ∂circleLebesgue := by
        apply integral_mono hBint hmajor
        intro z
        dsimp only [B, S]
        nlinarith [sq_nonneg
          (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z)]
      _ = 4 := by
        rw [integral_add,
          integral_const_mul, integral_const_mul,
          integral_sq_circlePoissonHalfDensity,
          integral_sq_circlePoissonHalfDensity]
        · ring
        · have hc := ((continuous_circlePoissonHalfDensity a).pow 2).const_mul 2
          exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        · have hc := ((continuous_circlePoissonHalfDensity b).pow 2).const_mul 2
          exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let g₁ : Circle → ℂ := fun z => (z : ℂ) * (D z : ℂ)
  let g₂ : Circle → ℂ := fun z => (S z : ℂ)
  have hg₁c : Continuous g₁ := by
    exact continuous_subtype_val.mul (Complex.continuous_ofReal.comp hDc)
  have hg₂c : Continuous g₂ := Complex.continuous_ofReal.comp hSc
  have hg₁sq : (∫ z, ‖g₁ z‖ ^ 2 ∂circleLebesgue) = A := by
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [g₁, A]
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hg₂sq : (∫ z, ‖g₂ z‖ ^ 2 ∂circleLebesgue) = B := by
    apply integral_congr_ae
    filter_upwards with z
    dsimp only [g₂, B]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hg₁int : Integrable (fun z => ‖g₁ z‖ ^ 2) circleLebesgue :=
    (hg₁c.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg₂int : Integrable (fun z => ‖g₂ z‖ ^ 2) circleLebesgue :=
    (hg₂c.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hprod : (∫ z, g₁ z * g₂ z * (1 : ℂ) ∂circleLebesgue) =
      (a : ℂ) - (b : ℂ) := by
    have hac : Continuous (fun z : Circle =>
        (z : ℂ) * (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ)) := by
      exact continuous_subtype_val.mul
        (Complex.continuous_ofReal.comp (continuous_circlePoissonDensity_real a))
    have hbc : Continuous (fun z : Circle =>
        (z : ℂ) * (poissonKernel 0 (b : ℂ) (z : ℂ) : ℂ)) := by
      exact continuous_subtype_val.mul
        (Complex.continuous_ofReal.comp (continuous_circlePoissonDensity_real b))
    calc
      (∫ z, g₁ z * g₂ z * (1 : ℂ) ∂circleLebesgue) =
          ∫ z, (z : ℂ) * (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ) -
            (z : ℂ) * (poissonKernel 0 (b : ℂ) (z : ℂ) : ℂ)
              ∂circleLebesgue := by
        apply integral_congr_ae
        filter_upwards with z
        dsimp only [g₁, g₂, D, S]
        have hDS :
            (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z) *
              (circlePoissonHalfDensity a z + circlePoissonHalfDensity b z) =
            poissonKernel 0 (a : ℂ) (z : ℂ) -
              poissonKernel 0 (b : ℂ) (z : ℂ) := by
          calc
            (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z) *
                (circlePoissonHalfDensity a z + circlePoissonHalfDensity b z) =
              circlePoissonHalfDensity a z ^ 2 - circlePoissonHalfDensity b z ^ 2 := by ring
            _ = _ := by rw [circlePoissonHalfDensity_sq, circlePoissonHalfDensity_sq]
        calc
          (z : ℂ) *
                ((circlePoissonHalfDensity a z - circlePoissonHalfDensity b z : ℝ) : ℂ) *
                ((circlePoissonHalfDensity a z + circlePoissonHalfDensity b z : ℝ) : ℂ) * 1 =
              (z : ℂ) *
                (((circlePoissonHalfDensity a z - circlePoissonHalfDensity b z) *
                  (circlePoissonHalfDensity a z + circlePoissonHalfDensity b z) : ℝ) : ℂ) := by
            push_cast
            ring
          _ = (z : ℂ) *
                ((poissonKernel 0 (a : ℂ) (z : ℂ) -
                  poissonKernel 0 (b : ℂ) (z : ℂ) : ℝ) : ℂ) := by rw [hDS]
          _ = (z : ℂ) * (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ) -
                (z : ℂ) * (poissonKernel 0 (b : ℂ) (z : ℂ) : ℂ) := by
            push_cast
            ring
      _ = (∫ z, (z : ℂ) *
            (poissonKernel 0 (a : ℂ) (z : ℂ) : ℂ) ∂circleLebesgue) -
          ∫ z, (z : ℂ) *
            (poissonKernel 0 (b : ℂ) (z : ℂ) : ℂ) ∂circleLebesgue := by
        exact integral_sub
          (hac.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (hbc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      _ = (a : ℂ) - (b : ℂ) := by
        rw [integral_coe_mul_poissonKernel_circleLebesgue,
          integral_coe_mul_poissonKernel_circleLebesgue]
  have hcs := norm_integral_mul_mul_le_sqrt_mul_sqrt_measure
    (g₁ := g₁) (g₂ := g₂) (W := fun _ : Circle => (1 : ℂ))
    hg₁c.aestronglyMeasurable hg₂c.aestronglyMeasurable aestronglyMeasurable_const
    (by simpa using hg₁int) (by simpa using hg₂int)
  simp only [norm_one, mul_one] at hcs
  have hprod' : (∫ z, g₁ z * g₂ z ∂circleLebesgue) =
      (a : ℂ) - (b : ℂ) := by simpa using hprod
  rw [hprod', hg₁sq, hg₂sq] at hcs
  have hsqrtB : Real.sqrt B ≤ 2 := by
    nlinarith [Real.sq_sqrt hB0, sq_nonneg (Real.sqrt B - 2)]
  have hnorm : ‖(a : ℂ) - (b : ℂ)‖ ≤ 2 * Real.sqrt A := by
    calc
      ‖(a : ℂ) - (b : ℂ)‖ ≤ Real.sqrt A * Real.sqrt B := hcs
      _ ≤ Real.sqrt A * 2 := mul_le_mul_of_nonneg_left hsqrtB (Real.sqrt_nonneg _)
      _ = 2 * Real.sqrt A := by ring
  have hsq : ‖(a : ℂ) - (b : ℂ)‖ ^ 2 ≤ 4 * A := by
    nlinarith [Real.sq_sqrt hA0, norm_nonneg ((a : ℂ) - (b : ℂ))]
  rw [one_sub_circlePoissonHellingerAffinity_eq]
  change ‖(a : ℂ) - (b : ℂ)‖ ^ 2 / 8 ≤ (1 / 2 : ℝ) * A
  linarith

private theorem abs_ratio_sq_sub_ratio_sq_le
    {N₁ N₂ d₁ d₂ δ : ℝ}
    (_hN₁0 : 0 ≤ N₁) (_hN₁1 : N₁ ≤ 1)
    (hN₂0 : 0 ≤ N₂) (hN₂1 : N₂ ≤ 1)
    (hd₁1 : 1 / 2 ≤ d₁) (hd₁2 : d₁ ≤ 3 / 2)
    (hd₂1 : 1 / 2 ≤ d₂) (hd₂2 : d₂ ≤ 3 / 2)
    (hN : |N₁ - N₂| ≤ δ) (hd : |d₁ - d₂| ≤ δ) :
    |N₁ / d₁ ^ 2 - N₂ / d₂ ^ 2| ≤ 52 * δ := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hN
  have hd₁0 : 0 < d₁ := lt_of_lt_of_le (by norm_num) hd₁1
  have hd₂0 : 0 < d₂ := lt_of_lt_of_le (by norm_num) hd₂1
  have hd₁sq : 1 / 4 ≤ d₁ ^ 2 := by nlinarith
  have hd₂sq : 1 / 4 ≤ d₂ ^ 2 := by nlinarith
  have hfirst : |N₁ - N₂| / d₁ ^ 2 ≤ 4 * δ := by
    rw [div_le_iff₀ (sq_pos_of_pos hd₁0)]
    nlinarith
  have hdsq : |d₂ ^ 2 - d₁ ^ 2| ≤ 3 * δ := by
    rw [show d₂ ^ 2 - d₁ ^ 2 = (d₂ - d₁) * (d₂ + d₁) by ring,
      abs_mul]
    have hdiff : |d₂ - d₁| ≤ δ := by simpa [abs_sub_comm] using hd
    have hsum0 : 0 ≤ d₂ + d₁ := by positivity
    rw [abs_of_nonneg hsum0]
    calc
      |d₂ - d₁| * (d₂ + d₁) ≤ δ * (d₂ + d₁) :=
        mul_le_mul_of_nonneg_right hdiff hsum0
      _ ≤ δ * 3 := mul_le_mul_of_nonneg_left (by linarith) hδ0
      _ = 3 * δ := by ring
  have hden : 1 / 16 ≤ d₁ ^ 2 * d₂ ^ 2 := by nlinarith
  have hsecond : N₂ * |d₂ ^ 2 - d₁ ^ 2| / (d₁ ^ 2 * d₂ ^ 2) ≤ 48 * δ := by
    rw [div_le_iff₀ (mul_pos (sq_pos_of_pos hd₁0) (sq_pos_of_pos hd₂0))]
    have hnum : N₂ * |d₂ ^ 2 - d₁ ^ 2| ≤ 3 * δ := by
      calc
        N₂ * |d₂ ^ 2 - d₁ ^ 2| ≤ 1 * |d₂ ^ 2 - d₁ ^ 2| :=
          mul_le_mul_of_nonneg_right hN₂1 (abs_nonneg _)
        _ ≤ 3 * δ := by simpa using hdsq
    nlinarith
  have hsplit :
      N₁ / d₁ ^ 2 - N₂ / d₂ ^ 2 =
        (N₁ - N₂) / d₁ ^ 2 +
          N₂ * (d₂ ^ 2 - d₁ ^ 2) / (d₁ ^ 2 * d₂ ^ 2) := by
    field_simp
    ring
  rw [hsplit]
  calc
    |(N₁ - N₂) / d₁ ^ 2 +
        N₂ * (d₂ ^ 2 - d₁ ^ 2) / (d₁ ^ 2 * d₂ ^ 2)| ≤
        |(N₁ - N₂) / d₁ ^ 2| +
          |N₂ * (d₂ ^ 2 - d₁ ^ 2) / (d₁ ^ 2 * d₂ ^ 2)| := abs_add_le _ _
    _ = |N₁ - N₂| / d₁ ^ 2 +
          N₂ * |d₂ ^ 2 - d₁ ^ 2| / (d₁ ^ 2 * d₂ ^ 2) := by
      rw [abs_div, abs_div, abs_mul, abs_of_nonneg hN₂0,
        abs_of_pos (sq_pos_of_pos hd₁0),
        abs_of_pos (mul_pos (sq_pos_of_pos hd₁0) (sq_pos_of_pos hd₂0))]
    _ ≤ 4 * δ + 48 * δ := add_le_add hfirst hsecond
    _ = 52 * δ := by ring

private theorem circlePoisson_geometry_halfDisk
    (a : CirclePoissonParameter) (ha : ‖(a : ℂ)‖ ≤ 1 / 2) (z : Circle) :
    0 ≤ 1 - ‖(a : ℂ)‖ ^ 2 ∧
      1 - ‖(a : ℂ)‖ ^ 2 ≤ 1 ∧
      1 / 2 ≤ ‖(z : ℂ) - (a : ℂ)‖ ∧
      ‖(z : ℂ) - (a : ℂ)‖ ≤ 3 / 2 := by
  have ha0 : 0 ≤ ‖(a : ℂ)‖ := norm_nonneg _
  have hlower : 1 - ‖(a : ℂ)‖ ≤ ‖(z : ℂ) - (a : ℂ)‖ := by
    simpa only [Circle.norm_coe] using norm_sub_norm_le (z : ℂ) (a : ℂ)
  have hupper := norm_sub_le (z : ℂ) (a : ℂ)
  rw [Circle.norm_coe] at hupper
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> linarith

private theorem abs_poissonKernel_sub_le_halfDisk
    (a b : CirclePoissonParameter) (ha : ‖(a : ℂ)‖ ≤ 1 / 2)
    (hb : ‖(b : ℂ)‖ ≤ 1 / 2) (z : Circle) :
    |poissonKernel 0 (a : ℂ) (z : ℂ) - poissonKernel 0 (b : ℂ) (z : ℂ)| ≤
      52 * ‖(a : ℂ) - (b : ℂ)‖ := by
  obtain ⟨hNa0, hNa1, hda1, hda2⟩ := circlePoisson_geometry_halfDisk a ha z
  obtain ⟨hNb0, hNb1, hdb1, hdb2⟩ := circlePoisson_geometry_halfDisk b hb z
  have hN : |(1 - ‖(a : ℂ)‖ ^ 2) - (1 - ‖(b : ℂ)‖ ^ 2)| ≤
      ‖(a : ℂ) - (b : ℂ)‖ := by
    rw [show (1 - ‖(a : ℂ)‖ ^ 2) - (1 - ‖(b : ℂ)‖ ^ 2) =
      (‖(b : ℂ)‖ - ‖(a : ℂ)‖) * (‖(b : ℂ)‖ + ‖(a : ℂ)‖) by ring,
      abs_mul]
    have hnormdiff : |‖(b : ℂ)‖ - ‖(a : ℂ)‖| ≤ ‖(a : ℂ) - (b : ℂ)‖ := by
      rw [abs_le]
      constructor
      · have h := norm_sub_norm_le (a : ℂ) (b : ℂ)
        linarith
      · have h := norm_sub_norm_le (b : ℂ) (a : ℂ)
        rwa [norm_sub_rev] at h
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      |‖(b : ℂ)‖ - ‖(a : ℂ)‖| * (‖(b : ℂ)‖ + ‖(a : ℂ)‖) ≤
          ‖(a : ℂ) - (b : ℂ)‖ * (‖(b : ℂ)‖ + ‖(a : ℂ)‖) :=
        mul_le_mul_of_nonneg_right hnormdiff (add_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ ‖(a : ℂ) - (b : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ = _ := mul_one _
  have hd : |‖(z : ℂ) - (a : ℂ)‖ - ‖(z : ℂ) - (b : ℂ)‖| ≤
      ‖(a : ℂ) - (b : ℂ)‖ := by
    rw [abs_le]
    constructor
    · have h := norm_sub_norm_le ((z : ℂ) - (b : ℂ)) ((z : ℂ) - (a : ℂ))
      rw [show ((z : ℂ) - (b : ℂ)) - ((z : ℂ) - (a : ℂ)) =
        (a : ℂ) - (b : ℂ) by ring] at h
      linarith
    · have h := norm_sub_norm_le ((z : ℂ) - (a : ℂ)) ((z : ℂ) - (b : ℂ))
      rw [show ((z : ℂ) - (a : ℂ)) - ((z : ℂ) - (b : ℂ)) =
        -((a : ℂ) - (b : ℂ)) by ring, norm_neg] at h
      exact h
  simp only [poissonKernel_def, sub_zero, Circle.norm_coe, one_pow]
  exact abs_ratio_sq_sub_ratio_sq_le hNa0 hNa1 hNb0 hNb1 hda1 hda2 hdb1 hdb2 hN hd

private theorem half_le_circlePoissonHalfDensity_halfDisk
    (a : CirclePoissonParameter) (ha : ‖(a : ℂ)‖ ≤ 1 / 2) (z : Circle) :
    1 / 2 ≤ circlePoissonHalfDensity a z := by
  obtain ⟨hN0, -, -, hd2⟩ := circlePoisson_geometry_halfDisk a ha z
  have hN : 3 / 4 ≤ 1 - ‖(a : ℂ)‖ ^ 2 := by nlinarith [norm_nonneg (a : ℂ)]
  have hden0 : 0 < ‖(z : ℂ) - (a : ℂ)‖ ^ 2 := by
    have := (circlePoisson_geometry_halfDisk a ha z).2.2.1
    positivity
  have hP : 1 / 3 ≤ poissonKernel 0 (a : ℂ) (z : ℂ) := by
    simp only [poissonKernel_def, sub_zero, Circle.norm_coe, one_pow]
    rw [le_div_iff₀ hden0]
    have hdenle : ‖(z : ℂ) - (a : ℂ)‖ ^ 2 ≤ 9 / 4 := by
      nlinarith [norm_nonneg ((z : ℂ) - (a : ℂ))]
    nlinarith
  rw [circlePoissonHalfDensity, Real.le_sqrt (by norm_num)
    (circlePoissonDensity_nonneg a z)]
  nlinarith

private theorem abs_circlePoissonHalfDensity_sub_le_halfDisk
    (a b : CirclePoissonParameter) (ha : ‖(a : ℂ)‖ ≤ 1 / 2)
    (hb : ‖(b : ℂ)‖ ≤ 1 / 2) (z : Circle) :
    |circlePoissonHalfDensity a z - circlePoissonHalfDensity b z| ≤
      52 * ‖(a : ℂ) - (b : ℂ)‖ := by
  have hsum : 1 ≤ circlePoissonHalfDensity a z + circlePoissonHalfDensity b z := by
    linarith [half_le_circlePoissonHalfDensity_halfDisk a ha z,
      half_le_circlePoissonHalfDensity_halfDisk b hb z]
  have hfactor :
      |poissonKernel 0 (a : ℂ) (z : ℂ) - poissonKernel 0 (b : ℂ) (z : ℂ)| =
        |circlePoissonHalfDensity a z - circlePoissonHalfDensity b z| *
          (circlePoissonHalfDensity a z + circlePoissonHalfDensity b z) := by
    rw [← circlePoissonHalfDensity_sq a z, ← circlePoissonHalfDensity_sq b z,
      show circlePoissonHalfDensity a z ^ 2 - circlePoissonHalfDensity b z ^ 2 =
        (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z) *
          (circlePoissonHalfDensity a z + circlePoissonHalfDensity b z) by ring,
      abs_mul, abs_of_nonneg (by positivity :
        0 ≤ circlePoissonHalfDensity a z + circlePoissonHalfDensity b z)]
  calc
    |circlePoissonHalfDensity a z - circlePoissonHalfDensity b z| ≤
        |circlePoissonHalfDensity a z - circlePoissonHalfDensity b z| *
          (circlePoissonHalfDensity a z + circlePoissonHalfDensity b z) := by
      nlinarith [abs_nonneg (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z)]
    _ = |poissonKernel 0 (a : ℂ) (z : ℂ) -
          poissonKernel 0 (b : ℂ) (z : ℂ)| := hfactor.symm
    _ ≤ 52 * ‖(a : ℂ) - (b : ℂ)‖ :=
      abs_poissonKernel_sub_le_halfDisk a b ha hb z

/-- Uniform quadratic upper bound on the local Hellinger defect in the closed half disk. -/
theorem one_sub_circlePoissonHellingerAffinity_le_norm_sq_halfDisk
    (a b : CirclePoissonParameter) (ha : ‖(a : ℂ)‖ ≤ 1 / 2)
    (hb : ‖(b : ℂ)‖ ≤ 1 / 2) :
    1 - circlePoissonHellingerAffinity a b ≤
      1352 * ‖(a : ℂ) - (b : ℂ)‖ ^ 2 := by
  rw [one_sub_circlePoissonHellingerAffinity_eq]
  have hdiffInt : Integrable (fun z : Circle =>
      (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z) ^ 2) circleLebesgue :=
    (((continuous_circlePoissonHalfDensity a).sub
      (continuous_circlePoissonHalfDensity b)).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hconstInt : Integrable (fun _ : Circle =>
      (52 * ‖(a : ℂ) - (b : ℂ)‖) ^ 2) circleLebesgue := integrable_const _
  have hsq : ∫ z : Circle,
      (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z) ^ 2 ∂circleLebesgue ≤
      ∫ _z : Circle, (52 * ‖(a : ℂ) - (b : ℂ)‖) ^ 2 ∂circleLebesgue := by
    apply integral_mono hdiffInt hconstInt
    intro z
    have habs := abs_circlePoissonHalfDensity_sub_le_halfDisk a b ha hb z
    have hright : 0 ≤ 52 * ‖(a : ℂ) - (b : ℂ)‖ := by positivity
    have hsquare := (sq_le_sq₀
      (abs_nonneg (circlePoissonHalfDensity a z - circlePoissonHalfDensity b z)) hright).2 habs
    rwa [sq_abs] at hsquare
  rw [integral_const, probReal_univ, smul_eq_mul, one_mul] at hsq
  nlinarith

/-- **Local Hellinger comparability for circle Poisson laws.**  This is the exact local lemma used
by Kakutani classification: on one fixed closed disk, affinity defect and squared Euclidean
parameter distance are comparable in both directions. -/
theorem exists_circlePoissonHellinger_quadratic_comparison :
    ∃ r₀ c C : ℝ, 0 < r₀ ∧ r₀ < 1 ∧ 0 < c ∧ c < C ∧
      ∀ a b : CirclePoissonParameter,
        ‖(a : ℂ)‖ ≤ r₀ → ‖(b : ℂ)‖ ≤ r₀ →
          c * ‖(a : ℂ) - (b : ℂ)‖ ^ 2 ≤
              1 - circlePoissonHellingerAffinity a b ∧
            1 - circlePoissonHellingerAffinity a b ≤
              C * ‖(a : ℂ) - (b : ℂ)‖ ^ 2 := by
  refine ⟨1 / 2, 1 / 8, 1352, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro a b ha hb
  constructor
  · simpa [div_eq_mul_inv, mul_comm] using
      norm_sq_div_eight_le_one_sub_circlePoissonHellingerAffinity a b
  · exact one_sub_circlePoissonHellingerAffinity_le_norm_sq_halfDisk a b ha hb

end

end GaloisForLFunctions.HTGeometry
