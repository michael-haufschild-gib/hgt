import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaStripCarrierTwoSided
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaStripSquareIntegrable
import GaloisForLFunctions.HTGeometry.WeightedHardyInequality

/-!
# The `L²` Hardy criterion for the forced Gamma strip equation

The homogeneous Gamma transport on the shifted line `z = x + iσ` is the operator

`H(z) = z^{-1/2} e^{iγz} [Γ(1+iz)/Γ(1-iz)]^{1/2} e^{-izT/2}`,

whose scalar modulus is the square root of the corpus strip density and whose operator factor is
bounded by `e^{σ‖T‖/2}` because `T` is self-adjoint.  Its inverse is the same expression with the
scalar inverted and the operator exponent reflected.

Variation of constants on the horizontal line writes every solution of the forced equation as

`f(x) = H(x)(c + ∫₁^x H(t)^{-1}b(t)dt)`,

and the two-sided power bound `c(1+|x|)^{-2p} ≤ |H|² ≤ C(1+|x|)^{-2p}`, `p = 1/2 + σ`, turns this
into the weighted Hardy configuration.  Hence a shifted-line `L²` bound on the first moment `x b(x)`
of the forcing — not a weighted frequency `L¹` moment — already forces the solution into
`L²` on either outward ray.

The orientation parameter `ε` with `|ε| = 1` carries both rays at once: the strip density is even in
the height, so the same constants serve the reflected ray.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

/-- The scalar modulus of the Gamma strip propagator on the shifted line. -/
def suzukiGammaStripCarrier (σ x : ℝ) : ℝ := Real.sqrt (suzukiGammaStripNormSq σ x)

theorem suzukiGammaStripCarrier_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    0 < suzukiGammaStripCarrier σ x :=
  Real.sqrt_pos.mpr (suzukiGammaStripNormSq_pos hσ0 hσ1 x)

/-- The Gamma strip propagator `H(z) = z^{-1/2}Q(z)` as a bounded operator. -/
def stripPropagator (E : ℂ → ℂ) (T : X →L[ℂ] X) (z : ℂ) : X →L[ℂ] X :=
  (z ^ (-(1 : ℂ) / 2)) • stripTransport E T z

omit [CompleteSpace X] [Nontrivial X] in
theorem stripPropagator_apply (E : ℂ → ℂ) (T : X →L[ℂ] X) (z : ℂ) (c : X) :
    stripPropagator E T z c = stripSolution E T c z := rfl

/-- The inverse Gamma strip propagator. -/
def stripPropagatorInv (E : ℂ → ℂ) (T : X →L[ℂ] X) (z : ℂ) : X →L[ℂ] X :=
  ((z ^ (-(1 : ℂ) / 2)
      * (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z))⁻¹)
    • NormedSpace.exp (((Complex.I / 2) * z) • T)

omit [Nontrivial X] in
/-- The inverse propagator really inverts the propagator wherever the branch does not vanish. -/
theorem stripPropagatorInv_stripPropagator {E : ℂ → ℂ} {T : X →L[ℂ] X} {z : ℂ}
    (hz : z ≠ 0) (hE : E z ≠ 0) (v : X) :
    stripPropagatorInv E T z (stripPropagator E T z v) = v := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  set a : ℂ := z ^ (-(1 : ℂ) / 2)
      * (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z) with hadef
  have hane : a ≠ 0 := by
    rw [hadef]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hz))
      (mul_ne_zero (Complex.exp_ne_zero _) hE)
  have hcomm : Commute (((Complex.I / 2) * z) • T) ((-(Complex.I / 2) * z) • T) := by
    have h : ((-(Complex.I / 2) * z) • T) = -(((Complex.I / 2) * z) • T) := by
      rw [← neg_smul]
      congr 1
      ring
    rw [h]
    exact (Commute.refl _).neg_right
  have hprod : NormedSpace.exp (((Complex.I / 2) * z) • T)
      * NormedSpace.exp ((-(Complex.I / 2) * z) • T) = 1 := by
    rw [← NormedSpace.exp_add_of_commute hcomm, ← add_smul,
      show (Complex.I / 2) * z + -(Complex.I / 2) * z = 0 by ring, zero_smul,
      NormedSpace.exp_zero]
  have hstep : stripPropagator E T z v
      = a • NormedSpace.exp ((-(Complex.I / 2) * z) • T) v := by
    rw [stripPropagator, smul_apply, stripTransport_apply, hadef,
      smul_smul]
  rw [hstep, stripPropagatorInv, smul_apply, map_smul, smul_smul,
    inv_mul_cancel₀ hane, one_smul]
  exact congrFun (congrArg (fun S : X →L[ℂ] X => (S : X → X)) hprod) v

section Bounds

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- On the shifted line the scalar factor of the propagator is exactly the strip carrier. -/
theorem norm_cpow_mul_branch_shift (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    ‖((x : ℂ) + (σ : ℂ) * Complex.I) ^ (-(1 : ℂ) / 2)‖
        * ‖E ((x : ℂ) + (σ : ℂ) * Complex.I)‖
      = suzukiGammaStripCarrier σ x := by
  set z : ℂ := (x : ℂ) + (σ : ℂ) * Complex.I with hz
  have hzim : z.im = σ := by rw [hz]; simp
  have hzne : z ≠ 0 := by
    intro hcon
    rw [hcon] at hzim
    simp at hzim
    linarith
  have hznorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hzne
  have hpow : ‖z ^ (-(1 : ℂ) / 2)‖ = (Real.sqrt ‖z‖)⁻¹ := by
    rw [Complex.norm_cpow_of_ne_zero hzne]
    norm_num
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hznorm.le]
  have hEsq : ‖E z‖ ^ 2 = ‖gammaRatio z‖ := by
    rw [← norm_pow, hE z (shift_mem_imStrip hσ0 hσ1 x)]
  have hnormSq : suzukiGammaStripNormSq σ x = ‖E z‖ ^ 2 / ‖z‖ := by
    rw [suzukiGammaStripNormSq, hEsq, norm_gammaRatio_shift σ x]
  rw [hpow, suzukiGammaStripCarrier, hnormSq, Real.sqrt_div (by positivity),
    Real.sqrt_sq (norm_nonneg _)]
  field_simp

/-- **`(3)`, propagator half.**  On the shifted line the Gamma propagator has operator norm at most
the strip carrier times the exact archimedean and operator factors. -/
theorem norm_stripPropagator_shift_le (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x : ℝ) :
    ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ Real.exp (-(Real.eulerMascheroniConstant * σ)) * Real.exp (σ / 2 * ‖T‖)
        * suzukiGammaStripCarrier σ x := by
  set z : ℂ := (x : ℂ) + (σ : ℂ) * Complex.I with hz
  have hzim : z.im = σ := by rw [hz]; simp
  have hzre : z.re = x := by rw [hz]; simp
  have hphase : ‖Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z)‖
      = Real.exp (-(Real.eulerMascheroniConstant * σ)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [hzim, hzre]
  have hop : ‖NormedSpace.exp ((-(Complex.I / 2) * z) • T)‖ ≤ Real.exp (σ / 2 * ‖T‖) := by
    have hre : (-(Complex.I / 2) * z).re = σ / 2 := by
      simp [hz]
      ring
    have := norm_exp_smul_le hT (-(Complex.I / 2) * z)
    rwa [hre, abs_of_pos (by linarith : (0 : ℝ) < σ / 2)] at this
  have hval : ‖stripPropagator E T z‖
      = ‖z ^ (-(1 : ℂ) / 2)‖ * (Real.exp (-(Real.eulerMascheroniConstant * σ)) * ‖E z‖)
        * ‖NormedSpace.exp ((-(Complex.I / 2) * z) • T)‖ := by
    rw [stripPropagator, norm_smul, stripTransport, norm_smul, norm_mul, hphase]
    ring
  have hcarrier := norm_cpow_mul_branch_shift hE hσ0 hσ1 x
  rw [hval]
  calc ‖z ^ (-(1 : ℂ) / 2)‖ * (Real.exp (-(Real.eulerMascheroniConstant * σ)) * ‖E z‖)
        * ‖NormedSpace.exp ((-(Complex.I / 2) * z) • T)‖
      ≤ ‖z ^ (-(1 : ℂ) / 2)‖ * (Real.exp (-(Real.eulerMascheroniConstant * σ)) * ‖E z‖)
        * Real.exp (σ / 2 * ‖T‖) := by
        refine mul_le_mul_of_nonneg_left hop (by positivity)
    _ = Real.exp (-(Real.eulerMascheroniConstant * σ)) * Real.exp (σ / 2 * ‖T‖)
        * (‖z ^ (-(1 : ℂ) / 2)‖ * ‖E z‖) := by ring
    _ = Real.exp (-(Real.eulerMascheroniConstant * σ)) * Real.exp (σ / 2 * ‖T‖)
        * suzukiGammaStripCarrier σ x := by rw [hcarrier]

/-- **`(3)`, inverse half.**  The inverse Gamma propagator has operator norm at most the reciprocal
of the strip carrier times the same archimedean and operator factors. -/
theorem norm_stripPropagatorInv_shift_le (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x : ℝ) :
    ‖stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.eulerMascheroniConstant * σ) * Real.exp (σ / 2 * ‖T‖)
        * (suzukiGammaStripCarrier σ x)⁻¹ := by
  set z : ℂ := (x : ℂ) + (σ : ℂ) * Complex.I with hz
  have hzim : z.im = σ := by rw [hz]; simp
  have hzre : z.re = x := by rw [hz]; simp
  have hphase : ‖Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z)‖
      = Real.exp (-(Real.eulerMascheroniConstant * σ)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [hzim, hzre]
  have hop : ‖NormedSpace.exp (((Complex.I / 2) * z) • T)‖ ≤ Real.exp (σ / 2 * ‖T‖) := by
    have hre : ((Complex.I / 2) * z).re = -(σ / 2) := by
      simp [hz]
      ring
    have := norm_exp_smul_le hT ((Complex.I / 2) * z)
    rwa [hre, abs_of_nonpos (by linarith : -(σ / 2) ≤ (0 : ℝ)), neg_neg] at this
  have hcarrier := norm_cpow_mul_branch_shift hE hσ0 hσ1 x
  have hcpos : 0 < suzukiGammaStripCarrier σ x := suzukiGammaStripCarrier_pos hσ0 hσ1 x
  have hscalar : ‖(z ^ (-(1 : ℂ) / 2)
      * (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z))⁻¹‖
      = Real.exp (Real.eulerMascheroniConstant * σ) * (suzukiGammaStripCarrier σ x)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, hphase]
    rw [show ‖z ^ (-(1 : ℂ) / 2)‖ * (Real.exp (-(Real.eulerMascheroniConstant * σ)) * ‖E z‖)
        = Real.exp (-(Real.eulerMascheroniConstant * σ))
          * (‖z ^ (-(1 : ℂ) / 2)‖ * ‖E z‖) by ring, hcarrier, mul_inv,
      Real.exp_neg, inv_inv]
  rw [stripPropagatorInv, norm_smul, hscalar]
  calc Real.exp (Real.eulerMascheroniConstant * σ) * (suzukiGammaStripCarrier σ x)⁻¹
        * ‖NormedSpace.exp (((Complex.I / 2) * z) • T)‖
      ≤ Real.exp (Real.eulerMascheroniConstant * σ) * (suzukiGammaStripCarrier σ x)⁻¹
        * Real.exp (σ / 2 * ‖T‖) := mul_le_mul_of_nonneg_left hop (by positivity)
    _ = Real.exp (Real.eulerMascheroniConstant * σ) * Real.exp (σ / 2 * ‖T‖)
        * (suzukiGammaStripCarrier σ x)⁻¹ := by ring

end Bounds

/-- **`(13)`: variation of constants along an outward ray of the shifted line.**  The orientation
`ε` with `|ε| = 1` selects the ray. -/
def forcedStripRay (E : ℂ → ℂ) (T : X →L[ℂ] X) (c : X) (b : ℝ → X) (σ ε x : ℝ) : X :=
  stripPropagator E T (((ε * x : ℝ) : ℂ) + (σ : ℂ) * Complex.I)
    (c + ∫ t in Ioc (1 : ℝ) x,
      stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I) (b (ε * t)))

/-- **Theorem 4, `(36) ⟹ (37)`.**  A shifted-line `L²` bound on the first moment of the forcing puts
the forced Gamma strip solution in `L²` on the outward ray.  The exponent `p = 1/2 + σ > 1/2` of the
exact Gamma quotient is what makes the weighted Hardy inequality available. -/
theorem lintegral_enorm_sq_forcedStripRay_lt_top {E : ℂ → ℂ} {T : X →L[ℂ] X}
    (hT : IsSelfAdjoint T) (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (c : X) (b : ℝ → X) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {ε : ℝ} (hε : |ε| = 1)
    (hmeas : AEMeasurable (fun t : ℝ => ‖b (ε * t)‖ₑ) (volume.restrict (Ioi (1 : ℝ))))
    (hmom : ∫⁻ t in Ioi (1 : ℝ), ‖(t : ℝ) • b (ε * t)‖ₑ ^ 2 < ⊤) :
    ∫⁻ x in Ioi (1 : ℝ), ‖forcedStripRay E T c b σ ε x‖ₑ ^ 2 < ⊤ := by
  set p : ℝ := 1 / 2 + σ with hpdef
  have hp : 1 / 2 < p := by rw [hpdef]; linarith
  obtain ⟨c₀, C₀, hc₀, hC₀, hbounds⟩ := exists_twoSided_suzukiGammaStripNormSq hσ0 hσ1
  have h2p : (1 : ℝ) + 2 * σ = 2 * p := by rw [hpdef]; ring
  -- carrier bounds transported from the two-sided density bound
  have hcarrier_le : ∀ y : ℝ,
      suzukiGammaStripCarrier σ y ≤ Real.sqrt C₀ * (1 + |y|) ^ (-p) := by
    intro y
    have hy : (0 : ℝ) < 1 + |y| := by positivity
    have hrw : Real.sqrt ((1 + |y|) ^ (-(1 + 2 * σ))) = (1 + |y|) ^ (-p) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy.le]
      congr 1
      rw [h2p]
      ring
    calc suzukiGammaStripCarrier σ y
        ≤ Real.sqrt (C₀ * (1 + |y|) ^ (-(1 + 2 * σ))) :=
          Real.sqrt_le_sqrt (hbounds y).2
      _ = Real.sqrt C₀ * (1 + |y|) ^ (-p) := by
          rw [Real.sqrt_mul hC₀.le, hrw]
  have hcarrier_ge : ∀ y : ℝ,
      Real.sqrt c₀ * (1 + |y|) ^ (-p) ≤ suzukiGammaStripCarrier σ y := by
    intro y
    have hy : (0 : ℝ) < 1 + |y| := by positivity
    have hrw : Real.sqrt ((1 + |y|) ^ (-(1 + 2 * σ))) = (1 + |y|) ^ (-p) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy.le]
      congr 1
      rw [h2p]
      ring
    calc Real.sqrt c₀ * (1 + |y|) ^ (-p) = Real.sqrt (c₀ * (1 + |y|) ^ (-(1 + 2 * σ))) := by
          rw [Real.sqrt_mul hc₀.le, hrw]
      _ ≤ suzukiGammaStripCarrier σ y := Real.sqrt_le_sqrt (hbounds y).1
  -- the two propagation constants
  set E₁ : ℝ := Real.exp (-(Real.eulerMascheroniConstant * σ)) * Real.exp (σ / 2 * ‖T‖) with hE₁
  set E₂ : ℝ := Real.exp (Real.eulerMascheroniConstant * σ) * Real.exp (σ / 2 * ‖T‖) with hE₂
  have hE₁pos : 0 < E₁ := by rw [hE₁]; positivity
  have hE₂pos : 0 < E₂ := by rw [hE₂]; positivity
  set K : ℝ := E₁ * Real.sqrt C₀ with hK
  set A : ℝ := E₂ * (Real.sqrt c₀)⁻¹ * 2 ^ p with hA
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos hE₁pos (Real.sqrt_pos.mpr hC₀)
  have hApos : 0 < A := by
    rw [hA]
    exact mul_pos (mul_pos hE₂pos (inv_pos.mpr (Real.sqrt_pos.mpr hc₀)))
      (Real.rpow_pos_of_pos (by norm_num) _)
  set h : ℝ → X := fun t => (A * t) • b (ε * t) with hhdef
  -- the propagated bound
  have hbound : ∀ x : ℝ, 1 < x →
      ‖forcedStripRay E T c b σ ε x‖ₑ ≤ ENNReal.ofReal (K * x ^ (-p))
        * (ENNReal.ofReal ‖c‖
          + ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have hxabs : |ε * x| = x := by rw [abs_mul, hε, one_mul, abs_of_pos hx0]
    -- outer factor
    have houter : ‖stripPropagator E T (((ε * x : ℝ) : ℂ) + (σ : ℂ) * Complex.I)‖
        ≤ K * x ^ (-p) := by
      refine le_trans (norm_stripPropagator_shift_le hT hE hσ0 hσ1 (ε * x)) ?_
      calc E₁ * suzukiGammaStripCarrier σ (ε * x)
          ≤ E₁ * (Real.sqrt C₀ * (1 + |ε * x|) ^ (-p)) :=
            mul_le_mul_of_nonneg_left (hcarrier_le (ε * x)) hE₁pos.le
        _ = K * (1 + x) ^ (-p) := by rw [hxabs, hK]; ring
        _ ≤ K * x ^ (-p) := by
            refine mul_le_mul_of_nonneg_left ?_ hKpos.le
            exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
    -- inner factor
    have hinner : ∀ t : ℝ, 1 < t → t ≤ x →
        ENNReal.ofReal ‖stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I)‖
            * ‖b (ε * t)‖ₑ
          ≤ ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ := by
      intro t ht _
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      have htabs : |ε * t| = t := by rw [abs_mul, hε, one_mul, abs_of_pos ht0]
      have hstep : ‖stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I)‖
          ≤ A * t ^ p := by
        refine le_trans (norm_stripPropagatorInv_shift_le hT hE hσ0 hσ1 (ε * t)) ?_
        have hinvle : (suzukiGammaStripCarrier σ (ε * t))⁻¹
            ≤ (Real.sqrt c₀)⁻¹ * (1 + t) ^ p := by
          have hpos : 0 < Real.sqrt c₀ * (1 + |ε * t|) ^ (-p) := by
            have : (0 : ℝ) < 1 + |ε * t| := by positivity
            exact mul_pos (Real.sqrt_pos.mpr hc₀) (Real.rpow_pos_of_pos this _)
          have hle := hcarrier_ge (ε * t)
          have := one_div_le_one_div_of_le hpos hle
          rw [one_div, one_div] at this
          rw [htabs] at this
          refine le_trans this (le_of_eq ?_)
          rw [mul_inv, Real.rpow_neg (by positivity), inv_inv]
        have h2t : (1 : ℝ) + t ≤ 2 * t := by linarith
        have hpowle : (1 + t) ^ p ≤ 2 ^ p * t ^ p := by
          calc (1 + t) ^ p ≤ (2 * t) ^ p :=
                Real.rpow_le_rpow (by positivity) h2t (by linarith)
            _ = 2 ^ p * t ^ p := Real.mul_rpow (by norm_num) ht0.le
        calc E₂ * (suzukiGammaStripCarrier σ (ε * t))⁻¹
            ≤ E₂ * ((Real.sqrt c₀)⁻¹ * (1 + t) ^ p) :=
              mul_le_mul_of_nonneg_left hinvle hE₂pos.le
          _ ≤ E₂ * ((Real.sqrt c₀)⁻¹ * (2 ^ p * t ^ p)) := by
              refine mul_le_mul_of_nonneg_left ?_ hE₂pos.le
              exact mul_le_mul_of_nonneg_left hpowle (by positivity)
          _ = A * t ^ p := by rw [hA]; ring
      have hsplit : ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ
          = ENNReal.ofReal (A * t ^ p) * ‖b (ε * t)‖ₑ := by
        rw [hhdef]
        simp only
        rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_pos (by positivity : (0 : ℝ) < A * t),
          ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)]
        congr 2
        rw [show t ^ (p - 1) * (A * t) = A * (t ^ (p - 1) * t ^ (1 : ℝ)) by
          rw [Real.rpow_one]; ring, ← Real.rpow_add ht0]
        congr 2
        ring
      rw [hsplit]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hstep) le_rfl
    -- assemble
    have hint : ‖∫ t in Ioc (1 : ℝ) x,
        stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I) (b (ε * t))‖ₑ
        ≤ ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ := by
      refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
      refine setLIntegral_mono' measurableSet_Ioc ?_
      intro t ht
      refine le_trans ?_ (hinner t ht.1 ht.2)
      calc ‖stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I) (b (ε * t))‖ₑ
          = ENNReal.ofReal
              ‖stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I) (b (ε * t))‖ :=
            (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal
              (‖stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I)‖
                * ‖b (ε * t)‖) :=
            ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
        _ = ENNReal.ofReal
              ‖stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I)‖
                * ‖b (ε * t)‖ₑ := by
            rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
    calc ‖forcedStripRay E T c b σ ε x‖ₑ
        = ENNReal.ofReal ‖forcedStripRay E T c b σ ε x‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (‖stripPropagator E T (((ε * x : ℝ) : ℂ) + (σ : ℂ) * Complex.I)‖
            * ‖c + ∫ t in Ioc (1 : ℝ) x,
                stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I) (b (ε * t))‖) :=
          ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
      _ = ENNReal.ofReal ‖stripPropagator E T (((ε * x : ℝ) : ℂ) + (σ : ℂ) * Complex.I)‖
            * ‖c + ∫ t in Ioc (1 : ℝ) x,
                stripPropagatorInv E T (((ε * t : ℝ) : ℂ) + (σ : ℂ) * Complex.I) (b (ε * t))‖ₑ := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
      _ ≤ ENNReal.ofReal (K * x ^ (-p))
            * (ENNReal.ofReal ‖c‖
              + ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ) := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal houter) ?_
          refine le_trans (enorm_add_le _ _) ?_
          refine add_le_add (le_of_eq ?_) hint
          exact (ofReal_norm c).symm
  -- the moment hypothesis for the rescaled forcing
  have hhmeas : AEMeasurable (fun t => ‖h t‖ₑ) (volume.restrict (Ioi (1 : ℝ))) := by
    have hrw : (fun t : ℝ => ‖h t‖ₑ)
        = fun t : ℝ => ENNReal.ofReal |A * t| * ‖b (ε * t)‖ₑ := by
      funext t
      rw [hhdef]
      simp only
      rw [enorm_smul, Real.enorm_eq_ofReal_abs]
    rw [hrw]
    exact AEMeasurable.mul
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((by fun_prop : Measurable fun t : ℝ => |A * t|).aemeasurable)) hmeas
  have hhfin : ∫⁻ t in Ioi (1 : ℝ), ‖h t‖ₑ ^ 2 < ⊤ := by
    have hrw : ∀ t ∈ Ioi (1 : ℝ), ‖h t‖ₑ ^ 2
        = ENNReal.ofReal (A ^ 2) * ‖(t : ℝ) • b (ε * t)‖ₑ ^ 2 := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      have hsm : h t = A • ((t : ℝ) • b (ε * t)) := by
        rw [hhdef]
        simp only
        rw [smul_smul]
      rw [hsm, enorm_smul, mul_pow, Real.enorm_eq_ofReal_abs,
        abs_of_pos hApos, ← ENNReal.ofReal_pow hApos.le]
    rw [setLIntegral_congr_fun measurableSet_Ioi hrw,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmom
  exact HTGeometry.lintegral_enorm_sq_lt_top_of_hardyBound hp hKpos.le (norm_nonneg c)
    hbound hhmeas hhfin

end GaloisForLFunctions.RHTower
