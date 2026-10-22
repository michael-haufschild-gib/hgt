import GaloisForLFunctions.RHTower.GammaRatioStripUniform
import GaloisForLFunctions.RHTower.Suzuki.SuzukiForcedStripHolomorphy

/-!
# The Gamma transport and its inverse on a closed lower substrip

On the closed substrip `0 ≤ Im z ≤ σ₁ < 1` the Gamma transport `Q(z)` is bounded, and its inverse
grows at most linearly:

`‖Q(z)‖ ≤ K,     ‖Q(z)^{-1}‖ ≤ A (1 + ‖z‖)`.

Both come from the two-sided substrip-uniform bound for the Gamma quotient: the branch satisfies
`‖E z‖² = ‖Γ(1+iz)/Γ(1-iz)‖`, so the transport carries the square root of the quotient and the
inverse transport its reciprocal, while the operator factor is `e^{|Im z|‖T‖/2}` by
self-adjointness.  The linear bound is the crude form of `(1+‖z‖)^{σ₁}`, which suffices because the
inverse only ever appears against a test transform decaying faster than every power.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- On the closed lower substrip the Gamma quotient of a point is the substrip pair value. -/
theorem norm_gammaRatio_eq_pair (z : ℂ) :
    ‖gammaRatio z‖ = gammaRatioPair (z.im, z.re) := by
  have harg : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := by
    simp
  simp only [gammaRatioPair]
  rw [← norm_gammaRatio_shift z.im z.re, harg]

/-- The branch modulus on the substrip is the square root of the Gamma quotient. -/
theorem norm_branch_sq (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {z : ℂ}
    (hz : z ∈ imStrip (-1) 1) : ‖E z‖ ^ 2 = gammaRatioPair (z.im, z.re) := by
  rw [← norm_pow, hE z hz, norm_gammaRatio_eq_pair]

private theorem mem_imStrip_of_mem_lower {σ₁ : ℝ} (h1 : σ₁ < 1) {z : ℂ}
    (hz : z.im ∈ Icc (0 : ℝ) σ₁) : z ∈ imStrip (-1) 1 :=
  ⟨by linarith [hz.1], by linarith [hz.2]⟩

/-- **The transport is bounded on the closed lower substrip.** -/
theorem exists_bound_stripTransport_substrip (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ₁ : ℝ} (h0 : 0 ≤ σ₁) (h1 : σ₁ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, z.im ∈ Icc (0 : ℝ) σ₁ → ‖stripTransport E T z‖ ≤ K := by
  obtain ⟨c, C, hc, hC, hpair⟩ := exists_twoSided_gammaRatioPair h0 h1
  refine ⟨Real.exp (|Real.eulerMascheroniConstant| * σ₁) * Real.sqrt C
    * Real.exp (σ₁ / 2 * ‖T‖), by positivity, fun z hz => ?_⟩
  have hzstrip : z ∈ imStrip (-1) 1 := mem_imStrip_of_mem_lower h1 hz
  have hphase : ‖Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z)‖
      = Real.exp (-(Real.eulerMascheroniConstant * z.im)) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hphasele : Real.exp (-(Real.eulerMascheroniConstant * z.im))
      ≤ Real.exp (|Real.eulerMascheroniConstant| * σ₁) := by
    refine Real.exp_le_exp.mpr ?_
    calc -(Real.eulerMascheroniConstant * z.im) ≤ |Real.eulerMascheroniConstant * z.im| :=
          neg_le_abs _
      _ = |Real.eulerMascheroniConstant| * |z.im| := abs_mul _ _
      _ ≤ |Real.eulerMascheroniConstant| * σ₁ := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_of_nonneg hz.1]
          exact hz.2
  have hbranch : ‖E z‖ ≤ Real.sqrt C := by
    have hsq : ‖E z‖ ^ 2 = gammaRatioPair (z.im, z.re) := norm_branch_sq hE hzstrip
    have hle : ‖E z‖ ^ 2 ≤ C := by
      rw [hsq]
      exact (hpair z.im ⟨hz.1, hz.2⟩ z.re).2
    calc ‖E z‖ = Real.sqrt (‖E z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt C := Real.sqrt_le_sqrt hle
  have hop : ‖NormedSpace.exp ((-(Complex.I / 2) * z) • T)‖ ≤ Real.exp (σ₁ / 2 * ‖T‖) := by
    have hre : (-(Complex.I / 2) * z).re = z.im / 2 := by
      simp
      ring
    have hb := norm_exp_smul_le hT (-(Complex.I / 2) * z)
    rw [hre] at hb
    refine le_trans hb (Real.exp_le_exp.mpr ?_)
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg T)
    rw [abs_of_nonneg (by linarith [hz.1] : (0 : ℝ) ≤ z.im / 2)]
    linarith [hz.2]
  calc ‖stripTransport E T z‖
      = ‖Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z‖
        * ‖NormedSpace.exp ((-(Complex.I / 2) * z) • T)‖ := by
        rw [stripTransport, norm_smul]
    _ = Real.exp (-(Real.eulerMascheroniConstant * z.im)) * ‖E z‖
        * ‖NormedSpace.exp ((-(Complex.I / 2) * z) • T)‖ := by rw [norm_mul, hphase]
    _ ≤ Real.exp (|Real.eulerMascheroniConstant| * σ₁) * Real.sqrt C
        * Real.exp (σ₁ / 2 * ‖T‖) := by
        refine mul_le_mul (mul_le_mul hphasele hbranch (norm_nonneg _) (by positivity)) hop
          (norm_nonneg _) (by positivity)

/-- **The inverse transport grows at most linearly on the closed lower substrip.** -/
theorem exists_bound_stripTransportInv_substrip (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ₁ : ℝ} (h0 : 0 ≤ σ₁) (h1 : σ₁ < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, z.im ∈ Icc (0 : ℝ) σ₁ →
      ‖stripTransportInv E T z‖ ≤ A * (1 + ‖z‖) := by
  obtain ⟨c, C, hc, hC, hpair⟩ := exists_twoSided_gammaRatioPair h0 h1
  refine ⟨Real.exp (|Real.eulerMascheroniConstant| * σ₁) * (Real.sqrt c)⁻¹
    * Real.exp (σ₁ / 2 * ‖T‖), by positivity, fun z hz => ?_⟩
  have hzstrip : z ∈ imStrip (-1) 1 := mem_imStrip_of_mem_lower h1 hz
  have hzre : (0 : ℝ) < 1 + |z.re| := by positivity
  have hphase : ‖Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z)‖
      = Real.exp (-(Real.eulerMascheroniConstant * z.im)) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hphasele : (Real.exp (-(Real.eulerMascheroniConstant * z.im)))⁻¹
      ≤ Real.exp (|Real.eulerMascheroniConstant| * σ₁) := by
    rw [← Real.exp_neg]
    refine Real.exp_le_exp.mpr ?_
    calc -(-(Real.eulerMascheroniConstant * z.im))
        ≤ |Real.eulerMascheroniConstant * z.im| := by
          rw [neg_neg]
          exact le_abs_self _
      _ = |Real.eulerMascheroniConstant| * |z.im| := abs_mul _ _
      _ ≤ |Real.eulerMascheroniConstant| * σ₁ := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_of_nonneg hz.1]
          exact hz.2
  -- the branch is bounded below by the substrip lower bound
  have hbranchpos : 0 < ‖E z‖ := by
    have hsq : ‖E z‖ ^ 2 = gammaRatioPair (z.im, z.re) := norm_branch_sq hE hzstrip
    have hpos : 0 < gammaRatioPair (z.im, z.re) := gammaRatioPair_pos h1 ⟨hz.1, hz.2⟩
    nlinarith [norm_nonneg (E z), hsq, hpos]
  have hbranchlow : (Real.sqrt c) * (1 + |z.re|) ^ (-σ₁) ≤ ‖E z‖ := by
    have hsq : ‖E z‖ ^ 2 = gammaRatioPair (z.im, z.re) := norm_branch_sq hE hzstrip
    have hlow : c * (1 + |z.re|) ^ (-(2 * σ₁)) ≤ ‖E z‖ ^ 2 := by
      rw [hsq]
      exact (hpair z.im ⟨hz.1, hz.2⟩ z.re).1
    have hrw : Real.sqrt (c * (1 + |z.re|) ^ (-(2 * σ₁)))
        = Real.sqrt c * (1 + |z.re|) ^ (-σ₁) := by
      rw [Real.sqrt_mul hc.le]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hzre.le]
      congr 1
      ring
    calc Real.sqrt c * (1 + |z.re|) ^ (-σ₁)
        = Real.sqrt (c * (1 + |z.re|) ^ (-(2 * σ₁))) := hrw.symm
      _ ≤ Real.sqrt (‖E z‖ ^ 2) := Real.sqrt_le_sqrt hlow
      _ = ‖E z‖ := Real.sqrt_sq (norm_nonneg _)
  have hbranchinv : (‖E z‖)⁻¹ ≤ (Real.sqrt c)⁻¹ * (1 + ‖z‖) := by
    have hpos : 0 < Real.sqrt c * (1 + |z.re|) ^ (-σ₁) :=
      mul_pos (Real.sqrt_pos.mpr hc) (Real.rpow_pos_of_pos hzre _)
    have hstep := one_div_le_one_div_of_le hpos hbranchlow
    rw [one_div, one_div] at hstep
    refine le_trans hstep ?_
    rw [mul_inv, Real.rpow_neg hzre.le, inv_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hle1 : (1 + |z.re|) ^ σ₁ ≤ (1 + ‖z‖) ^ σ₁ := by
      refine Real.rpow_le_rpow hzre.le ?_ h0
      have := Complex.abs_re_le_norm z
      linarith
    have hle2 : (1 + ‖z‖) ^ σ₁ ≤ (1 + ‖z‖) ^ (1 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      have := norm_nonneg z
      linarith
    rw [Real.rpow_one] at hle2
    linarith
  have hop : ‖NormedSpace.exp (((Complex.I / 2) * z) • T)‖ ≤ Real.exp (σ₁ / 2 * ‖T‖) := by
    have hre : ((Complex.I / 2) * z).re = -(z.im / 2) := by
      simp
      ring
    have hb := norm_exp_smul_le hT ((Complex.I / 2) * z)
    rw [hre] at hb
    refine le_trans hb (Real.exp_le_exp.mpr ?_)
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg T)
    rw [abs_of_nonpos (by linarith [hz.1] : -(z.im / 2) ≤ (0 : ℝ)), neg_neg]
    linarith [hz.2]
  have hscalar : ‖(Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z)⁻¹‖
      ≤ Real.exp (|Real.eulerMascheroniConstant| * σ₁) * ((Real.sqrt c)⁻¹ * (1 + ‖z‖)) := by
    rw [norm_inv, norm_mul, hphase, mul_inv]
    exact mul_le_mul hphasele hbranchinv (by positivity) (by positivity)
  calc ‖stripTransportInv E T z‖
      = ‖(Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z) * E z)⁻¹‖
        * ‖NormedSpace.exp (((Complex.I / 2) * z) • T)‖ := by
        rw [stripTransportInv, norm_smul]
    _ ≤ (Real.exp (|Real.eulerMascheroniConstant| * σ₁) * ((Real.sqrt c)⁻¹ * (1 + ‖z‖)))
        * Real.exp (σ₁ / 2 * ‖T‖) :=
        mul_le_mul hscalar hop (norm_nonneg _) (by positivity)
    _ = Real.exp (|Real.eulerMascheroniConstant| * σ₁) * (Real.sqrt c)⁻¹
        * Real.exp (σ₁ / 2 * ‖T‖) * (1 + ‖z‖) := by ring

/-- **Polynomial growth of the particular solution on a closed lower substrip.**  The transport is
bounded, the inverse transport grows linearly, and the segment stays inside the substrip, so the
branch-free kernel grows by one more power and the outer factor `z` by one more still. -/
theorem exists_bound_forcedParticular_substrip (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) {σ₁ : ℝ} (h0 : 0 ≤ σ₁) (h1 : σ₁ < 1)
    {b : ℂ → X} {D : ℝ} {n : ℕ} (hD : 0 ≤ D)
    (hb : ∀ w : ℂ, w.im ∈ Icc (0 : ℝ) σ₁ → ‖b w‖ ≤ D * (1 + ‖w‖) ^ n) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ z : ℂ, z.im ∈ Icc (0 : ℝ) σ₁ →
      ‖forcedParticular E T b z‖ ≤ P * (1 + ‖z‖) ^ (n + 2) := by
  obtain ⟨K, hK, hKb⟩ := exists_bound_stripTransport_substrip hT hE h0 h1
  obtain ⟨A, hA, hAb⟩ := exists_bound_stripTransportInv_substrip hT hE h0 h1
  refine ⟨K * (A * D), by positivity, fun z hz => ?_⟩
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hone : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith
  -- the segment stays inside the substrip and inside the disc of radius ‖z‖
  have hseg : ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) 1 →
      (z * (s : ℂ)).im ∈ Icc (0 : ℝ) σ₁ ∧ ‖z * (s : ℂ)‖ ≤ ‖z‖ := by
    intro s hs
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hs0 : 0 < s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have him : (z * (s : ℂ)).im = z.im * s := by simp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [him]
      exact mul_nonneg hz.1 hs0.le
    · rw [him]
      nlinarith [hz.1, hz.2, hs0, hs1]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
      nlinarith [hz0, hs1, hs0]
  -- the branch-free kernel
  have hker : ‖forcedParticularKernel E T b z‖ ≤ A * D * (1 + ‖z‖) ^ (n + 1) := by
    have hbnd : ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) 1 →
        ‖((s : ℂ) ^ ((1 : ℂ) / 2))
            • stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))‖
          ≤ A * D * (1 + ‖z‖) ^ (n + 1) := by
      intro s hs
      obtain ⟨hsim, hsnorm⟩ := hseg s hs
      have hsIcc : s ∈ Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
        exact ⟨hs.1.le, hs.2⟩
      have hw : (0 : ℝ) < 1 + ‖z * (s : ℂ)‖ := by positivity
      have hinner : ‖stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))‖
          ≤ A * D * (1 + ‖z‖) ^ (n + 1) := by
        have hop := hAb (z * (s : ℂ)) hsim
        have hvec := hb (z * (s : ℂ)) hsim
        have hstep1 : (1 : ℝ) + ‖z * (s : ℂ)‖ ≤ 1 + ‖z‖ := by linarith
        calc ‖stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))‖
            ≤ ‖stripTransportInv E T (z * (s : ℂ))‖ * ‖b (z * (s : ℂ))‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ (A * (1 + ‖z * (s : ℂ)‖)) * (D * (1 + ‖z * (s : ℂ)‖) ^ n) :=
              mul_le_mul hop hvec (norm_nonneg _) (by positivity)
          _ ≤ (A * (1 + ‖z‖)) * (D * (1 + ‖z‖) ^ n) := by
              refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
              · exact mul_le_mul_of_nonneg_left hstep1 hA.le
              · exact mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ hw.le hstep1 n) hD
          _ = A * D * (1 + ‖z‖) ^ (n + 1) := by ring
      calc ‖((s : ℂ) ^ ((1 : ℂ) / 2))
              • stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))‖
          = ‖((s : ℂ) ^ ((1 : ℂ) / 2))‖
              * ‖stripTransportInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))‖ := norm_smul _ _
        _ ≤ 1 * (A * D * (1 + ‖z‖) ^ (n + 1)) :=
            mul_le_mul (norm_cpowHalf_le_one s hsIcc) hinner (norm_nonneg _) (by norm_num)
        _ = A * D * (1 + ‖z‖) ^ (n + 1) := one_mul _
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    simpa [forcedParticularKernel] using this
  rw [forcedParticular_eq_total E T b z, norm_smul]
  calc ‖z‖ * ‖stripTransport E T z (forcedParticularKernel E T b z)‖
      ≤ (1 + ‖z‖) * (K * (A * D * (1 + ‖z‖) ^ (n + 1))) := by
        refine mul_le_mul (by linarith) ?_ (norm_nonneg _) (by linarith)
        calc ‖stripTransport E T z (forcedParticularKernel E T b z)‖
            ≤ ‖stripTransport E T z‖ * ‖forcedParticularKernel E T b z‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ K * (A * D * (1 + ‖z‖) ^ (n + 1)) :=
              mul_le_mul (hKb z hz) hker (norm_nonneg _) hK.le
    _ = K * (A * D) * (1 + ‖z‖) ^ (n + 2) := by ring

end GaloisForLFunctions.RHTower
