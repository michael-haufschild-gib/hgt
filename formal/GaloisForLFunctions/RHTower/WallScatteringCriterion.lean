import GaloisForLFunctions.RHTower.WallScatteringCharge
import GaloisForLFunctions.RHTower.WallFrequencyFirstBoundary
import GaloisForLFunctions.RHTower.WallForcedProfileMemLp
import GaloisForLFunctions.RHTower.ScatteringChargeNecessity

/-!
# `(47)`: the Gamma derivative scattering criterion

Multiplication by the frequency is physical differentiation, and the homogeneous derivative carrier
`xH(x+i\sigma)` is not square integrable for any `0 < \sigma < 1`.  So the frequency-weighted profile
can only be square integrable if the vector the propagator carries out to infinity vanishes.

The three-fold expansion isolates that vector: everything else in the profile is either one of the
three boundary amplitudes at the moving endpoint — each of which loses exactly one power to the
frequency and keeps enough decay — or the absolutely convergent tail past it, which is `O(x^{-2})`
after transport.  What remains is `xH(x+i\sigma)d_+`, and `(42)` in its vector form says that term is
square integrable only when `d_+ = 0`.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- **The transported ray remainder survives multiplication by the frequency.**  `(48)` gives it
`O(x^{-2})`; one power is spent on the frequency and one remains. -/
theorem norm_freq_smul_transported_wallTailVector_le {σ x μ₀ K₁ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g : ℝ → X} (hg : IntegrableOn g (Icc m (m + 1))) {A : ℝ}
    (hA : (∫ L in Icc m (m + 1), ‖g L‖) ≤ A) (hx : 1 ≤ x)
    (hgap : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Ioi x, μ₀ ≤ wallFloor T σ t + L) :
    ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (wallTailVector E T g m σ x)‖
      ≤ (2 * (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * A)
        * (1 + |x|) ^ (-(1 : ℝ)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hxabs : |x| = x := abs_of_pos hx0
  have hC3 : (0 : ℝ) ≤ wallAmplitude3Const μ₀ := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [wallAmplitude3Const]
    positivity
  have hden : (0 : ℝ) < 2 - (1 / 2 + σ) := by linarith
  have hCt : (0 : ℝ) ≤ K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)) := by positivity
  have hAnn : (0 : ℝ) ≤ ∫ L in Icc m (m + 1), ‖g L‖ :=
    setIntegral_nonneg measurableSet_Icc fun L _ => norm_nonneg _
  have hA0 : (0 : ℝ) ≤ A := le_trans hAnn hA
  have hIx := integrableOn_wallTailOperator_apply hEdiff hE hEne hσ0 hσ1 hμ hb₂ hK₂ hg hx hgap
  have hcomm : stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (wallTailVector E T g m σ x)
      = ∫ L in Icc m (m + 1), stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallTailOperator E T σ L x (g L)) :=
    (ContinuousLinearMap.integral_comp_comm _ hIx).symm
  have hbd : ∀ L ∈ Icc m (m + 1),
      ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallTailOperator E T σ L x (g L))‖
        ≤ ((K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * x ^ (-(2 : ℝ))) * ‖g L‖ := by
    intro L hL
    rw [← mul_apply_eq_comp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact norm_wallThirdTail_transported_le hσ0 hσ1 hμ hb₁ hK₁ hb₂ hK₂ hx
      (fun t ht => hgap L hL t ht)
  have hle := MeasureTheory.norm_integral_le_of_norm_le (hg.norm.const_mul _)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL using hbd L hL)
  rw [integral_const_mul] at hle
  rw [← hcomm] at hle
  have hstep : ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
      (wallTailVector E T g m σ x)‖
      ≤ x * (((K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * x ^ (-(2 : ℝ)))
        * ∫ L in Icc m (m + 1), ‖g L‖) := by
    rw [norm_smul, Real.norm_eq_abs, hxabs]
    exact mul_le_mul_of_nonneg_left hle hx0.le
  have hpow : x * x ^ (-(2 : ℝ)) = x ^ (-(1 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hinv : x ^ (-(1 : ℝ)) ≤ 2 * (1 + x) ^ (-(1 : ℝ)) := by
    have h1x : (0 : ℝ) < 1 + x := by linarith
    rw [Real.rpow_neg_one, Real.rpow_neg_one, ← sub_nonneg]
    have heq : 2 * (1 + x)⁻¹ - x⁻¹ = (2 * x - (1 + x)) / (x * (1 + x)) := by
      field_simp
    rw [heq]
    exact div_nonneg (by linarith) (by positivity)
  calc ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) (wallTailVector E T g m σ x)‖
      ≤ x * (((K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * x ^ (-(2 : ℝ)))
        * ∫ L in Icc m (m + 1), ‖g L‖) := hstep
    _ = (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
        * (x ^ (-(1 : ℝ)) * ∫ L in Icc m (m + 1), ‖g L‖) := by
          rw [← hpow]; ring
    _ ≤ (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
        * ((2 * (1 + x) ^ (-(1 : ℝ))) * A) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hinv hA hAnn (by positivity)) hCt
    _ = (2 * (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ))) * A)
        * (1 + |x|) ^ (-(1 : ℝ)) := by rw [hxabs]; ring


/-- The part of the point-dependent remainder that is estimated by a bare power tail. -/
def wallRestPart (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ x : ℝ) : X :=
  secondBoundary T g m σ x - (Complex.I : ℂ) • thirdBoundary T g m σ x
    - (Complex.I : ℂ) • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (wallTailVector E T g m σ x)

theorem wallScatteringRemainder_eq (E : ℂ → ℂ) (T : X →L[ℂ] X) (g : ℝ → X) (m σ x : ℝ) :
    wallScatteringRemainder E T g m σ x
      = (-(Complex.I) / 2 : ℂ) • ((Complex.I : ℂ) • firstBoundaryBlock T g m σ x
          + wallRestPart E T g m σ x) := by
  rw [wallScatteringRemainder, wallRestPart]
  module

/-- **The three remaining point-dependent terms decay like `x^{-1}` after multiplication by the
frequency.** -/
theorem norm_freq_smul_wallRestPart_le {σ x μ₀ K₁ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g g' : ℝ → X} (hgd : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hg : IntegrableOn g (Icc m (m + 1))) (hg' : IntegrableOn g' (Icc m (m + 1)))
    (hx : 1 ≤ x)
    (hfloor : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L)
    (hgapR : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Ioi x, μ₀ ≤ wallFloor T σ t + L) :
    ‖x • wallRestPart E T g m σ x‖
      ≤ ((3 * (μ₀⁻¹) ^ 4 * (3 + Real.pi) * (∫ L in Icc m (m + 1), ‖g L‖)
            + (μ₀⁻¹) ^ 3 * (3 + Real.pi) * (∫ L in Icc m (m + 1), ‖g' L‖))
          + (μ₀⁻¹ * wallAmplitudeConst μ₀) * (∫ L in Icc m (m + 1), ‖g L‖)
          + 2 * (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
              * (∫ L in Icc m (m + 1), ‖g L‖))
        * (1 + |x|) ^ (-(1 : ℝ)) := by
  have hxabs : (1 : ℝ) ≤ |x| := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
    exact hx
  have h2 := norm_freq_smul_secondBoundary_le (T := T) hσ0 hσ1 hμ hgd hsupp hg hg'
    (le_refl (∫ L in Icc m (m + 1), ‖g L‖)) (le_refl (∫ L in Icc m (m + 1), ‖g' L‖)) hxabs hfloor
  have h3 := norm_freq_smul_thirdBoundary_le (T := T) hσ0 hσ1 hμ hg
    (le_refl (∫ L in Icc m (m + 1), ‖g L‖)) hxabs hfloor
  have h4 := norm_freq_smul_transported_wallTailVector_le hEdiff hE hEne hσ0 hσ1 hμ hb₁ hK₁
    hb₂ hK₂ hg (le_refl (∫ L in Icc m (m + 1), ‖g L‖)) hx hgapR
  have hsmul : ∀ u : X, ‖x • ((Complex.I : ℂ) • u)‖ = ‖x • u‖ := by
    intro u
    rw [smul_comm, norm_smul, Complex.norm_I, one_mul]
  have hsplit : x • wallRestPart E T g m σ x
      = x • secondBoundary T g m σ x - x • ((Complex.I : ℂ) • thirdBoundary T g m σ x)
        - x • ((Complex.I : ℂ) • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
            (wallTailVector E T g m σ x)) := by
    rw [wallRestPart, smul_sub, smul_sub]
  rw [hsplit]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_sub_le _ _) (le_of_eq (hsmul _))) ?_
  rw [hsmul]
  have hw : (0 : ℝ) < (1 + |x|) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  nlinarith [h2, h3, h4, hw]


variable [Nontrivial X]

omit [Nontrivial X] in
/-- **All point-dependent terms of the three-fold expansion are square integrable after
multiplication by the frequency.** -/
theorem lintegral_sq_freq_wallScatteringRemainder_ne_top {σ Y μ₀ K₁ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 ≤ K₂)
    {g g' : ℝ → X} (hgd : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgm : StronglyMeasurable g)
    (hg'2 : MemLp g' 2 (volume : Measure ℝ))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hg : IntegrableOn g (Icc m (m + 1))) (hg' : IntegrableOn g' (Icc m (m + 1)))
    (hY : 1 ≤ Y) (hfloor : ∀ x ∈ Ioi Y, μ₀ - m ≤ wallFloor T σ x) :
    (∫⁻ x in Ioi Y, ‖x • wallScatteringRemainder E T g m σ x‖ₑ ^ 2) ≠ ⊤ := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hx1 : ∀ x ∈ Ioi Y, (1 : ℝ) ≤ x := fun x hx => le_trans hY (le_of_lt hx)
  have hfloorL : ∀ x ∈ Ioi Y, ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L := by
    intro x hx L hL
    have hm : m ≤ L := hL.1
    have := hfloor x hx
    linarith
  have hgapR : ∀ x ∈ Ioi Y, ∀ L ∈ Icc m (m + 1), ∀ t ∈ Ioi x, μ₀ ≤ wallFloor T σ t + L := by
    intro x hx L hL t ht
    exact hfloorL t (mem_Ioi.mpr (lt_trans (mem_Ioi.mp hx) (mem_Ioi.mp ht))) L hL
  -- the first boundary term
  have h1 : (∫⁻ x in Ioi Y, ‖x • firstBoundaryBlock T g m σ x‖ₑ ^ 2) ≠ ⊤ := by
    have hbase := lintegral_sq_freqFirstBoundary_le (T := T) (A := Ioi Y) measurableSet_Ioi
      hσ0 hσ1 hμ hgd hg2 hgm hg'2 hsupp hfloor
    rw [lintegral_sq_indicator_eq measurableSet_Ioi] at hbase
    have hcongr : (∫⁻ x in Ioi Y, ‖x • firstBoundaryBlock T g m σ x‖ₑ ^ 2)
        = ∫⁻ x in Ioi Y, ‖x • firstBoundary T g σ x‖ₑ ^ 2 := by
      refine lintegral_congr fun x => ?_
      rw [firstBoundaryBlock_eq_firstBoundary hsupp]
    intro htop
    rw [← hcongr, htop, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hbase
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hbase)
  -- the remaining three terms
  have hrest : (∫⁻ x in Ioi Y, ‖x • wallRestPart E T g m σ x‖ₑ ^ 2) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_sq_ray_powerTail_le
      (f := fun x : ℝ => x • wallRestPart E T g m σ x) (p := 1) (Y := Y)
      (C := (3 * (μ₀⁻¹) ^ 4 * (3 + Real.pi) * (∫ L in Icc m (m + 1), ‖g L‖)
            + (μ₀⁻¹) ^ 3 * (3 + Real.pi) * (∫ L in Icc m (m + 1), ‖g' L‖))
          + (μ₀⁻¹ * wallAmplitudeConst μ₀) * (∫ L in Icc m (m + 1), ‖g L‖)
          + 2 * (K₁ * (K₂ * wallAmplitude3Const μ₀) / (2 - (1 / 2 + σ)))
              * (∫ L in Icc m (m + 1), ‖g L‖))
      (by norm_num) hY0 (fun x hx => ?_))
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · have := norm_freq_smul_wallRestPart_le hEdiff hE hEne hσ0 hσ1 hμ hb₁ hK₁ hb₂ hK₂
        hgd hsupp hg hg' (hx1 x hx) (fun L hL => hfloorL x hx L hL)
        (fun L hL t ht => hgapR x hx L hL t ht)
      simpa using this
  -- assemble
  have hpair : ∀ u v : ℝ≥0∞, (u + v) ^ 2 ≤ 4 * (u ^ 2 + v ^ 2) := by
    intro u v
    have hle : u + v ≤ 2 * max u v :=
      (add_le_add (le_max_left u v) (le_max_right u v)).trans (by rw [two_mul])
    have hmax : max u v ^ 2 ≤ u ^ 2 + v ^ 2 := by
      rcases max_choice u v with h | h <;> rw [h]
      · exact le_self_add
      · exact le_add_self
    calc (u + v) ^ 2 ≤ (2 * max u v) ^ 2 := pow_le_pow_left' hle 2
      _ = 4 * max u v ^ 2 := by ring
      _ ≤ 4 * (u ^ 2 + v ^ 2) := mul_le_mul' le_rfl hmax
  have hcoef : ‖(-(Complex.I) / 2 : ℂ)‖ₑ ≤ 1 := by
    have hc : ‖(-(Complex.I) / 2 : ℂ)‖ ≤ 1 := by
      rw [norm_div, norm_neg, Complex.norm_I]
      norm_num
    calc ‖(-(Complex.I) / 2 : ℂ)‖ₑ = ENNReal.ofReal ‖(-(Complex.I) / 2 : ℂ)‖ :=
          (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hc
      _ = 1 := by simp
  have hsq : ∀ x : ℝ, ‖x • wallScatteringRemainder E T g m σ x‖ₑ ^ 2
      ≤ 4 * (‖x • firstBoundaryBlock T g m σ x‖ₑ ^ 2 + ‖x • wallRestPart E T g m σ x‖ₑ ^ 2) := by
    intro x
    have hstep : x • wallScatteringRemainder E T g m σ x
        = (-(Complex.I) / 2 : ℂ) • ((Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)
            + x • wallRestPart E T g m σ x) := by
      rw [wallScatteringRemainder_eq]
      module
    have hnorm : ‖x • wallScatteringRemainder E T g m σ x‖ₑ
        ≤ ‖x • firstBoundaryBlock T g m σ x‖ₑ + ‖x • wallRestPart E T g m σ x‖ₑ := by
      rw [hstep, enorm_smul]
      calc ‖(-(Complex.I) / 2 : ℂ)‖ₑ * ‖(Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)
              + x • wallRestPart E T g m σ x‖ₑ
          ≤ 1 * ‖(Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)
              + x • wallRestPart E T g m σ x‖ₑ := mul_le_mul' hcoef le_rfl
        _ = ‖(Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)
              + x • wallRestPart E T g m σ x‖ₑ := one_mul _
        _ ≤ ‖(Complex.I : ℂ) • (x • firstBoundaryBlock T g m σ x)‖ₑ
              + ‖x • wallRestPart E T g m σ x‖ₑ := enorm_add_le _ _
        _ = ‖x • firstBoundaryBlock T g m σ x‖ₑ + ‖x • wallRestPart E T g m σ x‖ₑ := by
              have hI : ‖(Complex.I : ℂ)‖ₑ = 1 := by
                rw [← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one]
              rw [enorm_smul, hI, one_mul]
    exact le_trans (pow_le_pow_left' hnorm 2) (hpair _ _)
  have hmeasFB : AEMeasurable
      (fun x : ℝ => ‖x • firstBoundaryBlock T g m σ x‖ₑ ^ 2) (volume.restrict (Ioi Y)) := by
    have hFB := aestronglyMeasurable_firstBoundaryBlock (T := T) hσ0 hσ1 measurableSet_Ioi
      hg.aestronglyMeasurable
      (fun x hx L hL => lt_of_lt_of_le hμ (hfloorL x hx L hL))
    exact ((continuous_id.aestronglyMeasurable.smul hFB).enorm).pow_const 2
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hsq)
  rw [lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤), lintegral_add_left' hmeasFB]
  exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨h1, hrest⟩)


/-- **`(47)`: the Gamma derivative scattering criterion, on the outward ray.**  The frequency-weighted
profile is square integrable on a terminal ray exactly when the outgoing charge vanishes. -/
theorem lintegral_sq_freq_forcedProfile_ray_ne_top_iff {σ Y μ₀ K₁ K₂ m : ℝ}
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0) (hT : IsSelfAdjoint T)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    (hb₁ : ∀ y : ℝ, ‖stripPropagator E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₁ * (1 + |y|) ^ (-(1 / 2 + σ))) (hK₁ : 0 ≤ K₁)
    (hb₂ : ∀ y : ℝ, ‖stripPropagatorInv E T ((y : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |y|) ^ (1 / 2 + σ)) (hK₂ : 0 < K₂)
    {g g' : ℝ → X} (hgd : ∀ L : ℝ, HasDerivAt g (g' L) L)
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hgm : StronglyMeasurable g)
    (hg'2 : MemLp g' 2 (volume : Measure ℝ))
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0)
    (hg : IntegrableOn g (Icc m (m + 1))) (hg' : IntegrableOn g' (Icc m (m + 1)))
    (c : X) (hY : 1 ≤ Y) (hfloor : ∀ x ∈ Ici Y, μ₀ - m ≤ wallFloor T σ x) :
    (∫⁻ x in Ioi Y, ‖x • forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2) ≠ ⊤
      ↔ wallScatteringCharge E T g c m σ Y = 0 := by
  have hIoi : ∀ x ∈ Ioi Y, μ₀ - m ≤ wallFloor T σ x :=
    fun x hx => hfloor x (mem_Ici.mpr (le_of_lt (mem_Ioi.mp hx)))
  have hfloorL : ∀ x : ℝ, Y ≤ x → ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L := by
    intro x hx L hL
    have hm : m ≤ L := hL.1
    have := hfloor x hx
    linarith
  have hgapR : ∀ L ∈ Icc m (m + 1), ∀ t ∈ Ioi Y, μ₀ ≤ wallFloor T σ t + L :=
    fun L hL t ht => hfloorL t (le_of_lt ht) L hL
  have hdecomp : ∀ x ∈ Ioi Y, x • forcedProfile E T (blockSource g m) c σ x
      = x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (wallScatteringCharge E T g c m σ Y)
        + x • wallScatteringRemainder E T g m σ x := by
    intro x hx
    have hYx : Y ≤ x := le_of_lt hx
    have hgapI : ∀ L ∈ Icc m (m + 1), ∀ t ∈ uIcc Y x, 0 < wallFloor T σ t + L := by
      intro L hL t ht
      rw [Set.uIcc_of_le hYx] at ht
      exact lt_of_lt_of_le hμ (hfloorL t ht.1 L hL)
    rw [forcedProfile_eq_charge_add_remainder hEdiff hE hEne hT hσ0 hσ1 hμ hb₂ hK₂.le hg c hY hYx
      (hfloorL x hYx) (hfloorL Y le_rfl) hgapI hgapR, smul_add]
  have hcongr : (∫⁻ x in Ioi Y, ‖x • forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
      = ∫⁻ x in Ioi Y, ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
            (wallScatteringCharge E T g c m σ Y)
          + x • wallScatteringRemainder E T g m σ x‖ₑ ^ 2 :=
    setLIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [hdecomp x hx])
  have hH : Continuous fun x : ℝ => stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) :=
    continuous_stripPropagator_line hEdiff hE hEne hσ0 hσ1
  have hleadm : AEStronglyMeasurable
      (fun x : ℝ => x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (wallScatteringCharge E T g c m σ Y)) (volume.restrict (Ioi Y)) :=
    (continuous_id.smul (hH.clm_apply continuous_const)).aestronglyMeasurable
  have htotm : AEStronglyMeasurable
      (fun x : ℝ => x • forcedProfile E T (blockSource g m) c σ x) (volume.restrict (Ioi Y)) :=
    (continuous_id.smul
      (continuous_forcedProfile_blockSource hEdiff hE hEne hσ0 hσ1 hg c)).aestronglyMeasurable
  have hremm : AEStronglyMeasurable
      (fun x : ℝ => x • wallScatteringRemainder E T g m σ x) (volume.restrict (Ioi Y)) := by
    refine (htotm.sub hleadm).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Pi.sub_apply]
    rw [hdecomp x hx]
    abel
  have hrem := lintegral_sq_freq_wallScatteringRemainder_ne_top hEdiff hE hEne hσ0 hσ1 hμ
    hb₁ hK₁ hb₂ hK₂.le hgd hg2 hgm hg'2 hsupp hg hg' hY hIoi
  constructor
  · intro htot
    by_contra hne
    have hlead : (∫⁻ x in Ioi Y, ‖x • stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (wallScatteringCharge E T g c m σ Y)‖ₑ ^ 2) = ⊤ :=
      lintegral_sq_freq_stripPropagator_eq_top hσ0 hσ1 hE hb₂ hK₂ hY hne
    exact htot (hcongr.trans (lintegral_sq_add_eq_top hleadm hremm hlead hrem))
  · intro hzero
    rw [hcongr, hzero]
    simpa using hrem

end GaloisForLFunctions.RHTower
