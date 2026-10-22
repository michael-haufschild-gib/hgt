import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.RHTower.ThetaWignerCenterMix
import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic
import GaloisForLFunctions.RHTower.Sieve.LogPolySetScaling
import GaloisForLFunctions.RHTower.ComplementaryPacketCofinalIsometry

/-!
# Positive theta tail first-moment kernel

This module constructs the literal tail first-moment kernel of the completed theta-cusp source.
It proves absolute integrability, symmetry, pointwise nonnegativity, the equivalent shifted-tail
formula, and the exact two-channel Krein factorization.  In particular, positivity is proved from
the even-source cancellation on the negative half-line; it is not inferred from the shifted
integrand, whose sign can change.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- Integrand defining the theta tail first-moment kernel. -/
def thetaTailFirstMomentIntegrand (x t u : ℝ) : ℝ :=
  u * thetaCuspFullSource ((u + x - t) / 2) *
    thetaCuspFullSource ((u - x + t) / 2)

lemma integrable_thetaTailFirstMomentIntegrand (x t : ℝ) :
    Integrable (thetaTailFirstMomentIntegrand x t) := by
  let C : ℝ := thetaCuspDerivativeExpConstant 0
  have hC : 0 ≤ C := by
    have h := abs_thetaCuspFullSource_le_exp_neg_abs 0
    have hp := HedenmalmThetaSource.thetaCuspFullSource_pos 0
    have hle : thetaCuspFullSource 0 ≤ C := by
      simpa [C, abs_of_pos hp] using h
    exact le_trans hp.le hle
  have hk : Continuous thetaCuspFullSource := contDiff_thetaCuspFullSource.continuous
  have hmeas : AEStronglyMeasurable (thetaTailFirstMomentIntegrand x t) volume := by
    apply Continuous.aestronglyMeasurable
    unfold thetaTailFirstMomentIntegrand
    exact (continuous_id.mul (hk.comp (by fun_prop))).mul (hk.comp (by fun_prop))
  refine Integrable.mono'
    ((integrable_abs_mul_exp_neg_mul_abs_weightedEulerStripFourierAnalytic (c := 1) one_pos).const_mul (C ^ (2 : ℕ)))
    hmeas ?_
  filter_upwards with u
  change |u * thetaCuspFullSource ((u + x - t) / 2) *
      thetaCuspFullSource ((u - x + t) / 2)| ≤ _
  rw [abs_mul, abs_mul]
  have h1 := abs_thetaCuspFullSource_le_exp_neg_abs ((u + x - t) / 2)
  have h2 := abs_thetaCuspFullSource_le_exp_neg_abs ((u - x + t) / 2)
  have habs : |u| ≤ |(u + x - t) / 2| + |(u - x + t) / 2| := by
    calc
      |u| = |(u + x - t) / 2 + (u - x + t) / 2| := by
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
  have hexp :
      Real.exp (-|(u + x - t) / 2|) * Real.exp (-|(u - x + t) / 2|)
        ≤ Real.exp (-|u|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    |u| * |thetaCuspFullSource ((u + x - t) / 2)| *
          |thetaCuspFullSource ((u - x + t) / 2)|
      ≤ |u| * (C * Real.exp (-|(u + x - t) / 2|)) *
          (C * Real.exp (-|(u - x + t) / 2|)) := by
        gcongr
    _ = C ^ (2 : ℕ) * (|u| *
          (Real.exp (-|(u + x - t) / 2|) *
            Real.exp (-|(u - x + t) / 2|))) := by ring
    _ ≤ C ^ (2 : ℕ) * (|u| * Real.exp (-|u|)) := by gcongr
    _ = C ^ (2 : ℕ) * (|u| * Real.exp (-(1 * |u|))) := by ring

/-- The actual theta tail first-moment kernel from the paper card. -/
def thetaTailFirstMomentKernel (x t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ u in Ioi (x + t), thetaTailFirstMomentIntegrand x t u

lemma thetaTailFirstMomentIntegrand_swap (x t u : ℝ) :
    thetaTailFirstMomentIntegrand t x u = thetaTailFirstMomentIntegrand x t u := by
  unfold thetaTailFirstMomentIntegrand
  ring

lemma thetaTailFirstMomentIntegrand_neg (x t u : ℝ) :
    thetaTailFirstMomentIntegrand x t (-u) =
      -thetaTailFirstMomentIntegrand x t u := by
  unfold thetaTailFirstMomentIntegrand
  rw [show (-u + x - t) / 2 = -((u - x + t) / 2) by ring,
    show (-u - x + t) / 2 = -((u + x - t) / 2) by ring,
    thetaCuspFullSource_neg, thetaCuspFullSource_neg]
  ring

/-- Symmetry of the actual theta tail first-moment kernel. -/
theorem thetaTailFirstMomentKernel_comm (x t : ℝ) :
    thetaTailFirstMomentKernel x t = thetaTailFirstMomentKernel t x := by
  unfold thetaTailFirstMomentKernel
  rw [add_comm]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  exact (thetaTailFirstMomentIntegrand_swap x t u).symm

lemma thetaTailFirstMomentIntegrand_neg_parameters (x t u : ℝ) :
    thetaTailFirstMomentIntegrand (-x) (-t) u =
      thetaTailFirstMomentIntegrand x t u := by
  unfold thetaTailFirstMomentIntegrand
  rw [show (u + -x - -t) / 2 = (u - x + t) / 2 by ring,
    show (u - -x + -t) / 2 = (u + x - t) / 2 by ring]
  ring

lemma integral_thetaTailFirstMomentIntegrand_eq_zero (x t : ℝ) :
    ∫ u : ℝ, thetaTailFirstMomentIntegrand x t u = 0 := by
  have hreflect := MeasureTheory.integral_neg_eq_self
    (thetaTailFirstMomentIntegrand x t) (volume : Measure ℝ)
  have hfun : (fun u : ℝ => thetaTailFirstMomentIntegrand x t (-u)) =
      fun u : ℝ => -thetaTailFirstMomentIntegrand x t u := by
    funext u
    exact thetaTailFirstMomentIntegrand_neg x t u
  rw [hfun, integral_neg] at hreflect
  linarith

lemma integral_Iic_add_Ioi_thetaTailFirstMomentIntegrand (x t r : ℝ) :
    (∫ u in Iic r, thetaTailFirstMomentIntegrand x t u) +
      ∫ u in Ioi r, thetaTailFirstMomentIntegrand x t u = 0 := by
  have hi := integrable_thetaTailFirstMomentIntegrand x t
  rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
    hi.integrableOn hi.integrableOn, Iic_union_Ioi, setIntegral_univ,
    integral_thetaTailFirstMomentIntegrand_eq_zero]

/-- Simultaneous reflection invariance of the actual theta tail first-moment kernel. -/
theorem thetaTailFirstMomentKernel_neg_neg (x t : ℝ) :
    thetaTailFirstMomentKernel (-x) (-t) = thetaTailFirstMomentKernel x t := by
  let F : ℝ → ℝ := thetaTailFirstMomentIntegrand x t
  have hodd (u : ℝ) : F (-u) = -F u := thetaTailFirstMomentIntegrand_neg x t u
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hreflect := hmp.setIntegral_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding F (Ioi (-(x + t)))
  have hpre : (fun u : ℝ => -u) ⁻¹' Ioi (-(x + t)) = Iio (x + t) := by
    ext u
    simp only [mem_preimage, mem_Ioi, mem_Iio]
    constructor <;> intro h <;> linarith
  rw [hpre] at hreflect
  simp only [hodd, integral_neg] at hreflect
  have hIio : (∫ u in Iio (x + t), F u) = ∫ u in Iic (x + t), F u := by
    rw [MeasureTheory.integral_Iic_eq_integral_Iio]
  have hsplit := integral_Iic_add_Ioi_thetaTailFirstMomentIntegrand x t (x + t)
  change (∫ u in Iic (x + t), F u) + ∫ u in Ioi (x + t), F u = 0 at hsplit
  unfold thetaTailFirstMomentKernel
  rw [show -x + -t = -(x + t) by ring]
  have hparam : (fun u => thetaTailFirstMomentIntegrand (-x) (-t) u) = F := by
    funext u
    exact thetaTailFirstMomentIntegrand_neg_parameters x t u
  rw [hparam]
  change (1 / 2 : ℝ) * (∫ u in Ioi (-(x + t)), F u) =
    (1 / 2 : ℝ) * ∫ u in Ioi (x + t), F u
  rw [← hreflect, hIio]
  linarith

/-- Pointwise nonnegativity of the actual theta tail first-moment kernel. -/
theorem thetaTailFirstMomentKernel_nonneg (x t : ℝ) :
    0 ≤ thetaTailFirstMomentKernel x t := by
  unfold thetaTailFirstMomentKernel
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  apply mul_nonneg hhalf
  by_cases hr : 0 ≤ x + t
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    unfold thetaTailFirstMomentIntegrand
    have hu0 : 0 ≤ u := le_trans hr hu.le
    exact mul_nonneg
      (mul_nonneg hu0 (HedenmalmThetaSource.thetaCuspFullSource_pos _).le)
      (HedenmalmThetaSource.thetaCuspFullSource_pos _).le
  · have hrneg : x + t < 0 := lt_of_not_ge hr
    have hleft : (∫ u in Iic (x + t), thetaTailFirstMomentIntegrand x t u) ≤ 0 := by
      apply integral_nonpos_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
      unfold thetaTailFirstMomentIntegrand
      have hu0 : u ≤ 0 := le_trans hu hrneg.le
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hu0
          (HedenmalmThetaSource.thetaCuspFullSource_pos _).le)
        (HedenmalmThetaSource.thetaCuspFullSource_pos _).le
    have hsplit := integral_Iic_add_Ioi_thetaTailFirstMomentIntegrand x t (x + t)
    linarith

/-- Shift-tail formula for the actual theta first-moment kernel. -/
theorem thetaTailFirstMomentKernel_eq_shiftTail (x t : ℝ) :
    thetaTailFirstMomentKernel x t =
      ∫ s in Ioi (0 : ℝ),
        (x + t + 2 * s) * thetaCuspFullSource (x + s) *
          thetaCuspFullSource (t + s) := by
  let F : ℝ → ℝ := thetaTailFirstMomentIntegrand x t
  have hF : Continuous F := by
    dsimp [F, thetaTailFirstMomentIntegrand]
    exact (continuous_id.mul
      (contDiff_thetaCuspFullSource.continuous.comp (by fun_prop))).mul
      (contDiff_thetaCuspFullSource.continuous.comp (by fun_prop))
  have htrans := setIntegral_Ioi_zero_comp_add_right F (x + t)
  have hscale := Sieve.setIntegral_comp_mul_left
    (S := Ioi (0 : ℝ)) (c := 2)
    (fun y : ℝ => F (y + (x + t)))
    (hF.comp (by fun_prop)) measurableSet_Ioi (by norm_num)
  have hpre : (fun v : ℝ => 2 * v) ⁻¹' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext v
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [hpre] at hscale
  have horiginal :
      (∫ u in Ioi (x + t), F u) =
        2 * ∫ s in Ioi (0 : ℝ), F (2 * s + (x + t)) := by
    rw [← htrans]
    linarith [hscale]
  unfold thetaTailFirstMomentKernel
  change (1 / 2 : ℝ) * ∫ u in Ioi (x + t), F u = _
  rw [horiginal]
  ring_nf
  apply integral_congr_ae
  filter_upwards with s
  dsimp [F, thetaTailFirstMomentIntegrand]
  rw [show (s * 2 + x + t + x - t) / 2 = x + s by ring,
    show (s * 2 + x + t - x + t) / 2 = t + s by ring]
  ring

/-- Positive Krein channel at source shift `s`. -/
def thetaTailKreinPlus (c x s : ℝ) : ℝ :=
  (x + s + c) * thetaCuspFullSource (x + s)

/-- Negative Krein channel at source shift `s`. -/
def thetaTailKreinMinus (c x s : ℝ) : ℝ :=
  (x + s - c) * thetaCuspFullSource (x + s)

/-- Exact two-channel Krein factorization of the actual theta tail kernel. -/
theorem thetaTailFirstMomentKernel_eq_kreinDifference
    {c : ℝ} (hc : 0 < c) (x t : ℝ) :
    thetaTailFirstMomentKernel x t =
      (1 / (2 * c)) * ∫ s in Ioi (0 : ℝ),
        (thetaTailKreinPlus c x s * thetaTailKreinPlus c t s -
          thetaTailKreinMinus c x s * thetaTailKreinMinus c t s) := by
  rw [thetaTailFirstMomentKernel_eq_shiftTail]
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  unfold thetaTailKreinPlus thetaTailKreinMinus
  field_simp [hcne]
  ring

end RHTower
