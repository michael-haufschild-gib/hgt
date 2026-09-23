import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.ThetaCuspKernelLogConcavity
import GaloisForLFunctions.RHTower.ThetaCuspFullDerivativeExponentialMoments
import GaloisForLFunctions.HTGeometry.MonotoneLikelihoodRatio
import GaloisForLFunctions.HTGeometry.PositiveJumpFormationChirality

/-!
# Negative orientation of the first unresolved prime/Gamma wall incidence

The cold prime/Gamma wall and its canonical Gamma-six correction agree with the completed Xi seam
through quadratic order. Their cubic logarithmic mismatch is

`normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ (3 : ℕ) / 4`.

This module determines its orientation without fitting a clock or selecting Xi zeros. Strict
log-concavity of the completed theta source makes its score strictly increasing. Integration by
parts and the exact two-copy monotone-likelihood identity then prove strict log-concavity of the
factorially normalized half-line moments. The required sixth-moment inequality and negative cubic
Malgrange incidence follow.
-/

open Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

private def thetaCuspScore : ℝ → ℝ :=
  -(iteratedDeriv 1 thetaCuspFullSource / thetaCuspFullSource)

private theorem hasDerivAt_thetaCuspScore (x : ℝ) :
    HasDerivAt thetaCuspScore
      (-(thetaCuspLogConcavityNumerator x / thetaCuspFullSource x ^ (2 : ℕ))) x := by
  have h₁ := hasDerivAt_thetaCuspFullDerivative 1 x
  rw [← iteratedDeriv_thetaCuspFullSource 1,
    ← iteratedDeriv_thetaCuspFullSource 2] at h₁
  have hquot := h₁.div (hasDerivAt_thetaCuspFullSource_iterate_zero x)
    (thetaCuspFullSource_pos_all x).ne'
  unfold thetaCuspScore
  simpa only [Pi.neg_apply, Pi.div_apply, thetaCuspLogConcavityNumerator,
    pow_two] using hquot.neg

private theorem strictMono_thetaCuspScore : StrictMono thetaCuspScore := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_thetaCuspScore x).deriv]
  exact neg_pos.mpr (div_neg_of_neg_of_pos
    (thetaCuspLogConcavityNumerator_neg_all x)
    (sq_pos_of_pos (thetaCuspFullSource_pos_all x)))

private theorem integrableOn_pow_mul_thetaCuspFullSource_deriv (k : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ k * iteratedDeriv 1 thetaCuspFullSource x) (Ioi 0) := by
  have hbase :=
    (integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource 1 1).const_mul
      (Nat.factorial k : ℝ)
  have hdom := hbase.mono_measure (Measure.restrict_le_self :
    volume.restrict (Ioi (0 : ℝ)) ≤ volume)
  apply hdom.mono
  · exact ((continuous_id.pow k).mul
      (contDiff_thetaCuspFullSource.continuous_iteratedDeriv 1
        (by exact_mod_cast (ENat.coe_lt_top 1).le))).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hpow := Real.pow_div_factorial_le_exp x hx.le k
    have hfac : (0 : ℝ) < Nat.factorial k := by positivity
    rw [div_le_iff₀ hfac] at hpow
    calc
      ‖x ^ k * iteratedDeriv 1 thetaCuspFullSource x‖ =
          x ^ k * |iteratedDeriv 1 thetaCuspFullSource x| := by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hx]
      _ ≤
          ((Nat.factorial k : ℝ) * Real.exp x) *
            |iteratedDeriv 1 thetaCuspFullSource x| := by
        exact mul_le_mul_of_nonneg_right (by simpa [mul_comm] using hpow) (abs_nonneg _)
      _ = (Nat.factorial k : ℝ) *
          (Real.exp (1 * |x|) * |iteratedDeriv 1 thetaCuspFullSource x|) := by
        rw [show |x| = x by exact abs_of_pos hx]
        ring
      _ = ‖(Nat.factorial k : ℝ) *
          (Real.exp (1 * |x|) * |iteratedDeriv 1 thetaCuspFullSource x|)‖ := by
        have hnonneg : 0 ≤ (Nat.factorial k : ℝ) *
            (Real.exp (1 * |x|) * |iteratedDeriv 1 thetaCuspFullSource x|) :=
          mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]

private theorem pow_mul_thetaCuspFullSource_tendsto_atTop_zero (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * thetaCuspFullSource x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖x ^ k * thetaCuspFullSource x‖ ≤
        thetaCuspDerivativeExpConstant 0 * (x ^ k * Real.exp (-x)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hsource := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg 0 hx
    simp only [iteratedDeriv_zero] at hsource
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx]
    calc
      x ^ k * |thetaCuspFullSource x| ≤
          x ^ k * (thetaCuspDerivativeExpConstant 0 * Real.exp (-x)) := by gcongr
      _ = thetaCuspDerivativeExpConstant 0 * (x ^ k * Real.exp (-x)) := by ring
  have hmajor : Tendsto
      (fun x : ℝ => thetaCuspDerivativeExpConstant 0 *
        (x ^ k * Real.exp (-x))) atTop (𝓝 0) := by
    simpa using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul
        (thetaCuspDerivativeExpConstant 0)
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle hmajor

private theorem pow_mul_thetaCuspFullSource_tendsto_zero_of_pos
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun x : ℝ => x ^ k * thetaCuspFullSource x)
      (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun x : ℝ => x ^ k * thetaCuspFullSource x) :=
    (continuous_id.pow k).mul contDiff_thetaCuspFullSource.continuous
  have h := (hc.tendsto 0).mono_left
    (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa [Nat.ne_of_gt hk] using! h

private theorem integral_pow_mul_thetaCuspScore (k : ℕ) (hk : 0 < k) :
    (∫ x : ℝ in Ioi 0,
      x ^ k * thetaCuspScore x * thetaCuspFullSource x) =
      (k : ℝ) * ∫ x : ℝ in Ioi 0,
        x ^ (k - 1) * thetaCuspFullSource x := by
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => x ^ k)
    (u' := fun x : ℝ => (k : ℝ) * x ^ (k - 1))
    (v := thetaCuspFullSource)
    (v' := iteratedDeriv 1 thetaCuspFullSource)
    (fun x _ => by simpa [mul_comm] using hasDerivAt_pow k x)
    (fun x _ => hasDerivAt_thetaCuspFullSource_iterate_zero x)
    (integrableOn_pow_mul_thetaCuspFullSource_deriv k)
    (by
      simpa only [Pi.mul_apply, ← mul_assoc] using!
        (integrableOn_thetaCuspRawMoment (k - 1)).const_mul (k : ℝ))
    (pow_mul_thetaCuspFullSource_tendsto_zero_of_pos hk)
    (pow_mul_thetaCuspFullSource_tendsto_atTop_zero k)
  calc
    (∫ x : ℝ in Ioi 0,
        x ^ k * thetaCuspScore x * thetaCuspFullSource x) =
        ∫ x : ℝ in Ioi 0,
          -(x ^ k * iteratedDeriv 1 thetaCuspFullSource x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hne := (thetaCuspFullSource_pos_of_pos hx).ne'
      simp only [thetaCuspScore, Pi.neg_apply, Pi.div_apply]
      field_simp [hne]
    _ = -(∫ x : ℝ in Ioi 0,
        x ^ k * iteratedDeriv 1 thetaCuspFullSource x) := by rw [integral_neg]
    _ = (k : ℝ) * ∫ x : ℝ in Ioi 0,
        x ^ (k - 1) * thetaCuspFullSource x := by
      rw [hibp]
      rw [show (fun x : ℝ => ((k : ℝ) * x ^ (k - 1)) *
          thetaCuspFullSource x) =
          fun x => (k : ℝ) * (x ^ (k - 1) * thetaCuspFullSource x) by
            funext x; ring,
        integral_const_mul]
      ring

private theorem integrableOn_pow_mul_thetaCuspScore (k : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ k * thetaCuspScore x * thetaCuspFullSource x) (Ioi 0) := by
  apply (integrableOn_pow_mul_thetaCuspFullSource_deriv k).neg.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hne := (thetaCuspFullSource_pos_of_pos hx).ne'
  simp only [thetaCuspScore, Pi.neg_apply, Pi.div_apply]
  field_simp [hne]

private def thetaCuspHalfMoment (k : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ k * thetaCuspFullSource x

private theorem thetaCuspPositiveRayMeasure_ne_zero :
    volume.restrict (Ioi (0 : ℝ)) ≠ 0 := by
  intro hzero
  have h := congrArg (fun μ : Measure ℝ => μ (Ioo (0 : ℝ) 1)) hzero
  rw [Measure.restrict_apply measurableSet_Ioo] at h
  have hinter : Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo 0 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
    tauto
  rw [hinter, Real.volume_Ioo] at h
  norm_num at h

private theorem thetaCuspHalfMoment_pos (k : ℕ) :
    0 < thetaCuspHalfMoment k := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  apply GaloisForLFunctions.HTGeometry.integral_pos_of_ae_pos
    (by simpa only [μ] using thetaCuspPositiveRayMeasure_ne_zero)
  · simpa only [thetaCuspHalfMoment, μ, IntegrableOn] using
      integrableOn_thetaCuspRawMoment k
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_pos (pow_pos hx k) (thetaCuspFullSource_pos_of_pos hx)

private def thetaCuspPositiveDiagonal : Set (ℝ × ℝ) :=
  {z | z.1 = z.2}

private theorem measurableSet_thetaCuspPositiveDiagonal :
    MeasurableSet thetaCuspPositiveDiagonal := by
  simpa only [thetaCuspPositiveDiagonal, diagonal, mem_setOf_eq] using
    (measurableSet_diagonal : MeasurableSet (diagonal ℝ))

private theorem measure_thetaCuspPositiveDiagonal_zero :
    ((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))) thetaCuspPositiveDiagonal = 0 := by
  rw [Measure.measure_prod_null measurableSet_thetaCuspPositiveDiagonal]
  filter_upwards with x
  have hsection :
      Prod.mk x ⁻¹' thetaCuspPositiveDiagonal = ({x} : Set ℝ) := by
    ext y
    simp only [mem_singleton_iff, thetaCuspPositiveDiagonal, mem_preimage,
      mem_setOf_eq]
    exact eq_comm
  rw [hsection]
  apply bot_unique
  calc
    (volume.restrict (Ioi (0 : ℝ))) ({x} : Set ℝ) ≤
        volume ({x} : Set ℝ) := Measure.restrict_le_self _
    _ = 0 := measure_singleton x

private theorem ae_fst_pos_thetaCuspPositiveProd :
    ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))), 0 < z.1 := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hnull : μ (Iic (0 : ℝ)) = 0 := by
    dsimp only [μ]
    rw [Measure.restrict_apply measurableSet_Iic]
    rw [Iic_inter_Ioi, Real.volume_Ioc]
    norm_num
  have hrect : (μ.prod μ) ((Iic (0 : ℝ)) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod, hnull, zero_mul]
  refine ae_iff.mpr (measure_mono_null ?_ hrect)
  intro z hz
  exact mem_prod.mpr ⟨not_lt.mp hz, mem_univ _⟩

private theorem ae_snd_pos_thetaCuspPositiveProd :
    ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))), 0 < z.2 := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hnull : μ (Iic (0 : ℝ)) = 0 := by
    dsimp only [μ]
    rw [Measure.restrict_apply measurableSet_Iic]
    rw [Iic_inter_Ioi, Real.volume_Ioc]
    norm_num
  have hrect : (μ.prod μ) ((univ : Set ℝ) ×ˢ (Iic (0 : ℝ))) = 0 := by
    rw [Measure.prod_prod, hnull, mul_zero]
  refine ae_iff.mpr (measure_mono_null ?_ hrect)
  intro z hz
  exact mem_prod.mpr ⟨mem_univ _, not_lt.mp hz⟩

private theorem ae_ne_thetaCuspPositiveProd :
    ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))), z.1 ≠ z.2 := by
  rw [ae_iff]
  simpa only [thetaCuspPositiveDiagonal, not_ne_iff] using
    measure_thetaCuspPositiveDiagonal_zero

private theorem thetaCuspPositiveProdMeasure_ne_zero :
    (volume.restrict (Ioi (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ))) ≠ 0 := by
  intro hzero
  let s : Set ℝ := Ioo 0 1
  have hs : (volume.restrict (Ioi (0 : ℝ))) s = 1 := by
    dsimp only [s]
    rw [Measure.restrict_apply measurableSet_Ioo]
    have hinter : Ioo (0 : ℝ) 1 ∩ Ioi 0 = Ioo 0 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ioo, mem_Ioi]
      tauto
    rw [hinter, Real.volume_Ioo]
    norm_num
  have h := congrArg (fun μ : Measure (ℝ × ℝ) => μ (s ×ˢ s)) hzero
  rw [Measure.prod_prod, hs] at h
  norm_num at h

private theorem thetaCuspHalfMoment_factorial_strictLogConcave
    (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * thetaCuspHalfMoment (n - 1) * thetaCuspHalfMoment (n + 1) <
      ((n + 1 : ℕ) : ℝ) * thetaCuspHalfMoment n ^ (2 : ℕ) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ → ℝ := fun x => x ^ (n + 1) * thetaCuspFullSource x
  let H : ℝ → ℝ := fun x => x ^ n * thetaCuspFullSource x
  let g : ℝ → ℝ := thetaCuspScore
  let K : ℝ × ℝ → ℝ := fun z =>
    (g z.2 - g z.1) * (H z.1 * F z.2 - H z.2 * F z.1)
  have hF : Integrable F μ := by
    simpa only [F, μ, IntegrableOn] using integrableOn_thetaCuspRawMoment (n + 1)
  have hH : Integrable H μ := by
    simpa only [H, μ, IntegrableOn] using integrableOn_thetaCuspRawMoment n
  have hgF : Integrable (fun x => g x * F x) μ := by
    have h := integrableOn_pow_mul_thetaCuspScore (n + 1)
    apply h.congr
    filter_upwards with x
    simp only [g, F]
    ring
  have hgH : Integrable (fun x => g x * H x) μ := by
    have h := integrableOn_pow_mul_thetaCuspScore n
    apply h.congr
    filter_upwards with x
    simp only [g, H]
    ring
  let T₁ : ℝ × ℝ → ℝ := fun z => H z.1 * (g z.2 * F z.2)
  let T₂ : ℝ × ℝ → ℝ := fun z => F z.1 * (g z.2 * H z.2)
  let T₃ : ℝ × ℝ → ℝ := fun z => (g z.1 * H z.1) * F z.2
  let T₄ : ℝ × ℝ → ℝ := fun z => (g z.1 * F z.1) * H z.2
  have hT₁ : Integrable T₁ (μ.prod μ) := by simpa only [T₁] using hH.mul_prod hgF
  have hT₂ : Integrable T₂ (μ.prod μ) := by simpa only [T₂] using hF.mul_prod hgH
  have hT₃ : Integrable T₃ (μ.prod μ) := by simpa only [T₃] using hgH.mul_prod hF
  have hT₄ : Integrable T₄ (μ.prod μ) := by simpa only [T₄] using hgF.mul_prod hH
  have hKexpand : K = T₁ - T₂ - T₃ + T₄ := by
    funext z
    simp only [K, T₁, T₂, T₃, T₄, Pi.add_apply, Pi.sub_apply]
    ring
  have hKint : Integrable K (μ.prod μ) := by
    rw [hKexpand]
    exact ((hT₁.sub hT₂).sub hT₃).add hT₄
  have hKposAe : ∀ᵐ z : ℝ × ℝ ∂μ.prod μ, 0 < K z := by
    filter_upwards [ae_fst_pos_thetaCuspPositiveProd,
      ae_snd_pos_thetaCuspPositiveProd, ae_ne_thetaCuspPositiveProd]
      with z hx hy hne
    have hweight : 0 < z.1 ^ n * z.2 ^ n *
        thetaCuspFullSource z.1 * thetaCuspFullSource z.2 := by
      exact mul_pos
        (mul_pos (mul_pos (pow_pos hx n) (pow_pos hy n))
          (thetaCuspFullSource_pos_of_pos hx))
        (thetaCuspFullSource_pos_of_pos hy)
    have hfactor : K z =
        ((g z.2 - g z.1) * (z.2 - z.1)) *
          (z.1 ^ n * z.2 ^ n * thetaCuspFullSource z.1 *
            thetaCuspFullSource z.2) := by
      dsimp only [K, F, H]
      rw [pow_succ, pow_succ]
      ring
    rw [hfactor]
    by_cases hxy : z.1 < z.2
    · exact mul_pos
        (mul_pos (sub_pos.mpr (strictMono_thetaCuspScore hxy)) (sub_pos.mpr hxy))
        hweight
    · have hyx : z.2 < z.1 := lt_of_le_of_ne (not_lt.mp hxy) (Ne.symm hne)
      exact mul_pos
        (mul_pos_of_neg_of_neg
          (sub_neg.mpr (strictMono_thetaCuspScore hyx)) (sub_neg.mpr hyx))
        hweight
  have hKpos : 0 < ∫ z, K z ∂μ.prod μ :=
    GaloisForLFunctions.HTGeometry.integral_pos_of_ae_pos
      (by simpa only [μ] using thetaCuspPositiveProdMeasure_ne_zero) hKint hKposAe
  have hgap := HTGeometry.integral_monotoneLikelihoodKernel_eq_two_mul_gap
    hF hH hgF hgH
  have hscoreF := integral_pow_mul_thetaCuspScore (n + 1) (by omega)
  have hscoreH := integral_pow_mul_thetaCuspScore n hn
  change (∫ z, (g z.2 - g z.1) *
    (H z.1 * F z.2 - H z.2 * F z.1) ∂μ.prod μ) = _ at hgap
  change (∫ z, K z ∂μ.prod μ) = _ at hgap
  rw [hgap] at hKpos
  have hgf : (∫ x, g x * F x ∂μ) =
      ((n + 1 : ℕ) : ℝ) * thetaCuspHalfMoment n := by
    rw [show (fun x => g x * F x) =
        fun x => x ^ (n + 1) * thetaCuspScore x * thetaCuspFullSource x by
      funext x; simp only [g, F]; ring]
    simpa only [μ, thetaCuspHalfMoment, show n + 1 - 1 = n by omega] using hscoreF
  have hgh : (∫ x, g x * H x ∂μ) =
      (n : ℝ) * thetaCuspHalfMoment (n - 1) := by
    rw [show (fun x => g x * H x) =
        fun x => x ^ n * thetaCuspScore x * thetaCuspFullSource x by
      funext x; simp only [g, H]; ring]
    simpa only [μ, thetaCuspHalfMoment] using hscoreH
  have hFmass : (∫ x, F x ∂μ) = thetaCuspHalfMoment (n + 1) := by rfl
  have hHmass : (∫ x, H x ∂μ) = thetaCuspHalfMoment n := by rfl
  rw [hgf, hgh, hFmass, hHmass] at hKpos
  nlinarith

private def thetaCuspFactorialMomentRatio (k : ℕ) : ℝ :=
  thetaCuspHalfMoment k / ((k : ℝ) * thetaCuspHalfMoment (k - 1))

private theorem thetaCuspFactorialMomentRatio_pos {k : ℕ} (hk : 0 < k) :
    0 < thetaCuspFactorialMomentRatio k := by
  exact div_pos (thetaCuspHalfMoment_pos k)
    (mul_pos (Nat.cast_pos.mpr hk) (thetaCuspHalfMoment_pos (k - 1)))

private theorem thetaCuspFactorialMomentRatio_succ_lt
    (n : ℕ) (hn : 0 < n) :
    thetaCuspFactorialMomentRatio (n + 1) < thetaCuspFactorialMomentRatio n := by
  have hlog := thetaCuspHalfMoment_factorial_strictLogConcave n hn
  have hleft : 0 < (((n + 1 : ℕ) : ℝ) * thetaCuspHalfMoment n) :=
    mul_pos (by positivity) (thetaCuspHalfMoment_pos n)
  have hright : 0 < (n : ℝ) * thetaCuspHalfMoment (n - 1) :=
    mul_pos (Nat.cast_pos.mpr hn) (thetaCuspHalfMoment_pos (n - 1))
  rw [thetaCuspFactorialMomentRatio]
  change thetaCuspHalfMoment (n + 1) /
      (((n + 1 : ℕ) : ℝ) * thetaCuspHalfMoment (n + 1 - 1)) <
    thetaCuspHalfMoment n / ((n : ℝ) * thetaCuspHalfMoment (n - 1))
  rw [show n + 1 - 1 = n by omega]
  rw [div_lt_div_iff₀ hleft hright]
  nlinarith

/-- Strict factorial-normalized contraction at the fourth theta moment. -/
theorem thetaCuspRawEvenMoment_two_mul_zero_lt_six_mul_one_sq :
    thetaCuspRawEvenMoment 2 * thetaCuspRawEvenMoment 0 <
      6 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) := by
  have h43 := thetaCuspFactorialMomentRatio_succ_lt 3 (by omega)
  have h32 := thetaCuspFactorialMomentRatio_succ_lt 2 (by omega)
  have h21 := thetaCuspFactorialMomentRatio_succ_lt 1 (by omega)
  have h42 : thetaCuspFactorialMomentRatio 4 < thetaCuspFactorialMomentRatio 2 :=
    h43.trans h32
  have h31 : thetaCuspFactorialMomentRatio 3 < thetaCuspFactorialMomentRatio 1 :=
    h32.trans h21
  have hprod :
      thetaCuspFactorialMomentRatio 4 * thetaCuspFactorialMomentRatio 3 <
        thetaCuspFactorialMomentRatio 2 * thetaCuspFactorialMomentRatio 1 :=
    mul_lt_mul h42 h31.le
      (thetaCuspFactorialMomentRatio_pos (k := 3) (by omega))
      (thetaCuspFactorialMomentRatio_pos (k := 2) (by omega)).le
  have hM0 := thetaCuspHalfMoment_pos 0
  have hM1 := thetaCuspHalfMoment_pos 1
  have hM2 := thetaCuspHalfMoment_pos 2
  have hM3 := thetaCuspHalfMoment_pos 3
  norm_num [thetaCuspFactorialMomentRatio] at hprod
  field_simp [hM0.ne', hM1.ne', hM2.ne', hM3.ne'] at hprod
  simp only [thetaCuspRawEvenMoment]
  dsimp only [thetaCuspHalfMoment] at hprod
  nlinarith

theorem thetaCuspRawEvenMoment_three_mul_zero_lt_fifteen_mul_one_mul_two :
    thetaCuspRawEvenMoment 3 * thetaCuspRawEvenMoment 0 <
      15 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 2 := by
  have h65 := thetaCuspFactorialMomentRatio_succ_lt 5 (by omega)
  have h54 := thetaCuspFactorialMomentRatio_succ_lt 4 (by omega)
  have h43 := thetaCuspFactorialMomentRatio_succ_lt 3 (by omega)
  have h32 := thetaCuspFactorialMomentRatio_succ_lt 2 (by omega)
  have h21 := thetaCuspFactorialMomentRatio_succ_lt 1 (by omega)
  have h62 : thetaCuspFactorialMomentRatio 6 < thetaCuspFactorialMomentRatio 2 :=
    h65.trans (h54.trans (h43.trans h32))
  have h51 : thetaCuspFactorialMomentRatio 5 < thetaCuspFactorialMomentRatio 1 :=
    h54.trans (h43.trans (h32.trans h21))
  have hprod :
      thetaCuspFactorialMomentRatio 6 * thetaCuspFactorialMomentRatio 5 <
        thetaCuspFactorialMomentRatio 2 * thetaCuspFactorialMomentRatio 1 :=
    mul_lt_mul h62 h51.le
      (thetaCuspFactorialMomentRatio_pos (k := 5) (by omega))
      (thetaCuspFactorialMomentRatio_pos (k := 2) (by omega)).le
  have hM0 := thetaCuspHalfMoment_pos 0
  have hM1 := thetaCuspHalfMoment_pos 1
  have hM2 := thetaCuspHalfMoment_pos 2
  have hM4 := thetaCuspHalfMoment_pos 4
  have hM5 := thetaCuspHalfMoment_pos 5
  norm_num [thetaCuspFactorialMomentRatio] at hprod
  field_simp [hM0.ne', hM1.ne', hM2.ne', hM4.ne', hM5.ne'] at hprod
  simp only [thetaCuspRawEvenMoment]
  dsimp only [thetaCuspHalfMoment] at hprod
  nlinarith

/-- Strict factorial-normalized contraction needed by the tenth theta moment. -/
theorem thetaCuspRawEvenMoment_five_mul_zero_lt_fortyFive_mul_one_mul_four :
    thetaCuspRawEvenMoment 5 * thetaCuspRawEvenMoment 0 <
      45 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 4 := by
  have h109 := thetaCuspFactorialMomentRatio_succ_lt 9 (by omega)
  have h98 := thetaCuspFactorialMomentRatio_succ_lt 8 (by omega)
  have h87 := thetaCuspFactorialMomentRatio_succ_lt 7 (by omega)
  have h76 := thetaCuspFactorialMomentRatio_succ_lt 6 (by omega)
  have h65 := thetaCuspFactorialMomentRatio_succ_lt 5 (by omega)
  have h54 := thetaCuspFactorialMomentRatio_succ_lt 4 (by omega)
  have h43 := thetaCuspFactorialMomentRatio_succ_lt 3 (by omega)
  have h32 := thetaCuspFactorialMomentRatio_succ_lt 2 (by omega)
  have h21 := thetaCuspFactorialMomentRatio_succ_lt 1 (by omega)
  have h102 : thetaCuspFactorialMomentRatio 10 < thetaCuspFactorialMomentRatio 2 :=
    h109.trans (h98.trans (h87.trans (h76.trans
      (h65.trans (h54.trans (h43.trans h32))))))
  have h91 : thetaCuspFactorialMomentRatio 9 < thetaCuspFactorialMomentRatio 1 :=
    h98.trans (h87.trans (h76.trans (h65.trans
      (h54.trans (h43.trans (h32.trans h21))))))
  have hprod :
      thetaCuspFactorialMomentRatio 10 * thetaCuspFactorialMomentRatio 9 <
        thetaCuspFactorialMomentRatio 2 * thetaCuspFactorialMomentRatio 1 :=
    mul_lt_mul h102 h91.le
      (thetaCuspFactorialMomentRatio_pos (k := 9) (by omega))
      (thetaCuspFactorialMomentRatio_pos (k := 2) (by omega)).le
  have hM0 := thetaCuspHalfMoment_pos 0
  have hM1 := thetaCuspHalfMoment_pos 1
  have hM2 := thetaCuspHalfMoment_pos 2
  have hM8 := thetaCuspHalfMoment_pos 8
  have hM9 := thetaCuspHalfMoment_pos 9
  norm_num [thetaCuspFactorialMomentRatio] at hprod
  field_simp [hM0.ne', hM1.ne', hM2.ne', hM8.ne', hM9.ne'] at hprod
  simp only [thetaCuspRawEvenMoment]
  dsimp only [thetaCuspHalfMoment] at hprod
  nlinarith

theorem normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg :
    normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ (3 : ℕ) / 4 < 0 := by
  have hraw := thetaCuspRawEvenMoment_three_mul_zero_lt_fifteen_mul_one_mul_two
  have hzero := thetaCuspRawEvenMoment_zero_pos
  rw [normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment,
    normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  simp only [thetaCuspNormalizedEvenMoment]
  field_simp [hzero.ne']
  nlinarith

end

end RHTower
