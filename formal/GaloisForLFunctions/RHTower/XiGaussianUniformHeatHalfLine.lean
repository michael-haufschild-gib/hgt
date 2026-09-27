import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorPrimeCancellation
import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorPhaseControl

/-!
# One null-direction cutoff for all orders and all later heat times

Positive sampled energy decreases with heat time because every actual
squared spectral coordinate has positive real part. A single annihilator
cutoff therefore controls the complete trace, energy, phase channel, and
arithmetic source uniformly on an entire positive heat half-line. Tests are
normalized once, in the sampled energy at its fixed left endpoint.
-/

open Complex Filter Topology
open scoped Real
noncomputable section

namespace RHTower

/-- Native positive energy decreases with heat time, without RH. -/
theorem xiGaussianNativeEnergy_antitone (P : Polynomial ℝ) :
    Antitone (xiGaussianNativeEnergy P) := by
  intro s t hst
  apply Summable.tsum_le_tsum _
    (summable_norm_xiPolynomialGaussianHeatTerm t.property P)
    (summable_norm_xiPolynomialGaussianHeatTerm s.property P)
  intro q
  rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact Real.exp_le_exp.mpr (neg_le_neg
    (mul_le_mul_of_nonneg_right hst (xiSpectralSq_re_pos q).le))

/-- Every time on this closed half-line is positive. -/
def xiGaussianHeatAfter (t₀ : {t : ℝ // 0 < t}) (s : Set.Ici (t₀ : ℝ)) :
    {t : ℝ // 0 < t} := ⟨s, lt_of_lt_of_le t₀.property s.property⟩

/-- The same cutoff handles arbitrary degree and every time above a fixed
positive anchor. The imaginary channel is half the full phase debt. -/
theorem eventually_forall_xiGaussianAnnihilator_heatHalfLine_control
    (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop,
      ∀ s : Set.Ici (t₀ : ℝ),
      ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t₀ ≤ 1},
        let t := xiGaussianHeatAfter t₀ s
        |xiPolynomialGaussianHeatTraceReal (P.1 + xiGaussianAnnihilator F) t -
          xiPolynomialGaussianHeatTraceReal P.1 t| < (ε : ℝ) ∧
        |xiGaussianNativeEnergy (P.1 + xiGaussianAnnihilator F) t -
          xiGaussianNativeEnergy P.1 t| < (ε : ℝ) ∧
        |(∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
            (P.1 + xiGaussianAnnihilator F) t q) -
          (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P.1 t q)| < (ε : ℝ) ∧
        |xiGaussianCompletedSourceResidual (P.1 + xiGaussianAnnihilator F) t -
          xiGaussianCompletedSourceResidual P.1 t| < π * (ε : ℝ) := by
  let η : {η : ℝ // 0 < η} := ⟨(ε : ℝ) / 2, div_pos ε.property (by positivity)⟩
  have hlim : Tendsto (fun F : Finset XiZeroCopy =>
      (η : ℝ) + (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy (xiGaussianAnnihilator F) t₀)
      atTop (𝓝 (η : ℝ)) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add
      ((tendsto_xiGaussianNativeEnergy_annihilator_zero t₀).const_mul (1 + 1 / (η : ℝ)))
  have hsmall : (η : ℝ) < (ε : ℝ) := by dsimp only [η]; linarith [ε.property]
  filter_upwards [hlim.eventually (Iio_mem_nhds hsmall)] with F hF s P
  dsimp only
  let t := xiGaussianHeatAfter t₀ s
  have hP : xiGaussianNativeEnergy P.1 t ≤ 1 :=
    (xiGaussianNativeEnergy_antitone P.1 s.property).trans P.property
  have hQ : xiGaussianNativeEnergy (xiGaussianAnnihilator F) t ≤
      xiGaussianNativeEnergy (xiGaussianAnnihilator F) t₀ :=
    xiGaussianNativeEnergy_antitone (xiGaussianAnnihilator F) s.property
  have hC : 0 ≤ 1 + 1 / (η : ℝ) := by have hη := η.property; positivity
  have hb : (η : ℝ) * xiGaussianNativeEnergy P.1 t +
      (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy (xiGaussianAnnihilator F) t < (ε : ℝ) := by
    have hunit : (η : ℝ) * xiGaussianNativeEnergy P.1 t ≤ (η : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hP η.property.le
    exact (add_le_add hunit (mul_le_mul_of_nonneg_left hQ hC)).trans_lt hF
  refine ⟨(abs_xiGaussianHeatTraceReal_add_sub_le P.1 (xiGaussianAnnihilator F) t η).trans_lt hb,
    (abs_xiGaussianNativeEnergy_add_sub_le P.1 (xiGaussianAnnihilator F) t η).trans_lt hb,
    (abs_xiGaussianImaginaryChannel_add_sub_le P.1 (xiGaussianAnnihilator F) t η).trans_lt hb, ?_⟩
  exact (abs_xiGaussianCompletedSourceResidual_add_sub_le P.1 (xiGaussianAnnihilator F) t η).trans_lt
    (mul_lt_mul_of_pos_left hb Real.pi_pos)

/-- Uniform cancellation of the actual complete source on the whole heat
half-line, with the same finite-divisor cutoff for every time. -/
theorem eventually_forall_xiGaussianAnnihilator_source_heatHalfLine_small
    (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ s : Set.Ici (t₀ : ℝ),
      |xiGaussianCompletedSourceResidual (xiGaussianAnnihilator F)
        (xiGaussianHeatAfter t₀ s)| < (ε : ℝ) := by
  have hlim := (tendsto_xiGaussianNativeEnergy_annihilator_zero t₀).const_mul π
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (Iio_mem_nhds ε.property)] with F hF s
  exact ((abs_xiGaussianCompletedSourceResidual_le_energy (xiGaussianAnnihilator F)
    (xiGaussianHeatAfter t₀ s)).trans (mul_le_mul_of_nonneg_left
      (xiGaussianNativeEnergy_antitone (xiGaussianAnnihilator F) s.property)
      Real.pi_pos.le)).trans_lt hF

/-- Complete mixed arithmetic cancellation is uniform over both unrestricted
polynomial order and the entire positive heat half-line. -/
theorem eventually_forall_xiGaussianAnnihilator_mixed_source_heatHalfLine_small
    (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ s : Set.Ici (t₀ : ℝ),
      ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t₀ ≤ 1},
        let t := xiGaussianHeatAfter t₀ s
        |xiGaussianCompletedSourceResidual (P.1 + xiGaussianAnnihilator F) t -
          xiGaussianCompletedSourceResidual P.1 t -
          xiGaussianCompletedSourceResidual (xiGaussianAnnihilator F) t| < (ε : ℝ) := by
  let e : {e : ℝ // 0 < e} := ⟨(ε : ℝ) / (2 * π), div_pos ε.property (by positivity)⟩
  let e' : {e : ℝ // 0 < e} := ⟨(ε : ℝ) / 2, div_pos ε.property (by positivity)⟩
  filter_upwards [eventually_forall_xiGaussianAnnihilator_heatHalfLine_control t₀ e,
    eventually_forall_xiGaussianAnnihilator_source_heatHalfLine_small t₀ e'] with F hF hD s P
  dsimp only
  have h := abs_sub_le
    (xiGaussianCompletedSourceResidual (P.1 + xiGaussianAnnihilator F) (xiGaussianHeatAfter t₀ s) -
      xiGaussianCompletedSourceResidual P.1 (xiGaussianHeatAfter t₀ s)) 0
    (xiGaussianCompletedSourceResidual (xiGaussianAnnihilator F) (xiGaussianHeatAfter t₀ s))
  simp only [sub_zero, zero_sub, abs_neg] at h
  have hs := h.trans_lt (add_lt_add (hF s P).2.2.2 (hD s))
  have he : π * (e : ℝ) + (e' : ℝ) = (ε : ℝ) := by
    dsimp only [e, e']
    field_simp [Real.pi_ne_zero]
    ring
  rwa [he] at hs

end RHTower
