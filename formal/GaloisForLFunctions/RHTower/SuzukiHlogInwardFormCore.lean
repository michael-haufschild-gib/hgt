import GaloisForLFunctions.RHTower.SuzukiHlogDilationContinuity

/-!
# Inward compression inside Suzuki's logarithmic aperture form domain

The weighted dilation theorem is lifted from Fourier space to the literal aperture-supported
`H^log` form domain. Fourier covariance identifies it with normalized time dilation, whose support
is strictly compressed into the aperture. The resulting form-domain vectors converge to every
input in the exact form norm. This is the first approximation stage in Connes--Consani (2021),
Lemma `core`; no ordinary-`L²` density surrogate is used.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem suzukiHlogWeightedToL2_directInwardDilate
    (n : ℕ) (f : SuzukiHlogFourierL2) :
    suzukiHlogWeightedToL2 (suzukiHlogDirectInwardDilate n f) =
      dilation (suzukiHlogInwardScale n)⁻¹
        (inv_pos.mpr (suzukiHlogInwardScale_pos n))
        (suzukiHlogWeightedToL2 f) := by
  apply Lp.ext
  have hleft := suzukiHlogWeightedToL2_coeFn
    (suzukiHlogDirectInwardDilate n f)
  have hdirect := (suzukiHlogDirectInwardDilate_ae n f).filter_mono
    (ae_mono volume_le_suzukiHlogMeasure)
  have hright := dilation_ae (suzukiHlogInwardScale n)⁻¹
    (inv_pos.mpr (suzukiHlogInwardScale_pos n))
    (suzukiHlogWeightedToL2 f)
  have hf := (suzukiHlogWeightedToL2_coeFn f).comp_tendsto
    (realMul_quasiMeasurePreserving (suzukiHlogInwardScale n)⁻¹
      (inv_ne_zero (suzukiHlogInwardScale_pos n).ne')).tendsto_ae
  filter_upwards [hleft, hdirect, hright, hf] with x hl hd hr hf
  rw [hl, hd, hr]
  unfold suzukiHlogDilatedFn
  rw [Real.sqrt_inv]
  congr 1
  simpa only [Function.comp_apply] using hf.symm

theorem suzukiHlogFourierToTime_directInwardDilate
    (n : ℕ) (f : SuzukiHlogFourierL2) :
    suzukiHlogFourierToTime (suzukiHlogDirectInwardDilate n f) =
      dilation (suzukiHlogInwardScale n) (suzukiHlogInwardScale_pos n)
        (suzukiHlogFourierToTime f) := by
  apply fourierUnitary.injective
  rw [fourierUnitary_suzukiHlogFourierToTime,
    suzukiHlogWeightedToL2_directInwardDilate, fourierUnitary_dilation,
    fourierUnitary_suzukiHlogFourierToTime]

theorem indicatorCutoff_central_eq_self_of_radius_le
    {a b : ℝ} (hab : a ≤ b) (f : SoninL2)
    (hf : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f = f) :
    indicatorCutoff (centralInterval b) (measurableSet_centralInterval b) f = f := by
  apply Lp.ext
  have hfix :
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f :
          ℝ → ℂ) =ᵐ[volume] f := by rw [hf]
  filter_upwards [
    indicatorCutoff_ae (centralInterval b) (measurableSet_centralInterval b) f,
    indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) f,
    hfix] with x hb ha hfixx
  rw [hb]
  by_cases hxb : x ∈ centralInterval b
  · rw [Set.indicator_of_mem hxb]
  · have hxa : x ∉ centralInterval a := by
      intro hxa
      apply hxb
      rw [centralInterval] at hxa ⊢
      constructor <;> linarith [hxa.1, hxa.2]
    rw [Set.indicator_of_notMem hxb]
    have hzero : f x = 0 := by
      rw [ha, Set.indicator_of_notMem hxa] at hfixx
      exact hfixx.symm
    rw [hzero]

def suzukiHlogFormInwardDilate
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SuzukiHlogFormDomain a) :
    SuzukiHlogFormDomain a :=
  ⟨suzukiHlogDirectInwardDilate n f.1, by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (suzukiHlogFourierToTime (suzukiHlogDirectInwardDilate n f.1)) = 0
    rw [suzukiHlogFourierToTime_directInwardDilate, sub_apply, one_apply_eq_self, sub_eq_zero,
      indicatorCutoff_dilation]
    apply congrArg (dilation (suzukiHlogInwardScale n)
      (suzukiHlogInwardScale_pos n))
    have hfix := indicatorCutoff_suzukiHlogFormEmbedding a f
    change indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (suzukiHlogFourierToTime f.1) =
        suzukiHlogFourierToTime f.1 at hfix
    apply (indicatorCutoff_central_eq_self_of_radius_le
      (f := suzukiHlogFourierToTime f.1) _ hfix).symm
    have hscale : 1 ≤ suzukiHlogInwardScale n := by
      unfold suzukiHlogInwardScale
      have hinv : 0 ≤ (((n + 1 : ℕ) : ℝ))⁻¹ := by positivity
      linarith
    nlinarith [a.2]⟩

theorem suzukiHlogFormInwardDilate_tendsto
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    Tendsto (fun n => suzukiHlogFormInwardDilate a n f) atTop (nhds f) := by
  rw [tendsto_subtype_rng]
  exact suzukiHlogDirectInwardDilate_tendsto f.1

end RHTower
