import GaloisForLFunctions.RHTower.SoninExtendedMellinPole
import GaloisForLFunctions.RHTower.SoninTruncatedMellinCauchy

/-!
# The Mellin transform of a vector of `L_a` as a continuous linear functional

On the strip `1/2 < Re s < 1` the Mellin integral `∫_0^∞ f(t)t^{-s}dt` of a vector of the extended
Sonine space splits into an explicit head `c·a^{1-s}/(1-s)` and a tail `∫_a^∞ f(t)t^{-s}dt`
(`integral_split_extendedMellin`).  Both pieces are inner products against fixed `L²` vectors — the
band indicator computes the head constant, and the tail power `1_{(a,∞)}t^{-s̄}` is square
integrable exactly because `Re s > 1/2`.  So the Mellin transform is the restriction to `L_a` of a
*continuous linear functional* on the whole of `L²(ℝ)`, and therefore commutes with Bochner
integrals of `L²`-valued families.

## Main results

* `tailPowerVector`, `inner_tailPowerVector`
* `inner_bandIndicator_eq_head`
* `mellinFunctional`, `mellinFunctional_apply_eq`
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace RHTower

/-- The tail power `1_{(a,∞)}t^{-s}` is square integrable for `Re s > 1/2`. -/
theorem memLp_two_tailPower {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 / 2 < s.re) :
    MemLp ((Ioi a).indicator (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s))) 2 (volume : Measure ℝ) :=
  (memLp_indicator_iff_restrict measurableSet_Ioi).2 (memLp_two_cpow_Ioi ha hs)

/-- The tail power, as a vector of `L²(ℝ)`. -/
def tailPowerVector (a : ℝ) (ha : 0 < a) {s : ℂ} (hs : 1 / 2 < s.re) : SoninL2 :=
  (memLp_two_tailPower ha (s := (starRingEnd ℂ) s) (by rwa [Complex.conj_re])).toLp _

/-- Pairing the tail power against a vector recovers the Mellin tail integral. -/
theorem inner_tailPowerVector {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 / 2 < s.re) (f : SoninL2) :
    ⟪tailPowerVector a ha hs, f⟫_ℂ
      = ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  rw [MeasureTheory.L2.inner_def]
  have hcoe := (memLp_two_tailPower ha (s := (starRingEnd ℂ) s)
    (by rwa [Complex.conj_re])).coeFn_toLp
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with u hu
  have hWu : ((tailPowerVector a ha hs : SoninL2) : ℝ → ℂ) u
      = (Ioi a).indicator (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-(starRingEnd ℂ) s)) u := by
    simp only [tailPowerVector]
    exact hu
  have hlhs : (starRingEnd ℂ) (((tailPowerVector a ha hs : SoninL2) : ℝ → ℂ) u)
      = (Ioi a).indicator (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s)) u := by
    rw [hWu]
    by_cases hmem : u ∈ Ioi a
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        conj_ofReal_cpow_neg (lt_trans ha hmem) s]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, map_zero]
  rw [RCLike.inner_apply, hlhs]
  by_cases hmem : u ∈ Ioi a
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    ring
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    ring

/-- Pairing against the band indicator reads off the head constant. -/
theorem inner_bandIndicator_eq_head {a : ℝ} (ha : 0 < a) {f : SoninL2} {c : ℂ}
    (hc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = c) :
    ⟪bandIndicator a, f⟫_ℂ = ((2 * a : ℝ) : ℂ) * c := by
  rw [MeasureTheory.L2.inner_def]
  have hsimp : (∫ u : ℝ, inner ℂ (((bandIndicator a : SoninL2) : ℝ → ℂ) u) ((f : ℝ → ℂ) u))
      = ∫ u : ℝ, (centralInterval a).indicator (fun _ : ℝ => c) u := by
    refine integral_congr_ae ?_
    filter_upwards [bandIndicator_coeFn a, hc] with u hb hf
    rw [RCLike.inner_apply, hb]
    by_cases hmem : u ∈ centralInterval a
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hf hmem, map_one]
      ring
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, map_zero]
      ring
  rw [hsimp, MeasureTheory.integral_indicator (measurableSet_centralInterval a),
    setIntegral_const, centralInterval]
  have hvol : (volume : Measure ℝ).real (Icc (-a) a) = 2 * a := by
    rw [Measure.real, Real.volume_Icc]
    have hsub : a - -a = 2 * a := by ring
    rw [hsub, ENNReal.toReal_ofReal (by linarith)]
  rw [hvol, Complex.real_smul]

/-- **The Mellin transform as a continuous linear functional.** -/
def mellinFunctional (a : ℝ) (ha : 0 < a) {s : ℂ} (hs : 1 / 2 < s.re) : SoninL2 →L[ℂ] ℂ :=
  ((((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / ((1 - s) * ((2 * a : ℝ) : ℂ))) • innerSL ℂ (bandIndicator a))
    + innerSL ℂ (tailPowerVector a ha hs)

theorem mellinFunctional_apply (a : ℝ) (ha : 0 < a) {s : ℂ} (hs : 1 / 2 < s.re) (f : SoninL2) :
    mellinFunctional a ha hs f
      = (((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / ((1 - s) * ((2 * a : ℝ) : ℂ)))
          * ⟪bandIndicator a, f⟫_ℂ + ⟪tailPowerVector a ha hs, f⟫_ℂ := rfl

/-- **On the extended Sonine space the functional is the Mellin integral.** -/
theorem mellinFunctional_apply_eq {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s.re < 1) {f : SoninL2} (hf : f ∈ centralSoninExtendedCarrier a) :
    mellinFunctional a ha hs f = ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  obtain ⟨c, hc⟩ := ae_eq_of_mem_extended hf
  rw [integral_split_extendedMellin ha hc hs hs1, mellinFunctional_apply,
    inner_bandIndicator_eq_head ha hc, inner_tailPowerVector]
  congr 1
  have h2a : ((2 * a : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    intro h
    have : a = 0 := by linarith
    exact ha.ne' this
  have hone : (1 : ℂ) - s ≠ 0 := by
    intro h
    have hre : ((1 : ℂ) - s).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith
  field_simp

end RHTower

end
