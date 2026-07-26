import GaloisForLFunctions.RHTower.ComplementaryPacketModulusMeasurable
import GaloisForLFunctions.RHTower.MobiusIncidenceClockGiniFisherFourUnit

/-!
# The critical packet energy of the complementary boundary packet is four

The clock carried by the squarefree critical source is already rescaled: the law
`squarefreeMobiusCriticalGapProbabilityMeasure σ` is the law of `ε (log d − log e)` with
`ε = σ − 1`, and its absolute first moment tends to one.  The packet modulus, however, is a
function of the *unrescaled* separation, so the source-framed packet energy is

```text
E_σ = 4 ε ∫ D_ω (|x| / ε) dμ_σ(x) ,        ω = ε/2 .
```

The cofinal bound `|D_ω a − c_ω² a| ≤ C` with a defect `C` uniform near the boundary turns this
into `4 c_ω² ∫ |x| dμ_σ + O(ε)`, hence into four.

* `RHTower.tendsto_four_mul_rescaledPacketEnergy` — the source-independent transfer;
* `RHTower.complementaryPacketDefect_le` — the uniform defect near the critical boundary;
* `RHTower.integrable_abs_squarefreeMobiusCriticalGap` — the clock gap has a finite absolute
  first moment, which is the last measure-theoretic hypothesis of the transfer.
-/

open MeasureTheory Filter Set

namespace RHTower

noncomputable section

/-- **Rescaled four-unit transfer.**  The clock law is already rescaled by `ε`, so the modulus is
evaluated at `|x| / ε`. -/
theorem tendsto_four_mul_rescaledPacketEnergy
    {ι : Type*} {F : Filter ι} [F.NeBot]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)] {ε c : ι → ℝ}
    {D : ι → ℝ → ℝ} {C : ℝ}
    (hD : ∀ᶠ i in F, ∀ a : ℝ, 0 ≤ a → |D i a - c i ^ 2 * a| ≤ C)
    (hDint : ∀ᶠ i in F, Integrable (fun x : ℝ => D i (|x| / ε i)) (μ i))
    (habs : ∀ᶠ i in F, Integrable (fun x : ℝ => |x|) (μ i))
    (hεpos : ∀ᶠ i in F, 0 < ε i)
    (hε : Tendsto ε F (nhds 0))
    (hgini : Tendsto (fun i => ∫ x, |x| ∂(μ i)) F (nhds 1))
    (hc : Tendsto c F (nhds 1)) :
    Tendsto (fun i => 4 * ε i * ∫ x, D i (|x| / ε i) ∂(μ i)) F (nhds 4) := by
  have hmain : Tendsto (fun i => 4 * c i ^ 2 * ∫ x, |x| ∂(μ i)) F (nhds 4) := by
    have h := (((hc.pow 2).const_mul (4 : ℝ))).mul hgini
    simpa using h
  have hrem : Tendsto
      (fun i => 4 * ε i * (∫ x, D i (|x| / ε i) ∂(μ i))
        - 4 * c i ^ 2 * ∫ x, |x| ∂(μ i)) F (nhds 0) := by
    have hbound : Tendsto (fun i => 4 * C * ε i) F (nhds 0) := by
      have h := hε.const_mul (4 * C)
      simpa using h
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hD, hDint, habs, hεpos] with i hDi hDinti habsi hεi
    have hsplit : (∫ x, (ε i * D i (|x| / ε i) - c i ^ 2 * |x|) ∂(μ i))
        = ε i * (∫ x, D i (|x| / ε i) ∂(μ i)) - c i ^ 2 * ∫ x, |x| ∂(μ i) := by
      rw [integral_sub (hDinti.const_mul _) (habsi.const_mul _), integral_const_mul,
        integral_const_mul]
    have hpt : ∀ x : ℝ, ‖ε i * D i (|x| / ε i) - c i ^ 2 * |x|‖ ≤ C * ε i := by
      intro x
      have hnn : (0 : ℝ) ≤ |x| / ε i := div_nonneg (abs_nonneg x) hεi.le
      have h := hDi (|x| / ε i) hnn
      have hrw : ε i * D i (|x| / ε i) - c i ^ 2 * |x|
          = ε i * (D i (|x| / ε i) - c i ^ 2 * (|x| / ε i)) := by
        field_simp
      rw [Real.norm_eq_abs, hrw, abs_mul, abs_of_pos hεi]
      calc ε i * |D i (|x| / ε i) - c i ^ 2 * (|x| / ε i)|
          ≤ ε i * C := mul_le_mul_of_nonneg_left h hεi.le
        _ = C * ε i := by ring
    have hnorm : ‖∫ x, (ε i * D i (|x| / ε i) - c i ^ 2 * |x|) ∂(μ i)‖ ≤ C * ε i := by
      have h := norm_integral_le_of_norm_le_const (μ := μ i) (C := C * ε i)
        (Filter.Eventually.of_forall hpt)
      simpa using h
    rw [hsplit] at hnorm
    rw [Real.norm_eq_abs] at hnorm ⊢
    have hfac : 4 * ε i * (∫ x, D i (|x| / ε i) ∂(μ i)) - 4 * c i ^ 2 * ∫ x, |x| ∂(μ i)
        = 4 * (ε i * (∫ x, D i (|x| / ε i) ∂(μ i)) - c i ^ 2 * ∫ x, |x| ∂(μ i)) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    calc 4 * |ε i * (∫ x, D i (|x| / ε i) ∂(μ i)) - c i ^ 2 * ∫ x, |x| ∂(μ i)|
        ≤ 4 * (C * ε i) := mul_le_mul_of_nonneg_left hnorm (by norm_num)
      _ = 4 * C * ε i := by ring
  have hsum := hrem.add hmain
  rw [zero_add] at hsum
  refine hsum.congr fun i => ?_
  ring

/-! ### The uniform defect of the complementary packet near the boundary -/

/-- Near the critical boundary the cofinal defect of the complementary packet is at most `14`. -/
theorem complementaryPacketDefect_le {ω : ℝ} (hω : 0 ≤ ω) (hω' : ω ≤ 1 / 2) {a : ℝ}
    (ha : 0 ≤ a) :
    |packetTranslationModulus (complementaryPacketKernel ω) (complementaryPacketConstant ω) a
        - complementaryPacketConstant ω ^ 2 * a| ≤ 14 := by
  refine le_trans (abs_complementaryPacketModulus_sub_le ω hω ha) ?_
  have h4 : (4 : ℝ) ^ ω ≤ 2 := by
    calc (4 : ℝ) ^ ω ≤ (4 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hω'
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num,
            ← Real.rpow_mul (by norm_num)]
          norm_num
  have h2 : (2 : ℝ) ^ ω ≤ 2 := by
    calc (2 : ℝ) ^ ω ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hc : |complementaryPacketConstant ω| ≤ 1 := by
    rw [complementaryPacketConstant, abs_of_nonneg (by positivity)]
    rw [div_le_one (by linarith)]
    linarith
  have hcnn : (0 : ℝ) ≤ |complementaryPacketConstant ω| := abs_nonneg _
  have h2nn : (0 : ℝ) ≤ (2 : ℝ) ^ ω := Real.rpow_nonneg (by norm_num) ω
  nlinarith

/-! ### The clock gap has a finite absolute first moment -/

/-- The oriented squarefree critical clock gap is absolutely integrable: its square is, and
`|x| ≤ (x² + 1)/2`. -/
theorem integrable_abs_squarefreeMobiusCriticalGap {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun x : ℝ => |x|)
      (squarefreeMobiusCriticalGapProbabilityMeasure σ : Measure ℝ) := by
  have hsq := integrable_squarefreeMobiusCriticalGap_sq hσ
  refine Integrable.mono' ((hsq.add (integrable_const (1 : ℝ))).const_mul (1 / 2))
    continuous_abs.measurable.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_abs]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (|x| - 1), abs_nonneg x, sq_abs x]

/-! ### Integrability of the rescaled modulus -/

/-- The scaled form of `integrable_packetTranslationModulus_abs`: the modulus read at `|x| / ε`
is integrable against every probability measure with a finite absolute first moment. -/
theorem integrable_packetTranslationModulus_abs_div
    {k : ℝ → ℝ} {A B c ε : ℝ} (hmk : Measurable k)
    (hint : IntegrableOn k (Ioi 0)) (hsq : IntegrableOn (fun r => k r ^ 2) (Ioi 0))
    (hA : (∫ r in Ioi (0 : ℝ), |k r|) ≤ A)
    (hB : (∫ r in Ioi (0 : ℝ), k r ^ 2) ≤ B)
    (hε : 0 < ε) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (habs : Integrable (fun x : ℝ => |x|) μ) :
    Integrable (fun x : ℝ => packetTranslationModulus k c (|x| / ε)) μ := by
  set C : ℝ := 5 * B + 2 * |c| * A with hCdef
  have hmeas : Measurable fun x : ℝ => packetTranslationModulus k c (|x| / ε) :=
    (measurable_packetTranslationModulus hmk hint hsq c).comp
      (continuous_abs.measurable.div_const ε)
  have hdom : Integrable (fun x : ℝ => c ^ 2 / ε * |x| + C) μ :=
    (habs.const_mul (c ^ 2 / ε)).add (integrable_const C)
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  have hnn : (0 : ℝ) ≤ |x| / ε := div_nonneg (abs_nonneg x) hε.le
  have hbound := abs_packetTranslationModulus_sub_le (c := c) hmk hint hsq hA hB hnn
  have hval : c ^ 2 * (|x| / ε) = c ^ 2 / ε * |x| := by ring
  rw [hval] at hbound
  have hnn2 : (0 : ℝ) ≤ c ^ 2 / ε * |x| := by positivity
  rw [Real.norm_eq_abs, abs_le]
  have h := abs_le.mp hbound
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ### The four-unit critical packet energy -/

/-- The source-framed critical packet energy of the complementary boundary packet. -/
def complementaryPacketCriticalEnergy (σ : ℝ) : ℝ :=
  4 * (σ - 1) *
    ∫ x, packetTranslationModulus (complementaryPacketKernel ((σ - 1) / 2))
        (complementaryPacketConstant ((σ - 1) / 2)) (|x| / (σ - 1))
      ∂(squarefreeMobiusCriticalGapProbabilityMeasure σ : Measure ℝ)

/-- **Exact critical four-unit packet energy.**  The complementary boundary packet, framed by the
squarefree critical divisor clock, has critical energy exactly four.  The bounded local defect —
the `ζ(2)` expansion at infinitesimal separation — is annihilated by the escaping arithmetic
clock, and only the cofinal slope `c_ω² → 1` survives. -/
theorem tendsto_complementaryPacketCriticalEnergy :
    Tendsto complementaryPacketCriticalEnergy (nhdsWithin 1 (Ioi 1)) (nhds 4) := by
  have hlt2 : ∀ᶠ σ : ℝ in nhdsWithin 1 (Ioi 1), σ < 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hεpos : ∀ᶠ σ : ℝ in nhdsWithin 1 (Ioi 1), 0 < σ - 1 := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact sub_pos.mpr hσ
  have hD : ∀ᶠ σ : ℝ in nhdsWithin 1 (Ioi 1), ∀ a : ℝ, 0 ≤ a →
      |packetTranslationModulus (complementaryPacketKernel ((σ - 1) / 2))
          (complementaryPacketConstant ((σ - 1) / 2)) a
        - complementaryPacketConstant ((σ - 1) / 2) ^ 2 * a| ≤ 14 := by
    filter_upwards [self_mem_nhdsWithin, hlt2] with σ hσ hσ2 a ha
    have h1 : (1 : ℝ) < σ := hσ
    exact complementaryPacketDefect_le (by linarith) (by linarith) ha
  have habs : ∀ᶠ σ : ℝ in nhdsWithin 1 (Ioi 1),
      Integrable (fun x : ℝ => |x|)
        (squarefreeMobiusCriticalGapProbabilityMeasure σ : Measure ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact integrable_abs_squarefreeMobiusCriticalGap hσ
  have hDint : ∀ᶠ σ : ℝ in nhdsWithin 1 (Ioi 1),
      Integrable (fun x : ℝ =>
          packetTranslationModulus (complementaryPacketKernel ((σ - 1) / 2))
            (complementaryPacketConstant ((σ - 1) / 2)) (|x| / (σ - 1)))
        (squarefreeMobiusCriticalGapProbabilityMeasure σ : Measure ℝ) := by
    filter_upwards [self_mem_nhdsWithin, habs] with σ hσ habsσ
    have hω : (0 : ℝ) ≤ (σ - 1) / 2 := by
      have : (1 : ℝ) < σ := hσ
      linarith
    exact integrable_packetTranslationModulus_abs_div
      (measurable_complementaryPacketKernel _ hω)
      (integrableOn_complementaryPacketKernel _ hω)
      (integrableOn_complementaryPacketKernel_sq _ hω)
      (setIntegral_abs_complementaryPacketKernel_le _ hω)
      (setIntegral_complementaryPacketKernel_sq_le _ hω)
      (sub_pos.mpr hσ) habsσ
  have hε : Tendsto (fun σ : ℝ => σ - 1) (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    have h : Tendsto (fun σ : ℝ => σ - 1) (nhds (1 : ℝ)) (nhds ((1 : ℝ) - 1)) :=
      tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun σ : ℝ => complementaryPacketConstant ((σ - 1) / 2))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    have hcont : ContinuousAt (fun σ : ℝ => 1 / (1 + (σ - 1) / 2)) 1 := by
      refine ContinuousAt.div continuousAt_const ?_ (by norm_num)
      fun_prop
    have h : Tendsto (fun σ : ℝ => 1 / (1 + (σ - 1) / 2)) (nhdsWithin 1 (Ioi 1))
        (nhds (1 / (1 + ((1 : ℝ) - 1) / 2))) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa [complementaryPacketConstant] using h
  exact tendsto_four_mul_rescaledPacketEnergy hD hDint habs hεpos hε
    tendsto_integral_abs_squarefreeMobiusCriticalGapProbabilityMeasure hc

end

end RHTower
