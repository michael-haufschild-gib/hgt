import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilChartsAreUniformlyBounded
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilChainIsOneScalarFlow

/-!
# The endpoint traces have their soft prime kick

Compare two apertures `a ≤ b = a + h` in the left-endpoint coordinate: `Δ = s_b − ρ s_a`, with
`ρ = e^{i z̄ h}`. The evaluation exponentials cancel, so the chart forcings differ only through `Δ`.

* **Energy** (`exists_chartIncrement_mass_bound`): the Hilbert residual gives `‖Δ‖₁ ≤ C√h`.
* **Interior smallness** (`exists_interior_bound`): away from the far endpoint,
  `|Δ| ≤ C V(3η) V(h^{1/4}) + C_η h^{1/4}`. The first constant does not depend on `η`.
* **The increment** (`exists_trace_increment_bound`): `τ_L(b,z) − ρ τ_L(a,z)` is the readout of the
  chart forcing of `Δ`. Up to interior size it equals `w τ_R(b,z) J(2h)`, with `J` the renewal coupling.
* **The kick** (`tendsto_leftTrace_right_kick`): as `b ↓ a`,
  `(τ_L(b,z) − τ_L(a,z)) log(1/(b−a)) → w(a) τ_R(a,z)`, where `w(a) = Λ(n)/√n` if `2a = log n`, and
  `w(a) = 0` when no integer has that logarithm. Approaching from below there is no kick at all
  (`tendsto_leftTrace_left_kick`).
* **The scalar flow**: `r` is continuous before contact (`continuousAt_anchorReflection`), and
  `(Ψ(x) − Ψ(a)) log(1/(x−a)) → w(a)` as `x ↓ a` (`tendsto_canonicalPotential_right_kick`).

The kick is continuous, of size `1/log(1/ε)`: this is the singular part of the potential at
`2a = log n`. Prime powers act only from the right of their aperture.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

local notation "v" => logarithmicCausalKernel
local notation "V" => logarithmicRenewalMass

namespace WeilHilbertBeforeContact
open GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

/-- The phase relating the two evaluation exponentials. -/
def chartPhase (z : ℂ) (h : ℝ) : ℂ := Complex.exp (I * (starRingEnd ℂ) z * (h : ℂ))

/-- The increment of the Riesz source in the left-endpoint coordinate. -/
def chartIncrement (a b : PrecontactAperture) (z : ℂ) (t : ℝ) : ℂ :=
  chartSource b z t - chartPhase z (b.1.1 - a.1.1) * chartSource a z t

theorem continuous_chartIncrement (a b : PrecontactAperture) (z : ℂ) :
    Continuous (chartIncrement a b z) :=
  (continuous_chartSource b z).sub (continuous_const.mul (continuous_chartSource a z))

theorem chartIncrement_eq_zero {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ) {t : ℝ}
    (ht : t ≤ 0 ∨ 2 * b.1.1 ≤ t) : chartIncrement a b z t = 0 := by
  have h1 := chartSource_eq_zero b z ht
  have h2 : chartSource a z t = 0 := chartSource_eq_zero a z (by
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith only [h, hab]))
  rw [chartIncrement, h1, h2, mul_zero, sub_zero]

theorem hasCompactSupport_chartIncrement {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    HasCompactSupport (chartIncrement a b z) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 2 * b.1.1))
  intro t ht
  apply chartIncrement_eq_zero hab
  have hs : ¬(0 ≤ t ∧ t ≤ 2 * b.1.1) := ht
  rcases not_and_or.mp hs with h | h
  · exact Or.inl (lt_of_not_ge h).le
  · exact Or.inr (lt_of_not_ge h).le

theorem norm_chartPhase (z : ℂ) (h : ℝ) : ‖chartPhase z h‖ = Real.exp (h * z.im) := by
  rw [chartPhase, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring

/-- The two evaluation exponentials differ by the phase. -/
theorem exp_forcing_shift (z : ℂ) (y a b : ℝ) :
    Complex.exp (-I * star z * ((y - b : ℝ) : ℂ)) =
      chartPhase z (b - a) * Complex.exp (-I * star z * ((y - a : ℝ) : ℂ)) := by
  rw [chartPhase, ← Complex.exp_add]
  congr 1
  simp only [RCLike.star_def]
  push_cast
  ring

/-- The orthogonal residual of a translated Riesz vector. -/
def chartResidual (a b : PrecontactAperture) (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    WeilHilbertBeforeContact b :=
  evalVector b z - chartPhase z (b.1.1 - a.1.1) •
    translate (b.1.1 - a.1.1) (by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; linarith only)
      (evalVector a z)

/-- The residual has the norm of the translated kernel difference. -/
theorem norm_chartResidual_sq (a b : PrecontactAperture) (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    ‖chartResidual a b hab z‖ ^ 2 =
      ‖evalVector b z‖ ^ 2 - Real.exp ((b.1.1 - a.1.1) * z.im) ^ 2 * ‖evalVector a z‖ ^ 2 := by
  set h := b.1.1 - a.1.1 with hh
  have hfit : a.1.1 + |h| ≤ b.1.1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    linarith only
  set T := translate (a := a) (b := b) h hfit
  have hi : inner ℂ (evalVector b z) (T (evalVector a z)) =
      Complex.exp (-I * z * (h : ℂ)) * (‖evalVector a z‖ : ℂ) ^ 2 := by
    rw [inner_evalVector]
    change fourier b (T (evalVector a z)) z = _
    rw [fourier_translate]
    change _ * eval a z (evalVector a z) = _
    rw [evalVector_self]
  have hphase : chartPhase z h * Complex.exp (-I * z * (h : ℂ)) =
      ((Real.exp (h * z.im) ^ 2 : ℝ) : ℂ) := by
    rw [chartPhase, ← Complex.exp_add, ← Real.exp_nat_mul, Complex.ofReal_exp]
    congr 1
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re,
        Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im]
      push_cast
      ring
    · simp only [Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re,
        Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im]
      ring
  change ‖evalVector b z - chartPhase z h • T (evalVector a z)‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hi, norm_smul, T.norm_map, norm_chartPhase]
  rw [← mul_assoc, hphase]
  have hRe (w : ℂ) : RCLike.re w = w.re := rfl
  rw [hRe, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- The residual has the literal physical increment. -/
theorem physical_chartResidual_ae (a b : PrecontactAperture) (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    (ccmArchimedeanFormEmbedding b.1 (toForm b (chartResidual a b hab z)) : ℝ → ℂ) =ᵐ[volume]
      fun x => chartIncrement a b z (x + b.1.1) := by
  set h := b.1.1 - a.1.1 with hh
  have hfit : a.1.1 + |h| ≤ b.1.1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    linarith only
  have hval : ccmArchimedeanFormEmbedding b.1 (toForm b (chartResidual a b hab z)) =
      ccmArchimedeanFormEmbedding b.1 (toForm b (evalVector b z)) -
        chartPhase z h • logTranslationCLM h
          (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z))) := by
    rw [chartResidual]
    simp only [map_sub, map_smul]
    congr 2
    exact physical_translate h hfit (evalVector a z)
  rw [hval]
  have hU := evalVectorContinuousRepresentative_ae a z
  have hshift := hU.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_sub (ccmArchimedeanFormEmbedding b.1 (toForm b (evalVector b z)))
      (chartPhase z h • logTranslationCLM h
        (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))),
    Lp.coeFn_smul (chartPhase z h) (logTranslationCLM h
      (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))),
    logarithmicTranslation_coeFn h (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z))),
    evalVectorContinuousRepresentative_ae b z, hshift] with x h1 h2 h3 h4 h5
  change evalVectorContinuousRepresentative a z (x + h) =
    ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)) (x + h) at h5
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, h3, ← h4, ← h5, chartIncrement, chartSource,
    chartSource]
  rw [add_sub_cancel_right, show x + b.1.1 - a.1.1 = x + h by rw [hh]; ring]

/-- The `L²` energy of the increment is at most the residual energy over the ground energy. -/
theorem groundEnergy_mul_chartIncrement_sq_le {a b c : PrecontactAperture} (hab : a.1.1 ≤ b.1.1)
    (hbc : b.1.1 ≤ c.1.1) (z : ℂ) :
    ccmRestrictedWeilGroundEnergy c.1 * ∫ t, ‖chartIncrement a b z t‖ ^ 2 ≤
      ‖chartResidual a b hab z‖ ^ 2 := by
  let w := chartResidual a b hab z
  have hphysical : ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hbc w)) =
      ccmArchimedeanFormEmbedding b.1 (toForm b w) := by
    rw [toForm_inclusion]
    exact ccmArchimedeanFormToAperture_coe_eq_of_val_eq
      (ArithmeticContinuationAndCriticalEnergy.apertureExt_val hbc (toForm b w))
  have hf := groundEnergy_mul_mass_le c (inclusion hbc w)
  rw [(inclusion hbc).norm_map] at hf
  change ccmRestrictedWeilGroundEnergy c.1 *
    ‖ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hbc w))‖ ^ 2 ≤ _ at hf
  rw [hphysical, Lp_two_norm_sq_eq_integral] at hf
  have hint : (∫ x, ‖ccmArchimedeanFormEmbedding b.1 (toForm b w) x‖ ^ 2) =
      ∫ t, ‖chartIncrement a b z t‖ ^ 2 := by
    rw [← integral_add_right_eq_self (fun t => ‖chartIncrement a b z t‖ ^ 2) b.1.1]
    apply integral_congr_ae
    filter_upwards [physical_chartResidual_ae a b hab z] with x hx
    rw [hx]
  rwa [hint] at hf

/-- `L²` energy controls `L¹` mass on the support, with any weight `λ > 0`. -/
private theorem integral_norm_le_of_sq {S : ℝ → ℂ} (hS : Continuous S) {T lam : ℝ} (hT : 0 ≤ T)
    (hlam : 0 < lam) (h0 : ∀ t, t ∉ Icc (0 : ℝ) T → S t = 0) :
    ∫ t, ‖S t‖ ≤ lam * T / 2 + (∫ t, ‖S t‖ ^ 2) / (2 * lam) := by
  have hc : HasCompactSupport S := HasCompactSupport.intro isCompact_Icc h0
  have hi : Integrable S := hS.integrable_of_hasCompactSupport hc
  have hsq : Integrable (fun t => ‖S t‖ ^ 2) :=
    (hS.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro
      (isCompact_Icc (a := 0) (b := T)) fun t ht => by
        change ‖S t‖ ^ 2 = 0
        rw [h0 t ht, norm_zero]
        norm_num)
  have hconst : Integrable ((Icc (0 : ℝ) T).indicator fun _ => lam / 2) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hle : ∫ t, ‖S t‖ ≤ ∫ t, ((Icc (0 : ℝ) T).indicator (fun _ => lam / 2) t +
      ‖S t‖ ^ 2 / (2 * lam)) := by
    apply integral_mono hi.norm (hconst.add (hsq.div_const _))
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) T
    · change ‖S t‖ ≤ (Icc (0 : ℝ) T).indicator (fun _ => lam / 2) t + ‖S t‖ ^ 2 / (2 * lam)
      rw [indicator_of_mem ht]
      have h2 : lam / 2 + ‖S t‖ ^ 2 / (2 * lam) - ‖S t‖ = (‖S t‖ - lam) ^ 2 / (2 * lam) := by
        field_simp
        ring
      have hnn : 0 ≤ (‖S t‖ - lam) ^ 2 / (2 * lam) := by positivity
      linarith only [h2, hnn]
    · change ‖S t‖ ≤ (Icc (0 : ℝ) T).indicator (fun _ => lam / 2) t + ‖S t‖ ^ 2 / (2 * lam)
      rw [indicator_of_notMem ht, h0 t ht, norm_zero]
      simp
  rw [integral_add hconst (hsq.div_const _), integral_indicator measurableSet_Icc,
    setIntegral_const, Real.volume_real_Icc_of_le hT, smul_eq_mul, sub_zero, integral_div] at hle
  calc
    _ ≤ _ := hle
    _ = _ := by ring


/-! ### Uniform endpoint data -/

/-- The sup norm of a chart forcing on a compact interval. -/
theorem chartForcing_sup_le (C : ChartCutoff) {a c : PrecontactAperture} (hac : a.1.1 ≤ c.1.1)
    (hC : ∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0) (z : ℂ) {M L : ℝ}
    (hM : ∀ t, ‖chartSource a z t‖ ≤ M) (hL : ∫ t, ‖chartSource a z t‖ ≤ L) :
    ∀ᵐ y ∂volume, ‖((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤
      Real.exp (2 * c.1.1 * |z.im|) +
        chartSupConstant (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊) * M +
        chartBoundedConstant (2 * c.1.1) (2 * c.1.1) * L + C.lip / 2 * L := by
  set N := Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊
  have hS := continuous_chartSource a z
  have hc := hasCompactSupport_chartSource a z
  have hi : Integrable (chartSource a z) := hS.integrable_of_hasCompactSupport hc
  have hL0 : 0 ≤ L := (integral_nonneg fun _ => norm_nonneg _).trans hL
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hK := chartSupConstant_nonneg N
  have hB := chartBoundedConstant_nonneg (2 * c.1.1) (2 * c.1.1)
  have hlip : 0 ≤ C.lip / 2 * L := mul_nonneg (div_nonneg C.lip_nonneg (by norm_num)) hL0
  have hE := Real.exp_pos (2 * c.1.1 * |z.im|)
  have hcomm (y : ℝ) : ‖C.commutatorIntegral (chartSource a z) y‖ ≤ C.lip / 2 * L :=
    (C.norm_commutatorIntegral_le hi y).trans
      (mul_le_mul_of_nonneg_left hL (div_nonneg C.lip_nonneg (by norm_num)))
  filter_upwards [chartForcing_negative C a z, chartForcing_ae C a hC z (N := N)
    (chartPrimeWindow_subset hac) fun n hn hn' => chartPrimeWindow_beyond hn hn'] with y h0 h1
  by_cases hy : y < 0
  · rw [h0 hy, norm_zero]
    positivity
  push Not at hy
  rw [h1 hy]
  refine (norm_add_le _ _).trans ?_
  by_cases hya : y < 2 * a.1.1
  · have hyc : y ≤ 2 * c.1.1 := by linarith only [hya, hac]
    have hexp : ‖Complex.exp (-I * star z * ((y - a.1.1 : ℝ) : ℂ))‖ ≤
        Real.exp (2 * c.1.1 * |z.im|) := by
      apply norm_exp_forcing_le
      apply abs_le.mpr
      have ha := a.1.2
      constructor <;> linarith only [hy, hya, hac, ha]
    have hb1 := (norm_chartBounded_le hS hc (R := 2 * c.1.1) (T := 2 * c.1.1) hy hyc
      (fun t ht => chartSource_eq_zero a z (Or.inl ht))
      (fun t ht => chartSource_eq_zero a z (Or.inr (by linarith only [ht, hac])))).trans
      (mul_le_mul_of_nonneg_left hL hB)
    have hsum : ‖Complex.exp (-I * star z * ((y - a.1.1 : ℝ) : ℂ)) +
        chartMass * chartSource a z y + chartBounded (chartSource a z) y +
        chartPrime N (chartSource a z) y‖ ≤ Real.exp (2 * c.1.1 * |z.im|) +
          chartBoundedConstant (2 * c.1.1) (2 * c.1.1) * L + chartSupConstant N * M := by
      have heq : Complex.exp (-I * star z * ((y - a.1.1 : ℝ) : ℂ)) +
          chartMass * chartSource a z y + chartBounded (chartSource a z) y +
          chartPrime N (chartSource a z) y =
          Complex.exp (-I * star z * ((y - a.1.1 : ℝ) : ℂ)) + chartBounded (chartSource a z) y +
            (chartMass * chartSource a z y + chartPrime N (chartSource a z) y) := by ring
      rw [heq]
      exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hexp hb1))
        ((norm_mass_add_prime_le N _ y).trans (chartMajorant_le N hM y)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hchi := mul_le_mul (C.abs_le y) hsum (norm_nonneg _) zero_le_one
    rw [one_mul] at hchi
    linarith only [hchi, hcomm y]
  · rw [hC y (not_lt.mp hya), Complex.ofReal_zero, zero_mul, norm_zero, zero_add]
    have hmul := mul_nonneg hK hM0
    have hmul2 := mul_nonneg hB hL0
    linarith only [hcomm y, hE, hmul, hmul2]

/-- **Uniform endpoint data.** On a compact precontact interval the trace, the `L¹` mass and the sup of
the source are bounded by one constant, and the source obeys a uniform edge law at the left endpoint. -/
theorem exists_uniform_endpoint_data (a₁ a₂ : PrecontactAperture) (z : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ a : PrecontactAperture, a₁.1.1 ≤ a.1.1 → a.1.1 ≤ a₂.1.1 →
      ‖evalVectorLeftTrace a z‖ ≤ A ∧ (∫ t, ‖chartSource a z t‖) ≤ A ∧
      (∀ t, ‖chartSource a z t‖ ≤ A) ∧
      ∀ t, t ≤ a.1.1 → ‖chartSource a z t‖ ≤ A * V t ∧
        ‖chartSource a z t - evalVectorLeftTrace a z * (V t : ℂ)‖ ≤ 2 * A * V t ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_chartSource_bound a₁ a₂ z
  have hμ := precontact_groundEnergy_pos a₂
  let L := a₂.1.1 + ‖evalVector a₂ z‖ ^ 2 / (2 * ccmRestrictedWeilGroundEnergy a₂.1)
  have hL0 : 0 ≤ L := add_nonneg a₂.1.2.le (by positivity)
  let N := Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊
  let A₀ := Real.exp (2 * a₂.1.1 * |z.im|) + chartSupConstant N * M +
    chartBoundedConstant (2 * a₂.1.1) (2 * a₂.1.1) * L + 1 / a₁.1.1 * L
  have hA₀ : 0 ≤ A₀ := by
    have h1 := chartSupConstant_nonneg N
    have h2 := chartBoundedConstant_nonneg (2 * a₂.1.1) (2 * a₂.1.1)
    have h3 := a₁.1.2
    dsimp only [A₀]
    positivity
  refine ⟨A₀ + M + L, by positivity, fun a ha₁ ha₂ => ?_⟩
  have hap : 0 < a.1.1 := a.1.2
  let C := ChartCutoff.endpoint a.1.1 hap
  have hCz : ∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0 := fun x hx =>
    logarithmicEndpointCutoff_eq_zero hap (by linarith only [hx, hap])
  have hCone : ∀ x, x ≤ a.1.1 → C.toFun x = 1 := fun x hx => logarithmicEndpointCutoff_eq_one hap hx
  have hLa : ∫ t, ‖chartSource a z t‖ ≤ L := integral_norm_chartSource_le ha₂ z
  have hlip : C.lip / 2 * L ≤ 1 / a₁.1.1 * L := by
    apply mul_le_mul_of_nonneg_right _ hL0
    change (2 / a.1.1) / 2 ≤ _
    rw [show (2 / a.1.1) / 2 = 1 / a.1.1 by field_simp]
    exact one_div_le_one_div_of_le a₁.1.2 ha₁
  have hF : ∀ᵐ y ∂volume, ‖((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) y‖ ≤
      A₀ + M + L := by
    filter_upwards [chartForcing_sup_le C ha₂ hCz z (fun t => (hM a ha₁ ha₂ t).1) hLa] with y hy
    dsimp only [A₀]
    linarith only [hy, hlip, hM0, hL0]
  have hA : 0 ≤ A₀ + M + L := by positivity
  have htrace : logarithmicBackwardConvolution (chartForcing C a z : RealLineL2) 0 =
      evalVectorLeftTrace a z :=
    logarithmicBackwardConvolution_chartForcing_zero C a hCz hap hCone z
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← htrace]
    exact norm_logarithmicBackwardConvolution_le hF 0
  · linarith only [hLa, hA₀, hM0]
  · intro t
    linarith only [(hM a ha₁ ha₂ t).1, hA₀, hL0]
  · intro t ht
    have hG := logarithmicGreenRepresentative_chartForcing C a hCz z t
    rw [hCone t ht, Complex.ofReal_one, one_mul] at hG
    constructor
    · rw [← hG]
      exact norm_logarithmicGreenRepresentative_le _ fun r _ =>
        norm_logarithmicBackwardConvolution_le hF r
    · by_cases ht0 : t ≤ 0
      · have hV : V t = 0 := by
          change ∫ s in Ioc (0 : ℝ) t, v s = 0
          rw [Ioc_eq_empty_of_le ht0]
          simp
        rw [chartSource_eq_zero a z (Or.inl ht0), hV]
        simp
      · rw [← hG, ← htrace]
        exact norm_logarithmicGreenRepresentative_sub_le _ hF (not_le.mp ht0)

/-! ### Energy of the increment -/

/-- **The `L¹` mass of the increment is at most `C√h`.** -/
theorem exists_chartIncrement_mass_bound (a₁ a₂ : PrecontactAperture) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : PrecontactAperture, a₁.1.1 ≤ a.1.1 → a.1.1 ≤ b.1.1 → b.1.1 ≤ a₂.1.1 →
      0 < b.1.1 - a.1.1 →
      ∫ t, ‖chartIncrement a b z t‖ ≤ C * Real.sqrt (b.1.1 - a.1.1) := by
  obtain ⟨A, hA0, hA⟩ := exists_uniform_endpoint_data a₁ a₂ z
  obtain ⟨A', hA'0, hA'⟩ := exists_uniform_endpoint_data a₁ a₂ (-z)
  have hμ := precontact_groundEnergy_pos a₂
  let D := A ^ 2 + A' ^ 2 + 2 * |z.im| * ‖evalVector a₂ z‖ ^ 2
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨a₂.1.1 + D / (2 * ccmRestrictedWeilGroundEnergy a₂.1),
    add_nonneg a₂.1.2.le (by positivity), fun a b ha₁ hab hb₂ hh => ?_⟩
  set h := b.1.1 - a.1.1 with hhdef
  have hba₂ : b.1.1 ≤ a₂.1.1 := hb₂
  have hs : Icc a.1.1 b.1.1 ⊆ precontactSet := fun x hx =>
    ⟨a.1.2.trans_le hx.1, (EReal.coe_le_coe_iff.mpr hx.2).trans_lt b.2⟩
  obtain ⟨hDi, hDv⟩ := integral_diagonalEndpointEnergy_eq_sub z hab hs
  -- The kernel gain is linear in the aperture increment.
  have hgain : diagonalEvalGram z b.1.1 - diagonalEvalGram z a.1.1 ≤ (A ^ 2 + A' ^ 2) * h := by
    rw [← hDv]
    have hle : ∀ x ∈ Icc a.1.1 b.1.1, diagonalEndpointEnergy z x ≤ A ^ 2 + A' ^ 2 := by
      intro x hx
      have hxp := hs hx
      rw [diagonalEndpointEnergy, dif_pos hxp]
      have hl := (hA (toPrecontact hxp) (ha₁.trans hx.1) (hx.2.trans hb₂)).1
      have hr := (hA' (toPrecontact hxp) (ha₁.trans hx.1) (hx.2.trans hb₂)).1
      change ‖evalVectorLeftTrace (toPrecontact hxp) z‖ ^ 2 +
        ‖evalVectorRightTrace (toPrecontact hxp) z‖ ^ 2 ≤ _
      rw [evalVectorRightTrace_eq_leftTrace_neg]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hl 2
      have h2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
      linarith only [h1, h2]
    have hint := intervalIntegral.integral_mono_on hab hDi
      (intervalIntegrable_const (c := A ^ 2 + A' ^ 2)) hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at hint
    linarith only [hint]
  -- The residual energy is at most `D h`.
  have hres : ‖chartResidual a b hab z‖ ^ 2 ≤ D * h := by
    rw [norm_chartResidual_sq, ← diagonalEvalGram_eq_norm z b, ← diagonalEvalGram_eq_norm z a]
    have hexp : 1 + 2 * (h * z.im) ≤ Real.exp (h * z.im) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have := Real.add_one_le_exp (((2 : ℕ) : ℝ) * (h * z.im))
      push_cast at this ⊢
      linarith only [this]
    have hKa : 0 ≤ diagonalEvalGram z a.1.1 := by
      rw [diagonalEvalGram_eq_norm z a]
      exact sq_nonneg _
    have hKa2 : diagonalEvalGram z a.1.1 ≤ ‖evalVector a₂ z‖ ^ 2 := by
      rw [diagonalEvalGram_eq_norm z a]
      exact norm_evalVector_sq_mono (hab.trans hb₂) z
    have hmul := mul_le_mul_of_nonneg_right hexp hKa
    have him : -(2 * (h * z.im)) ≤ 2 * h * |z.im| := by
      have := neg_abs_le z.im
      nlinarith only [this, hh]
    have him2 : 0 ≤ 2 * h * |z.im| := by positivity
    have hfinal : -(2 * (h * z.im) * diagonalEvalGram z a.1.1) ≤
        2 * h * |z.im| * ‖evalVector a₂ z‖ ^ 2 := by
      calc
        _ = -(2 * (h * z.im)) * diagonalEvalGram z a.1.1 := by ring
        _ ≤ 2 * h * |z.im| * diagonalEvalGram z a.1.1 := mul_le_mul_of_nonneg_right him hKa
        _ ≤ _ := mul_le_mul_of_nonneg_left hKa2 him2
    dsimp only [D]
    nlinarith only [hgain, hmul, hfinal]
  have hsqrt : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsqsq : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  have hL2 := groundEnergy_mul_chartIncrement_sq_le hab hb₂ z
  have hbound := integral_norm_le_of_sq (continuous_chartIncrement a b z) (T := 2 * b.1.1)
    (mul_nonneg (by norm_num) b.1.2.le) hsqrt (fun t ht => chartIncrement_eq_zero hab z (by
      have hs' : ¬(0 ≤ t ∧ t ≤ 2 * b.1.1) := ht
      rcases not_and_or.mp hs' with h' | h'
      · exact Or.inl (lt_of_not_ge h').le
      · exact Or.inr (lt_of_not_ge h').le))
  have hsq : (∫ t, ‖chartIncrement a b z t‖ ^ 2) ≤ D * h / ccmRestrictedWeilGroundEnergy a₂.1 := by
    rw [le_div_iff₀ hμ]
    nlinarith only [hL2, hres]
  have hdiv : (∫ t, ‖chartIncrement a b z t‖ ^ 2) / (2 * Real.sqrt h) ≤
      D / (2 * ccmRestrictedWeilGroundEnergy a₂.1) * Real.sqrt h := by
    rw [div_le_iff₀ (by positivity)]
    calc
      _ ≤ D * h / ccmRestrictedWeilGroundEnergy a₂.1 := hsq
      _ = D * (Real.sqrt h * Real.sqrt h) / ccmRestrictedWeilGroundEnergy a₂.1 := by rw [hsqsq]
      _ = _ := by field_simp
  have hmain : Real.sqrt h * (2 * b.1.1) / 2 ≤ a₂.1.1 * Real.sqrt h := by
    nlinarith only [hba₂, hsqrt]
  refine hbound.trans ?_
  rw [add_mul]
  exact add_le_add hmain hdiv


/-! ### Linearity of the forcing -/

private theorem integrable_bounded_mul {f k : ℝ → ℂ} (hf : Integrable f) (hk : Measurable k) {c : ℝ}
    (hb : ∀ t, ‖k t‖ ≤ c) : Integrable (fun t => k t * f t) :=
  (hf.mul_bdd hk.aestronglyMeasurable (Eventually.of_forall hb)).congr
    (Eventually.of_forall fun t => by simp only [mul_comm])

private theorem integrable_exp_source {S : ℝ → ℂ} (hS : Continuous S) (hc : HasCompactSupport S)
    (σ : ℝ) : Integrable (fun t : ℝ => (Real.exp (σ * t) : ℂ) * S t) :=
  (Continuous.mul (by fun_prop) hS).integrable_of_hasCompactSupport hc.mul_left

private theorem integrable_remainder_source {S : ℝ → ℂ} (hS : Integrable S) (y : ℝ) :
    Integrable (fun t : ℝ => (archLogRemainder |y - t| : ℂ) * S t) := by
  refine integrable_bounded_mul hS (c := 3 / 4) (Complex.continuous_ofReal.measurable.comp
    (measurable_archLogRemainder.comp (measurable_const.sub measurable_id).abs)) fun t => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (archLogRemainder_abs_nonneg _)]
  exact archLogRemainder_abs_le _

theorem chartBounded_sub_mul {S S' : ℝ → ℂ} (hS : Continuous S) (hc : HasCompactSupport S)
    (hS' : Continuous S') (hc' : HasCompactSupport S') (ρ : ℂ) (y' : ℝ) :
    chartBounded (fun t => S t - ρ * S' t) y' = chartBounded S y' - ρ * chartBounded S' y' := by
  have hi : Integrable S := hS.integrable_of_hasCompactSupport hc
  have hi' : Integrable S' := hS'.integrable_of_hasCompactSupport hc'
  have h1 : (∫ t : ℝ, (archLogRemainder |y' - t| : ℂ) * (S t - ρ * S' t)) =
      (∫ t : ℝ, (archLogRemainder |y' - t| : ℂ) * S t) -
        ρ * ∫ t : ℝ, (archLogRemainder |y' - t| : ℂ) * S' t := by
    rw [← integral_const_mul, ← integral_sub (integrable_remainder_source hi y')
      ((integrable_remainder_source hi' y').const_mul ρ)]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
  have h2 (σ : ℝ) : (∫ t : ℝ, (Real.exp (σ * t) : ℂ) * (S t - ρ * S' t)) =
      (∫ t : ℝ, (Real.exp (σ * t) : ℂ) * S t) - ρ * ∫ t : ℝ, (Real.exp (σ * t) : ℂ) * S' t := by
    rw [← integral_const_mul, ← integral_sub (integrable_exp_source hS hc σ)
      ((integrable_exp_source hS' hc' σ).const_mul ρ)]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)
  unfold chartBounded
  rw [h1, h2, h2]
  ring

theorem chartPrime_sub_mul (N : Finset ℕ) (S S' : ℝ → ℂ) (ρ : ℂ) (y : ℝ) :
    chartPrime N (fun t => S t - ρ * S' t) y = chartPrime N S y - ρ * chartPrime N S' y := by
  unfold chartPrime
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem commutatorIntegral_sub_mul (C : ChartCutoff) {S S' : ℝ → ℂ} (hS : Integrable S)
    (hS' : Integrable S') (ρ : ℂ) (y : ℝ) :
    C.commutatorIntegral (fun t => S t - ρ * S' t) y =
      C.commutatorIntegral S y - ρ * C.commutatorIntegral S' y := by
  have hm : Measurable (fun t : ℝ => logarithmicCutoffKernel C.toFun y t) :=
    (measurable_logarithmicCutoffKernel C.continuous'.measurable).comp
      (measurable_const.prodMk measurable_id)
  have hb (t : ℝ) : ‖logarithmicCutoffKernel C.toFun y t‖ ≤ C.lip / 2 := by
    refine (norm_logarithmicCutoffKernel_le C.lip_nonneg C.lipschitz y t).trans ?_
    have h1 : Real.exp (-|y - t|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
    have h2 : 0 ≤ C.lip / 2 := div_nonneg C.lip_nonneg (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_left h1 h2]
  unfold ChartCutoff.commutatorIntegral
  rw [← integral_const_mul, ← integral_sub (integrable_bounded_mul hS hm hb)
    ((integrable_bounded_mul hS' hm hb).const_mul ρ)]
  exact integral_congr_ae (Eventually.of_forall fun t => by simp only; ring)

/-- **The forcings of two apertures differ only through the increment.** -/
theorem chartForcing_sub_ae (C : ChartCutoff) {a b c : PrecontactAperture} (hab : a.1.1 ≤ b.1.1)
    (hbc : b.1.1 ≤ c.1.1) (hC : ∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0) (z : ℂ) :
    ∀ᵐ y ∂volume, 0 ≤ y →
      ((chartForcing C b z : LogarithmicHalfLineL2) : RealLineL2) y -
          chartPhase z (b.1.1 - a.1.1) *
            ((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) y =
        (C.toFun y : ℂ) * (0 + chartMass * chartIncrement a b z y +
          chartBounded (chartIncrement a b z) y +
          chartPrime (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊) (chartIncrement a b z) y) +
        C.commutatorIntegral (chartIncrement a b z) y := by
  set N := Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊
  set ρ := chartPhase z (b.1.1 - a.1.1)
  have hCb : ∀ x, 2 * b.1.1 ≤ x → C.toFun x = 0 := fun x hx => hC x (by linarith only [hx, hab])
  have hSa := continuous_chartSource a z
  have hSb := continuous_chartSource b z
  have hca := hasCompactSupport_chartSource a z
  have hcb := hasCompactSupport_chartSource b z
  filter_upwards [chartForcing_ae C b hCb z (N := N) (chartPrimeWindow_subset hbc)
      (fun n hn hn' => chartPrimeWindow_beyond hn hn'),
    chartForcing_ae C a hC z (N := N) (chartPrimeWindow_subset (hab.trans hbc))
      (fun n hn hn' => chartPrimeWindow_beyond hn hn')] with y hb ha hy
  rw [hb hy, ha hy]
  have hΔ : chartIncrement a b z = fun t => chartSource b z t - ρ * chartSource a z t := rfl
  rw [hΔ, chartBounded_sub_mul hSb hcb hSa hca ρ y, chartPrime_sub_mul,
    commutatorIntegral_sub_mul C (hSb.integrable_of_hasCompactSupport hcb)
      (hSa.integrable_of_hasCompactSupport hca)]
  have hexp := exp_forcing_shift z y a.1.1 b.1.1
  linear_combination (C.toFun y : ℂ) * hexp

private theorem integrable_kernel_forcing {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {A : ℝ}
    (hb : ∀ᵐ y ∂volume, ‖f y‖ ≤ A) (x : ℝ) :
    Integrable (fun y : ℝ => (v (y - x) : ℂ) * f y) := by
  have hk : Integrable (fun y : ℝ => v (y - x)) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-x)).integrable_comp_of_integrable
        logarithmicCausalKernel_mass_one.1
  exact (Complex.ofRealCLM.integrable_comp hk).mul_bdd hf hb

/-- The backward convolution of a combination of two forcings. -/
theorem logarithmicBackwardConvolution_sub_mul {f g : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) {A B : ℝ} (hfb : ∀ᵐ y ∂volume, ‖f y‖ ≤ A)
    (hgb : ∀ᵐ y ∂volume, ‖g y‖ ≤ B) (ρ : ℂ) (x : ℝ) :
    logarithmicBackwardConvolution (fun y => f y - ρ * g y) x =
      logarithmicBackwardConvolution f x - ρ * logarithmicBackwardConvolution g x := by
  unfold logarithmicBackwardConvolution
  rw [← integral_const_mul, ← integral_sub (integrable_kernel_forcing hf hfb x)
    ((integrable_kernel_forcing hg hgb x).const_mul ρ)]
  exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)

/-- The Green representation of a combination is bounded by the readout of the combination. -/
theorem norm_green_sub_mul_le (f g : LogarithmicHalfLineL2) (ρ : ℂ) {A A' B : ℝ}
    (hfb : ∀ᵐ y ∂volume, ‖(f : RealLineL2) y‖ ≤ A) (hgb : ∀ᵐ y ∂volume, ‖(g : RealLineL2) y‖ ≤ A')
    (hB : ∀ r, 0 ≤ r → ‖logarithmicBackwardConvolution (f : RealLineL2) r -
      ρ * logarithmicBackwardConvolution (g : RealLineL2) r‖ ≤ B) (t : ℝ) :
    ‖logarithmicGreenRepresentative f t - ρ * logarithmicGreenRepresentative g t‖ ≤ B * V t := by
  by_cases ht : t ≤ 0
  · rw [logarithmicGreenRepresentative_of_nonpos f ht, logarithmicGreenRepresentative_of_nonpos g ht]
    have hV : V t = 0 := by
      change ∫ s in Ioc (0 : ℝ) t, v s = 0
      rw [Ioc_eq_empty_of_le ht]
      simp
    simp [hV]
  have hker : Integrable (fun r : ℝ => (v r : ℂ)) :=
    Complex.ofRealCLM.integrable_comp logarithmicCausalKernel_mass_one.1
  have hint (w : LogarithmicHalfLineL2) {C : ℝ} (hw : ∀ᵐ y ∂volume, ‖(w : RealLineL2) y‖ ≤ C) :
      IntegrableOn (fun r : ℝ => (v r : ℂ) *
        logarithmicBackwardConvolution (w : RealLineL2) (t - r)) (Ioc 0 t) :=
    (hker.mul_bdd (((measurable_logarithmicBackwardConvolution
      (Lp.stronglyMeasurable (w : RealLineL2)).measurable).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (Eventually.of_forall fun r => norm_logarithmicBackwardConvolution_le hw _)).integrableOn
  unfold logarithmicGreenRepresentative
  rw [← integral_const_mul, ← integral_sub (hint f hfb) ((hint g hgb).const_mul ρ)]
  calc
    _ ≤ ∫ r in Ioc (0 : ℝ) t, v r * B := by
      apply norm_integral_le_of_norm_le
        (logarithmicCausalKernel_mass_one.1.mul_const B).integrableOn
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun r hr => ?_)
      have heq : (v r : ℂ) * logarithmicBackwardConvolution (f : RealLineL2) (t - r) -
          ρ * ((v r : ℂ) * logarithmicBackwardConvolution (g : RealLineL2) (t - r)) =
          (v r : ℂ) * (logarithmicBackwardConvolution (f : RealLineL2) (t - r) -
            ρ * logarithmicBackwardConvolution (g : RealLineL2) (t - r)) := by ring
      rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hB _ (sub_nonneg.mpr hr.2)) (logarithmicCausalKernel_nonneg _)
    _ = _ := by
      rw [integral_mul_const]
      change V t * B = _
      ring

/-! ### Interior smallness -/

/-- The scale `h^{1/4}`. -/
def chartScale (h : ℝ) : ℝ := Real.sqrt (Real.sqrt h)

theorem chartScale_pos {h : ℝ} (hh : 0 < h) : 0 < chartScale h :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hh)

theorem sqrt_eq_chartScale_sq (h : ℝ) : Real.sqrt h = chartScale h ^ 2 :=
  (Real.sq_sqrt (Real.sqrt_nonneg h)).symm

theorem chartScale_le_one {h : ℝ} (h1 : h ≤ 1) : chartScale h ≤ 1 := by
  have h2 : Real.sqrt h ≤ 1 := Real.sqrt_le_one.mpr h1
  exact Real.sqrt_le_one.mpr h2

/-- **Interior smallness of the increment.** Away from the far endpoint the increment is at most
`C₇ V(3η) V(h^{1/4}) + C₈ h^{1/4}`, with `C₇` independent of `η`. -/
theorem exists_interior_bound (a₁ a₂ : PrecontactAperture) (z : ℂ) :
    ∃ C₇ : ℝ, 0 ≤ C₇ ∧ ∀ η : ℝ, 0 < η → 3 * η ≤ a₁.1.1 →
      ∃ C₈ h₀ : ℝ, 0 ≤ C₈ ∧ 0 < h₀ ∧ ∀ a b : PrecontactAperture,
        a₁.1.1 ≤ a.1.1 → a.1.1 ≤ b.1.1 → b.1.1 ≤ a₂.1.1 → 0 < b.1.1 - a.1.1 → b.1.1 - a.1.1 < h₀ →
        ∀ t, t ≤ 2 * a.1.1 - 2 * η → ‖chartIncrement a b z t‖ ≤
          C₇ * V (3 * η) * V (chartScale (b.1.1 - a.1.1)) + C₈ * chartScale (b.1.1 - a.1.1) := by
  obtain ⟨Az, hAz0, hAz⟩ := exists_uniform_endpoint_data a₁ a₂ z
  obtain ⟨An, hAn0, hAn⟩ := exists_uniform_endpoint_data a₁ a₂ (-z)
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_chartIncrement_mass_bound a₁ a₂ z
  let A := Az + An
  have hA0 : 0 ≤ A := add_nonneg hAz0 hAn0
  let P := Real.exp (a₂.1.1 * |z.im|)
  have hP : 0 < P := Real.exp_pos _
  let N := Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊
  let K := chartSupConstant N
  have hK : 0 ≤ K := chartSupConstant_nonneg N
  let R := 2 * a₂.1.1
  have hR : 0 ≤ R := mul_nonneg (by norm_num) a₂.1.2.le
  let B := chartBoundedConstant R R
  have hB : 0 ≤ B := chartBoundedConstant_nonneg R R
  refine ⟨2 * K * ((1 + P) * A), by positivity, fun η hη h3η => ?_⟩
  let Cη := B * C₂ + K * C₂ + R * (B * C₂) + C₂ / (2 * η)
  have hCη : 0 ≤ Cη := by dsimp only [Cη]; positivity
  -- A threshold below which the prime terms are absorbed.
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), K * V (chartScale h) < 1 / 2 := by
    have ht : Tendsto chartScale (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous chartScale := Real.continuous_sqrt.comp Real.continuous_sqrt
        have h0 := hc.tendsto 0
        have hz : chartScale 0 = 0 := by simp [chartScale]
        rw [hz] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        exact chartScale_pos hh
    have hl := (tendsto_logarithmicRenewalMass_zero.comp ht).const_mul K
    rw [mul_zero] at hl
    exact hl.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (zero_lt_one' ℝ)).mp hsmall
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨2 * Cη, min (min u 1) (η / 2), by positivity, by positivity,
    fun a b ha₁ hab hb₂ hh hh₀ t ht => ?_⟩
  set h := b.1.1 - a.1.1 with hhdef
  have hh₁ : h < 1 := hh₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hhη : h ≤ η / 2 := hh₀.le.trans (min_le_right _ _)
  have hhu : h < u := hh₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have habso : K * V (chartScale h) < 1 / 2 := hsub ⟨hh, hhu⟩
  let q := chartScale h
  have hq : 0 < q := chartScale_pos hh
  have hq1 : q ≤ 1 := chartScale_le_one hh₁.le
  have hVq := logarithmicRenewalMass_le_one q
  have hVq0 := logarithmicRenewalMass_nonneg q
  have ha₁p := a₁.1.2
  have haa₂ : a.1.1 ≤ a₂.1.1 := hab.trans hb₂
  have hmass : ∫ s, ‖chartIncrement a b z s‖ ≤ C₂ * q ^ 2 := by
    rw [← sqrt_eq_chartScale_sq h]
    exact hC₂ a b ha₁ hab hb₂ hh
  have hc : 0 < 2 * a.1.1 - 2 * η := by linarith only [h3η, ha₁, hη]
  let c := 2 * a.1.1 - 2 * η
  have hcd : c < 2 * a.1.1 - η := by dsimp only [c]; linarith only [hη]
  let C := ChartCutoff.linear c (2 * a.1.1 - η) hcd
  have hlip : C.lip = 1 / η := by
    change 1 / ((2 * a.1.1 - η) - c) = 1 / η
    congr 1
    dsimp only [c]
    ring
  have hCa : ∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0 := fun x hx =>
    ChartCutoff.linear_eq_zero hcd (by linarith only [hx, hη])
  have hCb : ∀ x, 2 * b.1.1 ≤ x → C.toFun x = 0 := fun x hx =>
    hCa x (by linarith only [hx, hab])
  have hCR : ∀ x, R ≤ x → C.toFun x = 0 := fun x hx => hCa x (by
    dsimp only [R] at hx
    linarith only [hx, haa₂])
  have hρnorm : ‖chartPhase z h‖ ≤ P := by
    rw [norm_chartPhase]
    apply Real.exp_le_exp.mpr
    have h1 : h ≤ a₂.1.1 := by
      have := a.1.2
      rw [hhdef]
      linarith only [hb₂, this]
    calc
      h * z.im ≤ |h * z.im| := le_abs_self _
      _ = h * |z.im| := by rw [abs_mul, abs_of_pos hh]
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hAzle : Az ≤ A := by dsimp only [A]; linarith only [hAn0]
  have hAnle : An ≤ A := by dsimp only [A]; linarith only [hAz0]
  -- The tail near the far endpoint.
  let T := (1 + P) * A * V (3 * η)
  have hV3 := logarithmicRenewalMass_nonneg (3 * η)
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hmono := monotone_logarithmicRenewalMass
  have htail (x : ℝ) (hx : c ≤ x) : ‖chartIncrement a b z x‖ ≤ T := by
    have hb' : ‖chartSource b z x‖ ≤ A * V (3 * η) := by
      rw [chartSource_reflect]
      by_cases hx2 : 2 * b.1.1 - x ≤ 0
      · rw [chartSource_eq_zero b (-z) (Or.inl hx2), norm_zero]
        positivity
      have hle : 2 * b.1.1 - x ≤ 3 * η := by
        dsimp only [c] at hx
        linarith only [hx, hhη, hhdef]
      have hleb : 2 * b.1.1 - x ≤ b.1.1 := by linarith only [hle, h3η, ha₁, hab]
      have hd := ((hAn b (ha₁.trans hab) hb₂).2.2.2 _ hleb).1
      calc
        _ ≤ An * V (2 * b.1.1 - x) := hd
        _ ≤ A * V (3 * η) := mul_le_mul hAnle (hmono hle)
          (logarithmicRenewalMass_nonneg _) hA0
    have ha' : ‖chartSource a z x‖ ≤ A * V (3 * η) := by
      rw [chartSource_reflect]
      by_cases hx2 : 2 * a.1.1 - x ≤ 0
      · rw [chartSource_eq_zero a (-z) (Or.inl hx2), norm_zero]
        positivity
      have hle : 2 * a.1.1 - x ≤ 3 * η := by
        dsimp only [c] at hx
        linarith only [hx, hη]
      have hleb : 2 * a.1.1 - x ≤ a.1.1 := by linarith only [hle, h3η, ha₁]
      have hd := ((hAn a ha₁ haa₂).2.2.2 _ hleb).1
      calc
        _ ≤ An * V (2 * a.1.1 - x) := hd
        _ ≤ A * V (3 * η) := mul_le_mul hAnle (hmono hle)
          (logarithmicRenewalMass_nonneg _) hA0
    rw [chartIncrement]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have hp := mul_le_mul hρnorm ha' (norm_nonneg _) hP.le
    dsimp only [T]
    nlinarith only [hb', hp]
  -- The clamped supremum over the interior.
  have hcΔ := continuous_chartIncrement a b z
  have hsΔ := hasCompactSupport_chartIncrement hab z
  obtain ⟨Mb, hMb⟩ := hsΔ.exists_bound_of_continuous hcΔ
  let f : ℝ → ℝ := fun s => ‖chartIncrement a b z (min s c)‖
  have hfb : BddAbove (range f) := ⟨Mb, by rintro _ ⟨s, rfl⟩; exact hMb _⟩
  let D := ⨆ s, f s
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (le_ciSup hfb 0)
  have hDle (s : ℝ) (hs : s ≤ c) : ‖chartIncrement a b z s‖ ≤ D := by
    have := le_ciSup hfb s
    simpa only [f, min_eq_left hs] using this
  have hall (s : ℝ) : ‖chartIncrement a b z s‖ ≤ D + T := by
    rcases le_total s c with hs | hs
    · linarith only [hDle s hs, hT0]
    · linarith only [htail s hs, hD0]
  -- The readout of the difference.
  obtain ⟨A₁, hA₁, hF₁⟩ := chartForcing_bounded C b z
  obtain ⟨A₂, hA₂, hF₂⟩ := chartForcing_bounded C a z
  let g : ℝ → ℂ := fun y => ((chartForcing C b z : LogarithmicHalfLineL2) : RealLineL2) y -
    chartPhase z h * ((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) y
  have hread (r : ℝ) : ‖logarithmicBackwardConvolution g r‖ ≤
      (0 + K * (D + T) + B * (C₂ * q ^ 2)) * V q +
        (R * 0 + K * (C₂ * q ^ 2) + R * (B * (C₂ * q ^ 2))) / q + C.lip / 2 * (C₂ * q ^ 2) := by
    refine norm_readout_le_of_chart_form (f := g) (S := chartIncrement a b z) (E := fun _ => 0)
      hcΔ hsΔ C N (T := R) hR hCR
      (fun s hs => chartIncrement_eq_zero hab z (Or.inl hs))
      (fun s hs => chartIncrement_eq_zero hab z (Or.inr (by
        dsimp only [R] at hs
        linarith only [hs, hb₂]))) le_rfl (fun _ _ => by simp) hall hmass hq ?_ ?_ r
    · filter_upwards [chartForcing_negative C b z, chartForcing_negative C a z] with y h1 h2 hy
      simp only [g]
      rw [h1 hy, h2 hy, mul_zero, sub_zero]
    · exact chartForcing_sub_ae C hab hb₂ hCa z
  have hbound : (0 + K * (D + T) + B * (C₂ * q ^ 2)) * V q +
      (R * 0 + K * (C₂ * q ^ 2) + R * (B * (C₂ * q ^ 2))) / q + C.lip / 2 * (C₂ * q ^ 2) ≤
      K * (D + T) * V q + Cη * q := by
    rw [hlip]
    have hq2 : q ^ 2 ≤ q := by nlinarith only [hq, hq1]
    have h1 : B * (C₂ * q ^ 2) * V q ≤ B * C₂ * q := by
      have hmul : 0 ≤ B * C₂ := by positivity
      calc
        _ = (B * C₂) * (q ^ 2 * V q) := by ring
        _ ≤ (B * C₂) * q := mul_le_mul_of_nonneg_left
          (by nlinarith only [hq2, hVq, hVq0, sq_nonneg q]) hmul
    have h2 : (R * 0 + K * (C₂ * q ^ 2) + R * (B * (C₂ * q ^ 2))) / q =
        (K * C₂ + R * (B * C₂)) * q := by
      field_simp
      ring
    have h3 : 1 / η / 2 * (C₂ * q ^ 2) ≤ C₂ / (2 * η) * q := by
      have heq : 1 / η / 2 * (C₂ * q ^ 2) = C₂ / (2 * η) * q ^ 2 := by
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_left hq2 (by positivity)
    rw [h2]
    dsimp only [Cη]
    nlinarith only [h1, h3]
  have hgF₁ : AEStronglyMeasurable
      (((chartForcing C b z : LogarithmicHalfLineL2) : RealLineL2) : ℝ → ℂ) volume :=
    (Lp.stronglyMeasurable _).aestronglyMeasurable
  have hgF₂ : AEStronglyMeasurable
      (((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) : ℝ → ℂ) volume :=
    (Lp.stronglyMeasurable _).aestronglyMeasurable
  let BB := K * (D + T) * V q + Cη * q
  have hBB0 : 0 ≤ BB := by dsimp only [BB]; positivity
  have hgreen (s : ℝ) : ‖logarithmicGreenRepresentative (chartForcing C b z) s -
      chartPhase z h * logarithmicGreenRepresentative (chartForcing C a z) s‖ ≤ BB * V s :=
    norm_green_sub_mul_le _ _ _ hF₁ hF₂ (fun r _ => by
      rw [← logarithmicBackwardConvolution_sub_mul hgF₁ hgF₂ hF₁ hF₂]
      exact (hread r).trans hbound) s
  have hΔs (s : ℝ) (hs : s ≤ c) : ‖chartIncrement a b z s‖ ≤ BB := by
    have hG1 := logarithmicGreenRepresentative_chartForcing C b hCb z s
    have hG2 := logarithmicGreenRepresentative_chartForcing C a hCa z s
    rw [ChartCutoff.linear_eq_one hcd hs, Complex.ofReal_one, one_mul] at hG1 hG2
    have h := hgreen s
    rw [hG1, hG2] at h
    have hV := logarithmicRenewalMass_le_one s
    calc
      _ ≤ BB * V s := h
      _ ≤ BB := mul_le_of_le_one_right hBB0 hV
  have hDBB : D ≤ BB := ciSup_le fun s => hΔs _ (min_le_right s c)
  -- Absorption.
  have hfinal : D ≤ 2 * K * T * V q + 2 * Cη * q := by
    have h1 : K * D * V q ≤ D / 2 := by nlinarith only [habso, hD0]
    dsimp only [BB] at hDBB
    nlinarith only [hDBB, h1]
  refine (hDle t ht).trans (hfinal.trans_eq ?_)
  dsimp only [T]
  ring


/-! ### The trace increment -/

/-- The readout at the endpoint, with a majorant controlled only near the endpoint. -/
theorem norm_integral_kernel_le_of_near {r : ℝ → ℂ} {g : ℝ → ℝ} {A B ρ : ℝ}
    (hg : Integrable g) (hg0 : ∀ y, 0 ≤ g y) (hA : 0 ≤ A) (hρ : 0 < ρ)
    (hnear : ∀ y ∈ Ioc (0 : ℝ) ρ, g y ≤ A) (hb : ∀ᵐ y ∂volume, 0 < y → ‖r y‖ ≤ g y + B) :
    ‖∫ y : ℝ, (v y : ℂ) * r y‖ ≤ A * V ρ + (∫ y, g y) / ρ + B := by
  let G : ℝ → ℝ := (Ioc (0 : ℝ) ρ).indicator (fun t => v t * A)
  have hGi : Integrable G :=
    (logarithmicCausalKernel_mass_one.1.mul_const A).integrableOn.integrable_indicator
      measurableSet_Ioc
  have hG : ∫ t, G t = A * V ρ := by
    rw [integral_indicator measurableSet_Ioc, integral_mul_const]
    change V ρ * A = _
    ring
  have hmaj : Integrable (fun y => G y + g y / ρ + v y * B) :=
    (hGi.add (hg.div_const ρ)).add (logarithmicCausalKernel_mass_one.1.mul_const B)
  calc
    _ ≤ ∫ y, (G y + g y / ρ + v y * B) := by
      apply norm_integral_le_of_norm_le hmaj
      filter_upwards [hb] with y hy
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _)]
      have hG0 : 0 ≤ G y := indicator_nonneg
        (fun t _ => mul_nonneg (logarithmicCausalKernel_nonneg t) hA) _
      have hf0 : 0 ≤ g y / ρ := div_nonneg (hg0 y) hρ.le
      have hv0 := logarithmicCausalKernel_nonneg y
      by_cases hy0 : y ≤ 0
      · rw [logarithmicCausalKernel_of_nonpos hy0, zero_mul, zero_mul]
        linarith only [hG0, hf0]
      push Not at hy0
      have hbd := mul_le_mul_of_nonneg_left (hy hy0) hv0
      by_cases hyρ : y ≤ ρ
      · have hG1 : G y = v y * A := indicator_of_mem (show y ∈ Ioc (0 : ℝ) ρ from ⟨hy0, hyρ⟩) _
        have hn := mul_le_mul_of_nonneg_left (hnear y ⟨hy0, hyρ⟩) hv0
        rw [hG1]
        nlinarith only [hbd, hn, hf0]
      · push Not at hyρ
        have hvle : v y ≤ 1 / ρ :=
          (antitoneOn_logarithmicCausalKernel hρ hy0 hyρ.le).trans
            (logarithmicCausalKernel_le_inv hρ)
        have h2 : v y * g y ≤ g y / ρ := by
          calc
            _ ≤ 1 / ρ * g y := mul_le_mul_of_nonneg_right hvle (hg0 y)
            _ = _ := by ring
        nlinarith only [hbd, h2, hG0]
    _ = _ := by
      have h1 : ∫ y, (G y + g y / ρ + v y * B) = (∫ y, (G y + g y / ρ)) + ∫ y, v y * B :=
        integral_add (hGi.add (hg.div_const ρ)) (logarithmicCausalKernel_mass_one.1.mul_const B)
      have h2 : ∫ y, (G y + g y / ρ) = (∫ y, G y) + ∫ y, g y / ρ :=
        integral_add hGi (hg.div_const ρ)
      rw [h1, h2, hG, integral_div, integral_mul_const, logarithmicCausalKernel_mass_one.2, one_mul]

/-- The mass of the prime powers meeting the far endpoint of the old window. -/
def chartKickMass (N : Finset ℕ) (a : ℝ) : ℝ :=
  ∑ m ∈ N.filter (fun m : ℕ => Real.log m = 2 * a), criticalMellinAtomWeight m

theorem chartKickMass_nonneg (N : Finset ℕ) (a : ℝ) : 0 ≤ chartKickMass N a :=
  Finset.sum_nonneg fun n _ => criticalMellinAtomWeight_nonneg_chart n

theorem chartKickMass_le (N : Finset ℕ) (a : ℝ) : chartKickMass N a ≤ chartPrimeMass N :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun n _ _ => criticalMellinAtomWeight_nonneg_chart n

/-- **The exact form of the trace increment.** The trace moves by the kick of the prime powers at the
far endpoint, up to the interior size of the increment. -/
theorem exists_trace_increment_bound (a₁ a₂ : PrecontactAperture) (z : ℂ) :
    ∃ C₉ A : ℝ, 0 ≤ C₉ ∧ 0 ≤ A ∧ ∀ a b : PrecontactAperture,
      a₁.1.1 ≤ a.1.1 → a.1.1 ≤ b.1.1 → b.1.1 ≤ a₂.1.1 → 0 < b.1.1 - a.1.1 → b.1.1 - a.1.1 < 1 →
      4 * (b.1.1 - a.1.1) ≤ a₁.1.1 → ∀ η D : ℝ, 0 < η → 3 * η ≤ a₁.1.1 →
      chartScale (b.1.1 - a.1.1) ≤ 2 * η → chartScale (b.1.1 - a.1.1) < Real.log 2 → 0 ≤ D →
      (∀ t, t ≤ 2 * a.1.1 - 2 * η → ‖chartIncrement a b z t‖ ≤ D) →
      (∀ m ∈ Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊,
        Real.log m ≤ 2 * a.1.1 - 4 * η ∨ 2 * b.1.1 ≤ Real.log m ∨ Real.log m = 2 * a.1.1) →
      ‖evalVectorLeftTrace b z - chartPhase z (b.1.1 - a.1.1) * evalVectorLeftTrace a z -
          (chartKickMass (Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊) a.1.1 : ℂ) *
            evalVectorRightTrace b z *
            (logarithmicRenewalCoupling (2 * (b.1.1 - a.1.1)) : ℂ)‖ ≤
        chartSupConstant (Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊) * D *
            V (chartScale (b.1.1 - a.1.1)) + C₉ * chartScale (b.1.1 - a.1.1) +
          chartKickMass (Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊) a.1.1 *
            (2 * A * V (2 * (b.1.1 - a.1.1)) *
              logarithmicRenewalCoupling (2 * (b.1.1 - a.1.1))) := by
  obtain ⟨An, hAn0, hAn⟩ := exists_uniform_endpoint_data a₁ a₂ (-z)
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_chartIncrement_mass_bound a₁ a₂ z
  set N := Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊ with hNdef
  set K := chartSupConstant N with hKdef
  have hK : 0 ≤ K := chartSupConstant_nonneg N
  have ha₁p := a₁.1.2
  let B := chartBoundedConstant a₁.1.1 (2 * a₂.1.1)
  have hB : 0 ≤ B := chartBoundedConstant_nonneg _ _
  refine ⟨B * C₂ + a₁.1.1 * (B * C₂) + K * C₂ + C₂ / a₁.1.1, An, by positivity, hAn0,
    fun a b ha₁ hab hb₂ hh hh1 hh4 η D hη h3η hqη hqlog hD0 hDle hpart => ?_⟩
  set h := b.1.1 - a.1.1 with hhdef
  set q := chartScale h with hqdef
  have hq : 0 < q := chartScale_pos hh
  have hq1 : q ≤ 1 := chartScale_le_one hh1.le
  have hVq := logarithmicRenewalMass_le_one q
  have hVq0 := logarithmicRenewalMass_nonneg q
  set ρ := chartPhase z h with hρdef
  set W := chartKickMass N a.1.1 with hWdef
  have hW0 : 0 ≤ W := chartKickMass_nonneg N _
  set Δ := chartIncrement a b z with hΔdef
  have hcΔ : Continuous Δ := continuous_chartIncrement a b z
  have hsΔ : HasCompactSupport Δ := hasCompactSupport_chartIncrement hab z
  have hΔ0 (t : ℝ) (ht : t ≤ 0) : Δ t = 0 := chartIncrement_eq_zero hab z (Or.inl ht)
  have hΔT (t : ℝ) (ht : 2 * b.1.1 ≤ t) : Δ t = 0 := chartIncrement_eq_zero hab z (Or.inr ht)
  have hmass : ∫ s, ‖Δ s‖ ≤ C₂ * q ^ 2 := by
    rw [hqdef, ← sqrt_eq_chartScale_sq h]
    exact hC₂ a b ha₁ hab hb₂ hh
  have hL0 : 0 ≤ C₂ * q ^ 2 := by positivity
  have hcd : a₁.1.1 / 2 < a₁.1.1 := by linarith only [ha₁p]
  let C := ChartCutoff.linear (a₁.1.1 / 2) a₁.1.1 hcd
  have hlip : C.lip / 2 = 1 / a₁.1.1 := by
    change 1 / (a₁.1.1 - a₁.1.1 / 2) / 2 = 1 / a₁.1.1
    field_simp
    ring
  have hCa₁ : ∀ x, a₁.1.1 ≤ x → C.toFun x = 0 := fun x hx => ChartCutoff.linear_eq_zero hcd hx
  have hCa : ∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0 := fun x hx =>
    hCa₁ x (by linarith only [hx, ha₁, ha₁p])
  have hCb : ∀ x, 2 * b.1.1 ≤ x → C.toFun x = 0 := fun x hx =>
    hCa x (by linarith only [hx, hab])
  have hCone : ∀ x, x ≤ a₁.1.1 / 2 → C.toFun x = 1 := fun x hx => ChartCutoff.linear_eq_one hcd hx
  have htb := logarithmicBackwardConvolution_chartForcing_zero C b hCb
    (show 0 < a₁.1.1 / 2 by linarith only [ha₁p]) hCone z
  have hta := logarithmicBackwardConvolution_chartForcing_zero C a hCa
    (show 0 < a₁.1.1 / 2 by linarith only [ha₁p]) hCone z
  obtain ⟨A₁, hA₁, hF₁⟩ := chartForcing_bounded C b z
  obtain ⟨A₂, hA₂, hF₂⟩ := chartForcing_bounded C a z
  have hgF₁ : AEStronglyMeasurable
      (((chartForcing C b z : LogarithmicHalfLineL2) : RealLineL2) : ℝ → ℂ) volume :=
    (Lp.stronglyMeasurable _).aestronglyMeasurable
  have hgF₂ : AEStronglyMeasurable
      (((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) : ℝ → ℂ) volume :=
    (Lp.stronglyMeasurable _).aestronglyMeasurable
  let f : ℝ → ℂ := fun y => ((chartForcing C b z : LogarithmicHalfLineL2) : RealLineL2) y -
    ρ * ((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) y
  have hdiff : evalVectorLeftTrace b z - ρ * evalVectorLeftTrace a z =
      ∫ y : ℝ, (v y : ℂ) * f y := by
    rw [← htb, ← hta, ← logarithmicBackwardConvolution_sub_mul hgF₁ hgF₂ hF₁ hF₂]
    simp only [logarithmicBackwardConvolution, sub_zero]
    rfl
  -- The main term.
  obtain ⟨Mb, hMb⟩ := hsΔ.exists_bound_of_continuous hcΔ
  have hker : Integrable (fun r : ℝ => (v r : ℂ)) :=
    Complex.ofRealCLM.integrable_comp logarithmicCausalKernel_mass_one.1
  let main : ℝ → ℂ := fun y => (C.toFun y : ℂ) * Δ (y + 2 * a.1.1)
  have hmainc : Continuous main :=
    (Complex.continuous_ofReal.comp C.continuous').mul (hcΔ.comp (by fun_prop))
  have hmainb (y : ℝ) : ‖main y‖ ≤ Mb := by
    change ‖(C.toFun y : ℂ) * Δ (y + 2 * a.1.1)‖ ≤ Mb
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hMb (y + 2 * a.1.1)
    have h2 := mul_le_mul (C.abs_le y) h1 (norm_nonneg _) zero_le_one
    rwa [one_mul] at h2
  have hmaini : Integrable (fun y : ℝ => (v y : ℂ) * main y) :=
    hker.mul_bdd hmainc.aestronglyMeasurable (Eventually.of_forall hmainb)
  have hfi : Integrable (fun y : ℝ => (v y : ℂ) * f y) := by
    have h1 := integrable_kernel_forcing hgF₁ hF₁ 0
    have h2 := (integrable_kernel_forcing hgF₂ hF₂ 0).const_mul ρ
    simp only [sub_zero] at h1 h2
    exact (h1.sub h2).congr (Eventually.of_forall fun y => by
      simp only [Pi.sub_apply, f]
      ring)
  let rest : ℝ → ℂ := fun y => f y - (W : ℂ) * main y
  have hsplit : (∫ y : ℝ, (v y : ℂ) * f y) =
      (W : ℂ) * (∫ y : ℝ, (v y : ℂ) * main y) + ∫ y : ℝ, (v y : ℂ) * rest y := by
    rw [← integral_const_mul, ← integral_add (hmaini.const_mul _) (hfi.sub (hmaini.const_mul _) |>.congr
      (Eventually.of_forall fun y => by
        simp only [Pi.sub_apply, rest]
        ring))]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      simp only [rest]
      ring)
  -- The main term is the coupled readout of the far edge.
  set ε := 2 * h with hεdef
  have hε : 0 < ε := by positivity
  have hεa₁ : ε ≤ a₁.1.1 / 2 := by rw [hεdef]; linarith only [hh4]
  let G := chartSource b (-z)
  have hmainEq : (∫ y : ℝ, (v y : ℂ) * main y) = ∫ y in Ioc (0 : ℝ) ε, (v y : ℂ) * G (ε - y) := by
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    refine Eventually.of_forall fun y => ?_
    change (v y : ℂ) * main y = (Ioc (0 : ℝ) ε).indicator (fun y => (v y : ℂ) * G (ε - y)) y
    by_cases hy0 : y ≤ 0
    · rw [logarithmicCausalKernel_of_nonpos hy0, indicator_of_notMem
        (fun hm : y ∈ Ioc (0 : ℝ) ε => absurd hm.1 (not_lt.mpr hy0))]
      simp
    push Not at hy0
    by_cases hyε : y ≤ ε
    · rw [indicator_of_mem (show y ∈ Ioc (0 : ℝ) ε from ⟨hy0, hyε⟩)]
      congr 1
      change (C.toFun y : ℂ) * chartIncrement a b z (y + 2 * a.1.1) = _
      rw [hCone y (hyε.trans hεa₁), Complex.ofReal_one, one_mul, chartIncrement,
        chartSource_eq_zero a z (Or.inr (by linarith only [hy0])), mul_zero, sub_zero,
        chartSource_reflect]
      change _ = chartSource b (-z) (ε - y)
      congr 1
      rw [hεdef, hhdef]
      ring
    · push Not at hyε
      rw [indicator_of_notMem (fun hm : y ∈ Ioc (0 : ℝ) ε => absurd hm.2 (not_le.mpr hyε))]
      change (v y : ℂ) * ((C.toFun y : ℂ) * Δ (y + 2 * a.1.1)) = 0
      rw [hΔT _ (by rw [hεdef, hhdef] at hyε; linarith only [hyε]), mul_zero, mul_zero]
  have hGm : Measurable G := (continuous_chartSource b (-z)).measurable
  have hGb : ∃ c, ∀ t, ‖G t‖ ≤ c :=
    (hasCompactSupport_chartSource b (-z)).exists_bound_of_continuous
      (continuous_chartSource b (-z))
  have hedge : ∀ t ∈ Icc (0 : ℝ) ε, ‖G t - evalVectorRightTrace b z * (V t : ℂ)‖ ≤
      (2 * An) * V t ^ 2 := by
    intro t ht
    have htb' : t ≤ b.1.1 := by linarith only [ht.2, hεa₁, ha₁, hab, ha₁p]
    rw [evalVectorRightTrace_eq_leftTrace_neg]
    exact ((hAn b (ha₁.trans hab) hb₂).2.2.2 t htb').2
  have hcoupled := norm_integral_kernel_mul_sub_coupling_le (by positivity) hGm hGb hedge
  -- The remainder.
  let N₁ := N.filter (fun m : ℕ => ¬ Real.log m = 2 * a.1.1)
  let m₁ : ℝ → ℝ := fun y => ‖chartMass‖ * ‖Δ y‖ +
    ∑ m ∈ N₁, criticalMellinAtomWeight m * ‖Δ (y + Real.log m)‖ +
    ∑ m ∈ N, criticalMellinAtomWeight m * ‖Δ (y - Real.log m)‖
  have hm₁c : Continuous m₁ := by
    dsimp only [m₁]
    fun_prop
  have hwnn (m : ℕ) := criticalMellinAtomWeight_nonneg_chart m
  have hm₁0 (y : ℝ) : 0 ≤ m₁ y := by
    dsimp only [m₁]
    have h1 : 0 ≤ ∑ m ∈ N₁, criticalMellinAtomWeight m * ‖Δ (y + Real.log m)‖ :=
      Finset.sum_nonneg fun m _ => mul_nonneg (hwnn m) (norm_nonneg _)
    have h2 : 0 ≤ ∑ m ∈ N, criticalMellinAtomWeight m * ‖Δ (y - Real.log m)‖ :=
      Finset.sum_nonneg fun m _ => mul_nonneg (hwnn m) (norm_nonneg _)
    have h3 := mul_nonneg (norm_nonneg chartMass) (norm_nonneg (Δ y))
    linarith only [h1, h2, h3]
  have hm₁maj (y : ℝ) : m₁ y ≤ chartMajorant N Δ y := by
    have hsub : ∑ m ∈ N₁, criticalMellinAtomWeight m * ‖Δ (y + Real.log m)‖ ≤
        ∑ m ∈ N, criticalMellinAtomWeight m * ‖Δ (y + Real.log m)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun m _ _ => mul_nonneg (hwnn m) (norm_nonneg _)
    have heq : ∑ m ∈ N, criticalMellinAtomWeight m *
        (‖Δ (y + Real.log m)‖ + ‖Δ (y - Real.log m)‖) =
        ∑ m ∈ N, criticalMellinAtomWeight m * ‖Δ (y + Real.log m)‖ +
          ∑ m ∈ N, criticalMellinAtomWeight m * ‖Δ (y - Real.log m)‖ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    dsimp only [m₁, chartMajorant]
    rw [heq]
    linarith only [hsub]
  let L := C₂ * q ^ 2
  let g : ℝ → ℝ := (Ico (0 : ℝ) a₁.1.1).indicator (fun y => B * L + m₁ y)
  have hgc : Continuous (fun y => B * L + m₁ y) := continuous_const.add hm₁c
  have hgi : Integrable g :=
    ((hgc.integrableOn_Icc (a := 0) (b := a₁.1.1)).mono_set Ico_subset_Icc_self).integrable_indicator
      measurableSet_Ico
  have hg0 (y : ℝ) : 0 ≤ g y :=
    indicator_nonneg (fun y _ => add_nonneg (mul_nonneg hB hL0) (hm₁0 y)) y
  have hgint : (∫ y, g y) ≤ a₁.1.1 * (B * L) + K * L := by
    rw [integral_indicator measurableSet_Ico]
    have hconstI : IntegrableOn (fun _ : ℝ => B * L) (Ico (0 : ℝ) a₁.1.1) :=
      (continuous_const.integrableOn_Icc (a := 0) (b := a₁.1.1)).mono_set Ico_subset_Icc_self
    have hm₁I : IntegrableOn m₁ (Ico (0 : ℝ) a₁.1.1) :=
      (hm₁c.integrableOn_Icc (a := 0) (b := a₁.1.1)).mono_set Ico_subset_Icc_self
    have hmajI : IntegrableOn (chartMajorant N Δ) (Ico (0 : ℝ) a₁.1.1) :=
      ((continuous_chartMajorant N hcΔ).integrableOn_Icc (a := 0) (b := a₁.1.1)).mono_set
        Ico_subset_Icc_self
    rw [integral_add hconstI hm₁I, setIntegral_const, Real.volume_real_Ico_of_le ha₁p.le,
      smul_eq_mul, sub_zero]
    have h1 : (∫ y in Ico (0 : ℝ) a₁.1.1, m₁ y) ≤ ∫ y in Ico (0 : ℝ) a₁.1.1, chartMajorant N Δ y :=
      setIntegral_mono hm₁I hmajI hm₁maj
    have h2 := integral_chartMajorant_le N (hcΔ.integrable_of_hasCompactSupport hsΔ) ha₁p.le hcΔ
    have h3 := mul_le_mul_of_nonneg_left hmass hK
    linarith only [h1, h2, h3]
  -- Near the endpoint the remaining terms see only the interior of the increment.
  have hnear : ∀ y ∈ Ioc (0 : ℝ) q, g y ≤ B * L + K * D := by
    intro y hy
    by_cases hya : y ∈ Ico (0 : ℝ) a₁.1.1
    swap
    · change (Ico (0 : ℝ) a₁.1.1).indicator _ y ≤ _
      rw [indicator_of_notMem hya]
      positivity
    change (Ico (0 : ℝ) a₁.1.1).indicator _ y ≤ _
    rw [indicator_of_mem hya]
    have h1 : ‖Δ y‖ ≤ D := hDle y (by
      have := hy.2
      linarith only [this, hqη, h3η, ha₁, hη])
    have h2 : ∑ m ∈ N₁, criticalMellinAtomWeight m * ‖Δ (y + Real.log m)‖ ≤ chartPrimeMass N * D := by
      calc
        _ ≤ ∑ m ∈ N₁, criticalMellinAtomWeight m * D := by
          refine Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left ?_ (hwnn m)
          obtain ⟨hmN, hne⟩ := Finset.mem_filter.mp hm
          rcases hpart m hmN with h3 | h3 | h3
          · exact hDle _ (by
              have := hy.2
              linarith only [this, hqη, h3])
          · rw [hΔT _ (by linarith only [h3, hy.1]), norm_zero]
            exact hD0
          · exact absurd h3 hne
        _ ≤ ∑ m ∈ N, criticalMellinAtomWeight m * D :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun m _ _ => mul_nonneg (hwnn m) hD0
        _ = _ := by rw [chartPrimeMass, Finset.sum_mul]
    have h3 : ∑ m ∈ N, criticalMellinAtomWeight m * ‖Δ (y - Real.log m)‖ = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      have hlog : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm2
      rw [hΔ0 _ (by linarith only [hy.2, hqlog, hlog]), norm_zero, mul_zero]
    have hPM := chartPrimeMass_nonneg N
    have hmκ := mul_le_mul_of_nonneg_left h1 (norm_nonneg chartMass)
    dsimp only [m₁]
    rw [h3, hKdef, chartSupConstant]
    nlinarith only [h2, hmκ, hPM, hD0]
  have hcommb (y : ℝ) : ‖C.commutatorIntegral Δ y‖ ≤ 1 / a₁.1.1 * L := by
    have hi := C.norm_commutatorIntegral_le (hcΔ.integrable_of_hasCompactSupport hsΔ) y
    rw [hlip] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
  have hrest : ‖∫ y : ℝ, (v y : ℂ) * rest y‖ ≤
      (B * L + K * D) * V q + (∫ y, g y) / q + 1 / a₁.1.1 * L := by
    refine norm_integral_kernel_le_of_near hgi hg0 (by positivity) hq hnear ?_
    filter_upwards [chartForcing_sub_ae C hab hb₂ hCa z] with y hy hy0
    have hfy := hy hy0.le
    have hrestEq : rest y = (C.toFun y : ℂ) * (chartMass * Δ y + chartBounded Δ y +
        (∑ m ∈ N₁, (criticalMellinAtomWeight m : ℂ) * Δ (y + Real.log m) +
          ∑ m ∈ N, (criticalMellinAtomWeight m : ℂ) * Δ (y - Real.log m))) +
        C.commutatorIntegral Δ y := by
      change f y - (W : ℂ) * ((C.toFun y : ℂ) * Δ (y + 2 * a.1.1)) = _
      rw [show f y = _ from hfy]
      have hprime : chartPrime N Δ y = (W : ℂ) * Δ (y + 2 * a.1.1) +
          (∑ m ∈ N₁, (criticalMellinAtomWeight m : ℂ) * Δ (y + Real.log m) +
            ∑ m ∈ N, (criticalMellinAtomWeight m : ℂ) * Δ (y - Real.log m)) := by
        have h1 : chartPrime N Δ y = ∑ m ∈ N, (criticalMellinAtomWeight m : ℂ) * Δ (y + Real.log m) +
            ∑ m ∈ N, (criticalMellinAtomWeight m : ℂ) * Δ (y - Real.log m) := by
          rw [chartPrime, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun m _ => by ring
        have h2 := Finset.sum_filter_add_sum_filter_not N (fun m : ℕ => Real.log m = 2 * a.1.1)
          (fun m => (criticalMellinAtomWeight m : ℂ) * Δ (y + Real.log m))
        have h3 : ∑ m ∈ N.filter (fun m : ℕ => Real.log m = 2 * a.1.1),
            (criticalMellinAtomWeight m : ℂ) * Δ (y + Real.log m) =
            (W : ℂ) * Δ (y + 2 * a.1.1) := by
          rw [hWdef, chartKickMass]
          push_cast
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [(Finset.mem_filter.mp hm).2]
        rw [h1, ← h2, h3, add_assoc]
      rw [hprime]
      ring
    rw [hrestEq]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hcommb y))
    by_cases hya : y < a₁.1.1
    · have hmem : y ∈ Ico (0 : ℝ) a₁.1.1 := ⟨hy0.le, hya⟩
      change _ ≤ (Ico (0 : ℝ) a₁.1.1).indicator _ y
      rw [indicator_of_mem hmem, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hb1 := (norm_chartBounded_le hcΔ hsΔ (R := a₁.1.1) (T := 2 * a₂.1.1) hy0.le hya.le hΔ0
        (fun t ht => hΔT t (by linarith only [ht, hb₂]))).trans
        (mul_le_mul_of_nonneg_left hmass hB)
      have hsum1 : ‖∑ m ∈ N₁, (criticalMellinAtomWeight m : ℂ) * Δ (y + Real.log m)‖ ≤
          ∑ m ∈ N₁, criticalMellinAtomWeight m * ‖Δ (y + Real.log m)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hwnn m)])
      have hsum2 : ‖∑ m ∈ N, (criticalMellinAtomWeight m : ℂ) * Δ (y - Real.log m)‖ ≤
          ∑ m ∈ N, criticalMellinAtomWeight m * ‖Δ (y - Real.log m)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hwnn m)])
      have hall : ‖chartMass * Δ y + chartBounded Δ y +
          (∑ m ∈ N₁, (criticalMellinAtomWeight m : ℂ) * Δ (y + Real.log m) +
            ∑ m ∈ N, (criticalMellinAtomWeight m : ℂ) * Δ (y - Real.log m))‖ ≤ B * L + m₁ y := by
        have h1 := norm_add_le (chartMass * Δ y + chartBounded Δ y)
          (∑ m ∈ N₁, (criticalMellinAtomWeight m : ℂ) * Δ (y + Real.log m) +
            ∑ m ∈ N, (criticalMellinAtomWeight m : ℂ) * Δ (y - Real.log m))
        have h2 := norm_add_le (chartMass * Δ y) (chartBounded Δ y)
        have h3 := norm_add_le (∑ m ∈ N₁, (criticalMellinAtomWeight m : ℂ) * Δ (y + Real.log m))
          (∑ m ∈ N, (criticalMellinAtomWeight m : ℂ) * Δ (y - Real.log m))
        rw [norm_mul] at h2
        dsimp only [m₁]
        linarith only [h1, h2, h3, hb1, hsum1, hsum2]
      have hc1 := mul_le_mul (C.abs_le y) hall (norm_nonneg _) zero_le_one
      rwa [one_mul] at hc1
    · rw [hCa₁ y (not_lt.mp hya), Complex.ofReal_zero, zero_mul, norm_zero]
      exact hg0 y
  -- Assembly.
  have hreste : (B * L + K * D) * V q + (∫ y, g y) / q + 1 / a₁.1.1 * L ≤
      K * D * V q + (B * C₂ + a₁.1.1 * (B * C₂) + K * C₂ + C₂ / a₁.1.1) * q := by
    have hq2 : q ^ 2 ≤ q := by nlinarith only [hq, hq1]
    have hLq : L = C₂ * q ^ 2 := rfl
    have h1 : B * L * V q ≤ B * C₂ * q := by
      have hmul : 0 ≤ B * C₂ := by positivity
      rw [hLq]
      calc
        _ = (B * C₂) * (q ^ 2 * V q) := by ring
        _ ≤ (B * C₂) * q := mul_le_mul_of_nonneg_left
          (by nlinarith only [hq2, hVq, hVq0, sq_nonneg q]) hmul
    have h2 : (∫ y, g y) / q ≤ (a₁.1.1 * (B * C₂) + K * C₂) * q := by
      rw [div_le_iff₀ hq]
      refine hgint.trans_eq ?_
      rw [hLq]
      ring
    have h3 : 1 / a₁.1.1 * L ≤ C₂ / a₁.1.1 * q := by
      rw [hLq]
      have heq : 1 / a₁.1.1 * (C₂ * q ^ 2) = C₂ / a₁.1.1 * q ^ 2 := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hq2 (by positivity)
    nlinarith only [h1, h2, h3]
  have hfinal : evalVectorLeftTrace b z - ρ * evalVectorLeftTrace a z -
      (W : ℂ) * evalVectorRightTrace b z * (logarithmicRenewalCoupling ε : ℂ) =
      (W : ℂ) * ((∫ y in Ioc (0 : ℝ) ε, (v y : ℂ) * G (ε - y)) -
        evalVectorRightTrace b z * (logarithmicRenewalCoupling ε : ℂ)) +
      ∫ y : ℝ, (v y : ℂ) * rest y := by
    rw [hdiff, hsplit, hmainEq]
    ring
  rw [hfinal]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hW0]
  have hmainb' := mul_le_mul_of_nonneg_left hcoupled hW0
  have hrest' := hrest.trans hreste
  nlinarith only [hmainb', hrest']


/-! ### The limits -/

private theorem eventually_lt_nhdsGT {a c : ℝ} (hc : a < c) : ∀ᶠ x : ℝ in 𝓝[>] a, x < c :=
  mem_of_superset (Ioo_mem_nhdsGT hc) fun _ h => h.2

private theorem eventually_gt_nhdsLT {a c : ℝ} (hc : a < c) : ∀ᶠ x : ℝ in 𝓝[<] c, a < x :=
  mem_of_superset (Ioo_mem_nhdsLT hc) fun _ h => h.1

theorem tendsto_two_mul_nhdsGT :
    Tendsto (fun h : ℝ => 2 * h) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h0 : Tendsto (fun h : ℝ => 2 * h) (𝓝 (0 : ℝ)) (𝓝 (2 * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_pos two_pos (mem_Ioi.mp hh)

theorem logarithmicRenewalCoupling_nonneg (x : ℝ) : 0 ≤ logarithmicRenewalCoupling x :=
  setIntegral_nonneg measurableSet_Ioc fun _ _ =>
    mul_nonneg (logarithmicCausalKernel_nonneg _) (logarithmicRenewalMass_nonneg _)

theorem tendsto_logarithmicRenewalCoupling_zero :
    Tendsto logarithmicRenewalCoupling (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h2 := tendsto_logarithmicRenewalMass_zero.pow 2
  rw [zero_pow two_ne_zero] at h2
  exact squeeze_zero logarithmicRenewalCoupling_nonneg logarithmicRenewalCoupling_le_square h2

/-- `J(2h) log(1/h) → 1`. -/
theorem tendsto_coupling_two_mul_mul_log :
    Tendsto (fun h : ℝ => logarithmicRenewalCoupling (2 * h) * Real.log (1 / h)) (𝓝[>] (0 : ℝ))
      (𝓝 1) := by
  have h1 := tendsto_logarithmicRenewalCoupling_normalized.comp tendsto_two_mul_nhdsGT
  have h2 := (tendsto_logarithmicRenewalCoupling_zero.comp tendsto_two_mul_nhdsGT).mul_const
    (Real.log 2)
  have h3 := h1.add h2
  rw [zero_mul, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0 : ℝ) < h := hh
  simp only [Function.comp_apply]
  have hlog : Real.log (1 / h) = Real.log (1 / (2 * h)) + Real.log 2 := by
    rw [← Real.log_mul (by positivity) two_ne_zero]
    congr 1
    field_simp
  rw [hlog]
  ring

theorem tendsto_mul_log_one_div :
    Tendsto (fun h : ℝ => h * Real.log (1 / h)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h0 : Tendsto (fun h : ℝ => h * Real.log h) (𝓝 (0 : ℝ)) (𝓝 (0 * Real.log 0)) :=
    Real.continuous_mul_log.tendsto 0
  rw [zero_mul] at h0
  have h1 : Tendsto (fun h : ℝ => -(h * Real.log h)) (𝓝[>] (0 : ℝ)) (𝓝 (-0)) :=
    (h0.mono_left nhdsWithin_le_nhds).neg
  rw [neg_zero] at h1
  refine h1.congr fun h => ?_
  rw [one_div, Real.log_inv]
  ring

theorem norm_chartPhase_sub_one_le (z : ℂ) {h : ℝ} (hh : 0 ≤ h) (h1 : h * ‖z‖ ≤ 1) :
    ‖chartPhase z h - 1‖ ≤ 2 * ‖z‖ * h := by
  have hw : ‖I * (starRingEnd ℂ) z * (h : ℂ)‖ = h * ‖z‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg hh, mul_comm]
  have hb := Complex.norm_exp_sub_one_le (x := I * (starRingEnd ℂ) z * (h : ℂ)) (by rw [hw]; exact h1)
  rw [hw] at hb
  rw [chartPhase]
  linarith only [hb]

theorem tendsto_chartPhase_sub_one (z : ℂ) :
    Tendsto (fun h : ℝ => chartPhase z h - 1) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : Continuous (fun h : ℝ => chartPhase z h - 1) := by
    unfold chartPhase
    fun_prop
  have h0 := hc.tendsto 0
  have hz : chartPhase z 0 - 1 = 0 := by simp [chartPhase]
  rw [hz] at h0
  exact h0.mono_left nhdsWithin_le_nhds

/-- The phase is smooth, so it is invisible at logarithmic scale. -/
theorem tendsto_chartPhase_sub_one_mul_log (z : ℂ) :
    Tendsto (fun h : ℝ => (chartPhase z h - 1) * (Real.log (1 / h) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hb := (tendsto_mul_log_one_div.const_mul (2 * ‖z‖))
  rw [mul_zero] at hb
  refine squeeze_zero_norm' ?_ hb
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h * ‖z‖ < 1 := by
    have ht : Tendsto (fun h : ℝ => h * ‖z‖) (𝓝 (0 : ℝ)) (𝓝 (0 * ‖z‖)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at ht
    exact (ht.mono_left nhdsWithin_le_nhds).eventually_lt_const one_pos
  have hlt : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 := eventually_lt_nhdsGT one_pos
  filter_upwards [self_mem_nhdsWithin, hsmall, hlt] with h hh hs hl
  have hh' : (0 : ℝ) < h := hh
  have hL : 0 ≤ Real.log (1 / h) := Real.log_nonneg ((one_le_div hh').mpr hl.le)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (norm_chartPhase_sub_one_le z hh'.le hs.le) hL

theorem chartScale_lt {h s : ℝ} (hs : 0 < s) (hh : h < (s ^ 2) ^ 2) : chartScale h < s :=
  (Real.sqrt_lt' hs).mpr ((Real.sqrt_lt' (by positivity)).mpr hh)

/-- A finite set of logarithms is separated from any point except where it hits it. -/
theorem exists_log_gap (N : Finset ℕ) (c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m ∈ N, Real.log m = c ∨ Real.log m ≤ c - δ ∨ c + δ ≤ Real.log m := by
  classical
  induction N using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert m s _ ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    by_cases hm : Real.log m = c
    · refine ⟨δ, hδ, fun k hk => ?_⟩
      rcases Finset.mem_insert.mp hk with hkm | hk
      · rw [hkm]
        exact Or.inl hm
      · exact h k hk
    · have hpos : 0 < |Real.log m - c| := abs_pos.mpr (sub_ne_zero.mpr hm)
      obtain ⟨d, hd, hdδ, hdm⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ δ ∧ d ≤ |Real.log m - c| :=
        ⟨min δ |Real.log m - c|, lt_min hδ hpos, min_le_left _ _, min_le_right _ _⟩
      refine ⟨d, hd, fun k hk => ?_⟩
      rcases Finset.mem_insert.mp hk with hkm | hk
      · rw [hkm]
        right
        rcases le_total (Real.log m) c with hle | hle
        · left
          rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hdm
          linarith only [hdm]
        · right
          rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hdm
          linarith only [hdm]
      · rcases h k hk with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl (by linarith only [h1, hdδ]))
        · exact Or.inr (Or.inr (by linarith only [h1, hdδ]))

/-! ### The kick weight -/

/-- The kick weight of an aperture: `Λ(n)/√n` if `2a = log n`, and zero when no integer has that
logarithm. -/
def traceKickWeight (a : ℝ) : ℝ := chartKickMass (Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) a

theorem traceKickWeight_nonneg (a : ℝ) : 0 ≤ traceKickWeight a := chartKickMass_nonneg _ _

/-- The kick mass does not depend on the top of the prime window. -/
theorem chartKickMass_eq_traceKickWeight {a c : ℝ} (hac : a ≤ c) :
    chartKickMass (Finset.Icc 2 ⌊Real.exp (2 * c)⌋₊) a = traceKickWeight a := by
  unfold traceKickWeight chartKickMass
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h2, _⟩, hlog⟩
    refine ⟨⟨h2, ?_⟩, hlog⟩
    have hpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hfl : ⌊Real.exp (2 * a)⌋₊ = m := by rw [← hlog, Real.exp_log hpos, Nat.floor_natCast]
    exact hfl.ge
  · rintro ⟨⟨h2, hm⟩, hlog⟩
    exact ⟨⟨h2, hm.trans (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith only [hac])))⟩, hlog⟩

theorem traceKickWeight_of_log {a : ℝ} {n : ℕ} (hn : 2 ≤ n) (ha : 2 * a = Real.log n) :
    traceKickWeight a = criticalMellinAtomWeight n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold traceKickWeight chartKickMass
  have hfilter : (Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊).filter (fun m : ℕ => Real.log m = 2 * a) =
      {n} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h2, _⟩, hlog⟩
      have hm : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have := Real.log_injOn_pos (Set.mem_Ioi.mpr hm) (Set.mem_Ioi.mpr hpos) (hlog.trans ha)
      exact_mod_cast this
    · intro hm
      rw [hm]
      refine ⟨⟨hn, ?_⟩, ha.symm⟩
      have hfl : ⌊Real.exp (2 * a)⌋₊ = n := by rw [ha, Real.exp_log hpos, Nat.floor_natCast]
      exact hfl.ge
  rw [hfilter, Finset.sum_singleton]

theorem traceKickWeight_eq_zero {a : ℝ} (ha : ∀ n : ℕ, 2 ≤ n → Real.log n ≠ 2 * a) :
    traceKickWeight a = 0 := by
  unfold traceKickWeight chartKickMass
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨hmem, hlog⟩ := Finset.mem_filter.mp hm
  exact absurd hlog (ha m (Finset.mem_Icc.mp hmem).1)

/-! ### The logarithmic form of the increment -/

/-- **The increment at logarithmic scale.** The coefficient `Q` of the interior term does not depend
on the distance `η` to the far endpoint. -/
theorem exists_trace_increment_log_bound (a₁ a₂ : PrecontactAperture) (z : ℂ) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ η : ℝ, 0 < η → 3 * η ≤ a₁.1.1 →
      ∃ G : ℝ → ℝ, Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) ∧ ∃ h₀ : ℝ, 0 < h₀ ∧
        ∀ a b : PrecontactAperture, a₁.1.1 ≤ a.1.1 → a.1.1 ≤ b.1.1 → b.1.1 ≤ a₂.1.1 →
        0 < b.1.1 - a.1.1 → b.1.1 - a.1.1 < h₀ →
        (∀ m ∈ Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊,
          Real.log m ≤ 2 * a.1.1 - 4 * η ∨ 2 * b.1.1 ≤ Real.log m ∨ Real.log m = 2 * a.1.1) →
        ‖evalVectorLeftTrace b z - chartPhase z (b.1.1 - a.1.1) * evalVectorLeftTrace a z -
            (chartKickMass (Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊) a.1.1 : ℂ) *
              evalVectorRightTrace b z *
              (logarithmicRenewalCoupling (2 * (b.1.1 - a.1.1)) : ℂ)‖ *
            Real.log (1 / (b.1.1 - a.1.1)) ≤
          Q * V (3 * η) * (V (chartScale (b.1.1 - a.1.1)) ^ 2 * Real.log (1 / (b.1.1 - a.1.1))) +
            G (b.1.1 - a.1.1) := by
  obtain ⟨C₉, A, hC₉, hA, hinc⟩ := exists_trace_increment_bound a₁ a₂ z
  obtain ⟨C₇, hC₇, hint⟩ := exists_interior_bound a₁ a₂ z
  set N := Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊ with hNdef
  set K := chartSupConstant N with hKdef
  have hK : 0 ≤ K := chartSupConstant_nonneg N
  refine ⟨K * C₇, mul_nonneg hK hC₇, fun η hη h3η => ?_⟩
  obtain ⟨C₈, h₈, hC₈, hh₈, hint'⟩ := hint η hη h3η
  set PM := chartPrimeMass N with hPMdef
  have hPM : 0 ≤ PM := chartPrimeMass_nonneg N
  let G : ℝ → ℝ := fun h => (K * C₈ + C₉) * (chartScale h * Real.log (1 / h)) +
    2 * A * PM * (V (2 * h) * (logarithmicRenewalCoupling (2 * h) * Real.log (1 / h)))
  have hG : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 := tendsto_sqrt_sqrt_mul_log.const_mul (K * C₈ + C₉)
    have h2 := ((tendsto_logarithmicRenewalMass_zero.comp tendsto_two_mul_nhdsGT).mul
      tendsto_coupling_two_mul_mul_log).const_mul (2 * A * PM)
    have h3 := h1.add h2
    simp only [zero_mul, mul_zero, add_zero] at h3
    exact h3
  have ha₁p := a₁.1.2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hqη : 0 < 2 * η := by positivity
  refine ⟨G, hG, min (min 1 (a₁.1.1 / 4)) (min h₈ (min (((2 * η) ^ 2) ^ 2)
    ((Real.log 2 ^ 2) ^ 2))), by positivity, fun a b ha₁ hab hb₂ hh hh₀ hpart => ?_⟩
  set h := b.1.1 - a.1.1 with hhdef
  have hh1 : h < 1 := hh₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hh4 : 4 * h ≤ a₁.1.1 := by
    have : h < a₁.1.1 / 4 := hh₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    linarith only [this]
  have hh8 : h < h₈ := hh₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhq : h < ((2 * η) ^ 2) ^ 2 :=
    hh₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhl : h < (Real.log 2 ^ 2) ^ 2 :=
    hh₀.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  set q := chartScale h with hqdef
  have hq : 0 < q := chartScale_pos hh
  have hVq := logarithmicRenewalMass_le_one q
  have hVq0 := logarithmicRenewalMass_nonneg q
  have hV3 := logarithmicRenewalMass_nonneg (3 * η)
  let D := C₇ * V (3 * η) * V q + C₈ * q
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hmain := hinc a b ha₁ hab hb₂ hh hh1 hh4 η D hη h3η (chartScale_lt hqη hhq).le
    (chartScale_lt hlog2 hhl) hD0 (fun t ht => hint' a b ha₁ hab hb₂ hh hh8 t ht) hpart
  have hW : chartKickMass N a.1.1 ≤ PM := chartKickMass_le N _
  have hW0 := chartKickMass_nonneg N a.1.1
  have hJ0 := logarithmicRenewalCoupling_nonneg (2 * h)
  have hV2 := logarithmicRenewalMass_nonneg (2 * h)
  have hL : 0 ≤ Real.log (1 / h) := Real.log_nonneg ((one_le_div hh).mpr hh1.le)
  have hlast : chartKickMass N a.1.1 * (2 * A * V (2 * h) * logarithmicRenewalCoupling (2 * h)) ≤
      PM * (2 * A * V (2 * h) * logarithmicRenewalCoupling (2 * h)) :=
    mul_le_mul_of_nonneg_right hW (by positivity)
  have hKD : K * D * V q ≤ K * C₇ * V (3 * η) * V q ^ 2 + K * C₈ * q := by
    have h1 : K * C₈ * q * V q ≤ K * C₈ * q :=
      mul_le_of_le_one_right (by positivity) hVq
    dsimp only [D]
    nlinarith only [h1]
  have hbound := (hmain.trans (add_le_add (add_le_add hKD le_rfl) hlast))
  calc
    _ ≤ (K * C₇ * V (3 * η) * V q ^ 2 + K * C₈ * q + C₉ * q +
        PM * (2 * A * V (2 * h) * logarithmicRenewalCoupling (2 * h))) * Real.log (1 / h) :=
      mul_le_mul_of_nonneg_right hbound hL
    _ = K * C₇ * V (3 * η) * (V q ^ 2 * Real.log (1 / h)) +
        ((K * C₈ + C₉) * (q * Real.log (1 / h)) +
          2 * A * PM * (V (2 * h) * (logarithmicRenewalCoupling (2 * h) * Real.log (1 / h)))) := by
      ring

/-- **The increment is small at logarithmic scale**, uniformly on a compact precontact interval,
whenever the prime powers keep a fixed distance `g` below the old far endpoint. -/
theorem exists_trace_increment_small (a₁ a₂ : PrecontactAperture) (z : ℂ) {g e : ℝ} (hg : 0 < g)
    (he : 0 < e) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ a b : PrecontactAperture, a₁.1.1 ≤ a.1.1 → a.1.1 ≤ b.1.1 →
      b.1.1 ≤ a₂.1.1 → 0 < b.1.1 - a.1.1 → b.1.1 - a.1.1 < h₀ →
      (∀ m ∈ Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊,
        Real.log m ≤ 2 * a.1.1 - g ∨ 2 * b.1.1 ≤ Real.log m ∨ Real.log m = 2 * a.1.1) →
      ‖evalVectorLeftTrace b z - chartPhase z (b.1.1 - a.1.1) * evalVectorLeftTrace a z -
          (chartKickMass (Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊) a.1.1 : ℂ) *
            evalVectorRightTrace b z *
            (logarithmicRenewalCoupling (2 * (b.1.1 - a.1.1)) : ℂ)‖ *
          Real.log (1 / (b.1.1 - a.1.1)) < e := by
  obtain ⟨Q, hQ, hlog⟩ := exists_trace_increment_log_bound a₁ a₂ z
  have ha₁ := a₁.1.2
  -- Choose the distance `η` so that the interior term is below `e/2`.
  have hsmallη : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), Q * V (3 * η) * 5 < e / 2 := by
    have h3 : Tendsto (fun η : ℝ => 3 * η) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have h0 : Tendsto (fun h : ℝ => 3 * h) (𝓝 (0 : ℝ)) (𝓝 (3 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        exact mul_pos three_pos (mem_Ioi.mp hh)
    have ht := ((tendsto_logarithmicRenewalMass_zero.comp h3).const_mul Q).mul_const 5
    simp only [mul_zero, zero_mul] at ht
    exact ht.eventually_lt_const (half_pos he)
  have hη₁ : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), η < min (g / 4) (a₁.1.1 / 3) :=
    eventually_lt_nhdsGT (lt_min (by positivity) (by positivity))
  obtain ⟨η, hηs, hηm, hηp⟩ :=
    (hsmallη.and (hη₁.and eventually_mem_nhdsWithin)).exists
  have hη : 0 < η := hηp
  have hηg : 4 * η ≤ g := by
    have := hηm.trans_le (min_le_left _ _)
    linarith only [this]
  have h3η : 3 * η ≤ a₁.1.1 := by
    have := hηm.trans_le (min_le_right _ _)
    linarith only [this]
  obtain ⟨G, hG, h₀, hh₀, hmain⟩ := hlog η hη h3η
  have hF : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), V (chartScale h) ^ 2 * Real.log (1 / h) < 5 :=
    tendsto_renewalMass_quarter_sq_mul_log.eventually_lt_const (by norm_num)
  have hGs : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), G h < e / 2 :=
    hG.eventually_lt_const (half_pos he)
  have hlt : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < h₀ := eventually_lt_nhdsGT hh₀
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (zero_lt_one' ℝ)).mp
    (hF.and (hGs.and hlt))
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨u, hu0, fun a b ha₁' hab hb₂ hh hhu hpart => ?_⟩
  obtain ⟨hF', hG', hlt'⟩ := hsub ⟨hh, hhu⟩
  have hpart' : ∀ m ∈ Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊,
      Real.log m ≤ 2 * a.1.1 - 4 * η ∨ 2 * b.1.1 ≤ Real.log m ∨ Real.log m = 2 * a.1.1 := by
    intro m hm
    rcases hpart m hm with h | h | h
    · exact Or.inl (by linarith only [h, hηg])
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hb := hmain a b ha₁' hab hb₂ hh hlt' hpart'
  have hcoef : 0 ≤ Q * V (3 * η) := mul_nonneg hQ (logarithmicRenewalMass_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hF'.le hcoef
  linarith only [hb, hmul, hηs, hG']

/-! ### The filters of the two one-sided limits -/

/-- The apertures approaching `a` from above. -/
def fromAbove (a : ℝ) : Filter PrecontactAperture := comap (fun b => b.1.1) (𝓝[>] a)

/-- The apertures approaching `a` from below. -/
def fromBelow (a : ℝ) : Filter PrecontactAperture := comap (fun b => b.1.1) (𝓝[<] a)

theorem tendsto_fromAbove_sub (a : ℝ) :
    Tendsto (fun b : PrecontactAperture => b.1.1 - a) (fromAbove a) (𝓝[>] (0 : ℝ)) := by
  have h1 : Tendsto (fun b : PrecontactAperture => b.1.1) (fromAbove a) (𝓝[>] a) :=
    tendsto_comap
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h2 := (h1.mono_right nhdsWithin_le_nhds).sub_const a
    rwa [sub_self] at h2
  · filter_upwards [h1.eventually eventually_mem_nhdsWithin] with b hb
    exact sub_pos.mpr (mem_Ioi.mp hb)

theorem tendsto_fromBelow_sub (b : ℝ) :
    Tendsto (fun a : PrecontactAperture => b - a.1.1) (fromBelow b) (𝓝[>] (0 : ℝ)) := by
  have h1 : Tendsto (fun a : PrecontactAperture => a.1.1) (fromBelow b) (𝓝[<] b) :=
    tendsto_comap
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h2 := (h1.mono_right nhdsWithin_le_nhds).const_sub b
    rwa [sub_self] at h2
  · filter_upwards [h1.eventually eventually_mem_nhdsWithin] with a ha
    exact sub_pos.mpr (mem_Iio.mp ha)

theorem exists_precontact_gt (a : PrecontactAperture) :
    ∃ c : PrecontactAperture, a.1.1 < c.1.1 := by
  obtain ⟨x, hx1, hx2⟩ := EReal.exists_between_coe_real a.2
  have hax : a.1.1 < x := EReal.coe_lt_coe_iff.mp hx1
  exact ⟨toPrecontact (a := x) ⟨a.1.2.trans hax, hx2⟩, hax⟩

theorem exists_precontact_lt (b : PrecontactAperture) :
    ∃ c : PrecontactAperture, c.1.1 < b.1.1 := by
  have hb := b.1.2
  have hlt : ((b.1.1 / 2 : ℝ) : EReal) < _ :=
    (EReal.coe_le_coe_iff.mpr (by linarith only [hb] : b.1.1 / 2 ≤ b.1.1)).trans_lt b.2
  exact ⟨toPrecontact (a := b.1.1 / 2) ⟨by linarith only [hb], hlt⟩, by
    change b.1.1 / 2 < b.1.1
    linarith only [hb]⟩

/-- The fixed part of the right limit: the increment `X` of the trace is `o(1/log)`. -/
theorem tendsto_right_increment (a : PrecontactAperture) (z : ℂ) {c : PrecontactAperture}
    (hc : a.1.1 < c.1.1) :
    Tendsto (fun b : PrecontactAperture =>
        (evalVectorLeftTrace b z - chartPhase z (b.1.1 - a.1.1) * evalVectorLeftTrace a z -
          (traceKickWeight a.1.1 : ℂ) * evalVectorRightTrace b z *
            (logarithmicRenewalCoupling (2 * (b.1.1 - a.1.1)) : ℂ)) *
          (Real.log (1 / (b.1.1 - a.1.1)) : ℂ))
      (fromAbove a.1.1) (𝓝 0) := by
  have hs := tendsto_fromAbove_sub a.1.1
  have hval : Tendsto (fun b : PrecontactAperture => b.1.1) (fromAbove a.1.1) (𝓝[>] a.1.1) :=
    tendsto_comap
  obtain ⟨δ, hδ, hgap⟩ := exists_log_gap (Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊) (2 * a.1.1)
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨h₀, hh₀, hsmall⟩ := exists_trace_increment_small a c z hδ he
  have hlt1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < min (min h₀ 1) (δ / 2) :=
    eventually_lt_nhdsGT (by positivity)
  have hcle : ∀ᶠ x : ℝ in 𝓝[>] a.1.1, x < c.1.1 := eventually_lt_nhdsGT hc
  filter_upwards [hs.eventually eventually_mem_nhdsWithin, hs.eventually hlt1, hval.eventually hcle]
    with b hb0 hb1 hb2
  have hbpos : 0 < b.1.1 - a.1.1 := hb0
  have hab : a.1.1 ≤ b.1.1 := (sub_pos.mp hbpos).le
  have hmin : b.1.1 - a.1.1 < min (min h₀ 1) (δ / 2) := hb1
  have hbh₀ : b.1.1 - a.1.1 < h₀ := hmin.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hb1' : b.1.1 - a.1.1 < 1 := hmin.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hbδ : b.1.1 - a.1.1 < δ / 2 := hmin.trans_le (min_le_right _ _)
  have hpart : ∀ m ∈ Finset.Icc 2 ⌊Real.exp (2 * c.1.1)⌋₊,
      Real.log m ≤ 2 * a.1.1 - δ ∨ 2 * b.1.1 ≤ Real.log m ∨ Real.log m = 2 * a.1.1 := by
    intro m hm
    rcases hgap m hm with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linarith only [h, hbδ]))
  have hbound := hsmall a b le_rfl hab hb2.le hbpos hbh₀ hpart
  rw [chartKickMass_eq_traceKickWeight hc.le] at hbound
  have hL : 0 ≤ Real.log (1 / (b.1.1 - a.1.1)) :=
    Real.log_nonneg ((one_le_div hbpos).mpr hb1'.le)
  rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hL]
  exact hbound

/-- The fixed part of the left limit: there is no kick from below. -/
theorem tendsto_left_increment (b : PrecontactAperture) (z : ℂ) :
    Tendsto (fun a : PrecontactAperture =>
        (evalVectorLeftTrace b z - chartPhase z (b.1.1 - a.1.1) * evalVectorLeftTrace a z) *
          (Real.log (1 / (b.1.1 - a.1.1)) : ℂ))
      (fromBelow b.1.1) (𝓝 0) := by
  have hs := tendsto_fromBelow_sub b.1.1
  have hval : Tendsto (fun a : PrecontactAperture => a.1.1) (fromBelow b.1.1) (𝓝[<] b.1.1) :=
    tendsto_comap
  obtain ⟨a₁, ha₁⟩ := exists_precontact_lt b
  obtain ⟨δ, hδ, hgap⟩ := exists_log_gap (Finset.Icc 2 ⌊Real.exp (2 * b.1.1)⌋₊) (2 * b.1.1)
  rw [Metric.tendsto_nhds]
  intro e he
  obtain ⟨h₀, hh₀, hsmall⟩ := exists_trace_increment_small a₁ b z (half_pos hδ) he
  have hlt1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < min (min h₀ 1) (δ / 4) :=
    eventually_lt_nhdsGT (by positivity)
  have hcle : ∀ᶠ x : ℝ in 𝓝[<] b.1.1, a₁.1.1 < x := eventually_gt_nhdsLT ha₁
  filter_upwards [hs.eventually eventually_mem_nhdsWithin, hs.eventually hlt1, hval.eventually hcle]
    with a ha0 ha1 ha2
  have hapos : 0 < b.1.1 - a.1.1 := ha0
  have hab : a.1.1 ≤ b.1.1 := (sub_pos.mp hapos).le
  have hmin : b.1.1 - a.1.1 < min (min h₀ 1) (δ / 4) := ha1
  have hah₀ : b.1.1 - a.1.1 < h₀ := hmin.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have ha1' : b.1.1 - a.1.1 < 1 := hmin.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have haδ : b.1.1 - a.1.1 < δ / 4 := hmin.trans_le (min_le_right _ _)
  have hpart : ∀ m ∈ Finset.Icc 2 ⌊Real.exp (2 * b.1.1)⌋₊,
      Real.log m ≤ 2 * a.1.1 - δ / 2 ∨ 2 * b.1.1 ≤ Real.log m ∨ Real.log m = 2 * a.1.1 := by
    intro m hm
    rcases hgap m hm with h | h | h
    · exact Or.inr (Or.inl h.ge)
    · exact Or.inl (by linarith only [h, haδ])
    · exact Or.inr (Or.inl (by linarith only [h, hδ]))
  have hW : chartKickMass (Finset.Icc 2 ⌊Real.exp (2 * b.1.1)⌋₊) a.1.1 = 0 := by
    unfold chartKickMass
    refine Finset.sum_eq_zero fun m hm => ?_
    obtain ⟨hmem, hlog⟩ := Finset.mem_filter.mp hm
    exfalso
    rcases hgap m hmem with h | h | h
    · linarith only [h, hlog, hapos]
    · linarith only [h, hlog, haδ, hδ]
    · linarith only [h, hlog, hapos, hδ]
  have hbound := hsmall a b ha2.le hab le_rfl hapos hah₀ hpart
  rw [hW, Complex.ofReal_zero, zero_mul, zero_mul, sub_zero] at hbound
  have hL : 0 ≤ Real.log (1 / (b.1.1 - a.1.1)) :=
    Real.log_nonneg ((one_le_div hapos).mpr ha1'.le)
  rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hL]
  exact hbound

/-- A quantity which is `o(1/log(1/h))` tends to zero. -/
private theorem tendsto_zero_of_mul_log {ι : Type*} {l : Filter ι} {X : ι → ℂ} {h : ι → ℝ}
    (hh : Tendsto h l (𝓝[>] (0 : ℝ)))
    (hX : Tendsto (fun i => X i * (Real.log (1 / h i) : ℂ)) l (𝓝 0)) : Tendsto X l (𝓝 0) := by
  have hn : Tendsto (fun i => ‖X i * (Real.log (1 / h i) : ℂ)‖) l (𝓝 0) := by
    simpa only [norm_zero] using hX.norm
  refine squeeze_zero_norm' ?_ hn
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < Real.exp (-1) :=
    eventually_lt_nhdsGT (Real.exp_pos _)
  filter_upwards [hh.eventually eventually_mem_nhdsWithin, hh.eventually hlt] with i h0 h1
  have h0' : 0 < h i := h0
  have hl : Real.log (h i) < -1 := (Real.log_lt_iff_lt_exp h0').mpr h1
  have hL : 1 ≤ Real.log (1 / h i) := by
    rw [one_div, Real.log_inv]
    linarith only [hl]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hL])]
  exact le_mul_of_one_le_right (norm_nonneg _) hL

/-! ### Continuity of the traces -/

/-- **The traces are right-continuous** at every precontact aperture. -/
theorem tendsto_leftTrace_right (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun b : PrecontactAperture => evalVectorLeftTrace b z) (fromAbove a.1.1)
      (𝓝 (evalVectorLeftTrace a z)) := by
  obtain ⟨c, hc⟩ := exists_precontact_gt a
  have hs := tendsto_fromAbove_sub a.1.1
  have hval : Tendsto (fun b : PrecontactAperture => b.1.1) (fromAbove a.1.1) (𝓝[>] a.1.1) :=
    tendsto_comap
  have hX := tendsto_zero_of_mul_log hs (tendsto_right_increment a z hc)
  have hρ := ((tendsto_chartPhase_sub_one z).comp hs).mul_const (evalVectorLeftTrace a z)
  rw [zero_mul] at hρ
  obtain ⟨A, _, hA⟩ := exists_uniform_endpoint_data a c (-z)
  have hW := traceKickWeight_nonneg a.1.1
  have hJ := (tendsto_logarithmicRenewalCoupling_zero.comp
    (tendsto_two_mul_nhdsGT.comp hs)).const_mul (traceKickWeight a.1.1 * A)
  rw [mul_zero] at hJ
  have hkick : Tendsto (fun b : PrecontactAperture => (traceKickWeight a.1.1 : ℂ) *
      evalVectorRightTrace b z * (logarithmicRenewalCoupling (2 * (b.1.1 - a.1.1)) : ℂ))
      (fromAbove a.1.1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hJ
    have hcle : ∀ᶠ x : ℝ in 𝓝[>] a.1.1, x < c.1.1 := eventually_lt_nhdsGT hc
    filter_upwards [hval.eventually eventually_mem_nhdsWithin, hval.eventually hcle] with b hb0 hb1
    have hb0' : a.1.1 < b.1.1 := hb0
    have hJ0 := logarithmicRenewalCoupling_nonneg (2 * (b.1.1 - a.1.1))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hW,
      Real.norm_of_nonneg hJ0, evalVectorRightTrace_eq_leftTrace_neg]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (hA b hb0'.le hb1.le).1 hW) hJ0
  have hsum := ((hX.add hρ).add hkick).add_const (evalVectorLeftTrace a z)
  simp only [add_zero, zero_add] at hsum
  refine hsum.congr fun b => ?_
  simp only [Function.comp_apply]
  ring

/-- **The traces are left-continuous** at every precontact aperture. -/
theorem tendsto_leftTrace_left (b : PrecontactAperture) (z : ℂ) :
    Tendsto (fun a : PrecontactAperture => evalVectorLeftTrace a z) (fromBelow b.1.1)
      (𝓝 (evalVectorLeftTrace b z)) := by
  obtain ⟨a₁, ha₁⟩ := exists_precontact_lt b
  have hs := tendsto_fromBelow_sub b.1.1
  have hval : Tendsto (fun a : PrecontactAperture => a.1.1) (fromBelow b.1.1) (𝓝[<] b.1.1) :=
    tendsto_comap
  have hX := tendsto_zero_of_mul_log hs (tendsto_left_increment b z)
  obtain ⟨A, _, hA⟩ := exists_uniform_endpoint_data a₁ b z
  have hρ := ((tendsto_chartPhase_sub_one z).comp hs).norm.mul_const A
  rw [norm_zero, zero_mul] at hρ
  have hρt : Tendsto (fun a : PrecontactAperture =>
      (chartPhase z (b.1.1 - a.1.1) - 1) * evalVectorLeftTrace a z) (fromBelow b.1.1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hρ
    have hcle : ∀ᶠ x : ℝ in 𝓝[<] b.1.1, a₁.1.1 < x := eventually_gt_nhdsLT ha₁
    filter_upwards [hval.eventually eventually_mem_nhdsWithin, hval.eventually hcle] with a ha0 ha1
    have ha0' : a.1.1 < b.1.1 := ha0
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hA a ha1.le ha0'.le).1 (norm_nonneg _)
  have hsum := ((hX.neg).sub hρt).const_add (evalVectorLeftTrace b z)
  simp only [neg_zero, sub_zero, add_zero] at hsum
  refine hsum.congr fun a => ?_
  ring

/-! ### The soft kick -/

/-- **The soft prime kick.** As `b ↓ a`,
`(τ_L(b,z) − τ_L(a,z)) log(1/(b−a)) → w(a) τ_R(a,z)`, where `w(a) = Λ(n)/√n` if `2a = log n`, and
`w(a) = 0` when no integer has that logarithm. -/
theorem tendsto_leftTrace_right_kick (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun b : PrecontactAperture =>
        (evalVectorLeftTrace b z - evalVectorLeftTrace a z) *
          (Real.log (1 / (b.1.1 - a.1.1)) : ℂ))
      (fromAbove a.1.1) (𝓝 ((traceKickWeight a.1.1 : ℂ) * evalVectorRightTrace a z)) := by
  obtain ⟨c, hc⟩ := exists_precontact_gt a
  have hs := tendsto_fromAbove_sub a.1.1
  have hX := tendsto_right_increment a z hc
  have hρ := ((tendsto_chartPhase_sub_one_mul_log z).comp hs).mul_const (evalVectorLeftTrace a z)
  rw [zero_mul] at hρ
  have hJ : Tendsto (fun b : PrecontactAperture =>
      ((logarithmicRenewalCoupling (2 * (b.1.1 - a.1.1)) *
        Real.log (1 / (b.1.1 - a.1.1)) : ℝ) : ℂ)) (fromAbove a.1.1) (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp (tendsto_coupling_two_mul_mul_log.comp hs)
  rw [Complex.ofReal_one] at hJ
  have hτ : Tendsto (fun b : PrecontactAperture => evalVectorRightTrace b z) (fromAbove a.1.1)
      (𝓝 (evalVectorRightTrace a z)) := by
    simp only [evalVectorRightTrace_eq_leftTrace_neg]
    exact tendsto_leftTrace_right a (-z)
  have hsum := (hX.add hρ).add ((hτ.const_mul (traceKickWeight a.1.1 : ℂ)).mul hJ)
  simp only [add_zero, zero_add, mul_one] at hsum
  refine hsum.congr fun b => ?_
  simp only [Function.comp_apply]
  push_cast
  ring

/-- **No kick from below.** As `a ↑ b`, `(τ_L(b,z) − τ_L(a,z)) log(1/(b−a)) → 0`: the prime powers act
only from the right of their aperture. -/
theorem tendsto_leftTrace_left_kick (b : PrecontactAperture) (z : ℂ) :
    Tendsto (fun a : PrecontactAperture =>
        (evalVectorLeftTrace b z - evalVectorLeftTrace a z) *
          (Real.log (1 / (b.1.1 - a.1.1)) : ℂ))
      (fromBelow b.1.1) (𝓝 0) := by
  have hs := tendsto_fromBelow_sub b.1.1
  have hsum := (tendsto_left_increment b z).add
    (((tendsto_chartPhase_sub_one_mul_log z).comp hs).mul (tendsto_leftTrace_left b z))
  simp only [add_zero, zero_mul] at hsum
  refine hsum.congr fun a => ?_
  simp only [Function.comp_apply]
  ring

/-! ### The scalar flow -/

open SquareRootThreshold WindowVisibilityLaw Zeta23

theorem precontactSet_mem_nhds (a : PrecontactAperture) : precontactSet ∈ 𝓝 a.1.1 := by
  obtain ⟨c, hc⟩ := exists_precontact_gt a
  obtain ⟨d, hd⟩ := exists_precontact_lt a
  filter_upwards [Ioo_mem_nhds hd hc] with x hx
  exact ⟨d.1.2.trans hx.1, (EReal.coe_le_coe_iff.mpr hx.2.le).trans_lt c.2⟩

private theorem range_val_mem_nhds (a : PrecontactAperture) :
    range (fun b : PrecontactAperture => b.1.1) ∈ 𝓝 a.1.1 :=
  mem_of_superset (precontactSet_mem_nhds a) fun _ hx => ⟨toPrecontact hx, rfl⟩

theorem anchorReflection_coe (b : PrecontactAperture) :
    anchorReflection b.1.1 = (evalVectorRightTrace b I).re / (evalVectorLeftTrace b I).re := by
  have hb : b.1.1 ∈ precontactSet := ⟨b.1.2, b.2⟩
  rw [anchorReflection, dif_pos hb]
  rfl

theorem anchorLeftTrace_re_ne_zero (b : PrecontactAperture) : (evalVectorLeftTrace b I).re ≠ 0 := by
  intro h0
  have h := evalVector_anchorTrace_energy_difference b
  have hpos : 0 < ‖evalVector b I‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (evalVector_ne_zero _ _))
  rw [Complex.sq_norm, Complex.normSq_apply, evalVectorLeftTrace_I_im, Complex.sq_norm,
    Complex.normSq_apply, evalVectorRightTrace_I_im, h0] at h
  nlinarith only [h, hpos, mul_self_nonneg (evalVectorRightTrace b I).re]

private theorem tendsto_re_of_traces {l : Filter PrecontactAperture} (a : PrecontactAperture)
    (hcont : ∀ z, Tendsto (fun b => evalVectorLeftTrace b z) l (𝓝 (evalVectorLeftTrace a z))) :
    Tendsto (fun b => (evalVectorLeftTrace b I).re) l (𝓝 (evalVectorLeftTrace a I).re) ∧
      Tendsto (fun b => (evalVectorRightTrace b I).re) l (𝓝 (evalVectorRightTrace a I).re) := by
  constructor
  · exact Complex.continuous_re.continuousAt.tendsto.comp (hcont I)
  · simp only [evalVectorRightTrace_eq_leftTrace_neg]
    exact Complex.continuous_re.continuousAt.tendsto.comp (hcont (-I))

private theorem tendsto_anchorReflection_of_traces {l : Filter PrecontactAperture}
    (a : PrecontactAperture)
    (hcont : ∀ z, Tendsto (fun b => evalVectorLeftTrace b z) l (𝓝 (evalVectorLeftTrace a z))) :
    Tendsto (fun b : PrecontactAperture => anchorReflection b.1.1) l
      (𝓝 (anchorReflection a.1.1)) := by
  obtain ⟨hu, hv⟩ := tendsto_re_of_traces a hcont
  simp only [anchorReflection_coe]
  exact hv.div hu (anchorLeftTrace_re_ne_zero a)

/-- **The anchor reflection is continuous before contact**, although its derivative is singular at the
logarithms of the prime powers. -/
theorem continuousAt_anchorReflection (a : PrecontactAperture) :
    ContinuousAt anchorReflection a.1.1 := by
  have hright := tendsto_anchorReflection_of_traces a (fun z => tendsto_leftTrace_right a z)
  have hleft := tendsto_anchorReflection_of_traces a (fun z => tendsto_leftTrace_left a z)
  refine continuousAt_iff_continuous_left'_right'.mpr ⟨?_, ?_⟩
  · exact (tendsto_comap'_iff (m := anchorReflection)
      (i := fun b : PrecontactAperture => b.1.1) (f := 𝓝[<] a.1.1)
      (mem_nhdsWithin_of_mem_nhds (range_val_mem_nhds a))).mp hleft
  · exact (tendsto_comap'_iff (m := anchorReflection)
      (i := fun b : PrecontactAperture => b.1.1) (f := 𝓝[>] a.1.1)
      (mem_nhdsWithin_of_mem_nhds (range_val_mem_nhds a))).mp hright

/-- A differentiable function transports the logarithmic scale of its argument. -/
private theorem tendsto_comp_sub_mul_of_hasDerivAt {ι : Type*} {l : Filter ι} {f : ℝ → ℝ}
    {f' x₀ c : ℝ} (hf : HasDerivAt f f' x₀) {φ L : ι → ℝ} (hφ : Tendsto φ l (𝓝 x₀))
    (hL : Tendsto (fun i => (φ i - x₀) * L i) l (𝓝 c)) :
    Tendsto (fun i => (f (φ i) - f x₀) * L i) l (𝓝 (f' * c)) := by
  classical
  let g : ℝ → ℝ := Function.update (slope f x₀) x₀ f'
  have hg : ContinuousAt g x₀ := continuousAt_update_same.mpr (hasDerivAt_iff_tendsto_slope.mp hf)
  have hgx : g x₀ = f' := Function.update_self _ _ _
  have hval : ∀ y, f y - f x₀ = g y * (y - x₀) := by
    intro y
    by_cases hy : y = x₀
    · rw [hy, hgx]
      ring
    · have hgy : g y = slope f x₀ y := Function.update_of_ne hy _ _
      rw [hgy, slope_def_field]
      exact (div_mul_cancel₀ _ (sub_ne_zero.mpr hy)).symm
  have ht : Tendsto (fun i => g (φ i)) l (𝓝 f') := by
    have hcomp := hg.tendsto.comp hφ
    rw [hgx] at hcomp
    exact hcomp
  refine (ht.mul hL).congr fun i => ?_
  rw [hval (φ i)]
  ring

private theorem tendsto_artanh_of_traces {l : Filter PrecontactAperture} (a : PrecontactAperture)
    (hcont : ∀ z, Tendsto (fun b => evalVectorLeftTrace b z) l (𝓝 (evalVectorLeftTrace a z)))
    {L : PrecontactAperture → ℝ} {c : ℝ}
    (hu : Tendsto (fun b => ((evalVectorLeftTrace b I).re - (evalVectorLeftTrace a I).re) * L b) l
      (𝓝 (c * (evalVectorRightTrace a I).re)))
    (hv : Tendsto (fun b => ((evalVectorRightTrace b I).re - (evalVectorRightTrace a I).re) * L b) l
      (𝓝 (c * (evalVectorLeftTrace a I).re))) :
    Tendsto (fun b : PrecontactAperture =>
      (Real.artanh (anchorReflection b.1.1) - Real.artanh (anchorReflection a.1.1)) * L b) l
      (𝓝 c) := by
  have hap : a.1.1 ∈ precontactSet := ⟨a.1.2, a.2⟩
  have hmem := anchorReflection_mem hap
  have hφ := tendsto_anchorReflection_of_traces a hcont
  obtain ⟨hucont, _⟩ := tendsto_re_of_traces a hcont
  have hua := anchorLeftTrace_re_ne_zero a
  set ua := (evalVectorLeftTrace a I).re with huadef
  set va := (evalVectorRightTrace a I).re with hvadef
  have hra : anchorReflection a.1.1 = va / ua := anchorReflection_coe a
  have hne : 1 - anchorReflection a.1.1 ^ 2 ≠ 0 := by
    nlinarith only [hmem.1, hmem.2]
  have hr : Tendsto (fun b : PrecontactAperture =>
      (anchorReflection b.1.1 - anchorReflection a.1.1) * L b) l
      (𝓝 (c * (1 - anchorReflection a.1.1 ^ 2))) := by
    have hquot := ((hv.mul_const ua).sub (hu.const_mul va)).div (hucont.mul_const ua)
      (mul_ne_zero hua hua)
    have hlim : (c * ua * ua - va * (c * va)) / (ua * ua) =
        c * (1 - anchorReflection a.1.1 ^ 2) := by
      rw [hra]
      field_simp
      try ring
    rw [hlim] at hquot
    refine hquot.congr fun b => ?_
    have hub := anchorLeftTrace_re_ne_zero b
    rw [anchorReflection_coe b, hra]
    simp only [Pi.div_apply]
    field_simp
    try ring
  have hfinal := tendsto_comp_sub_mul_of_hasDerivAt (hasDerivAt_artanh hmem) hφ hr
  have hc : 1 / (1 - anchorReflection a.1.1 ^ 2) * (c * (1 - anchorReflection a.1.1 ^ 2)) = c := by
    field_simp
  rwa [hc] at hfinal

/-- **The hyperbolic angle receives the kick**: `(L(x) − L(a)) log(1/(x−a)) → w(a)` as `x ↓ a`, for
`L = artanh r`. -/
theorem tendsto_artanh_anchorReflection_right_kick (a : PrecontactAperture) :
    Tendsto (fun x : ℝ => (Real.artanh (anchorReflection x) -
        Real.artanh (anchorReflection a.1.1)) * Real.log (1 / (x - a.1.1)))
      (𝓝[>] a.1.1) (𝓝 (traceKickWeight a.1.1)) := by
  have hu : Tendsto (fun b : PrecontactAperture =>
      ((evalVectorLeftTrace b I).re - (evalVectorLeftTrace a I).re) *
        Real.log (1 / (b.1.1 - a.1.1))) (fromAbove a.1.1)
      (𝓝 (traceKickWeight a.1.1 * (evalVectorRightTrace a I).re)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_leftTrace_right_kick a I)
    rw [Complex.re_ofReal_mul] at h
    refine h.congr fun b => ?_
    simp only [Function.comp_apply]
    rw [Complex.re_mul_ofReal, Complex.sub_re]
  have hv : Tendsto (fun b : PrecontactAperture =>
      ((evalVectorRightTrace b I).re - (evalVectorRightTrace a I).re) *
        Real.log (1 / (b.1.1 - a.1.1))) (fromAbove a.1.1)
      (𝓝 (traceKickWeight a.1.1 * (evalVectorLeftTrace a I).re)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_leftTrace_right_kick a (-I))
    rw [evalVectorRightTrace_eq_leftTrace_neg, neg_neg, Complex.re_ofReal_mul] at h
    refine h.congr fun b => ?_
    simp only [Function.comp_apply, evalVectorRightTrace_eq_leftTrace_neg]
    rw [Complex.re_mul_ofReal, Complex.sub_re]
  have hmain := tendsto_artanh_of_traces a (fun z => tendsto_leftTrace_right a z) hu hv
  exact (tendsto_comap'_iff (i := fun b : PrecontactAperture => b.1.1) (f := 𝓝[>] a.1.1)
    (mem_nhdsWithin_of_mem_nhds (range_val_mem_nhds a))).mp hmain

/-- From below the hyperbolic angle receives no kick at the logarithmic scale. -/
theorem tendsto_artanh_anchorReflection_left_kick (b : PrecontactAperture) :
    Tendsto (fun x : ℝ => (Real.artanh (anchorReflection b.1.1) -
        Real.artanh (anchorReflection x)) * Real.log (1 / (b.1.1 - x)))
      (𝓝[<] b.1.1) (𝓝 0) := by
  have hu : Tendsto (fun a : PrecontactAperture =>
      ((evalVectorLeftTrace a I).re - (evalVectorLeftTrace b I).re) *
        Real.log (1 / (b.1.1 - a.1.1))) (fromBelow b.1.1)
      (𝓝 (0 * (evalVectorRightTrace b I).re)) := by
    rw [zero_mul]
    have h := (Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_leftTrace_left_kick b I)).neg
    rw [Complex.zero_re, neg_zero] at h
    refine h.congr fun a => ?_
    simp only [Function.comp_apply]
    rw [Complex.re_mul_ofReal, Complex.sub_re]
    ring
  have hv : Tendsto (fun a : PrecontactAperture =>
      ((evalVectorRightTrace a I).re - (evalVectorRightTrace b I).re) *
        Real.log (1 / (b.1.1 - a.1.1))) (fromBelow b.1.1)
      (𝓝 (0 * (evalVectorLeftTrace b I).re)) := by
    rw [zero_mul]
    have h := (Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_leftTrace_left_kick b (-I))).neg
    rw [Complex.zero_re, neg_zero] at h
    refine h.congr fun a => ?_
    simp only [Function.comp_apply, evalVectorRightTrace_eq_leftTrace_neg]
    rw [Complex.re_mul_ofReal, Complex.sub_re]
    ring
  have hmain := (tendsto_artanh_of_traces b (fun z => tendsto_leftTrace_left b z) hu hv).neg
  rw [neg_zero] at hmain
  have hF := (tendsto_comap'_iff (m := fun x : ℝ => -((Real.artanh (anchorReflection x) -
      Real.artanh (anchorReflection b.1.1)) * Real.log (1 / (b.1.1 - x))))
    (i := fun a : PrecontactAperture => a.1.1) (f := 𝓝[<] b.1.1)
    (mem_nhdsWithin_of_mem_nhds (range_val_mem_nhds b))).mp hmain
  refine hF.congr fun x => ?_
  ring

/-- The potential differs from the hyperbolic angle by the integral of the drift. -/
private theorem canonicalPotential_sub_eq {base x y : ℝ} (hb : base ∈ precontactSet)
    (hx : x ∈ precontactSet) (hy : y ∈ precontactSet) :
    canonicalPotential base y - canonicalPotential base x =
      Real.artanh (anchorReflection y) - Real.artanh (anchorReflection x) +
        ∫ t in x..y, precontactCanonicalDrift t := by
  have hl : 0 < min base (min x y) := lt_min hb.1 (lt_min hx.1 hy.1)
  have hm : max base (max x y) ∈ precontactSet := by
    rcases max_choice base (max x y) with h | h
    · rw [h]
      exact hb
    · rcases max_choice x y with h' | h' <;> rw [h, h']
      · exact hx
      · exact hy
  have hs : Icc (min base (min x y)) (max base (max x y)) ⊆ precontactSet := fun t ht =>
    ⟨hl.trans_le ht.1, (EReal.coe_le_coe_iff.mpr ht.2).trans_lt hm.2⟩
  have h := artanh_anchorReflection_sub hs (x := x) (y := y) (base := base)
    ⟨min_le_left _ _, le_max_left _ _⟩
    ⟨(min_le_right _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_right _ _)⟩
    ⟨(min_le_right _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  linarith only [h]

/-- Near a precontact aperture the drift is bounded. -/
private theorem exists_drift_bound (a : PrecontactAperture) :
    ∃ C s : ℝ, 0 ≤ C ∧ 0 < s ∧ ∀ t, |t - a.1.1| < s → ‖precontactCanonicalDrift t‖ ≤ C := by
  have hap : a.1.1 ∈ precontactSet := ⟨a.1.2, a.2⟩
  have hmem := anchorReflection_mem hap
  have hne : 1 - anchorReflection a.1.1 ^ 2 ≠ 0 := by
    nlinarith only [hmem.1, hmem.2]
  have hc := continuousAt_anchorReflection a
  have hf : ContinuousAt (fun t => 2 * anchorReflection t / (1 - anchorReflection t ^ 2)) a.1.1 :=
    (continuousAt_const.mul hc).div (continuousAt_const.sub (hc.pow 2)) hne
  have hev : ∀ᶠ t in 𝓝 a.1.1, ‖2 * anchorReflection t / (1 - anchorReflection t ^ 2)‖ <
      ‖2 * anchorReflection a.1.1 / (1 - anchorReflection a.1.1 ^ 2)‖ + 1 :=
    hf.norm.tendsto.eventually_lt_const (lt_add_one _)
  have hp : ∀ᶠ t in 𝓝 a.1.1, t ∈ precontactSet := precontactSet_mem_nhds a
  obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hp)
  refine ⟨‖2 * anchorReflection a.1.1 / (1 - anchorReflection a.1.1 ^ 2)‖ + 1, s,
    add_nonneg (norm_nonneg _) zero_le_one, hs, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hball (show dist t a.1.1 < s by rwa [Real.dist_eq])
  rw [precontactCanonicalDrift_eq h2]
  exact h1.le

/-- **The canonical potential has its singular term at the logarithms of the prime powers.** As
`x ↓ a`, `(Ψ(x) − Ψ(a)) log(1/(x−a)) → w(a)`: the singular part of `q = Ψ′` at `2a = log n` is the
derivative of the renewal coupling, with weight `Λ(n)/√n`. -/
theorem tendsto_canonicalPotential_right_kick {base : ℝ} (hbase : base ∈ precontactSet)
    (a : PrecontactAperture) :
    Tendsto (fun x : ℝ => (canonicalPotential base x - canonicalPotential base a.1.1) *
        Real.log (1 / (x - a.1.1)))
      (𝓝[>] a.1.1) (𝓝 (traceKickWeight a.1.1)) := by
  have hap : a.1.1 ∈ precontactSet := ⟨a.1.2, a.2⟩
  obtain ⟨C, s, hC, hs, hb⟩ := exists_drift_bound a
  have hsub : Tendsto (fun x : ℝ => x - a.1.1) (𝓝[>] a.1.1) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun x : ℝ => x - a.1.1) (𝓝 a.1.1) (𝓝 (a.1.1 - a.1.1)) :=
        (continuous_id.sub continuous_const).tendsto _
      rw [sub_self] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (mem_Ioi.mp hx)
  have hI : Tendsto (fun x : ℝ => (∫ t in a.1.1..x, precontactCanonicalDrift t) *
      Real.log (1 / (x - a.1.1))) (𝓝[>] a.1.1) (𝓝 0) := by
    have hbd := (tendsto_mul_log_one_div.comp hsub).const_mul C
    rw [mul_zero] at hbd
    refine squeeze_zero_norm' ?_ hbd
    have hlt : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < min s 1 :=
      eventually_lt_nhdsGT (by positivity)
    filter_upwards [self_mem_nhdsWithin, hsub.eventually hlt] with x hx hx1
    have hx' : a.1.1 < x := hx
    have hxs : x - a.1.1 < s := hx1.trans_le (min_le_left _ _)
    have hx1' : x - a.1.1 < 1 := hx1.trans_le (min_le_right _ _)
    have hL : 0 ≤ Real.log (1 / (x - a.1.1)) :=
      Real.log_nonneg ((one_le_div (sub_pos.mpr hx')).mpr hx1'.le)
    have hnorm : ‖∫ t in a.1.1..x, precontactCanonicalDrift t‖ ≤ C * |x - a.1.1| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
        rw [uIoc_of_le hx'.le] at ht
        apply hb
        rw [abs_of_pos (sub_pos.mpr ht.1)]
        linarith only [ht.2, hxs]
    rw [abs_of_pos (sub_pos.mpr hx')] at hnorm
    rw [norm_mul, Real.norm_of_nonneg hL]
    simp only [Function.comp_apply]
    calc
      _ ≤ C * (x - a.1.1) * Real.log (1 / (x - a.1.1)) := mul_le_mul_of_nonneg_right hnorm hL
      _ = _ := by ring
  have hsum := (tendsto_artanh_anchorReflection_right_kick a).add hI
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (precontactSet_mem_nhds a)] with x hx
  beta_reduce
  rw [canonicalPotential_sub_eq hbase hap hx]
  ring

/-- From below the potential has no singular term at the logarithmic scale. -/
theorem tendsto_canonicalPotential_left_kick {base : ℝ} (hbase : base ∈ precontactSet)
    (b : PrecontactAperture) :
    Tendsto (fun x : ℝ => (canonicalPotential base b.1.1 - canonicalPotential base x) *
        Real.log (1 / (b.1.1 - x)))
      (𝓝[<] b.1.1) (𝓝 0) := by
  have hbp : b.1.1 ∈ precontactSet := ⟨b.1.2, b.2⟩
  obtain ⟨C, s, hC, hs, hbd⟩ := exists_drift_bound b
  have hsub : Tendsto (fun x : ℝ => b.1.1 - x) (𝓝[<] b.1.1) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun x : ℝ => b.1.1 - x) (𝓝 b.1.1) (𝓝 (b.1.1 - b.1.1)) :=
        (continuous_const.sub continuous_id).tendsto _
      rw [sub_self] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (mem_Iio.mp hx)
  have hI : Tendsto (fun x : ℝ => (∫ t in x..b.1.1, precontactCanonicalDrift t) *
      Real.log (1 / (b.1.1 - x))) (𝓝[<] b.1.1) (𝓝 0) := by
    have hbound := (tendsto_mul_log_one_div.comp hsub).const_mul C
    rw [mul_zero] at hbound
    refine squeeze_zero_norm' ?_ hbound
    have hlt : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < min s 1 :=
      eventually_lt_nhdsGT (by positivity)
    filter_upwards [self_mem_nhdsWithin, hsub.eventually hlt] with x hx hx1
    have hx' : x < b.1.1 := hx
    have hxs : b.1.1 - x < s := hx1.trans_le (min_le_left _ _)
    have hx1' : b.1.1 - x < 1 := hx1.trans_le (min_le_right _ _)
    have hL : 0 ≤ Real.log (1 / (b.1.1 - x)) :=
      Real.log_nonneg ((one_le_div (sub_pos.mpr hx')).mpr hx1'.le)
    have hnorm : ‖∫ t in x..b.1.1, precontactCanonicalDrift t‖ ≤ C * |b.1.1 - x| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
        rw [uIoc_of_le hx'.le] at ht
        apply hbd
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.2)]
        linarith only [ht.1, hxs]
    rw [abs_of_pos (sub_pos.mpr hx')] at hnorm
    rw [norm_mul, Real.norm_of_nonneg hL]
    simp only [Function.comp_apply]
    calc
      _ ≤ C * (b.1.1 - x) * Real.log (1 / (b.1.1 - x)) := mul_le_mul_of_nonneg_right hnorm hL
      _ = _ := by ring
  have hsum := (tendsto_artanh_anchorReflection_left_kick b).add hI
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (precontactSet_mem_nhds b)] with x hx
  beta_reduce
  rw [canonicalPotential_sub_eq hbase hx hbp]
  ring

end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
