import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheCutStateSolvesTheLogarithmicWindowEquation
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheModulusOfContinuityOfTheStateIsCarriedByTheWall
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheWindowSolutionsAreBounded
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFormHasItsMixedJumpPairing
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicEnergyHasItsLiteralJumpForm
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# The state is continuous, with a pointwise law at the wall

Reflect the cut state `χF` of `TheCutStateSolvesTheLogarithmicWindowEquation` into the window
`[−A, A]` by `x ↦ −A − x`, so that the wall `u = 0` becomes the left edge `x = −A`. In these
coordinates the half-line identity

  `∫ G χF + ∫_{t>0} ν(t) ∫ ΔG ΔχF = ∫ G φ`

is the logarithmic window equation `E(f, u) = ⟨f, g⟩` of the critical Hardy theory of the window
cone, for every finite-energy `f` carried by the window (`logarithmicFullForm_reflected_cut_eq`):
the logarithmic form is mass plus the jump form of `ν` (`logarithmicFullForm_eq_inner_add_jump`),
and the real and imaginary parts of a complex test of finite logarithmic energy are tests of the
energy domain (`reflectedPart_mem_domain`). The solution and its forcing are bounded, so the left
edge theorem `left_edge_of_bounded` applies: on `[−A, 0)` the state agrees almost everywhere with a
continuous function `Ψ(−u)`, and `Ψ(t) √log(1/t)` converges as `t → 0⁺`
(`criticalState_exists_continuous_near_wall`).

Gluing the windows `A = 1, 2, …` gives a representative `Φ` of the state continuous on `u < 0`.
Its limit at the wall is identified by the mean-square law of the wall: with `a = a(W₀)`,
`M = ∫ F² e^{−8u}` and the sign `s` of the wall,

  `Φ(−t) √log(1/t) → s √(8aM)`,  `Φ(−t)² log(1/t) → 8aM`,  `s Φ(−t) > 0` for `0 < t < k₀`

(`criticalState_continuous_pointwise_wall_law`). The pointwise law at the wall and the continuity of
the state hold for every critical state.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower
open CanonicalSystemOfTheWindowTower (logReferenceLevyDensity archLogRemainder
  archLogRemainder_nonneg integrableOn_archLogRemainder measurable_logReferenceLevyDensity
  HasLogarithmicEnergy logarithmicFullForm logarithmicFullForm_eq_inner_add_jump
  logarithmicFullForm_conj hasLogarithmicEnergy_iff_integrable_jump logarithmicTranslation_coeFn)
open CriticalHardyTheoryOfTheWindowCone (left_edge_of_bounded)

/-! ### Reflection into the window -/

private theorem ae_reflect {p : ℝ → Prop} (h : ∀ᵐ v, p v) (c : ℝ) : ∀ᵐ x, p (c - x) :=
  (Measure.measurePreserving_sub_left volume c).quasiMeasurePreserving.ae h

private theorem ae_shift {p : ℝ → Prop} (h : ∀ᵐ v, p v) (t : ℝ) : ∀ᵐ u, p (u + t) :=
  (measurePreserving_add_right volume t).quasiMeasurePreserving.ae h

/-- The window vector `x ↦ W(−A − x)` of a square-integrable real profile. -/
def reflectedWindowVector (A : ℝ) {W : ℝ → ℝ} (hW : MemLp W 2 volume) : SoninL2 :=
  (hW.comp_measurePreserving (Measure.measurePreserving_sub_left volume (-A))).ofReal.toLp
    fun x => ((W (-A - x) : ℝ) : ℂ)

theorem reflectedWindowVector_coeFn (A : ℝ) {W : ℝ → ℝ} (hW : MemLp W 2 volume) :
    (reflectedWindowVector A hW : ℝ → ℂ) =ᵐ[volume] fun x => ((W (-A - x) : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

private theorem mem_aperture_of_ae {a : SuzukiPositiveAperture} {v : SoninL2}
    (h : ∀ᵐ x ∂volume, x ∉ centralInterval a.1 → (v : ℝ → ℂ) x = 0) :
    v ∈ suzukiApertureHilbert a := by
  rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
  refine ⟨v, Lp.ext ?_⟩
  filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) v, h]
    with x h1 h2
  show ((indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) v : SoninL2) :
    ℝ → ℂ) x = (v : ℝ → ℂ) x
  rw [h1]
  by_cases hx : x ∈ centralInterval a.1
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, h2 hx]

private theorem ae_zero_of_mem_aperture {a : SuzukiPositiveAperture} (f : suzukiApertureHilbert a) :
    ∀ᵐ x ∂volume, x ∉ Icc (-a.1) a.1 → ((f : SoninL2) : ℝ → ℂ) x = 0 := by
  have h := indicatorCutoff_suzukiApertureHilbert a f
  filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
    (f : SoninL2)] with x hx hxs
  rw [← h, hx, Set.indicator_of_notMem (show x ∉ centralInterval a.1 from hxs)]

/-- Pairing with a reflected real vector, in half-line coordinates. -/
private theorem inner_reflected_eq {P : ℝ → ℝ} {p q : SoninL2} {Q : ℝ → ℂ} (A : ℝ)
    (hp : (p : ℝ → ℂ) =ᵐ[volume] fun x => ((P (-A - x) : ℝ) : ℂ))
    (hq : (q : ℝ → ℂ) =ᵐ[volume] fun x => Q (-A - x)) :
    inner ℂ p q = ∫ v, (P v : ℂ) * Q v := by
  rw [L2.inner_def]
  calc (∫ x, inner ℂ ((p : ℝ → ℂ) x) ((q : ℝ → ℂ) x))
      = ∫ x, ((P (-A - x) : ℝ) : ℂ) * Q (-A - x) := by
        refine integral_congr_ae ?_
        filter_upwards [hp, hq] with x h1 h2
        rw [h1, h2, RCLike.inner_apply', Complex.conj_ofReal]
    _ = ∫ v, (P v : ℂ) * Q v := integral_sub_left_eq_self (fun v => (P v : ℂ) * Q v) volume (-A)

private theorem sub_logTranslation_reflected {p : SoninL2} {P : ℝ → ℂ} (A t : ℝ)
    (hp : (p : ℝ → ℂ) =ᵐ[volume] fun x => P (-A - x)) :
    ((logTranslationCLM t p - p : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => P (-A - x - t) - P (-A - x) := by
  have h4 : ∀ᵐ x, (p : ℝ → ℂ) (x + t) = P (-A - (x + t)) := ae_shift hp t
  filter_upwards [Lp.coeFn_sub (logTranslationCLM t p) p, logarithmicTranslation_coeFn t p, hp, h4]
    with x h1 h2 h3 h4
  simp only [h1, Pi.sub_apply, h2, h4, h3, show -A - (x + t) = -A - x - t by ring]

/-- The jump pairing of two reflected vectors, in half-line coordinates. -/
private theorem inner_jump_reflected {p q : SoninL2} {P Q : ℝ → ℂ} (A t : ℝ)
    (hp : (p : ℝ → ℂ) =ᵐ[volume] fun x => P (-A - x))
    (hq : (q : ℝ → ℂ) =ᵐ[volume] fun x => Q (-A - x)) :
    inner ℂ (logTranslationCLM t p - p) (logTranslationCLM t q - q) =
      ∫ v, conj (P v - P (v + t)) * (Q v - Q (v + t)) := by
  rw [L2.inner_def]
  calc (∫ x, inner ℂ (((logTranslationCLM t p - p : SoninL2) : ℝ → ℂ) x)
        (((logTranslationCLM t q - q : SoninL2) : ℝ → ℂ) x))
      = ∫ x, conj (P (-A - x - t) - P (-A - x)) * (Q (-A - x - t) - Q (-A - x)) := by
        refine integral_congr_ae ?_
        filter_upwards [sub_logTranslation_reflected A t hp, sub_logTranslation_reflected A t hq]
          with x h1 h2
        rw [h1, h2, RCLike.inner_apply']
    _ = ∫ v, conj (P v - P (v + t)) * (Q v - Q (v + t)) := by
        rw [← integral_sub_left_eq_self
          (fun v => conj (P v - P (v + t)) * (Q v - Q (v + t))) volume (-A - t)]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [show -A - t - x + t = -A - x by ring, show -A - x - t = -A - t - x by ring]

/-- The jump norm of a reflected vector, in half-line coordinates. -/
private theorem norm_sq_jump_reflected {p : SoninL2} {P : ℝ → ℂ} (A t : ℝ)
    (hp : (p : ℝ → ℂ) =ᵐ[volume] fun x => P (-A - x)) :
    ‖logTranslationCLM t p - p‖ ^ 2 = ∫ v, ‖P v - P (v + t)‖ ^ 2 := by
  rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc (∫ x, ‖((logTranslationCLM t p - p : SoninL2) : ℝ → ℂ) x‖ ^ 2)
      = ∫ x, ‖P (-A - x - t) - P (-A - x)‖ ^ 2 :=
        integral_congr_ae ((sub_logTranslation_reflected A t hp).mono fun x hx => by simp only [hx])
    _ = ∫ v, ‖P v - P (v + t)‖ ^ 2 := by
        rw [← integral_sub_left_eq_self (fun v => ‖P v - P (v + t)‖ ^ 2) volume (-A - t)]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [show -A - t - x + t = -A - x by ring, show -A - x - t = -A - t - x by ring]

/-- A real profile of the energy domain has a reflected vector of finite logarithmic energy. -/
theorem hasLogarithmicEnergy_reflectedWindowVector (A : ℝ) {W : ℝ → ℝ}
    (hWd : CriticalHalfLineEnergyDomain W) :
    HasLogarithmicEnergy (reflectedWindowVector A hWd.memLp_real) := by
  rw [hasLogarithmicEnergy_iff_integrable_jump]
  have hc := reflectedWindowVector_coeFn A hWd.memLp_real
  have hn : ∀ t, ‖logTranslationCLM t (reflectedWindowVector A hWd.memLp_real) -
      reflectedWindowVector A hWd.memLp_real‖ ^ 2 = ∫ v, (W v - W (v + t)) ^ 2 := by
    intro t
    rw [norm_sq_jump_reflected (P := fun v => ((W v : ℝ) : ℂ)) A t hc]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine hWd.integrableOn_levyIntegrand.mono'
    (measurable_logReferenceLevyDensity.aestronglyMeasurable.mul
      (((continuous_logTranslationCLM _).sub continuous_const).norm.pow 2).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hν : 0 < logReferenceLevyDensity t := by
    show 0 < Real.exp (-t) / (2 * t)
    exact div_pos (Real.exp_pos _) (by linarith [show (0 : ℝ) < t from ht])
  have hνω : logReferenceLevyDensity t ≤ archLevyDensity t := by
    have h := archLogRemainder_nonneg ht
    simp only [archLogRemainder] at h
    linarith
  have hI : 0 ≤ ∫ v, (W v - W (v + t)) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [hn t, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hν.le hI)]
  exact mul_le_mul_of_nonneg_right hνω hI

/-! ### Real coordinates of a complex test -/

/-- A real coordinate `p` of the reflected test `v ↦ f(−A − v)`, carried by `[−2A, 0)`. -/
def reflectedPart (A : ℝ) (p : ℂ →L[ℝ] ℝ) (f : ℝ → ℂ) (v : ℝ) : ℝ :=
  (Ico (-(2 * A)) 0).indicator (fun v => p (f (-A - v))) v

private theorem ae_reflectedPart_eq {A : ℝ} {f : ℝ → ℂ}
    (hf : ∀ᵐ x ∂volume, x ∉ Icc (-A) A → f x = 0) (p : ℂ →L[ℝ] ℝ) :
    ∀ᵐ v ∂volume, reflectedPart A p f v = p (f (-A - v)) := by
  have h0 : ∀ᵐ v : ℝ, v ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [ae_reflect hf (-A), h0] with v hv hv0
  by_cases hI : v ∈ Ico (-(2 * A)) 0
  · rw [reflectedPart, Set.indicator_of_mem hI]
  · have hx : -A - v ∉ Icc (-A) A := by
      intro hm
      exact hI ⟨by linarith [hm.2], lt_of_le_of_ne (by linarith [hm.1]) hv0⟩
    rw [reflectedPart, Set.indicator_of_notMem hI, hv hx, map_zero]

private theorem ae_eq_reflectedParts {A : ℝ} {f : ℝ → ℂ}
    (hf : ∀ᵐ x ∂volume, x ∉ Icc (-A) A → f x = 0) :
    ∀ᵐ v ∂volume, f (-A - v) =
      (reflectedPart A reCLM f v : ℂ) + (reflectedPart A imCLM f v : ℂ) * I := by
  filter_upwards [ae_reflectedPart_eq hf reCLM, ae_reflectedPart_eq hf imCLM] with v h1 h2
  rw [h1, h2, reCLM_apply, imCLM_apply, re_add_im]

/-- **The real coordinates of a complex test are tests of the energy domain.** A test of finite
logarithmic energy carried by the window has square-integrable jumps; its coordinates have the
smaller jumps, so finite Lévy energy and hence finite Gamma energy. -/
theorem reflectedPart_mem_domain {a : SuzukiPositiveAperture} (f : suzukiApertureHilbert a)
    (hf : HasLogarithmicEnergy (f : SoninL2)) (p : ℂ →L[ℝ] ℝ) (hp : ∀ z, |p z| ≤ ‖z‖) :
    CriticalHalfLineEnergyDomain (reflectedPart a.1 p (f : SoninL2)) ∧
      ∀ v, reflectedPart a.1 p (f : SoninL2) v ≠ 0 → v ∈ Icc (-(2 * a.1)) 0 := by
  obtain ⟨A, hA⟩ := a
  have hfm : Measurable ((f : SoninL2) : ℝ → ℂ) := (Lp.stronglyMeasurable _).measurable
  have hRm : MemLp (fun v => ((f : SoninL2) : ℝ → ℂ) (-A - v)) 2 volume :=
    (Lp.memLp (f : SoninL2)).comp_measurePreserving (Measure.measurePreserving_sub_left volume (-A))
  have hR2 : Integrable fun v => ‖((f : SoninL2) : ℝ → ℂ) (-A - v)‖ ^ 2 :=
    hRm.integrable_norm_pow (by norm_num)
  set G := reflectedPart A p (f : SoninL2) with hGdef
  have hGm : Measurable G :=
    (p.continuous.measurable.comp (hfm.comp (measurable_const.sub measurable_id))).indicator
      measurableSet_Ico
  have hGle : ∀ v, |G v| ≤ ‖((f : SoninL2) : ℝ → ℂ) (-A - v)‖ := fun v => by
    by_cases hv : v ∈ Ico (-(2 * A)) 0
    · rw [hGdef, reflectedPart, Set.indicator_of_mem hv]; exact hp _
    · rw [hGdef, reflectedPart, Set.indicator_of_notMem hv, abs_zero]; exact norm_nonneg _
  have hGz : ∀ v, v ∉ Ico (-(2 * A)) 0 → G v = 0 := fun v hv => by
    rw [hGdef, reflectedPart, Set.indicator_of_notMem hv]
  have hG2 : Integrable fun v => G v ^ 2 := by
    refine hR2.mono' (hGm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hGle v) 2
  have hone : Integrable ((Ico (-(2 * A)) (0 : ℝ)).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Ico).mpr
      (integrableOn_const (hs := by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))
  have hG1 : Integrable G := by
    refine (hone.add hG2).mono' hGm.aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, Pi.add_apply]
    by_cases hv : v ∈ Ico (-(2 * A)) 0
    · rw [Set.indicator_of_mem hv]
      nlinarith [abs_nonneg (G v), sq_abs (G v)]
    · rw [Set.indicator_of_notMem hv, hGz v hv, abs_zero]; positivity
  have hsupp : ∀ v, 0 ≤ v → G v = 0 := fun v hv => hGz v fun h => (not_le.mpr h.2) hv
  have hexp : Integrable fun v => G v ^ 2 * Real.exp (-(8 * v)) := by
    refine (hG2.const_mul (Real.exp (16 * A))).mono'
      ((hGm.pow_const 2).mul (by fun_prop : Continuous fun v : ℝ =>
        Real.exp (-(8 * v))).measurable).aestronglyMeasurable (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    by_cases hv : v ∈ Ico (-(2 * A)) 0
    · have he : Real.exp (-(8 * v)) ≤ Real.exp (16 * A) := Real.exp_le_exp.mpr (by linarith [hv.1])
      calc G v ^ 2 * Real.exp (-(8 * v)) ≤ G v ^ 2 * Real.exp (16 * A) :=
            mul_le_mul_of_nonneg_left he (sq_nonneg _)
        _ = Real.exp (16 * A) * G v ^ 2 := mul_comm _ _
    · rw [hGz v hv]; simp
  -- the jumps of `G` are dominated by those of `f`
  have hdec := ae_reflectedPart_eq (ae_zero_of_mem_aperture f) p
  have hfc : ((f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (fun v => ((f : SoninL2) : ℝ → ℂ) (-A - v)) (-A - x) :=
    ae_of_all _ fun x => by simp only [sub_sub_cancel]
  have hjump : ∀ t, (∫ v, (G v - G (v + t)) ^ 2) ≤ ‖logTranslationCLM t (f : SoninL2) - f‖ ^ 2 := by
    intro t
    rw [norm_sq_jump_reflected (P := fun v => ((f : SoninL2) : ℝ → ℂ) (-A - v)) A t hfc]
    have hΔ : MemLp (fun v => ((f : SoninL2) : ℝ → ℂ) (-A - v) -
        ((f : SoninL2) : ℝ → ℂ) (-A - (v + t))) 2 volume :=
      hRm.sub (hRm.comp_measurePreserving (measurePreserving_add_right volume t))
    refine integral_mono_ae ?_ (hΔ.integrable_norm_pow (by norm_num)) ?_
    · have hGL : MemLp G 2 volume := (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).mpr hG2
      exact ((hGL.sub (hGL.comp_measurePreserving (measurePreserving_add_right volume t))).integrable_norm_pow
        (by norm_num)).congr (ae_of_all _ fun v => by simp [Real.norm_eq_abs, sq_abs])
    · have hdec2 : ∀ᵐ v ∂volume, reflectedPart A p (f : SoninL2) (v + t) =
          p (((f : SoninL2) : ℝ → ℂ) (-A - (v + t))) := ae_shift hdec t
      filter_upwards [hdec, hdec2] with v h1 h2
      have hd : G v - G (v + t) = p (((f : SoninL2) : ℝ → ℂ) (-A - v) -
          ((f : SoninL2) : ℝ → ℂ) (-A - (v + t))) := by
        rw [map_sub, ← h1, ← h2]
      rw [hd, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hp _) 2
  have hfj := (hasLogarithmicEnergy_iff_integrable_jump _).mp hf
  have hnorm : ∀ t, ‖logTranslationCLM t (f : SoninL2) - f‖ ≤ 2 * ‖(f : SoninL2)‖ := fun t => by
    have hiso : ‖logTranslationCLM t (f : SoninL2)‖ = ‖(f : SoninL2)‖ :=
      (MellinL2.additiveTranslationUnitary t).norm_map _
    linarith [norm_sub_le (logTranslationCLM t (f : SoninL2)) (f : SoninL2)]
  have hmaj : IntegrableOn (fun t => logReferenceLevyDensity t *
      ‖logTranslationCLM t (f : SoninL2) - f‖ ^ 2 +
        archLogRemainder t * (2 * ‖(f : SoninL2)‖) ^ 2) (Ioi 0) :=
    hfj.add (integrableOn_archLogRemainder.mul_const _)
  have hlev : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
      ∫ u, (G u - G (u + x)) ^ 2)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (Integrable.lintegral_lt_top hmaj).ne (lintegral_mono_ae ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    refine ENNReal.ofReal_le_ofReal ?_
    have hr := archLogRemainder_nonneg ht
    have hν : 0 ≤ logReferenceLevyDensity t := by
      show 0 ≤ Real.exp (-t) / (2 * t)
      exact div_nonneg (Real.exp_pos _).le (by linarith [show (0 : ℝ) < t from ht])
    have hω : archLevyDensity t = logReferenceLevyDensity t + archLogRemainder t := by
      simp only [archLogRemainder]; ring
    have hj := hjump t
    have hn := pow_le_pow_left₀ (norm_nonneg _) (hnorm t) 2
    rw [hω, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hj hν)
      (mul_le_mul_of_nonneg_left (hj.trans hn) hr)
  refine ⟨⟨hGm, hG1, hG2, hexp, hsupp, integrable_gamma_of_lintegral_levy_ne_top hG1 hG2 hlev⟩,
    fun v hv => ?_⟩
  by_contra hvI
  exact hv (hGz v fun h => hvI (Ico_subset_Icc_self h))

/-! ### The window equation in logarithmic form -/

private theorem integral_real_mul_parts {P Gr Gi : ℝ → ℝ} {Gh : ℝ → ℂ}
    (hdec : ∀ᵐ v ∂volume, Gh v = (Gr v : ℂ) + (Gi v : ℂ) * I)
    (hr : Integrable fun v => Gr v * P v) (hi : Integrable fun v => Gi v * P v) :
    ∫ v, (P v : ℂ) * Gh v = ((∫ v, Gr v * P v : ℝ) : ℂ) + ((∫ v, Gi v * P v : ℝ) : ℂ) * I := by
  calc ∫ v, (P v : ℂ) * Gh v = ∫ v, (((Gr v * P v : ℝ) : ℂ) + ((Gi v * P v : ℝ) : ℂ) * I) :=
        integral_congr_ae (hdec.mono fun v hv => by
          show (P v : ℂ) * Gh v = _
          rw [hv]; push_cast; ring)
    _ = _ := by
        have h1 : Integrable fun v => ((Gr v * P v : ℝ) : ℂ) := hr.ofReal
        have h2 : Integrable fun v => ((Gi v * P v : ℝ) : ℂ) * I := hi.ofReal.mul_const I
        rw [integral_add h1 h2, integral_mul_const, integral_complex_ofReal,
          integral_complex_ofReal]

/-- **The reflected cut profile solves the logarithmic window equation.** If a bounded profile `W`
of the energy domain satisfies the half-line identity with forcing `φ` for every test carried by
`[−2A, 0]`, its reflected vector satisfies `E(f, u) = ⟨f, g⟩` for every finite-energy `f` of the
window `[−A, A]`, `g` the reflected forcing. -/
theorem logarithmicFullForm_reflected_cut_eq {A : ℝ} (hA : 0 < A) {W φ : ℝ → ℝ}
    (hWd : CriticalHalfLineEnergyDomain W) {C : ℝ} (hWb : ∀ᵐ u, |W u| ≤ C)
    (hφ : MemLp φ 2 volume)
    (heq : ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
      (∀ y, G y ≠ 0 → y ∈ Icc (-(2 * A)) 0) →
        (∫ u, G u * W u) + (∫ t in Ioi 0, logReferenceLevyDensity t *
          ∫ u, (G u - G (u + t)) * (W u - W (u + t))) = ∫ u, G u * φ u)
    (f : suzukiApertureHilbert ⟨A, hA⟩) (hf : HasLogarithmicEnergy (f : SoninL2)) :
    logarithmicFullForm (f : SoninL2) (reflectedWindowVector A hWd.memLp_real) =
      inner ℂ (f : SoninL2) (reflectedWindowVector A hφ) := by
  have huc := reflectedWindowVector_coeFn A hWd.memLp_real
  have hgc := reflectedWindowVector_coeFn A hφ
  have hu := hasLogarithmicEnergy_reflectedWindowVector A hWd
  have hfc : ((f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (fun v => ((f : SoninL2) : ℝ → ℂ) (-A - v)) (-A - x) :=
    ae_of_all _ fun x => by simp only [sub_sub_cancel]
  have hdec := ae_eq_reflectedParts (ae_zero_of_mem_aperture f)
  obtain ⟨hGr, hGrA⟩ := reflectedPart_mem_domain f hf reCLM fun z => abs_re_le_norm z
  obtain ⟨hGi, hGiA⟩ := reflectedPart_mem_domain f hf imCLM fun z => abs_im_le_norm z
  set Gr := reflectedPart A reCLM (f : SoninL2)
  set Gi := reflectedPart A imCLM (f : SoninL2)
  have hWm := hWd.memLp_real
  -- the pairing with the profile
  have hin : inner ℂ (reflectedWindowVector A hWd.memLp_real) (f : SoninL2) =
      ((∫ v, Gr v * W v : ℝ) : ℂ) + ((∫ v, Gi v * W v : ℝ) : ℂ) * I := by
    rw [inner_reflected_eq (Q := fun v => ((f : SoninL2) : ℝ → ℂ) (-A - v)) A huc hfc]
    exact integral_real_mul_parts hdec (integrable_mul_of_memLp hGr.memLp_real hWm)
      (integrable_mul_of_memLp hGi.memLp_real hWm)
  -- the pairing with the forcing
  have hing : inner ℂ (reflectedWindowVector A hφ) (f : SoninL2) =
      ((∫ v, Gr v * φ v : ℝ) : ℂ) + ((∫ v, Gi v * φ v : ℝ) : ℂ) * I := by
    rw [inner_reflected_eq (Q := fun v => ((f : SoninL2) : ℝ → ℂ) (-A - v)) A hgc hfc]
    exact integral_real_mul_parts hdec (integrable_mul_of_memLp hGr.memLp_real hφ)
      (integrable_mul_of_memLp hGi.memLp_real hφ)
  -- the jump pairing at each lag
  have hjt : ∀ t, inner ℂ (logTranslationCLM t (reflectedWindowVector A hWd.memLp_real) -
        reflectedWindowVector A hWd.memLp_real) (logTranslationCLM t (f : SoninL2) - f) =
      ((∫ v, (Gr v - Gr (v + t)) * (W v - W (v + t)) : ℝ) : ℂ) +
        ((∫ v, (Gi v - Gi (v + t)) * (W v - W (v + t)) : ℝ) : ℂ) * I := by
    intro t
    rw [inner_jump_reflected (P := fun v => ((W v : ℝ) : ℂ))
      (Q := fun v => ((f : SoninL2) : ℝ → ℂ) (-A - v)) A t huc hfc]
    have hdec2 : ∀ᵐ v ∂volume, ((f : SoninL2) : ℝ → ℂ) (-A - (v + t)) =
        (Gr (v + t) : ℂ) + (Gi (v + t) : ℂ) * I := ae_shift hdec t
    have hdec' : ∀ᵐ v ∂volume, ((f : SoninL2) : ℝ → ℂ) (-A - v) -
        ((f : SoninL2) : ℝ → ℂ) (-A - (v + t)) =
          ((Gr v - Gr (v + t) : ℝ) : ℂ) + ((Gi v - Gi (v + t) : ℝ) : ℂ) * I := by
      filter_upwards [hdec, hdec2] with v h1 h2
      rw [h1, h2]; push_cast; ring
    have hWt : MemLp (fun v => W v - W (v + t)) 2 volume :=
      hWm.sub (hWm.comp_measurePreserving (measurePreserving_add_right volume t))
    have hGrt : MemLp (fun v => Gr v - Gr (v + t)) 2 volume :=
      hGr.memLp_real.sub (hGr.memLp_real.comp_measurePreserving (measurePreserving_add_right volume t))
    have hGit : MemLp (fun v => Gi v - Gi (v + t)) 2 volume :=
      hGi.memLp_real.sub (hGi.memLp_real.comp_measurePreserving (measurePreserving_add_right volume t))
    refine (integral_congr_ae (ae_of_all _ fun v => ?_)).trans
      (integral_real_mul_parts hdec' (integrable_mul_of_memLp hGrt hWt)
        (integrable_mul_of_memLp hGit hWt))
    simp only [← Complex.ofReal_sub, Complex.conj_ofReal]
  -- the logarithmic jump integrals
  have hνint : ∀ {G : ℝ → ℝ}, CriticalHalfLineEnergyDomain G →
      IntegrableOn (fun t => logReferenceLevyDensity t *
        ∫ v, (G v - G (v + t)) * (W v - W (v + t))) (Ioi 0) := fun {G} hG => by
    refine ((integrableOn_levyMixedIntegrand hG hWd).sub (integral_archLogRemainder_jump hG.meas
      hG.integrable hG.memLp_real hWd.meas hWm hWb).1).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, archLogRemainder]; ring
  have hjump_int : (∫ t in Ioi 0, (logReferenceLevyDensity t : ℂ) *
      inner ℂ (logTranslationCLM t (reflectedWindowVector A hWd.memLp_real) -
        reflectedWindowVector A hWd.memLp_real) (logTranslationCLM t (f : SoninL2) - f)) =
      ((∫ t in Ioi 0, logReferenceLevyDensity t *
          ∫ v, (Gr v - Gr (v + t)) * (W v - W (v + t)) : ℝ) : ℂ) +
        ((∫ t in Ioi 0, logReferenceLevyDensity t *
          ∫ v, (Gi v - Gi (v + t)) * (W v - W (v + t)) : ℝ) : ℂ) * I := by
    calc _ = ∫ t in Ioi 0, (((logReferenceLevyDensity t *
            ∫ v, (Gr v - Gr (v + t)) * (W v - W (v + t)) : ℝ) : ℂ) +
          ((logReferenceLevyDensity t *
            ∫ v, (Gi v - Gi (v + t)) * (W v - W (v + t)) : ℝ) : ℂ) * I) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          rw [hjt t]; push_cast; ring
      _ = _ := by
          have h1 : Integrable (fun t => ((logReferenceLevyDensity t *
              ∫ v, (Gr v - Gr (v + t)) * (W v - W (v + t)) : ℝ) : ℂ)) (volume.restrict (Ioi 0)) :=
            Integrable.ofReal (hνint hGr)
          have h2 : Integrable (fun t => ((logReferenceLevyDensity t *
              ∫ v, (Gi v - Gi (v + t)) * (W v - W (v + t)) : ℝ) : ℂ) * I)
              (volume.restrict (Ioi 0)) :=
            (Integrable.ofReal (hνint hGi)).mul_const I
          rw [integral_add h1 h2, integral_mul_const, integral_complex_ofReal,
            integral_complex_ofReal]
  have key : logarithmicFullForm (reflectedWindowVector A hWd.memLp_real) (f : SoninL2) =
      inner ℂ (reflectedWindowVector A hφ) (f : SoninL2) := by
    rw [logarithmicFullForm_eq_inner_add_jump hu hf, hin, hjump_int, hing,
      ← heq Gr hGr hGrA, ← heq Gi hGi hGiA]
    push_cast; ring
  rw [← logarithmicFullForm_conj, key, ← inner_conj_symm (f : SoninL2)]
  rfl

/-! ### Continuity near the wall -/

/-- The left-edge representation of the reflected cut state gives the state on ¦[−A, 0)¦. -/
private theorem ae_state_eq_of_rep {A : ℝ} (hA : 0 < A) {F : ℝ → ℝ} {u : SoninL2} {Ψ : ℝ → ℂ}
    (hu : (u : ℝ → ℂ) =ᵐ[volume]
      fun x => (((wallWindowCutoff A (-A - x) * F (-A - x)) : ℝ) : ℂ))
    (hrep : ∀ᵐ x ∂volume, x ≤ 0 → (u : ℝ → ℂ) x = Ψ (x + A)) :
    ∀ᵐ v ∂volume, -A ≤ v → ((F v : ℝ) : ℂ) = Ψ (-v) := by
  have h1 : ∀ᵐ v ∂volume, -A - v ≤ 0 → (u : ℝ → ℂ) (-A - v) = Ψ (-A - v + A) :=
    ae_reflect hrep (-A)
  have h2 : ∀ᵐ v ∂volume, (u : ℝ → ℂ) (-A - v) =
      (((wallWindowCutoff A (-A - (-A - v)) * F (-A - (-A - v))) : ℝ) : ℂ) :=
    ae_reflect hu (-A)
  filter_upwards [h1, h2] with v hv1 hv2 hv
  have e := hv2.symm.trans (hv1 (by linarith))
  rw [sub_sub_cancel, show -A - v + A = -v by ring, wallWindowCutoff_of_ge hA hv, one_mul] at e
  exact e

/-- **The state is continuous up to the wall on every window.** For every `A > 0` there is a
continuous `Ψ` with `F(v) = Ψ(−v)` for almost every `v ≥ −A`, and `Ψ(t) √log(1/t)` converges as
`t → 0⁺`. -/
theorem criticalState_exists_continuous_near_wall {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {A : ℝ} (hA : 0 < A) :
    ∃ Ψ : ℝ → ℂ, Continuous Ψ ∧ (∀ᵐ v ∂volume, -A ≤ v → ((F v : ℝ) : ℂ) = Ψ (-v)) ∧
      ∃ L : ℂ, Tendsto (fun t : ℝ => Ψ t * (Real.sqrt (Real.log (1 / t)) : ℂ)) (𝓝[>] 0)
        (𝓝 L) := by
  have hFd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨C, hC, hCe⟩ := criticalState_ae_abs_le_exp hW hthreshold hF
  have hCb := ae_abs_le_of_abs_le_exp hC hFd.support hCe
  have hχm := measurable_wallWindowCutoff A
  have hWd := criticalHalfLineEnergyDomain_lipschitz_mul hFd hχm (abs_wallWindowCutoff_le A)
    (abs_wallWindowCutoff_sub_le hA)
  have hWb : ∀ᵐ u, |wallWindowCutoff A u * F u| ≤ C := hCb.mono fun u hu => by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (abs_wallWindowCutoff_le A u)).trans hu
  obtain ⟨⟨K, hK⟩, heq⟩ := criticalState_cut_logarithmic_equation hW hthreshold hF hA
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ → ℝ,
      φ = (Icc (-(2 * A)) 0).indicator (cutForcing W₀ (wallWindowCutoff A) F) := ⟨_, rfl⟩
  have hφA : ∀ v, v ∉ Icc (-(2 * A)) 0 → φ v = 0 := fun v hv => by
    rw [hφdef, Set.indicator_of_notMem hv]
  have hφb : ∀ᵐ y, |φ y| ≤ max K 0 := by
    filter_upwards [hK] with y hy
    by_cases hyI : y ∈ Icc (-(2 * A)) 0
    · rw [hφdef, Set.indicator_of_mem hyI]; exact (hy hyI).trans (le_max_left _ _)
    · rw [hφA y hyI, abs_zero]; exact le_max_right _ _
  haveI : IsFiniteMeasure (volume.restrict (Icc (-(2 * A)) (0 : ℝ))) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hφ2 : MemLp φ 2 volume := by
    rw [hφdef]
    exact (memLp_indicator_iff_restrict measurableSet_Icc).mpr
      (MemLp.of_bound (measurable_cutForcing hχm hFd.meas).aestronglyMeasurable K
        ((ae_restrict_iff' measurableSet_Icc).mpr
          (hK.mono fun y hy hyI => (Real.norm_eq_abs _).trans_le (hy hyI))))
  have heq' : ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
      (∀ y, G y ≠ 0 → y ∈ Icc (-(2 * A)) 0) →
        (∫ u, G u * (wallWindowCutoff A u * F u)) + (∫ t in Ioi 0, logReferenceLevyDensity t *
          ∫ u, (G u - G (u + t)) * (wallWindowCutoff A u * F u -
            wallWindowCutoff A (u + t) * F (u + t))) = ∫ u, G u * φ u := by
    intro G hG hGA
    rw [heq G hG hGA]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show G y * cutForcing W₀ (wallWindowCutoff A) F y = G y * φ y
    by_cases hyI : y ∈ Icc (-(2 * A)) 0
    · rw [hφdef, Set.indicator_of_mem hyI]
    · have hG0 : G y = 0 := by by_contra h; exact hyI (hGA y h)
      rw [hG0, zero_mul, zero_mul]
  have huc := reflectedWindowVector_coeFn A hWd.memLp_real
  have hgc := reflectedWindowVector_coeFn A hφ2
  have huA : reflectedWindowVector A hWd.memLp_real ∈ suzukiApertureHilbert ⟨A, hA⟩ := by
    refine mem_aperture_of_ae ?_
    filter_upwards [huc] with x hx hxI
    rw [hx]
    simp only [centralInterval, Set.mem_Icc, not_and_or, not_le] at hxI
    rcases hxI with h | h
    · rw [hFd.support _ (by linarith), mul_zero, Complex.ofReal_zero]
    · rw [wallWindowCutoff_of_le hA (by linarith), zero_mul, Complex.ofReal_zero]
  have hgA : reflectedWindowVector A hφ2 ∈ suzukiApertureHilbert ⟨A, hA⟩ := by
    refine mem_aperture_of_ae ?_
    filter_upwards [hgc] with x hx hxI
    rw [hx, hφA, Complex.ofReal_zero]
    intro hm
    simp only [centralInterval, Set.mem_Icc] at hxI
    exact hxI ⟨by linarith [hm.2], by linarith [hm.1]⟩
  let u : suzukiApertureHilbert ⟨A, hA⟩ := ⟨_, huA⟩
  let g : suzukiApertureHilbert ⟨A, hA⟩ := ⟨_, hgA⟩
  have hub : ∀ᵐ x ∂volume, ‖((u : SoninL2) : ℝ → ℂ) x‖ ≤ C := by
    have h := ae_reflect hWb (-A)
    filter_upwards [huc, h] with x hx hb
    show ‖(reflectedWindowVector A hWd.memLp_real : ℝ → ℂ) x‖ ≤ C
    rw [hx, Complex.norm_real, Real.norm_eq_abs]
    exact hb
  have hgb : ∀ᵐ x ∂volume, ‖((g : SoninL2) : ℝ → ℂ) x‖ ≤ max K 0 := by
    have h := ae_reflect hφb (-A)
    filter_upwards [hgc, h] with x hx hb
    show ‖(reflectedWindowVector A hφ2 : ℝ → ℂ) x‖ ≤ max K 0
    rw [hx, Complex.norm_real, Real.norm_eq_abs]
    exact hb
  obtain ⟨hcont, hrep, hlim⟩ := left_edge_of_bounded ⟨A, hA⟩ u g
    (hasLogarithmicEnergy_reflectedWindowVector A hWd)
    (fun f hf => logarithmicFullForm_reflected_cut_eq hA hWd hWb hφ2 heq' f hf) hC hub
    (le_max_right K 0) hgb
  exact ⟨_, hcont, ae_state_eq_of_rep hA huc hrep, _, hlim⟩

/-! ### The pointwise law at the wall -/

/-- `|√L φ − √T φ| ≤ |√T φ| (T − L)/T` for `0 < L ≤ T`. -/
private theorem abs_sqrt_mul_sub_le {L T φ : ℝ} (hL : 0 < L) (hLT : L ≤ T) :
    |Real.sqrt L * φ - Real.sqrt T * φ| ≤ |Real.sqrt T * φ| * ((T - L) / T) := by
  have hT : 0 < T := hL.trans_le hLT
  have hr := Real.sqrt_pos.mpr hL
  have hs := Real.sqrt_pos.mpr hT
  have hrs : Real.sqrt L ≤ Real.sqrt T := Real.sqrt_le_sqrt hLT
  have e1 : Real.sqrt T * L = Real.sqrt L ^ 2 * Real.sqrt T := by rw [Real.sq_sqrt hL.le]; ring
  have e2 : Real.sqrt L * T = Real.sqrt T ^ 2 * Real.sqrt L := by rw [Real.sq_sqrt hT.le]; ring
  have key : Real.sqrt T * L ≤ Real.sqrt L * T := by
    nlinarith [mul_nonneg (mul_nonneg hr.le hs.le) (sub_nonneg.mpr hrs)]
  have hk : Real.sqrt T - Real.sqrt L ≤ Real.sqrt T * ((T - L) / T) := by
    rw [mul_div_assoc', le_div_iff₀ hT]; linarith
  rw [← sub_mul, abs_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr hrs), abs_of_pos hs]
  nlinarith [abs_nonneg φ]

/-- A pointwise limit at the wall agrees with a limit in measure. -/
private theorem eq_of_tendsto_of_inMeasure {F Φ : ℝ → ℝ} {ℓ c : ℝ}
    (hΦ : Tendsto (fun t : ℝ => Φ (-t) * Real.sqrt (Real.log (1 / t))) (𝓝[>] 0) (𝓝 ℓ))
    (hae : ∀ᵐ u ∂volume, u ∈ Ioo (-1) 0 → F u = Φ u)
    (hmeas : ∀ δ : ℝ, 0 < δ → Tendsto (fun k : ℝ => volume.real (Ioo (-k) 0 ∩
      {u | δ ≤ |Real.sqrt (Real.log (1 / k)) * F u - c|}) / k) (𝓝[>] 0) (𝓝 0)) : ℓ = c := by
  by_contra hne
  have hδ : 0 < |ℓ - c| / 4 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
  set δ := |ℓ - c| / 4 with hδdef
  have hL : Tendsto (fun k : ℝ => Real.log (1 / k)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have h1 : ∀ᶠ k in 𝓝[>] (0 : ℝ), (|ℓ| + δ) * Real.log 2 / Real.log (1 / k) < δ :=
    (tendsto_const_nhds.div_atTop hL).eventually (gt_mem_nhds hδ)
  have h2 : ∀ᶠ k in 𝓝[>] (0 : ℝ), volume.real (Ioo (-k) 0 ∩
      {u | δ ≤ |Real.sqrt (Real.log (1 / k)) * F u - c|}) / k < 1 / 2 :=
    (hmeas δ hδ).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨k₁, hk₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hΦ.eventually (Metric.ball_mem_nhds ℓ hδ))
  have h3 : ∀ᶠ k in 𝓝[>] (0 : ℝ), k ∈ Ioo 0 (min k₁ (1 / 2)) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr
      ⟨min k₁ (1 / 2), Set.mem_Ioi.mpr (lt_min hk₁ (by norm_num)), subset_rfl⟩
  obtain ⟨k, hk1, hk2, hk3⟩ := (h1.and (h2.and h3)).exists
  have hk0 : 0 < k := hk3.1
  have hkk₁ : k < k₁ := hk3.2.trans_le (min_le_left _ _)
  have hkh : k < 1 / 2 := hk3.2.trans_le (min_le_right _ _)
  set B := Ioo (-k) 0 ∩ {u | δ ≤ |Real.sqrt (Real.log (1 / k)) * F u - c|}
  set N := {u : ℝ | ¬ (u ∈ Ioo (-1) 0 → F u = Φ u)}
  have hN : volume N = 0 := ae_iff.mp hae
  have hBfin : volume B ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_left)
  have hBlt : volume B < ENNReal.ofReal (k / 2) := by
    have hreal : volume.real B < k / 2 := by
      have := (div_lt_iff₀ hk0).mp hk2; linarith
    rw [← ENNReal.ofReal_toReal hBfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hreal
  have hS : volume (Ioo (-k) (-k / 2)) = ENNReal.ofReal (k / 2) := by
    rw [Real.volume_Ioo]; congr 1; ring
  have hnot : ¬ Ioo (-k) (-k / 2) ⊆ B ∪ N := by
    intro hsubset
    have := (measure_mono (μ := volume) hsubset).trans (measure_union_le (μ := volume) B N)
    rw [hN, add_zero, hS] at this
    exact absurd hBlt (not_lt.mpr this)
  obtain ⟨u, huS, huBN⟩ := Set.not_subset.mp hnot
  have huB : u ∉ B := fun h => huBN (Or.inl h)
  have huN : u ∉ N := fun h => huBN (Or.inr h)
  have huI : u ∈ Ioo (-1) 0 := ⟨by linarith [huS.1], by linarith [huS.2]⟩
  have hFu : F u = Φ u := by
    by_contra h; exact huN fun h' => h (h' huI)
  have hgood : |Real.sqrt (Real.log (1 / k)) * F u - c| < δ := by
    by_contra h; exact huB ⟨⟨huS.1, by linarith [huS.2]⟩, not_lt.mp h⟩
  set t := -u
  have ht0 : 0 < t := by linarith [huS.2]
  have htk : t < k := by linarith [huS.1]
  have htk2 : k / 2 < t := by linarith [huS.2]
  have hX : |Φ (-t) * Real.sqrt (Real.log (1 / t)) - ℓ| < δ := by
    have := hsub ⟨ht0, htk.trans hkk₁⟩
    simpa [Metric.mem_ball, Real.dist_eq] using this
  have hΦt : Φ (-t) = Φ u := by simp [t]
  rw [hΦt] at hX
  -- the logarithms at the two scales
  have hLk : 0 < Real.log (1 / k) := Real.log_pos (by rw [lt_div_iff₀ hk0]; linarith)
  have hLT : Real.log (1 / k) ≤ Real.log (1 / t) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le ht0 htk.le)
  have hTL : Real.log (1 / t) - Real.log (1 / k) ≤ Real.log 2 := by
    have : 1 / t ≤ 2 * (1 / k) := by
      rw [div_le_iff₀ ht0]; field_simp; linarith
    have h := Real.log_le_log (by positivity) this
    rw [Real.log_mul (by norm_num) (by positivity)] at h
    linarith
  have hratio : (Real.log (1 / t) - Real.log (1 / k)) / Real.log (1 / t) ≤
      Real.log 2 / Real.log (1 / k) := by
    rw [div_le_div_iff₀ (hLk.trans_le hLT) hLk]
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
  have hcmp := abs_sqrt_mul_sub_le (φ := Φ u) hLk hLT
  have hXb : |Real.sqrt (Real.log (1 / t)) * Φ u| ≤ |ℓ| + δ := by
    rw [mul_comm]
    have := abs_sub_abs_le_abs_sub (Φ u * Real.sqrt (Real.log (1 / t))) ℓ
    linarith
  have hclose : |Real.sqrt (Real.log (1 / k)) * Φ u - Real.sqrt (Real.log (1 / t)) * Φ u| < δ :=
    calc _ ≤ |Real.sqrt (Real.log (1 / t)) * Φ u| *
          ((Real.log (1 / t) - Real.log (1 / k)) / Real.log (1 / t)) := hcmp
      _ ≤ (|ℓ| + δ) * (Real.log 2 / Real.log (1 / k)) :=
          mul_le_mul hXb hratio (div_nonneg (by linarith) (hLk.trans_le hLT).le)
            (by positivity)
      _ = (|ℓ| + δ) * Real.log 2 / Real.log (1 / k) := by ring
      _ < δ := hk1
  rw [hFu] at hgood
  have htri : |ℓ - c| ≤ |ℓ - Φ u * Real.sqrt (Real.log (1 / t))| +
      |Real.sqrt (Real.log (1 / t)) * Φ u - Real.sqrt (Real.log (1 / k)) * Φ u| +
      |Real.sqrt (Real.log (1 / k)) * Φ u - c| := by
    have e : ℓ - c = (ℓ - Φ u * Real.sqrt (Real.log (1 / t))) +
        (Real.sqrt (Real.log (1 / t)) * Φ u - Real.sqrt (Real.log (1 / k)) * Φ u) +
        (Real.sqrt (Real.log (1 / k)) * Φ u - c) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_sub_comm ℓ (Φ u * Real.sqrt (Real.log (1 / t))),
    abs_sub_comm (Real.sqrt (Real.log (1 / t)) * Φ u)] at htri
  have : |ℓ - c| < 4 * δ := by linarith
  rw [hδdef] at this
  linarith

/-- **E-M10: the critical state is continuous, with a pointwise law at the wall.** The state has a
representative `Φ` continuous on `u < 0`; with `a = a(W₀)`, `M = ∫ F² e^{−8u}` and the sign `s` of
the wall, `Φ(−t) √log(1/t) → s √(8aM)` and `Φ(−t)² log(1/t) → 8aM` as `t → 0⁺`, and `Φ` has the
sign `s` on a full interval `(−k₀, 0)`. -/
theorem criticalState_continuous_pointwise_wall_law {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ Φ : ℝ → ℝ, ContinuousOn Φ (Iio 0) ∧ F =ᵐ[volume] Φ ∧
      Tendsto (fun t : ℝ => Φ (-t) * Real.sqrt (Real.log (1 / t))) (𝓝[>] 0)
        (𝓝 (s * Real.sqrt (8 * criticalAliasCoefficient W₀ *
          ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))))) ∧
      Tendsto (fun t : ℝ => Φ (-t) ^ 2 * Real.log (1 / t)) (𝓝[>] 0)
        (𝓝 (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) ∧
      ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ t ∈ Ioo 0 k₀, 0 < s * Φ (-t) := by
  have hFd := criticalHalfLineEnergyDomain_of_groundState hF
  have hrep : ∀ n : ℕ, ∃ Ψ : ℝ → ℂ, Continuous Ψ ∧
      (∀ᵐ v ∂volume, -((n : ℝ) + 1) ≤ v → ((F v : ℝ) : ℂ) = Ψ (-v)) ∧
      ∃ L : ℂ, Tendsto (fun t : ℝ => Ψ t * (Real.sqrt (Real.log (1 / t)) : ℂ)) (𝓝[>] 0) (𝓝 L) :=
    fun n => criticalState_exists_continuous_near_wall hW hthreshold hF (by positivity)
  choose Ψ hΨc hΨe hΨL using hrep
  -- the windows agree on their overlaps
  have hagree : ∀ m n : ℕ, m ≤ n → ∀ u ∈ Ioo (-((m : ℝ) + 1)) 0,
      (Ψ m (-u)).re = (Ψ n (-u)).re := by
    intro m n hmn
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioo
      (Complex.continuous_re.comp ((hΨc m).comp continuous_neg)).continuousOn
      (Complex.continuous_re.comp ((hΨc n).comp continuous_neg)).continuousOn
    refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
    filter_upwards [hΨe m, hΨe n] with v h1 h2 hv
    have hmn' : ((m : ℝ)) ≤ n := by exact_mod_cast hmn
    have e := (h1 (by linarith [hv.1])).symm.trans (h2 (by linarith [hv.1, hmn']))
    exact congrArg Complex.re e
  -- the glued representative
  set Φ : ℝ → ℝ := fun u => if u < 0 then (Ψ ⌊-u⌋₊ (-u)).re else 0 with hΦdef
  have hΦwin : ∀ u, u < 0 → Φ u = (Ψ ⌊-u⌋₊ (-u)).re := fun u hu => by simp [hΦdef, hu]
  have hmem : ∀ u : ℝ, u < 0 → u ∈ Ioo (-(((⌊-u⌋₊ : ℕ) : ℝ) + 1)) 0 := fun u hu =>
    ⟨by linarith [Nat.lt_floor_add_one (-u)], hu⟩
  have hΦF : F =ᵐ[volume] Φ := by
    filter_upwards [ae_all_iff.mpr hΨe] with v hv
    by_cases hv0 : v < 0
    · rw [hΦwin v hv0]
      have e := hv ⌊-v⌋₊ (hmem v hv0).1.le
      have := congrArg Complex.re e
      rwa [Complex.ofReal_re] at this
    · rw [hFd.support v (not_lt.mp hv0)]; simp [hΦdef, hv0]
  have hΦc : ContinuousOn Φ (Iio 0) := by
    intro u₀ hu₀
    have hu₀' : u₀ < 0 := hu₀
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊-u₀⌋₊ + 1 := ⟨_, rfl⟩
    have hNr : (N : ℝ) = (⌊-u₀⌋₊ : ℝ) + 1 := by rw [hN]; push_cast; ring
    have hU : Ioo (-((N : ℝ))) 0 ∈ 𝓝 u₀ := isOpen_Ioo.mem_nhds
      ⟨by linarith [Nat.lt_floor_add_one (-u₀)], hu₀'⟩
    have heqU : (fun u => (Ψ N (-u)).re) =ᶠ[𝓝 u₀] Φ := by
      filter_upwards [hU] with u hu
      show (Ψ N (-u)).re = Φ u
      rw [hΦwin u hu.2]
      have hm : ⌊-u⌋₊ ≤ N :=
        ((Nat.floor_lt (by linarith [hu.2])).mpr (by linarith [hu.1])).le
      exact (hagree _ N hm u (hmem u hu.2)).symm
    exact ((Complex.continuous_re.comp ((hΨc N).comp continuous_neg)).continuousAt.congr
      heqU).continuousWithinAt
  -- the limit at the wall
  obtain ⟨L, hL⟩ := hΨL 0
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 1 :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨1, Set.mem_Ioi.mpr one_pos, subset_rfl⟩
  have hΦ0 : ∀ t ∈ Ioo (0 : ℝ) 1, Φ (-t) = (Ψ 0 t).re := fun t ht => by
    rw [hΦwin (-t) (by linarith [ht.1]), neg_neg, Nat.floor_eq_zero.mpr ht.2]
  have hℓ : Tendsto (fun t : ℝ => Φ (-t) * Real.sqrt (Real.log (1 / t))) (𝓝[>] 0) (𝓝 L.re) := by
    refine ((Complex.continuous_re.tendsto L).comp hL).congr' ?_
    filter_upwards [hnear] with t ht
    simp only [Function.comp_apply, Complex.re_mul_ofReal, hΦ0 t ht]
  obtain ⟨s, hs, -, -, hmeas, -⟩ := criticalState_meanSquare_wall_law hW hthreshold hF
  have hae : ∀ᵐ u ∂volume, u ∈ Ioo (-1) 0 → F u = Φ u := hΦF.mono fun u hu _ => hu
  have hid := eq_of_tendsto_of_inMeasure hℓ hae hmeas
  rw [hid] at hℓ
  have hQ : 0 < 8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) :=
    mul_pos (mul_pos (by norm_num) (criticalAliasCoefficient_positive hW))
      (criticalState_exponentialMass_pos hW hF)
  have hss : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  refine ⟨s, hs, Φ, hΦc, hΦF, hℓ, ?_, ?_⟩
  · have hsq := hℓ.pow 2
    rw [mul_pow, Real.sq_sqrt hQ.le, show s ^ 2 = s * s by ring, hss, one_mul] at hsq
    refine hsq.congr' ?_
    filter_upwards [hnear] with t ht
    show (Φ (-t) * Real.sqrt (Real.log (1 / t))) ^ 2 = Φ (-t) ^ 2 * Real.log (1 / t)
    rw [mul_pow, Real.sq_sqrt (Real.log_nonneg (by rw [le_div_iff₀ ht.1]; linarith [ht.2]))]
  · have hpos : Tendsto (fun t : ℝ => s * (Φ (-t) * Real.sqrt (Real.log (1 / t)))) (𝓝[>] 0)
        (𝓝 (s * (s * Real.sqrt (8 * criticalAliasCoefficient W₀ *
          ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))))) := hℓ.const_mul s
    rw [← mul_assoc, hss, one_mul] at hpos
    obtain ⟨k₀, hk₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
      ((hpos.eventually (lt_mem_nhds (Real.sqrt_pos.mpr hQ))).and hnear)
    refine ⟨k₀, hk₀, fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := hsub ht
    have hlog : 0 < Real.sqrt (Real.log (1 / t)) :=
      Real.sqrt_pos.mpr (Real.log_pos (by rw [lt_div_iff₀ h2.1]; linarith [h2.2]))
    have h1' : 0 < s * (Φ (-t) * Real.sqrt (Real.log (1 / t))) := h1
    nlinarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
