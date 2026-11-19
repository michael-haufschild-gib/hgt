import GaloisForLFunctions.BlackHoleRingdown.CuspEscapeAndMixedPulseInterference
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity

/-!
# Reflected Tail Energy, Polarization, and Failure of Huygens' Principle on the Modular Cusp

For a compactly supported smooth pulse `h` incident on the cusp of `PSL₂(ℤ)\ℍ`, the reflected
signal `r_h = pulseReflected h` carries late-time tail energy `E_h(T) = ∫_T^∞ ‖r_h(u)‖² du` and
Hermitian cross-energy `E_{g,h}(T) = ∫_T^∞ r_g(u) conj(r_h(u)) du`.

This module establishes:
1. **Linearity, Step Decrements, and Time Differentiation**: `E_h(T) - E_h(T + L) = ∫_T^{T+L} ‖r_h‖²`,
   `lim_{T → ∞} E_h(T) = 0`, and `E_h'(T) = -‖r_h(T)‖²`.
2. **Relative-Phase Modulation and Four-Phase Polarization**: Phase variation `g + e^{iφ} h`
   isolates `2 Re(e^{-iφ} E_{g,h}(T))`, opposite-phase averaging cancels interference identically,
   and four-phase polarization reconstructs `E_{g,h}(T)` and its finite-step decrement from scalar
   tail energies alone.
3. **Resonance Pole Obstruction and Strict Tail Positivity (`tailEnergy_pos`)**: Whenever `r_h`
   decays as `O(e^{-δ u})`, `pulseAmplitude h (-i p)` must vanish at every pole `p` of
   `scatteringPhase` with `-δ < Re p < 0`. Consequently, every nonzero `h : CompactPulse` satisfies
   `0 < E_h(T)` at every `T ∈ ℝ` (via Jensen's linear zero-count bound against Alpöge–Furman's
   superlinear simple-critical zero count), and every `ℂ`-linearly independent pair `(g, h)` has a
   strictly positive definite `2 × 2` tail-energy Gram matrix at every time `T`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform Classical

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

/-! ## 1. Reflected Tail Energy, Cross-Energy, and Step Decrements -/

/-- Late-time reflected cusp tail energy `E_h(T) = ∫_T^∞ ‖pulseReflected h u‖² du`. -/
def tailEnergy (h : ℝ → ℂ) (T : ℝ) : ℝ :=
  ∫ u in Ioi T, ‖pulseReflected h u‖ ^ 2

/-- Hermitian tail cross-energy `E_{g,h}(T) = ∫_T^∞ pulseReflected g u * conj(pulseReflected h u) du`. -/
def tailCrossEnergy (g h : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∫ u in Ioi T, pulseReflected g u * (starRingEnd ℂ) (pulseReflected h u)

/-- Reflected energy radiated during the propagation step `(T, T + L]`. -/
def stepDecrement (h : ℝ → ℂ) (T L : ℝ) : ℝ :=
  ∫ u in Ioc T (T + L), ‖pulseReflected h u‖ ^ 2

/-- Hermitian cross-decrement over the propagation step `(T, T + L]`. -/
def stepCrossDecrement (g h : ℝ → ℂ) (T L : ℝ) : ℂ :=
  ∫ u in Ioc T (T + L), pulseReflected g u * (starRingEnd ℂ) (pulseReflected h u)

/-- Superposition `g + e^{iφ} h` of two compact pulses at relative phase `φ`. -/
def CompactPulse.phaseMix (φ : ℝ) (g h : CompactPulse) : CompactPulse :=
  g.add (CompactPulse.smul (Complex.exp (I * (φ : ℂ))) h)

@[simp] theorem CompactPulse.phaseMix_apply (φ : ℝ) (g h : CompactPulse) (S : ℝ) :
    (CompactPulse.phaseMix φ g h) S = g S + Complex.exp (I * (φ : ℂ)) * h S := rfl

theorem pulseAmplitude_zero (w : ℂ) : pulseAmplitude CompactPulse.zero w = 0 := by
  simp [pulseAmplitude]

theorem pulseReflected_zero (u : ℝ) : pulseReflected CompactPulse.zero u = 0 := by
  simp [pulseReflected, pulseAmplitude_zero]

theorem pulseReflected_add (g h : CompactPulse) (u : ℝ) :
    pulseReflected (g.add h) u = pulseReflected g u + pulseReflected h u := by
  have hg := g.integrable_amplitude_mul continuous_scatteringPhase_line.measurable
    (fun ξ => (norm_scatteringPhase_line ξ).le) u
  have hh := h.integrable_amplitude_mul continuous_scatteringPhase_line.measurable
    (fun ξ => (norm_scatteringPhase_line ξ).le) u
  rw [pulseReflected, pulseReflected, pulseReflected, ← integral_add hg hh]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [pulseAmplitude_add]
  ring

theorem pulseReflected_smul (c : ℂ) (h : CompactPulse) (u : ℝ) :
    pulseReflected (CompactPulse.smul c h) u = c * pulseReflected h u := by
  rw [pulseReflected, pulseReflected, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [pulseAmplitude_smul]
  ring

theorem pulseReflected_delay (d : ℝ) (h : CompactPulse) (u : ℝ) :
    pulseReflected (h.delay d) u = pulseReflected h (u - d) := by
  rw [pulseReflected, pulseReflected]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [pulseAmplitude_delay]
  have hexp : Complex.exp (-(I * (ξ : ℂ) * (d : ℂ))) * Complex.exp (I * (ξ : ℂ) * (u : ℂ)) =
      Complex.exp (I * (ξ : ℂ) * ((u - d : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (pulseAmplitude h (ξ : ℂ) * scatteringPhase ((ξ : ℂ) * I)) * hexp

theorem pulseReflected_phaseMix (φ : ℝ) (g h : CompactPulse) (u : ℝ) :
    pulseReflected (CompactPulse.phaseMix φ g h) u =
      pulseReflected g u + Complex.exp (I * (φ : ℂ)) * pulseReflected h u := by
  rw [CompactPulse.phaseMix, pulseReflected_add, pulseReflected_smul]

theorem tailEnergy_nonneg (h : ℝ → ℂ) (T : ℝ) : 0 ≤ tailEnergy h T :=
  integral_nonneg fun _ => sq_nonneg _

theorem stepDecrement_nonneg (h : ℝ → ℂ) (T L : ℝ) : 0 ≤ stepDecrement h T L :=
  integral_nonneg fun _ => sq_nonneg _

theorem tailEnergy_sub_step (h : CompactPulse) (T : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    tailEnergy h T - tailEnergy h (T + L) = stepDecrement h T L := by
  have hint := integrable_norm_sq_pulseReflected h
  have hdisj : Disjoint (Ioc T (T + L)) (Ioi (T + L)) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => hx1.2.not_gt hx2
  have hunion : Ioc T (T + L) ∪ Ioi (T + L) = Ioi T := Ioc_union_Ioi_eq_Ioi (by linarith)
  have hsplit : (∫ u in Ioi T, ‖pulseReflected h u‖ ^ 2) =
      (∫ u in Ioc T (T + L), ‖pulseReflected h u‖ ^ 2) +
        ∫ u in Ioi (T + L), ‖pulseReflected h u‖ ^ 2 := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioi hint.integrableOn hint.integrableOn]
  unfold tailEnergy stepDecrement
  linarith

theorem tailCrossEnergy_sub_step (g h : CompactPulse) (T : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    tailCrossEnergy g h T - tailCrossEnergy g h (T + L) = stepCrossDecrement g h T L := by
  have hint := integrable_pulseReflected_mul_conj g h
  have hdisj : Disjoint (Ioc T (T + L)) (Ioi (T + L)) :=
    Set.disjoint_left.mpr fun _ hx1 hx2 => hx1.2.not_gt hx2
  have hunion : Ioc T (T + L) ∪ Ioi (T + L) = Ioi T := Ioc_union_Ioi_eq_Ioi (by linarith)
  have hsplit : (∫ u in Ioi T, pulseReflected g u * (starRingEnd ℂ) (pulseReflected h u)) =
      (∫ u in Ioc T (T + L), pulseReflected g u * (starRingEnd ℂ) (pulseReflected h u)) +
        ∫ u in Ioi (T + L), pulseReflected g u * (starRingEnd ℂ) (pulseReflected h u) := by
    rw [← hunion, setIntegral_union hdisj measurableSet_Ioi hint.integrableOn hint.integrableOn]
  unfold tailCrossEnergy stepCrossDecrement
  linear_combination hsplit

theorem tailEnergy_anti (h : CompactPulse) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    tailEnergy h T₂ ≤ tailEnergy h T₁ := by
  have hsub := tailEnergy_sub_step h T₁ (L := T₂ - T₁) (by linarith)
  rw [add_sub_cancel] at hsub
  linarith [stepDecrement_nonneg h T₁ (T₂ - T₁)]

theorem tailEnergy_le_initial (h : CompactPulse) (T : ℝ) :
    tailEnergy h T ≤ ∫ S : ℝ, ‖h S‖ ^ 2 := by
  have hint := integrable_norm_sq_pulseReflected h
  have hall := integral_add_compl (s := Ioi T) measurableSet_Ioi hint
  have hcompl : 0 ≤ ∫ u in (Ioi T)ᶜ, ‖pulseReflected h u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  rw [integral_norm_sq_pulseReflected h] at hall
  unfold tailEnergy
  linarith

/-- Late-time exhaustion `lim_{T → +∞} E_h(T) = 0` for every compact pulse `h`. -/
theorem tendsto_tailEnergy_atTop (h : CompactPulse) :
    Tendsto (tailEnergy h) atTop (𝓝 0) := by
  have hint := integrable_norm_sq_pulseReflected h
  have h0 : (0 : ℝ) = ∫ _u : ℝ, (0 : ℝ) := by simp
  rw [h0]
  have hdom : Tendsto (fun T : ℝ => ∫ u : ℝ,
      (Ioi T).indicator (fun u => ‖pulseReflected h u‖ ^ 2) u) atTop
      (𝓝 (∫ _u : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => ‖pulseReflected h u‖ ^ 2) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun T =>
        (hint.indicator measurableSet_Ioi).aestronglyMeasurable
    · refine Eventually.of_forall fun T => Eventually.of_forall fun u => ?_
      rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) _)]
      exact indicator_le_self' (fun _ _ => sq_nonneg _) u
    · refine Eventually.of_forall fun u => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop u] with T hTu
      rw [indicator_of_notMem (not_lt.mpr hTu)]
  refine hdom.congr fun T => ?_
  rw [integral_indicator measurableSet_Ioi]
  rfl

/-- Exact fundamental-theorem-of-calculus derivative `E_h'(T) = -‖pulseReflected h T‖²`. -/
theorem hasDerivAt_tailEnergy (h : CompactPulse) (T : ℝ) :
    HasDerivAt (tailEnergy h) (-(‖pulseReflected h T‖ ^ 2)) T := by
  set f : ℝ → ℝ := fun u => ‖pulseReflected h u‖ ^ 2
  have hf_cont : Continuous f := ((continuous_pulseReflected h).norm).pow 2
  have hf_int : Integrable f := integrable_norm_sq_pulseReflected h
  have hsplit : ∀ x : ℝ, tailEnergy h x = (∫ u in Ioi (0 : ℝ), f u) - ∫ u in (0 : ℝ)..x, f u := by
    intro x
    rcases le_total 0 x with hx | hx
    · rw [intervalIntegral.integral_of_le hx]
      have hdisj : Disjoint (Ioc (0 : ℝ) x) (Ioi x) :=
        Set.disjoint_left.mpr fun _ h1 h2 => h1.2.not_gt h2
      have hun : Ioc (0 : ℝ) x ∪ Ioi x = Ioi 0 := Ioc_union_Ioi_eq_Ioi hx
      have hs : (∫ u in Ioi (0 : ℝ), f u) = (∫ u in Ioc (0 : ℝ) x, f u) + ∫ u in Ioi x, f u := by
        rw [← hun, setIntegral_union hdisj measurableSet_Ioi hf_int.integrableOn hf_int.integrableOn]
      unfold tailEnergy
      linarith
    · rw [intervalIntegral.integral_of_ge hx]
      have hdisj : Disjoint (Ioc x (0 : ℝ)) (Ioi (0 : ℝ)) :=
        Set.disjoint_left.mpr fun _ h1 h2 => h1.2.not_gt h2
      have hun : Ioc x (0 : ℝ) ∪ Ioi (0 : ℝ) = Ioi x := Ioc_union_Ioi_eq_Ioi hx
      have hs : (∫ u in Ioi x, f u) = (∫ u in Ioc x (0 : ℝ), f u) + ∫ u in Ioi (0 : ℝ), f u := by
        rw [← hun, setIntegral_union hdisj measurableSet_Ioi hf_int.integrableOn hf_int.integrableOn]
      unfold tailEnergy
      linarith
  have hd_int : HasDerivAt (fun x : ℝ => ∫ u in (0 : ℝ)..x, f u) (f T) T :=
    (intervalIntegral.integral_hasStrictDerivAt_right
      (hf_cont.intervalIntegrable 0 T) (hf_cont.stronglyMeasurableAtFilter volume (𝓝 T))
      hf_cont.continuousAt).hasDerivAt
  have hd := ((hasDerivAt_const T (∫ u in Ioi (0 : ℝ), f u)).sub hd_int).congr_deriv (by ring)
  exact hd.congr_of_eventuallyEq (Eventually.of_forall hsplit)

/-! ## 2. Two-Pulse Superposition, Relative Phase, and Four-Phase Polarization -/

private theorem norm_sq_linComb (c₁ c₂ z₁ z₂ : ℂ) :
    ‖c₁ * z₁ + c₂ * z₂‖ ^ 2 =
      ‖c₁‖ ^ 2 * ‖z₁‖ ^ 2 + ‖c₂‖ ^ 2 * ‖z₂‖ ^ 2 +
        2 * ((c₁ * (starRingEnd ℂ) c₂) * (z₁ * (starRingEnd ℂ) z₂)).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem polarization_pointwise (z₁ z₂ : ℂ) :
    z₁ * (starRingEnd ℂ) z₂ =
      ((1 / 4 : ℝ) : ℂ) *
        ((((‖z₁ + z₂‖ ^ 2 - ‖z₁ - z₂‖ ^ 2 : ℝ) : ℂ)) +
          I * (((‖z₁ + I * z₂‖ ^ 2 - ‖z₁ - I * z₂‖ ^ 2 : ℝ) : ℂ))) := by
  apply Complex.ext <;>
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    ring

/-- Hermitian expansion of `tailEnergy` on any two-pulse superposition `c₁ g + c₂ h`. -/
theorem tailEnergy_linComb (c₁ c₂ : ℂ) (g h : CompactPulse) (T : ℝ) :
    tailEnergy ((CompactPulse.smul c₁ g).add (CompactPulse.smul c₂ h)) T =
      ‖c₁‖ ^ 2 * tailEnergy g T + ‖c₂‖ ^ 2 * tailEnergy h T +
        2 * ((c₁ * (starRingEnd ℂ) c₂) * tailCrossEnergy g h T).re := by
  have hg_int := ((integrable_norm_sq_pulseReflected g).const_mul (‖c₁‖ ^ 2)).integrableOn (s := Ioi T)
  have hh_int := ((integrable_norm_sq_pulseReflected h).const_mul (‖c₂‖ ^ 2)).integrableOn (s := Ioi T)
  have hgh_c := ((integrable_pulseReflected_mul_conj g h).const_mul
    (c₁ * (starRingEnd ℂ) c₂)).integrableOn (s := Ioi T)
  have hgh_re : IntegrableOn
      (fun u : ℝ => 2 * ((c₁ * (starRingEnd ℂ) c₂) *
        (pulseReflected g u * (starRingEnd ℂ) (pulseReflected h u))).re) (Ioi T) :=
    (Complex.reCLM.integrable_comp hgh_c).const_mul 2
  have hpt : ∀ u : ℝ,
      ‖pulseReflected ((CompactPulse.smul c₁ g).add (CompactPulse.smul c₂ h)) u‖ ^ 2 =
        (‖c₁‖ ^ 2 * ‖pulseReflected g u‖ ^ 2 + ‖c₂‖ ^ 2 * ‖pulseReflected h u‖ ^ 2) +
          2 * ((c₁ * (starRingEnd ℂ) c₂) *
            (pulseReflected g u * (starRingEnd ℂ) (pulseReflected h u))).re := by
    intro u
    rw [pulseReflected_add, pulseReflected_smul, pulseReflected_smul]
    exact norm_sq_linComb c₁ c₂ _ _
  unfold tailEnergy tailCrossEnergy
  simp_rw [hpt]
  rw [integral_add (hg_int.add hh_int) hgh_re, integral_add hg_int hh_int,
    integral_const_mul, integral_const_mul, integral_const_mul]
  have hre := Complex.reCLM.integral_comp_comm hgh_c
  simp only [Complex.reCLM_apply] at hre
  rw [hre, integral_const_mul]

/-- Relative-phase law `E_{g + e^{iφ} h}(T) = E_g(T) + E_h(T) + 2 Re(e^{-iφ} E_{g,h}(T))`. -/
theorem tailEnergy_phaseMix (φ : ℝ) (g h : CompactPulse) (T : ℝ) :
    tailEnergy (CompactPulse.phaseMix φ g h) T =
      tailEnergy g T + tailEnergy h T +
        2 * (Complex.exp (-(I * (φ : ℂ))) * tailCrossEnergy g h T).re := by
  have heq : pulseReflected (CompactPulse.phaseMix φ g h) =
      pulseReflected ((CompactPulse.smul 1 g).add
        (CompactPulse.smul (Complex.exp (I * (φ : ℂ))) h)) := by
    funext u
    rw [pulseReflected_phaseMix, pulseReflected_add, pulseReflected_smul, pulseReflected_smul,
      one_mul]
  have hlin := tailEnergy_linComb 1 (Complex.exp (I * (φ : ℂ))) g h T
  unfold tailEnergy at hlin ⊢
  rw [heq]
  have h1 : ‖(1 : ℂ)‖ ^ 2 = 1 := by simp
  have h2 : ‖Complex.exp (I * (φ : ℂ))‖ ^ 2 = 1 := by
    rw [mul_comm I, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hconj : (1 : ℂ) * (starRingEnd ℂ) (Complex.exp (I * (φ : ℂ))) =
      Complex.exp (-(I * (φ : ℂ))) := by
    rw [one_mul, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  rw [h1, h2, one_mul, one_mul, hconj] at hlin
  exact hlin

/-- Averaging `E_{g + e^{iφ} h}(T)` and `E_{g + e^{i(φ + π)} h}(T)` cancels the cross term identically. -/
theorem tailEnergy_phase_average (φ : ℝ) (g h : CompactPulse) (T : ℝ) :
    (tailEnergy (CompactPulse.phaseMix φ g h) T +
        tailEnergy (CompactPulse.phaseMix (φ + Real.pi) g h) T) / 2 =
      tailEnergy g T + tailEnergy h T := by
  rw [tailEnergy_phaseMix, tailEnergy_phaseMix]
  have hexp : Complex.exp (-(I * ((φ + Real.pi : ℝ) : ℂ))) =
      -Complex.exp (-(I * (φ : ℂ))) := by
    have hsplit : -(I * ((φ + Real.pi : ℝ) : ℂ)) =
        -(I * (φ : ℂ)) + (-(Real.pi : ℂ) * I) := by push_cast; ring
    rw [hsplit, Complex.exp_add,
      show -(Real.pi : ℂ) * I = -((Real.pi : ℂ) * I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, mul_neg_one]
  rw [hexp, neg_mul, Complex.neg_re]
  ring

/-- **Four-Phase Polarization Identity for Tail Cross-Energy.** Reads the full complex cross-term
`E_{g,h}(T)` from scalar tail energies at phases `0, π, π/2, -π/2`. -/
theorem tailCrossEnergy_eq_polarization (g h : CompactPulse) (T : ℝ) :
    tailCrossEnergy g h T =
      ((1 / 4 : ℝ) : ℂ) *
        (((tailEnergy (g.add h) T - tailEnergy (g.add (CompactPulse.smul (-1) h)) T : ℝ) : ℂ) +
          I * ((tailEnergy (g.add (CompactPulse.smul I h)) T -
            tailEnergy (g.add (CompactPulse.smul (-I) h)) T : ℝ) : ℂ)) := by
  set p1 := g.add h
  set p2 := g.add (CompactPulse.smul (-1) h)
  set p3 := g.add (CompactPulse.smul I h)
  set p4 := g.add (CompactPulse.smul (-I) h)
  have hi1 := (integrable_norm_sq_pulseReflected p1).integrableOn (s := Ioi T)
  have hi2 := (integrable_norm_sq_pulseReflected p2).integrableOn (s := Ioi T)
  have hi3 := (integrable_norm_sq_pulseReflected p3).integrableOn (s := Ioi T)
  have hi4 := (integrable_norm_sq_pulseReflected p4).integrableOn (s := Ioi T)
  have hpt : ∀ u : ℝ,
      pulseReflected g u * (starRingEnd ℂ) (pulseReflected h u) =
        ((1 / 4 : ℝ) : ℂ) *
          ((((‖pulseReflected p1 u‖ ^ 2 - ‖pulseReflected p2 u‖ ^ 2 : ℝ) : ℂ)) +
            I * (((‖pulseReflected p3 u‖ ^ 2 - ‖pulseReflected p4 u‖ ^ 2 : ℝ) : ℂ))) := by
    intro u
    have r1 : pulseReflected p1 u = pulseReflected g u + pulseReflected h u :=
      pulseReflected_add g h u
    have r2 : pulseReflected p2 u = pulseReflected g u - pulseReflected h u := by
      rw [pulseReflected_add, pulseReflected_smul, neg_one_mul, sub_eq_add_neg]
    have r3 : pulseReflected p3 u = pulseReflected g u + I * pulseReflected h u := by
      rw [pulseReflected_add, pulseReflected_smul]
    have r4 : pulseReflected p4 u = pulseReflected g u - I * pulseReflected h u := by
      rw [pulseReflected_add, pulseReflected_smul, neg_mul, sub_eq_add_neg]
    rw [r1, r2, r3, r4]
    exact polarization_pointwise _ _
  unfold tailCrossEnergy tailEnergy
  simp_rw [hpt, integral_const_mul]
  congr 1
  have hc12 : IntegrableOn
      (fun u : ℝ => ((‖pulseReflected p1 u‖ ^ 2 - ‖pulseReflected p2 u‖ ^ 2 : ℝ) : ℂ)) (Ioi T) :=
    Complex.ofRealCLM.integrable_comp (hi1.sub hi2)
  have hc34 : IntegrableOn
      (fun u : ℝ => ((‖pulseReflected p3 u‖ ^ 2 - ‖pulseReflected p4 u‖ ^ 2 : ℝ) : ℂ)) (Ioi T) :=
    Complex.ofRealCLM.integrable_comp (hi3.sub hi4)
  rw [integral_add hc12 (hc34.const_mul I), integral_const_mul,
    integral_ofReal, integral_ofReal, integral_sub hi1 hi2, integral_sub hi3 hi4]

/-- **Four-Phase Polarization Identity for the Finite-Step Cross-Decrement.** -/
theorem stepCrossDecrement_eq_polarization (g h : CompactPulse) (T : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    stepCrossDecrement g h T L =
      ((1 / 4 : ℝ) : ℂ) *
        (((stepDecrement (g.add h) T L -
            stepDecrement (g.add (CompactPulse.smul (-1) h)) T L : ℝ) : ℂ) +
          I * ((stepDecrement (g.add (CompactPulse.smul I h)) T L -
            stepDecrement (g.add (CompactPulse.smul (-I) h)) T L : ℝ) : ℂ)) := by
  rw [← tailCrossEnergy_sub_step g h T hL,
    tailCrossEnergy_eq_polarization g h T, tailCrossEnergy_eq_polarization g h (T + L),
    ← tailEnergy_sub_step _ T hL, ← tailEnergy_sub_step _ T hL,
    ← tailEnergy_sub_step _ T hL, ← tailEnergy_sub_step _ T hL]
  push_cast
  ring

/-! ## 3. Resonance Pole Obstruction and Strict Eternal Tail Positivity -/

/-- Laplace transform of `pulseEcho h` on `Re w > 1/2`: convolution with `echoKernel` multiplies
`2π a_h(-iw)` by `scatteringPhase w`. -/
theorem integrable_and_laplace_pulseEcho (h : CompactPulse) {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun u : ℝ => Complex.exp (-w * (u : ℂ)) * pulseEcho h u) ∧
      (∫ u : ℝ, Complex.exp (-w * (u : ℂ)) * pulseEcho h u) =
        2 * Real.pi * pulseAmplitude h (-I * w) * scatteringPhase w := by
  set g₁ : ℝ → ℂ := fun S => Complex.exp (-w * (S : ℂ)) * h S
  set g₂ : ℝ → ℂ := fun τ => Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ)
  have hg₁ : Integrable g₁ := by
    refine (h.integrable_mul_cexp (-I * w)).congr (Eventually.of_forall fun S => ?_)
    dsimp only [g₁]
    have he : -(I * (-I * w) * (S : ℂ)) = -w * (S : ℂ) := by
      linear_combination (w * (S : ℂ)) * I_sq
    rw [he, mul_comm]
  have hg₂ : Integrable g₂ := integrable_cexp_mul_echoKernel hw
  have hconv : Integrable (fun p : ℝ × ℝ => g₂ p.2 * g₁ (p.1 - p.2)) (volume.prod volume) := by
    simpa using hg₂.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg₁
  have hpt : ∀ u τ : ℝ,
      Complex.exp (-w * (u : ℂ)) * (h (u - τ) * ((echoKernel τ : ℝ) : ℂ)) =
        g₂ τ * g₁ (u - τ) := by
    intro u τ
    dsimp only [g₁, g₂]
    have he : Complex.exp (-w * (u : ℂ)) =
        Complex.exp (-w * (τ : ℂ)) * Complex.exp (-w * ((u - τ : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rw [he]; ring
  have hint_u : Integrable fun u : ℝ => Complex.exp (-w * (u : ℂ)) * pulseEcho h u := by
    refine hconv.integral_prod_left.congr (Eventually.of_forall fun u => ?_)
    dsimp only [pulseEcho]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun τ => (hpt u τ).symm)
  refine ⟨hint_u, ?_⟩
  have hswap := integral_integral_swap (f := fun u τ => g₂ τ * g₁ (u - τ)) hconv
  have hlhs : (∫ u : ℝ, Complex.exp (-w * (u : ℂ)) * pulseEcho h u) =
      ∫ u : ℝ, ∫ τ : ℝ, g₂ τ * g₁ (u - τ) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only [pulseEcho]
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun τ => hpt u τ)
  have hg₁_val : (∫ v : ℝ, g₁ v) = 2 * Real.pi * pulseAmplitude h (-I * w) := by
    rw [← h.integral_mul_cexp_eq w]
    exact integral_congr_ae (Eventually.of_forall fun v => mul_comm _ _)
  have hg₂_val : (∫ τ : ℝ, g₂ τ) = scatteringPhase w := by
    rw [integral_cexp_mul_echoKernel_eq_completed hw, completed_div_eq_scatteringPhase hw]
  rw [hlhs, hswap]
  have hinner : ∀ τ : ℝ, (∫ u : ℝ, g₂ τ * g₁ (u - τ)) =
      g₂ τ * (2 * Real.pi * pulseAmplitude h (-I * w)) := by
    intro τ
    rw [integral_const_mul, integral_sub_right_eq_self g₁ τ, hg₁_val]
  simp_rw [hinner]
  rw [integral_mul_const, hg₂_val]
  ring

/-- **Resonance Pole Obstruction for `pulseReflected`.** If `‖pulseReflected h u‖ ≤ C₀ e^{-δ u}` on
`u ≥ 0` (`0 < δ`), then `pulseAmplitude h (-I * p) = 0` at every `ξ`-pole `p` (`xi (1 + 2 * p) = 0`)
lying in the strip `-δ < Re p < 0` with `-1/2 < Re p`. -/
theorem pulseAmplitude_eq_zero_of_pulseReflected_decay (h : CompactPulse) {δ C₀ : ℝ}
    (hδ : 0 < δ) (hbd : ∀ u : ℝ, 0 ≤ u → ‖pulseReflected h u‖ ≤ C₀ * Real.exp (-δ * u))
    {p : ℂ} (hp_xi : xi (1 + 2 * p) = 0) (hp_lo : -1 / 2 < p.re) (hp_hi : p.re < 0)
    (hp_δ : -δ < p.re) :
    pulseAmplitude h (-I * p) = 0 := by
  obtain ⟨S₀, hS₀_nn, hS₀⟩ := h.exists_support_bound
  set B : ℝ := S₀ + 1
  have hB0 : 0 ≤ B := by dsimp only [B]; linarith
  set G : ℝ → ℂ := pulseReflected h
  have hGc : Continuous G := continuous_pulseReflected h
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -B) (b := 0)).exists_bound_of_continuousOn hGc.continuousOn
  set C : ℝ := max (max C₀ M) 0
  have hC : 0 ≤ C := le_max_right _ _
  have hb : ∀ u : ℝ, -B < u → ‖G u‖ ≤ C * Real.exp (-δ * u) := by
    intro u hu
    rcases le_or_gt 0 u with hu0 | hu0
    · exact (hbd u hu0).trans
        (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (Real.exp_pos _).le)
    · have h1 : ‖G u‖ ≤ M := hM u ⟨hu.le, hu0.le⟩
      have h2 : 1 ≤ Real.exp (-δ * u) := Real.one_le_exp (by nlinarith)
      calc ‖G u‖ ≤ M := h1
        _ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
        _ ≤ C * Real.exp (-δ * u) := le_mul_of_one_le_right hC h2
  set m : ℂ := meanCoefficient h
  set L : ℂ → ℂ := fun w => ∫ u in Ioi (-B), Complex.exp (-w * (u : ℂ)) * G u
  set U : Set ℂ := {w : ℂ | -δ < w.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hLd : DifferentiableOn ℂ L U := RingdownRate.differentiableOn_laplace hGc hC hb
  set Φ₁ : ℂ → ℂ := fun w =>
    (2 * w - 1) * xi (1 + 2 * w) * L w +
      2 * m * xi (1 + 2 * w) * Complex.exp ((w - 1 / 2) * (B : ℂ))
  set Φ₂ : ℂ → ℂ := fun w =>
    2 * Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) * xi (2 * w)
  have hxid : Differentiable ℂ fun w : ℂ => xi (1 + 2 * w) := fun w => differentiable_xi_shift w
  have hΦ₁a : AnalyticOnNhd ℂ Φ₁ U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    intro w hw
    have hLw := (hLd w hw).differentiableAt (hUo.mem_nhds hw)
    have hxiw := hxid w
    exact (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 2 * v - 1) w).mul hxiw).mul hLw |>.add
      (((differentiableAt_const _).mul hxiw).mul (by fun_prop))).differentiableWithinAt
  have hΦ₂a : AnalyticOnNhd ℂ Φ₂ U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    intro w _
    exact ((((differentiableAt_const _).mul
      ((h.differentiable_amplitude _).comp w (by fun_prop))).mul (by fun_prop)).mul
      ((xi_differentiable _).comp w (by fun_prop))).differentiableWithinAt
  have hagree : ∀ w : ℂ, 1 / 2 < w.re → Φ₁ w = Φ₂ w := by
    intro w hw
    have hwU : -δ < w.re := by linarith
    have hlap := (integrable_and_laplace_pulseEcho h hw).2
    have hsplit : (∫ u : ℝ, Complex.exp (-w * (u : ℂ)) * pulseEcho h u) =
        L w + m * (-Complex.exp ((1 / 2 - w) * ((-B : ℝ) : ℂ)) / (1 / 2 - w)) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (-B)) fun u hu => by
        have hlt : u < -S₀ := by
          have : u ≤ -B := not_lt.mp hu
          dsimp only [B] at this
          linarith
        rw [h.pulseEcho_eq_zero hS₀ hlt, mul_zero]]
      have hre : (1 / 2 - w).re < 0 := by simp; linarith
      have he : ∀ u : ℝ, Complex.exp (-w * (u : ℂ)) * pulseEcho h u =
          Complex.exp (-w * (u : ℂ)) * G u + m * Complex.exp ((1 / 2 - w) * (u : ℂ)) := by
        intro u
        rw [h.pulseEcho_eq u]
        have e1 : Complex.exp (-w * (u : ℂ)) * Complex.exp ((u : ℂ) / 2) =
            Complex.exp ((1 / 2 - w) * (u : ℂ)) := by
          rw [← Complex.exp_add]; congr 1; ring
        dsimp only [G, m]
        linear_combination m * e1
      rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => he u),
        integral_add (RingdownRate.integrableOn_exp_mul_of_bound hGc hb hwU)
          ((integrableOn_exp_mul_complex_Ioi hre (-B)).const_mul m),
        integral_const_mul, integral_exp_mul_complex_Ioi hre (-B)]
    have hξ : xi (1 + 2 * w) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
    have h2w : 2 * w - 1 ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this; linarith
    have h12 : (1 / 2 - w : ℂ) ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    have hcomb := hlap.symm.trans hsplit
    set e : ℂ := Complex.exp ((w - 1 / 2) * (B : ℂ))
    have hexp : Complex.exp ((1 / 2 - w) * ((-B : ℝ) : ℂ)) = e := by
      dsimp only [e]; congr 1; push_cast; ring
    rw [hexp] at hcomb
    have hph : 2 * Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) * xi (2 * w) =
        (2 * w - 1) * xi (1 + 2 * w) *
          (2 * Real.pi * pulseAmplitude h (-I * w) * scatteringPhase w) := by
      unfold scatteringPhase
      field_simp [h2w, hξ]
    have h4 : (2 * w - 1) * (-e / (1 / 2 - w)) = 2 * e := by
      rw [show (2 * w - 1) * (-e / (1 / 2 - w)) = 2 * e * ((1 / 2 - w) / (1 / 2 - w)) by ring,
        div_self h12, mul_one]
    dsimp only [Φ₁, Φ₂]
    rw [hph, hcomb]
    linear_combination (-(xi (1 + 2 * w)) * m) * h4
  have hEq : EqOn Φ₁ Φ₂ U := by
    refine hΦ₁a.eqOn_of_preconnected_of_eventuallyEq hΦ₂a
      (convex_halfSpace_re_gt (-δ)).isPreconnected
      (show (1 : ℂ) ∈ U by show -δ < (1 : ℂ).re; simp; linarith) ?_
    have hV : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hV.mem_nhds (show (1 : ℂ) ∈ {w : ℂ | 1 / 2 < w.re} by simp; norm_num)] with w hw
    exact hagree w hw
  have hp_eq := hEq hp_δ
  dsimp only [Φ₁, Φ₂] at hp_eq
  rw [hp_xi, mul_zero, zero_mul, add_zero] at hp_eq
  have hpi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h12p : 1 + 2 * p ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hxi2p : xi (2 * p) ≠ 0 := by
    rw [← xi_one_sub (2 * p)]
    exact xi_ne_zero_of_one_le_re (by simp; linarith)
  have hprod : (2 * (Real.pi : ℂ) * (1 + 2 * p) * xi (2 * p)) * pulseAmplitude h (-I * p) = 0 := by
    linear_combination -hp_eq
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (mul_ne_zero hpi h12p) hxi2p)

/-- **Strict Eternal Tail Positivity (Failure of Huygens' Principle on the Modular Cusp).**
Every nonzero compact pulse `h` has strictly positive reflected tail energy `0 < E_h(T)` at every
cutoff time `T ∈ ℝ`. -/
theorem tailEnergy_pos (h : CompactPulse) (hne : ∃ S : ℝ, h S ≠ 0) (T : ℝ) :
    0 < tailEnergy h T := by
  by_contra hle
  push Not at hle
  have hE0 : tailEnergy h T = 0 := le_antisymm hle (tailEnergy_nonneg h T)
  have hvanish_tail : ∀ u : ℝ, T < u → pulseReflected h u = 0 := by
    intro u₀ hu₀
    by_contra hne_u
    have hpos_u : 0 < ‖pulseReflected h u₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne_u)
    have hcont : Continuous fun u : ℝ => ‖pulseReflected h u‖ ^ 2 :=
      ((continuous_pulseReflected h).norm).pow 2
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
      (‖pulseReflected h u₀‖ ^ 2 / 2) (by positivity)
    set a : ℝ := max ((T + u₀) / 2) (u₀ - δ / 2)
    set b : ℝ := u₀ + δ / 2
    have haT : T < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hab : a < b := by
      have : a ≤ u₀ := max_le (by linarith) (by linarith)
      dsimp only [b]; linarith
    have hsub : Ioc a b ⊆ Ioi T := fun x hx => haT.trans hx.1
    have hlow : ∀ x ∈ Ioc a b, ‖pulseReflected h u₀‖ ^ 2 / 2 ≤ ‖pulseReflected h x‖ ^ 2 := by
      intro x hx
      have hdist : |x - u₀| < δ := by
        rw [abs_lt]
        have ha2 : u₀ - δ / 2 ≤ a := le_max_right _ _
        exact ⟨by linarith [hx.1], by dsimp only [b] at hx; linarith [hx.2]⟩
      have hb' := hball hdist
      rw [Real.dist_eq, abs_lt] at hb'
      linarith [hb'.1]
    have hint := integrable_norm_sq_pulseReflected h
    have hpos_int : 0 < ∫ x in Ioc a b, ‖pulseReflected h x‖ ^ 2 := by
      have hconst : (∫ _x in Ioc a b, ‖pulseReflected h u₀‖ ^ 2 / 2) =
          (b - a) * (‖pulseReflected h u₀‖ ^ 2 / 2) := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith)]
      have hmono := setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
        hint.integrableOn measurableSet_Ioc hlow
      rw [hconst] at hmono
      exact lt_of_lt_of_le (mul_pos (by linarith) (by positivity)) hmono
    have hle_tail : (∫ x in Ioc a b, ‖pulseReflected h x‖ ^ 2) ≤ tailEnergy h T :=
      setIntegral_mono_set hint.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall hsub)
    linarith
  -- Construct global `O(e^{-u})` bound on `u ≥ 0`
  set B₁ : ℝ := max T 0 + 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B₁)).exists_bound_of_continuousOn
    (continuous_pulseReflected h).continuousOn
  set C₀ : ℝ := max M 0 * Real.exp B₁
  have hdecay1 : ∀ u : ℝ, 0 ≤ u → ‖pulseReflected h u‖ ≤ C₀ * Real.exp (-1 * u) := by
    intro u hu
    rcases le_or_gt u B₁ with huB | huB
    · calc ‖pulseReflected h u‖ ≤ max M 0 := (hM u ⟨hu, huB⟩).trans (le_max_left _ _)
        _ = max M 0 * 1 := (mul_one _).symm
        _ ≤ max M 0 * Real.exp (B₁ - u) :=
            mul_le_mul_of_nonneg_left (Real.one_le_exp (by linarith)) (le_max_right _ _)
        _ = C₀ * Real.exp (-1 * u) := by
            dsimp only [C₀]; rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    · have hTu : T < u := lt_of_le_of_lt ((le_max_left T 0).trans (by dsimp only [B₁]; linarith)) huB
      rw [hvanish_tail u hTu, norm_zero]
      positivity
  -- Apply exponential-type zero bound to `F z = pulseAmplitude h (z / 2 + I / 4)`
  set F : ℂ → ℂ := fun z => pulseAmplitude h (z / 2 + I / 4)
  have hFd : Differentiable ℂ F := h.differentiable_amplitude.comp (by fun_prop)
  have hFne : F ≠ 0 := by
    intro hF0
    have hamp0 : ∀ ξ : ℝ, pulseAmplitude h (ξ : ℂ) = 0 := by
      intro ξ
      have hz := congrFun hF0 (2 * (ξ : ℂ) - I / 2)
      dsimp only [F, Pi.zero_apply] at hz
      have hcoord : (2 * (ξ : ℂ) - I / 2) / 2 + I / 4 = (ξ : ℂ) := by ring
      rwa [hcoord] at hz
    obtain ⟨S₁, hS₁⟩ := hne
    apply hS₁
    rw [h.eq_integral_amplitude S₁]
    simp [hamp0]
  obtain ⟨S₀, hS₀_nn, hS₀⟩ := h.exists_support_bound
  set C_exp : ℝ := max 1 ((2 * Real.pi)⁻¹ * (∫ S : ℝ, ‖h S‖) * Real.exp (S₀ / 4))
  have hC1 : 1 ≤ C_exp := le_max_left _ _
  have hgrow : ∀ z : ℂ, ‖F z‖ ≤ C_exp * Real.exp ((S₀ / 2) * ‖z‖) := by
    intro z
    set w : ℂ := z / 2 + I / 4
    have hw_im : |w.im| ≤ ‖z‖ / 2 + 1 / 4 := by
      have him : w.im = z.im / 2 + 1 / 4 := by simp [w]
      rw [him]
      calc |z.im / 2 + 1 / 4| ≤ |z.im / 2| + |1 / 4| := abs_add_le _ _
        _ = |z.im| / 2 + 1 / 4 := by rw [abs_div, abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
        _ ≤ ‖z‖ / 2 + 1 / 4 := by linarith [Complex.abs_im_le_norm z]
    have hpi_inv : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hint_norm : Integrable fun S : ℝ => ‖h S‖ * Real.exp (|w.im| * S₀) :=
      h.integrable_toFun.norm.mul_const _
    have hamp_bd : ‖F z‖ ≤ (2 * Real.pi)⁻¹ * ((∫ S : ℝ, ‖h S‖) * Real.exp (|w.im| * S₀)) := by
      dsimp only [F]
      rw [pulseAmplitude, norm_mul, hpi_inv]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (norm_integral_le_of_norm_le hint_norm
        (Eventually.of_forall fun S => h.norm_mul_cexp_le hS₀ w S)).trans
        (le_of_eq (integral_mul_const _ _))
    have hexp_le : Real.exp (|w.im| * S₀) ≤ Real.exp (S₀ / 4) * Real.exp ((S₀ / 2) * ‖z‖) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    have hI_nn : 0 ≤ ∫ S : ℝ, ‖h S‖ := integral_nonneg fun _ => norm_nonneg _
    calc ‖F z‖ ≤ (2 * Real.pi)⁻¹ * ((∫ S : ℝ, ‖h S‖) * Real.exp (|w.im| * S₀)) := hamp_bd
      _ ≤ (2 * Real.pi)⁻¹ * ((∫ S : ℝ, ‖h S‖) * (Real.exp (S₀ / 4) * Real.exp ((S₀ / 2) * ‖z‖))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_le hI_nn) (by positivity)
      _ = ((2 * Real.pi)⁻¹ * (∫ S : ℝ, ‖h S‖) * Real.exp (S₀ / 4)) * Real.exp ((S₀ / 2) * ‖z‖) := by
          ring
      _ ≤ C_exp * Real.exp ((S₀ / 2) * ‖z‖) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  have hvanish_crit : ∀ t : ℝ, t ∉ (∅ : Finset ℝ) → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 → F (t : ℂ) = 0 := by
    intro t _ _ hxi _
    set p : ℂ := (-1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I
    have hp_line : 1 + 2 * p = linePt t := by
      apply Complex.ext
      · simp [p, linePt]; ring
      · simp [p, linePt]; ring
    have hp_xi : xi (1 + 2 * p) = 0 := by rw [hp_line]; exact hxi
    have hp_re : p.re = -1 / 4 := by simp [p]
    have hzero := pulseAmplitude_eq_zero_of_pulseReflected_decay h one_pos hdecay1 hp_xi
      (by rw [hp_re]; norm_num) (by rw [hp_re]; norm_num) (by rw [hp_re]; norm_num)
    have hcoord : -I * p = (t : ℂ) / 2 + I / 4 := by
      dsimp only [p]
      push_cast
      linear_combination (-(t : ℂ) / 2) * I_sq
    dsimp only [F]
    rwa [← hcoord]
  obtain ⟨K, _, hlin⟩ := exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros
    hFd hFne (by positivity) hC1 hgrow ∅ hvanish_crit
  exact not_linear_bound_of_superlinear (c := 1 / (72 * Real.pi)) (by positivity)
    eventually_superlinear_xiSimpleCriticalZeroCount hlin

/-- Cauchy–Schwarz bound `‖E_{g,h}(T)‖² ≤ E_g(T) * E_h(T)` at every time `T`. -/
theorem norm_tailCrossEnergy_sq_le_mul (g h : CompactPulse) (T : ℝ) :
    ‖tailCrossEnergy g h T‖ ^ 2 ≤ tailEnergy g T * tailEnergy h T := by
  by_cases hg0 : tailEnergy g T = 0
  · rw [hg0, zero_mul]
    have hlin := fun t : ℝ => tailEnergy_nonneg
      ((CompactPulse.smul (t : ℂ) g).add
        (CompactPulse.smul (-(tailCrossEnergy g h T)) h)) T
    have hexp : ∀ t : ℝ, 0 ≤ -(2 * t * ‖tailCrossEnergy g h T‖ ^ 2) +
        ‖tailCrossEnergy g h T‖ ^ 2 * tailEnergy h T := by
      intro t
      have h1 := hlin t
      rw [tailEnergy_linComb, hg0] at h1
      have hc : (((t : ℂ) * (starRingEnd ℂ) (-(tailCrossEnergy g h T))) *
          tailCrossEnergy g h T).re = -(t * ‖tailCrossEnergy g h T‖ ^ 2) := by
        rw [map_neg, mul_neg, neg_mul, mul_assoc, Complex.conj_mul', ← ofReal_pow,
          ← Complex.ofReal_mul, Complex.neg_re, Complex.ofReal_re]
      rw [hc] at h1
      have hn : ‖-(tailCrossEnergy g h T)‖ ^ 2 = ‖tailCrossEnergy g h T‖ ^ 2 := by rw [norm_neg]
      rw [hn] at h1
      linarith
    by_contra hgt
    push Not at hgt
    have hpos : 0 < ‖tailCrossEnergy g h T‖ ^ 2 := hgt
    have ht := hexp (tailEnergy h T + 1)
    nlinarith
  · have hg_pos : 0 < tailEnergy g T :=
      lt_of_le_of_ne (tailEnergy_nonneg g T) (Ne.symm hg0)
    set c₁ : ℂ := (starRingEnd ℂ) (tailCrossEnergy g h T)
    set c₂ : ℂ := -((tailEnergy g T : ℝ) : ℂ)
    have hnn := tailEnergy_nonneg ((CompactPulse.smul c₁ g).add (CompactPulse.smul c₂ h)) T
    rw [tailEnergy_linComb] at hnn
    have hc1 : ‖c₁‖ ^ 2 = ‖tailCrossEnergy g h T‖ ^ 2 := by simp [c₁]
    have hc2 : ‖c₂‖ ^ 2 = tailEnergy g T ^ 2 := by
      simp [c₂, Real.norm_of_nonneg hg_pos.le]
    have hcr : ((c₁ * (starRingEnd ℂ) c₂) * tailCrossEnergy g h T).re =
        -(tailEnergy g T * ‖tailCrossEnergy g h T‖ ^ 2) := by
      dsimp only [c₁, c₂]
      rw [map_neg, Complex.conj_ofReal, mul_neg, neg_mul, mul_right_comm, Complex.conj_mul',
        ← ofReal_pow, ← Complex.ofReal_mul, Complex.neg_re, Complex.ofReal_re, mul_comm]
    rw [hc1, hc2, hcr] at hnn
    nlinarith

/-- **Strict `2 × 2` Tail-Energy Gram Positivity.** For every `ℂ`-linearly independent pair of
compact pulses `(g, h)` and every time `T ∈ ℝ`, `‖E_{g,h}(T)‖² < E_g(T) * E_h(T)`. -/
theorem norm_tailCrossEnergy_sq_lt_mul (g h : CompactPulse)
    (hind : ∀ c₁ c₂ : ℂ, (∀ S : ℝ, c₁ * g S + c₂ * h S = 0) → c₁ = 0 ∧ c₂ = 0) (T : ℝ) :
    ‖tailCrossEnergy g h T‖ ^ 2 < tailEnergy g T * tailEnergy h T := by
  have hg_ne : ∃ S : ℝ, g S ≠ 0 := by
    by_contra hall
    push Not at hall
    exact one_ne_zero (hind 1 0 (fun S => by simp [hall S])).1
  have hg_pos : 0 < tailEnergy g T := tailEnergy_pos g hg_ne T
  set c₁ : ℂ := (starRingEnd ℂ) (tailCrossEnergy g h T)
  set c₂ : ℂ := -((tailEnergy g T : ℝ) : ℂ)
  have hc₂_ne : c₂ ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hg_pos.ne')
  have hcomb_ne : ∃ S : ℝ, ((CompactPulse.smul c₁ g).add (CompactPulse.smul c₂ h)) S ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hc₂_ne (hind c₁ c₂ hall).2
  have hpos := tailEnergy_pos _ hcomb_ne T
  rw [tailEnergy_linComb] at hpos
  have hc1 : ‖c₁‖ ^ 2 = ‖tailCrossEnergy g h T‖ ^ 2 := by simp [c₁]
  have hc2 : ‖c₂‖ ^ 2 = tailEnergy g T ^ 2 := by
    simp [c₂, Real.norm_of_nonneg hg_pos.le]
  have hcr : ((c₁ * (starRingEnd ℂ) c₂) * tailCrossEnergy g h T).re =
      -(tailEnergy g T * ‖tailCrossEnergy g h T‖ ^ 2) := by
    dsimp only [c₁, c₂]
    rw [map_neg, Complex.conj_ofReal, mul_neg, neg_mul, mul_right_comm, Complex.conj_mul',
      ← ofReal_pow, ← Complex.ofReal_mul, Complex.neg_re, Complex.ofReal_re, mul_comm]
  rw [hc1, hc2, hcr] at hpos
  nlinarith

end GaloisForLFunctions.BlackHoleRingdown

end
