import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.PolarizationAndPositivity

/-!
# Local Regularity, Horocycle Receiver Readout, and the Five-Way Zero-Free Strip Equivalence

Pointwise decay of a wave field cannot be inferred from `L²` tail energy `E_h(T)` alone without a
local regularity estimate, and bulk modular fields must be connected to `pulseReflected` by an
explicit receiver readout. This module establishes both bridges and closes the five-way equivalence
between zero-free strips of `ζ`, bulk ringdown, cusp readout, tail energy, and pulse-uniform
Sobolev-cone escape:

1. **Time Derivative and Agmon–Sobolev Local Regularity**:
   `∂_T (pulseReflected h)(T) = pulseReflected h.D T`, yielding the parameter-free Agmon–Sobolev
   interpolation inequality `‖pulseReflected h T‖ ^ 4 ≤ 4 * tailEnergy h T * tailEnergy h.D T` at
   every `T ∈ ℝ`.
2. **Exact Horocycle Zero-Mode Receiver Readout**:
   Once the incoming compact wavepacket supported in `[-S₀, S₀]` clears horocycle height `Y > 0`
   (`S₀ < T + 2 log Y`), the zero Fourier mode of `pulseField h` along the closed horocycle at height
   `Y` reads `pulseReflected h T` directly:
   `pulseReflected h T = (√Y)⁻¹ * ∫ x in Ioc 0 1, pulseField h (T + log Y) x Y`.
3. **Five-Way Zero-Free Strip & RH Equivalence and Unconditional Sobolev-Cone Escape**:
   For every `0 < δ ≤ 1/4`, the strip `Re ρ ≤ 1 - 2δ` (`Re ρ > 0`) is equivalent to bulk `pulseField`
   ringdown, pointwise `pulseReflected` decay, `tailEnergy` decay `O_{h,ε}(e^{-2(δ - ε)T})`, and the
   pulse-uniform Sobolev-cone escape law
   `tailEnergy h T ≤ K * ((∫ ‖h‖²) + ∫ ‖h^{[N]}‖²) * e^{-2σ T}` (`0 < σ < δ`, `supp h ⊆ [-S₀, S₀]`).
   At `δ = 1/4` this is equivalent to `RiemannHypothesis` (so any slower asymptotic actual tail
   energy or bulk field refutes RH), while for `0 < σ < 3001 / 48000` the Sobolev-cone escape law
   holds unconditionally on `PSL₂(ℤ)\ℍ`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform Classical

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
  (riemannZeta_zero_mem_sub_quasiRH_strip)

/-! ## 1. Iterated Pulse Derivatives and Spectral Multipliers -/

namespace CompactPulse

/-- `n`-fold derivative `h^{[n]}` of a compactly supported smooth pulse. -/
def iterD : ℕ → CompactPulse → CompactPulse
  | 0, h => h
  | n + 1, h => (iterD n h).D

@[simp] theorem iterD_zero (h : CompactPulse) : iterD 0 h = h := rfl

@[simp] theorem iterD_succ (n : ℕ) (h : CompactPulse) : iterD (n + 1) h = (iterD n h).D := rfl

theorem D_eq_zero_of_support_bound {S₀ : ℝ} (h : CompactPulse)
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) {s : ℝ} (hs : S₀ < |s|) :
    h.D s = 0 := by
  have hVo : IsOpen {x : ℝ | S₀ < |x|} := isOpen_lt continuous_const continuous_abs
  have hev : h.toFun =ᶠ[𝓝 s] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hVo.mem_nhds hs] with x hx
    exact hS₀ x hx
  exact (h.hasDerivAt s).unique ((hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq hev)

theorem iterD_eq_zero_of_support_bound :
    ∀ (n : ℕ) {S₀ : ℝ} (h : CompactPulse),
      (∀ x : ℝ, S₀ < |x| → h x = 0) → ∀ s : ℝ, S₀ < |s| → iterD n h s = 0
  | 0, _, _, hS₀, s, hs => hS₀ s hs
  | n + 1, _, h, hS₀, _, hs =>
      D_eq_zero_of_support_bound (iterD n h) (iterD_eq_zero_of_support_bound n h hS₀) hs

theorem amplitude_iterD :
    ∀ (n : ℕ) (h : CompactPulse) (w : ℂ),
      pulseAmplitude (iterD n h) w = (I * w) ^ n * pulseAmplitude h w
  | 0, h, w => by simp [iterD]
  | n + 1, h, w => by
      rw [iterD_succ, (iterD n h).amplitude_D, amplitude_iterD n h w, pow_succ]
      ring

theorem norm_amplitude_iterD (n : ℕ) (h : CompactPulse) (w : ℂ) :
    ‖pulseAmplitude (iterD n h) w‖ = ‖w‖ ^ n * ‖pulseAmplitude h w‖ := by
  rw [amplitude_iterD, norm_mul, norm_pow, norm_mul, Complex.norm_I, one_mul]

end CompactPulse

/-! ## 2. Time Derivative and Agmon–Sobolev Local Regularity -/

/-- Exact time derivative `∂_T (pulseReflected h)(T) = pulseReflected h.D T`. -/
theorem hasDerivAt_pulseReflected (h : CompactPulse) (T : ℝ) :
    HasDerivAt (pulseReflected h) (pulseReflected h.D T) T := by
  set F : ℝ → ℝ → ℂ := fun s ξ =>
    pulseAmplitude h (ξ : ℂ) * scatteringPhase ((ξ : ℂ) * I) *
      Complex.exp (I * (ξ : ℂ) * (s : ℂ))
  set F' : ℝ → ℝ → ℂ := fun s ξ =>
    pulseAmplitude h.D (ξ : ℂ) * scatteringPhase ((ξ : ℂ) * I) *
      Complex.exp (I * (ξ : ℂ) * (s : ℂ))
  set G : ℝ → ℝ := fun ξ => ‖pulseAmplitude h.D (ξ : ℂ)‖
  have hGint : Integrable G := by
    simpa [G] using (h.D.integrable_amplitude_line 0).norm
  have hFint : ∀ s : ℝ, Integrable (F s) := fun s =>
    h.integrable_amplitude_mul continuous_scatteringPhase_line.measurable
      (fun ξ => (norm_scatteringPhase_line ξ).le) s
  have hF'int : Integrable (F' T) :=
    h.D.integrable_amplitude_mul continuous_scatteringPhase_line.measurable
      (fun ξ => (norm_scatteringPhase_line ξ).le) T
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := T) (s := Set.univ) (bound := G) univ_mem
    (Eventually.of_forall fun s => (hFint s).aestronglyMeasurable)
    (hFint T) hF'int.aestronglyMeasurable
    (Eventually.of_forall fun ξ s _ => by
      dsimp only [F', G]
      rw [norm_mul, norm_mul, norm_exp_I_mul, mul_one]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_scatteringPhase_line ξ).le)
    hGint
    (Eventually.of_forall fun ξ s _ => by
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (I * (ξ : ℂ) * (t : ℂ)))
          (Complex.exp (I * (ξ : ℂ) * (s : ℂ)) * (I * (ξ : ℂ))) s := by
        have hlin : HasDerivAt (fun t : ℝ => I * (ξ : ℂ) * (t : ℂ)) (I * (ξ : ℂ)) s := by
          simpa [mul_assoc] using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (I * (ξ : ℂ))
        exact hlin.cexp
      have hm := hexp.const_mul (pulseAmplitude h (ξ : ℂ) * scatteringPhase ((ξ : ℂ) * I))
      refine hm.congr_deriv ?_
      dsimp only [F']
      rw [h.amplitude_D (ξ : ℂ)]
      ring)).2

private theorem real_inner_le_mul_norm (z w : ℂ) :
    |(z.re * w.re + z.im * w.im)| ≤ ‖z‖ * ‖w‖ := by
  have hsq : (z.re * w.re + z.im * w.im) ^ 2 ≤ (‖z‖ * ‖w‖) ^ 2 := by
    rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply]
    nlinarith [sq_nonneg (z.re * w.im - z.im * w.re)]
  have habs := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (by positivity : 0 ≤ ‖z‖ * ‖w‖)] at habs

private theorem hasDerivAt_norm_sq_pulseReflected (h : CompactPulse) (u : ℝ) :
    HasDerivAt (fun t : ℝ => ‖pulseReflected h t‖ ^ 2)
      (2 * ((pulseReflected h u).re * (pulseReflected h.D u).re +
        (pulseReflected h u).im * (pulseReflected h.D u).im)) u := by
  have hd := hasDerivAt_pulseReflected h u
  have hre : HasDerivAt (fun t : ℝ => (pulseReflected h t).re) (pulseReflected h.D u).re u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd
  have him : HasDerivAt (fun t : ℝ => (pulseReflected h t).im) (pulseReflected h.D u).im u :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt u hd
  have hsum : HasDerivAt (fun t : ℝ => (pulseReflected h t).re ^ 2 + (pulseReflected h t).im ^ 2)
      (2 * ((pulseReflected h u).re * (pulseReflected h.D u).re +
        (pulseReflected h u).im * (pulseReflected h.D u).im)) u := by
    exact ((hre.pow 2).add (him.pow 2)).congr_deriv (by ring)
  refine hsum.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private theorem norm_sq_pulseReflected_le_weighted (h : CompactPulse) (T : ℝ) {c : ℝ} (hc : 0 < c) :
    ‖pulseReflected h T‖ ^ 2 ≤ c * tailEnergy h T + c⁻¹ * tailEnergy h.D T := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hexists : ∃ B : ℝ, T ≤ B ∧ ‖pulseReflected h B‖ ^ 2 < ε := by
    by_contra hall
    push Not at hall
    set L : ℝ := (tailEnergy h T + 1) / ε
    have hL : 0 < L := by
      have := tailEnergy_nonneg h T
      positivity
    have hint := integrable_norm_sq_pulseReflected h
    have hconst : (∫ _u in Ioc T (T + L), ε) = L * ε := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    have hlow : ∀ u ∈ Ioc T (T + L), ε ≤ ‖pulseReflected h u‖ ^ 2 := fun u hu => hall u hu.1.le
    have hmono := setIntegral_mono_on
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      hint.integrableOn measurableSet_Ioc hlow
    have hsub : (∫ u in Ioc T (T + L), ‖pulseReflected h u‖ ^ 2) ≤ tailEnergy h T :=
      setIntegral_mono_set hint.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun _ hu => hu.1)
    have hLε : L * ε = tailEnergy h T + 1 := div_mul_cancel₀ _ hε.ne'
    rw [hconst, hLε] at hmono
    linarith
  obtain ⟨B, hTB, hBε⟩ := hexists
  set g' : ℝ → ℝ := fun u =>
    2 * ((pulseReflected h u).re * (pulseReflected h.D u).re +
      (pulseReflected h u).im * (pulseReflected h.D u).im)
  have hg'_cont : Continuous g' := by
    dsimp only [g']
    have hc1 := continuous_pulseReflected h
    have hc2 := continuous_pulseReflected h.D
    exact continuous_const.mul
      (((Complex.continuous_re.comp hc1).mul (Complex.continuous_re.comp hc2)).add
        ((Complex.continuous_im.comp hc1).mul (Complex.continuous_im.comp hc2)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => ‖pulseReflected h u‖ ^ 2) (f' := g')
    (fun u _ => hasDerivAt_norm_sq_pulseReflected h u)
    (hg'_cont.intervalIntegrable T B)
  have hdiff : ‖pulseReflected h T‖ ^ 2 - ‖pulseReflected h B‖ ^ 2 =
      ∫ u in Ioc T B, -g' u := by
    have hneg : ∫ u in T..B, -g' u = -(∫ u in T..B, g' u) := intervalIntegral.integral_neg
    rw [← intervalIntegral.integral_of_le hTB, hneg, hftc]
    ring
  have hpt : ∀ u : ℝ, -g' u ≤
      c * ‖pulseReflected h u‖ ^ 2 + c⁻¹ * ‖pulseReflected h.D u‖ ^ 2 := by
    intro u
    have hcs := real_inner_le_mul_norm (pulseReflected h u) (pulseReflected h.D u)
    have h1 : -g' u ≤ 2 * (‖pulseReflected h u‖ * ‖pulseReflected h.D u‖) := by
      dsimp only [g']
      linarith [hcs, neg_abs_le ((pulseReflected h u).re * (pulseReflected h.D u).re +
        (pulseReflected h u).im * (pulseReflected h.D u).im)]
    have hamgm : 2 * (‖pulseReflected h u‖ * ‖pulseReflected h.D u‖) ≤
        c * ‖pulseReflected h u‖ ^ 2 + c⁻¹ * ‖pulseReflected h.D u‖ ^ 2 := by
      have hsq : 0 ≤ c * (‖pulseReflected h u‖ - c⁻¹ * ‖pulseReflected h.D u‖) ^ 2 :=
        mul_nonneg hc.le (sq_nonneg _)
      have hexp : c * (‖pulseReflected h u‖ - c⁻¹ * ‖pulseReflected h.D u‖) ^ 2 =
          c * ‖pulseReflected h u‖ ^ 2 + c⁻¹ * ‖pulseReflected h.D u‖ ^ 2 -
            2 * (‖pulseReflected h u‖ * ‖pulseReflected h.D u‖) := by
        field_simp [hc.ne']
        ring
      linarith
    exact h1.trans hamgm
  have hi1 := ((integrable_norm_sq_pulseReflected h).const_mul c).integrableOn (s := Ioc T B)
  have hi2 := ((integrable_norm_sq_pulseReflected h.D).const_mul c⁻¹).integrableOn (s := Ioc T B)
  have hsum_int : IntegrableOn
      (fun u : ℝ => c * ‖pulseReflected h u‖ ^ 2 + c⁻¹ * ‖pulseReflected h.D u‖ ^ 2)
      (Ioc T B) := hi1.add hi2
  have hint_le := setIntegral_mono (hg'_cont.neg.integrableOn_Ioc) hsum_int hpt
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul] at hint_le
  have hsub1 : (∫ u in Ioc T B, ‖pulseReflected h u‖ ^ 2) ≤ tailEnergy h T :=
    setIntegral_mono_set (integrable_norm_sq_pulseReflected h).integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun _ hu => hu.1)
  have hsub2 : (∫ u in Ioc T B, ‖pulseReflected h.D u‖ ^ 2) ≤ tailEnergy h.D T :=
    setIntegral_mono_set (integrable_norm_sq_pulseReflected h.D).integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall fun _ hu => hu.1)
  have hcomb : ‖pulseReflected h T‖ ^ 2 - ‖pulseReflected h B‖ ^ 2 ≤
      c * tailEnergy h T + c⁻¹ * tailEnergy h.D T := by
    rw [hdiff]
    exact hint_le.trans (add_le_add (mul_le_mul_of_nonneg_left hsub1 hc.le)
      (mul_le_mul_of_nonneg_left hsub2 (inv_nonneg.mpr hc.le)))
  linarith

/-- **Agmon–Sobolev Local Regularity for `pulseReflected`.** For every compact pulse `h` and every
cutoff `T ∈ ℝ`, pointwise reflected amplitude is controlled parameter-freely by the tail energies of
`h` and its derivative `h.D`: `‖pulseReflected h T‖ ^ 4 ≤ 4 * tailEnergy h T * tailEnergy h.D T`. -/
theorem norm_pulseReflected_pow_four_le (h : CompactPulse) (T : ℝ) :
    ‖pulseReflected h T‖ ^ 4 ≤ 4 * tailEnergy h T * tailEnergy h.D T := by
  by_cases hE0 : tailEnergy h T = 0
  · rw [hE0, mul_zero, zero_mul]
    have hr0 : ‖pulseReflected h T‖ ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ‖pulseReflected h T‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      set c : ℝ := (2 * tailEnergy h.D T + 2) / (‖pulseReflected h T‖ ^ 2)
      have hc : 0 < c := by
        have := tailEnergy_nonneg h.D T
        positivity
      have hw := norm_sq_pulseReflected_le_weighted h T hc
      rw [hE0, mul_zero, zero_add] at hw
      have hinv : c⁻¹ * tailEnergy h.D T =
          ‖pulseReflected h T‖ ^ 2 * (tailEnergy h.D T / (2 * tailEnergy h.D T + 2)) := by
        dsimp only [c]
        field_simp [hpos.ne']
      have hfrac : tailEnergy h.D T / (2 * tailEnergy h.D T + 2) ≤ 1 / 2 := by
        have hd := tailEnergy_nonneg h.D T
        rw [div_le_iff₀ (by linarith)]
        linarith
      rw [hinv] at hw
      have hhalf := mul_le_mul_of_nonneg_left hfrac hpos.le
      linarith
    have : ‖pulseReflected h T‖ ^ 4 = (‖pulseReflected h T‖ ^ 2) ^ 2 := by ring
    rw [this, hr0]
    norm_num
  · by_cases hED0 : tailEnergy h.D T = 0
    · rw [hED0, mul_zero]
      have hr0 : ‖pulseReflected h T‖ ^ 2 = 0 := by
        by_contra hne
        have hpos : 0 < ‖pulseReflected h T‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
        set c : ℝ := (‖pulseReflected h T‖ ^ 2) / (2 * tailEnergy h T + 2)
        have hc : 0 < c := by
          have := tailEnergy_nonneg h T
          positivity
        have hw := norm_sq_pulseReflected_le_weighted h T hc
        rw [hED0, mul_zero, add_zero] at hw
        have hfrac : c * tailEnergy h T ≤ (1 / 2) * ‖pulseReflected h T‖ ^ 2 := by
          dsimp only [c]
          have hd := tailEnergy_nonneg h T
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          linarith
        linarith
      have : ‖pulseReflected h T‖ ^ 4 = (‖pulseReflected h T‖ ^ 2) ^ 2 := by ring
      rw [this, hr0]
      norm_num
    · have hE_pos : 0 < tailEnergy h T := lt_of_le_of_ne (tailEnergy_nonneg h T) (Ne.symm hE0)
      have hED_pos : 0 < tailEnergy h.D T := lt_of_le_of_ne (tailEnergy_nonneg h.D T) (Ne.symm hED0)
      set c : ℝ := Real.sqrt (tailEnergy h.D T / tailEnergy h T)
      have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hED_pos hE_pos)
      have hw := norm_sq_pulseReflected_le_weighted h T hc
      have hsq_le := pow_le_pow_left₀ (sq_nonneg _) hw 2
      have h4 : ‖pulseReflected h T‖ ^ 4 = (‖pulseReflected h T‖ ^ 2) ^ 2 := by ring
      have hrhs : (c * tailEnergy h T + c⁻¹ * tailEnergy h.D T) ^ 2 =
          4 * tailEnergy h T * tailEnergy h.D T := by
        have hcsq : c ^ 2 = tailEnergy h.D T / tailEnergy h T :=
          Real.sq_sqrt (div_nonneg hED_pos.le hE_pos.le)
        have hexp : (c * tailEnergy h T + c⁻¹ * tailEnergy h.D T) ^ 2 =
            c ^ 2 * tailEnergy h T ^ 2 + 2 * tailEnergy h T * tailEnergy h.D T +
              (c ^ 2)⁻¹ * tailEnergy h.D T ^ 2 := by
          field_simp [hc.ne']
          ring
        rw [hexp, hcsq]
        field_simp [hE_pos.ne', hED_pos.ne']
        ring
      rw [h4, ← hrhs]
      exact hsq_le

/-! ## 3. Exact Horocycle Zero-Mode Receiver Readout -/

/-- **Full Horocycle Zero-Mode Identity for `pulseField`.** Along the closed horocycle `x ∈ (0, 1]`
at height `Y > 0`, the zero mode of `pulseField h` equals `√Y` times the sum of the incoming pulse
and the reflected signal. -/
theorem setIntegral_pulseField_horocycle (h : CompactPulse) (τ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun x : ℝ => pulseField h τ x Y) (Ioc (0 : ℝ) 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, pulseField h τ x Y) =
        ((Real.sqrt Y : ℝ) : ℂ) * (h (τ + Real.log Y) + pulseReflected h (τ - Real.log Y)) := by
  have hpk := h.setIntegral_pulsePacket τ hY
  have heq : (fun x : ℝ => pulseField h τ x Y) = fun x : ℝ => pulsePacket h τ x Y :=
    funext fun x => pulseField_eq_packet h τ x hY
  rwa [heq]

/-- **Causal Horocycle Receiver Readout.** Once the incoming pulse supported in `[-S₀, S₀]` clears
height `Y > 0` (`S₀ < T + 2 * log Y`), `pulseReflected h T` is read directly by averaging
`pulseField h` along the closed horocycle at height `Y`. -/
theorem pulseReflected_eq_horocycle_receiver (h : CompactPulse) {S₀ : ℝ}
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0)
    (T : ℝ) {Y : ℝ} (hY : 0 < Y) (hclear : S₀ < T + 2 * Real.log Y) :
    pulseReflected h T =
      ((Real.sqrt Y : ℝ) : ℂ)⁻¹ * ∫ x in Ioc (0 : ℝ) 1, pulseField h (T + Real.log Y) x Y := by
  have horo := (setIntegral_pulseField_horocycle h (T + Real.log Y) hY).2
  have harg1 : T + Real.log Y + Real.log Y = T + 2 * Real.log Y := by ring
  have harg2 : T + Real.log Y - Real.log Y = T := by ring
  rw [harg1, harg2] at horo
  have hin : h (T + 2 * Real.log Y) = 0 :=
    hS₀ _ (lt_of_lt_of_le hclear (le_abs_self _))
  rw [hin, zero_add] at horo
  have hYne : ((Real.sqrt Y : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hY).ne'
  rw [horo, inv_mul_cancel_left₀ hYne]

/-- Unit-horocycle receiver specialization (`Y = 1`) for `T > S₀`, together with the `L¹` receiver
norm bound. -/
theorem pulseReflected_eq_unit_horocycle_receiver (h : CompactPulse) {S₀ : ℝ}
    (hS₀ : ∀ s : ℝ, S₀ < |s| → h s = 0) {T : ℝ} (hT : S₀ < T) :
    pulseReflected h T = (∫ x in Ioc (0 : ℝ) 1, pulseField h T x 1) ∧
      ‖pulseReflected h T‖ ≤ ∫ x in Ioc (0 : ℝ) 1, ‖pulseField h T x 1‖ := by
  have hrec := pulseReflected_eq_horocycle_receiver h hS₀ T one_pos
    (by rw [Real.log_one]; linarith)
  rw [Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, Real.log_one, add_zero] at hrec
  exact ⟨hrec, hrec ▸ norm_integral_le_integral_norm _⟩

/-! ## 4. Pulse-Uniform Sobolev-Cone Escape and Five-Way Zero-Free Strip Equivalence -/

private theorem one_add_pow_le_two_pow_mul {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    (1 + a) ^ N ≤ (2 : ℝ) ^ N * (1 + a ^ N) := by
  rcases le_or_gt a 1 with ha1 | ha1
  · calc (1 + a) ^ N ≤ (2 : ℝ) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = (2 : ℝ) ^ N * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ) ^ N * (1 + a ^ N) :=
          mul_le_mul_of_nonneg_left (by linarith [pow_nonneg ha N]) (by positivity)
  · calc (1 + a) ^ N ≤ (2 * a) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = (2 : ℝ) ^ N * a ^ N := mul_pow 2 a N
      _ ≤ (2 : ℝ) ^ N * (1 + a ^ N) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem integral_norm_sq_le_two_mul_support (g : CompactPulse) {S₀ : ℝ}
    (hS₀ : 0 < S₀) (hg : ∀ s : ℝ, S₀ < |s| → g s = 0) :
    (∫ S : ℝ, ‖g S‖) ^ 2 ≤ 2 * S₀ * ∫ S : ℝ, ‖g S‖ ^ 2 := by
  set A : ℝ := ∫ S : ℝ, ‖g S‖
  set E : ℝ := ∫ S : ℝ, ‖g S‖ ^ 2
  set t : ℝ := A / (2 * S₀)
  have hsupp : A = ∫ S in Icc (-S₀) S₀, ‖g S‖ := by
    dsimp only [A]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_).symm
    have hgt : S₀ < |s| := not_le.mp fun hle => hs (abs_le.mp hle)
    simp [hg s hgt]
  have hg1 : IntegrableOn (fun S : ℝ => 2 * t * ‖g S‖) (Icc (-S₀) S₀) :=
    (g.integrable_toFun.norm.const_mul (2 * t)).integrableOn
  have hg2_all : Integrable fun S : ℝ => ‖g S‖ ^ 2 :=
    (memLp_two_pulse g).integrable_norm_pow (by norm_num)
  have hg2 : IntegrableOn (fun S : ℝ => ‖g S‖ ^ 2) (Icc (-S₀) S₀) := hg2_all.integrableOn
  have hc : IntegrableOn (fun _S : ℝ => t ^ 2) (Icc (-S₀) S₀) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hpt : ∀ S : ℝ, 2 * t * ‖g S‖ ≤ ‖g S‖ ^ 2 + t ^ 2 := fun S => by
    nlinarith [sq_nonneg (‖g S‖ - t)]
  have hmono := setIntegral_mono hg1 (hg2.add hc) hpt
  have hsum : IntegrableOn (fun S : ℝ => ‖g S‖ ^ 2 + t ^ 2) (Icc (-S₀) S₀) := hg2.add hc
  have hlhs : (∫ S in Icc (-S₀) S₀, 2 * t * ‖g S‖) = 2 * t * A := by
    rw [integral_const_mul, ← hsupp]
  have hconst : (∫ _S in Icc (-S₀) S₀, t ^ 2) = 2 * S₀ * t ^ 2 := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hsubE : (∫ S in Icc (-S₀) S₀, ‖g S‖ ^ 2) ≤ E :=
    setIntegral_le_integral hg2_all (Eventually.of_forall fun _ => sq_nonneg _)
  rw [hlhs, integral_add hg2 hc, hconst] at hmono
  have hineq : 2 * t * A ≤ E + 2 * S₀ * t ^ 2 := by linarith
  have h2tA : 2 * t * A = A ^ 2 / S₀ := by dsimp only [t]; field_simp [hS₀.ne']; ring
  have h2St : 2 * S₀ * t ^ 2 = A ^ 2 / (2 * S₀) := by dsimp only [t]; field_simp [hS₀.ne']
  rw [h2tA, h2St] at hineq
  have hmul := mul_le_mul_of_nonneg_left hineq (show (0 : ℝ) ≤ 2 * S₀ by positivity)
  have hl1 : 2 * S₀ * (A ^ 2 / S₀) = 2 * A ^ 2 := by field_simp [hS₀.ne']
  have hl2 : 2 * S₀ * (E + A ^ 2 / (2 * S₀)) = 2 * S₀ * E + A ^ 2 := by
    field_simp [hS₀.ne']
  linarith

private theorem norm_pulseAmplitude_le_l2_of_support (g : CompactPulse) {S₀ σ : ℝ}
    (hS₀ : 0 < S₀) (hg : ∀ s : ℝ, S₀ < |s| → g s = 0)
    {w : ℂ} (hw : |w.im| ≤ σ) :
    ‖pulseAmplitude g w‖ ≤
      (2 * Real.pi)⁻¹ * Real.exp (σ * S₀) * Real.sqrt (2 * S₀) *
        Real.sqrt (∫ S : ℝ, ‖g S‖ ^ 2) := by
  have hpi_inv : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint : Integrable fun S : ℝ => ‖g S‖ * Real.exp (σ * S₀) :=
    g.integrable_toFun.norm.mul_const _
  have h1 : ‖pulseAmplitude g w‖ ≤ (2 * Real.pi)⁻¹ * ((∫ S : ℝ, ‖g S‖) * Real.exp (σ * S₀)) := by
    rw [pulseAmplitude, norm_mul, hpi_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun S => ?_)).trans
      (le_of_eq (integral_mul_const _ _))
    exact (g.norm_mul_cexp_le hg w S).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hw hS₀.le)) (norm_nonneg _))
  have hA_nn : 0 ≤ ∫ S : ℝ, ‖g S‖ := integral_nonneg fun _ => norm_nonneg _
  have hcs := Real.sqrt_le_sqrt (integral_norm_sq_le_two_mul_support g hS₀ hg)
  rw [Real.sqrt_sq hA_nn, Real.sqrt_mul (by positivity : 0 ≤ 2 * S₀)] at hcs
  calc ‖pulseAmplitude g w‖
      ≤ (2 * Real.pi)⁻¹ * ((∫ S : ℝ, ‖g S‖) * Real.exp (σ * S₀)) := h1
    _ ≤ (2 * Real.pi)⁻¹ *
          ((Real.sqrt (2 * S₀) * Real.sqrt (∫ S : ℝ, ‖g S‖ ^ 2)) * Real.exp (σ * S₀)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcs (Real.exp_pos _).le)
          (by positivity)
    _ = (2 * Real.pi)⁻¹ * Real.exp (σ * S₀) * Real.sqrt (2 * S₀) *
          Real.sqrt (∫ S : ℝ, ‖g S‖ ^ 2) := by ring

/-- **Converse Zero-Free Strip Theorem for `pulseReflected`.** If every compact pulse satisfies
`‖pulseReflected h T‖ = O_h(e^{-δ T})` on `T ≥ 0` (`0 < δ ≤ 1/4`), then every zero `ρ` of `ζ` with
`0 < Re ρ` satisfies `Re ρ ≤ 1 - 2δ`. -/
theorem re_le_of_pulseReflected_decay {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hdecay : ∀ h : CompactPulse, ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      ‖pulseReflected h T‖ ≤ C * Real.exp (-δ * T))
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) :
    ρ.re ≤ 1 - 2 * δ := by
  by_contra hgt
  push Not at hgt
  have hρ1 : ρ.re < 1 := lt_of_not_ge fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hρ
  have hne1 : ρ ≠ 1 := fun he => by rw [he, one_re] at hρ1; exact lt_irrefl _ hρ1
  set p : ℂ := (ρ - 1) / 2
  have hp1 : 1 + 2 * p = ρ := by dsimp only [p]; ring
  have hp_xi : xi (1 + 2 * p) = 0 := by rw [hp1]; exact (xi_eq_zero_iff hρ0 hne1).2 hρ
  have hp_re : p.re = (ρ.re - 1) / 2 := by simp [p]
  obtain ⟨C₀, hC₀⟩ := hdecay (excitingPulse p)
  have hzero := pulseAmplitude_eq_zero_of_pulseReflected_decay (excitingPulse p) hδ0 hC₀ hp_xi
    (by rw [hp_re]; linarith) (by rw [hp_re]; linarith) (by rw [hp_re]; linarith)
  exact pulseAmplitude_excitingPulse_ne_zero p hzero

/-- **Pulse-Uniform Sobolev-Cone Tail Escape from a Zero-Free Strip.** If every zero of `ζ` with
`0 < Re ρ` satisfies `Re ρ ≤ 1 - 2δ` (`0 < σ < δ ≤ 1/4`), then for every support half-width
`S₀ > 0` there exist a Sobolev order `N : ℕ` and a constant `K > 0` **independent of `h` and `T`**
such that every compact pulse `h` supported in `[-S₀, S₀]` obeys
`tailEnergy h T ≤ K * ((∫ ‖h‖²) + ∫ ‖h^{[N]}‖²) * e^{-2σ T}` for all `T ≥ 0`. -/
theorem exists_sobolev_cone_tailEnergy_decay_of_zeroFree {δ σ : ℝ}
    (hδ : δ ≤ 1 / 4) (hσ : 0 < σ) (hσδ : σ < δ)
    (hz : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * δ)
    {S₀ : ℝ} (hS₀ : 0 < S₀) :
    ∃ (N : ℕ) (K : ℝ), 0 < K ∧ ∀ h : CompactPulse,
      (∀ s : ℝ, S₀ < |s| → h s = 0) → ∀ T : ℝ, 0 ≤ T →
        tailEnergy h T ≤
          K * ((∫ S : ℝ, ‖h S‖ ^ 2) + ∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2) *
            Real.exp (-2 * σ * T) := by
  set Θ : ℝ := 1 - 2 * δ
  have hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0 := fun z hz' h0 => by
    have := hz z h0 (by linarith)
    linarith
  obtain ⟨κ, hκ, hζ⟩ := exists_zeta_lower_bound_subpolynomial_of_zeroFree (Θ := Θ) (by linarith)
    (by linarith) hzf (δ := 2 * (δ - σ)) (by linarith) (by linarith) (ε := 1) one_pos
  set boxU : Set ℂ := {u : ℂ | (-σ ≤ u.re ∧ u.re ≤ 0) ∧ 1 ≤ |u.im| ∧ |u.im| ≤ 3}
  have hboxU_c : IsCompact boxU := by
    have heq : boxU = ((Icc (-σ) 0) ×ℂ (Icc (-3 : ℝ) 3)) ∩ {u : ℂ | 1 ≤ |u.im|} := by
      ext u
      simp only [boxU, mem_inter_iff, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq, abs_le]
      tauto
    rw [heq]
    exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont_ζU : ContinuousOn (fun u : ℂ => (riemannZeta (1 + 2 * u))⁻¹) boxU := by
    intro u hu
    have hne1 : 1 + 2 * u ≠ 1 := fun he => by
      have him0 := congrArg Complex.im he; simp at him0
      have := hu.2.1; rw [him0, abs_zero] at this; linarith
    have hz0 : riemannZeta (1 + 2 * u) ≠ 0 := hzf _ (by simp [Θ]; linarith [hu.1.1])
    exact ((ContinuousAt.comp (f := fun v : ℂ => 1 + 2 * v)
      (differentiableAt_riemannZeta hne1).continuousAt (by fun_prop)).inv₀ hz0).continuousWithinAt
  obtain ⟨Mζ, hMζ⟩ := hboxU_c.exists_bound_of_continuousOn hcont_ζU
  have hζ_shift : ∀ s : ℂ, -σ + 1 / 2 ≤ s.re → s.re ≤ 1 / 2 → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ (max (max Mζ 0) (4 / κ)) * |s.im| ^ 1 := by
    intro s hs1 hs2 hsim
    set u : ℂ := s - 1 / 2
    have hu_eq : 1 + 2 * u = 2 * s := by simp [u]; ring
    have hu1 : -σ ≤ u.re := by simp [u]; linarith
    have hu2 : u.re ≤ 0 := by simp [u]; linarith
    have huim : |u.im| = |s.im| := by simp [u]
    rw [← hu_eq, ← huim]
    have hpow1 : (1 : ℝ) ≤ |u.im| ^ 1 := by simpa [huim] using hsim
    rcases le_or_gt |u.im| 3 with hsmall | hbig
    · calc ‖(riemannZeta (1 + 2 * u))⁻¹‖
          ≤ Mζ := hMζ u ⟨⟨hu1, hu2⟩, by rwa [huim], hsmall⟩
        _ ≤ max (max Mζ 0) (4 / κ) * 1 := by
            rw [mul_one]; exact (le_max_left Mζ 0).trans (le_max_left _ _)
        _ ≤ max (max Mζ 0) (4 / κ) * |u.im| ^ 1 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have him : |(1 + 2 * u).im| = 2 * |u.im| := by
        have : (1 + 2 * u).im = 2 * u.im := by simp
        rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hb := hζ (1 + 2 * u) (by simp [Θ]; linarith) (by rw [him]; linarith)
      rw [Real.rpow_neg_one, him] at hb
      have hpos : 0 < ‖riemannZeta (1 + 2 * u)‖ := lt_of_lt_of_le (by positivity) hb
      rw [norm_inv, inv_le_comm₀ hpos (by positivity)]
      have h2t : 2 + 2 * |u.im| ≤ 4 * |u.im| := by linarith
      calc (max (max Mζ 0) (4 / κ) * |u.im| ^ 1)⁻¹
          ≤ ((4 / κ) * |u.im|)⁻¹ := by
            rw [pow_one]
            exact inv_anti₀ (by positivity)
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        _ = κ * (4 * |u.im|)⁻¹ := by field_simp
        _ ≤ κ * (2 + 2 * |u.im|)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h2t) hκ.le
        _ ≤ ‖riemannZeta (1 + 2 * u)‖ := hb
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le (by positivity) hζ_shift
  have hxi_left : ∀ u : ℂ, -σ ≤ u.re → xi (1 + 2 * u) ≠ 0 :=
    fun _ hu1 => RingdownRate.xi_ne_zero_of_zeroFree hδ hσδ hz hu1
  have hdiff_φ : ∀ {u : ℂ}, u ≠ 1 / 2 → xi (1 + 2 * u) ≠ 0 →
      DifferentiableAt ℂ scatteringPhase u := by
    intro u hne hxi
    have hd : 2 * u - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 2)
    unfold scatteringPhase
    exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) u).div (by fun_prop) hd).mul
      (((xi_differentiable _).comp u (by fun_prop)).div
        ((xi_differentiable _).comp u (by fun_prop)) hxi)
  set Kbox : Set ℂ := Icc (-σ) 0 ×ℂ Icc (-1 : ℝ) 1
  have hKbox : IsCompact Kbox := isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn scatteringPhase Kbox := by
    intro u hu
    have hu' := Complex.mem_reProdIm.1 hu
    have hne : u ≠ 1 / 2 := fun he => by have := hu'.1.2; rw [he] at this; norm_num at this
    exact (hdiff_φ hne (hxi_left u hu'.1.1)).continuousAt.continuousWithinAt
  obtain ⟨Mφ, hMφ⟩ := hKbox.exists_bound_of_continuousOn hcontK
  set Cφ : ℝ := max (max Mφ 0) CQ
  have hCφ_nn : 0 ≤ Cφ := (le_max_right Mφ 0).trans (le_max_left _ _)
  have hφ_strip : ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 →
      ‖scatteringPhase u‖ ≤ Cφ * (1 + |u.im|) ^ NQ := by
    intro u hu1 hu2
    by_cases hut : 1 ≤ |u.im|
    · have h2le : ‖(2 : ℂ) / (2 * u - 1)‖ ≤ 1 := by
        have him2 : (2 : ℝ) ≤ |(2 * u - 1).im| := by simp; linarith
        have hn2 : (2 : ℝ) ≤ ‖2 * u - 1‖ := him2.trans (Complex.abs_im_le_norm _)
        rw [norm_div, Complex.norm_ofNat, div_le_one (by linarith)]
        exact hn2
      have hsc_eq : scatteringPhase u = ((2 : ℂ) / (2 * u - 1)) * scatterQ (u + 1 / 2) := by
        unfold scatteringPhase scatterQ
        rw [show 2 * (u + 1 / 2) - 1 = 2 * u by ring, show 2 * (u + 1 / 2) = 1 + 2 * u by ring]
        ring
      have hQb : ‖scatterQ (u + 1 / 2)‖ ≤ CQ * |u.im| ^ NQ := by
        simpa using hQ (u + 1 / 2) (by simp; linarith) (by simp; linarith) (by simpa using hut)
      have ht1 : |u.im| ^ NQ ≤ (1 + |u.im|) ^ NQ :=
        pow_le_pow_left₀ (abs_nonneg _) (by linarith) NQ
      rw [hsc_eq, norm_mul]
      calc ‖(2 : ℂ) / (2 * u - 1)‖ * ‖scatterQ (u + 1 / 2)‖
          ≤ 1 * (CQ * |u.im| ^ NQ) := mul_le_mul h2le hQb (norm_nonneg _) (by positivity)
        _ ≤ Cφ * (1 + |u.im|) ^ NQ := by
            rw [one_mul]
            exact mul_le_mul (le_max_right _ _) ht1 (by positivity) hCφ_nn
    · have hut' := abs_le.1 (not_le.1 hut).le
      have hb := hMφ u (Complex.mem_reProdIm.2 ⟨⟨hu1, hu2⟩, hut'⟩)
      have h1pow : (1 : ℝ) ≤ (1 + |u.im|) ^ NQ := one_le_pow₀ (by linarith [abs_nonneg u.im])
      calc ‖scatteringPhase u‖ ≤ Mφ := hb
        _ ≤ Cφ * 1 := by rw [mul_one]; exact (le_max_left Mφ 0).trans (le_max_left _ _)
        _ ≤ Cφ * (1 + |u.im|) ^ NQ := mul_le_mul_of_nonneg_left h1pow hCφ_nn
  set N : ℕ := NQ + 2
  set C_PW : ℝ := (2 * Real.pi)⁻¹ * Real.exp (σ * S₀) * Real.sqrt (2 * S₀) * Real.sqrt 2
  set M_tot : ℝ := Cφ * (2 : ℝ) ^ N * C_PW * Real.pi
  set K : ℝ := M_tot ^ 2 / (2 * σ) + 1
  refine ⟨N, K, by positivity, fun h hsupp T hT => ?_⟩
  set Sn : ℝ := (∫ S : ℝ, ‖h S‖ ^ 2) + ∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2
  have hSn_nn : 0 ≤ Sn := add_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)
  set Bh : ℝ := Cφ * (2 : ℝ) ^ N * C_PW * Real.sqrt Sn
  have hBh_nn : 0 ≤ Bh := by dsimp only [Bh, C_PW]; positivity
  have hB_left : ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 →
      ‖pulseAmplitude h (-I * u) * scatteringPhase u‖ ≤ Bh / (1 + u.im ^ 2) := by
    intro u hu1 hu2
    set w : ℂ := -I * u
    have hw_re : w.re = u.im := by simp [w]
    have hw_im : |w.im| ≤ σ := by
      have : w.im = -u.re := by simp [w]
      rw [this, abs_neg, abs_le]; constructor <;> linarith
    have ha0 := norm_pulseAmplitude_le_l2_of_support h hS₀ hsupp hw_im
    have haN := norm_pulseAmplitude_le_l2_of_support (CompactPulse.iterD N h) hS₀
      (CompactPulse.iterD_eq_zero_of_support_bound N h hsupp) hw_im
    have hsqrt_sum : Real.sqrt (∫ S : ℝ, ‖h S‖ ^ 2) +
        Real.sqrt (∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2) ≤ Real.sqrt 2 * Real.sqrt Sn := by
      set a := ∫ S : ℝ, ‖h S‖ ^ 2
      set b := ∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2
      have ha_nn : 0 ≤ a := integral_nonneg fun _ => sq_nonneg _
      have hb_nn : 0 ≤ b := integral_nonneg fun _ => sq_nonneg _
      have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt (a + b)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (add_nonneg ha_nn hb_nn)]
        nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha_nn, Real.sq_sqrt hb_nn]
      have habs := sq_le_sq.mp hsq
      rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at habs
    have hamp_sum : ‖pulseAmplitude h w‖ + ‖w‖ ^ N * ‖pulseAmplitude h w‖ ≤
        C_PW * Real.sqrt Sn := by
      rw [← CompactPulse.norm_amplitude_iterD N h w]
      set c₀ : ℝ := (2 * Real.pi)⁻¹ * Real.exp (σ * S₀) * Real.sqrt (2 * S₀)
      have hc₀ : 0 ≤ c₀ := by dsimp only [c₀]; positivity
      calc ‖pulseAmplitude h w‖ + ‖pulseAmplitude (CompactPulse.iterD N h) w‖
          ≤ c₀ * (Real.sqrt (∫ S : ℝ, ‖h S‖ ^ 2) +
              Real.sqrt (∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2)) := by linarith
        _ ≤ c₀ * (Real.sqrt 2 * Real.sqrt Sn) := mul_le_mul_of_nonneg_left hsqrt_sum hc₀
        _ = C_PW * Real.sqrt Sn := by dsimp only [C_PW, c₀]; ring
    have huim_pow : |u.im| ^ N ≤ ‖w‖ ^ N := by
      rw [← hw_re]
      exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm w) N
    have hpoly : ‖pulseAmplitude h w‖ * (1 + |u.im|) ^ N ≤ (2 : ℝ) ^ N * (C_PW * Real.sqrt Sn) := by
      calc ‖pulseAmplitude h w‖ * (1 + |u.im|) ^ N
          ≤ ‖pulseAmplitude h w‖ * ((2 : ℝ) ^ N * (1 + |u.im| ^ N)) :=
            mul_le_mul_of_nonneg_left (one_add_pow_le_two_pow_mul (abs_nonneg _) N) (norm_nonneg _)
        _ ≤ ‖pulseAmplitude h w‖ * ((2 : ℝ) ^ N * (1 + ‖w‖ ^ N)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (norm_nonneg _)
        _ = (2 : ℝ) ^ N * (‖pulseAmplitude h w‖ + ‖w‖ ^ N * ‖pulseAmplitude h w‖) := by ring
        _ ≤ (2 : ℝ) ^ N * (C_PW * Real.sqrt Sn) :=
            mul_le_mul_of_nonneg_left hamp_sum (by positivity)
    have ht2 : 1 + u.im ^ 2 ≤ (1 + |u.im|) ^ 2 := by nlinarith [abs_nonneg u.im, sq_abs u.im]
    rw [le_div_iff₀ (by positivity), norm_mul]
    calc ‖pulseAmplitude h w‖ * ‖scatteringPhase u‖ * (1 + u.im ^ 2)
        ≤ ‖pulseAmplitude h w‖ * (Cφ * (1 + |u.im|) ^ NQ) * (1 + |u.im|) ^ 2 := by
          gcongr
          exact hφ_strip u hu1 hu2
      _ = Cφ * (‖pulseAmplitude h w‖ * (1 + |u.im|) ^ N) := by dsimp only [N]; ring
      _ ≤ Cφ * ((2 : ℝ) ^ N * (C_PW * Real.sqrt Sn)) := mul_le_mul_of_nonneg_left hpoly hCφ_nn
      _ = Bh := by dsimp only [Bh]; ring
  have hpt_decay : ∀ u : ℝ, 0 ≤ u → ‖pulseReflected h u‖ ≤ (Bh * Real.pi) * Real.exp (-σ * u) := by
    intro u hu
    set Φ : ℂ → ℂ := fun s =>
      pulseAmplitude h (-I * s) * scatteringPhase s * Complex.exp (s * (u : ℂ)) with hΦ
    have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → -σ ≤ s.re ∧ s.re ≤ 0 := by
      intro s hs; rw [uIcc_of_ge (by linarith)] at hs; exact hs
    have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → DifferentiableAt ℂ Φ s := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
      exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
        (hdiff_φ hne (hxi_left s hs1))).mul (by fun_prop))
    have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → ‖Φ s‖ ≤ Bh / (1 + s.im ^ 2) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := hstrip s hs
      have he : ‖Complex.exp (s * (u : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        have : (s * (u : ℂ)).re = s.re * u := by simp
        rw [this]
        exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hs2 hu)
      simp only [hΦ]; rw [norm_mul]
      calc ‖pulseAmplitude h (-I * s) * scatteringPhase s‖ * ‖Complex.exp (s * (u : ℂ))‖
          ≤ Bh / (1 + s.im ^ 2) * 1 :=
            mul_le_mul (hB_left s hs1 hs2) he (norm_nonneg _) (by positivity)
        _ = Bh / (1 + s.im ^ 2) := mul_one _
    have hshift := integral_vertical_line_shift_of_decay hd hbΦ
    have hpk : pulseReflected h u = ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + (t : ℂ) * I) := by
      rw [pulseReflected]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hΦ]
      have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
      rw [e, show -I * ((t : ℂ) * I) = (t : ℂ) by linear_combination (-(t : ℂ)) * I_sq]
      congr 2; ring
    rw [hpk, hshift]
    have hpt : ∀ t : ℝ,
        ‖Φ (((-σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Bh * (1 + t ^ 2)⁻¹ * Real.exp (-σ * u) := by
      intro t
      have hre : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).re = -σ := by simp
      have him : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
      simp only [hΦ]; rw [norm_mul, Complex.norm_exp]
      have : ((((-σ : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ)).re = -σ * u := by simp
      rw [this]
      have hb := hB_left _ (by rw [hre]) (by rw [hre]; linarith)
      rw [him, div_eq_mul_inv] at hb
      exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    have hint : Integrable fun t : ℝ => Bh * (1 + t ^ 2)⁻¹ * Real.exp (-σ * u) :=
      (integrable_inv_one_add_sq.const_mul Bh).mul_const _
    calc ‖∫ t : ℝ, Φ (((-σ : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, Bh * (1 + t ^ 2)⁻¹ * Real.exp (-σ * u) :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
      _ = (Bh * Real.pi) * Real.exp (-σ * u) := by
          rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]
  have hdom : IntegrableOn (fun u : ℝ => (Bh * Real.pi) ^ 2 * Real.exp (-2 * σ * u)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith) T).const_mul _
  have hle : tailEnergy h T ≤ ∫ u in Ioi T, (Bh * Real.pi) ^ 2 * Real.exp (-2 * σ * u) := by
    refine setIntegral_mono_on (integrable_norm_sq_pulseReflected h).integrableOn hdom
      measurableSet_Ioi fun u hu => ?_
    have hb := hpt_decay u (hT.trans (mem_Ioi.mp hu).le)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [mul_pow, sq (Real.exp (-σ * u)), ← Real.exp_add] at hsq
    refine hsq.trans (le_of_eq ?_)
    congr 2; ring
  have hint_eq : (∫ u in Ioi T, (Bh * Real.pi) ^ 2 * Real.exp (-2 * σ * u)) =
      ((Bh * Real.pi) ^ 2 / (2 * σ)) * Real.exp (-2 * σ * T) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -2 * σ < 0) T]
    field_simp
  have hBh_sq : (Bh * Real.pi) ^ 2 = M_tot ^ 2 * Sn := by
    have h1 : Bh * Real.pi = M_tot * Real.sqrt Sn := by dsimp only [Bh, M_tot]; ring
    rw [h1, mul_pow, Real.sq_sqrt hSn_nn]
  have hK_le : (M_tot ^ 2 * Sn) / (2 * σ) ≤ K * Sn := by
    dsimp only [K]
    have : (M_tot ^ 2 * Sn) / (2 * σ) = (M_tot ^ 2 / (2 * σ)) * Sn := by ring
    rw [this]
    nlinarith
  exact hle.trans (hint_eq.le.trans (by
    rw [hBh_sq]
    exact mul_le_mul_of_nonneg_right hK_le (Real.exp_pos _).le))

private theorem le_of_pow_four_le {x y : ℝ} (hy : 0 ≤ y) (h4 : x ^ 4 ≤ y ^ 4) :
    x ≤ y := by
  by_contra hgt
  push Not at hgt
  have : y ^ 4 < x ^ 4 := pow_lt_pow_left₀ hgt hy (by norm_num)
  linarith

/-- **Five-Way Equivalence of Zero-Free Strips, Bulk Ringdown, Cusp Readout, Tail Energy, and
Uniform Sobolev-Cone Escape.** For every `0 < δ ≤ 1/4`, all five properties are unconditionally
equivalent. -/
theorem zeroFreeStrip_tailEnergy_equivalences {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4) :
    let P_strip := ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * δ
    let P_bulk := ∀ ε : ℝ, 0 < ε → ∀ (h : CompactPulse) (x Y : ℝ), 0 < Y →
      ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ → ‖pulseField h τ x Y‖ ≤ C * Real.exp (-(δ - ε) * τ)
    let P_cusp := ∀ ε : ℝ, 0 < ε → ∀ h : CompactPulse,
      ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → ‖pulseReflected h T‖ ≤ C * Real.exp (-(δ - ε) * T)
    let P_tail := ∀ ε : ℝ, 0 < ε → ∀ h : CompactPulse,
      ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → tailEnergy h T ≤ C * Real.exp (-2 * (δ - ε) * T)
    let P_sobolev := ∀ σ : ℝ, 0 < σ → σ < δ → ∀ S₀ : ℝ, 0 < S₀ →
      ∃ (N : ℕ) (K : ℝ), 0 < K ∧ ∀ h : CompactPulse,
        (∀ s : ℝ, S₀ < |s| → h s = 0) → ∀ T : ℝ, 0 ≤ T →
          tailEnergy h T ≤
            K * ((∫ S : ℝ, ‖h S‖ ^ 2) + ∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2) *
              Real.exp (-2 * σ * T)
    (P_strip ↔ P_bulk) ∧ (P_strip ↔ P_cusp) ∧ (P_strip ↔ P_tail) ∧ (P_strip ↔ P_sobolev) := by
  intro P_strip P_bulk P_cusp P_tail P_sobolev
  have h12 : P_strip ↔ P_bulk := RingdownRate.zeroFreeStrip_iff_pulse_ringdown hδ0 hδ
  have h15 : P_strip → P_sobolev := fun hz σ hσ0 hσδ S₀ hS₀ =>
    exists_sobolev_cone_tailEnergy_decay_of_zeroFree hδ hσ0 hσδ hz hS₀
  have h54 : P_sobolev → P_tail := by
    intro hsob ε hε h
    set σ : ℝ := δ - min ε (δ / 2)
    have hσ0 : 0 < σ := by
      have : min ε (δ / 2) ≤ δ / 2 := min_le_right _ _
      dsimp only [σ]; linarith
    have hσδ : σ < δ := by
      have : 0 < min ε (δ / 2) := lt_min hε (by linarith)
      dsimp only [σ]; linarith
    obtain ⟨S₁, hS₁_nn, hS₁⟩ := h.exists_support_bound
    obtain ⟨N, K, hK, hbd⟩ := hsob σ hσ0 hσδ (S₁ + 1) (by linarith)
    set C : ℝ := K * ((∫ S : ℝ, ‖h S‖ ^ 2) + ∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2)
    have hC_nn : 0 ≤ C := mul_nonneg hK.le
      (add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _))
    refine ⟨C, fun T hT => (hbd h (fun s hs => hS₁ s (by linarith)) T hT).trans ?_⟩
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC_nn
    have : min ε (δ / 2) ≤ ε := min_le_left _ _
    dsimp only [σ]; nlinarith
  have h43 : P_tail → P_cusp := by
    intro htail ε hε h
    set ε' : ℝ := min ε (δ / 2)
    have hε'0 : 0 < ε' := lt_min hε (by linarith)
    have hε'le : ε' ≤ ε := min_le_left _ _
    obtain ⟨C₁, hC₁⟩ := htail ε' hε'0 h
    obtain ⟨C₂, hC₂⟩ := htail ε' hε'0 h.D
    set M : ℝ := Real.sqrt (Real.sqrt (4 * max C₁ 0 * max C₂ 0))
    have hM_nn : 0 ≤ M := Real.sqrt_nonneg _
    have hM4 : M ^ 4 = 4 * max C₁ 0 * max C₂ 0 := by
      dsimp only [M]
      have h1 : (Real.sqrt (Real.sqrt (4 * max C₁ 0 * max C₂ 0))) ^ 4 =
          ((Real.sqrt (Real.sqrt (4 * max C₁ 0 * max C₂ 0))) ^ 2) ^ 2 := by ring
      rw [h1, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
    refine ⟨M, fun T hT => ?_⟩
    have hreg := norm_pulseReflected_pow_four_le h T
    have hb1 : tailEnergy h T ≤ max C₁ 0 * Real.exp (-2 * (δ - ε') * T) :=
      (hC₁ T hT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hb2 : tailEnergy h.D T ≤ max C₂ 0 * Real.exp (-2 * (δ - ε') * T) :=
      (hC₂ T hT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hprod : 4 * tailEnergy h T * tailEnergy h.D T ≤
        (M * Real.exp (-(δ - ε') * T)) ^ 4 := by
      have hmul : 4 * tailEnergy h T * tailEnergy h.D T ≤
          4 * (max C₁ 0 * Real.exp (-2 * (δ - ε') * T)) *
            (max C₂ 0 * Real.exp (-2 * (δ - ε') * T)) := by
        have h12_le := mul_le_mul hb1 hb2 (tailEnergy_nonneg h.D T) (by positivity)
        linarith
      have hrhs : 4 * (max C₁ 0 * Real.exp (-2 * (δ - ε') * T)) *
          (max C₂ 0 * Real.exp (-2 * (δ - ε') * T)) =
          (M * Real.exp (-(δ - ε') * T)) ^ 4 := by
        rw [mul_pow, hM4]
        have hexp4 : (Real.exp (-(δ - ε') * T)) ^ 4 =
            Real.exp (-2 * (δ - ε') * T) * Real.exp (-2 * (δ - ε') * T) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          congr 1; push_cast; ring
        rw [hexp4]; ring
      exact hmul.trans hrhs.le
    have hpt := le_of_pow_four_le (norm_nonneg _) (by positivity) (hreg.trans hprod)
    exact hpt.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hM_nn)
  have h31 : P_cusp → P_strip := by
    intro hcusp ρ hρ hρ0
    by_contra hlt
    push Not at hlt
    set ε : ℝ := (ρ.re - (1 - 2 * δ)) / 4
    have hε0 : 0 < ε := by dsimp only [ε]; linarith
    have hεδ : ε < δ := by
      have hρ1 : ρ.re < 1 := lt_of_not_ge fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hρ
      dsimp only [ε]; linarith
    have := re_le_of_pulseReflected_decay (δ := δ - ε) (by linarith) (by linarith)
      (fun h => hcusp ε hε0 h) hρ hρ0
    dsimp only [ε] at this
    linarith
  exact ⟨h12, ⟨fun h => h43 (h54 (h15 h)), h31⟩,
    ⟨fun h => h54 (h15 h), fun h => h31 (h43 h)⟩,
    ⟨h15, fun h => h31 (h43 (h54 h))⟩⟩

/-- **Riemann Hypothesis Equivalence with Quarter-Rate Tail-Energy Decay and Sobolev-Cone Escape.** -/
theorem riemannHypothesis_iff_tailEnergy_decay :
    (RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∀ h : CompactPulse,
        ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → tailEnergy h T ≤ C * Real.exp (-(1 / 2 - 2 * ε) * T)) ∧
    (RiemannHypothesis ↔
      ∀ σ : ℝ, 0 < σ → σ < 1 / 4 → ∀ S₀ : ℝ, 0 < S₀ →
        ∃ (N : ℕ) (K : ℝ), 0 < K ∧ ∀ h : CompactPulse,
          (∀ s : ℝ, S₀ < |s| → h s = 0) → ∀ T : ℝ, 0 ≤ T →
            tailEnergy h T ≤
              K * ((∫ S : ℝ, ‖h S‖ ^ 2) + ∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2) *
                Real.exp (-2 * σ * T)) := by
  have heq := zeroFreeStrip_tailEnergy_equivalences (δ := 1 / 4) (by norm_num) le_rfl
  have hrh_bulk := RingdownRate.riemannHypothesis_iff_pulse_ringdown
  have hrh_strip : RiemannHypothesis ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * (1 / 4 : ℝ) :=
    hrh_bulk.trans heq.1.symm
  refine ⟨hrh_strip.trans (heq.2.2.1.trans ?_), hrh_strip.trans heq.2.2.2⟩
  constructor <;> intro H ε hε h <;> obtain ⟨C, hC⟩ := H ε hε h <;>
    refine ⟨C, fun T hT => ?_⟩ <;>
    convert hC T hT using 3 <;> ring

/-- **Explicit RH Falsification Criterion via Actual Modular Tail Energy.** The Riemann Hypothesis is
false if and only if some compact pulse `h` and `ε > 0` produce unboundedly many late times `T ≥ 0`
at which `tailEnergy h T > C * e^{-(1/2 - 2ε) T}` for every `C : ℝ`. -/
theorem not_riemannHypothesis_iff_exists_slower_tailEnergy :
    ¬RiemannHypothesis ↔
      ∃ (ε : ℝ) (h : CompactPulse), 0 < ε ∧
        ∀ C : ℝ, ∃ T : ℝ, 0 ≤ T ∧ C * Real.exp (-(1 / 2 - 2 * ε) * T) < tailEnergy h T := by
  rw [riemannHypothesis_iff_tailEnergy_decay.1]
  push Not
  constructor
  · rintro ⟨ε, hε, h, hC⟩
    exact ⟨ε, h, hε, hC⟩
  · rintro ⟨ε, h, hε, hC⟩
    exact ⟨ε, hε, h, hC⟩

/-- **Unconditional Sub-`3001/48000` Pulse-Uniform Sobolev-Cone Tail Escape on `PSL₂(ℤ)\ℍ`.** -/
theorem unconditional_sobolev_cone_tailEnergy_escape {σ S₀ : ℝ}
    (hσ0 : 0 < σ) (hσ : σ < 3001 / 48000) (hS₀ : 0 < S₀) :
    ∃ (N : ℕ) (K : ℝ), 0 < K ∧ ∀ h : CompactPulse,
      (∀ s : ℝ, S₀ < |s| → h s = 0) → ∀ T : ℝ, 0 ≤ T →
        tailEnergy h T ≤
          K * ((∫ S : ℝ, ‖h S‖ ^ 2) + ∫ S : ℝ, ‖CompactPulse.iterD N h S‖ ^ 2) *
            Real.exp (-2 * σ * T) := by
  have hz : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * (3001 / 48000 : ℝ) := by
    intro ρ h0 hpos
    have hmem := riemannZeta_zero_mem_sub_quasiRH_strip hpos h0
    linarith [hmem.2]
  exact exists_sobolev_cone_tailEnergy_decay_of_zeroFree (δ := 3001 / 48000)
    (by norm_num) hσ0 hσ hz hS₀

end GaloisForLFunctions.BlackHoleRingdown

end
