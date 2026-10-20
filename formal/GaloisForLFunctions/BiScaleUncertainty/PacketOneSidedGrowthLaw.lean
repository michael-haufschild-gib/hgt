import GaloisForLFunctions.BiScaleUncertainty.PacketBoundednessCriterion
import GaloisForLFunctions.RHTower.LiouvilleTriangularHeadOscillation
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# One-sided packet bounds: a packet bounded on one side sees no deeper zero

For a real compact `C²` source `f`, the packet growth law says `P_f(τ) = O(e^{στ})` iff
`f̂(γ_ρ) = 0` at every zero of depth `Re ρ − 1/2 > σ`. Here one side suffices.

**Packet sign law** (`packet_upper_iff`, `packet_lower_iff`). For `σ ≥ 0`, an eventual upper
bound `P_f(τ) ≤ K e^{στ}` alone, or an eventual lower bound `P_f(τ) ≥ −K e^{στ}` alone, forces
`f̂(γ_ρ) = 0` at every zero of depth `> σ`; the packet is then two-sided `O(e^{στ})`.

Consequences:

* `riemannHypothesis_iff_forall_packet_bddAbove`, `riemannHypothesis_iff_forall_packet_bddBelow`:
  RH iff every compact packet is eventually bounded above, iff every one is bounded below.
* `xiZeroHalfPlaneBound_iff_forall_packet_upper`: the zero width is the universal one-sided
  packet growth exponent.
* `packet_oscillates`: a source that sees a zero of depth `> σ` has a packet above `K e^{στ}` and
  below `−K e^{στ}` at arbitrarily large shifts, for every `K`.

**Mechanism.** If `η P_f ≤ K e^{στ}` beyond `b` (`η = ±1`), then `ε e^{σu} − η P_f(u) 1_{u>b}` is
the density of a nonnegative measure (`RHTower.LiouvilleTriangularHeadOscillation.expOneSidedMeasure`).
On `Re z > 1/2` its Laplace transform is `ε/(z − σ) − η (L_A(z) − R(z))`, with `L_A` the transform
of the bounded archimedean tail and `R` the zero resolvent. It is analytic at every real `t > σ`,
because `ζ` has no real zero in the critical strip, so no shifted zero is a positive real
(`zeroShift_ne_ofReal`). Landau's theorem puts the abscissa at `σ`; the transform of the measure
is then holomorphic on `Re z > σ`, and so is the continuation of `R`. Its residues
`m_ρ f̂(γ_ρ)` at deeper zeros vanish (`coeff_eq_zero_of_eqOn_zeroResolvent`).
-/

open MeasureTheory Set Filter Topology Complex
open RHTower.LiouvilleTriangularHeadOscillation (expOneSidedMeasure isAbscissa_oneSidedMeasure
  complexLaplace_oneSidedMeasure_eq isAbscissa_eq_of_analyticAt_real)

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-- The zero series is at most `Σ |c_ρ|` times `e^{|τ|/2}`. -/
theorem norm_zeroSeries_le {Z : Zeta23.ZeroConfig} {c : Z.carrier → ℂ}
    (hc : Summable fun ρ => ‖c ρ‖) (τ : ℝ) :
    ‖zeroSeries c τ‖ ≤ (∑' ρ, ‖c ρ‖) * Real.exp (|τ| / 2) := by
  have hterm : ∀ ρ, ‖c ρ * cexp (zeroShift ρ * τ)‖ ≤ ‖c ρ‖ * Real.exp (|τ| / 2) := fun ρ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_exp_zeroShift_mul_le ρ τ) (norm_nonneg _)
  have hdom : Summable fun ρ => ‖c ρ‖ * Real.exp (|τ| / 2) := hc.mul_right _
  rw [zeroSeries, ← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm)).trans
    (Summable.tsum_le_tsum hterm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm) hdom)

/-- Laplace integrability on `(b, ∞)` of a continuous function of exponential order `a`. -/
theorem integrableOn_cexp_mul_of_norm_le {F : ℝ → ℂ} (hF : Continuous F) {b C a : ℝ} {z : ℂ}
    (hFb : ∀ u : ℝ, b < u → ‖F u‖ ≤ C * Real.exp (a * u)) (hz : a < z.re) :
    IntegrableOn (fun u : ℝ => cexp (-z * u) * F u) (Ioi b) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi b (sub_pos.mpr hz)).const_mul C)
    ((by fun_prop : Continuous fun u : ℝ => cexp (-z * u)).mul hF).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  rw [norm_mul, GaloisForLFunctions.RHTower.norm_cexp_neg_mul]
  calc Real.exp (-z.re * u) * ‖F u‖ ≤ Real.exp (-z.re * u) * (C * Real.exp (a * u)) :=
        mul_le_mul_of_nonneg_left (hFb u hu) (Real.exp_pos _).le
    _ = C * Real.exp (-(z.re - a) * u) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring

/-- No shifted zero is a positive real: `ζ` has no real zero in the critical strip. -/
theorem zeroShift_ne_ofReal (ρ : 𝒵) {t : ℝ} (ht : 0 < t) : zeroShift ρ ≠ (t : ℂ) := by
  intro h
  have hρ : (ρ : ℂ) = ((t + 1 / 2 : ℝ) : ℂ) := by
    rw [show (ρ : ℂ) = zeroShift ρ + 1 / 2 by simp [zeroShift], h]
    push_cast
    ring
  have h1 : t + 1 / 2 < 1 := by
    have := ρ.2.2.2
    rwa [hρ, ofReal_re] at this
  exact _root_.RHTower.riemannZeta_real_strip_ne_zero (by linarith) h1 (by rw [← hρ]; exact ρ.2.1)

/-- **One-sided Landau step.** If `η P_f(τ) ≤ K e^{στ}` eventually, with `η = ±1` and `σ ≥ 0`,
then `f̂(γ_ρ) = 0` at every zero of depth `Re ρ − 1/2 > σ`. -/
theorem paperFT_eq_zero_of_signed_packet_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {η σ : ℝ} (hη : |η| = 1) (hσ : 0 ≤ σ)
    (hbd : ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → η * stationaryPacket f τ ≤ K * Real.exp (σ * τ))
    (ρ : 𝒵) (hρ : σ < (ρ : ℂ).re - 1 / 2) :
    Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  obtain ⟨T, K₀, hK₀⟩ := hbd
  obtain ⟨w, hw, hwf⟩ := hfc.exists_pos_le_norm
  have hwz : ∀ v : ℝ, w < |v| → f v = 0 := fun v hv =>
    hwf v (by rw [Real.norm_eq_abs]; exact hv.le)
  have hσ2 : σ ≤ 1 / 2 := by have := ρ.2.2.2; linarith
  have hηc : (η : ℂ) * η = 1 := by
    have : η * η = 1 := by rw [← abs_mul_abs_self, hη, one_mul]
    exact_mod_cast this
  have hc := summable_norm_packetCoeff hf hfc
  set A := packetArchTail f
  set G := zeroSeries (packetCoeff f)
  set R := zeroResolvent (packetCoeff f)
  set CA := 1 / (2 * Real.pi) * ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (f u : ℂ)) r *
    (Zeta23.EF.gammaBracket r : ℂ)‖
  have hA : ∀ τ, ‖A τ‖ ≤ CA := norm_packetArchTail_le f
  have hCA0 : 0 ≤ CA := (norm_nonneg _).trans (hA 0)
  set S := ∑' ρ, ‖packetCoeff f ρ‖
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  have hAc : Continuous A := continuous_packetArchTail hf hfc hwz
  have hGc : Continuous G := continuous_zeroSeries hc
  have hG : ∀ u : ℝ, 0 < u → ‖G u‖ ≤ S * Real.exp (1 / 2 * u) := fun u hu => by
    have h := norm_zeroSeries_le hc u
    rwa [abs_of_pos hu, show u / 2 = 1 / 2 * u by ring] at h
  set b := max T w + 1
  have hb : 0 < b := by have := le_max_right T w; linarith
  have hbw : w < b := by have := le_max_right T w; linarith
  have hbT : T < b := by have := le_max_left T w; linarith
  -- the packet beyond `b`, extended by zero
  set g : ℝ → ℝ := (Ioi b).indicator fun u => (A u - G u).re
  have hgm : Measurable g :=
    (Complex.continuous_re.comp (hAc.sub hGc)).measurable.indicator measurableSet_Ioi
  have hgP : ∀ u, b < u → (g u : ℂ) = A u - G u := fun u hu => by
    have hP := stationaryPacket_eq hf hfc hw.le hwz (hbw.trans hu)
    simp only [g, indicator_of_mem (show u ∈ Ioi b from hu)]
    rw [← hP, ofReal_re]
  have hgP' : ∀ u, b < u → g u = stationaryPacket f u := fun u hu => by
    have h := hgP u hu
    rw [← stationaryPacket_eq hf hfc hw.le hwz (hbw.trans hu)] at h
    exact_mod_cast h
  have hg0 : ∀ u, ¬ b < u → g u = 0 := fun u hu =>
    indicator_of_notMem (show u ∉ Ioi b from hu) _
  have hgη : ∀ u, 0 < u → η * g u ≤ |K₀| * Real.exp (σ * u) + 0 := fun u _ => by
    by_cases hub : b < u
    · rw [hgP' u hub, add_zero]
      exact (hK₀ u (by linarith)).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
    · rw [hg0 u hub, mul_zero, add_zero]
      positivity
  have hgb : ∀ u, 0 < u → |g u| ≤ (CA + S) * Real.exp (1 / 2 * u) := fun u hu => by
    have he : 1 ≤ Real.exp (1 / 2 * u) := Real.one_le_exp (by positivity)
    by_cases hub : b < u
    · rw [← Real.norm_eq_abs, ← Complex.norm_real, hgP u hub]
      calc ‖A u - G u‖ ≤ ‖A u‖ + ‖G u‖ := norm_sub_le _ _
        _ ≤ CA + S * Real.exp (1 / 2 * u) := add_le_add (hA u) (hG u hu)
        _ ≤ (CA + S) * Real.exp (1 / 2 * u) := by nlinarith
    · rw [hg0 u hub, abs_zero]
      positivity
  -- the nonnegative measure `(ε e^{σu} − η g(u)) du` and its abscissa
  set ε : ℝ := |K₀| + 1
  set ν := expOneSidedMeasure g η ε σ 0
  obtain ⟨hc₀, hσc₀, hc₀γ⟩ := isAbscissa_oneSidedMeasure hgm hη (abs_nonneg K₀)
    (lt_add_one |K₀|) le_rfl (add_nonneg hCA0 hS0) hσ2 (by norm_num) hgb hgη
  -- the transform of the archimedean tail, holomorphic on `Re z > 0`
  set Lre := RHTower.ccmAbelLaplaceTail (fun τ => (A τ).re) b
  set Lim := RHTower.ccmAbelLaplaceTail (fun τ => (A τ).im) b
  have hLre := RHTower.analyticOnNhd_ccmAbelLaplaceTail_of_bounded
    (Complex.continuous_re.comp hAc).measurable hb hCA0
    fun τ _ => (abs_re_le_norm _).trans (hA τ)
  have hLim := RHTower.analyticOnNhd_ccmAbelLaplaceTail_of_bounded
    (Complex.continuous_im.comp hAc).measurable hb hCA0
    fun τ _ => (abs_im_le_norm _).trans (hA τ)
  set LA : ℂ → ℂ := fun z => Lre z + I * Lim z
  have hLAan : AnalyticOnNhd ℂ LA {z : ℂ | 0 < z.re} := fun z hz =>
    (hLre z hz).add (analyticAt_const.mul (hLim z hz))
  have hAint : ∀ z : ℂ, 0 < z.re → ∀ q : ℝ → ℝ, Continuous q → (∀ τ, |q τ| ≤ CA) →
      IntegrableOn (fun u : ℝ => cexp (-z * u) * (q u : ℂ)) (Ioi b) := fun z hz q hq hqA =>
    integrableOn_cexp_mul_of_norm_le (F := fun u => (q u : ℂ)) (C := CA) (a := 0)
      (Complex.continuous_ofReal.comp hq)
      (fun u _ => by
        rw [zero_mul, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact hqA u) hz
  have hLAeq : ∀ z : ℂ, 0 < z.re → LA z = ∫ u in Ioi b, cexp (-z * u) * A u := by
    intro z hz
    have hre : Integrable (fun u : ℝ => cexp (-z * u) * ((A u).re : ℂ))
        (volume.restrict (Ioi b)) :=
      hAint z hz _ (Complex.continuous_re.comp hAc) fun τ => (abs_re_le_norm _).trans (hA τ)
    have him : Integrable (fun u : ℝ => I * (cexp (-z * u) * ((A u).im : ℂ)))
        (volume.restrict (Ioi b)) :=
      (hAint z hz _ (Complex.continuous_im.comp hAc)
        fun τ => (abs_im_le_norm _).trans (hA τ)).const_mul I
    simp only [LA, Lre, Lim, RHTower.ccmAbelLaplaceTail]
    rw [← integral_const_mul, ← integral_add hre him]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hsplit : ((A u).re : ℂ) + ((A u).im : ℂ) * I = A u := Complex.re_add_im (A u)
    calc cexp (-z * u) * ((A u).re : ℂ) + I * (cexp (-z * u) * ((A u).im : ℂ))
        = cexp (-z * u) * (((A u).re : ℂ) + ((A u).im : ℂ) * I) := by ring
      _ = cexp (-z * u) * A u := by rw [hsplit]
  -- the transform of the measure on `Re z > 1/2`
  set Ψ : ℂ → ℂ := fun z => (ε : ℂ) / (z - σ) - η * (LA z - R b z)
  have hagree : ∀ z : ℂ, 1 / 2 < z.re →
      GaloisForLFunctions.RHTower.complexLaplace ν z = Ψ z := by
    intro z hz
    have hz0 : 0 < z.re := by linarith
    have hGint : IntegrableOn (fun u : ℝ => cexp (-z * u) * G u) (Ioi b) :=
      integrableOn_cexp_mul_of_norm_le hGc (fun u hu => hG u (hb.trans hu)) hz
    have hAint' : IntegrableOn (fun u : ℝ => cexp (-z * u) * A u) (Ioi b) :=
      integrableOn_cexp_mul_of_norm_le (C := CA) (a := 0) hAc
        (fun u _ => by rw [zero_mul, Real.exp_zero, mul_one]; exact hA u) hz0
    have hind : (fun u : ℝ => (g u : ℂ) * cexp (-z * u)) =
        (Ioi b).indicator fun u => cexp (-z * u) * A u - cexp (-z * u) * G u := by
      funext u
      by_cases hu : u ∈ Ioi b
      · rw [indicator_of_mem hu, hgP u hu]
        ring
      · rw [indicator_of_notMem hu, hg0 u hu, ofReal_zero, zero_mul]
    rw [complexLaplace_oneSidedMeasure_eq hgm hσ hσ2 (lt_add_one |K₀|).le hgb hgη hz, hind,
      setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hb.le,
      integral_sub hAint' hGint, integral_exp_mul_zeroSeries hc hb hz, ← hLAeq z hz0]
    simp only [Ψ, R, ε]
    push_cast
    ring
  -- Landau: the abscissa is `σ`
  have hΨ : ∀ t : ℝ, σ < t → AnalyticAt ℂ Ψ t := by
    intro t ht
    have ht0 : 0 < t := hσ.trans_lt ht
    have hsub : (t : ℂ) - σ ≠ 0 := by
      rw [← ofReal_sub]
      exact ofReal_ne_zero.mpr (by linarith)
    exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hsub).sub
      (analyticAt_const.mul ((hLAan t (by simpa using ht0)).sub
        (analyticAt_zeroResolvent hc b fun ρ => zeroShift_ne_ofReal ρ ht0)))
  have hσν := isAbscissa_eq_of_analyticAt_real hc₀ hσc₀ hc₀γ hΨ hagree
  have hCLan : AnalyticOnNhd ℂ (GaloisForLFunctions.RHTower.complexLaplace ν)
      {z : ℂ | σ < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      (GaloisForLFunctions.RHTower.hasDerivAt_complexLaplace hσν hz).differentiableAt
        |>.differentiableWithinAt) (isOpen_lt continuous_const Complex.continuous_re)
  -- the zero resolvent continues to `Re z > σ`
  set M : ℂ → ℂ := fun z =>
    LA z - η * ((ε : ℂ) / (z - σ) - GaloisForLFunctions.RHTower.complexLaplace ν z)
  have hMan : AnalyticOnNhd ℂ M {z : ℂ | σ < z.re} := fun z hz => by
    have hz' : σ < z.re := hz
    have hsub : z - σ ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp only [sub_re, ofReal_re, zero_re] at this
      linarith
    exact (hLAan z (show 0 < z.re by linarith)).sub (analyticAt_const.mul
      ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) hsub).sub (hCLan z hz)))
  have hMR : ∀ z : ℂ, 1 / 2 < z.re → M z = R b z := by
    intro z hz
    have h := hagree z hz
    simp only [M, Ψ] at h ⊢
    linear_combination (η : ℂ) * h - (LA z - R b z) * hηc
  exact (packetCoeff_eq_zero_iff f ρ).mp
    (coeff_eq_zero_of_eqOn_zeroResolvent hc hMan hMR (by simpa [zeroShift] using hρ))

/-- **Packet sign law, upper side.** For `σ ≥ 0`, `P_f(τ) ≤ K e^{στ}` eventually iff `f̂(γ_ρ) = 0`
at every zero of depth `Re ρ − 1/2 > σ`. -/
theorem packet_upper_iff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K * Real.exp (σ * τ)) ↔
      ∀ ρ : 𝒵, σ < (ρ : ℂ).re - 1 / 2 →
        Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  constructor
  · rintro ⟨T, K, h⟩
    exact paperFT_eq_zero_of_signed_packet_le hf hfc (η := 1) (by simp) hσ
      ⟨T, K, fun τ hτ => by rw [one_mul]; exact h τ hτ⟩
  · intro h
    obtain ⟨T, K, hK⟩ := (packet_growth_iff hf hfc hσ).mpr h
    exact ⟨T, K, fun τ hτ => (le_abs_self _).trans (hK τ hτ)⟩

/-- **Packet sign law, lower side.** For `σ ≥ 0`, `P_f(τ) ≥ −K e^{στ}` eventually iff
`f̂(γ_ρ) = 0` at every zero of depth `Re ρ − 1/2 > σ`. -/
theorem packet_lower_iff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → -(K * Real.exp (σ * τ)) ≤ stationaryPacket f τ) ↔
      ∀ ρ : 𝒵, σ < (ρ : ℂ).re - 1 / 2 →
        Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  constructor
  · rintro ⟨T, K, h⟩
    exact paperFT_eq_zero_of_signed_packet_le hf hfc (η := -1) (by simp) hσ
      ⟨T, K, fun τ hτ => by linarith [h τ hτ]⟩
  · intro h
    obtain ⟨T, K, hK⟩ := (packet_growth_iff hf hfc hσ).mpr h
    exact ⟨T, K, fun τ hτ => by linarith [hK τ hτ, neg_abs_le (stationaryPacket f τ)]⟩

/-- **RH is the upper boundedness of every compact packet.** -/
theorem riemannHypothesis_iff_forall_packet_bddAbove :
    RiemannHypothesis ↔ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K := by
  rw [riemannHypothesis_iff_forall_packet_bounded]
  refine forall_congr' fun f => forall_congr' fun hf => forall_congr' fun hfc => ?_
  have h := packet_upper_iff hf hfc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one, sub_pos] at h
  exact (packet_bounded_iff_blind hf hfc).trans h.symm

/-- **RH is the lower boundedness of every compact packet.** -/
theorem riemannHypothesis_iff_forall_packet_bddBelow :
    RiemannHypothesis ↔ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → K ≤ stationaryPacket f τ := by
  rw [riemannHypothesis_iff_forall_packet_bounded]
  refine forall_congr' fun f => forall_congr' fun hf => forall_congr' fun hfc => ?_
  have h := packet_lower_iff hf hfc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one, sub_pos] at h
  refine (packet_bounded_iff_blind hf hfc).trans (h.symm.trans ?_)
  exact ⟨fun ⟨T, K, hK⟩ => ⟨T, -K, hK⟩,
    fun ⟨T, K, hK⟩ => ⟨T, -K, fun τ hτ => by rw [neg_neg]; exact hK τ hτ⟩⟩

/-- **The zero width is the universal one-sided packet growth exponent.** For `β ≥ 0`, every zero
has `Re ρ ≤ 1/2 + β` iff every compact packet is eventually at most `K e^{βτ}`. -/
theorem xiZeroHalfPlaneBound_iff_forall_packet_upper {β : ℝ} (hβ : 0 ≤ β) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K * Real.exp (β * τ) := by
  rw [xiZeroHalfPlaneBound_iff_forall_packet_growth hβ]
  refine forall_congr' fun f => forall_congr' fun hf => forall_congr' fun hfc => ?_
  rw [packet_growth_iff hf hfc hβ, packet_upper_iff hf hfc hβ]

/-- **Ω± for packets.** A source that sees a zero of depth `Re ρ − 1/2 > σ ≥ 0` has a packet
above `K e^{στ}` and below `−K e^{στ}` at arbitrarily large shifts. -/
theorem packet_oscillates {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 ≤ σ) {ρ : 𝒵} (hρ : σ < (ρ : ℂ).re - 1 / 2)
    (hne : Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) ≠ 0) (T K : ℝ) :
    (∃ τ, T ≤ τ ∧ K * Real.exp (σ * τ) < stationaryPacket f τ) ∧
      ∃ τ, T ≤ τ ∧ stationaryPacket f τ < -(K * Real.exp (σ * τ)) := by
  constructor
  · by_contra h
    push Not at h
    exact hne ((packet_upper_iff hf hfc hσ).mp ⟨T, K, h⟩ ρ hρ)
  · by_contra h
    push Not at h
    exact hne ((packet_lower_iff hf hfc hσ).mp ⟨T, K, h⟩ ρ hρ)

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
