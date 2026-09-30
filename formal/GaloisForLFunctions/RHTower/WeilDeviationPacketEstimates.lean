import GaloisForLFunctions.RHTower.WeilDeviationDecomposition

/-!
# Packet estimates for the deficit of a Weil-positive system

Let `w ≥ 0` be a Cauchy-bounded weight (bound `D`) and `h` a smooth compactly supported amplitude.
For a smooth compactly supported shape `B` and `0 < η ≤ 1`:
- **Packet limit** (`exists_packet_limit`). `‖W(𝓕(h · B_{γ,η})) − h(γ) W(𝓕B_{γ,η})‖ ≤ K η`,
  with `K` independent of `γ` and `η`.
- **Wave comparison** (`norm_weightPairing_pdPacket_le`). For the positive-definite packet `G`,
  `|W(𝓕G_{γ,δ})| ≤ W(𝓕G_{0,δ})`, because `𝓕G ≥ 0`. The right side is the *deficit mean*
  `A_δ ≥ 0`.
- **Flattening** (`norm_weightPairing_flatCorrection_le`). The correction `c_ε = (1 − G)B(·/ε)`
  satisfies `|W(𝓕c_{ε,γ,δ})| ≤ K' ε`, uniformly in `γ` and `δ`. It is a flat bump at scale `εδ`
  with amplitude `h₁((·−γ)/δ)` where `h₁(0) = 0`, and the packet-limit error is scale-covariant.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ContDiff

namespace RHTower.WeilExcess

noncomputable section

/-! ## Packets of smooth shapes -/

theorem contDiff_packet {B : ℝ → ℂ} (hB : ContDiff ℝ ∞ B) (γ η : ℝ) :
    ContDiff ℝ ∞ (packet B γ η) :=
  hB.comp ((contDiff_id.sub contDiff_const).div_const η)

theorem hasCompactSupport_packet {B : ℝ → ℂ} (hB : HasCompactSupport B) (γ : ℝ) {η : ℝ}
    (hη : 0 < η) : HasCompactSupport (packet B γ η) := by
  have h1 : HasCompactSupport fun x => B (η⁻¹ * x) :=
    hB.comp_homeomorph (Homeomorph.mulLeft₀ η⁻¹ (inv_ne_zero hη.ne'))
  have h2 := h1.comp_homeomorph (Homeomorph.subRight γ)
  have e : packet B γ η = (fun x => B (η⁻¹ * x)) ∘ Homeomorph.subRight γ := by
    funext x; simp [packet, div_eq_inv_mul]
  rw [e]; exact h2

theorem norm_fourier_packet (B : ℝ → ℂ) (γ : ℝ) {η : ℝ} (hη : 0 < η) (u : ℝ) :
    ‖𝓕 (packet B γ η) u‖ = η * ‖𝓕 B (η * u)‖ := by
  rw [fourier_packet B γ hη, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hη, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The weighted moment of a packet transform is scale-covariant. -/
theorem integral_norm_fourier_packet_moment (h : ℝ → ℂ) (γ : ℝ) {δ ε : ℝ} (hδ : 0 < δ) :
    ∫ s, ‖𝓕 (packet h γ δ) s‖ * (ε * δ * |s| * (1 + (ε * δ) ^ 2 * s ^ 2)) =
      ∫ t, ‖𝓕 h t‖ * (ε * |t| * (1 + ε ^ 2 * t ^ 2)) := by
  simp only [norm_fourier_packet h γ hδ]
  have := Measure.integral_comp_mul_left (fun t => ‖𝓕 h t‖ * (ε * |t| * (1 + ε ^ 2 * t ^ 2))) δ
  rw [abs_inv, abs_of_pos hδ, smul_eq_mul] at this
  rw [← mul_inv_cancel_left₀ hδ.ne' (∫ t, ‖𝓕 h t‖ * (ε * |t| * (1 + ε ^ 2 * t ^ 2))), ← this,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  dsimp only
  rw [abs_mul, abs_of_pos hδ]
  ring

/-! ## The packet limit for smooth shapes -/

/-- **Packet limit for smooth shapes and amplitudes.** -/
theorem exists_packet_limit {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {D : ℝ} (hD : CauchyBounded w D)
    {B : ℝ → ℂ} (hBs : ContDiff ℝ ∞ B) (hBc : HasCompactSupport B) :
    ∃ CB' : ℝ, 0 ≤ CB' ∧ ∀ {h : ℝ → ℂ}, ContDiff ℝ ∞ h → HasCompactSupport h →
      ∀ (γ : ℝ) {η : ℝ}, 0 < η → η ≤ 1 →
      Summable (fun n : ℕ => (w n : ℂ) * (𝓕 (fun ξ => h ξ * packet B γ η ξ) (Real.log n) +
        𝓕 (fun ξ => h ξ * packet B γ η ξ) (-Real.log n))) ∧
      ‖weightPairing w (𝓕 fun ξ => h ξ * packet B γ η ξ) -
          h γ * weightPairing w (𝓕 (packet B γ η))‖ ≤
        2 * CB' * D * ∫ s, ‖𝓕 h s‖ * (η * |s| * (1 + η ^ 2 * s ^ 2)) := by
  obtain ⟨CB, -, hCB⟩ := exists_fourier_profile_smooth hBs hBc
  obtain ⟨CB', hCB'0, hCB'⟩ := exists_deriv_fourier_profile_smooth hBs hBc
  refine ⟨CB', hCB'0, fun {h} hs hc γ η hη0 hη1 => ?_⟩
  exact norm_weightPairing_fourier_mul_packet_sub_le hw hD
    (hBs.continuous.integrable_of_hasCompactSupport hBc) hCB
    (hasDerivAt_fourier_smooth hBs hBc) hCB' hs.continuous
    (hs.continuous.integrable_of_hasCompactSupport hc) (integrable_fourier_smooth hs hc)
    (integrable_fourier_moment_smooth hs hc) γ hη0 hη1

theorem integral_moment_le {h : ℝ → ℂ} {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hm : Integrable fun s => ‖𝓕 h s‖ * (|s| * (1 + s ^ 2))) :
    ∫ s, ‖𝓕 h s‖ * (η * |s| * (1 + η ^ 2 * s ^ 2)) ≤
      η * ∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2)) := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun s => by positivity)
    (hm.const_mul η) (Eventually.of_forall fun s => ?_)
  have hη2 : η ^ 2 ≤ 1 := by nlinarith
  have : 1 + η ^ 2 * s ^ 2 ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  have hn := norm_nonneg (𝓕 h s)
  calc ‖𝓕 h s‖ * (η * |s| * (1 + η ^ 2 * s ^ 2)) ≤ ‖𝓕 h s‖ * (η * |s| * (1 + s ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (by positivity)) hn
    _ = η * (‖𝓕 h s‖ * (|s| * (1 + s ^ 2))) := by ring

/-! ## The positive-definite packet: wave comparison -/

theorem integrable_pdPacketC : Integrable pdPacketC :=
  contDiff_pdPacketC.continuous.integrable_of_hasCompactSupport hasCompactSupport_pdPacketC

/-- The pairing of a weight with the transform of the `G`-packet at frequency `γ`. -/
theorem norm_weightPairing_pdPacket_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {D : ℝ}
    (hD : CauchyBounded w D) (γ : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖weightPairing w (𝓕 (packet pdPacketC γ δ))‖ ≤
      (weightPairing w (𝓕 (packet pdPacketC 0 δ))).re ∧
    (weightPairing w (𝓕 (packet pdPacketC 0 δ))).im = 0 := by
  obtain ⟨CB, -, hCB⟩ := exists_fourier_profile_smooth contDiff_pdPacketC hasCompactSupport_pdPacketC
  have hprof : ∀ γ' u, ‖𝓕 (packet pdPacketC γ' δ) u‖ ≤ CB * cauchyProfile δ 0 u := by
    intro γ' u
    rw [norm_fourier_packet _ _ hδ0]
    calc δ * ‖𝓕 pdPacketC (δ * u)‖ ≤ δ * (CB / (1 + (δ * u) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hCB _) hδ0.le
      _ = CB * cauchyProfile δ 0 u := by simp only [cauchyProfile, sub_zero]; ring
  obtain ⟨hs0, -⟩ := summable_weightPairing_of_profile hw hD hδ0 hδ1 (hprof 0)
  -- real transforms
  have hG : ∀ x, 𝓕 pdPacketC x = ((𝓕 pdPacketC x).re : ℂ) := fun x =>
    Complex.ext (by simp) (by simp [(fourier_pdPacketC_nonneg x).1])
  have hG0 : ∀ x, 0 ≤ (𝓕 pdPacketC x).re := fun x => (fourier_pdPacketC_nonneg x).2
  have hpk : ∀ γ' u, 𝓕 (packet pdPacketC γ' δ) u =
      (δ : ℂ) * Complex.exp (-(2 * π * γ' * u : ℝ) * I) * ((𝓕 pdPacketC (δ * u)).re : ℂ) :=
    fun γ' u => by rw [fourier_packet _ _ hδ0, ← hG]
  set r : ℕ → ℝ := fun n => w n * (δ * (𝓕 pdPacketC (δ * Real.log n)).re +
    δ * (𝓕 pdPacketC (δ * -Real.log n)).re) with hr
  have hr0 : ∀ n, (w n : ℂ) * (𝓕 (packet pdPacketC 0 δ) (Real.log n) +
      𝓕 (packet pdPacketC 0 δ) (-Real.log n)) = (r n : ℂ) := by
    intro n
    rw [hpk, hpk]
    simp only [hr, mul_zero, zero_mul, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero,
      mul_one]
    push_cast; ring
  have hrs : Summable r := by
    have h1 : Summable fun n : ℕ => (r n : ℂ) := hs0.congr hr0
    exact Complex.summable_ofReal.mp h1
  have hW0 : weightPairing w (𝓕 (packet pdPacketC 0 δ)) = ((∑' n, r n : ℝ) : ℂ) := by
    unfold weightPairing
    rw [tsum_congr hr0, Complex.ofReal_tsum]
  have hbound : ∀ n : ℕ, ‖(w n : ℂ) * (𝓕 (packet pdPacketC γ δ) (Real.log n) +
      𝓕 (packet pdPacketC γ δ) (-Real.log n))‖ ≤ r n := by
    intro n
    rw [hpk, hpk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n)]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (le_of_eq ?_)) (hw n)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0,
      ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one,
      abs_of_nonneg (hG0 _)]
  constructor
  · rw [hW0, Complex.ofReal_re]
    unfold weightPairing
    exact tsum_of_norm_bounded hrs.hasSum hbound
  · rw [hW0, Complex.ofReal_im]

/-! ## Additivity -/

theorem fourier_add_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (u : ℝ) :
    𝓕 (fun ξ => f ξ + g ξ) u = 𝓕 f u + 𝓕 g u := by
  rw [fourier_eq_integral, fourier_eq_integral, fourier_eq_integral,
    ← integral_add (integrable_exp_mul hf u) (integrable_exp_mul hg u)]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by ring)

theorem weightPairing_add {w : ℕ → ℝ} {φ ψ : ℝ → ℂ}
    (hφ : Summable fun n : ℕ => (w n : ℂ) * (φ (Real.log n) + φ (-Real.log n)))
    (hψ : Summable fun n : ℕ => (w n : ℂ) * (ψ (Real.log n) + ψ (-Real.log n))) :
    weightPairing w (fun u => φ u + ψ u) = weightPairing w φ + weightPairing w ψ := by
  unfold weightPairing
  rw [← Summable.tsum_add hφ hψ]
  exact tsum_congr fun n => by ring

/-! ## The flattening correction -/

/-- The complex flattening correction is smooth and compactly supported. -/
theorem contDiff_excessFlatCorrection (ε : ℝ) : ContDiff ℝ ∞ (excessFlatCorrection ε) :=
  ofRealCLM.contDiff.comp ((contDiff_const.sub contDiff_pdPacket).mul
    (excessFlatBump.contDiff.comp (contDiff_id.div_const ε)))

theorem hasCompactSupport_excessFlatCorrection {ε : ℝ} (hε : ε ≠ 0) :
    HasCompactSupport (excessFlatCorrection ε) := by
  have h1 : HasCompactSupport fun x : ℝ => (excessFlatBump (ε⁻¹ * x) : ℝ) :=
    excessFlatBump.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft₀ ε⁻¹ (inv_ne_zero hε))
  refine h1.mono' fun x hx => subset_tsupport _ ?_
  rw [Function.mem_support] at hx ⊢
  intro h0; apply hx
  simp only [excessFlatCorrection]
  rw [show x / ε = ε⁻¹ * x by rw [div_eq_inv_mul], h0]
  simp

/-- **The flattening bound.** -/
theorem exists_flatCorrection_bound {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {D : ℝ}
    (hD : CauchyBounded w D) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ (γ : ℝ) {δ ε : ℝ}, 0 < δ → δ ≤ 1 → 0 < ε → ε ≤ 1 →
      Summable (fun n : ℕ => (w n : ℂ) *
        (𝓕 (packet (excessFlatCorrection ε) γ δ) (Real.log n) +
          𝓕 (packet (excessFlatCorrection ε) γ δ) (-Real.log n))) ∧
      ‖weightPairing w (𝓕 (packet (excessFlatCorrection ε) γ δ))‖ ≤ K' * ε := by
  obtain ⟨CB', hCB', hPL⟩ := exists_packet_limit hw hD contDiff_cutoffC hasCompactSupport_cutoffC
  have hD0 : 0 ≤ D := by
    obtain ⟨-, hle⟩ := hD 1 one_pos le_rfl 0
    exact le_trans (tsum_nonneg fun n => mul_nonneg (hw n) (add_nonneg
      (cauchyProfile_nonneg zero_le_one 0 _) (cauchyProfile_nonneg zero_le_one 0 _))) hle
  set M₁ := ∫ t, ‖𝓕 excessFlatAmplitude t‖ * (|t| * (1 + t ^ 2)) with hM₁
  have hM₁0 : 0 ≤ M₁ := integral_nonneg fun t => by positivity
  refine ⟨2 * CB' * D * M₁, by positivity, fun γ δ ε hδ0 hδ1 hε0 hε1 => ?_⟩
  set h := packet excessFlatAmplitude γ δ with hh
  have hs : ContDiff ℝ ∞ h := contDiff_packet contDiff_excessFlatAmplitude γ δ
  have hc : HasCompactSupport h := hasCompactSupport_packet hasCompactSupport_excessFlatAmplitude γ hδ0
  have hεδ0 : 0 < ε * δ := mul_pos hε0 hδ0
  have hεδ1 : ε * δ ≤ 1 := by nlinarith
  have key : packet (excessFlatCorrection ε) γ δ = fun ξ => h ξ * packet cutoffC γ (ε * δ) ξ := by
    funext ξ
    simp only [packet, hh]
    rw [excessFlatCorrection_eq hε0 hε1, cutoffC, div_div, mul_comm δ ε]
  obtain ⟨hsum, hle⟩ := hPL hs hc γ hεδ0 hεδ1
  have hγ : h γ = 0 := by simp [hh, packet, excessFlatAmplitude_zero]
  rw [hγ, zero_mul, sub_zero] at hle
  rw [key]
  refine ⟨hsum, hle.trans ?_⟩
  have hm := integral_moment_le (h := excessFlatAmplitude) hε0.le hε1
    (integrable_fourier_moment_smooth contDiff_excessFlatAmplitude hasCompactSupport_excessFlatAmplitude)
  calc 2 * CB' * D * ∫ s, ‖𝓕 h s‖ * (ε * δ * |s| * (1 + (ε * δ) ^ 2 * s ^ 2))
      = 2 * CB' * D * ∫ t, ‖𝓕 excessFlatAmplitude t‖ * (ε * |t| * (1 + ε ^ 2 * t ^ 2)) := by
        rw [hh, integral_norm_fourier_packet_moment excessFlatAmplitude γ hδ0]
    _ ≤ 2 * CB' * D * (ε * M₁) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 2 * CB' * D * M₁ * ε := by ring

/-! ## Zero packets and the packet at the origin -/

/-- The flattened packet as a complex function. -/
def flatPacketC (ε x : ℝ) : ℂ := ((excessFlatPacket ε x : ℝ) : ℂ)

theorem packet_flatPacketC (ε γ δ : ℝ) :
    packet (flatPacketC ε) γ δ =
      fun ξ => packet pdPacketC γ δ ξ + packet (excessFlatCorrection ε) γ δ ξ :=
  funext fun ξ => by simp only [packet, flatPacketC]; exact excessFlatPacket_eq ε _

/-- The deficit mean `A_δ`: the pairing with the transform of the `G`-packet at the origin. -/
def deficitMean (w : ℕ → ℝ) (δ : ℝ) : ℝ := (weightPairing w (𝓕 (packet pdPacketC 0 δ))).re

theorem moment_nonneg (h : ℝ → ℂ) : 0 ≤ ∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2)) :=
  integral_nonneg fun s => by positivity

/-- **The zero-packet estimate.** A flattened packet at a zero `γ` contributes at most
`|h(γ)| (A_δ + K'ε)` up to an error `O_ε(δ)`. -/
theorem exists_zeroPacket_bound {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {D : ℝ}
    (hD : CauchyBounded w D) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∃ Kε : ℝ, 0 ≤ Kε ∧
      ∀ {h : ℝ → ℂ}, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ (γ : ℝ) {δ : ℝ}, 0 < δ → δ ≤ 1 →
      Summable (fun n : ℕ => (w n : ℂ) *
        (𝓕 (fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ) (Real.log n) +
          𝓕 (fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ) (-Real.log n))) ∧
      ‖weightPairing w (𝓕 fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ)‖ ≤
        ‖h γ‖ * (deficitMean w δ + K' * ε) +
          Kε * δ * ∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2)) := by
  obtain ⟨CG', hCG', hPG⟩ := exists_packet_limit hw hD contDiff_pdPacketC hasCompactSupport_pdPacketC
  obtain ⟨K', hK', hflat⟩ := exists_flatCorrection_bound hw hD
  have hD0 : 0 ≤ D := by
    obtain ⟨-, hle⟩ := hD 1 one_pos le_rfl 0
    exact le_trans (tsum_nonneg fun n => mul_nonneg (hw n) (add_nonneg
      (cauchyProfile_nonneg zero_le_one 0 _) (cauchyProfile_nonneg zero_le_one 0 _))) hle
  refine ⟨K', hK', fun {ε} hε0 hε1 => ?_⟩
  obtain ⟨Cc', hCc', hPc⟩ := exists_packet_limit hw hD (contDiff_excessFlatCorrection ε)
    (hasCompactSupport_excessFlatCorrection hε0.ne')
  refine ⟨2 * CG' * D + 2 * Cc' * D, by positivity, fun {h} hs hc γ δ hδ0 hδ1 => ?_⟩
  have hi : Integrable h := hs.continuous.integrable_of_hasCompactSupport hc
  have hm := moment_nonneg h
  obtain ⟨hs₁, hle₁⟩ := hPG hs hc γ hδ0 hδ1
  obtain ⟨hs₂, hle₂⟩ := hPc hs hc γ hδ0 hδ1
  obtain ⟨-, hflatle⟩ := hflat γ hδ0 hδ1 hε0 hε1
  obtain ⟨hGle, -⟩ := norm_weightPairing_pdPacket_le hw hD γ hδ0 hδ1
  have hmδ := integral_moment_le (h := h) hδ0.le hδ1 (integrable_fourier_moment_smooth hs hc)
  have hi₁ : Integrable fun ξ => h ξ * packet pdPacketC γ δ ξ :=
    (hs.mul (contDiff_packet contDiff_pdPacketC γ δ)).continuous.integrable_of_hasCompactSupport
      hc.mul_right
  have hi₂ : Integrable fun ξ => h ξ * packet (excessFlatCorrection ε) γ δ ξ :=
    (hs.mul (contDiff_packet (contDiff_excessFlatCorrection ε) γ δ)).continuous.integrable_of_hasCompactSupport
      hc.mul_right
  have hsplit : (fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ) =
      fun ξ => h ξ * packet pdPacketC γ δ ξ + h ξ * packet (excessFlatCorrection ε) γ δ ξ := by
    rw [packet_flatPacketC]; funext ξ; ring
  have hF : 𝓕 (fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ) =
      fun u => 𝓕 (fun ξ => h ξ * packet pdPacketC γ δ ξ) u +
        𝓕 (fun ξ => h ξ * packet (excessFlatCorrection ε) γ δ ξ) u := by
    rw [hsplit]; funext u; exact fourier_add_eq hi₁ hi₂ u
  rw [hF]
  refine ⟨(hs₁.add hs₂).congr fun n => by ring, ?_⟩
  rw [weightPairing_add hs₁ hs₂]
  have e1 : ‖weightPairing w (𝓕 fun ξ => h ξ * packet pdPacketC γ δ ξ)‖ ≤
      ‖h γ‖ * deficitMean w δ + 2 * CG' * D * (δ * ∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2))) := by
    have := norm_sub_norm_le (weightPairing w (𝓕 fun ξ => h ξ * packet pdPacketC γ δ ξ))
      (h γ * weightPairing w (𝓕 (packet pdPacketC γ δ)))
    rw [norm_mul] at this
    have h3 : ‖h γ‖ * ‖weightPairing w (𝓕 (packet pdPacketC γ δ))‖ ≤ ‖h γ‖ * deficitMean w δ :=
      mul_le_mul_of_nonneg_left hGle (norm_nonneg _)
    have h4 := mul_le_mul_of_nonneg_left hmδ (show 0 ≤ 2 * CG' * D by positivity)
    linarith
  have e2 : ‖weightPairing w (𝓕 fun ξ => h ξ * packet (excessFlatCorrection ε) γ δ ξ)‖ ≤
      ‖h γ‖ * (K' * ε) + 2 * Cc' * D * (δ * ∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2))) := by
    have := norm_sub_norm_le (weightPairing w (𝓕 fun ξ => h ξ * packet (excessFlatCorrection ε) γ δ ξ))
      (h γ * weightPairing w (𝓕 (packet (excessFlatCorrection ε) γ δ)))
    rw [norm_mul] at this
    have h3 := mul_le_mul_of_nonneg_left hflatle (norm_nonneg (h γ))
    have h4 := mul_le_mul_of_nonneg_left hmδ (show 0 ≤ 2 * Cc' * D by positivity)
    linarith
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring

/-- **The packet at the origin.** Its pairing is `h(0) A_δ` up to `O(δ)`. -/
theorem exists_originPacket_bound {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {D : ℝ}
    (hD : CauchyBounded w D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {h : ℝ → ℂ}, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ {δ : ℝ},
      0 < δ → δ ≤ 1 →
      Summable (fun n : ℕ => (w n : ℂ) *
        (𝓕 (fun ξ => h ξ * packet pdPacketC 0 δ ξ) (Real.log n) +
          𝓕 (fun ξ => h ξ * packet pdPacketC 0 δ ξ) (-Real.log n))) ∧
      ‖weightPairing w (𝓕 fun ξ => h ξ * packet pdPacketC 0 δ ξ) - h 0 * (deficitMean w δ : ℂ)‖ ≤
        K * δ * ∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2)) := by
  obtain ⟨CG', hCG', hPG⟩ := exists_packet_limit hw hD contDiff_pdPacketC hasCompactSupport_pdPacketC
  have hD0 : 0 ≤ D := by
    obtain ⟨-, hle⟩ := hD 1 one_pos le_rfl 0
    exact le_trans (tsum_nonneg fun n => mul_nonneg (hw n) (add_nonneg
      (cauchyProfile_nonneg zero_le_one 0 _) (cauchyProfile_nonneg zero_le_one 0 _))) hle
  refine ⟨2 * CG' * D, by positivity, fun {h} hs hc δ hδ0 hδ1 => ?_⟩
  obtain ⟨hs₁, hle₁⟩ := hPG hs hc 0 hδ0 hδ1
  obtain ⟨-, him⟩ := norm_weightPairing_pdPacket_le hw hD 0 hδ0 hδ1
  have hreal : weightPairing w (𝓕 (packet pdPacketC 0 δ)) = (deficitMean w δ : ℂ) :=
    Complex.ext (by simp [deficitMean]) (by simp [him])
  rw [hreal] at hle₁
  refine ⟨hs₁, hle₁.trans ?_⟩
  have hmδ := integral_moment_le (h := h) hδ0.le hδ1 (integrable_fourier_moment_smooth hs hc)
  calc _ ≤ 2 * CG' * D * (δ * ∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2))) :=
        mul_le_mul_of_nonneg_left hmδ (by positivity)
    _ = _ := by ring

theorem deficitMean_nonneg {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {D : ℝ} (hD : CauchyBounded w D)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ deficitMean w δ :=
  (norm_nonneg _).trans (norm_weightPairing_pdPacket_le hw hD 0 hδ0 hδ1).1

/-! ## The excess part of a packet -/

theorem integral_norm_packet (B : ℝ → ℂ) (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ ξ, ‖packet B γ δ ξ‖ = δ * ∫ x, ‖B x‖ := by
  have h := Measure.integral_comp_mul_left (fun x => ‖B x‖) δ⁻¹
  rw [inv_inv, abs_of_pos hδ, smul_eq_mul] at h
  rw [← h, ← integral_add_right_eq_self (μ := volume) (fun ξ => ‖packet B γ δ ξ‖) γ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [packet, div_eq_inv_mul]

/-- The excess pairs with a packet of width `δ` at most `2‖e‖₁ ‖h‖_∞ δ ‖B‖₁`. -/
theorem norm_weightPairing_excess_packet_le {e : ℕ → ℝ} (he0 : ∀ n, 0 ≤ e n) (he : Summable e)
    {h B : ℝ → ℂ} {H γ δ : ℝ} (hH : ∀ ξ, ‖h ξ‖ ≤ H)
    (hmeas : Continuous fun ξ => h ξ * packet B γ δ ξ) (hB : Integrable B) (hδ : 0 < δ) :
    Summable (fun n : ℕ => (e n : ℂ) * (𝓕 (fun ξ => h ξ * packet B γ δ ξ) (Real.log n) +
        𝓕 (fun ξ => h ξ * packet B γ δ ξ) (-Real.log n))) ∧
    ‖weightPairing e (𝓕 fun ξ => h ξ * packet B γ δ ξ)‖ ≤
      2 * (H * (δ * ∫ x, ‖B x‖)) * ∑' n, e n := by
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  have hpi := integrable_packet hB γ hδ
  have hfi : Integrable fun ξ => h ξ * packet B γ δ ξ := by
    refine (hpi.norm.const_mul H).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hH ξ) (norm_nonneg _)
  have hsup : ∀ u, ‖𝓕 (fun ξ => h ξ * packet B γ δ ξ) u‖ ≤ H * (δ * ∫ x, ‖B x‖) := by
    intro u
    refine (norm_fourier_le_integral_norm _ u).trans ?_
    rw [← integral_norm_packet B γ hδ, ← integral_const_mul]
    exact integral_mono hfi.norm (hpi.norm.const_mul H) fun ξ => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hH ξ) (norm_nonneg _)
  have hb : ∀ n : ℕ, ‖(e n : ℂ) * (𝓕 (fun ξ => h ξ * packet B γ δ ξ) (Real.log n) +
      𝓕 (fun ξ => h ξ * packet B γ δ ξ) (-Real.log n))‖ ≤ e n * (2 * (H * (δ * ∫ x, ‖B x‖))) := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (he0 n)]
    have h1 := hsup (Real.log n)
    have h2 := hsup (-Real.log n)
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) (he0 n)
  refine ⟨Summable.of_norm_bounded (he.mul_right _) hb, ?_⟩
  unfold weightPairing
  calc _ ≤ ∑' n, e n * (2 * (H * (δ * ∫ x, ‖B x‖))) :=
        tsum_of_norm_bounded (he.mul_right _).hasSum hb
    _ = _ := by rw [tsum_mul_right]; ring

end

end RHTower.WeilExcess
