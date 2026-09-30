import GaloisForLFunctions.RHTower.WeilFullConeSummableExcessRigidity

/-!
# Two-sided mean comparison for Weil-positive systems

Let `lam` be full-cone Weil-positive, with translation-bounded (`CauchyBounded`) excess `e` and
deficit `v`. For a weight `w`, `M_δ(w) = W_w(𝓕G_{0,δ})` is its mean over windows of length `1/δ`.
Write `A_δ = M_δ(v)` and `E_δ = M_δ(e)`.

**Theorem** (`exists_excessMean_le_deficitMean`). `E_δ ≤ A_δ + Cδ` for all `0 < δ ≤ 1`: the excess
cannot outweigh the deficit.

**Proof.** Apply near-null positivity (`deviationPairing_fourier_riemannXi_sq_mul`) to
`g = χ·G_δ ≥ 0`. This gives `W_a(𝓕(Ξ²χ G_δ)) = −∫ g(t/2π) dσ ≤ 0`. By the packet limit,
`W_w(𝓕(Ξ²χ G_δ)) = Ξ(0)² M_δ(w) + O(δ)` for `w = e, v`.

With `meanBalance` this makes the two densities comparable:
`E_δ ≤ A_δ + o(1)` and `(F(0) − 3/8) A_δ ≤ (F(0) + 3/8) E_δ + o(1)`.

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_deficitMeanVanishes`). A full-cone
Weil-positive `lam` whose deficit below `Λ` is translation-bounded with vanishing mean equals `Λ`.
This extends summable-deficit rigidity from `ℓ¹` to density zero.

**Proof.** A translation-bounded deficit forces a translation-bounded excess
(`exists_tsum_excess_cauchyProfile_le`). The comparison then gives `E_δ → 0`, and density-zero
excess rigidity finishes.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ContDiff

namespace RHTower.WeilExcess

noncomputable section

/-- The smooth weight `h = Ξ²χ`, with `h(0) = Ξ(0)² > 0`. -/
def xiSqCutoff (ξ : ℝ) : ℂ := riemannXi ξ ^ 2 * packet cutoffC 0 1 ξ

theorem contDiff_xiSqCutoff : ContDiff ℝ ∞ xiSqCutoff :=
  (contDiff_riemannXi.pow 2).mul (contDiff_packet contDiff_cutoffC 0 1)

theorem hasCompactSupport_xiSqCutoff : HasCompactSupport xiSqCutoff := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun ξ hξ => ?_
  rw [xiSqCutoff, packet_cutoffC_eq_zero one_pos, mul_zero]
  rw [mem_Icc, not_and_or, not_le, not_le] at hξ
  rcases hξ with h | h
  · linarith [neg_abs_le ξ]
  · linarith [le_abs_self ξ]

theorem xiSqCutoff_zero : xiSqCutoff 0 = ((riemannXiReal 0 ^ 2 : ℝ) : ℂ) := by
  rw [xiSqCutoff, packet_cutoffC_eq_one one_pos (by simp), mul_one, riemannXi_eq_ofReal]
  push_cast; ring

theorem riemannXiReal_zero_sq_pos : 0 < riemannXiReal 0 ^ 2 :=
  pow_pos (abs_pos.mpr riemannXiReal_zero_ne) 2 |>.trans_eq (by rw [sq_abs])

/-- The nonnegative real amplitude `χ G_δ`. -/
def cutoffPacket (δ ξ : ℝ) : ℂ := packet cutoffC 0 1 ξ * packet pdPacketC 0 δ ξ

theorem cutoffPacket_eq (δ ξ : ℝ) :
    cutoffPacket δ ξ = ((excessFlatBump ((ξ - 0) / 1) * pdPacket ((ξ - 0) / δ) : ℝ) : ℂ) := by
  simp only [cutoffPacket, packet, cutoffC, pdPacketC]
  push_cast; ring

theorem contDiff_cutoffPacket (δ : ℝ) : ContDiff ℝ ∞ (cutoffPacket δ) :=
  (contDiff_packet contDiff_cutoffC 0 1).mul (contDiff_packet contDiff_pdPacketC 0 δ)

theorem hasCompactSupport_cutoffPacket (δ : ℝ) : HasCompactSupport (cutoffPacket δ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun ξ hξ => ?_
  rw [cutoffPacket, packet_cutoffC_eq_zero one_pos, zero_mul]
  rw [mem_Icc, not_and_or, not_le, not_le] at hξ
  rcases hξ with h | h
  · linarith [neg_abs_le ξ]
  · linarith [le_abs_self ξ]

theorem xiSqCutoff_mul_packet (δ : ℝ) :
    (fun ξ => xiSqCutoff ξ * packet pdPacketC 0 δ ξ) =
      fun ξ => riemannXi ξ ^ 2 * cutoffPacket δ ξ := by
  funext ξ; simp only [xiSqCutoff, cutoffPacket]; ring

/-- **Near-null positivity at the origin.** The deviation pairs nonpositively with
`𝓕(Ξ²χ G_δ)`. -/
theorem re_deviationPairing_xiSqCutoff_nonpos {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {Dₑ : ℝ} (hexc : CauchyBounded (deviationExcess lam) Dₑ) (δ : ℝ) :
    (deviationPairing lam (𝓕 fun ξ => xiSqCutoff ξ * packet pdPacketC 0 δ ξ)).re ≤ 0 := by
  obtain ⟨σ, hσf, hσ⟩ := exists_spectralMeasure hW
  have hs := contDiff_cutoffPacket δ
  have hc := hasCompactSupport_cutoffPacket δ
  rw [xiSqCutoff_mul_packet, deviationPairing_fourier_riemannXi_sq_mul hW hexc σ hσ hs.continuous
    (hs.continuous.integrable_of_hasCompactSupport hc) (integrable_fourier_smooth hs hc),
    Complex.neg_re, neg_nonpos]
  have hfun : (fun t => cutoffPacket δ (t / (2 * π))) = fun t =>
      ((excessFlatBump ((t / (2 * π) - 0) / 1) * pdPacket ((t / (2 * π) - 0) / δ) : ℝ) : ℂ) :=
    funext fun t => cutoffPacket_eq δ _
  rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun t => mul_nonneg excessFlatBump.nonneg (pdPacket_nonneg _)

/-- **The excess mean is at most the deficit mean**, up to `O(δ)`. -/
theorem exists_excessMean_le_deficitMean {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      deficitMean (deviationExcess lam) δ ≤ deficitMean (deviationDeficit lam) δ + C * δ := by
  obtain ⟨D, -, hD'⟩ := exists_tsum_deficit_cauchyProfile_le hW hexc
  have hD : CauchyBounded (deviationDeficit lam) D := hD'
  obtain ⟨Kv, hKv, hOPv⟩ := exists_originPacket_bound (deviationDeficit_nonneg lam) hD
  obtain ⟨Ke, hKe, hOPe⟩ := exists_originPacket_bound (deviationExcess_nonneg lam) hexc
  set M := ∫ s, ‖𝓕 xiSqCutoff s‖ * (|s| * (1 + s ^ 2)) with hM
  have hM0 : 0 ≤ M := moment_nonneg _
  set c := riemannXiReal 0 ^ 2 with hc
  have hc0 : 0 < c := riemannXiReal_zero_sq_pos
  refine ⟨(Kv + Ke) * M / c, by positivity, fun δ hδ0 hδ1 => ?_⟩
  obtain ⟨hvs, hv⟩ := hOPv contDiff_xiSqCutoff hasCompactSupport_xiSqCutoff hδ0 hδ1
  obtain ⟨hes, he⟩ := hOPe contDiff_xiSqCutoff hasCompactSupport_xiSqCutoff hδ0 hδ1
  rw [xiSqCutoff_zero] at hv he
  have hP := deviationPairing_eq_sub hes hvs
  have hneg : -deviationPairing lam (𝓕 fun ξ => xiSqCutoff ξ * packet pdPacketC 0 δ ξ) =
      weightPairing (deviationDeficit lam) (𝓕 fun ξ => xiSqCutoff ξ * packet pdPacketC 0 δ ξ) -
        weightPairing (deviationExcess lam) (𝓕 fun ξ => xiSqCutoff ξ * packet pdPacketC 0 δ ξ) := by
    rw [hP]; ring
  have h1 := mul_sub_le_of_eq_sub hneg hv he
  have h2 := re_deviationPairing_xiSqCutoff_nonpos hW hexc δ
  rw [Complex.neg_re] at h1
  have h3 : c * deficitMean (deviationExcess lam) δ - c * deficitMean (deviationDeficit lam) δ ≤
      (Kv + Ke) * M * δ := by linarith
  have h4 : deficitMean (deviationExcess lam) δ - deficitMean (deviationDeficit lam) δ ≤
      (Kv + Ke) * M * δ / c := by
    rw [le_div_iff₀ hc0]; linarith
  have h5 : (Kv + Ke) * M / c * δ = (Kv + Ke) * M * δ / c := by ring
  linarith

/-- **Deficit mean vanishing forces excess mean vanishing.** -/
theorem excessMeanVanishes_of_deficitMean {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ)
    (hmean : ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      deficitMean (deviationDeficit lam) δ ≤ η) :
    ExcessMeanVanishes lam := by
  obtain ⟨C, hC0, hC⟩ := exists_excessMean_le_deficitMean hW hexc
  intro η hη
  obtain ⟨δ₁, hδ₁, h₁⟩ := hmean (η / 2) (by positivity)
  refine ⟨min (min δ₁ 1) (η / (2 * (C + 1))), lt_min (lt_min hδ₁ one_pos) (by positivity),
    fun δ hδ0 hδ => ?_⟩
  have hδ1 : δ ≤ δ₁ := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ2 : δ ≤ 1 := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ3 : δ ≤ η / (2 * (C + 1)) := hδ.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at hδ3
  have := hC δ hδ0 hδ2
  have := h₁ δ hδ0 hδ1
  nlinarith

/-- **Density-zero deficit rigidity.** A full-cone Weil-positive `lam` whose deficit below `Λ` is
translation-bounded with vanishing mean equals `Λ` at every `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_deficitMeanVanishes {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {D : ℝ} (hdef : CauchyBounded (deviationDeficit lam) D)
    (hmean : ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      deficitMean (deviationDeficit lam) δ ≤ η) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨Dₑ, -, hexc⟩ := exists_tsum_excess_cauchyProfile_le hW hdef
  exact eq_vonMangoldt_of_weilPositiveFull_of_excessMeanVanishes hW hexc
    (excessMeanVanishes_of_deficitMean hW hexc hmean)

end

end RHTower.WeilExcess
