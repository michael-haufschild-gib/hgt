import GaloisForLFunctions.RHTower.WeilDeviationDeficitMeanVanishes

/-!
# A Weil-positive system with density-zero excess annihilates every smooth test

Let `lam` be full-cone Weil-positive, and `a = (lam − Λ)/√n` its deviation. Assume the excess
`a⁺` is translation-bounded (`CauchyBounded`) and has vanishing mean (`ExcessMeanVanishes`).
Summable excess is a special case.

**Theorem** (`deviationPairing_fourier_eq_zero`). For every smooth compactly supported `h`,
`Σ_n a(n) (𝓕h(log n) + 𝓕h(−log n)) = 0`.

**Proof.** Decompose `h` into a packet at the origin, flat packets at the zeros of `Ξ` in a
window, and a remainder `R_h` vanishing near those zeros.
- The packets contribute at most `H(1 + N)(A_δ + E_δ + K'ε) + O_ε(δ)`, where `H` bounds `|h|`,
  `N` counts the zeros, and `A_δ`, `E_δ` are the deficit and excess means. These are small: the
  excess mean vanishes by hypothesis, and then the deficit mean vanishes by mean balance.
- The remainder pairs to `−∫ (R_h/Ξ²)(t/2π) dσ`. It is dominated by `C` times the remainder of
  `r = F(·/s) χ(·/Γ)`, where `F(·/s)` is a dilated Fejér test and `r ≥ |h|/C`.
- The pairing of `r` equals minus the tail of the Fejér identity, and its packets are small by the
  same estimate.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ContDiff

namespace RHTower.WeilExcess

noncomputable section

/-! ## The cut-off identity for band-limited tests -/

/-- The transform of `Φ` splits into the cut-off part and the tail. -/
theorem fourier_eq_add_tailTransform {Φ : ℝ → ℂ} (hΦi : Integrable Φ) (Γ u : ℝ) :
    𝓕 Φ u = 𝓕 (fun ξ => Φ ξ * packet cutoffC 0 Γ ξ) u + tailTransform Φ Γ u := by
  have hmeas : Continuous (packet cutoffC 0 Γ) := (contDiff_packet contDiff_cutoffC 0 Γ).continuous
  have hi : Integrable fun ξ => Φ ξ * packet cutoffC 0 Γ ξ :=
    hΦi.mul_bdd hmeas.aestronglyMeasurable
      (Eventually.of_forall fun ξ => norm_packet_cutoffC_le Γ ξ)
  have hi2 : Integrable fun ξ => Φ ξ * (1 - packet cutoffC 0 Γ ξ) :=
    hΦi.mul_bdd (continuous_const.sub hmeas).aestronglyMeasurable
      (Eventually.of_forall fun ξ => norm_one_sub_cutoffC_le _)
  have hfun : (fun ξ => Φ ξ * packet cutoffC 0 Γ ξ + Φ ξ * (1 - packet cutoffC 0 Γ ξ)) = Φ := by
    funext ξ; ring
  rw [tailTransform, ← fourier_add_eq hi hi2, hfun]

/-- If `𝓕Φ` vanishes at every `±log n` with `n ≥ 2`, then the cut-off test `Φ χ(·/Γ)` pairs to
minus the tail. -/
theorem deviationPairing_fourier_mul_cutoff (lam : ℕ → ℝ) {Φ : ℝ → ℂ} (hΦi : Integrable Φ)
    (hlog : ∀ n : ℕ, 2 ≤ n → 𝓕 Φ (Real.log n) = 0 ∧ 𝓕 Φ (-Real.log n) = 0) (Γ : ℝ) :
    deviationPairing lam (𝓕 fun ξ => Φ ξ * packet cutoffC 0 Γ ξ) =
      -deviationPairing lam (tailTransform Φ Γ) := by
  have hsplit := fourier_eq_add_tailTransform hΦi Γ
  unfold deviationPairing
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  by_cases hn : 2 ≤ n
  · have e1 := hsplit (Real.log n)
    have e2 := hsplit (-Real.log n)
    rw [(hlog n hn).1] at e1
    rw [(hlog n hn).2] at e2
    rw [show 𝓕 (fun ξ => Φ ξ * packet cutoffC 0 Γ ξ) (Real.log n) =
          -tailTransform Φ Γ (Real.log n) by linear_combination -e1,
      show 𝓕 (fun ξ => Φ ξ * packet cutoffC 0 Γ ξ) (-Real.log n) =
          -tailTransform Φ Γ (-Real.log n) by linear_combination -e2]
    ring
  · simp [weilDeviation, hn]

/-! ## Dilated Fejér tests -/

/-- The Fejér test dilated by `s`: `F(ξ/s)`. -/
def dilatedFejer (s : ℝ) : ℝ → ℂ := packet fejerTestC 0 s

theorem fourier_dilatedFejer {s : ℝ} (hs : 0 < s) (u : ℝ) :
    𝓕 (dilatedFejer s) u = (s : ℂ) * 𝓕 fejerTestC (s * u) := by
  rw [dilatedFejer, fourier_packet _ _ hs]
  simp

theorem fourier_dilatedFejer_eq_zero {s : ℝ} (hs : 1 ≤ s) {u : ℝ} (hu : 17 / 25 < |u|) :
    𝓕 (dilatedFejer s) u = 0 := by
  rw [fourier_dilatedFejer (by linarith), fourier_fejerTestC_eq_zero, mul_zero]
  rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s)]
  exact hu.trans_le (le_mul_of_one_le_left (abs_nonneg u) hs)

theorem fourier_dilatedFejer_log_eq_zero {s : ℝ} (hs : 1 ≤ s) (n : ℕ) (hn : 2 ≤ n) :
    𝓕 (dilatedFejer s) (Real.log n) = 0 ∧ 𝓕 (dilatedFejer s) (-Real.log n) = 0 := by
  have hlog : 17 / 25 < Real.log n := seventeen_div_twentyfive_lt_log_two.trans_le
    (Real.log_le_log two_pos (by exact_mod_cast hn))
  have hpos : 0 < Real.log n := by linarith
  exact ⟨fourier_dilatedFejer_eq_zero hs (by rwa [abs_of_pos hpos]),
    fourier_dilatedFejer_eq_zero hs (by rwa [abs_neg, abs_of_pos hpos])⟩

theorem contDiff_dilatedFejer (s : ℝ) : ContDiff ℝ ∞ (dilatedFejer s) :=
  contDiff_packet contDiff_fejerTestC 0 s

theorem integrable_dilatedFejer {s : ℝ} (hs : 0 < s) : Integrable (dilatedFejer s) :=
  integrable_packet integrable_fejerTestC 0 hs

theorem integrable_fourier_dilatedFejer {s : ℝ} (hs : 1 ≤ s) :
    Integrable (𝓕 (dilatedFejer s)) := by
  refine (continuous_fourier_integrable
    (integrable_dilatedFejer (by linarith))).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -(17 / 25)) (b := 17 / 25)) fun u hu => ?_
  apply fourier_dilatedFejer_eq_zero hs
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with hu | hu
  · linarith [neg_abs_le u]
  · linarith [le_abs_self u]

/-- The cut-off dilated Fejér test `F(ξ/s) χ(ξ/Γ)`, as a real function. -/
def dilatedFejerCutoff (s Γ ξ : ℝ) : ℝ := fejerTest (ξ / s) * excessFlatBump (ξ / Γ)

theorem dilatedFejerCutoff_nonneg (s Γ ξ : ℝ) : 0 ≤ dilatedFejerCutoff s Γ ξ :=
  mul_nonneg (fejerTest_nonneg _) excessFlatBump.nonneg

theorem dilatedFejer_mul_cutoff_eq (s Γ : ℝ) :
    (fun ξ => dilatedFejer s ξ * packet cutoffC 0 Γ ξ) =
      fun ξ => (dilatedFejerCutoff s Γ ξ : ℂ) := by
  funext ξ
  simp [dilatedFejer, dilatedFejerCutoff, packet, fejerTestC, cutoffC]

theorem contDiff_dilatedFejerCutoff (s Γ : ℝ) :
    ContDiff ℝ ∞ fun ξ => (dilatedFejerCutoff s Γ ξ : ℂ) := by
  rw [← dilatedFejer_mul_cutoff_eq]
  exact (contDiff_dilatedFejer s).mul (contDiff_packet contDiff_cutoffC 0 Γ)

theorem hasCompactSupport_dilatedFejerCutoff (s : ℝ) {Γ : ℝ} (hΓ : 0 < Γ) :
    HasCompactSupport fun ξ => (dilatedFejerCutoff s Γ ξ : ℂ) := by
  rw [← dilatedFejer_mul_cutoff_eq]
  exact hasCompactSupport_mul_cutoff hΓ

theorem tsupport_dilatedFejerCutoff_subset (s : ℝ) {Γ : ℝ} (hΓ : 0 < Γ) :
    tsupport (fun ξ => (dilatedFejerCutoff s Γ ξ : ℂ)) ⊆ Icc (-(2 * Γ)) (2 * Γ) := by
  rw [← dilatedFejer_mul_cutoff_eq]
  exact tsupport_mul_cutoff_subset hΓ

theorem norm_dilatedFejerCutoff_le (s Γ ξ : ℝ) : ‖(dilatedFejerCutoff s Γ ξ : ℂ)‖ ≤ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dilatedFejerCutoff_nonneg s Γ ξ)]
  have h1 : fejerTest (ξ / s) ≤ 2 := by
    refine (fejerTest_le_profile _).trans ?_
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (ξ / s)]
  calc dilatedFejerCutoff s Γ ξ ≤ fejerTest (ξ / s) * 1 :=
        mul_le_mul_of_nonneg_left excessFlatBump.le_one (fejerTest_nonneg _)
    _ ≤ 2 := by rw [mul_one]; exact h1

/-- The Fejér test is at least half its peak near the origin. -/
theorem exists_fejerTest_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ x, |x| ≤ c → fejerTest 0 / 2 ≤ fejerTest x := by
  have hcont : Continuous fejerTest := by
    have : fejerTest = fun x => (fejerTestC x).re := funext fun x => by simp [fejerTestC]
    rw [this]; exact Complex.continuous_re.comp contDiff_fejerTestC.continuous
  have hF0 : 0 < fejerTest 0 := lt_trans (by norm_num) three_eighths_lt_fejerTest_zero
  obtain ⟨c, hc, hcδ⟩ := Metric.continuous_iff.mp hcont 0 (fejerTest 0 / 2) (by linarith)
  refine ⟨c / 2, by linarith, fun x hx => ?_⟩
  have := hcδ x (by rw [Real.dist_eq, sub_zero]; linarith)
  rw [Real.dist_eq] at this
  linarith [neg_abs_le (fejerTest x - fejerTest 0)]

/-- **Domination by a dilated Fejér test.** A bounded function supported in `[−L, L]` is at most
`C` times the cut-off dilated Fejér test `F(·/s) χ(·/Γ)`, for every `Γ ≥ L`. -/
theorem exists_dilatedFejer_domination {h : ℝ → ℂ} {H L : ℝ} (hH : ∀ ξ, ‖h ξ‖ ≤ H)
    (hL : ∀ ξ ∈ tsupport h, |ξ| ≤ L) :
    ∃ C s : ℝ, 0 ≤ C ∧ 1 ≤ s ∧ ∀ Γ : ℝ, L ≤ Γ → 0 < Γ → ∀ ξ,
      ‖h ξ‖ ≤ C * dilatedFejerCutoff s Γ ξ := by
  obtain ⟨c, hc0, hcF⟩ := exists_fejerTest_lower
  have hF0 : 0 < fejerTest 0 := lt_trans (by norm_num) three_eighths_lt_fejerTest_zero
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  refine ⟨2 * H / fejerTest 0, max 1 (L / c), by positivity, le_max_left _ _,
    fun Γ hLΓ hΓ ξ => ?_⟩
  by_cases hξ : ξ ∈ tsupport h
  · have hξL := hL ξ hξ
    have hs : 0 < max 1 (L / c) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hsc : |ξ / max 1 (L / c)| ≤ c := by
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
      calc |ξ| ≤ L := hξL
        _ = L / c * c := by field_simp
        _ ≤ max 1 (L / c) * c := mul_le_mul_of_nonneg_right (le_max_right _ _) hc0.le
        _ = c * max 1 (L / c) := mul_comm _ _
    have hχ : excessFlatBump (ξ / Γ) = 1 := excessFlatBump_eq_one (by
      rw [abs_div, abs_of_pos hΓ, div_le_one hΓ]; exact hξL.trans hLΓ)
    rw [dilatedFejerCutoff, hχ, mul_one]
    have h1 := hcF _ hsc
    calc ‖h ξ‖ ≤ H := hH ξ
      _ = 2 * H / fejerTest 0 * (fejerTest 0 / 2) := by field_simp
      _ ≤ 2 * H / fejerTest 0 * fejerTest (ξ / max 1 (L / c)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
  · rw [image_eq_zero_of_notMem_tsupport hξ, norm_zero]
    exact mul_nonneg (by positivity) (dilatedFejerCutoff_nonneg _ _ _)

/-! ## The packet error -/

/-- A pairing within `k` of `h(x)·M` has norm at most `‖h(x)‖ M + k`, for `M ≥ 0`. -/
theorem norm_le_of_norm_sub_le {W c : ℂ} {M k : ℝ} (hM : 0 ≤ M)
    (h : ‖W - c * (M : ℂ)‖ ≤ k) : ‖W‖ ≤ ‖c‖ * M + k := by
  have h1 := norm_sub_norm_le W (c * (M : ℂ))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM] at h1
  linarith

/-- **The packet error.** The origin packet and the flat packets at the points of `Z` pair with the
deviation to at most `H (1 + |Z|)(A_δ + E_δ + K'ε) + O_ε(δ)`, where `H` bounds `|h|` and `A_δ`,
`E_δ` are the deficit and excess means. -/
theorem exists_packet_error_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ) :
    ∃ K₀ K' : ℝ, 0 ≤ K₀ ∧ 0 ≤ K' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ Kε : ℝ, 0 ≤ Kε ∧
      ∀ {h : ℝ → ℂ}, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ {H : ℝ}, (∀ ξ, ‖h ξ‖ ≤ H) →
      ∀ (Z : Finset ℝ) {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ‖deviationPairing lam (𝓕 fun ξ => h ξ * packet pdPacketC 0 δ ξ)‖ +
        ∑ γ ∈ Z, ‖deviationPairing lam (𝓕 fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ)‖ ≤
      H * (1 + Z.card) * ((deficitMean (deviationDeficit lam) δ +
          deficitMean (deviationExcess lam) δ) + K' * ε) +
        (K₀ + Z.card * Kε) * δ * (∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2))) := by
  obtain ⟨D, -, hD'⟩ := exists_tsum_deficit_cauchyProfile_le hW hexc
  have hD : CauchyBounded (deviationDeficit lam) D := hD'
  have hv0 := deviationDeficit_nonneg lam
  have he0 := deviationExcess_nonneg lam
  obtain ⟨K₀v, hK₀v, hOPv⟩ := exists_originPacket_bound hv0 hD
  obtain ⟨K₀e, hK₀e, hOPe⟩ := exists_originPacket_bound he0 hexc
  obtain ⟨K'v, hK'v, hZPv⟩ := exists_zeroPacket_bound hv0 hD
  obtain ⟨K'e, hK'e, hZPe⟩ := exists_zeroPacket_bound he0 hexc
  refine ⟨K₀v + K₀e, K'v + K'e, add_nonneg hK₀v hK₀e, add_nonneg hK'v hK'e,
    fun ε hε0 hε1 => ?_⟩
  obtain ⟨Kεv, hKεv, hZPεv⟩ := hZPv hε0 hε1
  obtain ⟨Kεe, hKεe, hZPεe⟩ := hZPe hε0 hε1
  refine ⟨Kεv + Kεe, add_nonneg hKεv hKεe, fun {h} hs hc {H} hH Z {δ} hδ0 hδ1 => ?_⟩
  have hA0 := deficitMean_nonneg hv0 hD hδ0 hδ1
  have hE0 := deficitMean_nonneg he0 hexc hδ0 hδ1
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  have hK'ε : 0 ≤ H * ((K'v + K'e) * ε) :=
    mul_nonneg hH0 (mul_nonneg (add_nonneg hK'v hK'e) hε0.le)
  -- the origin packet
  obtain ⟨hvs₀, hv₀⟩ := hOPv hs hc hδ0 hδ1
  obtain ⟨hes₀, he₀⟩ := hOPe hs hc hδ0 hδ1
  have h0 : ‖deviationPairing lam (𝓕 fun ξ => h ξ * packet pdPacketC 0 δ ξ)‖ ≤
      H * ((deficitMean (deviationDeficit lam) δ + deficitMean (deviationExcess lam) δ) +
        (K'v + K'e) * ε) +
      (K₀v + K₀e) * δ * ∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2)) := by
    rw [deviationPairing_eq_sub hes₀ hvs₀]
    have h1 := norm_le_of_norm_sub_le hA0 hv₀
    have h2 := norm_le_of_norm_sub_le hE0 he₀
    have h3 := mul_le_mul_of_nonneg_right (hH 0) hA0
    have h4 := mul_le_mul_of_nonneg_right (hH 0) hE0
    have h5 := norm_sub_le (weightPairing (deviationExcess lam)
      (𝓕 fun ξ => h ξ * packet pdPacketC 0 δ ξ))
      (weightPairing (deviationDeficit lam) (𝓕 fun ξ => h ξ * packet pdPacketC 0 δ ξ))
    linarith
  -- the zero packets
  have hγ : ∀ γ ∈ Z,
      ‖deviationPairing lam (𝓕 fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ)‖ ≤
        H * ((deficitMean (deviationDeficit lam) δ + deficitMean (deviationExcess lam) δ) +
          (K'v + K'e) * ε) +
        (Kεv + Kεe) * δ * ∫ s, ‖𝓕 h s‖ * (|s| * (1 + s ^ 2)) := by
    intro γ _
    obtain ⟨hvsγ, hvγ⟩ := hZPεv hs hc γ hδ0 hδ1
    obtain ⟨hesγ, heγ⟩ := hZPεe hs hc γ hδ0 hδ1
    rw [deviationPairing_eq_sub hesγ hvsγ]
    have h2 := mul_le_mul_of_nonneg_right (hH γ)
      (add_nonneg (add_nonneg hA0 hE0) (mul_nonneg (add_nonneg hK'v hK'e) hε0.le))
    have h5 := norm_sub_le (weightPairing (deviationExcess lam)
      (𝓕 fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ))
      (weightPairing (deviationDeficit lam) (𝓕 fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ))
    linarith
  have hsum := Finset.sum_le_card_nsmul Z _ _ hγ
  rw [nsmul_eq_mul] at hsum
  linarith

/-! ## Domination of the remainder -/

theorem integrable_divRiemannXiSq_remainder {h : ℝ → ℂ} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {Z : Finset ℝ} {δ ε : ℝ} (hS : Separated Z δ) (hε0 : 0 < ε)
    (hε : ε ≤ 1) (hZ : ∀ ξ ∈ tsupport h, riemannXi ξ = 0 → ξ ∈ Z) (σ : Measure ℝ)
    [IsFiniteMeasure σ] :
    Integrable (fun t => divRiemannXiSq (packetRemainder h Z ε δ) (t / (2 * π))) σ := by
  have hvan : ∀ ξ, riemannXi ξ = 0 → packetRemainder h Z ε δ =ᶠ[𝓝 ξ] 0 := fun ξ hξ =>
    remainder_eventuallyEq_zero hS hε0 hε hZ hξ
  have hgs := contDiff_divRiemannXiSq (contDiff_packetRemainder hs Z ε δ) hvan
  have hgc := hasCompactSupport_divRiemannXiSq (hasCompactSupport_packetRemainder hc Z ε δ)
  obtain ⟨C, hC⟩ := hgs.continuous.norm.bddAbove_range_of_hasCompactSupport hgc.norm
  exact (integrable_const C).mono' ((hgs.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t => hC ⟨_, rfl⟩)

/-- The remainder quotient of a real test is real. -/
theorem divRiemannXiSq_remainder_ofReal (r : ℝ → ℝ) (Z : Finset ℝ) (ε δ ξ : ℝ) :
    divRiemannXiSq (packetRemainder (fun ξ => (r ξ : ℂ)) Z ε δ) ξ =
      ((r ξ * (1 - packetSumReal Z ε δ ξ) / riemannXiReal ξ ^ 2 : ℝ) : ℂ) := by
  simp only [divRiemannXiSq, packetRemainder, riemannXi_eq_ofReal]
  push_cast; ring

theorem norm_divRiemannXiSq_remainder_le {h : ℝ → ℂ} {r : ℝ → ℝ} {C : ℝ}
    (hhr : ∀ ξ, ‖h ξ‖ ≤ C * r ξ) {Z : Finset ℝ} {δ ε : ℝ} (hS : Separated Z δ) (hε0 : 0 < ε)
    (hε : ε ≤ 1) (ξ : ℝ) :
    ‖divRiemannXiSq (packetRemainder h Z ε δ) ξ‖ ≤
      C * (r ξ * (1 - packetSumReal Z ε δ ξ) / riemannXiReal ξ ^ 2) := by
  have hS1 : 0 ≤ 1 - packetSumReal Z ε δ ξ := by linarith [packetSumReal_le_one hS hε0 hε ξ]
  have e1 : ‖divRiemannXiSq (packetRemainder h Z ε δ) ξ‖ =
      ‖h ξ‖ * (1 - packetSumReal Z ε δ ξ) / riemannXiReal ξ ^ 2 := by
    rw [divRiemannXiSq, packetRemainder, riemannXi_eq_ofReal, norm_div, norm_mul, norm_pow,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hS1, sq_abs]
  rw [e1, mul_div_assoc', ← mul_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hhr ξ) hS1) (sq_nonneg _)

theorem norm_integral_le_of_real {σ : Measure ℝ} {f : ℝ → ℂ} {g : ℝ → ℝ} {C : ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hgi : Integrable g σ) (hfg : ∀ t, ‖f t‖ ≤ C * g t) :
    ‖∫ t, f t ∂σ‖ ≤ C * ‖∫ t, (g t : ℂ) ∂σ‖ := by
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg hg0),
    ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hgi.const_mul C) (Eventually.of_forall hfg)

/-- **Domination of the remainder.** If `|h| ≤ C r` with `r ≥ 0` real, the remainder of `h` pairs to
at most `C` times the remainder of `r`. -/
theorem norm_deviationPairing_remainder_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {Dₑ : ℝ} (hexc : CauchyBounded (deviationExcess lam) Dₑ) {h : ℝ → ℂ} {r : ℝ → ℝ} {C : ℝ}
    (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hrs : ContDiff ℝ ∞ fun ξ => (r ξ : ℂ)) (hrc : HasCompactSupport fun ξ => (r ξ : ℂ))
    (hr0 : ∀ ξ, 0 ≤ r ξ) (hhr : ∀ ξ, ‖h ξ‖ ≤ C * r ξ) {Z : Finset ℝ} {δ ε : ℝ}
    (hS : Separated Z δ) (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hZ : ∀ ξ ∈ tsupport h, riemannXi ξ = 0 → ξ ∈ Z)
    (hZr : ∀ ξ ∈ tsupport (fun ξ => (r ξ : ℂ)), riemannXi ξ = 0 → ξ ∈ Z) :
    ‖deviationPairing lam (𝓕 (packetRemainder h Z ε δ))‖ ≤
      C * ‖deviationPairing lam (𝓕 (packetRemainder (fun ξ => (r ξ : ℂ)) Z ε δ))‖ := by
  obtain ⟨σ, hσf, hσ⟩ := exists_spectralMeasure hW
  have hir := integrable_divRiemannXiSq_remainder hrs hrc hS hε0 hε hZr σ
  rw [deviationPairing_packetRemainder hW hexc σ hσ hs hc hS hε0 hε hZ,
    deviationPairing_packetRemainder hW hexc σ hσ hrs hrc hS hε0 hε hZr, norm_neg, norm_neg]
  set g : ℝ → ℝ := fun t => r (t / (2 * π)) * (1 - packetSumReal Z ε δ (t / (2 * π))) /
    riemannXiReal (t / (2 * π)) ^ 2 with hg
  have hfun : (fun t => divRiemannXiSq (packetRemainder (fun ξ => (r ξ : ℂ)) Z ε δ)
      (t / (2 * π))) = fun t => (g t : ℂ) :=
    funext fun t => divRiemannXiSq_remainder_ofReal r Z ε δ _
  have hg0 : ∀ t, 0 ≤ g t := fun t =>
    div_nonneg (mul_nonneg (hr0 _) (by linarith [packetSumReal_le_one hS hε0 hε (t / (2 * π))]))
      (sq_nonneg _)
  rw [hfun] at hir ⊢
  have hgi : Integrable g σ := hir.norm.congr (Eventually.of_forall fun t => by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 t)])
  exact norm_integral_le_of_real hg0 hgi fun t => norm_divRiemannXiSq_remainder_le hhr hS hε0 hε _

/-- **The dominated estimate.** If `|h| ≤ C r`, the pairing of `h` is bounded by the packets of `h`
plus `C` times the pairing and packets of `r`. -/
theorem norm_deviationPairing_le_of_dominated {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {Dₑ : ℝ} (hexc : CauchyBounded (deviationExcess lam) Dₑ) {D : ℝ} (hD : CauchyBounded (deviationDeficit lam) D)
    {h : ℝ → ℂ} {r : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
    (hrs : ContDiff ℝ ∞ fun ξ => (r ξ : ℂ)) (hrc : HasCompactSupport fun ξ => (r ξ : ℂ))
    (hr0 : ∀ ξ, 0 ≤ r ξ) (hhr : ∀ ξ, ‖h ξ‖ ≤ C * r ξ) {Z : Finset ℝ} {δ ε : ℝ}
    (hS : Separated Z δ) (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hZ : ∀ ξ ∈ tsupport h, riemannXi ξ = 0 → ξ ∈ Z)
    (hZr : ∀ ξ ∈ tsupport (fun ξ => (r ξ : ℂ)), riemannXi ξ = 0 → ξ ∈ Z) :
    ‖deviationPairing lam (𝓕 h)‖ ≤
      (‖deviationPairing lam (𝓕 fun ξ => h ξ * packet pdPacketC 0 δ ξ)‖ +
        ∑ γ ∈ Z, ‖deviationPairing lam (𝓕 fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ)‖) +
      C * (‖deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ))‖ +
        (‖deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ) * packet pdPacketC 0 δ ξ)‖ +
          ∑ γ ∈ Z, ‖deviationPairing lam
            (𝓕 fun ξ => (r ξ : ℂ) * packet (flatPacketC ε) γ δ ξ)‖)) := by
  have eh := deviationPairing_packet_decomposition hexc hD hs hc Z ε δ
  have er := deviationPairing_packet_decomposition hexc hD hrs hrc Z ε δ
  have hR := norm_deviationPairing_remainder_le hW hexc hs hc hrs hrc hr0 hhr hS hε0 hε hZ hZr
  have hRr : ‖deviationPairing lam (𝓕 (packetRemainder (fun ξ => (r ξ : ℂ)) Z ε δ))‖ ≤
      ‖deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ))‖ +
        (‖deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ) * packet pdPacketC 0 δ ξ)‖ +
          ∑ γ ∈ Z, ‖deviationPairing lam
            (𝓕 fun ξ => (r ξ : ℂ) * packet (flatPacketC ε) γ δ ξ)‖) := by
    rw [show deviationPairing lam (𝓕 (packetRemainder (fun ξ => (r ξ : ℂ)) Z ε δ)) =
        deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ)) -
          deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ) * packet pdPacketC 0 δ ξ) -
          ∑ γ ∈ Z, deviationPairing lam
            (𝓕 fun ξ => (r ξ : ℂ) * packet (flatPacketC ε) γ δ ξ) by rw [er]; ring]
    have h1 := norm_sub_le (deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ)) -
      deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ) * packet pdPacketC 0 δ ξ))
      (∑ γ ∈ Z, deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ) * packet (flatPacketC ε) γ δ ξ))
    have h2 := norm_sub_le (deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ)))
      (deviationPairing lam (𝓕 fun ξ => (r ξ : ℂ) * packet pdPacketC 0 δ ξ))
    have h3 := norm_sum_le Z fun γ => deviationPairing lam
      (𝓕 fun ξ => (r ξ : ℂ) * packet (flatPacketC ε) γ δ ξ)
    linarith
  have h4 := mul_le_mul_of_nonneg_left hRr hC
  rw [eh]
  refine norm_add₃_le.trans ?_
  have h6 := norm_sum_le Z fun γ => deviationPairing lam
    (𝓕 fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ)
  linarith

/-! ## The annihilation theorem -/

/-- **The dominated bound at fixed parameters.** For `h` dominated by `C` times the cut-off
dilated Fejér test, the pairing of `h` is at most the packet errors of `h` and of the Fejér test
plus `C` times the Fejér tail. -/
theorem exists_norm_deviationPairing_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ) {h : ℝ → ℂ} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) {H L C s : ℝ} (hH : ∀ ξ, ‖h ξ‖ ≤ H)
    (hL : ∀ ξ ∈ tsupport h, |ξ| ≤ L) (hC : 0 ≤ C) (hs1 : 1 ≤ s)
    (hdom : ∀ Γ : ℝ, L ≤ Γ → 0 < Γ → ∀ ξ, ‖h ξ‖ ≤ C * dilatedFejerCutoff s Γ ξ) :
    ∃ K₀ K' : ℝ, 0 ≤ K₀ ∧ 0 ≤ K' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ Kε : ℝ, 0 ≤ Kε ∧
      ∀ Γ δ : ℝ, L ≤ Γ → 0 < Γ → 0 < δ → δ ≤ 1 → Separated (zeroWindow (2 * Γ)) δ →
      ‖deviationPairing lam (𝓕 h)‖ ≤
        (H + 2 * C) * (1 + ((zeroWindow (2 * Γ)).card : ℝ)) *
          ((deficitMean (deviationDeficit lam) δ + deficitMean (deviationExcess lam) δ) +
            K' * ε) +
        (K₀ + ((zeroWindow (2 * Γ)).card : ℝ) * Kε) * δ *
          ((∫ u, ‖𝓕 h u‖ * (|u| * (1 + u ^ 2))) +
            C * ∫ u, ‖𝓕 (fun ξ => (dilatedFejerCutoff s Γ ξ : ℂ)) u‖ * (|u| * (1 + u ^ 2))) +
        C * ‖deviationPairing lam (tailTransform (dilatedFejer s) Γ)‖ := by
  obtain ⟨D, -, hD'⟩ := exists_tsum_deficit_cauchyProfile_le hW hexc
  have hD : CauchyBounded (deviationDeficit lam) D := hD'
  obtain ⟨K₀, K', hK₀, hK', herr⟩ := exists_packet_error_le hW hexc
  refine ⟨K₀, K', hK₀, hK', fun ε hε0 hε1 => ?_⟩
  obtain ⟨Kε, hKε, herrε⟩ := herr ε hε0 hε1
  refine ⟨Kε, hKε, fun Γ δ hLΓ hΓ hδ0 hδ1 hS => ?_⟩
  have hrs := contDiff_dilatedFejerCutoff s Γ
  have hrc := hasCompactSupport_dilatedFejerCutoff s hΓ
  have hZ : ∀ ξ ∈ tsupport h, riemannXi ξ = 0 → ξ ∈ zeroWindow (2 * Γ) := fun ξ hξ hz =>
    mem_zeroWindow.mpr ⟨by linarith [hL ξ hξ], hz⟩
  have hZr : ∀ ξ ∈ tsupport (fun ξ => (dilatedFejerCutoff s Γ ξ : ℂ)), riemannXi ξ = 0 →
      ξ ∈ zeroWindow (2 * Γ) := fun ξ hξ hz =>
    mem_zeroWindow.mpr ⟨abs_le.mpr (tsupport_dilatedFejerCutoff_subset s hΓ hξ), hz⟩
  have key := norm_deviationPairing_le_of_dominated hW hexc hD hC hs hc hrs hrc
    (dilatedFejerCutoff_nonneg s Γ) (hdom Γ hLΓ hΓ) hS hε0 hε1 hZ hZr
  have eh := herrε hs hc hH (zeroWindow (2 * Γ)) hδ0 hδ1
  have er := herrε hrs hrc (norm_dilatedFejerCutoff_le s Γ) (zeroWindow (2 * Γ)) hδ0 hδ1
  have htail : deviationPairing lam (𝓕 fun ξ => (dilatedFejerCutoff s Γ ξ : ℂ)) =
      -deviationPairing lam (tailTransform (dilatedFejer s) Γ) := by
    rw [← dilatedFejer_mul_cutoff_eq]
    exact deviationPairing_fourier_mul_cutoff lam (integrable_dilatedFejer (by linarith))
      (fourier_dilatedFejer_log_eq_zero hs1) Γ
  rw [htail, norm_neg] at key
  have er' := mul_le_mul_of_nonneg_left er hC
  linarith

/-- **The deviation annihilates every smooth test.** Let `lam` be full-cone Weil-positive whose
excess is translation-bounded with vanishing mean. Then `Σ_n a(n)(𝓕h(log n) + 𝓕h(−log n)) = 0`
for every smooth compactly supported `h`. -/
theorem deviationPairing_fourier_eq_zero {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ) (hmean : ExcessMeanVanishes lam)
    {h : ℝ → ℂ} (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    deviationPairing lam (𝓕 h) = 0 := by
  obtain ⟨D, -, hD'⟩ := exists_tsum_deficit_cauchyProfile_le hW hexc
  have hD : CauchyBounded (deviationDeficit lam) D := hD'
  obtain ⟨H, hH⟩ : ∃ H, ∀ ξ, ‖h ξ‖ ≤ H := by
    obtain ⟨H, hH⟩ := hs.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
    exact ⟨H, fun ξ => hH ⟨ξ, rfl⟩⟩
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  obtain ⟨L, hL⟩ : ∃ L, ∀ ξ ∈ tsupport h, |ξ| ≤ L := by
    obtain ⟨L, hL⟩ := hc.isCompact.isBounded.subset_closedBall 0
    refine ⟨L, fun ξ hξ => ?_⟩
    have := hL hξ
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  obtain ⟨C, s, hC, hs1, hdom⟩ := exists_dilatedFejer_domination hH hL
  obtain ⟨K₀, K', hK₀, hK', hineq⟩ :=
    exists_norm_deviationPairing_le hW hexc hs hc hH hL hC hs1 hdom
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun η hη => ?_)
  rw [zero_add]
  obtain ⟨η₁, hη₁0, hη₁⟩ : ∃ η₁ : ℝ, 0 < η₁ ∧ 4 * η₁ = η := ⟨η / 4, by positivity, by ring⟩
  -- the cut-off
  have htail := tendsto_deviationPairing_tail hexc hD (Φ := dilatedFejer s)
    (contDiff_dilatedFejer s).continuous (integrable_dilatedFejer (by linarith))
    (integrable_fourier_dilatedFejer hs1) (b := 17 / 25) (by norm_num)
    (fun u hu => fourier_dilatedFejer_eq_zero hs1 hu)
  obtain ⟨Γ₀, hΓ₀⟩ := (Metric.tendsto_atTop.mp htail) (η₁ / (C + 1)) (by positivity)
  obtain ⟨Γ, hLΓ, hΓ, hT⟩ : ∃ Γ : ℝ, L ≤ Γ ∧ 0 < Γ ∧
      C * ‖deviationPairing lam (tailTransform (dilatedFejer s) Γ)‖ ≤ η₁ := by
    refine ⟨max (max Γ₀ L) 1, (le_max_right _ _).trans (le_max_left _ _),
      lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    have h1 := hΓ₀ (max (max Γ₀ L) 1) ((le_max_left _ _).trans (le_max_left _ _))
    rw [dist_zero_right, lt_div_iff₀ (by linarith)] at h1
    linarith [norm_nonneg (deviationPairing lam (tailTransform (dilatedFejer s) (max (max Γ₀ L) 1)))]
  -- the flatness
  have hN0 : (0 : ℝ) ≤ (zeroWindow (2 * Γ)).card := Nat.cast_nonneg _
  have hQ : 0 ≤ (H + 2 * C) * (1 + ((zeroWindow (2 * Γ)).card : ℝ)) := by positivity
  obtain ⟨ε, hε0, hε1, hεK⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      (H + 2 * C) * (1 + ((zeroWindow (2 * Γ)).card : ℝ)) * K' * ε ≤ η₁ := by
    obtain ⟨δ₀, h0, h1, -, h3, -⟩ :=
      exists_small_width (mul_nonneg hQ hK') (mul_nonneg hQ hK') hη₁0 one_pos
    exact ⟨δ₀, h0, h1, h3⟩
  obtain ⟨Kε, hKε, hineqε⟩ := hineq ε hε0 hε1
  -- the width
  obtain ⟨d, hd, hsep⟩ := exists_separation (insert 0 (zeroWindow (2 * Γ)))
  have hQ1 : 0 < 2 * ((H + 2 * C) * (1 + ((zeroWindow (2 * Γ)).card : ℝ)) + 1) := by positivity
  obtain ⟨δ₁, hδ₁, hA⟩ := tendsto_deficitMean hW hexc hmean (η₁ / (2 * ((H + 2 * C) *
    (1 + ((zeroWindow (2 * Γ)).card : ℝ)) + 1))) (div_pos hη₁0 hQ1)
  obtain ⟨δ₂, hδ₂, hE⟩ := hmean (η₁ / (2 * ((H + 2 * C) *
    (1 + ((zeroWindow (2 * Γ)).card : ℝ)) + 1))) (div_pos hη₁0 hQ1)
  have hMh := moment_nonneg h
  have hMr := moment_nonneg (fun ξ => (dilatedFejerCutoff s Γ ξ : ℂ))
  have hC₁ : 0 ≤ (K₀ + ((zeroWindow (2 * Γ)).card : ℝ) * Kε) *
      ((∫ u, ‖𝓕 h u‖ * (|u| * (1 + u ^ 2))) +
        C * ∫ u, ‖𝓕 (fun ξ => (dilatedFejerCutoff s Γ ξ : ℂ)) u‖ * (|u| * (1 + u ^ 2))) :=
    mul_nonneg (add_nonneg hK₀ (mul_nonneg hN0 hKε)) (add_nonneg hMh (mul_nonneg hC hMr))
  obtain ⟨δ₀, hδ₀, hδ₀1, hδ₀d, hδ₀C₁, -⟩ := exists_small_width hC₁ hC₁ hη₁0 hd
  set δ := min δ₀ (min δ₁ δ₂) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hδ : δ ≤ δ₀ := min_le_left _ _
  have hδ1' : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2' : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hS := separated_of_separation (zero_notMem_zeroWindow (2 * Γ)) hsep hδ0 (hδ.trans hδ₀d)
  have key := hineqε Γ δ hLΓ hΓ hδ0 (hδ.trans hδ₀1) hS
  have hAδ := hA δ hδ0 hδ1'
  have hEδ := hE δ hδ0 hδ2'
  have e1 := (mul_le_mul_of_nonneg_left hδ hC₁).trans hδ₀C₁
  have e3 : (H + 2 * C) * (1 + ((zeroWindow (2 * Γ)).card : ℝ)) *
      (deficitMean (deviationDeficit lam) δ + deficitMean (deviationExcess lam) δ) ≤ η₁ := by
    have hsum := add_le_add hAδ hEδ
    refine (mul_le_mul_of_nonneg_left hsum hQ).trans ?_
    rw [← add_div, mul_div_assoc', div_le_iff₀ hQ1]
    nlinarith
  linarith

end

end RHTower.WeilExcess
